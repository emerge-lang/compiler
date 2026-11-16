package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.llvm.IrSimpleTypeImpl
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emergeStringLiteral
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.DiBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmDebugInfo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmNamedStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.u32
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativeI32FlagGroup
import io.github.tmarsteel.emerge.backend.llvm.requireStructuralSupertypeOf
import io.github.tmarsteel.emerge.backend.llvm.typeinfoHolder

internal val staticObjectFinalizer: KotlinLlvmFunction<LlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.finalizeStaticObject",
    LlvmVoidType,
) {
    @Suppress("UNUSED")
    val self by param(PointerToAnyEmergeValue)
    body {
        // by definition a noop. Static values cannot be finalized. Erroring on static value finalization is not
        // possible because sharing static data across threads fucks up the reference counter (data races).
        retVoid()
    }
}

internal class VTableType private constructor(val nEntries: Long) : LlvmNamedStructType("vtable_vectors$nEntries") {
    val shiftLeftAmount by structMember(LlvmU32Type)
    val shiftRightAmount by structMember(LlvmU32Type)
    val addresses by structMember(LlvmArrayType(nEntries, LlvmFunctionAddressType))

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return computeDiType(this, diBuilder, listOf(::shiftLeftAmount, ::shiftRightAmount, ::addresses))
    }

    companion object {
        private val cache = MapMaker().weakValues().makeMap<Long, VTableType>()
        operator fun invoke(nEntries: Long): VTableType {
            return cache.computeIfAbsent(nEntries, ::VTableType)
        }
    }
}

internal class TypeinfoType private constructor(val nVTableEntries: Long) : LlvmNamedStructType("typeinfo$nVTableEntries"), LlvmCachedType.ForwardDeclared {
    /**
     * actually always is a [PointerToEmergeArrayOfPointersToTypeInfoType]. Declaring that type here (or even
     * [PointerToAnyEmergeValue] would create a cyclic reference on JVM classload time.
     */
    val supertypes by structMember(pointerTo(LlvmVoidType))
    /**
     * points to an array object of references to static `emerge.core.reflection.NamedType`s: the parameterized
     * supertypes as seen from this type, see [staticSupertypeTemplates].
     */
    val supertypeTemplates by structMember(pointerTo(LlvmVoidType))
    val anyValueVirtuals by structMember(EmergeAnyValueVirtualsType)
    /** for dynamic typeinfo instances: null; for static ones: points to the dynamic version */
    val dynamicTypeInfoPtr by structMember(pointerTo(this))
    /** always points to a static `emerge.core.String` */
    val canonicalNamePtr by structMember(PointerToAnyEmergeValue)
    /** the [ArrayElementLayoutKind] (its [ArrayElementLayoutKind.code]) of arrays with elements of this type */
    val arrayElementLayoutKind by structMember(EmergeUWordType)
    /** see [io.github.tmarsteel.emerge.backend.api.ir.IrBaseType.isConst] */
    val isConst by structMember(LlvmBooleanType)
    /** see [io.github.tmarsteel.emerge.backend.api.ir.IrBaseType.isNonToken] */
    val isNonToken by structMember(LlvmBooleanType)
    /** !! dynamically sized !! */
    val vtable by structMember(VTableType(nVTableEntries))

    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        if (nVTableEntries == 0L) {
            return super.computeRaw(context)
        }

        val supertypeRaw = GENERIC.getRawInContext(context)
        val selfRaw = super.computeRaw(context)
        requireStructuralSupertypeOf(supertypeRaw, supertypeRaw, context.targetData.ref)
        return selfRaw
    }

    override fun isAssignableTo(other: LlvmType): Boolean {
        return other is TypeinfoType && other.nVTableEntries <= this.nVTableEntries
    }

    override fun computeDiType(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return computeDiType(this, diBuilder, listOf(::supertypes, ::supertypeTemplates, ::anyValueVirtuals, ::dynamicTypeInfoPtr, ::canonicalNamePtr, ::arrayElementLayoutKind, ::isConst, ::isNonToken, ::vtable), NativeI32FlagGroup())
    }

    override fun createTemporaryForwardDeclaration(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createTemporaryForwardDeclarationOfStructType(
            name,
            /*
             * approximation:
             * supertypes: pointer
             * supertypeTemplates: pointer
             * anyValueVirtuals: { pointer to dtor }
             * dynamicTypeInfoPtr: pointer
             * canonicalNamePtr: pointer to emerge string
             * arrayElementLayoutKind: word
             * isConst, isNonToken: booleans, padded to a word
             * vtable: [pointer x size]
             */
            sizeInBits = diBuilder.context.targetData.pointerSizeInBits * (7u + vtable.type.nEntries.toUInt()),
            alignInBits = diBuilder.context.targetData.pointerSizeInBits.toUInt(),
            flags = NativeI32FlagGroup(),
            declaredAt = Companion.declaredAt,
        )
    }

    companion object {
        private val cache = MapMaker().weakValues().makeMap<Long, TypeinfoType>()
        operator fun invoke(nVTableEntries: Long): TypeinfoType {
            return cache.computeIfAbsent(nVTableEntries, ::TypeinfoType)
        }
        val GENERIC = TypeinfoType(0)

        val declaredAt = JvmStackFrameIrSourceLocation(Thread.currentThread().stackTrace[1])
    }
}

/**
 * The array type for `Array<ReflectionBaseType>`: the elements are pointers to [TypeinfoType]; boxed into
 * `emerge.platform.ReflectionBaseTypeBox` when accessed through the virtual accessors.
 */
internal val PointerToEmergeArrayOfPointersToTypeInfoType by lazy {
    pointerTo(buildValueArrayType("pointer_to_typeinfo", pointerTo(TypeinfoType.GENERIC), EmergeLlvmContext::boxTypeReflectionBaseType))
}

internal class StaticAndDynamicTypeInfo private constructor(
    val context: EmergeLlvmContext,
    val dynamic: LlvmGlobal<TypeinfoType>,
    val static: LlvmGlobal<TypeinfoType>,
) {
    fun interface Provider {
        fun provide(context: EmergeLlvmContext): StaticAndDynamicTypeInfo
    }

    private class ProviderImpl(
        val canonicalNameGetter: (EmergeLlvmContext) -> String,
        val supertypes: Collection<(EmergeLlvmContext) -> LlvmGlobal<TypeinfoType>>,
        val supertypeTemplatesOf: IrBaseType?,
        val isConst: Boolean,
        val isNonToken: Boolean,
        val finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
        val runtimeTypeGetter: (EmergeLlvmContext) -> LlvmFunction<LlvmPointerType<out EmergeHeapAllocated>>,
        val virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
        val arrayElementLayoutKind: ArrayElementLayoutKind,
    ) : Provider {
        private val byContext: MutableMap<LlvmContext, StaticAndDynamicTypeInfo> = MapMaker().weakKeys().makeMap()
        override fun provide(context: EmergeLlvmContext): StaticAndDynamicTypeInfo {
            byContext[context]?.let { return it }

            val canonicalName = canonicalNameGetter(context)
            val vtableConstant = buildVTable(context, virtualFunctions(context), context.registerIntrinsic(missingVirtualFunctionHandler).address)
            val typeinfoType = TypeinfoType(vtableConstant.type.nEntries)

            val dynamicGlobal = context.addGlobal(context.undefValue(typeinfoType), LlvmThreadLocalMode.NOT_THREAD_LOCAL, "typeinfo_${canonicalName}_dynamic")
            val staticGlobal = context.addGlobal(context.undefValue(typeinfoType), LlvmThreadLocalMode.NOT_THREAD_LOCAL, "typeinfo_${canonicalName}_static")
            val bundle = StaticAndDynamicTypeInfo(context, dynamicGlobal, staticGlobal)
            // register now to break loops
            byContext[context] = bundle

            val (dynamicConstant, staticConstant) = build(
                context,
                typeinfoType,
                canonicalName,
                vtableConstant,
                dynamicGlobal,
            )
            Llvm.LLVMSetInitializer(dynamicGlobal.raw, dynamicConstant.raw)
            Llvm.LLVMSetInitializer(staticGlobal.raw, staticConstant.raw)

            return bundle
        }

        private fun build(
            context: EmergeLlvmContext,
            typeinfoType: TypeinfoType,
            canonicalName: String,
            vtable: LlvmConstant<VTableType>,
            dynamicGlobal: LlvmGlobal<TypeinfoType>,
        ): Pair<LlvmConstant<TypeinfoType>, LlvmConstant<TypeinfoType>> {
            val supertypesData = PointerToEmergeArrayOfPointersToTypeInfoType.pointed.buildConstantIn(
                context,
                supertypes,
                context.staticReifiedType(IrSimpleTypeImpl(context.rawReflectionBaseTypeClazz, IrTypeMutability.IMMUTABLE, false)),
            ) {
                it(context)
            }
            val supertypesGlobal = context.addGlobal(supertypesData, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
                .reinterpretAs(pointerTo(LlvmVoidType))

            val supertypeTemplatesGlobal = context.staticSupertypeTemplates(supertypeTemplatesOf)

            val canonicalNameGlobal = context.emergeStringLiteral(canonicalName)

            val typeinfoDynamicData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.supertypeTemplates, supertypeTemplatesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, finalizerFunction(context).address)
                    setValue(EmergeAnyValueVirtualsType.runtimeTypeGetterFunction, runtimeTypeGetter(context).address)
                })
                setNull(typeinfoType.dynamicTypeInfoPtr)
                setValue(typeinfoType.canonicalNamePtr, canonicalNameGlobal)
                setValue(typeinfoType.arrayElementLayoutKind, context.uWord(arrayElementLayoutKind.code))
                setValue(typeinfoType.isConst, context.i1(isConst))
                setValue(typeinfoType.isNonToken, context.i1(isNonToken))
            }

            val typeinfoStaticData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.supertypeTemplates, supertypeTemplatesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, context.registerIntrinsic(staticObjectFinalizer).address)
                    setValue(EmergeAnyValueVirtualsType.runtimeTypeGetterFunction, runtimeTypeGetter(context).address)
                })
                setValue(typeinfoType.dynamicTypeInfoPtr, dynamicGlobal)
                setValue(typeinfoType.canonicalNamePtr, canonicalNameGlobal)
                setValue(typeinfoType.arrayElementLayoutKind, context.uWord(arrayElementLayoutKind.code))
                setValue(typeinfoType.isConst, context.i1(isConst))
                setValue(typeinfoType.isNonToken, context.i1(isNonToken))
            }

            return Pair(typeinfoDynamicData, typeinfoStaticData)
        }
    }

    companion object {
        fun defineRaw(
            typeName: (EmergeLlvmContext) -> String,
            supertypes: Collection<(EmergeLlvmContext) -> LlvmGlobal<TypeinfoType>>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
            runtimeTypeGetter: (EmergeLlvmContext) -> LlvmFunction<LlvmPointerType<out EmergeHeapAllocated>>,
            virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
            arrayElementLayoutKind: ArrayElementLayoutKind = ArrayElementLayoutKind.REFERENCE,
        ): Provider = ProviderImpl(
            typeName,
            supertypes,
            null,
            false,
            true, // these are arrays, and no class of arrays is a token class
            finalizerFunction,
            runtimeTypeGetter,
            virtualFunctions,
            arrayElementLayoutKind,
        )

        /**
         * @param describedType the base type the typeinfo describes; its [IrBaseType.parameterizedSupertypes]
         * end up in [TypeinfoType.supertypeTemplates]
         * @param isConst see [TypeinfoType.isConst]
         * @param isNonToken see [TypeinfoType.isNonToken]
         */
        fun define(
            typeName: (EmergeLlvmContext) -> String,
            describedType: IrBaseType,
            isConst: Boolean,
            isNonToken: Boolean,
            supertypes: Collection<IrInterface>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
            runtimeTypeGetter: (EmergeLlvmContext) -> LlvmFunction<LlvmPointerType<out EmergeHeapAllocated>>,
            virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
            arrayElementLayoutKind: ArrayElementLayoutKind,
        ): Provider = ProviderImpl(
            typeName,
            supertypes.map { irSupertype -> { ctx -> irSupertype.typeinfoHolder.getTypeinfoInContext(ctx) } },
            describedType,
            isConst,
            isNonToken,
            finalizerFunction,
            runtimeTypeGetter,
            virtualFunctions,
            arrayElementLayoutKind,
        )
    }
}

/**
 * The maximum number of entries in any vtable is `2^(this value)`.
 */
private const val VTABLE_MAX_SIZE_LOG2 = 10

/**
 * @param missingFunction the address to place in the spots in the vtable where none of the [functions] end up in.
 */
internal fun buildVTable(
    context: EmergeLlvmContext,
    functions: Map<ULong, LlvmFunction<*>>,
    missingFunction: LlvmValue<LlvmFunctionAddressType>,
): LlvmConstant<VTableType> {
    fun getSection(hash: ULong, shiftLeftAmount: Int, shiftRightAmount: Int): ULong {
        return (hash shl shiftLeftAmount) shr shiftRightAmount
    }

    var windowSize = (functions.size.toUInt().discreteLog2Ceil().coerceAtLeast(2u)).toInt()
    var shiftLeftAmount: Int
    var shiftRightAmount: Int
    tryWindowSize@while (true) {
        if (windowSize > VTABLE_MAX_SIZE_LOG2) {
            val nCommonOneBits = functions.keys.reduce(ULong::and).countOneBits()
            val nCommonZeroBits = functions.keys.map(ULong::inv).reduce(ULong::and).countOneBits()
            val hashes = functions.keys.joinToString(transform = { it.toString(2).padStart(64, '0') })
            throw VirtualFunctionHashCollisionException("signature collision. Couldn't find a unique window of <= $VTABLE_MAX_SIZE_LOG2 bits. ${nCommonOneBits + nCommonZeroBits} common bits; for hashes $hashes")
        }
        shiftRightAmount = 64 - windowSize
        shiftLeftAmount = 0
        while (shiftLeftAmount <= 63) {
            val sections = functions.keys.map { getSection(it, shiftLeftAmount, shiftRightAmount) }
            if (sections.isDistinct()) {
                break@tryWindowSize
            }

            shiftLeftAmount++
        }
        windowSize++
    }

    val maxSection = StrictMath.toIntExact(getSection(ULong.MAX_VALUE, shiftLeftAmount, shiftRightAmount).toLong())
    val entries = Array<LlvmFunction<*>?>(maxSection + 1) { null }
    functions.forEach { (hash, fn) ->
        val section = StrictMath.toIntExact(getSection(hash, shiftLeftAmount, shiftRightAmount).toLong())
        entries[section] = fn
    }

    val vtableType = VTableType(entries.size.toLong())
    val addressesArrayType = vtableType.addresses.type

    return vtableType.buildConstantIn(context) {
        setValue(vtableType.shiftLeftAmount, context.u32(shiftLeftAmount.toUInt()))
        setValue(vtableType.shiftRightAmount, context.u32(shiftRightAmount.toUInt()))
        setValue(vtableType.addresses, addressesArrayType.buildConstantIn(context, entries.map { fnPtr ->
            fnPtr?.address ?: missingFunction
        }))
    }
}

private fun UInt.discreteLog2Ceil(): UInt {
    var log = 0u
    var carry = this
    while (carry > 0u) {
        log++
        carry = carry shr 1
    }

    return log
}

private fun List<ULong>.isDistinct(): Boolean {
    val seen = HashSet<ULong>()
    for (n in this) {
        if (!seen.add(n)) {
            return false
        }
    }

    return true
}

val getDynamicCallAddress: KotlinLlvmFunction<EmergeLlvmContext, LlvmFunctionAddressType> = KotlinLlvmFunction.define(
    "getDynamicCallAddress",
    LlvmFunctionAddressType,
) {
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.Hot)

    val self by param(PointerToAnyEmergeValue)
    val hash by param(EmergeUWordType)

    body {
        val typeinfoPtr = self
            .anyValueBase()
            .member { typeinfo }
            .get()
            .dereference()
        val shiftLeftAmountI32 = getelementptr(typeinfoPtr)
            .member { vtable }
            .member { shiftLeftAmount }
            .get()
            .dereference()
        val shiftLeftAmountWord = enlargeUnsigned(shiftLeftAmountI32, EmergeUWordType)
        val shiftRightAmountI32 = getelementptr(typeinfoPtr)
            .member { vtable }
            .member { shiftRightAmount }
            .get()
            .dereference()
        val shiftRightAmountWord = enlargeUnsigned(shiftRightAmountI32, EmergeUWordType)

        val reducedHash = lshr(shl(hash, shiftLeftAmountWord), shiftRightAmountWord)
        val functionAddress = getelementptr(typeinfoPtr)
            .member { vtable }
            .member { addresses }
            .index(reducedHash)
            .get()
            .dereference()
        ret(functionAddress)
    }
}

class VirtualFunctionHashCollisionException(message: String, cause: Throwable? = null) : RuntimeException(message, cause)

val missingVirtualFunctionHandler = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>(
    "emerge.platform.missingVirtualFunction",
    LlvmVoidType,
) {
    body {
        inlinePanic("Missing virtual function")
    }
}