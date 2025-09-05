package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emergeStringLiteral
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.DiBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
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
import io.github.tmarsteel.emerge.backend.llvm.dsl.u32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleSuccess
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.retFallibleVoid
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
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
    val anyValueVirtuals by structMember(EmergeAnyValueVirtualsType)
    /** for dynamic typeinfo instances: null; for static ones: points to the dynamic version */
    val dynamicTypeInfoPtr by structMember(pointerTo(this))
    /** always points to a static `emerge.core.String` */
    val canonicalNamePtr by structMember(PointerToAnyEmergeValue)
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
        return computeDiType(this, diBuilder, listOf(::supertypes, ::anyValueVirtuals, ::dynamicTypeInfoPtr, ::canonicalNamePtr, ::vtable), NativeI32FlagGroup())
    }

    override fun createTemporaryForwardDeclaration(diBuilder: DiBuilder): LlvmDebugInfo.Type {
        return diBuilder.createTemporaryForwardDeclarationOfStructType(
            name,
            /*
             * approximation:
             * supertypes: pointer
             * anyValueVirtuals: { pointer to dtor }
             * dynamicTypeInfoPtr: pointer
             * canonicalNamePtr: pointer to emerge string
             * vtable: [pointer x size]
             */
            sizeInBits = diBuilder.context.targetData.pointerSizeInBits * (4u + vtable.type.nEntries.toUInt()),
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
 * Getter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val getter_EmergeArrayOfPointersToTypeInfoType_fallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<TypeinfoType>>> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Get_ExceptionOnOutOfBounds",
        EmergeFallibleCallResult.WithValue(pointerTo(TypeinfoType.GENERIC)),
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeUWordType)
        body {
            inlineFallibleBoundsCheck(self, index)
            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            ret(fallibleSuccess(raw))
        }
    }
}

/**
 * Getter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val getter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<TypeinfoType>> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Get_PanicOnOutOfBounds",
        pointerTo(TypeinfoType.GENERIC),
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeUWordType)
        body {
            val selfSize = getelementptr(self)
                .member { base }
                .member { elementCount }
                .get()
                .dereference()
            conditionalBranch(
                condition = icmp(index, LlvmIntPredicate.UNSIGNED_GREATER_THAN_OR_EQUAL, selfSize),
                ifTrue = {
                    inlinePanic("index into array of typeinfo pointers is out of bounds")
                }
            )
            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            ret(raw)
        }
    }
}

/**
 * Setter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val setter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Set",
        LlvmVoidType
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeUWordType)
        val value by param(pointerTo(TypeinfoType.GENERIC))
        body {
            inlinePanicBoundsCheck(self, index)
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(value, targetPointer)

            retVoid()
        }
    }
}

/**
 * Setter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val setter_EmergeArrayOfPointersToTypeInfoType_fallibleBoundsCheck: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.OfVoid> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Set",
        EmergeFallibleCallResult.OfVoid,
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeUWordType)
        val value by param(pointerTo(TypeinfoType.GENERIC))
        body {
            inlinePanicBoundsCheck(self, index)
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(value, targetPointer)

            retFallibleVoid()
        }
    }
}

internal val PointerToEmergeArrayOfPointersToTypeInfoType by lazy {
    val virtualGetterFallible = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualGet_fallible",
        EmergeFallibleCallResult.ofEmergeReference,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeUWordType)

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualGet is not implemented")
        }
    }

    val virtualGetterPanic = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualGet_panic",
        PointerToAnyEmergeValue,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeUWordType)

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualGet is not implemented")
        }
    }

    val virtualSetterFallible = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualSet_fallible",
        EmergeFallibleCallResult.OfVoid,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeUWordType)
        param(pointerTo(TypeinfoType.GENERIC))

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualSet is not implemented")
        }
    }

    val virtualSetterPanic = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualSet_panic",
        LlvmVoidType,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeUWordType)
        param(pointerTo(TypeinfoType.GENERIC))

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualSet is not implemented")
        }
    }

    val defaultValueCtor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_defaultValueCtor",
        PointerToAnyEmergeValue,
    ) {
        param(EmergeUWordType)
        param(pointerTo(TypeinfoType.GENERIC))

        body {
            inlinePanic("array_pointer_to_typeinfo_defaultValueCtor is not implemented")
        }
    }

    pointerTo(
        EmergeArrayType(
            "pointer_to_typeinfo",
            pointerTo(TypeinfoType.GENERIC),
            virtualGetterFallible,
            virtualGetterPanic,
            virtualSetterFallible,
            virtualSetterPanic,
            getter_EmergeArrayOfPointersToTypeInfoType_fallibleBoundsCheck,
            getter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck,
            getter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck,
            setter_EmergeArrayOfPointersToTypeInfoType_fallibleBoundsCheck,
            setter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck,
            setter_EmergeArrayOfPointersToTypeInfoType_panicBoundsCheck,
            valueArrayDestructor,
            defaultValueCtor,
            listOf(EmergeReferenceArrayType.typeinfo),
        )
    )
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
        val finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
        val virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
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
            val supertypesData = PointerToEmergeArrayOfPointersToTypeInfoType.pointed.buildConstantIn(context, supertypes) {
                it(context)
            }
            val supertypesGlobal = context.addGlobal(supertypesData, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
                .reinterpretAs(pointerTo(LlvmVoidType))

            val canonicalNameGlobal = context.emergeStringLiteral(canonicalName)

            val typeinfoDynamicData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, finalizerFunction(context).address)
                })
                setNull(typeinfoType.dynamicTypeInfoPtr)
                setValue(typeinfoType.canonicalNamePtr, canonicalNameGlobal)
            }

            val typeinfoStaticData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, context.registerIntrinsic(staticObjectFinalizer).address)
                })
                setValue(typeinfoType.dynamicTypeInfoPtr, dynamicGlobal)
                setValue(typeinfoType.canonicalNamePtr, canonicalNameGlobal)
            }

            return Pair(typeinfoDynamicData, typeinfoStaticData)
        }
    }

    companion object {
        fun defineRaw(
            typeName: (EmergeLlvmContext) -> String,
            supertypes: Collection<(EmergeLlvmContext) -> LlvmGlobal<TypeinfoType>>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
            virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
        ): Provider = ProviderImpl(
            typeName,
            supertypes,
            finalizerFunction,
            virtualFunctions
        )

        fun define(
            typeName: (EmergeLlvmContext) -> String,
            supertypes: Collection<IrInterface>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<*>,
            virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
        ): Provider = ProviderImpl(
            typeName,
            supertypes.map { irSupertype -> { ctx -> irSupertype.typeinfoHolder.getTypeinfoInContext(ctx) } },
            finalizerFunction,
            virtualFunctions,
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