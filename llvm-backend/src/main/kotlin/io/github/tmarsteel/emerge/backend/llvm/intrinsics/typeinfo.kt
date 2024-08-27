package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emergeStringLiteral
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmNamedStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleSuccess
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.retFallibleVoid
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
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
    val shiftLeftAmount by structMember(LlvmI32Type)
    val shiftRightAmount by structMember(LlvmI32Type)
    val addresses by structMember(LlvmArrayType(nEntries, LlvmFunctionAddressType))

    companion object {
        private val cache = MapMaker().weakValues().makeMap<Long, VTableType>()
        operator fun invoke(nEntries: Long): VTableType {
            return cache.computeIfAbsent(nEntries, ::VTableType)
        }
    }
}

internal class TypeinfoType private constructor(val nVTableEntries: Long) : LlvmNamedStructType("typeinfo$nVTableEntries") {
    /**
     * actually always is a [PointerToEmergeArrayOfPointersToTypeInfoType]. Declaring that type here (or even
     * [PointerToAnyEmergeValueo] would create a cyclic reference on JVM classload time.
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

    companion object {
        private val cache = MapMaker().weakValues().makeMap<Long, TypeinfoType>()
        operator fun invoke(nVTableEntries: Long): TypeinfoType {
            return cache.computeIfAbsent(nVTableEntries, ::TypeinfoType)
        }
        val GENERIC = TypeinfoType(0)
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
        val index by param(EmergeWordType)
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
        val index by param(EmergeWordType)
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
        val index by param(EmergeWordType)
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
        val index by param(EmergeWordType)
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
        param(EmergeWordType)

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualGet is not implemented")
        }
    }

    val virtualGetterPanic = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualGet_panic",
        PointerToAnyEmergeValue,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeWordType)

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualGet is not implemented")
        }
    }

    val virtualSetterFallible = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_virtualSet_fallible",
        EmergeFallibleCallResult.OfVoid,
    ) {
        param(PointerToAnyEmergeValue)
        param(EmergeWordType)
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
        param(EmergeWordType)
        param(pointerTo(TypeinfoType.GENERIC))

        body {
            inlinePanic("array_pointer_to_typeinfo_virtualSet is not implemented")
        }
    }

    val defaultValueCtor = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
        "array_pointer_to_typeinfo_defaultValueCtor",
        PointerToAnyEmergeValue,
    ) {
        param(EmergeWordType)
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
 * @param missingFunction the address to place in the spots in the vtable where none of the [functions] end up in.
 */
private fun buildVTable(
    context: EmergeLlvmContext,
    functions: Map<ULong, LlvmFunction<*>>,
    missingFunction: LlvmValue<LlvmFunctionAddressType>,
): LlvmConstant<VTableType> {
    fun getSection(hash: ULong, shiftLeftAmount: Int, shiftRightAmount: Int): ULong {
        return (hash shl shiftLeftAmount) shr shiftRightAmount
    }

    var windowSize = 2
    var shiftLeftAmount: Int
    var shiftRightAmount: Int
    tryWindowSize@while (true) {
        if (windowSize > 10) {
            throw VirtualFunctionHashCollisionException("signature collision. Couldn't find a unique window of <= 10 bits for hashes ${functions.keys.joinToString()}")
        }
        shiftLeftAmount = 0
        while (shiftLeftAmount <= 63) {
            shiftRightAmount = shiftLeftAmount + (63 - shiftLeftAmount) - windowSize
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

    val addressesArrayType = LlvmArrayType(entries.size.toLong(), LlvmFunctionAddressType)

    val vtableType = VTableType(entries.size.toLong())
    return vtableType.buildConstantIn(context) {
        setValue(vtableType.shiftLeftAmount, context.i32(shiftLeftAmount))
        setValue(vtableType.shiftRightAmount, context.i32(shiftRightAmount))
        setValue(vtableType.addresses, addressesArrayType.buildConstantIn(context, entries.map { fnPtr ->
            fnPtr?.address ?: missingFunction
        }))
    }
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
    val hash by param(EmergeWordType)

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
        val shiftLeftAmountWord = enlargeUnsigned(shiftLeftAmountI32, EmergeWordType)
        val shiftRightAmountI32 = getelementptr(typeinfoPtr)
            .member { vtable }
            .member { shiftRightAmount }
            .get()
            .dereference()
        val shiftRightAmountWord = enlargeUnsigned(shiftRightAmountI32, EmergeWordType)

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