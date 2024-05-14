package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.requireStructuralSupertypeOf

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

internal class VTableType private constructor(val nEntries: Long) : LlvmStructType("vtable_vectors$nEntries") {
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

internal class TypeinfoType private constructor(val nVTableEntries: Long) : LlvmStructType("typeinfo$nVTableEntries") {
    /**
     * actually always is a [PointerToEmergeArrayOfPointersToTypeInfoType]. Declaring that type here would create a cyclic
     * reference on JVM classload time. This is cast back in the [getSupertypePointers] intrinsic.
     */
    val supertypes by structMember(PointerToAnyEmergeValue)
    val anyValueVirtuals by structMember(EmergeAnyValueVirtualsType)
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
private val getter_EmergeArrayOfPointersToTypeInfoType: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<TypeinfoType>> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Get",
        pointerTo(TypeinfoType.GENERIC)
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeWordType)
        body {
            // TODO: bounds check!
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
private val setter_EmergeArrayOfPointersToTypeInfoType: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> by lazy {
    KotlinLlvmFunction.define(
        "emerge.platform.valueArrayOfPointersToTypeinfo_Set",
        LlvmVoidType
    ) {
        val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
        val index by param(EmergeWordType)
        val value by param(pointerTo(TypeinfoType.GENERIC))
        body {
            // TODO: bounds check!
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(value, targetPointer)

            retVoid()
        }
    }
}

internal val PointerToEmergeArrayOfPointersToTypeInfoType by lazy {
    pointerTo(
        EmergeArrayType(
            pointerTo(TypeinfoType.GENERIC),
            StaticAndDynamicTypeInfo.define(
                "valuearray_pointers_to_typeinfo",
                emptyList(),
                { ctx -> ctx.registerIntrinsic(valueArrayFinalize) },
            ) {
                mapOf(
                    EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT to registerIntrinsic(getter_EmergeArrayOfPointersToTypeInfoType),
                    EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT to registerIntrinsic(setter_EmergeArrayOfPointersToTypeInfoType),
                )
            },
            "pointer_to_typeinfo",
        )
    )
}

internal class StaticAndDynamicTypeInfo private constructor(
    val context: EmergeLlvmContext,
    val dynamic: LlvmGlobal<TypeinfoType>,
    val static: LlvmGlobal<TypeinfoType>,
) {
    interface Provider {
        fun provide(context: EmergeLlvmContext): StaticAndDynamicTypeInfo
    }

    private class ProviderImpl(
        val typeName: String,
        val supertypes: List<LlvmConstant<LlvmPointerType<TypeinfoType>>>,
        val finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<LlvmVoidType>,
        val virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
    ) : Provider {
        private val byContext: MutableMap<LlvmContext, StaticAndDynamicTypeInfo> = MapMaker().weakKeys().makeMap()
        override fun provide(context: EmergeLlvmContext): StaticAndDynamicTypeInfo {
            byContext[context]?.let { return it }

            val vtableConstant = buildVTable(context, virtualFunctions(context))
            val typeinfoType = TypeinfoType(vtableConstant.type.nEntries)

            val dynamicGlobal = context.addGlobal(context.undefValue(typeinfoType), LlvmThreadLocalMode.NOT_THREAD_LOCAL)
            val staticGlobal = context.addGlobal(context.undefValue(typeinfoType), LlvmThreadLocalMode.NOT_THREAD_LOCAL)
            val bundle = StaticAndDynamicTypeInfo(context, dynamicGlobal, staticGlobal)
            // register now to break loops
            byContext[context] = bundle

            val (dynamicConstant, staticConstant) = build(context, typeinfoType, vtableConstant)
            Llvm.LLVMSetInitializer(dynamicGlobal.raw, dynamicConstant.raw)
            Llvm.LLVMSetInitializer(staticGlobal.raw, staticConstant.raw)

            return bundle
        }

        private fun build(
            context: EmergeLlvmContext,
            typeinfoType: TypeinfoType,
            vtable: LlvmConstant<VTableType>,
        ): Pair<LlvmConstant<TypeinfoType>, LlvmConstant<TypeinfoType>> {
            val supertypesData = PointerToEmergeArrayOfPointersToTypeInfoType.pointed.buildConstantIn(context, supertypes, { it })
            val supertypesGlobal = context.addGlobal(supertypesData, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
                .reinterpretAs(PointerToAnyEmergeValue)

            val typeinfoDynamicData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, finalizerFunction(context).address)
                })
            }

            val typeinfoStaticData = typeinfoType.buildConstantIn(context) {
                setValue(typeinfoType.vtable, vtable)
                setValue(typeinfoType.supertypes, supertypesGlobal)
                setValue(typeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, context.registerIntrinsic(staticObjectFinalizer).address)
                })
            }

            return Pair(typeinfoDynamicData, typeinfoStaticData)
        }
    }

    companion object {
        fun define(
            typeName: String,
            supertypes: List<LlvmConstant<LlvmPointerType<TypeinfoType>>>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<LlvmVoidType>,
            virtualFunctions: EmergeLlvmContext.() -> Map<ULong, LlvmFunction<*>>,
        ): Provider = ProviderImpl(typeName, supertypes, finalizerFunction, virtualFunctions)
    }
}

private fun buildVTable(context: EmergeLlvmContext, functions: Map<ULong, LlvmFunction<*>>): LlvmConstant<VTableType> {
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
            assert(shiftLeftAmount < shiftRightAmount)
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
            fnPtr?.address ?: context.nullValue(LlvmFunctionAddressType)
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
    val self by param(PointerToAnyEmergeValue)
    val hash by param(EmergeWordType)
    body {
        val typeinfoPtr = getelementptr(self)
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