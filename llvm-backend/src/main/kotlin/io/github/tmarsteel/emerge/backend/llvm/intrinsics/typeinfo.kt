package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import com.google.common.collect.MapMaker
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
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
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import org.bytedeco.llvm.global.LLVM

internal val staticObjectFinalizer: KotlinLlvmFunction<LlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.finalizeStaticObject",
    LlvmVoidType,
) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // by definition a noop. Static values cannot be finalized. Erroring on static value finalization is not
        // possible because sharing static data across threads fucks up the reference counter (data races).
        retVoid()
    }
}

internal object TypeinfoType : LlvmStructType("typeinfo") {
    val shiftRightAmount by structMember(EmergeWordType)
    val supertypes by structMember(PointerToEmergeArrayOfPointersToTypeInfoType)
    val anyValueVirtuals by structMember(EmergeAnyValueVirtualsType)
    val vtableBlob by structMember(LlvmArrayType(0L, LlvmFunctionAddressType))
}

/**
 * Getter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val getter_EmergeArrayOfPointersToTypeInfoType: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<TypeinfoType>> = KotlinLlvmFunction.define(
    "emerge.platform.valueArrayOfPointersToTypeinfo_Get",
    pointerTo(TypeinfoType)
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

/**
 * Setter function for [EmergeArrayOfPointersToTypeInfoType]
 */
private val setter_EmergeArrayOfPointersToTypeInfoType: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "emerge.platform.valueArrayOfPointersToTypeinfo_Set",
    LlvmVoidType
) {
    val self by param(PointerToEmergeArrayOfPointersToTypeInfoType)
    val index by param(EmergeWordType)
    val value by param(pointerTo(TypeinfoType))
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

internal val PointerToEmergeArrayOfPointersToTypeInfoType by lazy {
    pointerTo(
        EmergeArrayType(
            pointerTo(TypeinfoType),
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
        val virtualFunctions: EmergeLlvmContext.() -> Map<Long, LlvmFunction<*>>,
    ) : Provider {
        private val byContext: MutableMap<LlvmContext, StaticAndDynamicTypeInfo> = MapMaker().weakKeys().makeMap()
        override fun provide(context: EmergeLlvmContext): StaticAndDynamicTypeInfo {
            byContext[context]?.let { return it }
            val dynamicGlobal = context.addGlobal(context.undefValue(TypeinfoType), LlvmGlobal.ThreadLocalMode.SHARED)
            val staticGlobal = context.addGlobal(context.undefValue(TypeinfoType), LlvmGlobal.ThreadLocalMode.SHARED)
            val bundle = StaticAndDynamicTypeInfo(context, dynamicGlobal, staticGlobal)
            // register now to break loops
            byContext[context] = bundle

            val (dynamicConstant, staticConstant) = build(context)
            LLVM.LLVMSetInitializer(dynamicGlobal.raw, dynamicConstant.raw)
            LLVM.LLVMSetInitializer(staticGlobal.raw, staticConstant.raw)

            return bundle
        }

        private fun build(context: EmergeLlvmContext): Pair<LlvmConstant<TypeinfoType>, LlvmConstant<TypeinfoType>> {
            val dynamicSupertypesData = PointerToEmergeArrayOfPointersToTypeInfoType.pointed.buildConstantIn(context, supertypes, { it })
            val dynamicSupertypesGlobal = context.addGlobal(dynamicSupertypesData, LlvmGlobal.ThreadLocalMode.SHARED)
                .reinterpretAs(PointerToEmergeArrayOfPointersToTypeInfoType)

            val (vtableBlob, shiftRightAmount) = buildVTable(context, virtualFunctions(context))

            val typeinfoDynamicData = TypeinfoType.buildConstantIn(context) {
                setValue(TypeinfoType.shiftRightAmount, shiftRightAmount)
                setValue(TypeinfoType.supertypes, dynamicSupertypesGlobal)
                setValue(TypeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, finalizerFunction(context).address)
                })
                setValue(TypeinfoType.vtableBlob, vtableBlob)
            }

            val staticSupertypesData = PointerToEmergeArrayOfPointersToTypeInfoType.pointed.buildConstantIn(context, supertypes, { it })
            val staticSupertypesGlobal = context.addGlobal(staticSupertypesData, LlvmGlobal.ThreadLocalMode.SHARED)
                .reinterpretAs(PointerToEmergeArrayOfPointersToTypeInfoType)

            val typeinfoStaticData = TypeinfoType.buildConstantIn(context) {
                setValue(TypeinfoType.shiftRightAmount, shiftRightAmount)
                setValue(TypeinfoType.supertypes, staticSupertypesGlobal)
                setValue(TypeinfoType.anyValueVirtuals, EmergeAnyValueVirtualsType.buildConstantIn(context) {
                    setValue(EmergeAnyValueVirtualsType.finalizeFunction, context.registerIntrinsic(staticObjectFinalizer).address)
                })
                setValue(TypeinfoType.vtableBlob, vtableBlob)
            }

            return Pair(typeinfoDynamicData, typeinfoStaticData)
        }
    }

    companion object {
        fun define(
            typeName: String,
            supertypes: List<LlvmConstant<LlvmPointerType<TypeinfoType>>>,
            finalizerFunction: (EmergeLlvmContext) -> LlvmFunction<LlvmVoidType>,
            virtualFunctions: EmergeLlvmContext.() -> Map<Long, LlvmFunction<*>>,
        ): Provider = ProviderImpl(typeName, supertypes, finalizerFunction, virtualFunctions)
    }
}

private fun buildVTable(context: EmergeLlvmContext, functions: Map<Long, LlvmFunction<*>>): Pair<LlvmValue<LlvmArrayType<LlvmFunctionAddressType>>, LlvmConstant<EmergeWordType>> {
    var prefixLength = 1
    var shiftRightAmount: Int
    while (true) {
        if (prefixLength > 10) {
            throw CodeGenerationException("signature collision. Couldn't find a unique prefix of <= 10 bits for hashes ${functions.keys.joinToString()}")
        }
        shiftRightAmount = 64 - prefixLength
        val prefixes = functions.keys.map { it ushr shiftRightAmount }
        if (prefixes.isDistinct()) {
            break
        }
        prefixLength++
    }

    val entries = Array<LlvmFunction<*>?>(1 shl prefixLength) { null }
    functions.forEach { (hash, fn) ->
        val prefix = StrictMath.toIntExact(hash ushr shiftRightAmount)
        entries[prefix] = fn
    }

    val vtableBlobType = LlvmArrayType(entries.size.toLong(), LlvmFunctionAddressType)
    val vtableBlob = vtableBlobType.buildConstantIn(context, entries.map { fnPtr ->
        fnPtr?.address ?: context.nullValue(LlvmFunctionAddressType)
    })

    return Pair(vtableBlob, context.word(shiftRightAmount))
}

private fun List<Long>.isDistinct(): Boolean {
    val seen = HashSet<Long>()
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
        val shiftRightAmount = getelementptr(typeinfoPtr)
            .member { shiftRightAmount }
            .get()
            .dereference()

        val reducedHash = lshr(hash, shiftRightAmount)
        val functionAddress = getelementptr(typeinfoPtr)
            .member { vtableBlob }
            .index(reducedHash)
            .get()
            .dereference()
        ret(functionAddress)
    }
}