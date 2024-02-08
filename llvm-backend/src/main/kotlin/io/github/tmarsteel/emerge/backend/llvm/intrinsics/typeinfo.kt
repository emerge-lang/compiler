package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn

internal val staticValueDropFunction: KotlinLlvmFunction<LlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "drop_static",
    LlvmVoidType,
) {
    val self by param(PointerToAnyValue)
    body {
        // by definition a noop. Static values cannot be dropped, erroring on static value drop is not
        // possible because sharing static data across threads fucks up the refcounting with data races
        retVoid()
    }
}

internal object TypeinfoType : LlvmStructType("typeinfo") {
    val shiftRightAmount by structMember(LlvmWordType)
    val supertypes by structMember(pointerTo(EmergeArrayOfPointersToTypeInfoType))
    val anyValueVirtuals by structMember(AnyValueVirtualsType)
    val vtableBlob by structMember(LlvmArrayType(0L, LlvmFunctionAddressType))
}

private val ArrayOfPointersToTypeInfosGetElement: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<TypeinfoType>> = KotlinLlvmFunction.define(
    "valuearray_pointers_to_typeinfo_get",
    pointerTo(TypeinfoType)
) {
    val self by param(pointerTo(EmergeArrayOfPointersToTypeInfoType))
    val index by param(LlvmWordType)
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

private val ArrayOfPointersToTypeInfosSetElement: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "valuearray_pointers_to_typeinfo_set",
    LlvmVoidType
) {
    val self by param(pointerTo(EmergeArrayOfPointersToTypeInfoType))
    val index by param(LlvmWordType)
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

internal val EmergeArrayOfPointersToTypeInfoType = ArrayType(pointerTo(TypeinfoType), "pointer_to_typeinfo") { context ->
    StaticAndDynamicTypeInfo.buildInContext(
        context,
        "valuearray_pointers_to_typeinfo",
        emptyList(),
        valueArrayFinalize,
        listOf(
            context.word(ArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT) to ArrayOfPointersToTypeInfosGetElement,
            context.word(ArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT) to ArrayOfPointersToTypeInfosSetElement,
        )
    )
}

internal class StaticAndDynamicTypeInfo private constructor(
    val context: EmergeLlvmContext,
    val dynamic: LlvmGlobal<TypeinfoType>,
    val static: LlvmGlobal<TypeinfoType>,
) {
    companion object {
        fun buildInContext(
            context: EmergeLlvmContext,
            typeName: String,
            supertypes: List<LlvmConstant<LlvmPointerType<TypeinfoType>>>,
            finalizerFunction: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType>,
            virtualFunctions: List<Pair<LlvmConstant<LlvmWordType>, KotlinLlvmFunction<*, *>>>,
        ) : StaticAndDynamicTypeInfo {
            val dropFunction = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>(
                "drop_$typeName",
                LlvmVoidType
            ) {
                val self by param(PointerToAnyValue)
                body {
                    // TODO: check refcount is 0!
                    call(finalizerFunction.getInContext(context), listOf(self))
                    retVoid()
                }
            }

            val dynamicSupertypesData = EmergeArrayOfPointersToTypeInfoType.buildConstantIn(context, supertypes, { it })
            val dynamicSupertypesGlobal = context.addGlobal(dynamicSupertypesData, LlvmGlobal.ThreadLocalMode.SHARED)

            val vtableBlob = TypeinfoType.vtableBlob.type.buildConstantIn(context, emptyList()) // TODO: build vtable
            val shiftRightAmount = context.word(0)// TODO: build vtable

            val typeinfoDynamicData = TypeinfoType.buildConstantIn(context) {
                setValue(TypeinfoType.shiftRightAmount, shiftRightAmount)
                setValue(TypeinfoType.supertypes, dynamicSupertypesGlobal)
                setValue(TypeinfoType.anyValueVirtuals, AnyValueVirtualsType.buildConstantIn(context) {
                    setValue(AnyValueVirtualsType.dropFunction, dropFunction.getInContext(context).address)
                })
                setValue(TypeinfoType.vtableBlob, vtableBlob)
            }
            val typeinfoDynamicGlobal = context.addGlobal(typeinfoDynamicData, LlvmGlobal.ThreadLocalMode.SHARED)

            val staticSupertypesData = EmergeArrayOfPointersToTypeInfoType.buildConstantIn(context, supertypes + listOf(typeinfoDynamicGlobal), { it })
            val staticSupertypesGlobal = context.addGlobal(staticSupertypesData, LlvmGlobal.ThreadLocalMode.SHARED)

            val typeinfoStaticData = TypeinfoType.buildConstantIn(context) {
                setValue(TypeinfoType.shiftRightAmount, shiftRightAmount)
                setValue(TypeinfoType.supertypes, staticSupertypesGlobal)
                setValue(TypeinfoType.anyValueVirtuals, AnyValueVirtualsType.buildConstantIn(context) {
                    setValue(AnyValueVirtualsType.dropFunction, staticValueDropFunction.getInContext(context).address)
                })
            }
            val typeinfoStaticGlobal = context.addGlobal(typeinfoStaticData, LlvmGlobal.ThreadLocalMode.SHARED)

            return StaticAndDynamicTypeInfo(context, typeinfoDynamicGlobal, typeinfoStaticGlobal)
        }
    }
}