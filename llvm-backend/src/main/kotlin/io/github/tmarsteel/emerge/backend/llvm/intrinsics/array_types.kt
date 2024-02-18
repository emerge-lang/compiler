package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member

internal fun <Element : LlvmType> buildValueArrayBoxingElementGetter(
    typeName: String,
    getValueArrayType: () -> ArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeStructType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<AnyValueType>> {
    return KotlinLlvmFunction.define(
        "valuearray_${typeName}_get_boxed",
        pointerTo(AnyValueType)
    ) {
        val self by param(pointerTo(getValueArrayType()))
        val index by param(LlvmWordType)
        body {
            // TODO: bounds check!
            val raw = getelementptr(self)
                .member { elements }
                .index(index)
                .get()
                .dereference()

            val ctor = getBoxType(context).defaultConstructor.getInContext(context)
            ret(call(ctor, listOf(raw)).reinterpretAs(pointerTo(AnyValueType)))
        }
    }
}

internal fun <Element : LlvmType> buildValueArrayBoxingElementSetter(
    typeName: String,
    getValueArrayType: () -> ArrayType<Element>,
    getBoxType: EmergeLlvmContext.() -> EmergeStructType,
): KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> {
    return KotlinLlvmFunction.define(
        "valuearray_${typeName}_set_boxed",
        LlvmVoidType,
    ) {
        val arrayType = getValueArrayType()
        val self by param(pointerTo(arrayType))
        val index by param(LlvmWordType)
        val valueBoxAny by param(pointerTo(AnyValueType))
        body {
            val boxType = getBoxType(context)
            val valueMember = boxType.irStruct.members.single()
            check(valueMember.name == "value")
            check(context.getReferenceSiteType(valueMember.type) == arrayType.elementType)

            val valueBox = valueBoxAny.reinterpretAs(pointerTo(boxType))

            // TODO: bounds check!
            val raw = getelementptr(valueBox)
                .member(boxType.irStruct.members.single())
                .get()
                .dereference()
                .reinterpretAs(arrayType.elementType)
            val targetPointer = getelementptr(self)
                .member { elements }
                .index(index)
                .get()

            store(raw, targetPointer)
            retVoid()
        }
    }
}

internal fun <Element : LlvmType> buildValueArrayType(
    typeName: String,
    elementType: Element,
    getBoxType: EmergeLlvmContext.() -> EmergeStructType,
) : ArrayType<Element> {
    lateinit var arrayTypeHolder: ArrayType<Element>
    val getter = buildValueArrayBoxingElementGetter(typeName, { arrayTypeHolder }, getBoxType)
    val setter = buildValueArrayBoxingElementSetter(typeName, { arrayTypeHolder }, getBoxType)
    arrayTypeHolder = ArrayType(
        elementType,
        StaticAndDynamicTypeInfo.define(
            "array_$typeName",
            emptyList(),
            valueArrayFinalize,
        ) {
            listOf(
                word(ArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT) to getter,
                word(ArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT) to setter,
            )
        }
    )

    return arrayTypeHolder
}

internal val ValueArrayS8Type = buildValueArrayType("s8", LlvmI8Type, EmergeLlvmContext::boxTypeS8)
internal val ValueArrayU8Type = buildValueArrayType("u8", LlvmI8Type, EmergeLlvmContext::boxTypeU8)
internal val ValueArrayS16Type = buildValueArrayType("s16", LlvmI8Type, EmergeLlvmContext::boxTypeS16)
internal val ValueArrayU16Type = buildValueArrayType("u16", LlvmI8Type, EmergeLlvmContext::boxTypeU16)
internal val ValueArrayS32Type = buildValueArrayType("s32", LlvmI8Type, EmergeLlvmContext::boxTypeS32)
internal val ValueArrayU32Type = buildValueArrayType("u32", LlvmI8Type, EmergeLlvmContext::boxTypeU32)
internal val ValueArrayS64Type = buildValueArrayType("s64", LlvmI8Type, EmergeLlvmContext::boxTypeS64)
internal val ValueArrayU64Type = buildValueArrayType("u64", LlvmI8Type, EmergeLlvmContext::boxTypeU64)
internal val ValueArraySWordType = buildValueArrayType("sword", LlvmI8Type, EmergeLlvmContext::boxTypeSWord)
internal val ValueArrayUWordType = buildValueArrayType("uword", LlvmI8Type, EmergeLlvmContext::boxTypeUWord)
internal val ValueArrayBooleanType = buildValueArrayType("bool", LlvmBooleanType, EmergeLlvmContext::boxTypeBoolean)

private val referenceArrayElementGetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<AnyValueType>> = KotlinLlvmFunction.define(
    "refarray_get",
    pointerTo(AnyValueType),
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(LlvmWordType)
    body {
        // TODO: bounds check!
        val referenceEntry = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
            .dereference()

        ret(referenceEntry)
    }
}

private val referenceArrayElementSetter: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "refarray_set",
    LlvmVoidType,
) {
    val self by param(pointerTo(EmergeReferenceArrayType))
    val index by param(LlvmWordType)
    val value by param(pointerTo(AnyValueType))
    body {
        // TODO: bounds check!
        val pointerToSlotInArray = getelementptr(self)
            .member { elements }
            .index(index)
            .get()

        store(value, pointerToSlotInArray)
        retVoid()
    }
}

private val refArrayFinalize: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "refarray_finalize",
    LlvmVoidType,
) {
    val self by param(PointerToAnyValue)
    body {
        // TODO: walk references, drop each properly
        retVoid()
    }
}

internal val EmergeReferenceArrayType: ArrayType<LlvmPointerType<AnyValueType>> = ArrayType(
    PointerToAnyValue,
    StaticAndDynamicTypeInfo.define(
        "array_ref",
        emptyList(),
        refArrayFinalize,
    ) {
        listOf(
            word(ArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT) to referenceArrayElementGetter,
            word(ArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT) to referenceArrayElementSetter,
        )
    },
    "ref"
)