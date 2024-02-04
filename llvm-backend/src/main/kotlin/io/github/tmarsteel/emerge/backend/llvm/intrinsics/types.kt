package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import org.bytedeco.llvm.global.LLVM

internal object LlvmWordType : LlvmCachedType(), LlvmIntegerType {
    override fun computeRaw(context: LlvmContext) = LLVM.LLVMIntTypeInContext(context.ref, LLVM.LLVMPointerSize(context.targetData) * 8)
}

internal fun LlvmContext.word(value: Int): LlvmValue<LlvmWordType> = LlvmValue(
    LLVM.LLVMConstInt(LlvmWordType.getRawInContext(this), value.toLong(), 0),
    LlvmWordType,
)

internal object TypeinfoType : LlvmStructType("typeinfo") {
    val shiftRightAmount by structMember(LlvmWordType)
    val supertypes by structMember(
        pointerTo(
            ValueArrayType(
                pointerTo(this@TypeinfoType),
                this@TypeinfoType.name,
            )
        )
    )
    val vtableBlob by structMember(LlvmArrayType(0L, LlvmFunctionAddressType))
}

internal object WeakReferenceCollectionType : LlvmStructType("weakrefcoll") {
    val weakObjects = structMember(
        LlvmArrayType(10, PointerToAnyValue)
    )
    val next = structMember(pointerTo(this@WeakReferenceCollectionType))
}

internal object AnyValueType : LlvmStructType("anyvalue") {
    val strongReferenceCount by structMember(LlvmVoidType)
    val typeinfo by structMember(pointerTo(TypeinfoType))
    val weakReferenceCollection by structMember(pointerTo(WeakReferenceCollectionType))
}

internal val PointerToAnyValue: LlvmPointerType<AnyValueType> = pointerTo(AnyValueType)

internal class ReferenceArrayType<Element : LlvmType>(
    val elementType: Element,
) : LlvmStructType("refarray") {
    val base by structMember(AnyValueType)
    val elementCount by structMember(LlvmWordType)
    val elementsArray by structMember(LlvmArrayType(0L, elementType))
}

internal class ValueArrayType<Element : LlvmType>(
    elementType: Element,
    valueTypeName: String,
) : LlvmStructType("valuearray_$valueTypeName") {
    val strongReferenceCount by structMember(LlvmWordType)
    val weakReferenceCollection by structMember(pointerTo(WeakReferenceCollectionType))
    val elementCount by structMember(LlvmWordType)
    val elementsArray by structMember(LlvmArrayType(0L, elementType))
}

