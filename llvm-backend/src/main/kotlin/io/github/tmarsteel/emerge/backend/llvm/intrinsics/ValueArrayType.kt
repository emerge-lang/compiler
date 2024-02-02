package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType

internal class ValueArrayType<Element : LlvmType>(
    elementType: Element,
    valueTypeName: String,
) : LlvmStructType(elementType.context, "valuearray_$valueTypeName") {
    val referenceCount by structMemberRaw { wordTypeRaw }
    val weakReferenceCollection by structMemberRaw { pointerTypeRaw }
    val elementCount by structMemberRaw { wordTypeRaw }
    val elementsArray by structMember { LlvmArrayType(this, 0L, elementType) }
}