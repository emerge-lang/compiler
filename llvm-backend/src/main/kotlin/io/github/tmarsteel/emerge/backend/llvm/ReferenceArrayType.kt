package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType

internal class ReferenceArrayType<Element : LlvmType>(
    context: LlvmContext,
    val elementType: Element,
) : AnyvalueType(context, "refarray") {
    val elementCount by structMemberRaw { wordTypeRaw }
    val elementsArray by structMember { LlvmArrayType(this, 0L, elementType) }
}