package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType

internal open class AnyvalueType(
    context: LlvmContext,
    name: String = "anyvalue",
) : LlvmStructType(context, name) {
    val strongReferenceCount by structMemberRaw { wordTypeRaw }
    val typeinfo by structMemberRaw { pointerTypeRaw }
    val weakReferenceCollection by structMember { weakReferenceCollection }
}