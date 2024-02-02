package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType

internal class AnyvalueType(
    context: LlvmContext,
) : LlvmStructType(context, "anyvalue") {
    val strongReferenceCount by structMember { word }
    val typeinfo by structMember { pointerTo(typeinfo) }
    val weakReferenceCollection by structMember { pointerTo(weakReferenceCollection) }
}