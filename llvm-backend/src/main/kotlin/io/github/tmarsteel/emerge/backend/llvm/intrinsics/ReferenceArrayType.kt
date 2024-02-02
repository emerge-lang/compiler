package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType

internal class ReferenceArrayType<Element : LlvmType>(
    context: LlvmContext,
    val elementType: Element,
) : LlvmStructType(context, "refarray") {
    val base by structMember { any }
    val elementCount by structMember { word }
    val elementsArray by structMember { LlvmArrayType(this, 0L, elementType) }
}