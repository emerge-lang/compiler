package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmLeafType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.cachedType
import org.bytedeco.llvm.global.LLVM

internal val LlvmContext.boolean: LlvmType by cachedType {
    LlvmLeafType(this, LLVM.LLVMInt1TypeInContext(ref))
}

internal val LlvmContext.i8 by cachedType {
    LlvmIntegerType(this, 16)
}

internal val LlvmContext.i16 by cachedType {
    LlvmIntegerType(this, 16)
}

internal val LlvmContext.i32 by cachedType {
    LlvmIntegerType(this, 32)
}

internal val LlvmContext.i64 by cachedType {
    LlvmIntegerType(this, 64)
}

internal val LlvmContext.word by cachedType {
    LlvmIntegerType(this, LLVM.LLVMPointerSize(targetData) * 8)
}

internal val LlvmContext.any by cachedType(::AnyvalueType)
internal val LlvmContext.pointerToAnyValue by cachedType { LlvmPointerType(any) }
internal val LlvmContext.weakReferenceCollection by cachedType(::WeakReferenceCollectionType)
internal val LlvmContext.typeinfo by cachedType(::TypeinfoType)