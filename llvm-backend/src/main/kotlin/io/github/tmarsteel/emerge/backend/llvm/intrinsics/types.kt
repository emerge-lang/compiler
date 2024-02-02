package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmLeafType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import org.bytedeco.llvm.global.LLVM

internal val LlvmContext.boolean: LlvmType
    get() = cachedType {
        LlvmLeafType(this, LLVM.LLVMInt1TypeInContext(ref))
    }

internal val LlvmContext.i8
    get() = cachedType {
        LlvmIntegerType(this, 16)
    }

internal val LlvmContext.i16
    get() = cachedType {
        LlvmIntegerType(this, 16)
    }

internal val LlvmContext.i32
    get() = cachedType {
        LlvmIntegerType(this, 32)
    }

internal val LlvmContext.i64
    get() = cachedType {
        LlvmIntegerType(this, 64)
    }

internal val LlvmContext.word
    get() = cachedType {
        LlvmIntegerType(this, LLVM.LLVMPointerSize(targetData) * 8)
    }

internal val LlvmContext.any get() = cachedType { AnyvalueType(this) }
internal val LlvmContext.pointerToAnyValue get() = cachedType { LlvmPointerType(any) }
internal val LlvmContext.weakReferenceCollection get() = cachedType { WeakReferenceCollectionType(this) }