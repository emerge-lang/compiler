package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef

sealed class DebugInfoScope(val ref: LlvmMetadataRef) {
    class File internal constructor(ref: LlvmMetadataRef) : DebugInfoScope(ref)
    class CompileUnit internal constructor(ref: LlvmMetadataRef, val file: File) : DebugInfoScope(ref)
    class Function internal constructor(ref: LlvmMetadataRef): DebugInfoScope(ref)
}