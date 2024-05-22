package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef

sealed interface DebugInfoScope {
    val ref: LlvmMetadataRef

    interface Locatable : DebugInfoScope

    class File internal constructor(override val ref: LlvmMetadataRef) : DebugInfoScope
    class CompileUnit internal constructor(override val ref: LlvmMetadataRef) : DebugInfoScope
    class Function internal constructor(override val ref: LlvmMetadataRef): Locatable
}