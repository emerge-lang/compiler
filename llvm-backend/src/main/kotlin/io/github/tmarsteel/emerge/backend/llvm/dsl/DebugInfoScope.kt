package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import java.nio.file.Path

sealed interface DebugInfoScope {
    val ref: LlvmMetadataRef

    interface Locatable : DebugInfoScope

    class File internal constructor(override val ref: LlvmMetadataRef, val path: Path) : DebugInfoScope {
        override fun toString() = "file $path"
    }
    class CompileUnit internal constructor(override val ref: LlvmMetadataRef, val name: String) : DebugInfoScope {
        override fun toString() = "compilation unit $name"
    }
    class Function internal constructor(override val ref: LlvmMetadataRef, val name: String): Locatable {
        override fun toString() = "function $name"
    }
}