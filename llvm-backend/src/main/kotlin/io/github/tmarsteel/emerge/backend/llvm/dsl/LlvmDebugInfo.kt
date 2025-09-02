package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import java.nio.file.Path

interface LlvmDebugInfo {
    interface Scope {
        val ref: LlvmMetadataRef

        class File internal constructor(override val ref: LlvmMetadataRef, val path: Path) : Scope {
            override fun toString() = "file $path"
        }
        class CompileUnit internal constructor(override val ref: LlvmMetadataRef, val name: String) : Scope {
            override fun toString() = "compilation unit $name"
        }
        class Function internal constructor(override val ref: LlvmMetadataRef, val name: String): Scope {
            override fun toString() = "function $name"
        }
        class LexicalBlock internal constructor(override val ref: LlvmMetadataRef) : Scope {
            override fun toString()= "lexical block"
        }
    }

    @JvmInline
    value class SubroutineType(val ref: LlvmMetadataRef)

    @JvmInline
    value class Type(val ref: LlvmMetadataRef) {
        val sizeInBits: ULong get() = Llvm.LLVMDITypeGetSizeInBits(ref).toULong()
        val alignInBits: UInt get() = Llvm.LLVMDITypeGetAlignInBits(ref).toUInt()
    }

    @JvmInline
    value class StructMember(val ref: LlvmMetadataRef)

    @JvmInline
    value class Location(val ref: LlvmMetadataRef)

    @JvmInline
    value class LocalVariable(val ref: LlvmMetadataRef)

    @JvmInline
    value class Expression(val ref: LlvmMetadataRef)
}