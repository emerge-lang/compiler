package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.BytePointer
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTargetRef
import org.bytedeco.llvm.global.LLVM

class LlvmTarget private constructor(
    private val triple: String,
    internal val ref: LLVMTargetRef,
) {
    val name: String by lazy {
        LLVM.LLVMGetTargetName(ref).string
    }

    fun createTargetMachine(): LlvmTargetMachine {
        val ref = LLVM.LLVMCreateTargetMachine(
            ref,
            triple,
            "generic",
            "",
            LLVM.LLVMCodeGenLevelDefault,
            RelocationModel.PIC.numeric,
            CodeModel.SMALL.numeric
        )
        return LlvmTargetMachine(ref)
    }

    companion object {
        fun fromTriple(triple: String): LlvmTarget {
            val dataBuffer = PointerPointer<LLVMTargetRef>(1)
            val errorBuffer = BytePointer(1024)
            if (LLVM.LLVMGetTargetFromTriple(triple, dataBuffer, errorBuffer) != 0) {
                throw IllegalArgumentException(errorBuffer.string)
            }

            val targetRef = dataBuffer.get(LLVMTargetRef::class.java, 0L)
            return LlvmTarget(triple, targetRef)
        }
    }
}