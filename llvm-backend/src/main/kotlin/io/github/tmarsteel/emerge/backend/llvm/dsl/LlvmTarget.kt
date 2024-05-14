package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.ptr.PointerByReference
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmCodeGenOptModel
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmCodeModel
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmRelocMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTargetRef

class LlvmTarget private constructor(
    val triple: String,
    internal val ref: LlvmTargetRef,
) {
    val name: String by lazy { Llvm.LLVMGetTargetName(ref) }

    fun createTargetMachine(): LlvmTargetMachine {
        val ref = Llvm.LLVMCreateTargetMachine(
            ref,
            triple,
            "generic",
            "",
            LlvmCodeGenOptModel.DEFAULT,
            LlvmRelocMode.POSITION_INDEPENDENT,
            LlvmCodeModel.SMALL,
        )
        return LlvmTargetMachine(ref)
    }

    companion object {
        fun fromTriple(triple: String): LlvmTarget {
            val data = PointerByReference()
            val error = PointerByReference()
            if (Llvm.LLVMGetTargetFromTriple(triple, data, error) != 0) {
                val errorStr = error.value.getString(0)
                Llvm.LLVMDisposeMessage(error.value)
                throw IllegalArgumentException(errorStr)
            }

            val targetRef = LlvmTargetRef(data.value)
            return LlvmTarget(triple, targetRef)
        }
    }
}