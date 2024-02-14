package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

class PassBuilderOptions : AutoCloseable {
    val ref = LLVM.LLVMCreatePassBuilderOptions()

    fun setDebugLogging(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetDebugLogging(ref, if(value) 1 else 0)
    }

    fun seLoopInterleaving(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetLoopInterleaving(ref, if (value) 1 else 0)
    }

    fun seLoopVectorization(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetLoopVectorization(ref, if (value) 1 else 0)
    }

    fun setSLPVectorization(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetSLPVectorization(ref, if (value) 1 else 0)
    }

    fun setLoopUnrolling(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetLoopUnrolling(ref, if (value) 1 else 0)
    }

    fun setForgetAllSCEVInLoopUnroll(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetForgetAllSCEVInLoopUnroll(ref, if (value) 1 else 0)
    }

    fun setLicmMssaOptCap(value: UInt) {
        LLVM.LLVMPassBuilderOptionsSetLicmMssaOptCap(ref, value.toInt())
    }

    fun setLicmMssaNoAccForPromotionCap(value: UInt) {
        LLVM.LLVMPassBuilderOptionsSetLicmMssaNoAccForPromotionCap(ref, value.toInt())
    }

    fun setCallGraphProfile(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetCallGraphProfile(ref, if (value) 1 else 0)
    }

    fun setMergeFunctions(value: Boolean) {
        LLVM.LLVMPassBuilderOptionsSetMergeFunctions(ref, if (value) 1 else 0)
    }

    fun setInlinerThreshold(value: Int) {
        LLVM.LLVMPassBuilderOptionsSetInlinerThreshold(ref, value)
    }
    
    override fun close() {
        LLVM.LLVMDisposePassBuilderOptions(ref)
    }
}