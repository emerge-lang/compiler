package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm

class PassBuilderOptions : AutoCloseable {
    val ref = Llvm.LLVMCreatePassBuilderOptions()

    fun setDebugLogging(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetDebugLogging(ref, if(value) 1 else 0)
    }

    fun seLoopInterleaving(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetLoopInterleaving(ref, if (value) 1 else 0)
    }

    fun seLoopVectorization(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetLoopVectorization(ref, if (value) 1 else 0)
    }

    fun setSLPVectorization(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetSLPVectorization(ref, if (value) 1 else 0)
    }

    fun setLoopUnrolling(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetLoopUnrolling(ref, if (value) 1 else 0)
    }

    fun setForgetAllSCEVInLoopUnroll(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetForgetAllSCEVInLoopUnroll(ref, if (value) 1 else 0)
    }

    fun setLicmMssaOptCap(value: UInt) {
        Llvm.LLVMPassBuilderOptionsSetLicmMssaOptCap(ref, value.toInt())
    }

    fun setLicmMssaNoAccForPromotionCap(value: UInt) {
        Llvm.LLVMPassBuilderOptionsSetLicmMssaNoAccForPromotionCap(ref, value.toInt())
    }

    fun setCallGraphProfile(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetCallGraphProfile(ref, if (value) 1 else 0)
    }

    fun setMergeFunctions(value: Boolean) {
        Llvm.LLVMPassBuilderOptionsSetMergeFunctions(ref, if (value) 1 else 0)
    }

    fun setInlinerThreshold(value: Int) {
        Llvm.LLVMPassBuilderOptionsSetInlinerThreshold(ref, value)
    }
    
    override fun close() {
        Llvm.LLVMDisposePassBuilderOptions(ref)
    }
}