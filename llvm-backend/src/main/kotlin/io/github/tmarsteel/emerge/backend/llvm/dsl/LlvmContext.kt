package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

open class LlvmContext(val target: LlvmTarget) : AutoCloseable {
    val ref = LLVM.LLVMContextCreate()
    val module = LLVM.LLVMModuleCreateWithNameInContext("app", ref)
    val targetMachine = target.createTargetMachine()
    val targetData = targetMachine.targetData
    init {
        LLVM.LLVMSetTarget(module, target.triple)
        LLVM.LLVMSetModuleDataLayout(module, targetData.ref)
    }
    val rawPointer = LLVM.LLVMPointerTypeInContext(ref, 0)
    val globalsScope = NameScope("global")

    fun <T : LlvmType> nullValue(type: T): LlvmConstant<T> = LlvmConstant(
        LLVM.LLVMConstNull(type.getRawInContext(this)),
        type,
    )

    fun <T : LlvmType> undefValue(type: T): LlvmConstant<T> = LlvmConstant(
        LLVM.LLVMGetUndef(type.getRawInContext(this)),
        type,
    )

    fun <T : LlvmType> addGlobal(initialValue: LlvmConstant<T>, mode: LlvmGlobal.ThreadLocalMode): LlvmGlobal<T> {
        val name = globalsScope.next()
        val rawRef = LLVM.LLVMAddGlobal(module, initialValue.type.getRawInContext(this), name)
        val allocation = LlvmGlobal(rawRef, initialValue.type)
        LLVM.LLVMSetThreadLocalMode(rawRef, mode.llvmKindValue)
        LLVM.LLVMSetInitializer(rawRef, initialValue.raw)
        LLVM.LLVMSetUnnamedAddress(rawRef, LLVM.LLVMGlobalUnnamedAddr)
        LLVM.LLVMSetLinkage(rawRef, LLVM.LLVMPrivateLinkage)
        return allocation
    }

    override fun close() {
        LLVM.LLVMDisposeModule(module)
        LLVM.LLVMContextDispose(ref)
    }
}