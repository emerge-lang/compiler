package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMContextRef
import org.bytedeco.llvm.LLVM.LLVMModuleRef
import org.bytedeco.llvm.LLVM.LLVMTargetDataRef
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

interface LlvmContext {
    val ref: LLVMContextRef
    val module: LLVMModuleRef
    val targetData: LLVMTargetDataRef
    val rawPointer: LLVMTypeRef
    val opaquePointer: LlvmPointerType<LlvmVoidType>
    val globalsScope: NameScope

    fun <T : LlvmType> nullValue(type: T): LlvmValue<T> = LlvmValue(
        LLVM.LLVMConstNull(type.getRawInContext(this)),
        type,
    )

    companion object {
        fun createDoAndDispose(targetTriple: String, action: (LlvmContext) -> Unit) {
            return LlvmContextImpl(targetTriple).use(action)
        }
    }
}

private class LlvmContextImpl(val targetTriple: String) : LlvmContext, AutoCloseable {
    override val ref = LLVM.LLVMContextCreate()
    override val module = LLVM.LLVMModuleCreateWithName("app")
    init {
        LLVM.LLVMSetTarget(module, targetTriple)
    }
    override val targetData = LLVM.LLVMGetModuleDataLayout(module)
    override val rawPointer = LLVM.LLVMPointerTypeInContext(ref, 0)
    override val opaquePointer: LlvmPointerType<LlvmVoidType> = LlvmPointerType(LlvmVoidType)
    override val globalsScope = NameScope("global")

    override fun close() {
        LLVM.LLVMDisposeModule(module)
        LLVM.LLVMContextDispose(ref)
    }
}