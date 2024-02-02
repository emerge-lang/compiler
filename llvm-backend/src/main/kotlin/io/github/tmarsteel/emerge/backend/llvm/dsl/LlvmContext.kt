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
    val void: LlvmVoidType
    val rawPointer: LLVMTypeRef
    val opaquePointer: LlvmPointerType<LlvmVoidType>
    val functionAddress: LlvmFunctionAddressType

    fun <T : LlvmType> cachedType(name: String, builder: LlvmContext.() -> T): T

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
    override val void = LlvmVoidType(this)
    override val rawPointer: LLVMTypeRef = LLVM.LLVMPointerTypeInContext(ref, 0)
    override val opaquePointer: LlvmPointerType<LlvmVoidType> = LlvmPointerType(void)
    override val functionAddress = LlvmFunctionAddressType(this)

    private val typesWithHandle = HashMap<LlvmContext.() -> LlvmType, LlvmType>()
    override fun <T : LlvmType> cachedType(name: String, builder: LlvmContext.() -> T): T {
        @Suppress("UNCHECKED_CAST")
        typesWithHandle[builder]?.let { return it as T }
        val type = builder(this)
        typesWithHandle[builder] = type
        return type
    }

    override fun close() {
        LLVM.LLVMDisposeModule(module)
        LLVM.LLVMContextDispose(ref)
    }
}