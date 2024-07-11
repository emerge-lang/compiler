package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmLinkage
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmModuleFlagBehavior
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmUnnamedAddr

open class LlvmContext(val target: LlvmTarget) : AutoCloseable {
    val ref = Llvm.LLVMContextCreate()
    /* todo: rename to moduleRef */
    val module = Llvm.LLVMModuleCreateWithNameInContext("app", ref)
    val targetMachine = target.createTargetMachine()
    val targetData = targetMachine.targetData
    init {
        Llvm.LLVMSetTarget(module, target.triple)
        Llvm.LLVMSetModuleDataLayout(module, targetData.ref)
    }
    val rawPointer = Llvm.LLVMPointerTypeInContext(ref, 0)
    val globalsScope = NameScope("global")

    fun <T : LlvmType> nullValue(type: T): LlvmConstant<T> = LlvmConstant(
        Llvm.LLVMConstNull(type.getRawInContext(this)),
        type,
    )

    fun <T : LlvmType> undefValue(type: T): LlvmConstant<T> = LlvmConstant(
        Llvm.LLVMGetUndef(type.getRawInContext(this)),
        type,
    )

    fun <T : LlvmType> poisonValue(type: T): LlvmConstant<T> = LlvmConstant(
        Llvm.LLVMGetPoison(type.getRawInContext(this)),
        type,
    )

    fun <T : LlvmType> addGlobal(
        initialValue: LlvmConstant<T>,
        mode: LlvmThreadLocalMode,
        name: String? = null,
    ): LlvmGlobal<T> {
        val rawRef = Llvm.LLVMAddGlobal(
            module,
            initialValue.type.getRawInContext(this),
            name ?: globalsScope.next(),
        )
        val allocation = LlvmGlobal(rawRef, initialValue.type)
        Llvm.LLVMSetThreadLocalMode(rawRef, mode)
        Llvm.LLVMSetInitializer(rawRef, initialValue.raw)
        Llvm.LLVMSetUnnamedAddress(rawRef, LlvmUnnamedAddr.GLOBAL_UNNAMED_ADDR)
        Llvm.LLVMSetLinkage(rawRef, LlvmLinkage.PRIVATE)
        return allocation
    }

    fun addModuleFlag(behavior: LlvmModuleFlagBehavior, id: String, value: LlvmMetadataRef) {
        val idBytes = id.toByteArray(Charsets.UTF_8)
        Llvm.LLVMAddModuleFlag(module, behavior, idBytes, NativeLong(idBytes.size.toLong()), value)
    }

    fun getNamedFunctionAddress(name: String): LlvmConstant<LlvmFunctionAddressType>? {
        val raw = Llvm.LLVMGetNamedFunction(module, name) ?: return null
        return LlvmConstant(raw, LlvmFunctionAddressType)
    }

    override fun close() {
        Llvm.LLVMDisposeModule(module)
        Llvm.LLVMContextDispose(ref)
    }
}