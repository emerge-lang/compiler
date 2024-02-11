package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

open class LlvmContext(val target: LlvmTarget) : AutoCloseable {
    val ref = LLVM.LLVMContextCreate()
    val module = LLVM.LLVMModuleCreateWithName("app")
    val targetMachine = target.createTargetMachine()
    val targetData = targetMachine.targetData
    init {
        LLVM.LLVMSetTarget(module, target.name)
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

    private val initializerFunctions = ArrayList<LlvmFunction<LlvmVoidType>>()
    fun addModuleInitFunction(initializer: LlvmFunction<LlvmVoidType>) {
        initializerFunctions.add(initializer)
    }

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

    open fun complete() {
        val arrayType = LlvmArrayType(initializerFunctions.size.toLong(), LlvmGlobalCtorEntry)
        val ctorsGlobal = LLVM.LLVMAddGlobal(module, arrayType.getRawInContext(this), "llvm.global_ctors")
        val ctorsData = arrayType.buildConstantIn(this, initializerFunctions.mapIndexed { initializerIndex, initializer ->
            LlvmGlobalCtorEntry.buildConstantIn(this) {
                setValue(LlvmGlobalCtorEntry.priority, i32(initializerIndex))
                setValue(LlvmGlobalCtorEntry.function, initializer.address)
                setNull(LlvmGlobalCtorEntry.data)
            }
        })
        LLVM.LLVMSetInitializer(ctorsGlobal, ctorsData.raw)
        LLVM.LLVMSetLinkage(ctorsGlobal, LLVM.LLVMAppendingLinkage)
    }

    override fun close() {
        LLVM.LLVMDisposeModule(module)
        LLVM.LLVMContextDispose(ref)
    }
}