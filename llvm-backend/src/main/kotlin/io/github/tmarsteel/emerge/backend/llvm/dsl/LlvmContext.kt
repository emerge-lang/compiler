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

    private val initializerFunctions = ArrayList<LlvmFunction<LlvmVoidType>>()
    fun addModuleInitFunction(initializer: LlvmFunction<LlvmVoidType>) {
        initializerFunctions.add(initializer)
    }

    fun <T : LlvmType> addGlobal(initialValue: LlvmConstant<T>, mode: LlvmThreadLocalMode): LlvmGlobal<T> {
        val name = globalsScope.next()
        val rawRef = Llvm.LLVMAddGlobal(module, initialValue.type.getRawInContext(this), name)
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

    open fun complete() {
        val arrayType = LlvmArrayType(initializerFunctions.size.toLong(), LlvmGlobalCtorEntry)
        val ctorsGlobal = Llvm.LLVMAddGlobal(module, arrayType.getRawInContext(this), "llvm.global_ctors")
        val ctorsData = arrayType.buildConstantIn(this, initializerFunctions.mapIndexed { initializerIndex, initializer ->
            LlvmGlobalCtorEntry.buildConstantIn(this) {
                setValue(LlvmGlobalCtorEntry.priority, i32(initializerIndex))
                setValue(LlvmGlobalCtorEntry.function, initializer.address)
                setNull(LlvmGlobalCtorEntry.data)
            }
        })
        Llvm.LLVMSetInitializer(ctorsGlobal, ctorsData.raw)
        Llvm.LLVMSetLinkage(ctorsGlobal, LlvmLinkage.APPENDING)
    }

    override fun close() {
        Llvm.LLVMDisposeModule(module)
        Llvm.LLVMContextDispose(ref)
    }
}