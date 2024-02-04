package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.i32
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMBasicBlockRef
import org.bytedeco.llvm.global.LLVM

class BasicBlockBuilder private constructor(
    private val context: LlvmContext,
    private val basicBlock: LLVMBasicBlockRef,
) : LlvmContext by context, AutoCloseable {
    private val builder = LLVM.LLVMCreateBuilder()
    private val tmpVars = TempVarsScope()
    init {
        LLVM.LLVMPositionBuilderAtEnd(builder, basicBlock)
    }

    fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType> = base.type.context.i32(0)
    ): GetElementPointerStep<BasePointee> {
        return GetElementPointerStep.initial(base, index)
    }

    fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
        val (basePointer, indices, resultPointeeType) = completeAndGetData()
        val indicesRaw = PointerPointer(*indices.toTypedArray())
        val instruction = LLVM.LLVMBuildGEP2(
            builder,
            basePointer.type.pointed.raw,
            basePointer.raw,
            indicesRaw,
            indices.size,
            tmpVars.next(),
        )
        return LlvmValue(instruction, LlvmPointerType(resultPointeeType))
    }

    fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P> {
        val loadResult = LLVM.LLVMBuildLoad2(builder, type.pointed.raw, raw, tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        LLVM.LLVMBuildStore(builder, value.raw, to.raw)
    }

    fun add(a: LlvmValue<LlvmIntegerType>, b: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmIntegerType> {
        check(a.type.nBits == b.type.nBits)
        val addInstr = LLVM.LLVMBuildAdd(builder, a.raw, b.raw, tmpVars.next())
        return LlvmValue(addInstr, a.type)
    }

    override fun close() {
        LLVM.LLVMDisposeBuilder(builder)
    }

    companion object {
        fun appendToUnsafe(context: LlvmContext, block: LLVMBasicBlockRef, code: (BasicBlockBuilder) -> Unit) {
            BasicBlockBuilder(context, block).use(code)
        }

        fun <ReturnType : LlvmType> appendToWithReturn(context: LlvmContext, block: LLVMBasicBlockRef, code: BasicBlockBuilder.() -> LlvmValue<ReturnType>) {
            BasicBlockBuilder(context, block).use {
                val returnValue = it.code()
                LLVM.LLVMBuildRet(it.builder, returnValue.raw)
            }
        }
    }
}

private class TempVarsScope {
    private var counter: ULong = 0u

    fun next(): String {
        return "tmp${counter++}"
    }
}