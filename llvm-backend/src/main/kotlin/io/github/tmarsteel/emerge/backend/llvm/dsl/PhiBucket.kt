package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBasicBlockRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray

class PhiBucket<E : LlvmType>(val type: E) {
    private val branches = ArrayList<LlvmBasicBlockRef>()
    private val results = ArrayList<LlvmValueRef>()

    context(BasicBlockBuilder<*, *>)
    fun setBranchResult(result: LlvmValue<E>) {
        assert(result.type == type)
        branches.add(Llvm.LLVMGetInsertBlock(builder))
        results.add(result.raw)
    }

    context(BasicBlockBuilder<*, *>)
    fun buildPhi(): LlvmValue<E> {
        val phiInst = Llvm.LLVMBuildPhi(builder, type.getRawInContext(context), "result")

        NativePointerArray.fromJavaPointers(branches).use { incomingBranches ->
            NativePointerArray.fromJavaPointers(results).use { incomingValues ->
                check(incomingBranches.length == incomingValues.length)
                Llvm.LLVMAddIncoming(phiInst, incomingValues, incomingBranches, incomingBranches.length)
            }
        }

        return LlvmValue(phiInst, type)
    }
}