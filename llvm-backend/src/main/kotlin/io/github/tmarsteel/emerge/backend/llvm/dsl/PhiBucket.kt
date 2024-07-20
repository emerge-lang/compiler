package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBasicBlockRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray

class PhiBucket<E : LlvmType>(val type: E) {
    private val branches = ArrayList<LlvmBasicBlockRef>()
    private val results = ArrayList<LlvmValueRef>()

    private var built = false

    context(BasicBlockBuilder<*, *>)
    fun setBranchResult(result: LlvmValue<E>) {
        check(!built) {
            // is that actually true? Could be that just calling LLVMAddIncoming again will do the trick
            // look into extending this code if you encounter this error
            "phi node is already built, cannot add more branch results"
        }
        assert(result.isLlvmAssignableTo(this.type))
        branches.add(Llvm.LLVMGetInsertBlock(builder))
        results.add(result.raw)
    }

    context(BasicBlockBuilder<*, *>)
    fun buildPhi(): LlvmValue<E> {
        check(!built) {
            // that is likely possible, but not needed as of now
            // look into extending this code if you encounter this error
            "cannot build two phi nodes from the same PhiBucket"
        }
        built = true

        check(branches.isNotEmpty()) {
            "phi node with no incoming values"
        }

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