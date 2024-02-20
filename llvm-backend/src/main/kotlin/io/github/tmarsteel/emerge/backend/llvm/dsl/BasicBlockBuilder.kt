package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.getLlvmMessage
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMBasicBlockRef
import org.bytedeco.llvm.LLVM.LLVMBuilderRef
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

interface BasicBlockBuilder<C : LlvmContext, R : LlvmType> {
    val context: C
    val builder: LLVMBuilderRef
    fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType> = context.i32(0)
    ): GetElementPointerStep<BasePointee>

    fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>>
    fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P>
    fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>)
    fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> mul(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: IntegerComparison, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType>
    fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>>
    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(function: LlvmValue<LlvmFunctionAddressType>, functionType: LlvmFunctionType<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T>
    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean = false)
    fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun not(value: LlvmValue<LlvmBooleanType>): LlvmValue<LlvmBooleanType>
    fun ret(value: LlvmValue<R>): Termination

    fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: Branch<C, R>.() -> Termination,
        ifFalse: (Branch<C, R>.() -> Termination)? = null
    )

    fun loop(
        header: LoopHeader<C, R>.() -> Termination,
        body: LoopBody<C, R>.() -> Termination,
    )

    /**
     * Used to symbol that a terminal instruction has been built. There are two key facts about the [Termination] type:
     * * only [BasicBlockBuilderImpl] can instantiate this value
     * * it will only do so if you build one of the terminal instructions (e.g. [BasicBlockBuilderImpl.ret])
     * This assures that any code builder passed to [fill] will cleanly terminate the basic block.
     */
    sealed interface Termination

    interface Branch<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /** transfers control flow to the basic block after the current branch. */
        fun concludeBranch(): Termination
    }

    interface AbstractLoop<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /**
         * Transfers control flow to the code after the loop
         */
        fun breakLoop(): Termination
    }

    interface LoopHeader<C : LlvmContext, R : LlvmType> : AbstractLoop<C, R> {
        /** starts the next iteration of the loop by transferring control flow to the loop body. */
        fun doIteration(): Termination
    }

    interface LoopBody<C : LlvmContext, R : LlvmType> : AbstractLoop<C, R> {
        /** Transfers control flow back to the loop header. */
        fun loopContinue(): Termination
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> fillBody(context: C, function: LlvmFunction<R>, code: CodeGenerator<C, R>) {
            val rawFn = function.address.raw
            val entryBlock = LLVM.LLVMAppendBasicBlockInContext(context.ref, rawFn, "entry")

            val builder = LLVM.LLVMCreateBuilderInContext(context.ref)
            LLVM.LLVMPositionBuilderAtEnd(builder, entryBlock)
            try {
                val dslBuilder = BasicBlockBuilderImpl<C, R>(context, rawFn, builder)
                dslBuilder.code()
            }
            finally {
                LLVM.LLVMDisposeBuilder(builder)
            }
        }

        fun BasicBlockBuilder<*, LlvmVoidType>.retVoid(): Termination {
            LLVM.LLVMBuildRetVoid(builder)
            return TerminationImpl
        }
    }
}

private open class BasicBlockBuilderImpl<C : LlvmContext, R : LlvmType>(
    override val context: C,
    val owningFunction: LLVMValueRef,
    override val builder: LLVMBuilderRef,
) : BasicBlockBuilder<C, R> {
    private val tmpVars = NameScope("tmp")

    override fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType>
    ): GetElementPointerStep<BasePointee> {
        return GetElementPointerStep.initial(base, index)
    }

    override fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
        val (basePointer, indices, resultPointeeType) = completeAndGetData()
        val indicesRaw = PointerPointer(*indices.toTypedArray())
        val instruction = LLVM.LLVMBuildGEP2(
            builder,
            basePointer.type.pointed.getRawInContext(context),
            basePointer.raw,
            indicesRaw,
            indices.size,
            tmpVars.next(),
        )
        return LlvmValue(instruction, LlvmPointerType(resultPointeeType))
    }

    override fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P> {
        val loadResult = LLVM.LLVMBuildLoad2(builder, type.pointed.getRawInContext(context), raw, tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    override fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        LLVM.LLVMBuildStore(builder, value.raw, to.raw)
    }

    override fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val addInstr = LLVM.LLVMBuildAdd(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(addInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val subInstr = LLVM.LLVMBuildSub(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(subInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> mul(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val mulInstr = LLVM.LLVMBuildMul(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(mulInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: IntegerComparison, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType> {
        val cmpInstr = LLVM.LLVMBuildICmp(builder, type.numeric, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(cmpInstr, LlvmBooleanType)
    }

    override fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>> {
        val ptr = LLVM.LLVMBuildAlloca(builder, type.getRawInContext(context), tmpVars.next())
        return LlvmValue(ptr, LlvmPointerType(type))
    }

    override fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        require(function.type.parameterTypes.size == args.size) {
            "The function ${getLlvmMessage(LLVM.LLVMGetValueName(function.address.raw))} takes ${function.type.parameterTypes.size} parameters, ${args.size} arguments given."
        }

        val name = if (function.type.returnType == LlvmVoidType) "" else tmpVars.next()

        val argsArray = args.map { it.raw }.toTypedArray()
        val argsPointerPointer = PointerPointer(*argsArray)
        val result = LLVM.LLVMBuildCall2(
            builder,
            function.rawType,
            function.address.raw,
            argsPointerPointer,
            args.size,
            name,
        )

        return LlvmValue(result, function.type.returnType)
    }

    override fun <R : LlvmType> call(
        function: LlvmValue<LlvmFunctionAddressType>,
        functionType: LlvmFunctionType<R>,
        args: List<LlvmValue<*>>
    ): LlvmValue<R> {
        val argsRaw = args.map { it.raw }.toTypedArray()
        val callInst = LLVM.LLVMBuildCall2(
            builder,
            functionType.getRawInContext(context),
            function.raw,
            PointerPointer(*argsRaw),
            argsRaw.size,
            if (functionType.returnType == LlvmVoidType) "" else tmpVars.next(),
        )

        return LlvmValue(callInst, functionType.returnType)
    }

    override fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T> {
        val inst = LLVM.LLVMBuildPtrToInt(builder, pointer.raw, integerType.getRawInContext(context), tmpVars.next())
        return LlvmValue(inst, integerType)
    }

    override fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean) {
        // TODO: alignment; 1 is bad
        val inst = LLVM.LLVMBuildMemCpy(builder, destination.raw, 1, source.raw, 1, nBytes.raw)
        LLVM.LLVMSetVolatile(inst, if (volatile) 1 else 0)
    }

    override fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val asInt = LLVM.LLVMBuildPtrToInt(builder, pointer.raw, EmergeWordType.getRawInContext(context), tmpVars.next())
        val isNullInstr = LLVM.LLVMBuildICmp(builder, LLVM.LLVMIntEQ, asInt, context.word(0).raw, tmpVars.next())
        return LlvmValue(isNullInstr, LlvmBooleanType)
    }

    override fun not(value: LlvmValue<LlvmBooleanType>): LlvmValue<LlvmBooleanType> {
        val inst = LLVM.LLVMBuildNot(builder, value.raw, tmpVars.next())
        return LlvmValue(inst, LlvmBooleanType)
    }

    override fun ret(value: LlvmValue<R>): BasicBlockBuilder.Termination {
        LLVM.LLVMBuildRet(builder, value.raw)

        return TerminationImpl
    }

    override fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination,
        ifFalse: (BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination)?,
    ) {
        val branchName = tmpVars.next() + "_br"
        val thenBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${branchName}_then")
        lateinit var elseBlock: LLVMBasicBlockRef
        if (ifFalse != null) {
            elseBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${branchName}_else")
        }

        val continueBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${branchName}_cont")

        if (ifFalse != null) {
            LLVM.LLVMBuildCondBr(builder, condition.raw, thenBlock, elseBlock)
        } else {
            LLVM.LLVMBuildCondBr(builder, condition.raw, thenBlock, continueBlock)
        }

        LLVM.LLVMPositionBuilderAtEnd(builder, thenBlock)
        val thenBranchBuilder = BranchImpl<C, R>(context, owningFunction, builder, continueBlock)
        val thenTermination = thenBranchBuilder.ifTrue()

        if (ifFalse != null) {
            LLVM.LLVMPositionBuilderAtEnd(builder, elseBlock)
            val elseBranchBuilder = BranchImpl<C, R>(context, owningFunction, builder, continueBlock)
            val elseTermination = elseBranchBuilder.ifFalse()
        }

        LLVM.LLVMPositionBuilderAtEnd(builder, continueBlock)
        return
    }

    override fun loop(
        header: BasicBlockBuilder.LoopHeader<C, R>.() -> BasicBlockBuilder.Termination,
        body: BasicBlockBuilder.LoopBody<C, R>.() -> BasicBlockBuilder.Termination
    ) {
        val loopName = tmpVars.next() + "_loop"
        val headerBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${loopName}_header")
        val bodyBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${loopName}_body")
        val continueBlock = LLVM.LLVMAppendBasicBlock(owningFunction, "${loopName}_cont")

        LLVM.LLVMBuildBr(builder, headerBlock)

        LLVM.LLVMPositionBuilderAtEnd(builder, headerBlock)
        val headerDslBuilder = LoopImpl<C, R>(context, owningFunction, builder, headerBlock, bodyBlock, continueBlock)
        headerDslBuilder.header()

        LLVM.LLVMPositionBuilderAtEnd(builder, bodyBlock)
        val bodyDslBuilder = LoopImpl<C, R>(context, owningFunction, builder, headerBlock, bodyBlock, continueBlock)
        bodyDslBuilder.body()

        LLVM.LLVMPositionBuilderAtEnd(builder, continueBlock)
        return
    }
}

private class BranchImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    owningFunction: LLVMValueRef,
    builder: LLVMBuilderRef,
    val continueBlock: LLVMBasicBlockRef,
) : BasicBlockBuilderImpl<C, R>(context, owningFunction, builder), BasicBlockBuilder.Branch<C, R> {
    override fun concludeBranch(): BasicBlockBuilder.Termination {
        LLVM.LLVMBuildBr(builder, continueBlock)
        return TerminationImpl
    }
}

private class LoopImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    owningFunction: LLVMValueRef,
    builder: LLVMBuilderRef,
    val headerBlockRef: LLVMBasicBlockRef,
    val bodyBlockRef: LLVMBasicBlockRef,
    val continueBlock: LLVMBasicBlockRef,
) : BasicBlockBuilderImpl<C, R>(context, owningFunction, builder), BasicBlockBuilder.LoopHeader<C, R>, BasicBlockBuilder.LoopBody<C, R> {
    override fun breakLoop(): BasicBlockBuilder.Termination {
        LLVM.LLVMBuildBr(builder, continueBlock)
        return TerminationImpl
    }

    override fun doIteration(): BasicBlockBuilder.Termination {
        LLVM.LLVMBuildBr(builder, bodyBlockRef)
        return TerminationImpl
    }

    override fun loopContinue(): BasicBlockBuilder.Termination {
        LLVM.LLVMBuildBr(builder, headerBlockRef)
        return TerminationImpl
    }
}

private data object TerminationImpl : BasicBlockBuilder.Termination

typealias CodeGenerator<C, R> = BasicBlockBuilder<C, R>.() -> BasicBlockBuilder.Termination

enum class IntegerComparison(val numeric: Int) {
    EQUAL(LLVM.LLVMIntEQ),
    NOT_EQUAL(LLVM.LLVMIntNE),
    UNSIGNED_GREATER_THAN(LLVM.LLVMIntUGT),
    UNSIGNED_GREATER_THAN_OR_EQUAL(LLVM.LLVMIntUGE),
    UNSIGNED_LESS_THAN(LLVM.LLVMIntULT),
    UNSIGNED_LESS_THAN_OR_EQUAL(LLVM.LLVMIntULE),
    SIGNED_GREATER_THAN(LLVM.LLVMIntSGT),
    SIGNED_GREATER_THAN_OR_EQUAL(LLVM.LLVMIntSGE),
    SIGNED_LESS_THAN(LLVM.LLVMIntSLT),
    SIGNED_LESS_THAN_OR_EQUAL(LLVM.LLVMIntSLE),
}