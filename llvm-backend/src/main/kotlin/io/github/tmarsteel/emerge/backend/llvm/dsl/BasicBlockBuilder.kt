package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.getLlvmMessage
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
    fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: IntegerComparison, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType>
    fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>>
    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(function: LlvmValue<LlvmFunctionAddressType>, functionType: LlvmFunctionType<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T>
    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean = false)
    fun ret(value: LlvmValue<R>): Termination

    fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: Branch<C, R>.() -> Termination,
        ifFalse: (Branch<C, R>.() -> Termination)? = null
    )

    /**
     * Used to symbol that a terminal instruction has been built. There are two key facts about the [Termination] type:
     * * only [BasicBlockBuilderImpl] can instantiate this value
     * * it will only do so if you build one of the terminal instructions (e.g. [BasicBlockBuilderImpl.ret])
     * This assures that any code builder passed to [fill] will cleanly terminate the basic block.
     */
    sealed interface Termination {
        /**
         * @throws IllegalStateException if this termination did not originate from the given [builder]
         */
        fun checkIsFromBuilder(builder: BasicBlockBuilder<*, *>)
    }

    interface Branch<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /** transfers control flow to the basic block after the current branch. */
        fun concludeBranch(): Termination
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> fillBody(context: C, function: LlvmFunction<R>, code: CodeGenerator<C, R>) {
            val rawFn = function.address.raw
            val entryBlock = LLVM.LLVMAppendBasicBlockInContext(context.ref, rawFn, "entry")

            val builder = LLVM.LLVMCreateBuilderInContext(context.ref)
            LLVM.LLVMPositionBuilderAtEnd(builder, entryBlock)
            try {
                val dslBuilder = BasicBlockBuilderImpl<C, R>(context, rawFn, builder)
                val termination = dslBuilder.code()
                termination.checkIsFromBuilder(dslBuilder)
            }
            finally {
                LLVM.LLVMDisposeBuilder(builder)
            }
        }

        fun BasicBlockBuilder<*, LlvmVoidType>.retVoid(): Termination {
            LLVM.LLVMBuildRetVoid(builder)
            return TerminationImpl(this)
        }
    }
}

private open class BasicBlockBuilderImpl<C : LlvmContext, R : LlvmType>(
    override val context: C,
    val owningFunction: LLVMValueRef,
    override val builder: LLVMBuilderRef,
) : BasicBlockBuilder<C, R> {
    private val tmpVars = NameScope("tmp")

    private var terminated = false
    protected fun markTerminated() {
        check(!terminated) {
            "You are trying to terminate a single basic block more than once, this is illegal."
        }
        terminated = true
    }
    protected fun checkNotTerminated() {
        check(!terminated) {
            "This basic has already been terminated, cannot add any more instructions"
        }
    }

    override fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType>
    ): GetElementPointerStep<BasePointee> {
        return GetElementPointerStep.initial(base, index)
    }

    override fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
        checkNotTerminated()

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
        checkNotTerminated()

        val loadResult = LLVM.LLVMBuildLoad2(builder, type.pointed.getRawInContext(context), raw, tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    override fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        checkNotTerminated()

        LLVM.LLVMBuildStore(builder, value.raw, to.raw)
    }

    override fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        checkNotTerminated()

        val addInstr = LLVM.LLVMBuildAdd(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(addInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        checkNotTerminated()

        val subInstr = LLVM.LLVMBuildSub(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(subInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: IntegerComparison, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType> {
        checkNotTerminated()

        val cmpInstr = LLVM.LLVMBuildICmp(builder, type.numeric, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(cmpInstr, LlvmBooleanType)
    }

    override fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>> {
        checkNotTerminated()

        val ptr = LLVM.LLVMBuildAlloca(builder, type.getRawInContext(context), tmpVars.next())
        return LlvmValue(ptr, LlvmPointerType(type))
    }

    override fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        require(function.parameterTypes.size == args.size) {
            "The function ${getLlvmMessage(LLVM.LLVMGetValueName(function.address.raw))} takes ${function.parameterTypes.size} parameters, ${args.size} arguments given."
        }
        checkNotTerminated()

        val name = if (function.returnType == LlvmVoidType) "" else tmpVars.next()

        val argsArray = args.map { it.raw }.toTypedArray()
        val argsPointerPointer = PointerPointer(*argsArray)
        val result = LLVM.LLVMBuildCall2(
            builder,
            function.rawFunctionType,
            function.address.raw,
            argsPointerPointer,
            args.size,
            name,
        )

        return LlvmValue(result, function.returnType)
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
        checkNotTerminated()

        val inst = LLVM.LLVMBuildPtrToInt(builder, pointer.raw, integerType.getRawInContext(context), tmpVars.next())
        return LlvmValue(inst, integerType)
    }

    override fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean) {
        checkNotTerminated()

        // TODO: alignment; 1 is bad
        val inst = LLVM.LLVMBuildMemCpy(builder, destination.raw, 1, source.raw, 1, nBytes.raw)
        LLVM.LLVMSetVolatile(inst, if (volatile) 1 else 0)
    }

    override fun ret(value: LlvmValue<R>): BasicBlockBuilder.Termination {
        markTerminated()

        LLVM.LLVMBuildRet(builder, value.raw)

        return TerminationImpl(this)
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
        thenTermination.checkIsFromBuilder(thenBranchBuilder)

        if (ifFalse != null) {
            LLVM.LLVMPositionBuilderAtEnd(builder, elseBlock)
            val elseBranchBuilder = BranchImpl<C, R>(context, owningFunction, builder, continueBlock)
            val elseTermination = elseBranchBuilder.ifFalse()
            elseTermination.checkIsFromBuilder(elseBranchBuilder)
        }

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
        markTerminated()

        LLVM.LLVMBuildBr(builder, continueBlock)
        return TerminationImpl(this)
    }
}

private class TerminationImpl(val fromBuilder: BasicBlockBuilder<*, *>) : BasicBlockBuilder.Termination {
    override fun checkIsFromBuilder(builder: BasicBlockBuilder<*, *>) {
        require(fromBuilder === builder) {
            "The code generator returned a termination token from a different builder. Something is seriously off in the generator code!"
        }
    }
}

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

/*
fun loop(
        header: LoopHeader<C, R>.() -> Termination,
        body: LoopBody<C, R>.() -> Termination,
    )

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
 */