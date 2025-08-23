package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBasicBlockRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBuilderRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.util.Stack

@DslMarker
annotation class LlvmBasicBlockDsl

/**
 * DSL for deferred code. Has limited capabilities:
 * * cannot terminate the basic block, including no return from the function
 * * cannot add further deferred statements
 */
@LlvmBasicBlockDsl
interface DeferScopeBasicBlockBuilder<C : LlvmContext> {
    val context: C
    val llvmRef: LlvmBuilderRef

    fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType> = context.s32(0)
    ): GetElementPointerStep<BasePointee>

    fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>>
    /** @param name Name for the LLVM temporary, auto-generates one if null */
    fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(name: String? = null): LlvmValue<P>
    fun <S : LlvmStructType, T : LlvmType> extractValue(struct: LlvmValue<S>, memberSelector: S.() -> LlvmStructType.Member<S, T>): LlvmValue<T>
    fun <S : LlvmStructType, T : LlvmType> insertValue(struct: LlvmValue<S>, value: LlvmValue<T>, memberSelector: S.() -> LlvmStructType.Member<S, T>): LlvmValue<S>

    fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>)
    fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> mul(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> sdiv(lhs: LlvmValue<T>, rhs: LlvmValue<T>, knownToBeExact: Boolean = false): LlvmValue<T>
    fun <T : LlvmIntegerType> udiv(lhs: LlvmValue<T>, rhs: LlvmValue<T>, knownToBeExact: Boolean = false): LlvmValue<T>
    fun <T : LlvmIntegerType> srem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> urem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: LlvmIntPredicate, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType>
    fun <T : LlvmIntegerType> shl(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> lshr(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> ashr(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> and(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> or(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> xor(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeUnsigned(value: LlvmValue<Small>, to: Large): LlvmValue<Large>
    fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeSigned(value: LlvmValue<Small>, to: Large): LlvmValue<Large>
    fun <Small : LlvmIntegerType, Large: LlvmIntegerType> truncate(value: LlvmValue<Large>, to: Small): LlvmValue<Small>
    /**
     * @param forceEntryBlock if true, the `alloca` instruction will be placed in the functions entry block. This greatly
     * helps the `mem2reg` LLVM pass optimize stack variables into register uses.
     * @param name Name for the LLVM temporary, auto-generates one if null
     */
    fun <T: LlvmType> alloca(type: T, forceEntryBlock: Boolean = true, name: String? = null): LlvmValue<LlvmPointerType<T>>
    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(function: LlvmValue<LlvmFunctionAddressType>, functionType: LlvmFunctionType<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(llvmIntrinsic: LlvmIntrinsic<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        return call(llvmIntrinsic.getRawInContext(context), args)
    }
    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T>
    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>)
    fun memset(destination: LlvmValue<LlvmPointerType<*>>, value: LlvmValue<LlvmS8Type>, nBytes: LlvmValue<LlvmIntegerType>)
    fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun isNotNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun isZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType>
    fun isNotZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType>
    fun isEq(pointerA: LlvmValue<LlvmPointerType<*>>, pointerB: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun <T : LlvmIntegerType> not(value: LlvmValue<T>): LlvmValue<T>

    fun <R : LlvmType> select(condition: LlvmValue<LlvmBooleanType>, ifTrue: LlvmValue<R>, ifFalse: LlvmValue<R>): LlvmValue<R>

    fun enterScope(scope: LlvmDebugInfo.Scope)
    fun leaveScope()
    fun markSourceLocation(line: UInt, column: UInt)
    fun currentDebugLocation(): String
    fun createAndEnterLexicalScope(): LlvmDebugInfo.Scope.LexicalBlock
    fun leaveLexicalScope(scope: LlvmDebugInfo.Scope.LexicalBlock)
}

/**
 * Full DSL for LLVM instructions
 */
@LlvmBasicBlockDsl
interface BasicBlockBuilder<C : LlvmContext, R : LlvmType> : DeferScopeBasicBlockBuilder<C> {
    val llvmFunctionReturnType: R

    /**
     * @param code will be executed when this scope is closed, either on a function-terminating instruction
     * or when a logical scope is completed (e.g. [conditionalBranch], [loop])
     */
    fun defer(code: DeferredCodeGenerator<C>)

    fun ret(value: LlvmValue<R>): Termination
    fun unreachable(): Termination

    /**
     * directly resembles an if-else from typical imperative languages
     */
    fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: Branch<C, R>.() -> Termination,
        ifFalse: (Branch<C, R>.() -> Termination)? = null,
        branchBlockName: String? = null,
    )

    /**
     * @param body is executed infinitely in a loop. Use [LoopBody.breakLoop] together with [conditionalBranch]
     * to implement loop latches for different kinds of source-program loops.
     */
    fun loop(body: LoopBody<C, R>.() -> Termination)

    /**
     * Creates a new basic block in the owning function. Then continues to fill the current basic block
     * with [prepare].
     * This is called "unsafe" because there is no guarantee that the resulting control flow graph is safe,
     * or even legal in terms of LLVM IR. The safe alternatives are [conditionalBranch] and [loop].
     *
     * @param prepare in kotlin runtime, is executed before [branch] so that it can create state for [branch]
     * to reference
     */
    fun unsafeBranch(
        prepare: UnsafeBranchPrepare<C, R>.() -> Termination,
        branch: Branch<C, R>.() -> Termination,
        branchBlockName: String? = null,
        resumeBlockName: String? = null,
    )

    /**
     * Used to symbol that a terminal instruction has been built. There are two key facts about the [Termination] type:
     * * only [BasicBlockBuilderImpl] can instantiate this value
     * * it will only do so if you build one of the terminal instructions (e.g. [BasicBlockBuilderImpl.ret])
     * This assures that any code builder passed to [fill] will cleanly terminate the basic block.
     */
    sealed interface Termination

    @LlvmBasicBlockDsl
    interface Branch<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /** transfers control flow to the basic block after the current branch. */
        fun concludeBranch(): Termination
    }

    @LlvmBasicBlockDsl
    interface UnsafeBranchPrepare<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /**
         * transfers control to the `branch` portion of the related [unsafeBranch] call.
         */
        fun jumpToUnsafeBranch(): Termination

        /**
         * transfers control back to after the call to [unsafeBranch], just like [Branch.concludeBranch]. The
         * unsafe branch is not taken.
         */
        fun skipUnsafeBranch(): Termination
    }

    @LlvmBasicBlockDsl
    interface LoopBody<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        /** Transfers control flow to the code after the loop */
        fun breakLoop(): Termination

        /** Transfers control flow back to the beginning of the looped code */
        fun loopContinue(): Termination
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> fillBody(
            context: C,
            function: LlvmFunction<R>,
            diBuilder: DiBuilder,
            diFunction: LlvmDebugInfo.Scope.Function,
            code: CodeGenerator<C, R>
        ) {
            val rawFn = function.address.raw
            val entryBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, rawFn, "entry")

            val scopeTracker = ScopeTracker<C>()
            val builder = Llvm.LLVMCreateBuilderInContext(context.ref)
            Llvm.LLVMPositionBuilderAtEnd(builder, entryBlock)
            try {
                val dslBuilder = BasicBlockBuilderImpl<C, R>(context, function.type.returnType, diBuilder, rawFn, builder, NameScope("tmp"), scopeTracker)
                dslBuilder.enterScope(diFunction)
                dslBuilder.code()
            }
            finally {
                Llvm.LLVMDisposeBuilder(builder)
            }
        }

        fun <C : LlvmContext> BasicBlockBuilder<C, LlvmVoidType>.retVoid(): Termination {
            with(this as BasicBlockBuilderImpl<C, *>) {
                this.scopeTracker.runAllFunctionDeferredCode()
            }
            Llvm.LLVMBuildRetVoid(llvmRef)
            return TerminationImpl
        }
    }
}

private open class BasicBlockBuilderImpl<C : LlvmContext, R : LlvmType>(
    override val context: C,
    override val llvmFunctionReturnType: R,
    val diBuilder: DiBuilder,
    val owningFunction: LlvmValueRef,
    override val llvmRef: LlvmBuilderRef,
    val tmpVars: NameScope,
    val scopeTracker: ScopeTracker<C>,
) : BasicBlockBuilder<C, R> {
    override fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType>
    ): GetElementPointerStep<BasePointee> {
        return GetElementPointerStep.initial(base, index)
    }

    override fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
        val (basePointer, indices, resultPointeeType) = completeAndGetData()
        val indicesRaw = NativePointerArray.fromJavaPointers(indices)
        val instruction = Llvm.LLVMBuildGEP2(
            llvmRef,
            basePointer.type.pointed.getRawInContext(context),
            basePointer.raw,
            indicesRaw,
            indicesRaw.length,
            tmpVars.next(),
        )
        return LlvmValue(instruction, LlvmPointerType(resultPointeeType))
    }

    override fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(name: String?): LlvmValue<P> {
        val loadResult = Llvm.LLVMBuildLoad2(llvmRef, type.pointed.getRawInContext(context), raw, name ?: tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    override fun <S : LlvmStructType, T : LlvmType> extractValue(
        struct: LlvmValue<S>,
        memberSelector: S.() -> LlvmStructType.Member<S, T>,
    ): LlvmValue<T> {
        val member = struct.type.memberSelector()
        val extractInst = Llvm.LLVMBuildExtractValue(llvmRef, struct.raw, member.indexInStruct, tmpVars.next())
        return LlvmValue(extractInst, member.type)
    }

    override fun <S : LlvmStructType, T : LlvmType> insertValue(
        struct: LlvmValue<S>,
        value: LlvmValue<T>,
        memberSelector: S.() -> LlvmStructType.Member<S, T>,
    ): LlvmValue<S> {
        val member = struct.type.memberSelector()
        val insertInst = Llvm.LLVMBuildInsertValue(llvmRef, struct.raw, value.raw, member.indexInStruct, tmpVars.next())
        return LlvmValue(insertInst, struct.type)
    }

    override fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        check(value.type !is LlvmVoidType) // LLVM segfaults if this doesn't hold
        Llvm.LLVMBuildStore(llvmRef, value.raw, to.raw)
    }

    override fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)
        val addInstr = Llvm.LLVMBuildAdd(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(addInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)
        val subInstr = Llvm.LLVMBuildSub(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(subInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> mul(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)
        val mulInstr = Llvm.LLVMBuildMul(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(mulInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sdiv(
        lhs: LlvmValue<T>,
        rhs: LlvmValue<T>,
        knownToBeExact: Boolean
    ): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val inst = if (knownToBeExact) {
            Llvm.LLVMBuildExactSDiv(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        } else {
            Llvm.LLVMBuildSDiv(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        }

        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> udiv(
        lhs: LlvmValue<T>,
        rhs: LlvmValue<T>,
        knownToBeExact: Boolean
    ): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val inst = if (knownToBeExact) {
            Llvm.LLVMBuildExactUDiv(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        } else {
            Llvm.LLVMBuildUDiv(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        }

        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> srem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val inst = Llvm.LLVMBuildSRem(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> urem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val inst = Llvm.LLVMBuildURem(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: LlvmIntPredicate, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType> {
        assert(lhs.type == rhs.type)

        val cmpInstr = Llvm.LLVMBuildICmp(llvmRef, type, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(cmpInstr, LlvmBooleanType)
    }

    override fun <T : LlvmIntegerType> shl(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T> {
        val shiftInstr = Llvm.LLVMBuildShl(llvmRef, value.raw, shiftAmount.raw, tmpVars.next())
        return LlvmValue(shiftInstr, value.type)
    }

    override fun <T : LlvmIntegerType> lshr(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T> {
        val shiftInstr = Llvm.LLVMBuildLShr(llvmRef, value.raw, shiftAmount.raw, tmpVars.next())
        return LlvmValue(shiftInstr, value.type)
    }

    override fun <T : LlvmIntegerType> ashr(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T> {
        val shiftInstr = Llvm.LLVMBuildAShr(llvmRef, value.raw, shiftAmount.raw, tmpVars.next())
        return LlvmValue(shiftInstr, value.type)
    }

    override fun <T : LlvmIntegerType> and(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val andInstr = Llvm.LLVMBuildAnd(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(andInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> or(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val orInstr = Llvm.LLVMBuildOr(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(orInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> xor(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        assert(lhs.type == rhs.type)

        val xorInst = Llvm.LLVMBuildXor(llvmRef, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(xorInst, lhs.type)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeSigned(
        value: LlvmValue<Small>,
        to: Large,
    ): LlvmValue<Large> {
        val sextInstr = Llvm.LLVMBuildSExt(llvmRef, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(sextInstr, to)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeUnsigned(
        value: LlvmValue<Small>,
        to: Large,
    ): LlvmValue<Large> {
        require(value.type.getNBitsInContext(context) <= to.getNBitsInContext(context))
        val zextInstr = Llvm.LLVMBuildZExt(llvmRef, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(zextInstr, to)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> truncate(
        value: LlvmValue<Large>,
        to: Small,
    ): LlvmValue<Small> {
        val truncInstr = Llvm.LLVMBuildTrunc(llvmRef, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(truncInstr, to)
    }

    override fun <T: LlvmType> alloca(type: T, forceEntryBlock: Boolean, name: String?): LlvmValue<LlvmPointerType<T>> {
        val switchBackToBlockAfter: LlvmBasicBlockRef?
        if (forceEntryBlock) {
            switchBackToBlockAfter = Llvm.LLVMGetInsertBlock(llvmRef)
            val entryBlock = Llvm.LLVMGetEntryBasicBlock(owningFunction)
            val firstInstruction = Llvm.LLVMGetFirstInstruction(entryBlock)
            if (firstInstruction != null) {
                Llvm.LLVMPositionBuilderBefore(llvmRef, firstInstruction)
            } else {
                Llvm.LLVMPositionBuilderAtEnd(llvmRef, entryBlock)
            }
        } else {
            switchBackToBlockAfter = null
        }
        val ptr = Llvm.LLVMBuildAlloca(llvmRef, type.getRawInContext(context), name ?: tmpVars.next())
        switchBackToBlockAfter?.let {
            Llvm.LLVMPositionBuilderAtEnd(llvmRef, it)
        }
        return LlvmValue(ptr, pointerTo(type))
    }

    override fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        require(function.type.parameterTypes.size == args.size) {
            "The function ${function.name} takes ${function.type.parameterTypes.size} parameters, ${args.size} arguments given."
        }
        args.zip(function.type.parameterTypes).forEachIndexed { index, (arg, paramType) ->
            require(arg.isLlvmAssignableTo(paramType)) {
                "argument #$index: ${arg.type} is not llvm-assignable to $paramType"
            }
        }

        val name = if (function.type.returnType == LlvmVoidType) "" else tmpVars.next()

        val argsArray = NativePointerArray.fromJavaPointers(args.map { it.raw })
        val result = Llvm.LLVMBuildCall2(
            llvmRef,
            function.type.getRawInContext(context),
            function.address.raw,
            argsArray,
            argsArray.length,
            name,
        )

        return LlvmValue(result, function.type.returnType)
    }

    override fun <R : LlvmType> call(
        function: LlvmValue<LlvmFunctionAddressType>,
        functionType: LlvmFunctionType<R>,
        args: List<LlvmValue<*>>
    ): LlvmValue<R> {
        val callInst = NativePointerArray.fromJavaPointers(args.map { it.raw }).use { argsRaw ->
            Llvm.LLVMBuildCall2(
                llvmRef,
                functionType.getRawInContext(context),
                function.raw,
                argsRaw,
                argsRaw.length,
                if (functionType.returnType == LlvmVoidType) "" else tmpVars.next(),
            )
        }

        return LlvmValue(callInst, functionType.returnType)
    }

    override fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T> {
        val inst = Llvm.LLVMBuildPtrToInt(llvmRef, pointer.raw, integerType.getRawInContext(context), tmpVars.next())
        return LlvmValue(inst, integerType)
    }

    override fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>) {
        // TODO: alignment; 1 is bad
        val inst = Llvm.LLVMBuildMemCpy(llvmRef, destination.raw, 1, source.raw, 1, nBytes.raw)
    }

    override fun memset(destination: LlvmValue<LlvmPointerType<*>>, value: LlvmValue<LlvmS8Type>, nBytes: LlvmValue<LlvmIntegerType>) {
        // TODO: alignment; 1 is bad
        val inst = Llvm.LLVMBuildMemSet(llvmRef, destination.raw, value.raw, nBytes.raw, 1)
    }

    override fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNull(llvmRef, pointer.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isNotNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNotNull(llvmRef, pointer.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNull(llvmRef, int.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isNotZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNotNull(llvmRef, int.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isEq(pointerA: LlvmValue<LlvmPointerType<*>>, pointerB: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val aAsInt = ptrtoint(pointerA, EmergeUWordType)
        val bAsInt = ptrtoint(pointerB, EmergeUWordType)
        return icmp(aAsInt, LlvmIntPredicate.EQUAL, bAsInt)
    }

    override fun <T : LlvmIntegerType> not(value: LlvmValue<T>): LlvmValue<T> {
        val inst = Llvm.LLVMBuildNot(llvmRef, value.raw, tmpVars.next())
        return LlvmValue(inst, value.type)
    }

    override fun <R : LlvmType> select(condition: LlvmValue<LlvmBooleanType>, ifTrue: LlvmValue<R>, ifFalse: LlvmValue<R>): LlvmValue<R> {
        check(ifTrue.type == ifFalse.type)

        val inst = Llvm.LLVMBuildSelect(
            llvmRef,
            condition.raw,
            ifTrue.raw,
            ifFalse.raw,
            tmpVars.next(),
        )
        return LlvmValue(inst, ifTrue.type)
    }

    override fun enterScope(scope: LlvmDebugInfo.Scope) {
        scopeTracker.enterScope(scope)
    }

    override fun createAndEnterLexicalScope(): LlvmDebugInfo.Scope.LexicalBlock {
        val scope = diBuilder.createLexicalScope(
            parentScope = try {
                scopeTracker.currentScope
            } catch (ex: NoSuchElementException) {
                null
            },
            lastKnownLine,
            0u,
        )
        scopeTracker.enterScope(scope)
        return scope
    }

    override fun leaveLexicalScope(scope: LlvmDebugInfo.Scope.LexicalBlock) {
        check(scopeTracker.currentScope == scope) { "Trying to leave scope $scope, but we are in ${scopeTracker.currentScope}" }

        scopeTracker.leaveScope()
    }

    override fun leaveScope() {
        scopeTracker.leaveScope()
    }

    private var lastKnownLine: UInt = 0u
    override fun markSourceLocation(line: UInt, column: UInt) {
        lastKnownLine = line
        val location = diBuilder.createDebugLocation(
            scopeTracker.currentScope,
            line,
            column,
        )
        Llvm.LLVMSetCurrentDebugLocation2(llvmRef, location.ref)
    }

    override fun currentDebugLocation(): String {
        val scope = try {
            scopeTracker.currentScope
        } catch (ex: NoSuchElementException) {
            return "unknown"
        }

        return "$scope, line $lastKnownLine"
    }

    override fun defer(code: DeferredCodeGenerator<C>) {
        scopeTracker.addDeferredStatement(code)
    }

    override fun ret(value: LlvmValue<R>): BasicBlockBuilder.Termination {
        scopeTracker.runAllFunctionDeferredCode()
        Llvm.LLVMBuildRet(llvmRef, value.raw)

        return TerminationImpl
    }

    override fun unreachable(): BasicBlockBuilder.Termination {
        Llvm.LLVMBuildUnreachable(llvmRef)

        return TerminationImpl
    }

    override fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination,
        ifFalse: (BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination)?,
        branchBlockName: String?,
    ) {
        val branchName = branchBlockName ?: (tmpVars.next() + "_br")
        val thenBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_then")
        lateinit var elseBlock: LlvmBasicBlockRef
        if (ifFalse != null) {
            elseBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_else")
        }

        val continueBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_cont")

        if (ifFalse != null) {
            Llvm.LLVMBuildCondBr(llvmRef, condition.raw, thenBlock, elseBlock)
        } else {
            Llvm.LLVMBuildCondBr(llvmRef, condition.raw, thenBlock, continueBlock)
        }

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, thenBlock)
        val thenBranchBuilder = BranchImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, llvmRef, tmpVars, scopeTracker.createSubScope(), continueBlock)
        thenBranchBuilder.ifTrue()

        if (ifFalse != null) {
            val elseBranchBuilder = BranchImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, llvmRef, tmpVars, scopeTracker.createSubScope(), continueBlock)
            Llvm.LLVMPositionBuilderAtEnd(llvmRef, elseBlock)
            elseBranchBuilder.ifFalse()
        }

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, continueBlock)
        return
    }

    override fun loop(
        body: BasicBlockBuilder.LoopBody<C, R>.() -> BasicBlockBuilder.Termination
    ) {
        val loopName = tmpVars.next() + "_loop"
        val bodyBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, loopName)
        val continueBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${loopName}_cont")

        Llvm.LLVMBuildBr(llvmRef, bodyBlock)

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, bodyBlock)
        val bodyDslBuilder = LoopImpl(context, llvmFunctionReturnType, diBuilder, owningFunction, llvmRef, tmpVars, scopeTracker.createSubScope(), bodyBlock, continueBlock)
        bodyDslBuilder.body()

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, continueBlock)
        return
    }

    override fun unsafeBranch(
        prepare: BasicBlockBuilder.UnsafeBranchPrepare<C, R>.() -> BasicBlockBuilder.Termination,
        branch: BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination,
        branchBlockName: String?,
        resumeBlockName: String?,
    ) {
        val branchBlockRef = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, tmpVars.next() + "_" + (branchBlockName ?: "unsafe_branch"))
        val resumeBlockRef = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, tmpVars.next() + "_" + (resumeBlockName ?: "unsafe_resume"))

        prepare(UnsafeBranchPrepareImpl(
            context,
            llvmFunctionReturnType,
            diBuilder,
            owningFunction,
            llvmRef,
            tmpVars,
            scopeTracker,
            branchBlockRef,
            resumeBlockRef,
        ))

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, branchBlockRef)
        branch(BranchImpl(
            context,
            llvmFunctionReturnType,
            diBuilder,
            owningFunction,
            llvmRef,
            tmpVars,
            scopeTracker.createSubScope(),
            resumeBlockRef,
        ))

        Llvm.LLVMPositionBuilderAtEnd(llvmRef, resumeBlockRef)
    }
}

private class BranchImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    functionReturnType: R,
    diBuilder: DiBuilder,
    owningFunction: LlvmValueRef,
    builder: LlvmBuilderRef,
    tmpVars: NameScope,
    scopeTracker: ScopeTracker<C>,
    val continueBlock: LlvmBasicBlockRef,
) : BasicBlockBuilderImpl<C, R>(context, functionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker), BasicBlockBuilder.Branch<C, R> {
    override fun concludeBranch(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(llvmRef, continueBlock)
        return TerminationImpl
    }
}

private class LoopImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    functionReturnType: R,
    diBuilder: DiBuilder,
    owningFunction: LlvmValueRef,
    builder: LlvmBuilderRef,
    tmpVars: NameScope,
    scopeTracker: ScopeTracker<C>,
    val bodyBlockRef: LlvmBasicBlockRef,
    val continueBlock: LlvmBasicBlockRef,
) : BasicBlockBuilderImpl<C, R>(context, functionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker), BasicBlockBuilder.LoopBody<C, R> {
    override fun breakLoop(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(llvmRef, continueBlock)
        return TerminationImpl
    }

    override fun loopContinue(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(llvmRef, bodyBlockRef)
        return TerminationImpl
    }
}

private class UnsafeBranchPrepareImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    llvmFunctionReturnType: R,
    diBuilder: DiBuilder,
    owningFunction: LlvmValueRef,
    builder: LlvmBuilderRef,
    tmpVars: NameScope,
    scopeTracker: ScopeTracker<C>,
    private val branchBlockRef: LlvmBasicBlockRef,
    private val resumeBlockRef: LlvmBasicBlockRef,
) : BasicBlockBuilder.UnsafeBranchPrepare<C, R>, BasicBlockBuilderImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker) {
    override fun jumpToUnsafeBranch(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(llvmRef, branchBlockRef)
        return TerminationImpl
    }

    override fun skipUnsafeBranch(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(llvmRef, resumeBlockRef)
        return TerminationImpl
    }
}

private data object TerminationImpl : BasicBlockBuilder.Termination

typealias CodeGenerator<C, R> = BasicBlockBuilder<C, R>.() -> BasicBlockBuilder.Termination

/**
 * code to execute before the scope exits, must not emit terminal instructions.
 */
typealias DeferredCodeGenerator<C> = DeferScopeBasicBlockBuilder<C>.() -> Unit

private class ScopeTracker<C : LlvmContext> private constructor(private val parent: ScopeTracker<C>?) {
    constructor() : this(null) {}

    private val deferredCode = ArrayList<DeferredCodeGenerator<C>>()

    fun addDeferredStatement(code: DeferredCodeGenerator<C>) {
        deferredCode.add(code)
    }

    fun createSubScope(): ScopeTracker<C> = ScopeTracker(this)

    context(builder: BasicBlockBuilder<C, *>)
    fun runLocalDeferredCode() {
        deferredCode.forEach {
            it(builder)
        }
    }

    context(builder: BasicBlockBuilder<C, *>)
    fun runAllFunctionDeferredCode() {
        parent?.runAllFunctionDeferredCode()
        runLocalDeferredCode()
    }

    private val debugScopes = Stack<LlvmDebugInfo.Scope>()

    fun enterScope(scope: LlvmDebugInfo.Scope) {
        debugScopes.push(scope)
    }

    fun leaveScope() {
        debugScopes.pop()
    }

    val currentScope: LlvmDebugInfo.Scope get() {
        if (debugScopes.isNotEmpty()) {
            return debugScopes.peek()
        }

        if (parent == null) {
            throw NoSuchElementException()
        }

        return parent.currentScope
    }
}