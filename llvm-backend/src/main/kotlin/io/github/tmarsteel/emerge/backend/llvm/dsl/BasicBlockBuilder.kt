package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBasicBlockRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBuilderRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.util.Stack

interface BasicBlockBuilder<C : LlvmContext, R : LlvmType> {
    val context: C
    val llvmFunctionReturnType: R
    val builder: LlvmBuilderRef
    fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmIntegerType> = context.i32(0)
    ): GetElementPointerStep<BasePointee>

    fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>>
    fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P>
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
    fun <T : LlvmIntegerType> and(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> or(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <T : LlvmIntegerType> xor(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T>
    fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeUnsigned(value: LlvmValue<Small>, to: Large): LlvmValue<Large>
    fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeSigned(value: LlvmValue<Small>, to: Large): LlvmValue<Large>
    fun <Small : LlvmIntegerType, Large: LlvmIntegerType> truncate(value: LlvmValue<Large>, to: Small): LlvmValue<Small>
    fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>>
    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(function: LlvmValue<LlvmFunctionAddressType>, functionType: LlvmFunctionType<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <R : LlvmType> call(llvmIntrinsic: LlvmIntrinsic<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        return call(llvmIntrinsic.getRawInContext(context), args)
    }
    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T>
    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>)
    fun memset(destination: LlvmValue<LlvmPointerType<*>>, value: LlvmValue<LlvmI8Type>, nBytes: LlvmValue<LlvmIntegerType>)
    fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun isNotNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun isZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType>
    fun isNotZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType>
    fun isEq(pointerA: LlvmValue<LlvmPointerType<*>>, pointerB: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType>
    fun <T : LlvmIntegerType> not(value: LlvmValue<T>): LlvmValue<T>

    fun <R : LlvmType> select(condition: LlvmValue<LlvmBooleanType>, ifTrue: LlvmValue<R>, ifFalse: LlvmValue<R>): LlvmValue<R>

    fun enterDebugScope(scope: DebugInfoScope)
    fun leaveDebugScope()
    fun markSourceLocation(line: UInt, column: UInt)

    /**
     * @param code will be executed when this scope is closed, either on a function-terminating instruction
     * or when a logical scope is completed (e.g. [conditionalBranch], [loop])
     * TODO: encode into the type of [code] that defer cannot be called there again. Maybe it even throws a ConcurrentModificationException?
     */
    fun defer(code: NonTerminalCodeGenerator<C>)

    /**
     * Generates the given [code] in a new scope for [defer].
     */
    fun <SubR> inSubScope(code: BasicBlockBuilder<C, R>.() -> SubR): SubR

    fun ret(value: LlvmValue<R>): Termination
    fun unreachable(): Termination

    fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: Branch<C, R>.() -> Termination,
        ifFalse: (Branch<C, R>.() -> Termination)? = null
    )

    /**
     * @param header is executed before every iteration and implements the loop condition
     * @param body is executed on every iteration, can break out of the loop or continue at the header
     */
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

    interface DeferSubScope<C : LlvmContext, R : LlvmType> : BasicBlockBuilder<C, R> {
        fun concludeSubScope(): Termination
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> fillBody(
            context: C,
            function: LlvmFunction<R>,
            diBuilder: DiBuilder,
            diFunction: DebugInfoScope.Function,
            code: CodeGenerator<C, R>
        ) {
            val rawFn = function.address.raw
            val entryBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, rawFn, "entry")

            val scopeTracker = ScopeTracker<C>()
            val builder = Llvm.LLVMCreateBuilderInContext(context.ref)
            Llvm.LLVMPositionBuilderAtEnd(builder, entryBlock)
            try {
                val dslBuilder = BasicBlockBuilderImpl<C, R>(context, function.type.returnType, diBuilder, rawFn, builder, NameScope("tmp"), scopeTracker)
                dslBuilder.enterDebugScope(diFunction)
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
            Llvm.LLVMBuildRetVoid(builder)
            return TerminationImpl
        }
    }
}

private open class BasicBlockBuilderImpl<C : LlvmContext, R : LlvmType>(
    override val context: C,
    override val llvmFunctionReturnType: R,
    val diBuilder: DiBuilder,
    val owningFunction: LlvmValueRef,
    override val builder: LlvmBuilderRef,
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
            builder,
            basePointer.type.pointed.getRawInContext(context),
            basePointer.raw,
            indicesRaw,
            indicesRaw.length,
            tmpVars.next(),
        )
        return LlvmValue(instruction, LlvmPointerType(resultPointeeType))
    }

    override fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P> {
        val loadResult = Llvm.LLVMBuildLoad2(builder, type.pointed.getRawInContext(context), raw, tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    override fun <S : LlvmStructType, T : LlvmType> extractValue(
        struct: LlvmValue<S>,
        memberSelector: S.() -> LlvmStructType.Member<S, T>,
    ): LlvmValue<T> {
        val member = struct.type.memberSelector()
        val extractInst = Llvm.LLVMBuildExtractValue(builder, struct.raw, member.indexInStruct, tmpVars.next())
        return LlvmValue(extractInst, member.type)
    }

    override fun <S : LlvmStructType, T : LlvmType> insertValue(
        struct: LlvmValue<S>,
        value: LlvmValue<T>,
        memberSelector: S.() -> LlvmStructType.Member<S, T>,
    ): LlvmValue<S> {
        val member = struct.type.memberSelector()
        val insertInst = Llvm.LLVMBuildInsertValue(builder, struct.raw, value.raw, member.indexInStruct, tmpVars.next())
        return LlvmValue(insertInst, struct.type)
    }

    override fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        check(value.type !is LlvmVoidType) // LLVM segfaults if this doesn't hold
        Llvm.LLVMBuildStore(builder, value.raw, to.raw)
    }

    override fun <T : LlvmIntegerType> add(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val addInstr = Llvm.LLVMBuildAdd(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(addInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sub(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val subInstr = Llvm.LLVMBuildSub(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(subInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> mul(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val mulInstr = Llvm.LLVMBuildMul(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(mulInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> sdiv(
        lhs: LlvmValue<T>,
        rhs: LlvmValue<T>,
        knownToBeExact: Boolean
    ): LlvmValue<T> {
        val inst = if (knownToBeExact) {
            Llvm.LLVMBuildExactSDiv(builder, lhs.raw, rhs.raw, tmpVars.next())
        } else {
            Llvm.LLVMBuildSDiv(builder, lhs.raw, rhs.raw, tmpVars.next())
        }

        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> udiv(
        lhs: LlvmValue<T>,
        rhs: LlvmValue<T>,
        knownToBeExact: Boolean
    ): LlvmValue<T> {
        val inst = if (knownToBeExact) {
            Llvm.LLVMBuildExactUDiv(builder, lhs.raw, rhs.raw, tmpVars.next())
        } else {
            Llvm.LLVMBuildUDiv(builder, lhs.raw, rhs.raw, tmpVars.next())
        }

        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> srem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val inst = Llvm.LLVMBuildSRem(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> urem(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val inst = Llvm.LLVMBuildURem(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(inst, lhs.type)
    }

    override fun <T : LlvmIntegerType> icmp(lhs: LlvmValue<T>, type: LlvmIntPredicate, rhs: LlvmValue<T>): LlvmValue<LlvmBooleanType> {
        val cmpInstr = Llvm.LLVMBuildICmp(builder, type, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(cmpInstr, LlvmBooleanType)
    }

    override fun <T : LlvmIntegerType> shl(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T> {
        val shiftInstr = Llvm.LLVMBuildShl(builder, value.raw, shiftAmount.raw, tmpVars.next())
        return LlvmValue(shiftInstr, value.type)
    }

    override fun <T : LlvmIntegerType> lshr(value: LlvmValue<T>, shiftAmount: LlvmValue<T>): LlvmValue<T> {
        val shiftInstr = Llvm.LLVMBuildLShr(builder, value.raw, shiftAmount.raw, tmpVars.next())
        return LlvmValue(shiftInstr, value.type)
    }

    override fun <T : LlvmIntegerType> and(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val andInstr = Llvm.LLVMBuildAnd(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(andInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> or(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val orInstr = Llvm.LLVMBuildOr(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(orInstr, lhs.type)
    }

    override fun <T : LlvmIntegerType> xor(lhs: LlvmValue<T>, rhs: LlvmValue<T>): LlvmValue<T> {
        val xorInst = Llvm.LLVMBuildXor(builder, lhs.raw, rhs.raw, tmpVars.next())
        return LlvmValue(xorInst, lhs.type)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeSigned(
        value: LlvmValue<Small>,
        to: Large,
    ): LlvmValue<Large> {
        val sextInstr = Llvm.LLVMBuildSExt(builder, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(sextInstr, to)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> enlargeUnsigned(
        value: LlvmValue<Small>,
        to: Large,
    ): LlvmValue<Large> {
        val zextInstr = Llvm.LLVMBuildZExt(builder, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(zextInstr, to)
    }

    override fun <Small : LlvmIntegerType, Large : LlvmIntegerType> truncate(
        value: LlvmValue<Large>,
        to: Small,
    ): LlvmValue<Small> {
        val truncInstr = Llvm.LLVMBuildTrunc(builder, value.raw, to.getRawInContext(context), tmpVars.next())
        return LlvmValue(truncInstr, to)
    }

    override fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>> {
        val ptr = Llvm.LLVMBuildAlloca(builder, type.getRawInContext(context), tmpVars.next())
        return LlvmValue(ptr, pointerTo(type))
    }

    override fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
        require(function.type.parameterTypes.size == args.size) {
            "The function ${function.name} takes ${function.type.parameterTypes.size} parameters, ${args.size} arguments given."
        }
        args.zip(function.type.parameterTypes).forEachIndexed { index, (arg, paramType) ->
            require(arg.isLlvmAssignableTo(paramType.getRawInContext(context))) {
                "argument #$index: ${arg.type} is not llvm-assignable to $paramType"
            }
        }

        val name = if (function.type.returnType == LlvmVoidType) "" else tmpVars.next()

        val argsArray = NativePointerArray.fromJavaPointers(args.map { it.raw })
        val result = Llvm.LLVMBuildCall2(
            builder,
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
                builder,
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
        val inst = Llvm.LLVMBuildPtrToInt(builder, pointer.raw, integerType.getRawInContext(context), tmpVars.next())
        return LlvmValue(inst, integerType)
    }

    override fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>) {
        // TODO: alignment; 1 is bad
        val inst = Llvm.LLVMBuildMemCpy(builder, destination.raw, 1, source.raw, 1, nBytes.raw)
    }

    override fun memset(destination: LlvmValue<LlvmPointerType<*>>, value: LlvmValue<LlvmI8Type>, nBytes: LlvmValue<LlvmIntegerType>) {
        // TODO: alignment; 1 is bad
        val inst = Llvm.LLVMBuildMemSet(builder, destination.raw, value.raw, nBytes.raw, 1)
    }

    override fun isNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNull(builder, pointer.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isNotNull(pointer: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNotNull(builder, pointer.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNull(builder, int.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isNotZero(int: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmBooleanType> {
        val instr = Llvm.LLVMBuildIsNotNull(builder, int.raw, tmpVars.next())
        return LlvmValue(instr, LlvmBooleanType)
    }

    override fun isEq(pointerA: LlvmValue<LlvmPointerType<*>>, pointerB: LlvmValue<LlvmPointerType<*>>): LlvmValue<LlvmBooleanType> {
        val aAsInt = ptrtoint(pointerA, EmergeWordType)
        val bAsInt = ptrtoint(pointerB, EmergeWordType)
        return icmp(aAsInt, LlvmIntPredicate.EQUAL, bAsInt)
    }

    override fun <T : LlvmIntegerType> not(value: LlvmValue<T>): LlvmValue<T> {
        val inst = Llvm.LLVMBuildNot(builder, value.raw, tmpVars.next())
        return LlvmValue(inst, value.type)
    }

    override fun <R : LlvmType> select(condition: LlvmValue<LlvmBooleanType>, ifTrue: LlvmValue<R>, ifFalse: LlvmValue<R>): LlvmValue<R> {
        check(ifTrue.type == ifFalse.type)

        val inst = Llvm.LLVMBuildSelect(
            builder,
            condition.raw,
            ifTrue.raw,
            ifFalse.raw,
            tmpVars.next(),
        )
        return LlvmValue(inst, ifTrue.type)
    }

    override fun enterDebugScope(scope: DebugInfoScope) {
        scopeTracker.enterDebugScope(scope)
    }

    override fun leaveDebugScope() {
        scopeTracker.leaveDebugScope()
    }

    private var lastKnownLine: UInt = 0u
    override fun markSourceLocation(line: UInt, column: UInt) {
        lastKnownLine = line
        val location = diBuilder.createDebugLocation(
            scopeTracker.currentDebugScope,
            line,
            column,
        )
        Llvm.LLVMSetCurrentDebugLocation2(builder, location)
    }

    override fun defer(code: NonTerminalCodeGenerator<C>) {
        scopeTracker.addDeferredStatement(code)
    }

    override fun <SubR> inSubScope(code: BasicBlockBuilder<C, R>.() -> SubR): SubR {
        val subBuilder = BasicBlockBuilderImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker.createSubScope())
        val returnValue = subBuilder.code()

        val mostRecentInstruction = Llvm.LLVMGetLastInstruction(Llvm.LLVMGetInsertBlock(builder))
        if (mostRecentInstruction == null || Llvm.LLVMIsATerminatorInst(mostRecentInstruction) == null) {
            // the sub-scope code didn't terminate -> need to emit defer code
            subBuilder.scopeTracker.runLocalDeferredCode()
        }

        return returnValue
    }

    override fun ret(value: LlvmValue<R>): BasicBlockBuilder.Termination {
        scopeTracker.runAllFunctionDeferredCode()
        Llvm.LLVMBuildRet(builder, value.raw)

        return TerminationImpl
    }

    override fun unreachable(): BasicBlockBuilder.Termination {
        Llvm.LLVMBuildUnreachable(builder)

        return TerminationImpl
    }

    override fun conditionalBranch(
        condition: LlvmValue<LlvmBooleanType>,
        ifTrue: BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination,
        ifFalse: (BasicBlockBuilder.Branch<C, R>.() -> BasicBlockBuilder.Termination)?,
    ) {
        val branchName = tmpVars.next() + "_br"
        val thenBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_then")
        lateinit var elseBlock: LlvmBasicBlockRef
        if (ifFalse != null) {
            elseBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_else")
        }

        val continueBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${branchName}_cont")

        if (ifFalse != null) {
            Llvm.LLVMBuildCondBr(builder, condition.raw, thenBlock, elseBlock)
        } else {
            Llvm.LLVMBuildCondBr(builder, condition.raw, thenBlock, continueBlock)
        }

        Llvm.LLVMPositionBuilderAtEnd(builder, thenBlock)
        val thenBranchBuilder = BranchImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker.createSubScope(), continueBlock)
        thenBranchBuilder.ifTrue()

        if (ifFalse != null) {
            val elseBranchBuilder = BranchImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker.createSubScope(), continueBlock)
            Llvm.LLVMPositionBuilderAtEnd(builder, elseBlock)
            elseBranchBuilder.ifFalse()
        }

        Llvm.LLVMPositionBuilderAtEnd(builder, continueBlock)
        return
    }

    override fun loop(
        header: BasicBlockBuilder.LoopHeader<C, R>.() -> BasicBlockBuilder.Termination,
        body: BasicBlockBuilder.LoopBody<C, R>.() -> BasicBlockBuilder.Termination
    ) {
        val loopName = tmpVars.next() + "_loop"
        val headerBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${loopName}_header")
        val bodyBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${loopName}_body")
        val continueBlock = Llvm.LLVMAppendBasicBlockInContext(context.ref, owningFunction, "${loopName}_cont")

        Llvm.LLVMBuildBr(builder, headerBlock)

        Llvm.LLVMPositionBuilderAtEnd(builder, headerBlock)
        val headerDslBuilder = LoopImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker.createSubScope(), headerBlock, bodyBlock, continueBlock)
        headerDslBuilder.header()

        Llvm.LLVMPositionBuilderAtEnd(builder, bodyBlock)
        val bodyDslBuilder = LoopImpl<C, R>(context, llvmFunctionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker.createSubScope(), headerBlock, bodyBlock, continueBlock)
        bodyDslBuilder.body()

        Llvm.LLVMPositionBuilderAtEnd(builder, continueBlock)
        return
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
        Llvm.LLVMBuildBr(builder, continueBlock)
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
    val headerBlockRef: LlvmBasicBlockRef,
    val bodyBlockRef: LlvmBasicBlockRef,
    val continueBlock: LlvmBasicBlockRef,
) : BasicBlockBuilderImpl<C, R>(context, functionReturnType, diBuilder, owningFunction, builder, tmpVars, scopeTracker), BasicBlockBuilder.LoopHeader<C, R>, BasicBlockBuilder.LoopBody<C, R> {
    override fun breakLoop(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(builder, continueBlock)
        return TerminationImpl
    }

    override fun doIteration(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(builder, bodyBlockRef)
        return TerminationImpl
    }

    override fun loopContinue(): BasicBlockBuilder.Termination {
        scopeTracker.runLocalDeferredCode()
        Llvm.LLVMBuildBr(builder, headerBlockRef)
        return TerminationImpl
    }
}

private data object TerminationImpl : BasicBlockBuilder.Termination

typealias CodeGenerator<C, R> = BasicBlockBuilder<C, R>.() -> BasicBlockBuilder.Termination

/**
 * code to execute before the scope exits, must not emit terminal instructions.
 * TODO: build the "no terminals" limitation into the type of the lambda, e.g. BasicBlockBuilder.NonTerminal<C, R>
 */
typealias NonTerminalCodeGenerator<C> = BasicBlockBuilder<C, *>.() -> Unit

private class ScopeTracker<C : LlvmContext> private constructor(private val parent: ScopeTracker<C>?) {
    constructor() : this(null) {}

    private val deferredCode = ArrayList<NonTerminalCodeGenerator<C>>()

    fun addDeferredStatement(code: NonTerminalCodeGenerator<C>) {
        deferredCode.add(code)
    }

    fun createSubScope(): ScopeTracker<C> = ScopeTracker(this)

    context(BasicBlockBuilder<C, *>)
    fun runLocalDeferredCode() {
        deferredCode.forEach {
            it(this@BasicBlockBuilder)
        }
    }

    context(BasicBlockBuilder<C, *>)
    fun runAllFunctionDeferredCode() {
        parent?.runAllFunctionDeferredCode()
        runLocalDeferredCode()
    }

    private val debugScopes = Stack<DebugInfoScope>()

    fun enterDebugScope(scope: DebugInfoScope) {
        debugScopes.push(scope)
    }

    fun leaveDebugScope() {
        debugScopes.pop()
    }

    val currentDebugScope: DebugInfoScope get() {
        if (debugScopes.isNotEmpty()) {
            return debugScopes.peek()
        }

        if (parent == null) {
            throw NoSuchElementException()
        }

        return parent.currentDebugScope
    }
}