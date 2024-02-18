package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.getLlvmMessage
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMBasicBlockRef
import org.bytedeco.llvm.LLVM.LLVMBuilderRef
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
    fun <T : LlvmIntegerType> add(a: LlvmValue<T>, b: LlvmValue<T>): LlvmValue<T>
    fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>>
    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R>
    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T>
    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean = false)
    fun ret(value: LlvmValue<R>): Termination

    /**
     * Used to symbol that a terminal instruction has been built. There are two key facts about the [Termination] type:
     * * only [BasicBlockBuilderImpl] can instantiate this value
     * * it will only do so if you build one of the terminal instructions (e.g. [BasicBlockBuilderImpl.ret])
     * This assures that any code builder passed to [fill] will cleanly terminate the basic block.
     */
    sealed interface Termination

    companion object {
        fun <C : LlvmContext, R : LlvmType> fill(context: C, block: LLVMBasicBlockRef, code: CodeGenerator<C, R>) {
            check(LLVM.LLVMGetFirstInstruction(block) == null) {
                "The basic block ${LLVM.LLVMGetBasicBlockName(block).string} already contains instructions, cannot safely add more."
            }

            val builder = LLVM.LLVMCreateBuilderInContext(context.ref)
            LLVM.LLVMPositionBuilderAtEnd(builder, block)
            try {
                val dslBuilder = BasicBlockBuilderImpl<C, R>(context, builder)
                val termination = dslBuilder.code()
                require((termination as TerminationImpl).fromBuilder === dslBuilder) {
                    "The code generator returned a termination token from a different builder. Something is seriously off in the generator code!"
                }
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

private class BasicBlockBuilderImpl<C : LlvmContext, R : LlvmType>(
    override val context: C,
    override val builder: LLVMBuilderRef,
) : BasicBlockBuilder<C, R> {
    private val tmpVars = NameScope("tmp")

    private var terminated = false
    private fun markTerminated() {
        check(!terminated) {
            "You are trying to terminate a single basic block more than once, this is illegal."
        }
        terminated = true
    }
    private fun checkNotTerminated() {
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

    override fun <T : LlvmIntegerType> add(a: LlvmValue<T>, b: LlvmValue<T>): LlvmValue<T> {
        checkNotTerminated()

        val addInstr = LLVM.LLVMBuildAdd(builder, a.raw, b.raw, tmpVars.next())
        return LlvmValue(addInstr, a.type)
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
}

/*
fun loop(
        header: BasicBlockBuilder<C, R>.(goToBody: () -> Termination, goTo: () -> Termination) -> Termination,
        body: BasicBlockBuilder<C, R>.() -> Termination,
        latch: BasicBlockBuilder<C, R>.() -> Termination
    )
 */

private class TerminationImpl(val fromBuilder: BasicBlockBuilder<*, *>) : BasicBlockBuilder.Termination

typealias CodeGenerator<C, R> = BasicBlockBuilder<C, R>.() -> BasicBlockBuilder.Termination