package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.getLlvmMessage
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.AnyValueType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMBasicBlockRef
import org.bytedeco.llvm.global.LLVM

class BasicBlockBuilder<C : LlvmContext, R : LlvmType> private constructor(
    val context: C,
    private val basicBlock: LLVMBasicBlockRef,
) : AutoCloseable {
    private val builder = LLVM.LLVMCreateBuilder()
    private val tmpVars = NameScope("tmp")
    init {
        LLVM.LLVMPositionBuilderAtEnd(builder, basicBlock)
    }

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

    fun <BasePointee : LlvmType> getelementptr(
        base: LlvmValue<LlvmPointerType<out BasePointee>>,
        index: LlvmValue<LlvmFixedIntegerType> = context.i32(0)
    ): GetElementPointerStep<BasePointee> {
        return GetElementPointerStep.initial(base, index)
    }

    fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
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

    fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P> {
        checkNotTerminated()

        val loadResult = LLVM.LLVMBuildLoad2(builder, type.pointed.getRawInContext(context), raw, tmpVars.next())
        return LlvmValue(loadResult, type.pointed)
    }

    fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
        checkNotTerminated()

        LLVM.LLVMBuildStore(builder, value.raw, to.raw)
    }

    fun <T : LlvmIntegerType> add(a: LlvmValue<T>, b: LlvmValue<T>): LlvmValue<T> {
        checkNotTerminated()

        val addInstr = LLVM.LLVMBuildAdd(builder, a.raw, b.raw, tmpVars.next())
        return LlvmValue(addInstr, a.type)
    }

    fun <T: LlvmType> alloca(type: T): LlvmValue<LlvmPointerType<T>> {
        checkNotTerminated()

        val ptr = LLVM.LLVMBuildAlloca(builder, type.getRawInContext(context), tmpVars.next())
        return LlvmValue(ptr, LlvmPointerType(type))
    }

    fun <R : LlvmType> call(function: LlvmFunction<R>, args: List<LlvmValue<*>>): LlvmValue<R> {
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

    fun <T : LlvmIntegerType> ptrtoint(pointer: LlvmValue<LlvmPointerType<*>>, integerType: T): LlvmValue<T> {
        checkNotTerminated()

        val inst = LLVM.LLVMBuildPtrToInt(builder, pointer.raw, integerType.getRawInContext(context), tmpVars.next())
        return LlvmValue(inst, integerType)
    }

    fun memcpy(destination: LlvmValue<LlvmPointerType<*>>, source: LlvmValue<LlvmPointerType<*>>, nBytes: LlvmValue<LlvmIntegerType>, volatile: Boolean = false) {
        checkNotTerminated()

        // TODO: alignment; 1 is bad
        val inst = LLVM.LLVMBuildMemCpy(builder, destination.raw, 1, source.raw, 1, nBytes.raw)
        if (volatile) {
            LLVM.LLVMSetVolatile(inst, 1)
        }
    }

    internal fun LlvmType.sizeof(): LlvmValue<LlvmI32Type> {
        // thanks to https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type
        val pointerFromNullToSize = getelementptr(
            context.nullValue(LlvmPointerType(this)),
            context.i32(1)
        )
            .get()

        return ptrtoint(pointerFromNullToSize, LlvmI32Type)
    }

    fun ret(value: LlvmValue<R>): Termination {
        markTerminated()

        LLVM.LLVMBuildRet(builder, value.raw)

        return TerminationImpl(this)
    }

    internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.anyValueBase(): GetElementPointerStep<AnyValueType> {
        return this.type.pointed.pointerToAnyValueBase(this@BasicBlockBuilder, this@anyValueBase)
    }

    override fun close() {
        LLVM.LLVMDisposeBuilder(builder)
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> fill(context: C, block: LLVMBasicBlockRef, code: CodeGenerator<C, R>) {
            BasicBlockBuilder<C, R>(context, block).use {
                val termination = it.code()
                require((termination as TerminationImpl).fromBuilder === it) {
                    "The code generator returned a termination token from a different builder. Something is seriously off in the generator code!"
                }
            }
        }

        fun BasicBlockBuilder<*, LlvmVoidType>.retVoid(): Termination {
            LLVM.LLVMBuildRetVoid(builder)
            return TerminationImpl(this)
        }
    }

    /**
     * Used to symbol that a terminal instruction has been built. There are two key facts about the [Termination] type:
     * * only [BasicBlockBuilder] can instantiate this value
     * * it will only do so if you build one of the terminal instructions (e.g. [BasicBlockBuilder.ret])
     * This assures that any code builder passed to [fill] will cleanly terminate the basic block.
     */
    sealed interface Termination
    private class TerminationImpl(val fromBuilder: BasicBlockBuilder<*, *>) : Termination
}

typealias CodeGenerator<C, R> = BasicBlockBuilder<C, R>.() -> BasicBlockBuilder.Termination