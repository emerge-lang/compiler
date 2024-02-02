package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM
import kotlin.reflect.KProperty

class LlvmFunction<ReturnType : LlvmType> private constructor(
    val buildAndAdd: (LlvmContext) -> LLVMValueRef,
) {
    fun addTo(context: LlvmContext) {
        buildAndAdd(context)
    }

    companion object {
        fun <ReturnType : LlvmType> declare(
            name: String,
            returnType: LlvmContext.() -> ReturnType,
            declaration: DeclareFunctionBuilderContext.() -> Unit
        ) = LlvmFunction<ReturnType> { context ->
            val fnContext = DeclareFunctionBuilderContextImpl(context, returnType(context))
            fnContext.declaration()
            fnContext.buildAndAdd(name)
        }

        fun <ReturnType : LlvmType> define(
            name: String,
            returnType: LlvmContext.() -> ReturnType,
            body: DefineFunctionBuilderContext<ReturnType>.() -> Unit
        ) = LlvmFunction<ReturnType> { context ->
            val fnContext = DefineFunctionBuilderContextImpl(context, returnType(context))
            fnContext.body()
            fnContext.buildAndAdd(name)
        }
    }
}

class ParameterDelegate<T : LlvmType>(
    val type: T,
    val index: Int,
) {
    private lateinit var function: LLVMValueRef
    internal fun setFunctionInstance(function: LLVMValueRef) {
        check(LLVM.LLVMIsAFunction(function) != null)
        this.function = function
    }

    operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T> {
        return LlvmValue(LLVM.LLVMGetParam(function, index), type)
    }
}

interface DeclareFunctionBuilderContext : LlvmContext {
    fun <T : LlvmType> param(type: T): ParameterDelegate<T>
}

interface DefineFunctionBuilderContext<ReturnType : LlvmType> : DeclareFunctionBuilderContext {
    fun body(build: BasicBlockBuilder.() -> LlvmValue<ReturnType>)
}

private abstract class BaseFunctionBuilderContext<R : LlvmType>(
    private val context: LlvmContext,
    private val returnType: R,
) : DeclareFunctionBuilderContext {
    protected val parameters = ArrayList<ParameterDelegate<*>>()
    override fun <T : LlvmType> param(type: T) : ParameterDelegate<T> {
        val delegate = ParameterDelegate(type, parameters.size)
        parameters.add(delegate)
        return delegate
    }

    abstract fun buildAndAdd(name: String): LLVMValueRef

    protected fun buildAndAddFunctionInstance(name: String): LLVMValueRef {
        val functionType = LLVM.LLVMFunctionType(
            returnType.raw,
            PointerPointer(*parameters.map { it.type.raw }.toTypedArray()),
            parameters.size,
            0
        )
        return LLVM.LLVMAddFunction(context.module, name, functionType)
    }
}

private class DeclareFunctionBuilderContextImpl<R : LlvmType>(
    context: LlvmContext,
    returnType: R,
) : BaseFunctionBuilderContext<R>(context, returnType), LlvmContext by context {
    private var built = false
    override fun buildAndAdd(name: String): LLVMValueRef {
        check(!built) { "Already built" }
        built = true

        return buildAndAddFunctionInstance(name)
    }
}

private class DefineFunctionBuilderContextImpl<R : LlvmType>(
    private val context: LlvmContext,
    returnType: R,
) : BaseFunctionBuilderContext<R>(context, returnType), DefineFunctionBuilderContext<R>, LlvmContext by context {
    private var state = State.PRELUDE
    private lateinit var bodyBuilder: BasicBlockBuilder.() -> LlvmValue<R>

    override fun <T : LlvmType> param(type: T): ParameterDelegate<T> {
        check(state == State.PRELUDE) {
            "Cannot define parameters after defining the body"
        }
        return super.param(type)
    }

    override fun body(build: BasicBlockBuilder.() -> LlvmValue<R>) {
        check(state == State.PRELUDE) {
            "Cannot declare body more than once"
        }

        state = State.BODY_KNOWN
        bodyBuilder = build
    }

    override fun buildAndAdd(name: String): LLVMValueRef {
        check(state == State.BODY_KNOWN) {
            "Cannot build before declaring body"
        }
        state = State.BUILT

        val functionInstance = buildAndAddFunctionInstance(name)
        parameters.forEach { it.setFunctionInstance(functionInstance) }
        val basicBlock = LLVM.LLVMAppendBasicBlock(functionInstance, "entry")
        BasicBlockBuilder.appendToWithReturn(context, basicBlock, bodyBuilder)

        return functionInstance
    }

    private enum class State {
        PRELUDE,
        BODY_KNOWN,
        BUILT
    }
}