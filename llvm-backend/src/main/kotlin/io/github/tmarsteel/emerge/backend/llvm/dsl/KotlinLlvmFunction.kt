package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM
import kotlin.reflect.KProperty

class KotlinLlvmFunction<C : LlvmContext, R : LlvmType> private constructor(
    val buildAndAdd: (C) -> LLVMValueRef,
) {
    fun addTo(context: C) {
        buildAndAdd(context)
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> declare(
            name: String,
            returnType: C.() -> R,
            declaration: DeclareFunctionBuilderContext.() -> Unit
        ) = KotlinLlvmFunction<C, R> { context ->
            val fnContext = DeclareFunctionBuilderContextImpl(context, returnType(context))
            fnContext.declaration()
            fnContext.buildAndAdd(name)
        }

        fun <C : LlvmContext, R : LlvmType> define(
            name: String,
            returnType: C.() -> R,
            body: DefineFunctionBuilderContext<C, R>.() -> Unit
        ) = KotlinLlvmFunction<C, R> { context ->
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

interface DeclareFunctionBuilderContext {
    fun <T : LlvmType> param(type: T): ParameterDelegate<T>
}

interface DefineFunctionBuilderContext<C : LlvmContext, R : LlvmType> : DeclareFunctionBuilderContext {
    fun body(build: CodeGenerator<C, R>)
}

private abstract class BaseFunctionBuilderContext<C : LlvmContext, R : LlvmType>(
    private val context: C,
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
            returnType.getRawInContext(context),
            PointerPointer(*parameters.map { it.type.getRawInContext(context) }.toTypedArray()),
            parameters.size,
            0
        )
        return LLVM.LLVMAddFunction(context.module, name, functionType)
    }
}

private class DeclareFunctionBuilderContextImpl<C : LlvmContext, R : LlvmType>(
    context: C,
    returnType: R,
) : BaseFunctionBuilderContext<C, R>(context, returnType), LlvmContext by context {
    private var built = false
    override fun buildAndAdd(name: String): LLVMValueRef {
        check(!built) { "Already built" }
        built = true

        return buildAndAddFunctionInstance(name)
    }
}

private class DefineFunctionBuilderContextImpl<C : LlvmContext, R : LlvmType>(
    private val context: C,
    returnType: R,
) : BaseFunctionBuilderContext<C, R>(context, returnType), DefineFunctionBuilderContext<C, R>, LlvmContext by context {
    private var state = State.PRELUDE
    private lateinit var bodyBuilder: CodeGenerator<C, R>

    override fun <T : LlvmType> param(type: T): ParameterDelegate<T> {
        check(state == State.PRELUDE) {
            "Cannot define parameters after defining the body"
        }
        return super.param(type)
    }

    override fun body(build: CodeGenerator<C, R>) {
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
        BasicBlockBuilder.fill(context, basicBlock, bodyBuilder)

        return functionInstance
    }

    private enum class State {
        PRELUDE,
        BODY_KNOWN,
        BUILT
    }
}