package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM
import kotlin.reflect.KProperty

class KotlinLlvmFunction<C : LlvmContext, R : LlvmType> private constructor(
    val name: String,
    val returnType: R,
    val definition: DefinitionReceiver<C, R>.() -> Unit
) {
    /**
     * Declares this function in the given [context] but doesn't attempt to generate the body
     * yet (to allow forward references to be set).
     */
    fun declareInContext(context: C): DeclaredInContext<C, R> {
        val definitionReceiver = DefinitionReceiverImpl<C, R>()
        definitionReceiver.definition()
        val functionType = LlvmFunctionType(returnType, definitionReceiver.parameters.map { it.type })
        val functionRaw = LLVM.LLVMAddFunction(context.module, name, functionType.getRawInContext(context))
        val function = LlvmFunction(LlvmConstant(functionRaw, LlvmFunctionAddressType), functionType)
        return DeclaredInContextImpl(
            context,
            definitionReceiver.parameters,
            function,
            definitionReceiver.bodyGenerator,
        )
    }

    interface DeclaredInContext<C : LlvmContext, R : LlvmType> {
        val function: LlvmFunction<R>

        /**
         * When all forward references are present/should be present, this method can be called to
         * define the body of the function in the original context.
         */
        fun defineBody()
    }

    interface ParameterDelegate<T : LlvmType> {
        operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T>
    }

    interface DefinitionReceiver<C : LlvmContext, R : LlvmType> {
        fun <T : LlvmType> param(type: T): ParameterDelegate<T>
        fun body(build: CodeGenerator<C, R>)
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> define(
            name: String,
            returnType: R,
            definition: DefinitionReceiver<C, R>.() -> Unit
        ): KotlinLlvmFunction<C, R> = KotlinLlvmFunction(name, returnType, definition)
    }
}

private class ParameterDelegateImpl<T : LlvmType>(
    val type: T,
    val index: Int,
) : KotlinLlvmFunction.ParameterDelegate<T> {
    private lateinit var function: LLVMValueRef
    private var valueCache: LlvmValue<T>? = null

    fun setFunctionInstance(function: LLVMValueRef) {
        if (this::function.isInitialized && this.function.address() != function.address()) {
            valueCache = null
        }
        this.function = function
    }

    override operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T> {
        valueCache?.let { return it }
        val localValue = LlvmValue(LLVM.LLVMGetParam(function, index), type)
        valueCache = localValue
        return localValue
    }
}

private class DefinitionReceiverImpl<C : LlvmContext, R : LlvmType> : KotlinLlvmFunction.DefinitionReceiver<C, R> {
    private var state = State.PRELUDE
    val parameters = ArrayList<ParameterDelegateImpl<*>>()

    lateinit var bodyGenerator: CodeGenerator<C, R>
        private set

    override fun <T : LlvmType> param(type: T): KotlinLlvmFunction.ParameterDelegate<T> {
        check(state == State.PRELUDE) {
            "Cannot define parameters after defining the body"
        }
        val delegate = ParameterDelegateImpl(type, parameters.size)
        parameters.add(delegate)
        return delegate
    }

    override fun body(build: CodeGenerator<C, R>) {
        check(state == State.PRELUDE) {
            "Cannot declare body more than once"
        }

        state = State.BODY_KNOWN
        bodyGenerator = build
    }

    private enum class State {
        PRELUDE,
        BODY_KNOWN,
    }
}

private class DeclaredInContextImpl<C : LlvmContext, R : LlvmType>(
    val context: C,
    val parameterDelegates: List<ParameterDelegateImpl<*>>,
    override val function: LlvmFunction<R>,
    val bodyGenerator: CodeGenerator<C, R>,
) : KotlinLlvmFunction.DeclaredInContext<C, R> {
    override fun defineBody() {
        parameterDelegates.forEach {
            it.setFunctionInstance(function.address.raw)
        }
        BasicBlockBuilder.fillBody(context, function, bodyGenerator)
    }
}