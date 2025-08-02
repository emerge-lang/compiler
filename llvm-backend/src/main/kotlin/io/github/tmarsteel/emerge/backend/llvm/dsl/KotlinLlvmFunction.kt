package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfEmissionKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.nio.file.Path
import kotlin.reflect.KProperty

class KotlinLlvmFunction<C : LlvmContext, R : LlvmType> private constructor(
    val name: String,
    val declaredOn: StackTraceElement,
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
        val functionRaw = Llvm.LLVMAddFunction(context.module, name, functionType.getRawInContext(context))
        val function = LlvmFunction(LlvmConstant(functionRaw, LlvmFunctionAddressType), functionType)
        definitionReceiver.attributes.forEach(function::addAttributeToFunction)
        return DeclaredInContextImpl(
            context,
            name,
            declaredOn,
            definitionReceiver.parameters,
            function,
            definitionReceiver.bodyGenerator,
        )
    }

    fun createAlias(name: String): KotlinLlvmFunction<C, R> = KotlinLlvmFunction(
        name,
        declaredOn,
        returnType,
        definition,
    )

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
        fun functionAttribute(attribute: LlvmFunctionAttribute)
    }

    companion object {
        fun <C : LlvmContext, R : LlvmType> define(
            name: String,
            returnType: R,
            definition: DefinitionReceiver<C, R>.() -> Unit
        ): KotlinLlvmFunction<C, R> {
            val declaredOn = Thread.currentThread().stackTrace[2]
            return KotlinLlvmFunction(name, declaredOn, returnType, definition)
        }

        context(builder: BasicBlockBuilder<EmergeLlvmContext, *>)
        fun <R : LlvmType> callIntrinsic(fn: KotlinLlvmFunction<in EmergeLlvmContext, out R>, args: List<LlvmValue<*>>): LlvmValue<R> {
            return builder.call(builder.context.registerIntrinsic(fn), args)
        }
    }
}

private class ParameterDelegateImpl<T : LlvmType>(
    val type: T,
    val index: Int,
) : KotlinLlvmFunction.ParameterDelegate<T> {
    private lateinit var function: LlvmValueRef
    private var valueCache: LlvmValue<T>? = null

    fun setFunctionInstance(function: LlvmValueRef) {
        if (this::function.isInitialized && this.function.pointer != function.pointer) {
            valueCache = null
        }
        this.function = function
    }

    override operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T> {
        valueCache?.let { return it }
        val localValue = LlvmValue(Llvm.LLVMGetParam(function, index), type)
        valueCache = localValue
        return localValue
    }
}

private class DefinitionReceiverImpl<C : LlvmContext, R : LlvmType> : KotlinLlvmFunction.DefinitionReceiver<C, R> {
    private var state = State.PRELUDE
    val parameters = ArrayList<ParameterDelegateImpl<*>>()
    val attributes = ArrayList<LlvmFunctionAttribute>()

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

    override fun functionAttribute(attribute: LlvmFunctionAttribute) {
        attributes.add(attribute)
    }

    private enum class State {
        PRELUDE,
        BODY_KNOWN,
    }
}

private class DeclaredInContextImpl<C : LlvmContext, R : LlvmType>(
    val context: C,
    val name: String,
    val declaredOn: StackTraceElement,
    val parameterDelegates: List<ParameterDelegateImpl<*>>,
    override val function: LlvmFunction<R>,
    val bodyGenerator: CodeGenerator<C, R>,
) : KotlinLlvmFunction.DeclaredInContext<C, R> {
    override fun defineBody() {
        parameterDelegates.forEach {
            it.setFunctionInstance(function.address.raw)
        }

        val canonicalPackageName = CanonicalElementName.Package(
            name.split('.')
                .drop(1)
                .takeUnless { it.isEmpty() }
                ?: listOf("emerge", "platform")
        )
        val canonicalName = CanonicalElementName.Function(canonicalPackageName, name.split('.').last())

        val diBuilder = DiBuilder(context.module, Path.of(declaredOn.fileName ?: "<unknown file>"), LlvmDwarfEmissionKind.None)
        val diFunction = diBuilder.createFunction(canonicalName, declaredOn.lineNumber.toUInt())

        BasicBlockBuilder.fillBody(context, function, diBuilder, diFunction, bodyGenerator)
    }
}