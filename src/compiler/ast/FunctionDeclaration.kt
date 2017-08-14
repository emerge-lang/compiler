package compiler.ast

import compiler.ast.expression.Expression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

interface FunctionDeclaration : Declaration, Bindable<BoundFunction> {
    val modifiers: Set<FunctionModifier>
    /**
     * The receiver type; is null if the declared function has no receiver.
     */
    val receiverType: TypeReference?
    val name: IdentifierToken
    val parameters: ParameterList

    /**
     * The return type. Is null if none was declared and it has not been inferred yet (see semantic analysis phase 2)
     */
    val returnType: TypeReference?
}

/**
 * Default function declaration with curly-braced code or no code at all
 *
 *     external fun foobar() -> Int
 *     fun abc() {
 *         // code
 *     }
 */
class DefaultFunctionDeclaration(
    override val declaredAt: SourceLocation,
    override val modifiers: Set<FunctionModifier>,
     /**
      * The receiver type; is null if the declared function has no receiver.
      */
    override val receiverType: TypeReference?,
    override val name: IdentifierToken,
    override val parameters: ParameterList,
    parsedReturnType: TypeReference?,
    val code: CodeChunk?
) : FunctionDeclaration {
    override val returnType = parsedReturnType ?: compiler.binding.type.Unit.reference

    override fun bindTo(context: CTContext): BoundFunction {
        val functionContext = MutableCTContext(context)
        functionContext.swCtx = context.swCtx

        val boundParams = parameters.parameters.map(functionContext::addVariable)
        val boundParamList = BoundParameterList(context, parameters, boundParams)

        return BoundFunction(
            functionContext,
            this,
            boundParamList,
            code?.bindTo(functionContext)
        )
    }
}

/**
 * A function declaration defined with a single expression as the body:
 *
 *     fun abc() = foobar() + 3
 */
class SingleExpressionFunctionDeclaration(
    override val declaredAt: SourceLocation,
    override val modifiers: Set<FunctionModifier>,
    /**
     * The receiver type; is null if the declared function has no receiver.
     */
    override val receiverType: TypeReference?,
    override val name: IdentifierToken,
    override val parameters: ParameterList,
    override val returnType: TypeReference?,
    val expression: Expression<*>
) : FunctionDeclaration {
    override fun bindTo(context: CTContext): BoundFunction {
        val functionContext = MutableCTContext(context)
        functionContext.swCtx = context.swCtx

        val boundParams = parameters.parameters.map(functionContext::addVariable)
        val boundParamList = BoundParameterList(context, parameters, boundParams)

        return BoundFunction(
            functionContext,
            this,
            boundParamList,
            expression.bindTo(functionContext)
        )
    }
}