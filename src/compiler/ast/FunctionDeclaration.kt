package compiler.ast

import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.lexer.*

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val modifiers: Set<FunctionModifier>,
    /**
     * The receiver type; is null if the declared function has no receiver.
     */
    val receiverType: TypeReference?,
    val name: IdentifierToken,
    val parameters: ParameterList,
    parsedReturnType: TypeReference?,
    val code: CodeChunk?
) : Declaration, Bindable<BoundFunction> {

    /**
     * The return type. Is null if none was declared and it has not been inferred yet (see semantic analysis phase 2)
     */
    val returnType = parsedReturnType ?: compiler.binding.type.Unit.reference

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