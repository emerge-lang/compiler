package compiler.ast

import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val modifiers: Set<FunctionModifier>,

    /**
     * The receiver type; is null if the declared function has no receiver.
     */
    val receiverType: TypeReference?,
    val name: IdentifierToken,
    val parameters: ParameterList,
    val returnType: TypeReference,
    val code: CodeChunk?
) : Declaration, Bindable<BoundFunction> {
    override fun bindTo(context: CTContext) = BoundFunction(
        context,
        this,
        parameters.bindTo(context),
        code?.bindTo(context)
    )
}