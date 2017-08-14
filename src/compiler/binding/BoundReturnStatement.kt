package compiler.binding

import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {

    val expression = declaration.expression.bindTo(context)

    var returnType: BaseTypeReference? = null
        private set

    override val isGuaranteedToReturn = true // this is the core LoC that makes the property work big-scale

    override val isGuaranteedToThrow = expression.isGuaranteedToThrow
}