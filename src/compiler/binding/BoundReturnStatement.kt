package compiler.binding

import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {

    val expression = declaration.expression.bindTo(context)

    var returnType: BaseTypeReference? = null
        private set

    override val isGuaranteedToReturn = true // this is the core LoC that makes the property work big-scale
    override val mayReturn = true            // this is the core LoC that makes the property work big-scale

    override val isGuaranteedToThrow = expression.isGuaranteedToThrow

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return expression.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return expression.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return expression.semanticAnalysisPhase3()
    }
}