package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.reportings.Reporting

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {

    private var expectedReturnType: BaseTypeReference? = null

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
        val reportings = mutableSetOf<Reporting>()
        reportings += expression.semanticAnalysisPhase3()

        val expectedReturnType = this.expectedReturnType ?: throw InternalCompilerError("Return type not specified - cannot validate")
        val expressionType = expression.type

        if (expressionType != null) {
            if (!(expressionType isAssignableTo expectedReturnType)) {
                reportings += Reporting.returnTypeMismatch(expectedReturnType, expressionType, declaration.sourceLocation)
            }
        }

        return reportings
    }

    override fun enforceReturnType(type: BaseTypeReference) {
        expectedReturnType = type
    }
}