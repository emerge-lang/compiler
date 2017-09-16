package compiler.binding.expression

import compiler.ast.expression.Expression
import compiler.ast.expression.IfExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.BuiltinBoolean
import compiler.nullableAnd
import compiler.parser.Reporting

class BoundIfExpression(
    override val context: CTContext,
    override val declaration: IfExpression,
    val condition: BoundExpression<Expression<*>>,
    val thenCode: BoundExecutable<*>,
    val elseCode: BoundExecutable<*>?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override val isGuaranteedToThrow: Boolean?
        get() = thenCode.isGuaranteedToThrow nullableAnd (elseCode?.isGuaranteedToThrow ?: false)

    override val isGuaranteedToReturn: Boolean?
        get() = thenCode.isGuaranteedToReturn nullableAnd (elseCode?.isGuaranteedToReturn ?: true)

    override var type: BaseTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        var reportings = condition.semanticAnalysisPhase1() + thenCode.semanticAnalysisPhase1()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase1()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        var reportings = condition.semanticAnalysisPhase2() + thenCode.semanticAnalysisPhase2()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase2()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        var reportings = mutableSetOf<Reporting>()

        reportings.addAll(condition.semanticAnalysisPhase3())
        reportings.addAll(thenCode.semanticAnalysisPhase3())

        if (elseCode != null) {
            reportings.addAll(elseCode.semanticAnalysisPhase3())
        }

        if (condition.type != null) {
            val conditionType = condition.type!!
            if (!conditionType.isAssignableTo(BuiltinBoolean.baseReference(context))) {
                reportings.add(Reporting.conditionIsNotBoolean(condition, condition.declaration.sourceLocation))
            }
        }

        return reportings
    }
}