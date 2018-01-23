package compiler.binding.expression

import compiler.ast.expression.Expression
import compiler.ast.expression.IfExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.Unit
import compiler.nullableAnd
import compiler.reportings.Reporting

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
        get() {
            if (elseCode == null) {
                return false
            }
            else {
                return thenCode.isGuaranteedToReturn nullableAnd elseCode.isGuaranteedToReturn
            }
        }

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

        var thenType = if (thenCode is BoundExpression<*>) thenCode.type else Unit.baseReference(context)
        var elseType = if (elseCode is BoundExpression<*>) elseCode.type else Unit.baseReference(context)

        if (thenType != null && elseType != null) {
            type = BaseTypeReference.closestCommonAncestorOf(thenType, elseType)
        }

        return reportings
    }

    override fun enforceReturnType(type: BaseTypeReference) {
        thenCode.enforceReturnType(type)
        elseCode?.enforceReturnType(type)
    }
}