package compiler.binding

import compiler.ast.Expression
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.conditionIsNotBoolean
import compiler.diagnostic.mutationInCondition

class BoundCondition(
    val expression: BoundExpression<*>,
) : BoundExpression<Expression> by expression {
    override val type: BoundTypeReference get() = context.swCtx.bool.baseReference

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase2(diagnosis)

        if (expression.type?.isAssignableTo(context.swCtx.bool.baseReference) == false) {
            diagnosis.conditionIsNotBoolean(expression)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase3(diagnosis)

        expression.visitWritesBeyond(
            context,
            object : ImpurityVisitor {
                override fun visitReadBeyondBoundary(purityBoundary: CTContext, read: BoundExpression<*>) {
                    // reading in conditions is okay
                }

                override fun visitWriteBeyondBoundary(purityBoundary: CTContext, write: BoundExecutable<*>) {
                    diagnosis.mutationInCondition(write)
                }
            }
        )
    }
}