package compiler.binding.impurity

import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.ValueUsage

data class ReadingVariableBeyondBoundary(
    val readingExpression: BoundIdentifierExpression,
    val referral: BoundIdentifierExpression.ReferringVariable,
    val usage: ValueUsage
): Impurity {
    override val span = readingExpression.declaration.span
    override val kind = Impurity.ActionKind.READ
    override fun describe(): String = usage.describeForDiagnostic('`' + referral.variable.name + '`')
}