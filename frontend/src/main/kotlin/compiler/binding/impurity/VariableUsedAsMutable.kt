package compiler.binding.impurity

import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.ValueUsage
import compiler.diagnostic.SourceHint

data class VariableUsedAsMutable(val referral: BoundIdentifierExpression.ReferringVariable, val usage: ValueUsage) :
    Impurity {
    override val span = referral.span
    override val kind = Impurity.ActionKind.MODIFY
    override val sourceHints get() = arrayOf(
        SourceHint(span = referral.span, "`${referral.variable.name}` is used with a mut type here"),
        SourceHint(span = usage.span, "mut reference is created here"),
    )
    override fun describe() = usage.describeForDiagnostic("`" + referral.variable.name + "`")
}