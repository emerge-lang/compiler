package compiler.diagnostic

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.type.BoundTypeReference

class UnresolvedMemberVariableDiagnostic(
    val accessExpression: MemberAccessExpression,
    val hostType: BoundTypeReference?,
) : Diagnostic(
    Severity.ERROR,
    // TODO: find similarly named members (edit distance) and suggest. "Did you mean ... ?"
    "Type ${hostType ?: "Any"} does not have a member named \"${accessExpression.memberName.value}\"",
    accessExpression.memberName.span,
)