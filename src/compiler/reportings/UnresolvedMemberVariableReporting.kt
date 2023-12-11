package compiler.reportings

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.type.ResolvedTypeReference

class UnresolvedMemberVariableReporting(
    val accessExpression: MemberAccessExpression,
    val hostType: ResolvedTypeReference,
) : Reporting(
    Level.ERROR,
    // TODO: find similarly named members (edit distance) and suggest. "Did you mean ... ?"
    "Type $hostType does not have a member named \"${accessExpression.memberName.value}\"",
    accessExpression.memberName.sourceLocation,
)