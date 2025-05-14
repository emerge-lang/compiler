package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.binding.AccessorKind
import compiler.lexer.Span

class AmbiguousMemberVariableAccessDiagnostic(
    val memberVariableName: String,
    val accessKind: AccessorKind,
    val actualMemberVariables: Collection<BaseTypeMemberVariableDeclaration>,
    val possibleAccessorsDeclaredAt: Collection<Span>,
    referenceAt: Span,
) : Diagnostic(
    Severity.ERROR,
    run {
        val virtualStr = if (actualMemberVariables.isEmpty()) "virtual " else ""
        "This reference to ${virtualStr}member variable `${memberVariableName}` is ambiguous."
    },
    referenceAt,
) {
    override fun toString(): String {
        return "$levelAndMessage\n" +
            illustrateSourceLocations(setOf(span)) +
            when (accessKind) {
                AccessorKind.Read -> "\nThese options can all be used to obtain a value for `$memberVariableName`:\n"
                AccessorKind.Write -> "\nThese options can all be used to set the value of `$memberVariableName`:\n"
            } +
            illustrateSourceLocations(actualMemberVariables.map { it.span } + possibleAccessorsDeclaredAt)
    }
}