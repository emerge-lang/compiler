package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

class AmbiguousMemberVariableAccessDiagnostic(
    val memberVariableName: String,
    val actualMemberVariable: BaseTypeMemberVariableDeclaration?,
    val possibleAccessorsDeclaredAt: Collection<Span>,
    referenceAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "This reference to member variable `${memberVariableName}` is ambiguous.",
    referenceAt,
) {
    override fun toString(): String {
        return "$levelAndMessage\n" +
            illustrateSourceLocations(setOf(span)) +
            "\nThese options can all be used to supply a value:\n" +
            illustrateSourceLocations(listOfNotNull(actualMemberVariable?.span) + possibleAccessorsDeclaredAt)
    }
}