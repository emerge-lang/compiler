package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.binding.AccessorKind
import compiler.diagnostic.rendering.CellBuilder
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
    context(CellBuilder)
    override fun renderBody() {
        sourceHints(SourceHint(span, severity = severity))
        assureOnBlankLine()
        appendLineBreak()
        text(when (accessKind) {
            AccessorKind.Read -> "These options can all be used to obtain a value for ${memberVariableName.quoteIdentifier()}:"
            AccessorKind.Write -> "These options can all be used to set the value of `${memberVariableName.quoteIdentifier()}`:"
        })
        sourceHints(
            (actualMemberVariables.map { it.span } + possibleAccessorsDeclaredAt).map { SourceHint(it) }
        )
    }
}