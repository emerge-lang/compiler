package compiler.binding.impurity

import compiler.diagnostic.Diagnostic
import compiler.diagnostic.SourceHint
import compiler.lexer.Span

sealed interface Impurity {
    val span: Span
    val kind: ActionKind
    val sourceHints: Collection<SourceHint>
        get() = listOf(SourceHint(span = span, severity = Diagnostic.Severity.ERROR))

    fun describe(): String

    enum class ActionKind {
        READ,
        MODIFY,
        ;
    }
}