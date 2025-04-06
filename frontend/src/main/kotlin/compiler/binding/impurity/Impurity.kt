package compiler.binding.impurity

import compiler.diagnostic.SourceHint
import compiler.lexer.Span

sealed interface Impurity {
    val span: Span
    val kind: ActionKind
    val sourceHints: Array<SourceHint>
        get() = arrayOf(SourceHint(span = span, description = null))

    fun describe(): String

    enum class ActionKind {
        READ,
        MODIFY,
        ;
    }
}