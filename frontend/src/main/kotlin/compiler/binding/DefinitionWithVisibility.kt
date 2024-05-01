package compiler.binding

import compiler.lexer.Span
import compiler.reportings.Reporting

interface DefinitionWithVisibility {
    val visibility: BoundVisibility

    fun validateAccessFrom(location: Span): Collection<Reporting>

    fun toStringForErrorMessage(): String
}