package compiler.binding

import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

interface DefinitionWithVisibility {
    val visibility: BoundVisibility

    fun validateAccessFrom(location: SourceLocation): Collection<Reporting>

    fun toStringForErrorMessage(): String
}