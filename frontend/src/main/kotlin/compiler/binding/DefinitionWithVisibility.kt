package compiler.binding

import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

sealed interface DefinitionWithVisibility {
    fun validateAccessFrom(location: SourceLocation): Collection<Reporting>
}