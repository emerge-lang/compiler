package compiler.binding.classdef

import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SemanticallyAnalyzable
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

sealed interface BoundClassMember : BoundClassEntry, SemanticallyAnalyzable, DefinitionWithVisibility {
    val visibility: BoundVisibility
    val name: String

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }
}