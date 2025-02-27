package compiler.binding

import compiler.lexer.Span
import compiler.reportings.Diagnosis

interface DefinitionWithVisibility {
    val visibility: BoundVisibility

    fun validateAccessFrom(location: Span, diagnosis: Diagnosis)

    fun toStringForErrorMessage(): String
}