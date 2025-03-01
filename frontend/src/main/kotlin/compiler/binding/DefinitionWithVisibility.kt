package compiler.binding

import compiler.lexer.Span
import compiler.diagnostic.Diagnosis

interface DefinitionWithVisibility {
    val visibility: BoundVisibility

    fun validateAccessFrom(location: Span, diagnosis: Diagnosis)

    fun toStringForErrorMessage(): String
}