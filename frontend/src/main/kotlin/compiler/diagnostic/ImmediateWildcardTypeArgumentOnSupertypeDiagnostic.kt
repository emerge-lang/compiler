package compiler.diagnostic

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeVariance
import compiler.lexer.Span

class ImmediateWildcardTypeArgumentOnSupertypeDiagnostic(
    val erroneousArg: TypeArgument,
    val parameter: TypeParameter?,
) : Diagnostic(
    Severity.ERROR,
    "Wildcards are not supported as arguments of immediate supertypes; use variance and the actual bound instead: ${getSubstituteNotation(parameter)}",
    erroneousArg.span ?: Span.UNKNOWN
) {
    private companion object {
        fun getSubstituteNotation(parameter: TypeParameter?): String {
            val varianceStr = when (parameter?.variance) {
                TypeVariance.OUT,
                TypeVariance.IN -> ""
                TypeVariance.UNSPECIFIED,
                 null -> "out "
            }
            val boundStr = parameter?.bound?.toString() ?: "Any"
            return "$varianceStr $boundStr"
        }
    }
}