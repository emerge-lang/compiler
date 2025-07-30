package compiler.diagnostic

import compiler.ast.type.AstTypeArgument
import compiler.ast.type.TypeParameter
import compiler.lexer.Span

class ImmediateWildcardTypeArgumentOnSupertypeDiagnostic(
    val erroneousArg: AstTypeArgument,
    val parameter: TypeParameter?,
) : Diagnostic(
    Severity.ERROR,
    "Wildcards are not supported as arguments of immediate supertypes; use variance and the actual bound instead: ${getSubstituteNotation(parameter)}",
    erroneousArg.span ?: Span.UNKNOWN
) {
    private companion object {
        fun getSubstituteNotation(parameter: TypeParameter?): String {
            val boundStr = parameter?.bound?.toString() ?: "Any"
            return "out $boundStr"
        }
    }
}