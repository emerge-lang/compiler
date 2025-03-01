package compiler.reportings

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

class VarianceOnInvocationTypeArgumentDiagnostic(
    val argument: TypeArgument,
) : Diagnostic(
    Level.ERROR,
    "Type parameters on invocations cannot have variance",
    argument.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as VarianceOnInvocationTypeArgumentDiagnostic

        return argument.span == other.argument.span
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + argument.span.hashCode()
        return result
    }
}