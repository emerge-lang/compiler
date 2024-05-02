package compiler.reportings

import compiler.lexer.IdentifierToken
import compiler.lexer.Span

class UnconventionalTypeNameReporting(
    val typename: IdentifierToken,
    val violatedConvention: ViolatedConvention,
) : Reporting(
    Level.WARNING,
    violatedConvention.name,
    violatedConvention.transformLocation(typename.span)
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        if (!super.equals(other)) return false

        other as UnconventionalTypeNameReporting

        return span == other.span
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }

    enum class ViolatedConvention(val message: String) {
        FIRST_LETTER_UPPERCASE("Type names should start with an uppercase letter"),
        UPPER_CAMEL_CASE("Type names should be UpperCamelCase"),
        ;

        fun transformLocation(nameLocation: Span): Span = when(this) {
            FIRST_LETTER_UPPERCASE -> nameLocation.copy(
                toLineNumber = nameLocation.fromLineNumber,
                toColumnNumber = nameLocation.fromColumnNumber,
            )
            else -> nameLocation
        }
    }
}