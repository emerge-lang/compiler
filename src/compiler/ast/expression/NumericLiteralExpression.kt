package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.Float
import compiler.binding.type.Int
import compiler.binding.type.Number
import compiler.lexer.NumericLiteralToken
import compiler.lexer.SourceLocation
import compiler.parser.Reporting
import java.math.BigDecimal
import java.math.BigInteger

class NumericLiteralExpression(val literalToken: NumericLiteralToken) : Expression {

    /** integer value of this expression, if integer */
    private var integerValue: BigInteger? = null

    /** floating point value of this expression, if floating */
    private var floatingValue: BigDecimal? = null

    private var validationResult: Collection<Reporting>? = null

    override val sourceLocation = literalToken.sourceLocation

    /** Validates this expression */
    fun validate(): Collection<Reporting> {
        if (validationResult != null) return validationResult!!

        var str = literalToken.stringContent

        if (str.contains('.') || str.endsWith('f') || str.contains('e')) {
            // Floating point
            if (str.endsWith('f')) {
                str = str.substring(0, str.lastIndex - 1)
            }

            var allowedChars = ('0' .. '9') + arrayOf('.', 'e', 'E')
            val unallowed = str.minus(allowedChars)
            if (unallowed.isNotEmpty()) {
                return setOf(Reporting.error(
                    "Floating point literal contains unallowed characters: ${unallowed.unique()}",
                    literalToken
                ))
            }

            // cut e
            val expIndex = str.toLowerCase().indexOf('e')
            val exp: String?
            if (expIndex >= 0) {
                exp = str.substring(expIndex + 1)
                str = str.substring(0 .. expIndex - 1)
            }
            else {
                exp = null
            }

            val fpIndex = str.indexOf('.')
            val preComma: String
            val postComma: String?

            if (fpIndex >= 0) {
                preComma = str.substring(0 .. fpIndex - 1)
                postComma = str.substring(fpIndex + 1)
            }
            else {
                preComma = str
                postComma = null
            }

            allowedChars = ('0'..'9').toList()

            if (!preComma.map(Char::isDigit).reduce(Boolean::and)) {
                // preComma is not OK
                return setOf(Reporting.error(
                    "Floating point literal contains non-decimal characters before the floating point: ${preComma.minus(allowedChars).unique()}",
                    literalToken
                ))
            }

            if (postComma != null && !postComma.map(Char::isDigit).reduce(Boolean::and)) {
                // postComma is not OK
                return setOf(Reporting.error(
                    "Floating point literal contains non-decimal characters after the floating point: ${postComma.minus(allowedChars).unique()}",
                    literalToken
                ))
            }

            if (exp != null && exp.isBlank()) {
                return setOf(Reporting.error(
                    "Empty exponent in floating point literal",
                    literalToken
                ))
            }

            if (exp != null && exp.map(Char::isDigit).reduce(Boolean::and)) {
                // exponent is not OK
                return setOf(Reporting.error(
                    "Floating point literal contains non-decimal characters in the exponent: ${exp.minus(allowedChars).unique()}",
                    literalToken
                ))
            }

            floatingValue = BigDecimal(str)
            return emptySet()
        }
        else {
            // Integer
            val base: Int
            val allowedChars: Collection<Char>
            if (str.startsWith("0x")) {
                base = 16
                allowedChars = ('0'..'9') + ('a'..'f') + ('A'..'F')
                str = str.substring(2)
            }
            else if (str.startsWith("0b")) {
                base = 2
                allowedChars = setOf('0', '1')
                str = str.substring(2)
            }
            else if (str.endsWith("oct")) {
                base = 8
                allowedChars = ('0'..'7').toList()
                str = str.dropLast(3)
            }
            else {
                base = 10
                allowedChars = ('0'..'9').toList()
            }

            val unallowed = str.minus(allowedChars)
            if (unallowed.isNotEmpty()) {
                return setOf(Reporting.error(
                    "Integer literal contains unallowed characters: ${unallowed.unique()}",
                    literalToken
                ))
            }

            integerValue = BigInteger(str, base)
            return emptySet()
        }
    }

    override fun determineType(context: CTContext): BaseTypeReference {
        validate()

        if (integerValue != null) {
            return Int.baseReference(context)
        }
        else if (floatingValue != null) {
            return Float.baseReference(context)
        }
        else {
            return Number.baseReference(context)
        }
    }
}

/**
 * Returns a string with any char contained in the given chars removed from it.
 */
private fun String.minus(chars: Collection<Char>): String {
    return this.filter { char -> !chars.contains(char) }
}

private fun String.unique(): String {
    return this.toSet().joinToString()
}