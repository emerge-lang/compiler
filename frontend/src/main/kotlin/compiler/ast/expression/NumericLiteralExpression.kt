/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundFloatingPointLiteral
import compiler.binding.expression.BoundIntegerLiteral
import compiler.binding.expression.BoundNumericLiteral
import compiler.lexer.NumericLiteralToken
import compiler.diagnostic.Diagnostic
import java.math.BigDecimal
import java.math.BigInteger

class NumericLiteralExpression(val literalToken: NumericLiteralToken) : Expression {

    /** integer value of this expression, if integer */
    private var integerValue: BigInteger? = null

    /** if [integerValue] is not null, this is the base used in the source program to represent that number */
    private var integerBase: UInt = 10u

    /** floating point value of this expression, if floating */
    private var floatingValue: BigDecimal? = null

    /** Cached validation result; numeric literals are the same in every context */
    private var validationResult: Collection<Diagnostic>? = null

    override val span = literalToken.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundNumericLiteral {
        validateAndInitialize()

        if (integerValue != null) {
            return BoundIntegerLiteral(
                context,
                this,
                integerValue!!,
                integerBase,
                validationResult!!
            )
        }

        if (floatingValue != null) {
            return BoundFloatingPointLiteral(
                context,
                this,
                floatingValue!!,
                validationResult!!
            )
        }

        return BoundNumericLiteral(
            context,
            this,
            validationResult ?: setOf(Diagnostic.erroneousLiteralExpression("Could not determine type of numeric literal", this.span))
        )
    }

    /**
     * initializes this object, assigns meaningful values to
     * * [validationResult]
     * * [integerValue] and [integerBase]
     * * [floatingValue]
     */
    private fun validateAndInitialize() {
        if (validationResult != null) return

        val str = literalToken.stringContent

        if (str.startsWith("0x")) {
            validateAndInitializeAsInteger()
        } else if (str.contains('.') || str.endsWith('f') || str.contains('e')) {
            validateAndInitializeAsFloatingPoint()
        }
        else {
            validateAndInitializeAsInteger()
        }
    }

    private fun validateAndInitializeAsFloatingPoint() {
        var str = literalToken.stringContent

        if (str.endsWith('f')) {
            str = str.substring(0, str.lastIndex)
        }

        var allowedChars = ('0' .. '9') + arrayOf('.', 'e', 'E', '-')
        val unallowed = str.minus(allowedChars)
        if (unallowed.isNotEmpty()) {
            validationResult = setOf(Diagnostic.erroneousLiteralExpression(
                "Floating point literal contains forbidden characters: ${unallowed.unique()}",
                literalToken.span
            ))
            return
        }

        // cut e
        val expIndex = str.lowercase().indexOf('e')
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
            validationResult = setOf(Diagnostic.erroneousLiteralExpression(
                "Floating point literal contains non-decimal characters before the floating point: ${preComma.minus(allowedChars).unique()}",
                literalToken.span
            ))
            return
        }

        if (postComma != null && !postComma.map(Char::isDigit).reduce(Boolean::and)) {
            // postComma is not OK
            validationResult = setOf(Diagnostic.erroneousLiteralExpression(
                "Floating point literal contains non-decimal characters after the floating point: ${postComma.minus(allowedChars).unique()}",
                literalToken.span
            ))
            return
        }

        if (exp != null && exp.isBlank()) {
            validationResult =  setOf(Diagnostic.erroneousLiteralExpression(
                "Empty exponent in floating point literal",
                literalToken.span
            ))
            return
        }

        if (exp != null && exp.map(Char::isDigit).reduce(Boolean::and)) {
            // exponent is not OK
            validationResult = setOf(Diagnostic.erroneousLiteralExpression(
                "Floating point literal contains non-decimal characters in the exponent: ${exp.minus(allowedChars).unique()}",
                literalToken.span
            ))
            return
        }

        floatingValue = BigDecimal(str)
        validationResult = emptySet()
    }

    private fun validateAndInitializeAsInteger() {
        var str = literalToken.stringContent

        val allowedChars: Collection<Char>
        if (str.startsWith("0x")) {
            integerBase = 16u
            allowedChars = ('0'..'9') + ('a'..'f') + ('A'..'F')
            str = str.substring(2)
        }
        else if (str.startsWith("0b")) {
            integerBase = 2u
            allowedChars = setOf('0', '1')
            str = str.substring(2)
        }
        else if (str.endsWith("oct")) {
            integerBase = 8u
            allowedChars = ('0'..'7').toList()
            str = str.dropLast(3)
        }
        else {
            integerBase = 10u
            allowedChars = ('0'..'9').toList()
        }

        val unallowed = str.minus(allowedChars + listOf('-'))
        if (unallowed.isNotEmpty()) {
            validationResult = setOf(Diagnostic.erroneousLiteralExpression(
                "Integer literal contains unallowed characters: ${unallowed.unique()}",
                literalToken.span
            ))
            return
        }

        integerValue = BigInteger(str, integerBase.toInt())
        validationResult = emptySet()
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