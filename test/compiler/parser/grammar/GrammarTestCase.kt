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

package compiler.parser.grammar

import compiler.lexer.*
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.toTransactional
import io.kotlintest.specs.FreeSpec

abstract class GrammarTestCase : FreeSpec() {
    fun lex(code: String): TokenSequence {
        var source = object : SourceContentAwareSourceDescriptor() {
            override val sourceLocation = "testcode"
            override val sourceLines = code.split("\n")
        }

        return compiler.lexer.lex(code, source).toTransactional(source.toLocation(1, 1))
    }

    fun tokenSequence(sequenceDefinition: TokenSequenceGenerator.() -> Unit): TokenSequence {
        val generator = TokenSequenceGenerator()
        generator.sequenceDefinition()
        return generator.toTransactional()
    }

    fun <R> TokenSequence.matchAgainst(rule: Rule<R>): RuleMatchingResult<R> = rule.tryMatch(this)
}

class TokenSequenceGenerator {

    private val tokens: MutableList<Token> = ArrayList()

    private var currentLine = 1
    private var currentColumn = 1
    private val locationModificationMutex = Any()

    private val sD = SimpleSourceDescriptor("mocked tokens")
    private val initialSourceLocation = SourceLocation(sD, 1, 1)

    fun toTransactional(): TokenSequence {
        return TokenSequence(ArrayList(tokens), initialSourceLocation)
    }

    fun identifier(value: String) {
        var location: SourceLocation? = null

        synchronized(locationModificationMutex) {
            location = SourceLocation(sD, currentLine, currentColumn)
            currentColumn += value.length + 1
        }

        tokens += IdentifierToken(value, location!!)
    }

    fun keyword(keyword: Keyword) {
        var location: SourceLocation? = null

        synchronized(locationModificationMutex) {
            location = SourceLocation(sD, currentLine, currentColumn)
            currentColumn += keyword.text.length + 1
        }

        tokens += KeywordToken(keyword, keyword.text, location!!)
    }

    fun operator(operator: Operator) {
        var location: SourceLocation? = null

        synchronized(locationModificationMutex) {
            location = SourceLocation(sD, currentLine, currentColumn)

            if (operator == Operator.NEWLINE) {
                currentLine++
                currentColumn = 1
            } else {
                currentColumn += operator.text.length + 1
            }
        }

        tokens += OperatorToken(operator, location!!)
    }

    fun newline() {
        operator(Operator.NEWLINE)
    }

    fun mockRef(replacement: Any) {
        var location: SourceLocation? = null

        synchronized(locationModificationMutex) {
            location = SourceLocation(sD, currentLine, currentColumn)
            currentColumn += 2
        }

        tokens += NestedRuleMockingToken(replacement, location!!)
    }
}

/**
 * To be used as a placeholder for nested rules. E.g. the rule [ParameterList] uses [GrammarReceiver.ref] with
 * [VariableDeclaration] as the parameter. An instance of this class can be used instead of actual tokens resembling
 * the variable declaration. The given [replacement] will be returned as if the nested rule had parsed it.
 */
class NestedRuleMockingToken(val replacement: Any, override val sourceLocation: SourceLocation) : Token() {
    override val type: TokenType = TokenType.OPERATOR
}