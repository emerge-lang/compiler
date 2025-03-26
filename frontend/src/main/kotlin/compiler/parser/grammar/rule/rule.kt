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

package compiler.parser.grammar.rule

import compiler.InternalCompilerError
import compiler.lexer.Token
import compiler.diagnostic.ParsingMismatchDiagnostic

sealed interface MatchingResult<out Item : Any> {
    class Success<out Item : Any>(val item: Item, val continueAtIndex: Int) : MatchingResult<Item>
    class Error(val diagnostic: ParsingMismatchDiagnostic) : MatchingResult<Nothing>
}

interface Rule<out Item : Any> {
    val explicitName: String?

    /*
    optimization potential: whenever there is a branch, a flatMap on the Sequence is required. This involves a bunch
    of heap allocations and uses stack frames. Instead, have this matching function suspend and have a receiver
    of type SequenceScope<MatchingResult>. The matching function would then just yield() to the SequenceScope, making
    that flatMap more efficient.
     */
    fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<Item>>

    fun <R : Any> visit(visitor: GrammarVisitor<R>) {
        val reference = visitor.tryGetReference(this)
        if (reference == null) {
            visitNoReference(visitor)
        } else {
            visitor.visitReference(reference)
        }
    }
    fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>)
}

fun <Item : Any> matchAgainst(tokens: Array<Token>, rule: Rule<Item>): MatchingResult<Item> {
    require(tokens.isNotEmpty()) { "Cannot match an empty token sequence" }
    var diagnostic: ParsingMismatchDiagnostic? = null
    for (resultOption in rule.match(tokens, 0)) {
        when (resultOption) {
            is MatchingResult.Success -> return resultOption
            is MatchingResult.Error -> diagnostic = if (diagnostic == null) {
                resultOption.diagnostic
            } else {
                reduceCombineParseError(
                    diagnostic,
                    resultOption.diagnostic
                )
            }
        }
    }

    diagnostic ?: throw InternalCompilerError("No options from rule")
    return MatchingResult.Error(diagnostic)
}

private val parseErrorComparator: Comparator<ParsingMismatchDiagnostic> =
    compareBy<ParsingMismatchDiagnostic> { it.severity }
        .thenBy { it.span.fromLineNumber }
        .thenBy { it.span.fromColumnNumber }

internal fun reduceCombineParseError(a: ParsingMismatchDiagnostic, b: ParsingMismatchDiagnostic): ParsingMismatchDiagnostic {
    val comparison = parseErrorComparator.compare(a, b)
    when {
        comparison > 0 -> return a
        comparison < 0 -> return b
    }

    // same location and severity
    return ParsingMismatchDiagnostic((a.expectedAlternatives + b.expectedAlternatives).toSet(), a.actual)
}