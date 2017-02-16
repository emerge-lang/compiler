/**
 *
 */
package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.ImportDeclaration
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.Reporting
import compiler.parser.TokenMismatchReporting
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ImportPostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<ImportDeclaration> {
    return rule

    // enhance error for "import xyz"
    .enhanceErrors(
        { it is TokenMismatchReporting && it.expected == OperatorToken(Operator.DOT) && it.actual == OperatorToken(Operator.NEWLINE) },
        { _it ->
            val it = _it as TokenMismatchReporting
            Reporting.Companion.error("${it.message}; To import all exports of the module write module.*", it.actual)
        }
    )
    .flatten()
    .trimWhitespaceTokens()
    .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): ImportDeclaration {
    // discard the import keyword
    tokens.next()

    val identifiers = ArrayList<String>()

    while (tokens.hasNext()) {
        // collect the identifier
        val identifierToken = tokens.next()!!

        if (identifierToken is IdentifierToken) {
            identifiers.add(identifierToken.value)
        }
        else if (identifierToken is OperatorToken) {
            // can only be *
            identifiers.add(identifierToken.operator.text)
        }
        else throw InternalCompilerError("Unexpected object type in lexer verified sequence - lexer bug? parser bug?")

        // skip the dot, if there
        tokens.next()
    }

    return ImportDeclaration(*identifiers.toTypedArray())
}