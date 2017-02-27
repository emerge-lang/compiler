/**
 *
 */
package compiler.parser.postproc

import compiler.ast.ImportDeclaration
import compiler.ast.ModuleDeclaration
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
    .mapResult(::toAST_import)
}

private fun toAST_import(tokens: TransactionalSequence<Any, Position>): ImportDeclaration {
    // discard the import keyword
    tokens.next()

    val identifiers = ArrayList<IdentifierToken>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add(tokens.next()!! as IdentifierToken)

        // skip the dot, if there
        tokens.next()
    }

    return ImportDeclaration(identifiers)
}

fun ModuleDeclarationPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<ModuleDeclaration> {
    return rule
        .flatten()
        .trimWhitespaceTokens()
        .mapResult(::toAST_module)
}

private fun toAST_module(tokens: TransactionalSequence<Any, Position>): ModuleDeclaration {
    // discard the module keyword

    val identifiers = ArrayList<IdentifierToken>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add(tokens.next()!! as IdentifierToken)

        // skip the dot, if there
        tokens.next()
    }

    return ModuleDeclaration(identifiers)
}