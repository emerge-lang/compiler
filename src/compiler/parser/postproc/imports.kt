/**
 *
 */
package compiler.parser.postproc

import compiler.ast.ImportDeclaration
import compiler.ast.ModuleDeclaration
import compiler.lexer.*
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
    val keyword = tokens.next()!! as KeywordToken

    val identifiers = ArrayList<IdentifierToken>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add(tokens.next()!! as IdentifierToken)

        // skip the dot, if there
        tokens.next()
    }

    return ImportDeclaration(keyword.sourceLocation ?: SourceLocation.UNKNOWN, identifiers)
}

fun ModuleDeclarationPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<ModuleDeclaration> {
    return rule
        .flatten()
        .trimWhitespaceTokens()
        .mapResult(::toAST_moduleDeclaration)
}

private fun toAST_moduleDeclaration(tokens: TransactionalSequence<Any, Position>): ModuleDeclaration {
    val keyword = tokens.next()!! as KeywordToken

    val identifiers = ArrayList<String>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add((tokens.next()!! as IdentifierToken).value)

        // skip the dot, if there
        tokens.next()
    }

    return ModuleDeclaration(keyword.sourceLocation ?: SourceLocation.UNKNOWN, identifiers.toTypedArray())
}