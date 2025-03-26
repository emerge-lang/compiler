package compiler.parser.grammar.rule

import compiler.lexer.Token

/**
 * Used to export the grammar to other formats (e.g. tree-sitter)
 */
interface GrammarVisitor<Reference : Any> {
    /**
     * Invoked for every [Rule] of the grammar, at all nesting levels. This function may be called many times for
     * the same instance of [Rule].
     *
     * If this function returns a non-null value, this means that [rule] should be referenced instead of detailed
     * out inline.
     */
    fun tryGetReference(rule: Rule<*>): Reference?

    fun visitReference(reference: Reference)

    fun visitSequence(subRules: Iterable<Rule<*>>)
    fun visitEitherOf(choices: Iterable<Rule<*>>)
    fun visitRepeating(repeated: Rule<*>, lowerBound: UInt, upperBound: UInt?)
    fun visitEndOfInput()

    fun visitDelimitedIdentifierContent()
    fun visitNonDelimitedIdentifier()

    fun visitNumericLiteral()
    fun visitStringContent()

    fun visitExpectedIdenticalToken(token: Token)
}