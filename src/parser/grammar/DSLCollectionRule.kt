package parser.grammar

import lexer.*
import matching.PredicateMatcher
import parser.Reporting
import parser.rule.FixedSequenceRule
import parser.rule.Rule

/**
 * A mutable subclass of [FixedSequenceRule] with DSL supporting methods
 */
interface DSLCollectionRule<ResultType> : Rule<ResultType>
{
    val subRules: MutableList<Rule<*>>

    /**
     * Matches exactly one [KeywordToken] with the given [lexer.Keyword]
     */
    fun keyword(kw: Keyword): Unit {
        subRules.add(Rule.singleton(PredicateMatcher(
                { it is KeywordToken && it.keyword == kw },
                TokenType.KEYWORD.name + " " + kw,
                Reporting.tokenMismatch(TokenType.KEYWORD.name + " " + kw)
        )))
    }

    /**
     * Matches exactly one [OperatorToken] with the given [Operator]
     */
    fun operator(op: Operator): Unit {
        subRules.add(Rule.singleton(PredicateMatcher(
                { it is OperatorToken && it.operator == op},
                TokenType.OPERATOR.name + " " + op,
                Reporting.tokenMismatch(TokenType.OPERATOR.name + " " + op)
        )))
    }

    /**
     * Matches exactly one [IdentifierToken]
     */
    fun identifier(): Unit
    {
        subRules.add(Rule.singleton(PredicateMatcher(
                { it is IdentifierToken },
                TokenType.IDENTIFIER.name,
                Reporting.tokenMismatch(TokenType.IDENTIFIER)
        )))
    }

    /**
     * Matches at least `times` occurences of the given rule
     */
    fun atLeast(times: Int, initFn: DSLFixedSequenceRule.() -> Any?): Unit
    {
        val rule = DSLFixedSequenceRule()
        rule.initFn()

        subRules.add(rule)
    }

    /**
     * Matches the first of any of the sub-rules
     */
    fun firstOf(initFn: DSLFirstOfRule.() -> Any?): Unit
    {
        val rule = DSLFirstOfRule()
        rule.initFn()

        subRules.add(rule)
    }
}
