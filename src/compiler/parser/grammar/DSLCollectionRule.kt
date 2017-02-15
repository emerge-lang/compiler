package compiler.parser.grammar

import compiler.lexer.*
import compiler.matching.PredicateMatcher
import compiler.parser.Reporting
import compiler.parser.rule.FixedSequenceRule
import compiler.parser.rule.OptionalRule
import compiler.parser.rule.Rule

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
        subRules.add(Rule.singleton(KeywordToken(kw)))
    }

    /**
     * Matches exactly one [OperatorToken] with the given [Operator]
     */
    fun operator(op: Operator): Unit {
        subRules.add(Rule.singleton(OperatorToken(op)))
    }

    /**
     * Matches exactly one [IdentifierToken]
     */
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList()): Unit
    {
        subRules.add(Rule.singletonOfType(TokenType.IDENTIFIER))
    }

    fun optional(initFn: DSLFixedSequenceRule.() -> Any?): Unit
    {
        val subRule = DSLFixedSequenceRule()
        subRule.initFn()

        subRules.add(OptionalRule(subRule))
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
    fun eitherOf(initFn: DSLEitherOfRule.() -> Any?): Unit
    {
        val rule = DSLEitherOfRule()
        rule.initFn()

        subRules.add(rule)
    }

    /**
     * Adds the given rule to the list of subrules
     */
    fun ref(otherRule: Rule<*>): Unit {
        subRules.add(otherRule)
    }
}
