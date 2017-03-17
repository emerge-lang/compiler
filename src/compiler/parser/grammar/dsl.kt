package compiler.parser.grammar

import compiler.lexer.*
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.*

fun rule(initFn: DSLFixedSequenceRule.() -> Any?): Rule<List<RuleMatchingResult<*>>> {
    val rule = DSLFixedSequenceRule()
    // any rule can be preceeded by whitespace
    rule.optionalWhitespace()

    rule.initFn()

    return rule
}

fun <T> Rule<T>.describeAs(description: String): Rule<T> {
    val base = this
    return object : Rule<T> {
        override val descriptionOfAMatchingThing = description

        override fun tryMatch(input: TokenSequence): RuleMatchingResult<T> {
            return base.tryMatch(input)
        }
    }
}

fun <ResultBefore,ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)

/**
 * A mutable subclass of [FixedSequenceRule] with DSL supporting methods
 */
interface DSLCollectionRule<ResultType> : Rule<ResultType>
{
    val subRules: MutableList<Rule<*>>

    fun sequence(initFn: DSLFixedSequenceRule.() -> Any?): Unit {
        subRules.add(rule(initFn))
    }

    /**
     * Matches exactly one [KeywordToken] with the given [lexer.Keyword]
     */
    fun keyword(kw: Keyword, mismatchCertainty: ResultCertainty = ResultCertainty.NOT_RECOGNIZED): Unit {
        subRules.add(Rule.singleton(KeywordToken(kw), mismatchCertainty))
    }

    fun operator(op: Operator?): Unit {
        if (op == null) {
            subRules.add(Rule.singletonOfType(TokenType.OPERATOR))
        }
        else {
            subRules.add(Rule.singleton(OperatorToken(op)))
        }
    }

    /**
     * Matches exactly one [OperatorToken] with the given [Operator]
     */
    fun eitherOf(vararg op: Operator): Unit {
        if (op.size == 0) return
        if (op.size == 1) {
            subRules.add(Rule.singleton(OperatorToken(op[0])))
        }

        subRules.add(
            EitherOfRule(
                op.map { it -> Rule.singleton(OperatorToken(it))}
            )
        )
    }

    /**
     * Matches exactly one [IdentifierToken]
     */
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList()): Unit
    {
        if (acceptedOperators.isEmpty() && acceptedKeywords.isEmpty()) {
            subRules.add(Rule.singletonOfType(TokenType.IDENTIFIER))
        } else {
            subRules.add(TolerantIdentifierMatchingRule(acceptedOperators, acceptedKeywords))
        }
    }

    fun optional(initFn: DSLFixedSequenceRule.() -> Any?): Unit
    {
        val subRule = DSLFixedSequenceRule()
        subRule.initFn()

        subRules.add(OptionalRule(subRule))
    }

    /**
     * Skips whitespace (newlines); Always matches successfully with [ResultCertainty.NOT_RECOGNIZED]
     * TODO: horrible name, possibly horrible mechanic... refactor this whenever things become more clear
     */
    fun optionalWhitespace(): Unit
    {
        subRules.add(WhitespaceEaterRule.instance)
    }

    /**
     * Matches at least `times` occurences of the given rule
     */
    fun atLeast(times: Int, initFn: DSLFixedSequenceRule.() -> Any?): Unit
    {
        val rule = DSLFixedSequenceRule()
        rule.initFn()

        subRules.add(VariableTimesRule(rule, IntRange(times, Int.MAX_VALUE)))
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

    /**
     * Adds [ExpressionRule.INSTANCE] to the list of subrules
     */
    fun expression(): Unit {
        subRules.add(ExpressionRule.INSTANCE)
    }

    /**
     * Adds [CodeChunkRule.INSTANCE] tp the list of subrules
     */
    fun codeChunk(): Unit {
        subRules.add(CodeChunkRule.INSTANCE)
    }

    /**
     * Matches a single token of the given type, see [Rule.Companion.singletonOfType]
     */
    fun tokenOfType(type: TokenType): Unit {
        subRules.add(Rule.singletonOfType(type))
    }

    /**
     * Matches the end of the givne token sequence.
     */
    fun endOfInput() {
        subRules.add(EOIRule.INSTANCE)
    }
}

class DSLEitherOfRule(
        override val subRules: MutableList<Rule<*>> = mutableListOf()
) : DSLCollectionRule<Any?>, EitherOfRule(subRules)

class DSLFixedSequenceRule(
    override val subRules: MutableList<Rule<*>> = mutableListOf(),
    private val certaintySteps: MutableList<Pair<Int, ResultCertainty>> = mutableListOf(0 to ResultCertainty.NOT_RECOGNIZED)
) : FixedSequenceRule(subRules, certaintySteps), DSLCollectionRule<List<RuleMatchingResult<*>>>
{
    /**
     * Reading from this property: returns the level of certainty the rule has at the current point of configuration
     * Writing to this property: if the previous rule matches successfully, sets the certainty level of the result
     * to the given [ResultCertainty]
     */
    var __certainty: ResultCertainty
        get() = certaintySteps.last().second
        set(c)
        {
            val lastStep = certaintySteps.last()
            val currentIndex = subRules.lastIndex
            if (c.level <= lastStep.second.level)
            {
                throw MisconfigurationException("Certainty steps have to increase; last was " + lastStep.second + ", new one is " + c)
            }

            if (lastStep.first == currentIndex)
            {
                certaintySteps.removeAt(certaintySteps.lastIndex)
            }

            certaintySteps.add(currentIndex to c)
        }

    /**
     * Sets certainty at this matching stage to [ResultCertainty.MATCHED]
     */
    fun __matched(): Unit
    {
        __certainty = ResultCertainty.MATCHED
    }

    /**
     * Sets certainty at this matching stage to [ResultCertainty.OPTIMISTIC]
     */
    fun __optimistic(): Unit
    {
        __certainty = ResultCertainty.OPTIMISTIC
    }

    /**
     * Sets certainty at this matching stage to [ResultCertainty.DEFINITIVE]
     */
    fun __definitive(): Unit
    {
        __certainty = ResultCertainty.DEFINITIVE
    }
}