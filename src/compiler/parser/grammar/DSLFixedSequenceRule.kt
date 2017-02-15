package compiler.parser.grammar

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.FixedSequenceRule
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.MisconfigurationException
import compiler.parser.rule.Rule

class DSLFixedSequenceRule(
    override val subRules: MutableList<Rule<*>> = mutableListOf(),
    private val certaintySteps: MutableList<Pair<Int, ResultCertainty>> = mutableListOf(0 to ResultCertainty.OPTIMISTIC)
) : FixedSequenceRule(subRules, certaintySteps), DSLCollectionRule<List<MatchingResult<*>>>
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
     * Sets certainty at this compiler.matching stage to [ResultCertainty.DEFINITIVE]
     */
    fun __definitive(): Unit
    {
        __certainty = ResultCertainty.DEFINITIVE
    }
}
