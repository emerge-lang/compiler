package compiler.parser.grammar.rule

import compiler.lexer.Token

class SequenceRule(
    val subRules: Array<Rule<*>>,
    override val explicitName: String?,
) : Rule<SequenceRule.MatchedSequence> {
    init {
        require(subRules.isNotEmpty())
    }

    override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<MatchedSequence>> {
        return match(tokens, atIndex, emptyList(), 0)
    }

    private fun match(tokens: Array<Token>, atIndex: Int, priorResults: List<Any>, ruleIndex: Int): Sequence<MatchingResult<MatchedSequence>> {
        if (ruleIndex == subRules.lastIndex) {
            return subRules[ruleIndex].match(tokens, atIndex).map { lastOption ->
                when (lastOption) {
                    is MatchingResult.Error -> lastOption
                    is MatchingResult.Success -> MatchingResult.Success(MatchedSequence(priorResults + lastOption.item), lastOption.continueAtIndex)
                }
            }
        }

        return subRules[ruleIndex].match(tokens, atIndex).flatMap { stepOption ->
            when (stepOption) {
                is MatchingResult.Error -> sequenceOf(stepOption)
                is MatchingResult.Success -> match(tokens, stepOption.continueAtIndex, priorResults + stepOption.item, ruleIndex + 1)
            }
        }
    }

    override fun <R : Any> visit(visitor: GrammarVisitor<R>) {
        val reference = if (explicitName != null) visitor.tryGetReference(this) else null
        if (reference != null) {
            visitor.visitReference(reference)
        } else {
            visitNoReference(visitor)
        }
    }

    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitSequence(subRules.asIterable())
    }

    override fun toString() = explicitName ?: super.toString()

    data class MatchedSequence(val subResults: List<Any>)
}