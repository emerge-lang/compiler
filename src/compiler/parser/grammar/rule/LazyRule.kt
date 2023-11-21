package compiler.parser.grammar.rule

import compiler.parser.TokenSequence

class LazyRule<T>(private val compute: () -> Rule<T>) : Rule<T> {
    private val rule by lazy(compute)

    override val explicitName get() = rule.descriptionOfAMatchingThing
    override val descriptionOfAMatchingThing get() = rule.descriptionOfAMatchingThing
    override fun tryMatch(context: Any, input: TokenSequence) = rule.tryMatch(context, input)
    override val minimalMatchingSequence get() = rule.minimalMatchingSequence
    override fun toString() = rule.toString()
}