package compiler.parser.grammar.rule

import compiler.parser.TokenSequence

class LazyRule<T>(private val compute: () -> Rule<T>) : Rule<T> {
    private val rule by lazy(compute)

    override val explicitName get() = rule.descriptionOfAMatchingThing
    override val descriptionOfAMatchingThing get() = rule.descriptionOfAMatchingThing
    override fun match(context: Any, input: TokenSequence) = rule.match(context, input)
    override fun markAmbiguityResolved(inContext: Any) = rule.markAmbiguityResolved(inContext)
    override val minimalMatchingSequence get() = rule.minimalMatchingSequence
    override fun toString() = rule.toString()
}