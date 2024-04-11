package compiler.parser.grammar.rule

class LazyRule<T : Any>(private val compute: () -> Rule<T>) : Rule<T> {
    private val rule by lazy(compute)

    override val explicitName get() = rule.explicitName
    override fun startMatching(continueWith: MatchingContinuation<T>): OngoingMatch = rule.startMatching(continueWith)
    override fun toString() = rule.toString()
}