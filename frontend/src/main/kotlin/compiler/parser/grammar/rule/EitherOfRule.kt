package compiler.parser.grammar.rule

class EitherOfRule(
    val options: List<Rule<Any>>,
    override val explicitName: String?
) : Rule<Any> {
    init {
        require(options.isNotEmpty())
    }

    override fun startMatching(continueWith: MatchingContinuation<Any>): OngoingMatch {
        return BranchingOngoingMatch(options, continueWith, explicitName)
    }

    override fun toString() = explicitName ?: super.toString()
}