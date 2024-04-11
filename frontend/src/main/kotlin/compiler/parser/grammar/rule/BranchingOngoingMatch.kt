package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.reportings.ParsingMismatchReporting
import java.util.IdentityHashMap
import java.util.LinkedList

class BranchingOngoingMatch<Item : Any>(
    branches: Collection<Rule<Item>>,
    private val afterBranch: MatchingContinuation<Item>,
    val name: String? = null,
) : OngoingMatch {
    init {
        require(branches.isNotEmpty())
    }

    override fun toString() = name ?: super.toString()

    private val lifeBranches = branches
        .map { option ->
            val continuation = BranchContinuation()
            val branch = option.startMatching(continuation)
            continuation.branch = branch
            branch
        }
        .let(::LinkedList)

    private val resultsByBranch = IdentityHashMap<OngoingMatch, MutableList<MatchingResult<Item>>>()
    private var anyBranchCompletedSuccessfully: Boolean = false
    private lateinit var continued: OngoingMatch

    override fun step(token: Token): Boolean {
        if (this::continued.isInitialized) {
            return continued.step(token)
        }

        var anyConsumed = false
        val lifeBranchIterator = lifeBranches.iterator()
        val removedBranches = ArrayList<OngoingMatch>(2)
        while (lifeBranchIterator.hasNext()) {
            val branch = lifeBranchIterator.next()
            val branchConsumed = branch.step(token)
            if (!branchConsumed) {
                lifeBranchIterator.remove()
                removedBranches.add(branch)
                val resultsFromBranch = resultsByBranch[branch]
                if (resultsFromBranch != null && resultsFromBranch.any { !it.hasErrors }) {
                    anyBranchCompletedSuccessfully = true
                }
            }
            anyConsumed = anyConsumed || branchConsumed
        }

        if (anyConsumed) {
            removedBranches.forEach(resultsByBranch::remove)
            if (lifeBranches.size == 1) {
                continued = lifeBranches.single()
                lifeBranches.clear()
                resultsByBranch.clear()
            }
            return true
        }

        check(removedBranches.isNotEmpty()) {
            "If the last branch died earlier, this code path should already have been taken. And it can only be taken once (continued variable)"
        }

        val relevantResults = resultsByBranch.values.flatten()
        continued = if (!anyBranchCompletedSuccessfully && relevantResults.all { it.hasErrors }) {
            afterBranch.resume(MatchingResult(null, aggregateErrors(relevantResults)))
        } else {
            OngoingMatch.Completed
        }

        return continued.step(token)
    }

    // TODO: make into a single instance per branch instance?
    private inner class BranchContinuation : MatchingContinuation<Item> {
        lateinit var branch: OngoingMatch
        override fun resume(result: MatchingResult<Item>): OngoingMatch {
            resultsByBranch.computeIfAbsent(branch, { ArrayList(2) }).add(result)
            return afterBranch.resume(result)
        }
    }
}

private inline fun <T, reified M> Collection<T>.mapIndexedToArray(mapper: (Int, T) -> M): Array<M> {
    val array = Array<M?>(size) { null }
    forEachIndexed { index, t ->
        array[index] = mapper(index, t)
    }
    @Suppress("UNCHECKED_CAST")
    return array as Array<M>
}

private val parseErrorComparator: Comparator<ParsingMismatchReporting> =
    compareBy<ParsingMismatchReporting> { it.level }
    .thenBy { it.sourceLocation.fromLineNumber }
    .thenBy { it.sourceLocation.fromColumnNumber }

internal fun reduceCombineParseError(a: ParsingMismatchReporting, b: ParsingMismatchReporting): ParsingMismatchReporting {
    val comparison = parseErrorComparator.compare(a, b)
    when {
        comparison > 0 -> return a
        comparison < 0 -> return b
    }

    // same location and severity
    return ParsingMismatchReporting((a.expectedAlternatives + b.expectedAlternatives).toSet(), a.actual)
}

private fun aggregateErrors(results: Collection<MatchingResult<*>>) = setOf(
    results.asSequence()
        .flatMap { it.reportings }
        .reduce(::reduceCombineParseError)
)