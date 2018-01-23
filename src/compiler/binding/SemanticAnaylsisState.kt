package compiler.binding

import compiler.reportings.Reporting

/**
 * Assists elements with semantic analysis methods in managing the state of the analysis:
 * * assure that each phase is executed only once
 * * if a phase is called recursively, return an appropriate reporting
 */
class SemanticAnaylsisState {
    val phase1 = SemanticAnalysisPhaseState()
    val phase2 = SemanticAnalysisPhaseState()
    val phase3 = SemanticAnalysisPhaseState()
}

class SemanticAnalysisPhaseState {
    private var executing: Boolean = false
    private var result: Collection<Reporting>? = null

    /**
     * If the phase has already been executed, returns the cached results. If the phase is already executing,
     * returns an error that states the recursion error; otherwise, runs the given closure, stores the result and returns
     * the results.
     */
    fun synchronize(code: () -> Collection<Reporting>): Collection<Reporting> {
        if (executing) {
            return setOf(Reporting.semanticRecursion("Semantic recursion... i dont know how to get good error info in here yet..."))
        }

        if (result != null) {
            return result!!
        }

        this.executing = true

        try {
            val result = code()
            this.result = result
            return result
        }
        finally {
            this.executing = false
        }
    }
}