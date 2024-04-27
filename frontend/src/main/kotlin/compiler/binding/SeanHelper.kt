package compiler.binding

import compiler.InternalCompilerError
import compiler.reportings.Reporting

/**
 * Sean is short for SEmantic ANalysis
 */
class SeanHelper {
    private lateinit var phase1Results: Collection<Reporting>
    var phase1HadErrors = false
        get() {
            requirePhase1Done()
            return field
        }
        private set

    private lateinit var phase2Results: Collection<Reporting>
    var phase2HadErrors = false
        get() {
            requirePhase2Done()
            return field
        }
        private set

    private lateinit var phase3Results: Collection<Reporting>
    var phase3HadErrors = false
        get() {
            requirePhase3Done()
            return field
        }
        private set

    fun phase1(impl: () -> Collection<Reporting>): Collection<Reporting> {
        if (this::phase1Results.isInitialized) {
            return this.phase1Results
        }

        val results = impl()
        phase1Results = results
        phase1HadErrors = results.any { it.level >= Reporting.Level.ERROR }
        return results
    }

    fun phase2(impl: () -> Collection<Reporting>): Collection<Reporting> {
        requirePhase1Done()

        if (this::phase2Results.isInitialized) {
            return this.phase2Results
        }

        val results = impl()
        phase2Results = results
        phase2HadErrors = results.any { it.level >= Reporting.Level.ERROR }
        return results
    }

    /**
     * @param runIfErrorsPreviously if `false` and [phase1] or [phase2] returned errors, this function
     * will return an empty collection without invoking [impl]. [phase3] will also not be marked completed then.
     */
    fun phase3(runIfErrorsPreviously: Boolean = true, impl: () -> Collection<Reporting>): Collection<Reporting> {
        requirePhase2Done()

        if (this::phase3Results.isInitialized) {
            return this.phase3Results
        }

        if (!runIfErrorsPreviously && (phase1HadErrors || phase2HadErrors)) {
            return emptySet()
        }

        val results = impl()
        phase3Results = results
        phase3HadErrors = results.any { it.level >= Reporting.Level.ERROR }
        return results
    }

    fun requirePhase1Done(): Collection<Reporting> {
        if (!this::phase1Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 1 is required but hasn't been done yet.")
        }

        return this.phase1Results
    }

    fun requirePhase1NotDone() {
        if (this::phase1Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 1 must not have been done yet.")
        }
    }

    fun requirePhase2Done(): Collection<Reporting> {
        requirePhase1Done()

        if (!this::phase2Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 2 is required but hasn't been done yet.")
        }

        return this.phase2Results
    }

    fun requirePhase2NotDone() {
        if (this::phase2Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 2 must not have been done yet.")
        }
    }

    fun requirePhase3Done(): Collection<Reporting> {
        requirePhase2Done()

        if (!this::phase3Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 3 is required but hasn't been done yet.")
        }

        return this.phase3Results
    }

    fun requirePhase3NotDone() {
        if (this::phase3Results.isInitialized) {
            throw InternalCompilerError("Semantic analysis phase 3 must not have been done yet.")
        }
    }

    override fun toString(): String {
        val phase1State = if (this::phase1Results.isInitialized) {
            if (phase1HadErrors) {
                "\u274C"
            } else {
                "\u2705"
            }
        } else {
            "?"
        }
        val phase2State = if (this::phase2Results.isInitialized) {
            if (phase2HadErrors) {
                "\u274C"
            } else {
                "\u2705"
            }
        } else {
            "?"
        }
        val phase3State = if (this::phase3Results.isInitialized) {
            if (phase3HadErrors) {
                "\u274C"
            } else {
                "\u2705"
            }
        } else {
            "?"
        }

        return "SeanHelper[1$phase1State 2$phase2State 3$phase3State]"
    }
}
