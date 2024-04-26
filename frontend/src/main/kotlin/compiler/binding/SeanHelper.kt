package compiler.binding

import compiler.InternalCompilerError
import compiler.reportings.Reporting

/**
 * Sean is short for SEmantic ANalysis
 */
class SeanHelper {
    private lateinit var phase1Results: Collection<Reporting>
    private lateinit var phase2Results: Collection<Reporting>
    private lateinit var phase3Results: Collection<Reporting>

    fun phase1(impl: () -> Collection<Reporting>): Collection<Reporting> {
        if (this::phase1Results.isInitialized) {
            return this.phase1Results
        }

        val results = impl()
        phase1Results = results
        return results
    }

    fun phase2(impl: () -> Collection<Reporting>): Collection<Reporting> {
        requirePhase1Done()

        if (this::phase2Results.isInitialized) {
            return this.phase2Results
        }

        val results = impl()
        phase2Results = results
        return results
    }

    fun phase3(impl: () -> Collection<Reporting>): Collection<Reporting> {
        requirePhase2Done()

        if (this::phase3Results.isInitialized) {
            return this.phase2Results
        }

        val results = impl()
        phase3Results = results
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
}
