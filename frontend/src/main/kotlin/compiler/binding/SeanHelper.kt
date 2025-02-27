package compiler.binding

import compiler.InternalCompilerError
import compiler.reportings.Diagnosis

/**
 * Sean is short for SEmantic ANalysis
 */
class SeanHelper {
    private lateinit var phase1Results: Diagnosis.Recorded
    val phase1HadErrors: Boolean
        get() = requirePhase1Done().hasErrors

    private lateinit var phase2Results: Diagnosis.Recorded
    val phase2HadErrors: Boolean
        get() = requirePhase2Done().hasErrors

    private lateinit var phase3Results: Diagnosis.Recorded
    val phase3HadErrors: Boolean
        get() = requirePhase3Done().hasErrors

    fun phase1(diagnosis: Diagnosis, impl: (Diagnosis) -> Unit) {
        if (this::phase1Results.isInitialized) {
            this.phase1Results.replayOnto(diagnosis)
            return
        }

        diagnosis.record().use { diagnosisRecording ->
            impl(diagnosis)
            phase1Results = diagnosisRecording.complete()
        }
    }

    fun phase2(diagnosis: Diagnosis, impl: (Diagnosis) -> Unit) {
        requirePhase1Done()

        if (this::phase2Results.isInitialized) {
            this.phase2Results.replayOnto(diagnosis)
            return
        }

        diagnosis.record().use { diagnosisRecording ->
            impl(diagnosis)
            phase2Results = diagnosisRecording.complete()
        }
    }

    /**
     * @param runIfErrorsPreviously if `false` and [phase1] or [phase2] returned errors, this function
     * will return an empty collection without invoking [impl]. [phase3] will also not be marked completed then.
     */
    fun phase3(diagnosis: Diagnosis, runIfErrorsPreviously: Boolean = true, impl: (Diagnosis) -> Unit) {
        requirePhase2Done()

        if (this::phase3Results.isInitialized) {
            this.phase3Results.replayOnto(diagnosis)
            return
        }

        if (!runIfErrorsPreviously && (phase1HadErrors || phase2HadErrors)) {
            return
        }

        diagnosis.record().use { diagnosisRecording ->
            impl(diagnosis)
            phase3Results = diagnosisRecording.complete()
        }
    }

    fun requirePhase1Done(): Diagnosis.Recorded {
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

    fun requirePhase2Done(): Diagnosis.Recorded {
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

    fun requirePhase3Done(): Diagnosis.Recorded {
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
