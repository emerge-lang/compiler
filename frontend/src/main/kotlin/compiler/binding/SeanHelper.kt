package compiler.binding

import compiler.InternalCompilerError
import compiler.diagnostic.Diagnosis

/**
 * Sean is short for SEmantic ANalysis
 */
class SeanHelper {
    // TODO: avoid double-checking on a best-effort basis without allocating new objects per invocation of the phases
    private var phase1DoneOn: Diagnosis? = null
    var phase1HadErrors = false
        private set

    private var phase2DoneOn: Diagnosis? = null
    var phase2HadErrors = false
        private set

    private var phase3DoneOn: Diagnosis? = null
    var phase3HadErrors = false
        private set

    fun phase1(diagnosis: Diagnosis, impl: () -> Unit) {
        phase1DoneOn?.let { phase1Diag ->
            check(phase1Diag.hasSameDrainAs(diagnosis))
            return
        }

        val nErrorsBefore = diagnosis.nErrors
        impl()
        phase1DoneOn = diagnosis
        phase1HadErrors = diagnosis.nErrors > nErrorsBefore
    }

    fun phase2(diagnosis: Diagnosis, impl: (PhaseContext) -> Unit) {
        requirePhase1Done()

        phase2DoneOn?.let { phase2Diag ->
            check(phase2Diag.hasSameDrainAs(diagnosis))
            return
        }

        var phase2MarkedErroneousExplicitly = false
        val nErrorsBefore = diagnosis.nErrors
        impl(object : PhaseContext {
            override fun markErroneous() {
                phase2MarkedErroneousExplicitly = true
            }
        })
        phase2DoneOn = diagnosis
        phase2HadErrors = phase2MarkedErroneousExplicitly || diagnosis.nErrors > nErrorsBefore
    }

    /**
     * @param runIfErrorsPreviously if `false` and [phase1] or [phase2] returned errors, this function
     * will return an empty collection without invoking [impl]. [phase3] will also not be marked completed then.
     */
    fun phase3(diagnosis: Diagnosis, runIfErrorsPreviously: Boolean = true, impl: (Diagnosis) -> Unit) {
        requirePhase2Done()

        phase3DoneOn?.let { phase3Diag ->
            check(phase3Diag.hasSameDrainAs(diagnosis))
            return
        }

        if (!runIfErrorsPreviously && (phase1HadErrors || phase2HadErrors)) {
            return
        }

        val nErrorsBefore = diagnosis.nErrors
        impl(diagnosis)
        phase3DoneOn = diagnosis
        phase3HadErrors = diagnosis.nErrors > nErrorsBefore
    }

    private val phase1Done: Boolean get() = phase1DoneOn != null
    private val phase2Done: Boolean get() = phase2DoneOn != null
    private val phase3Done: Boolean get() = phase3DoneOn != null

    fun requirePhase1Done() {
        if (!phase1Done) {
            throw InternalCompilerError("Semantic analysis phase 1 is required but hasn't been done yet.")
        }
    }

    fun requirePhase1NotDone() {
        if (phase1Done) {
            throw InternalCompilerError("Semantic analysis phase 1 must not have been done yet.")
        }
    }

    fun requirePhase2Done() {
        requirePhase1Done()

        if (!phase2Done) {
            throw InternalCompilerError("Semantic analysis phase 2 is required but hasn't been done yet.")
        }
    }

    fun requirePhase2NotDone() {
        if (phase2Done) {
            throw InternalCompilerError("Semantic analysis phase 2 must not have been done yet.")
        }
    }

    fun requirePhase3Done() {
        requirePhase2Done()

        if (!phase3Done) {
            throw InternalCompilerError("Semantic analysis phase 3 is required but hasn't been done yet.")
        }
    }

    fun requirePhase3NotDone() {
        if (phase3Done) {
            throw InternalCompilerError("Semantic analysis phase 3 must not have been done yet.")
        }
    }

    override fun toString(): String {
        val phase1State = if (phase1Done) {
            if (phase1HadErrors) {
                "\u274C"
            } else {
                "\u2705"
            }
        } else {
            "?"
        }
        val phase2State = if (phase2Done) {
            if (phase2HadErrors) {
                "\u274C"
            } else {
                "\u2705"
            }
        } else {
            "?"
        }
        val phase3State = if (phase3Done) {
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

    interface PhaseContext {
        /**
         * can be invoked within [phase2] to interact with the `runIfErrorsPreviously` parameter of [phase3].
         */
        fun markErroneous()
    }
}
