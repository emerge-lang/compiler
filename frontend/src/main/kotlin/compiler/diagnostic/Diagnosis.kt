package compiler.diagnostic

import compiler.InternalCompilerError

/**
 * Collects [Diagnostic]s. This is an ongoing refactoring: lots of code returns a `Collection<Reporting>` which
 * overall leads to lots and lots of copying and allocations. By inversing this and having [Diagnostic]s be
 * passed to a [Diagnosis], this can be made much more efficient.
 */
interface Diagnosis {
    val nErrors: ULong

    fun add(finding: Diagnostic)
    fun hasSameDrainAs(other: Diagnosis): Boolean

    companion object {
        fun failOnError(): Diagnosis = object : Diagnosis {
            override val nErrors = 0uL

            override fun add(finding: Diagnostic) {
                if (finding.severity >= Diagnostic.Severity.ERROR) {
                    throw InternalCompilerError("Generated code produced an error finding:\n$finding")
                }
            }

            override fun hasSameDrainAs(other: Diagnosis): Boolean {
                return other === this
            }
        }

        /**
         * Runs [action]. All [Diagnostic]s it adds are collected and ran through [transformer]
         * before they are passed on `this`.
         * @param action the action to run; this is intended to be an object+method reference, e.g. `leftHandSide::semanticAnalysisPhase1`
         * @param transformer transforms a sequence of diagnostics originating from [action] to one that is added to
         *        the original [Diagnosis]. Is invoked exactly once, after [action] has fully completed.
         */
        fun Diagnosis.doWithTransformedFindings(
            action: (Diagnosis) -> Unit,
            transformer: (Sequence<Diagnostic>) -> Sequence<Diagnostic>
        ) {
            val transformingDiagnosis = TransformingDiagnosis(this, transformer)
            try {
                action(transformingDiagnosis)
            }
            catch (e: Throwable) {
                transformingDiagnosis.closeAndDiscard()
                throw e
            }

            transformingDiagnosis.closeAndObtain().forEach(this::add)
        }
    }
}

class CollectingDiagnosis : Diagnosis {
    private val storage = ArrayList<Diagnostic>()

    override val nErrors: ULong
        get() = storage.count { it.severity >= Diagnostic.Severity.ERROR }.toULong()

    override fun add(finding: Diagnostic) {
        storage.add(finding)
    }

    fun replayOnto(diagnosis: Diagnosis) {
        storage.forEach(diagnosis::add)
    }

    val findings: Iterable<Diagnostic> = storage

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return other === this || other.hasSameDrainAs(this)
    }
}

private class TransformingDiagnosis(
    private val delegate: Diagnosis,
    private val transformer: (Sequence<Diagnostic>) -> Sequence<Diagnostic>,
) : Diagnosis by delegate {
    private var collected: MutableList<Diagnostic>? = ArrayList<Diagnostic>(0)
    override fun add(finding: Diagnostic) {
        val localCollected = collected ?: throw InternalCompilerError("This transforming diagnosis is already closed.")
        localCollected.add(finding)
    }

    override val nErrors get() = delegate.nErrors + (collected ?: emptyList()).count { it.severity >= Diagnostic.Severity.ERROR }.toULong()

    fun closeAndDiscard() {
        collected = null
    }

    fun closeAndObtain(): Sequence<Diagnostic> {
        val localCollected = collected ?: throw InternalCompilerError("This transforming diagnosis is already closed")
        collected = null
        return transformer(localCollected.asSequence())
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return when (other) {
            is TransformingDiagnosis -> delegate.hasSameDrainAs(other.delegate)
            else -> other.hasSameDrainAs(delegate) || other.hasSameDrainAs(this)
        }
    }
}