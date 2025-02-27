package compiler.reportings

import compiler.InternalCompilerError

/**
 * Collects [Reporting]s. This is an ongoing refactoring: lots of code returns a `Collection<Reporting>` which
 * overall leads to lots and lots of copying and allocations. By inversing this and having [Reporting]s be
 * passed to a [Diagnosis], this can be made much more efficient.
 */
interface Diagnosis {
    val hasErrors: Boolean

    fun add(finding: Reporting)
    fun incorporate(diagnosis: Diagnosis)

    fun record(): OngoingRecording

    fun mapping(mapper: (Reporting) -> Reporting): Diagnosis = MappingDiagnosisImpl(this, mapper)

    interface OngoingRecording : AutoCloseable {
        fun complete(): Recorded
    }

    interface Recorded {
        val hasErrors: Boolean
        fun replayOnto(diagnosis: Diagnosis)
    }

    companion object {
        fun newDiagnosis(): Diagnosis = DiagnosisImpl()
        fun failOnError(): Diagnosis = object : Diagnosis by Diagnosis.newDiagnosis() {
            override val hasErrors = false

            override fun add(finding: Reporting) {
                if (finding.level >= Reporting.Level.ERROR) {
                    throw InternalCompilerError("Generated code produced an error finding:\n$finding")
                }
            }

            override fun incorporate(diagnosis: Diagnosis) {
                TODO("generic impl")
            }
        }
    }
}

private class DiagnosisImpl : Diagnosis {
    private val storage = ArrayList<Reporting>()

    override val hasErrors: Boolean
        get() = storage.any { it.level >= Reporting.Level.ERROR }

    override fun add(finding: Reporting) {
        storage.add(finding)
    }

    override fun incorporate(diagnosis: Diagnosis) {
        if (diagnosis === this) {
            return
        }

        if (diagnosis !is DiagnosisImpl) {
            TODO("abstract impl")
        }

        storage.addAll(diagnosis.storage)
    }

    override fun record(): Diagnosis.OngoingRecording {
        return object : Diagnosis.OngoingRecording {
            private val firstIndex = storage.size
            private var closed = false
            override fun complete(): Diagnosis.Recorded {
                check(!closed)
                close()
                val lastIndex = storage.lastIndex
                return object : Diagnosis.Recorded {
                    private val findings: Sequence<Reporting> = IntProgression.fromClosedRange(firstIndex, lastIndex, 1)
                        .asSequence()
                        .map(storage::get)

                    override val hasErrors: Boolean
                        get() = findings.any { it.level >= Reporting.Level.ERROR }

                    override fun replayOnto(diagnosis: Diagnosis) {
                        if (diagnosis === this@DiagnosisImpl) {
                            return
                        }

                        findings.forEach(diagnosis::add)
                    }
                }
            }

            override fun close() {
                closed = true
            }
        }
    }
}

private class MappingDiagnosisImpl(private val delegate: Diagnosis, private val mapper: (Reporting) -> Reporting) : Diagnosis by delegate {
    override fun add(finding: Reporting) {
        delegate.add(mapper(finding))
    }

    override fun incorporate(diagnosis: Diagnosis) {
        TODO("abstract impl")
    }
}