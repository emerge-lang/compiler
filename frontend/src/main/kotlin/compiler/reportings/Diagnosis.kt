package compiler.reportings

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

    fun mapping(mapper: (Diagnostic) -> Diagnostic): Diagnosis = MappingDiagnosisImpl(this, mapper)

    companion object {
        fun failOnError(): Diagnosis = object : Diagnosis {
            override val nErrors = 0uL

            override fun add(finding: Diagnostic) {
                if (finding.level >= Diagnostic.Level.ERROR) {
                    throw InternalCompilerError("Generated code produced an error finding:\n$finding")
                }
            }

            override fun hasSameDrainAs(other: Diagnosis): Boolean {
                return other === this
            }
        }
    }
}

class CollectingDiagnosis : Diagnosis {
    private val storage = ArrayList<Diagnostic>()

    override val nErrors: ULong
        get() = storage.count { it.level >= Diagnostic.Level.ERROR }.toULong()

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

private class MappingDiagnosisImpl(private val delegate: Diagnosis, private val mapper: (Diagnostic) -> Diagnostic) : Diagnosis by delegate {
    override fun add(finding: Diagnostic) {
        delegate.add(mapper(finding))
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return when (other) {
            is MappingDiagnosisImpl -> delegate.hasSameDrainAs(other.delegate)
            else -> other.hasSameDrainAs(delegate) || other.hasSameDrainAs(this)
        }
    }
}