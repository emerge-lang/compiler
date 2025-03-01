package compiler.reportings

import compiler.InternalCompilerError

/**
 * Collects [Reporting]s. This is an ongoing refactoring: lots of code returns a `Collection<Reporting>` which
 * overall leads to lots and lots of copying and allocations. By inversing this and having [Reporting]s be
 * passed to a [Diagnosis], this can be made much more efficient.
 */
interface Diagnosis {
    val nErrors: ULong

    fun add(finding: Reporting)
    fun hasSameDrainAs(other: Diagnosis): Boolean

    fun mapping(mapper: (Reporting) -> Reporting): Diagnosis = MappingDiagnosisImpl(this, mapper)

    companion object {
        fun failOnError(): Diagnosis = object : Diagnosis {
            override val nErrors = 0uL

            override fun add(finding: Reporting) {
                if (finding.level >= Reporting.Level.ERROR) {
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
    private val storage = ArrayList<Reporting>()

    override val nErrors: ULong
        get() = storage.count { it.level >= Reporting.Level.ERROR }.toULong()

    override fun add(finding: Reporting) {
        storage.add(finding)
    }

    fun replayOnto(diagnosis: Diagnosis) {
        storage.forEach(diagnosis::add)
    }

    val findings: Iterable<Reporting> = storage

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return other === this || other.hasSameDrainAs(this)
    }
}

private class MappingDiagnosisImpl(private val delegate: Diagnosis, private val mapper: (Reporting) -> Reporting) : Diagnosis by delegate {
    override fun add(finding: Reporting) {
        delegate.add(mapper(finding))
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return when (other) {
            is MappingDiagnosisImpl -> delegate.hasSameDrainAs(other.delegate)
            else -> other.hasSameDrainAs(delegate) || other.hasSameDrainAs(this)
        }
    }
}