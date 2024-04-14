package compiler.binding

import compiler.binding.misc_ir.IrOverloadGroupImpl
import compiler.binding.type.nonDisjointPairs
import compiler.pivot
import compiler.reportings.InconsistentReceiverPresenceInOverloadSetReporting
import compiler.reportings.OverloadSetHasNoDisjointParameterReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import kotlin.properties.Delegates

class BoundOverloadSet<out Fn : BoundFunction>(
    val canonicalName: CanonicalElementName.Function,
    val parameterCount: Int,
    val overloads: Collection<Fn>,
) : SemanticallyAnalyzable {
    init {
        require(overloads.isNotEmpty())
        assert(overloads.all { it.canonicalName == canonicalName }) {
            val violator = overloads.first { it.canonicalName != canonicalName }
            """
                This overload has a different canonical name than the overload set:
               ${violator.declaredAt}
               
               overload set has name $canonicalName
            """.trimIndent()

        }
        assert(overloads.all { it.parameters.parameters.size == parameterCount })
    }

    /** set during [semanticAnalysisPhase1] */
    var declaresReceiver: Boolean by Delegates.notNull()
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        val reportings = mutableListOf<Reporting>()

        val (withReceiver, withoutReceiver) = overloads.partition { it.declaresReceiver }
        if (withReceiver.isNotEmpty() && withoutReceiver.isNotEmpty()) {
            reportings.add(InconsistentReceiverPresenceInOverloadSetReporting(this))
        }
        this.declaresReceiver = withReceiver.size >= withoutReceiver.size

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)
        return emptySet()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        // // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        if (overloads.size == 1) {
            // not actually overloaded
            return emptySet()
        }

        val hasAtLeastOneDisjointParameter = this.overloads
            .map { it.parameters.parameters.asSequence() }
            .asSequence()
            .pivot()
            .filter { parametersAtIndex ->
                assert(parametersAtIndex.all { it != null })
                @Suppress("UNCHECKED_CAST")
                parametersAtIndex as List<BoundParameter>
                val parameterIsDisjoint = parametersAtIndex
                    .nonDisjointPairs()
                    .none()
                return@filter parameterIsDisjoint
            }
            .any()

        if (hasAtLeastOneDisjointParameter) {
            return emptySet()
        }

        return setOf(OverloadSetHasNoDisjointParameterReporting(this))
    }

    fun toBackendIr(): IrOverloadGroup<IrFunction> {
        return IrOverloadGroupImpl(canonicalName, parameterCount, overloads)
    }

    companion object {
        fun <Fn : BoundFunction>fromSingle(fn: Fn): BoundOverloadSet<Fn> {
            return BoundOverloadSet(
                fn.canonicalName,
                fn.parameters.parameters.size,
                setOf(fn),
            )
        }
    }
}