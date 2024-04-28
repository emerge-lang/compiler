package compiler.binding

import compiler.binding.misc_ir.IrOverloadGroupImpl
import compiler.binding.type.nonDisjointPairs
import compiler.pivot
import compiler.reportings.InconsistentReceiverPresenceInOverloadSetReporting
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

    private val seanHelper = SeanHelper()

    /** set during [semanticAnalysisPhase1] */
    var declaresReceiver: Boolean by Delegates.notNull()
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        return seanHelper.phase1 {
            val reportings = mutableListOf<Reporting>()

            val (withReceiver, withoutReceiver) = overloads.partition { it.declaresReceiver }
            if (withReceiver.isNotEmpty() && withoutReceiver.isNotEmpty()) {
                reportings.add(InconsistentReceiverPresenceInOverloadSetReporting(this))
            }
            this.declaresReceiver = withReceiver.size >= withoutReceiver.size

            return@phase1 reportings
        }
    }

    /**
     * `true` iff [semanticAnalysisPhase1] nor [semanticAnalysisPhase2] produced any errors.
     */
    val isValidAfterSemanticPhase2: Boolean
        get() {
            return !seanHelper.phase1HadErrors && !seanHelper.phase2HadErrors
        }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        return seanHelper.phase2 {
            if (overloads.size == 1) {
                // not actually overloaded
                return@phase2 emptySet()
            }

            return@phase2 if (areOverloadsDisjoint(overloads)) {
                emptySet()
            } else {
                setOf(Reporting.overloadSetHasNoDisjointParameter(this))
            }
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)
        return seanHelper.phase3 {
            emptySet()
        }
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

        /**
         * see the ([Sequence]) overload
         */
        internal fun areOverloadsDisjoint(overloads: Collection<BoundFunction>) = areOverloadsDisjoint(overloads.asSequence())

        /**
         * internal because it assumes some things that are checked in [BoundOverloadSet], but not here:
         * * [overloads] is not empty
         * * all functions in [overloads] have the same number of parameters
         * * all parameter types of the functions in [overloads] are resolved
         */
        internal fun areOverloadsDisjoint(overloads: Sequence<BoundFunction>): Boolean {
            return overloads
                .map { it.parameters.parameters.asSequence() }
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
        }
    }
}