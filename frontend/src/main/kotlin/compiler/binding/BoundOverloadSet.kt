package compiler.binding

import compiler.binding.misc_ir.IrOverloadGroupImpl
import compiler.binding.type.nonDisjointPairs
import compiler.reportings.Diagnosis
import compiler.reportings.InconsistentReceiverPresenceInOverloadSetReporting
import compiler.reportings.Reporting
import compiler.util.pivot
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.common.CanonicalElementName
import kotlin.properties.Delegates

class BoundOverloadSet<out Fn : BoundFunction>(
    val canonicalName: CanonicalElementName.Function,
    val parameterCount: Int,
    val overloads: Collection<Fn>,
) : SemanticallyAnalyzable {
    init {
        require(overloads.isNotEmpty())
    }

    private val seanHelper = SeanHelper()

    /** set during [semanticAnalysisPhase1] */
    var declaresReceiver: Boolean by Delegates.notNull()
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        return seanHelper.phase1(diagnosis) {

            val (withReceiver, withoutReceiver) = overloads.partition { it.declaresReceiver }
            if (withReceiver.isNotEmpty() && withoutReceiver.isNotEmpty()) {
                diagnosis.add(InconsistentReceiverPresenceInOverloadSetReporting(this))
            }
            this.declaresReceiver = withReceiver.size >= withoutReceiver.size
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)

        return seanHelper.phase2(diagnosis) {
            if (overloads.size == 1) {
                // not actually overloaded
                return@phase2
            }

            if (!areOverloadsDisjoint(overloads)) {
                diagnosis.add(Reporting.overloadSetHasNoDisjointParameter(this))
            }
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        // the individual overload implementations are validated through the regular/obvious tree structure (SourceFile)
        return seanHelper.phase3(diagnosis) {

        }
    }

    fun toBackendIr(): IrOverloadGroup<IrFunction> {
        overloads
            .firstOrNull { it.canonicalName != canonicalName }
            ?.let { sameCanonicalNameViolator ->
                error("""
                    This overload has a different canonical name than the overload set:
                    
                    ${sameCanonicalNameViolator.declaredAt}
                    
                    overload set has name $canonicalName
                """.trimIndent())
            }
        assert(overloads.all { it.parameters.parameters.size == parameterCount })

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