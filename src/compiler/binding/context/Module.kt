package compiler.binding.context

import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.parser.Reporting

class Module(
    val name: Array<String>,
    val context: MutableCTContext,
    /** [Reporting]s generated at bind-time: double declarations, ... */
    val bindTimeReportings: Collection<Reporting> = emptySet()
) {
    /**
     * Delegates to semantic analysis phase 1 of all components that make up this module;
     * collects the results and returns them. Also returns the [Reporting]s found when binding
     * elements to the module (such as doubly declared variables).
     */
    fun semanticAnalysisPhase1(): Collection<Reporting> =
        bindTimeReportings +
        context.variables.flatMap(BoundVariable::semanticAnalysisPhase1) +
        context.functions.flatMap(BoundFunction::semanticAnalysisPhase1)

    /**
     * Delegates to semantic analysis phase 2 of all components that make up this module;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase2(): Collection<Reporting> =
        context.variables.flatMap(BoundVariable::semanticAnalysisPhase2) +
        context.functions.flatMap(BoundFunction::semanticAnalysisPhase2)

    /**
     * Delegates to semantic analysis phase 3 of all components that make up this module;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet() // TODO: implement
}