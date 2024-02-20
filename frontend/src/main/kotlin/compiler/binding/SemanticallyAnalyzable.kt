package compiler.binding

import compiler.reportings.Reporting

interface SemanticallyAnalyzable {
    /**
     * This method is in place to verify explicit mentions of types in expressions. At the current stage,
     * this affects no expression. In the future, there will be expressions that can (or event must) contain
     * such explicit mentions:
     * * casts
     * * explicit generics
     */
    fun semanticAnalysisPhase1(): Collection<Reporting>

    /**
     * This method does currently not affect any expression. In the future, these expressions will make
     * good use of this method:
     * * constructor invocations
     * * method references (both static ones and such with a context)
     */
    fun semanticAnalysisPhase2(): Collection<Reporting>

    /**
     * Here is where actual semantics are validated.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting>
}