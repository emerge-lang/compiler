package compiler.binding

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.parser.Reporting

interface BoundExecutable<out ASTType> {
    val context: CTContext

    val declaration: ASTType

    /**
     * Communicates changes the [Executable] applies any changes to its enclosing scope (e.g. a variable declaration declares a new
     * variable)
     * @return A [CTContext] derived from the given one, with all the necessary changes applied.
     */
    fun modified(context: CTContext): CTContext = context

    /**
     * This method is in place to verify explicit mentions of types in expressions. At the current stage,
     * this affects no expression. In the future, there will be expressions that can (or event must) contain
     * such explicit mentions:
     * * casts
     * * explicit generics
     */
    fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()

    /**
     * This method does currently not affect any expression. In the future, these expressions will make
     * good use of this method:
     * * constructor invocations
     * * method references (both static ones and such with a context)
     */
    fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()

    /**
     *
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()
}