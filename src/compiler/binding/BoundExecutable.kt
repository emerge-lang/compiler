package compiler.binding

import compiler.ast.Executable
import compiler.ast.expression.Expression
import compiler.binding.context.CTContext
import compiler.parser.Reporting

interface BoundExecutable<out ASTType> {
    /**
     * The context this expression has been bound to.
     */
    val context: CTContext

    /**
     * The [Expression] that was bound to [context].
     */
    val declaration: ASTType

    /**
     * Whether this expression is readonly. An expression is readonly if it never writes to its context, not even
     * parameters passed to it.
     * Is `null` if the property has not yet been determined. Must be non-null after semantic analysis is completed.
     */
    val isReadonly: Boolean?

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
     * Here is where actual semantics are validated.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    /**
     * Returns whether this executable reads state declared in any of the parents of the given context. Used to
     * determine purity of the expression.
     * @param boundary The bounding context.
     */
    fun readsBeyond(boundary: CTContext): Boolean = false // TODO remove default impl

    /**
     * Returns whether this executable writes state declared in any of the parents of the given context. Used to
     * determine purity and readonlyness of the expression.
     * @param boundary The bounding context.
     */
    fun writesBeyond(boundary: CTContext): Boolean = false // TODO remove default impl
}