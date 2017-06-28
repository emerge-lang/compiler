package compiler.binding.expression

import compiler.ast.expression.Expression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

interface BoundExpression<out ASTType> {
    /**
     * The context this expression has been bound to.
     */
    val context: CTContext

    /**
     * The [Expression] that was bound to [context].
     */
    val declaration: ASTType

    /**
     * The type of this expression when evaluated If the type could not be determined due to semantic errors,
     * this might be a close guess or null.
     */
    val type: BaseTypeReference?

    /**
     * Whether this expression is readonly. An expression is readonly if it never writes to its context, not even
     * parameters passed to it.
     * Is `null` if the property has not yet been determined. Must be non-null after semantic analysis is completed.
     */
    val isReadonly: Boolean?

    /**
     * This method is in place to verify explicit mentions of types in expressions. At the current stage,
     * this affects no expression. In the future, there will be expressions that can (or event must) contain
     * such explicit mentions:
     * * casts
     * * function invocation with explicit generics
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
}