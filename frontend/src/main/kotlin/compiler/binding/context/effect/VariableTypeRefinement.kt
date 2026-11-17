package compiler.binding.context.effect

import compiler.binding.BoundLoop
import compiler.binding.BoundVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.LoopExecutionScopedCTContext
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeReference

/**
 * Tracks what is known about the type of the value of a variable beyond its declared type, e.g. after
 * `if v is Foo` (smart casts). The backends rely on these refinements (they surface in the IR, see
 * [io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression.evaluatesTo]), so they must be sound:
 * a refinement only lasts as long as the variable isn't assigned a new value.
 *
 * Use [refinedType] to get the effective type.
 */
object VariableTypeRefinement : EphemeralStateClass<BoundVariable, VariableTypeRefinement.State, VariableTypeRefinement.Effect> {
    override fun getInitialState(subject: BoundVariable): State = State.UNREFINED

    override val joinsOnlyBranchesThatCompleteNormally = true

    override fun fold(state: State, effect: Effect): State {
        return when (effect) {
            is Effect.Refine -> State(state.refinements + Refinement(effect.intersectWith, effect.establishedIn))
            is Effect.NewValueAssigned -> State.UNREFINED
        }
    }

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return commonRefinements(state, advancedMaybe)
    }

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
        return commonRefinements(stateOne, stateTwo)
    }

    /**
     * Keeps only the refinements that hold in both states; refinements are only ever added to the end of the list,
     * so the result is a common prefix.
     */
    private fun commonRefinements(a: State, b: State): State {
        if (a.refinements.isEmpty()) {
            return a
        }
        if (b.refinements.isEmpty()) {
            return b
        }

        val common = a.refinements.zip(b.refinements)
            .takeWhile { (fromA, fromB) -> fromA == fromB }
            .map { it.first }

        return when (common.size) {
            a.refinements.size -> a
            b.refinements.size -> b
            else -> State(common)
        }
    }

    /**
     * @return the type of [variable] in [context], considering all refinements that are valid there
     */
    fun refinedType(variable: BoundVariable, context: ExecutionScopedCTContext): BoundTypeReference? {
        val declaredType = variable.typeAtDeclarationTime ?: return null
        val refinements = context.getEphemeralState(this, variable).refinements
        if (refinements.isEmpty()) {
            return declaredType
        }

        return refinements
            .asSequence()
            .filter { it.isValidIn(variable, context) }
            .fold(declaredType) { carry, refinement -> carry.intersect(refinement.intersectWith) }
    }

    /**
     * Whether a refinement of [variable] can be trusted: only if all changes to its value are visible as side effects
     * in the [ExecutionScopedCTContext]s. That is the case for variables local to a function. A re-assignable member
     * or global variable could be assigned from elsewhere, e.g. by a function invoked in between.
     */
    fun canBeRefined(variable: BoundVariable): Boolean = when (variable.kind) {
        BoundVariable.Kind.LOCAL_VARIABLE,
        BoundVariable.Kind.PARAMETER,
        BoundVariable.Kind.CONSTRUCTOR_PARAMETER -> true
        BoundVariable.Kind.MEMBER_VARIABLE,
        BoundVariable.Kind.DECORATED_MEMBER_VARIABLE,
        BoundVariable.Kind.GLOBAL_VARIABLE -> !variable.isReAssignable
    }

    data class State(val refinements: List<Refinement>) {
        companion object {
            val UNREFINED = State(emptyList())
        }
    }

    /**
     * @param establishedIn the context where the refinement starts to be valid
     */
    data class Refinement(
        val intersectWith: BoundTypeReference,
        val establishedIn: ExecutionScopedCTContext,
    ) {
        fun isValidIn(variable: BoundVariable, context: ExecutionScopedCTContext): Boolean {
            if (!variable.isReAssignable) {
                return true
            }

            // an assignment later in the body of a loop that started after the refinement was established
            // changes the value for the next iteration; the side effect of that assignment is not visible
            // from here, so the refinement cannot be trusted. establishedIn is not necessarily an ancestor of
            // context (the refinement may come from a branch, e.g. `if isNull(v) { return }`), so compare the loops
            return context.innermostLoop === establishedIn.innermostLoop
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Refinement) return false
            return establishedIn === other.establishedIn && intersectWith == other.intersectWith
        }

        override fun hashCode(): Int {
            return System.identityHashCode(establishedIn) * 31 + intersectWith.hashCode()
        }
    }

    private val ExecutionScopedCTContext.innermostLoop: BoundLoop<*>?
        get() = (this as? LoopExecutionScopedCTContext<*>)?.loopNode ?: parentLoop

    sealed class Effect(override val subject: BoundVariable) : SideEffect<BoundVariable> {
        override val stateClass get() = VariableTypeRefinement

        class Refine(
            subject: BoundVariable,
            val intersectWith: BoundTypeReference,
            val establishedIn: ExecutionScopedCTContext,
        ) : Effect(subject)

        class NewValueAssigned(subject: BoundVariable) : Effect(subject)
    }
}
