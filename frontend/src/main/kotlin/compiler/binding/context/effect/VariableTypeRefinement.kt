package compiler.binding.context.effect

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundVariable
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberVariableReadExpression
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo

/**
 * Tracks what is known about the type of the value of a variable, or of a member variable reached from it (see [Path]),
 * beyond its declared type, e.g. after `if v is Foo` (smart casts). The backends rely on these refinements (they surface
 * in the IR, see [io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression.evaluatesTo]), so they must be
 * sound: a refinement only lasts as long as the variable isn't assigned a new value; the member variables on a
 * [Path] cannot change their value at all. In loops, that includes assignments in a previous iteration, see
 * [compiler.binding.context.LoopExecutionScopedCTContext.trackSideEffectInBody].
 *
 * Use [refinedType] to get the effective type.
 */
object VariableTypeRefinement : EphemeralStateClass<BoundVariable, VariableTypeRefinement.State, VariableTypeRefinement.Effect> {
    override fun getInitialState(subject: BoundVariable): State = State.UNREFINED

    override val joinsOnlyBranchesThatCompleteNormally = true

    override fun fold(state: State, effect: Effect): State {
        return when (effect) {
            is Effect.Refine -> State(state.refinements + Refinement(effect.path, effect.intersectWith, Refinement.Origin.EstablishedIn(effect.establishedIn)))
            // the member variables on the paths are reached through the variable, so their refinements end, too
            is Effect.NewValueAssigned -> State.UNREFINED
        }
    }

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return join(state, advancedMaybe)
    }

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
        return join(stateOne, stateTwo)
    }

    /**
     * Keeps what holds in both states:
     * * the refinements both have in common. Refinements are only ever added to the end of the list, and the
     *   refinements from before the states diverged are the same objects in both, so these are a common prefix.
     * * for each [Path] that both refine after that prefix: that its value is of the closest common supertype of what
     *   each of the states knows about it there.
     */
    private fun join(a: State, b: State): State {
        if (a.refinements.isEmpty()) {
            return a
        }
        if (b.refinements.isEmpty()) {
            return b
        }

        val common = a.refinements.zip(b.refinements)
            .takeWhile { (fromA, fromB) -> fromA == fromB }
            .map { it.first }

        if (common.size == a.refinements.size) {
            return a
        }
        if (common.size == b.refinements.size) {
            return b
        }

        val onlyInA = a.refinements.subList(common.size, a.refinements.size)
        val onlyInB = b.refinements.subList(common.size, b.refinements.size)
        val joined = onlyInA
            .map { it.path }
            .distinct()
            .mapNotNull { path ->
                val fromA = onlyInA.filter { it.path == path }
                val fromB = onlyInB.filter { it.path == path }.takeUnless { it.isEmpty() } ?: return@mapNotNull null
                Refinement(
                    path,
                    fromA.intersectedType().closestCommonSupertypeWith(fromB.intersectedType()),
                    Refinement.Origin.Joined(setOf(fromA, fromB)),
                )
            }

        return State(common + joined)
    }

    private fun List<Refinement>.intersectedType(): BoundTypeReference = asSequence()
        .map { it.intersectWith }
        .reduce { carry, type -> carry.intersect(type) }

    /**
     * @return the type of [variable] in [context], considering all refinements that are valid there
     */
    fun refinedType(variable: BoundVariable, context: ExecutionScopedCTContext): BoundTypeReference? {
        val declaredType = variable.typeAtDeclarationTime ?: return null
        return refinedType(Path(variable, emptyList()), declaredType, context)
    }

    /**
     * @param unrefinedType the type of the value at [path] without any refinements
     * @return the type of the value at [path] in [context], considering all refinements that are valid there
     */
    fun refinedType(path: Path, unrefinedType: BoundTypeReference, context: ExecutionScopedCTContext): BoundTypeReference {
        val refinements = context.getEphemeralState(this, path.root).refinements
        if (refinements.isEmpty()) {
            return unrefinedType
        }

        return refinements
            .asSequence()
            .filter { it.path == path }
            .fold(unrefinedType) { carry, refinement -> carry.intersect(refinement.intersectWith) }
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

    /**
     * @return the [Path] that [expression] reads from, if refinements of it can be trusted; `null` otherwise
     */
    fun pathOf(expression: BoundExpression<*>): Path? = when (expression) {
        is BoundIdentifierExpression -> expression.refinablePath
        is BoundMemberVariableReadExpression -> expression.refinablePath
        else -> null
    }

    /**
     * Whether the value of [member], read from an object referred to with [holderType], cannot change while a
     * refinement holds: [member] cannot be re-assigned, or nobody can modify the object (it is `const`). Otherwise,
     * aliases, invoked functions and destructors (run when references are dropped) could assign it.
     */
    fun memberValueIsStable(member: BoundBaseTypeMemberVariable, holderType: BoundTypeReference?): Boolean {
        if (member.isDecorated) {
            return false
        }

        return !member.isReAssignable || holderType?.mutability == TypeMutability.IMMUTABLE
    }

    /**
     * @return for a nullable [expression] at a [Path]: that it evaluating to a non-null value implies that the value at
     * that path is not null
     */
    fun nonNullImplications(expression: BoundExpression<*>): List<BoundExpression.ResultImplication> {
        val path = pathOf(expression) ?: return emptyList()
        val type = expression.type ?: return emptyList()
        if (!type.isNullable) {
            return emptyList()
        }

        return listOf(BoundExpression.ResultImplication(
            BoundExpression.ImplyingResult.NON_NULL_VALUE,
            mapOf(path to type.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)),
        ))
    }

    /**
     * Tracks that, after [variable] was assigned a value of type [assignedType], it holds a value of that type; which
     * may be more specific than its declared type (e.g. not nullable, or a subtype).
     *
     * The refinement keeps the declared mutability of [variable]: the variable holds a reference to the value, so
     * e.g. an `exclusive` value is no longer exclusive when read from it. Assigning `null` or a value of type
     * `Nothing` doesn't refine: a variable of type `Nothing?` offers no members, which is less useful than its
     * declared type.
     */
    fun trackAssignedValue(variable: BoundVariable, assignedType: BoundTypeReference?, context: MutableExecutionScopedCTContext) {
        if (assignedType == null || !canBeRefined(variable)) {
            return
        }
        val declaredType = variable.typeAtDeclarationTime ?: return
        if (assignedType.baseTypeOfLowerBound == context.swCtx.nothing || !(assignedType isAssignableTo declaredType)) {
            return
        }

        context.trackSideEffect(Effect.Refine(
            Path(variable, emptyList()),
            assignedType.withMutability(declaredType.mutability),
            context,
        ))
    }

    /**
     * Tracks the refinements that [implications] imply on [onResult] in [context], where that result is known.
     */
    fun trackImplications(implications: List<BoundExpression.ResultImplication>, onResult: BoundExpression.ImplyingResult, context: MutableExecutionScopedCTContext) {
        implications
            .filter { it.onResult == onResult }
            .flatMap { it.typeRefinements.entries }
            .forEach { (path, intersectWith) -> context.trackSideEffect(Effect.Refine(path, intersectWith, context)) }
    }

    /**
     * A variable ([root]), or a member variable reached from it through [members]: `v.a.b` is `Path(v, [a, b])`. Only
     * created where the values of [members] are stable, see [memberValueIsStable].
     */
    class Path(val root: BoundVariable, val members: List<BoundBaseTypeMemberVariable>) {
        operator fun plus(member: BoundBaseTypeMemberVariable) = Path(root, members + member)

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Path) return false
            return root === other.root && members.size == other.members.size && members.indices.all { members[it] === other.members[it] }
        }

        override fun hashCode(): Int = members.fold(System.identityHashCode(root)) { carry, member -> carry * 31 + System.identityHashCode(member) }

        override fun toString() = (listOf(root.name) + members.map { it.name }).joinToString(separator = ".")
    }

    data class State(val refinements: List<Refinement>) {
        companion object {
            val UNREFINED = State(emptyList())
        }
    }

    /**
     * @param origin tells apart refinements of the same [path] to the same type: only the very same refinement holds in
     * two states that diverged after it was established.
     */
    class Refinement(
        val path: Path,
        val intersectWith: BoundTypeReference,
        val origin: Origin,
    ) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Refinement) return false
            return origin == other.origin && path == other.path && intersectWith == other.intersectWith
        }

        override fun hashCode(): Int {
            return (origin.hashCode() * 31 + path.hashCode()) * 31 + intersectWith.hashCode()
        }

        sealed interface Origin {
            /** established by a [Effect.Refine] in [context], where it starts to be valid */
            class EstablishedIn(val context: ExecutionScopedCTContext) : Origin {
                override fun equals(other: Any?) = other is EstablishedIn && other.context === context
                override fun hashCode() = System.identityHashCode(context)
            }

            /**
             * by joining states, each with the refinements in [fromStates]. The same join can be computed more than
             * once; the results are equal.
             */
            data class Joined(val fromStates: Set<List<Refinement>>) : Origin
        }
    }

    sealed class Effect(override val subject: BoundVariable) : SideEffect<BoundVariable> {
        override val stateClass get() = VariableTypeRefinement

        class Refine(
            val path: Path,
            val intersectWith: BoundTypeReference,
            val establishedIn: ExecutionScopedCTContext,
        ) : Effect(path.root)

        class NewValueAssigned(subject: BoundVariable) : Effect(subject)
    }
}
