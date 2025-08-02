package compiler.binding.context.effect

import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundMixinStatement
import compiler.binding.context.effect.PartialObjectInitialization.State

/**
 * The analysis happens during [SemanticallyAnalyzable.semanticAnalysisPhase2]; **the [State] is not meaningful
 * before [SemanticallyAnalyzable.semanticAnalysisPhase3]!**
 */
object PartialObjectInitialization : EphemeralStateClass<BoundVariable, State, PartialObjectInitialization.Effect> {
    override fun getInitialState(subject: BoundVariable) = State.INITIAL
    override fun fold(state: State, effect: Effect) = state.fold(effect)
    override fun combineMaybe(state: State, advancedMaybe: State) = state.combineMaybe(advancedMaybe)
    override fun combineExclusiveBranches(stateOne: State, stateTwo: State) = stateOne.intersect(stateTwo)

    class State(
        private val knownMemberStates: Map<String, VariableInitialization.State>,
        private val initializedMixins: Set<BoundMixinStatement>,
        private val assumeMixinsUninitialized: Boolean,
    ) {
        fun fold(effect: Effect): State = when (effect) {
            is Effect.MarkObjectAsEntirelyUninitializedEffect -> {
                check(knownMemberStates.isEmpty()) {
                    "Marking object as completely uninitialized after state of some member has already been tracked - somethings off!"
                }
                State(
                    effect.classDef.memberVariables.associate { it.name to VariableInitialization.State.NOT_INITIALIZED },
                    initializedMixins,
                    true,
                )
            }
            is Effect.WriteToMemberVariableEffect -> State(
                knownMemberStates + mapOf(
                    effect.member.name to VariableInitialization.State.INITIALIZED
                ),
                initializedMixins,
                assumeMixinsUninitialized,
            )
            is Effect.MixinInitialized -> State(
                knownMemberStates,
                initializedMixins + effect.mixin,
                assumeMixinsUninitialized,
            )
        }

        private fun combineEach(
            other: State,
            fieldStateCombinator: (VariableInitialization.State, VariableInitialization.State) -> VariableInitialization.State,
            mixinStateCombinator: (Set<BoundMixinStatement>, Set<BoundMixinStatement>) -> Set<BoundMixinStatement>,
        ): State {
            val newFieldData = HashMap<String, VariableInitialization.State>(knownMemberStates)
            other.knownMemberStates.forEach { (memberName, otherMemberState) ->
                newFieldData.compute(memberName) { _, selfState ->
                    fieldStateCombinator(selfState ?: VariableInitialization.State.INITIALIZED, otherMemberState)
                }
            }
            val newMixinData = mixinStateCombinator(this.initializedMixins, other.initializedMixins)
            return State(newFieldData, newMixinData, this.assumeMixinsUninitialized || other.assumeMixinsUninitialized)
        }

        fun combineMaybe(advancedMaybe: State) = combineEach(advancedMaybe, VariableInitialization::combineMaybe, { before, _ -> before })
        fun intersect(other: State) = combineEach(other, VariableInitialization::combineExclusiveBranches, Set<BoundMixinStatement>::intersect)

        fun getMemberInitializationState(member: BoundBaseTypeMemberVariable): VariableInitialization.State {
            return knownMemberStates[member.name] ?: VariableInitialization.State.INITIALIZED
        }

        fun getUninitializedMembers(classDef: BoundBaseType): Collection<BoundBaseTypeMemberVariable> {
            if (knownMemberStates.isEmpty()) {
                return emptySet()
            }

            return classDef.memberVariables.filter { getMemberInitializationState(it) != VariableInitialization.State.INITIALIZED }
        }

        fun getUninitializedMixins(classDef: BoundBaseType): Set<BoundMixinStatement> {
            val allMixins = classDef.constructor?.mixins ?: return emptySet()

            if (!assumeMixinsUninitialized && initializedMixins.isEmpty()) {
                // this happens when [MarkObjectAsEntirelyUninitializedEffect] wasn't called, which is the case
                // for ALL objects instead of the `self` in constructors. Those can safely be assumed to be completely
                // initialized, hence there are NO uninitialized mixins
                return emptySet()
            }

            return allMixins.toMutableSet().apply {
                removeAll(initializedMixins)
            }
        }

        companion object {
            val INITIAL = State(emptyMap(), emptySet(), false)
        }
    }

    sealed interface Effect : SideEffect<BoundVariable> {
        override val stateClass get() = PartialObjectInitialization

        class MarkObjectAsEntirelyUninitializedEffect(
            override val subject: BoundVariable,
            val classDef: BoundBaseType,
        ) : Effect {
            override fun equals(other: Any?): Boolean {
                if (other === this) return true
                if (other !is MarkObjectAsEntirelyUninitializedEffect) return false

                if (other.subject !== other.subject) return false
                return true
            }

            override fun hashCode(): Int {
                var result = javaClass.hashCode()
                result = 31 * result + System.identityHashCode(subject)
                return result
            }
        }

        class WriteToMemberVariableEffect(
            override val subject: BoundVariable,
            val member: BoundBaseTypeMemberVariable,
        ) : Effect {
            override fun equals(other: Any?): Boolean {
                if (other === this) return true
                if (other !is WriteToMemberVariableEffect) return false

                if (other.subject !== this.subject) return false
                if (other.member !== this.member) return false

                return true
            }

            override fun hashCode(): Int {
                var result = javaClass.hashCode()
                result = 31 * result + System.identityHashCode(subject)
                result = 31 * result + System.identityHashCode(member)
                return result
            }
        }

        class MixinInitialized(
            override val subject: BoundVariable,
            val mixin: BoundMixinStatement,
        ) : Effect {
            override fun equals(other: Any?): Boolean {
                if (other === this) return true
                if (other !is MixinInitialized) return false

                if (other.subject !== this.subject) return false
                if (other.mixin !== this.mixin) return false

                return true
            }

            override fun hashCode(): Int {
                var result = javaClass.hashCode()
                result = 31 * result + System.identityHashCode(subject)
                result = 31 * result + System.identityHashCode(mixin)
                return result
            }
        }
    }
}