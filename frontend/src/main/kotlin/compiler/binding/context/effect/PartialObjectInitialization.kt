package compiler.binding.context.effect

import compiler.binding.BoundVariable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable

object PartialObjectInitialization : EphemeralStateClass<BoundVariable, PartialObjectInitialization.State, PartialObjectInitialization.Effect> {
    override fun getInitialState(subject: BoundVariable) = State.INITIAL
    override fun fold(state: State, effect: Effect) = state.fold(effect)
    override fun combineMaybe(state: State, advancedMaybe: State) = state.combineMaybe(advancedMaybe)
    override fun intersect(stateOne: State, stateTwo: State) = stateOne.intersect(stateTwo)

    class State(
        private val knownMemberStates: Map<String, VariableInitialization.State>
    ) {
        fun fold(effect: Effect): State = when (effect) {
            is Effect.MarkObjectAsEntirelyUninitializedEffect -> {
                check(knownMemberStates.isEmpty()) {
                    "Marking object as completely uninitialized after state of some member has already been tracked - somethings off!"
                }
                State(effect.classDef.memberVariables.associate { it.name to VariableInitialization.State.NOT_INITIALIZED })
            }
            is Effect.WriteToMemberVariableEffect -> State(knownMemberStates + mapOf(
                effect.member.name to VariableInitialization.State.INITIALIZED
            ))
        }

        private fun combineEach(other: State, combinator: (VariableInitialization.State, VariableInitialization.State) -> VariableInitialization.State): State {
            val newData = HashMap<String, VariableInitialization.State>(knownMemberStates)
            other.knownMemberStates.forEach { (memberName, otherMemberState) ->
                newData.compute(memberName) { _, selfState ->
                    combinator(selfState ?: VariableInitialization.State.INITIALIZED, otherMemberState)
                }
            }
            return State(newData)
        }

        fun combineMaybe(advancedMaybe: State) = combineEach(advancedMaybe, VariableInitialization::combineMaybe)
        fun intersect(other: State) = combineEach(other, VariableInitialization::intersect)

        fun getMemberInitializationState(member: BoundBaseTypeMemberVariable): VariableInitialization.State {
            return knownMemberStates[member.name] ?: VariableInitialization.State.INITIALIZED
        }

        fun getUninitializedMembers(classDef: BoundBaseType): Collection<BoundBaseTypeMemberVariable> {
            if (knownMemberStates.isEmpty()) {
                return emptySet()
            }

            return classDef.memberVariables.filter { getMemberInitializationState(it) != VariableInitialization.State.INITIALIZED }
        }

        companion object {
            val INITIAL = State(emptyMap())
        }
    }

    sealed interface Effect : SideEffect<BoundVariable> {
        override val stateClass get() = PartialObjectInitialization

        class MarkObjectAsEntirelyUninitializedEffect(
            override val subject: BoundVariable,
            val classDef: BoundBaseType,
        ) : Effect

        class WriteToMemberVariableEffect(
            override val subject: BoundVariable,
            val member: BoundBaseTypeMemberVariable,
        ) : Effect
    }
}