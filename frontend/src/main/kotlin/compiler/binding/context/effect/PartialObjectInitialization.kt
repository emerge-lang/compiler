package compiler.binding.context.effect

import compiler.binding.BoundVariable
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.classdef.BoundClassMemberVariable

object PartialObjectInitialization : EphemeralStateClass<BoundVariable, PartialObjectInitialization.State, PartialObjectInitialization.Effect> {
    override fun getInitialState(subject: BoundVariable) = State.INITIAL
    override fun fold(state: State, effect: Effect) = state.fold(effect)
    override fun combineMaybe(state: State, advancedMaybe: State) = state.combineMaybe(advancedMaybe)
    override fun intersect(stateOne: State, stateTwo: State) = stateOne.intersect(stateTwo)

    class State(
        private val knownMemberStates: Map<String, VariableInitialization.State>
    ) {
        fun fold(effect: Effect): State = when (effect) {
            is Effect.MarkObjectAsEntireUninitializedEffect -> {
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

        fun getMemberInitializationState(member: BoundClassMemberVariable): VariableInitialization.State {
            return knownMemberStates[member.name] ?: VariableInitialization.State.INITIALIZED
        }

        fun getUninitializedMembers(classDef: BoundClassDefinition): Collection<BoundClassMemberVariable> {
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

        class MarkObjectAsEntireUninitializedEffect(
            override val subject: BoundVariable,
            val classDef: BoundClassDefinition,
        ) : Effect

        class WriteToMemberVariableEffect(
            override val subject: BoundVariable,
            val member: BoundClassMemberVariable,
        ) : Effect
    }
}