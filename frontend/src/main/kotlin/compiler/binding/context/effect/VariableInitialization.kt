package compiler.binding.context.effect

import compiler.InternalCompilerError
import compiler.binding.BoundVariable

object VariableInitialization : EphemeralStateClass<BoundVariable, VariableInitialization.State, VariableInitialization.WriteToVariableEffect> {
    override fun getInitialState(subject: BoundVariable) = State.NOT_INITIALIZED

    override fun fold(state: State, effect: WriteToVariableEffect): State {
        return State.INITIALIZED
    }

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
        return when (stateOne) {
            State.NOT_INITIALIZED -> when (stateTwo) {
                State.NOT_INITIALIZED -> State.NOT_INITIALIZED
                State.MAYBE_INITIALIZED -> State.MAYBE_INITIALIZED
                State.INITIALIZED -> State.MAYBE_INITIALIZED
            }
            State.MAYBE_INITIALIZED -> State.MAYBE_INITIALIZED
            State.INITIALIZED -> when (stateTwo) {
                State.NOT_INITIALIZED -> State.MAYBE_INITIALIZED
                State.MAYBE_INITIALIZED -> State.MAYBE_INITIALIZED
                State.INITIALIZED -> State.INITIALIZED
            }
        }
    }

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return when(state) {
            State.NOT_INITIALIZED -> when (advancedMaybe) {
                State.NOT_INITIALIZED -> State.NOT_INITIALIZED
                State.MAYBE_INITIALIZED -> State.MAYBE_INITIALIZED
                State.INITIALIZED -> State.MAYBE_INITIALIZED
            }
            State.MAYBE_INITIALIZED -> State.MAYBE_INITIALIZED
            State.INITIALIZED -> when (advancedMaybe) {
                State.NOT_INITIALIZED -> throw InternalCompilerError("this should never happen, one cannot un-initialize a variable")
                else -> State.INITIALIZED
            }
        }
    }

    enum class State {
        NOT_INITIALIZED,
        MAYBE_INITIALIZED,
        INITIALIZED,
        ;
    }

    class WriteToVariableEffect(
        override val subject: BoundVariable,
    ) : SideEffect<BoundVariable> {
        override val stateClass = VariableInitialization
    }
}