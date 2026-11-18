package compiler.binding.context.effect

/**
 * Whether code may have jumped to the start or end of a loop with `break` or `continue`. [CallFrameExit] doesn't model
 * these jumps, so code that is guaranteed to return by [CallFrameExit] may still leave through a `break` or `continue`.
 */
object LoopJump : SingletonEphemeralStateClass<LoopJump.State, LoopJump.Effect>() {
    override val initialState = State(mayHaveJumped = false)

    override fun fold(state: State, effect: Effect): State = State(mayHaveJumped = true)

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return State(state.mayHaveJumped || advancedMaybe.mayHaveJumped)
    }

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
        return State(stateOne.mayHaveJumped || stateTwo.mayHaveJumped)
    }

    data class State(val mayHaveJumped: Boolean)

    /** a `break` or `continue` */
    data object Effect : SingletonEffect(LoopJump)
}
