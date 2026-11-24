package compiler.binding.context.effect

import compiler.binding.context.effect.CallFrameExit.Occurrence

/**
 * Whether code jumps to the start or end of a loop with `break` or `continue`. [CallFrameExit] doesn't model these
 * jumps. The jumps in a loop don't concern the code after it, see [exitLoop].
 */
object LoopJump : SingletonEphemeralStateClass<LoopJump.State, LoopJump.Effect>() {
    override val initialState = State(Occurrence.NEVER)

    override fun fold(state: State, effect: Effect): State = State(Occurrence.GUARANTEED)

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return State(state.jumps.combineSequentialExecution(advancedMaybe.jumps.maybe()))
    }

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
        return State(stateOne.jumps.combineExclusiveBranch(stateTwo.jumps))
    }

    override fun exitLoop(beforeLoop: State, atExit: State): State = beforeLoop

    data class State(val jumps: Occurrence) {
        val isGuaranteedToJump: Boolean get() = jumps == Occurrence.GUARANTEED
    }

    /** a `break` or `continue` */
    data object Effect : SingletonEffect(LoopJump)
}
