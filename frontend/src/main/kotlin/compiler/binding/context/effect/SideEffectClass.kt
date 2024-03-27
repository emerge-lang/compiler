package compiler.binding.context.effect

import compiler.binding.context.ExecutionScopedCTContext

/**
 * A single type of side effect that can be tracked across [ExecutionScopedCTContext]s, e.g. initialization of a variable
 * @param Subject the subject represents state external to the code that is affected by this side effect. E.g. a variable
 * @param State this type holds the information about the ephemeral state in one particular [ExecutionScopedCTContext]
 * (as in: at one particular point in time). E.g. whether a variable is initialized at a certain point in the code.
 * @param Effect the type of all effects that belong to this clas
 */
interface SideEffectClass<Subject : Any, State, Effect : SideEffect<Subject>> {
    /**
     * The state of this effect when no influencing actions have been tracked. E.g. a variable starts out
     * uninitialized until an action is recorded that initializes it.
     */
    fun getInitialState(subject: Subject): State

    /**
     * Given a previous state [state] and an effect [effect] that happens in that state, returns
     * the state of the subject after the effect has been applied
     */
    fun fold(state: State, effect: Effect): State

    /**
     * Given a previous state [state] and a new state [advancedMaybe] that _may_ have manifested through
     * [fold], returns a new state that encodes that information if necessary. In doubt, this function should
     * just return [state]
     */
    fun combineMaybe(state: State, advancedMaybe: State): State

    /**
     * Given two states of this effect, returns a new state that contains only information that be safely deducted
     * from both states. It may also contain the information that some effects _may_ have occured, but aren't guaranteed
     * to (a superposition, basically).
     */
    fun intersect(stateOne: State, stateTwo: State): State
}