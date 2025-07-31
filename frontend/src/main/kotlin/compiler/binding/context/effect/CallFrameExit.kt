package compiler.binding.context.effect

import compiler.binding.BoundExecutable

/**
 * Models how code execution exits the current stack frame / function call.
 */
object CallFrameExit : SingletonEphemeralStateClass<CallFrameExit.Behavior, CallFrameExit.Effect>() {
    override val initialState = Behavior(
        Occurrence.NEVER,
        Occurrence.NEVER,
        Occurrence.NEVER,
        Occurrence.NEVER,
        Occurrence.NEVER,
        Occurrence.NEVER,
        Occurrence.NEVER,
    )

    override fun fold(state: Behavior, effect: Effect): Behavior {
        return Behavior(
            returns = when (effect) {
                Effect.Returns -> Occurrence.GUARANTEED
                Effect.Throws -> Occurrence.NEVER
                Effect.ThrowsPossibly ->  Occurrence.POSSIBLY
                is Effect.InvokesFunction -> state.returns
            },
            throws = when (effect) {
                Effect.Returns -> state.throws
                Effect.Throws -> Occurrence.GUARANTEED
                Effect.ThrowsPossibly -> Occurrence.POSSIBLY
                is Effect.InvokesFunction -> state.throws.combineSequentialExecution(effect.behavior.throws)
            },
            terminates = when (effect) {
                Effect.Returns,
                Effect.Throws,
                Effect.ThrowsPossibly -> Occurrence.POSSIBLY
                is Effect.InvokesFunction -> state.terminates.combineSequentialExecution(effect.behavior.terminates)
            },
        )
    }

    override fun combineMaybe(state: Behavior, advancedMaybe: Behavior): Behavior {
        return Behavior(
            returns = state.returns.combineSequentialExecution(advancedMaybe.returns.maybe()),
            throws = state.throws.combineSequentialExecution(advancedMaybe.throws.maybe()),
            terminates = state.throws.combineSequentialExecution(advancedMaybe.terminates.maybe()),
        )
    }

    override fun combineExclusiveBranches(stateOne: Behavior, stateTwo: Behavior): Behavior {
        return Behavior(
            returns = stateOne.returns.combineBranch(stateTwo.returns),
            throws = stateOne.throws.combineBranch(stateTwo.throws),
            terminates = stateOne.throws.combineBranch(stateTwo.terminates),
            eitherThrowsOrTerminates = stateOne.eitherThrowsOrTerminates.combineExclusiveBranch(stateTwo.eitherThrowsOrTerminates),
            eitherThrowsOrReturns = stateOne.eitherThrowsOrReturns.combineExclusiveBranch(stateTwo.eitherThrowsOrReturns),
            eitherTerminatesOrReturns = stateOne.eitherTerminatesOrReturns.combineExclusiveBranch(stateTwo.eitherTerminatesOrReturns),
            eitherThrowsReturnsOrTerminates = stateOne.eitherThrowsReturnsOrTerminates.combineExclusiveBranch(stateTwo.eitherThrowsReturnsOrTerminates),
        )
    }

    class FunctionBehavior(
        /** How a function being invoked behaves in terms of throwing */
        val throws: Occurrence,

        /** How a function being invoked behaves in terms of terminating the program */
        val terminates: Occurrence,
    )

    class Behavior(
        /** How a given [BoundExecutable] behaves in terms of throwing */
        val throws: Occurrence,

        /** How a given [BoundExecutable] behaves in terms of terminating the program */
        val terminates: Occurrence,

        /** How a given [BoundExecutable] behaves in terms of normally returning to the caller */
        val returns: Occurrence,

        val eitherThrowsOrTerminates: Occurrence = throws or terminates,
        val eitherThrowsOrReturns: Occurrence = throws or returns,
        val eitherTerminatesOrReturns: Occurrence = terminates or returns,
        val eitherThrowsReturnsOrTerminates: Occurrence = returns or throws or terminates,
    ) {
        val isGuaranteedToReturnThrowOrTerminate: Boolean = eitherThrowsReturnsOrTerminates == Occurrence.GUARANTEED
    }

    sealed class Effect : SingletonEffect(CallFrameExit) {
        override val stateClass get()= CallFrameExit

        data object Throws : Effect()
        data object ThrowsPossibly : Effect()
        data object Returns : Effect()
        data class InvokesFunction(val behavior: FunctionBehavior) : Effect()
    }

    /**
     * Describes what is known about the occurrence of a particular side effect (e.g. return, throw) at runtime.
     * A `null` value of this type means: analysis hasn't been done yet, the runtime behavior is completely unknown.
     *
     * TODO: better name
     */
    enum class Occurrence {
        /** the side effect will never occur */
        NEVER,

        /** the side effect may occur at runtime, not necessarily though */
        POSSIBLY,

        /** the side effect is guaranteed to occur at runtime */
        GUARANTEED,
        ;

        fun maybe(): Occurrence = when (this) {
            NEVER -> NEVER
            POSSIBLY -> POSSIBLY
            GUARANTEED -> POSSIBLY
        }

        /**
         * @return the [Occurrence] when sequentially executing code with `this` and [other] behavior.
         */
        fun combineSequentialExecution(other: Occurrence): Occurrence = when (this) {
            NEVER -> when (other) {
                NEVER -> NEVER
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
            }
            POSSIBLY -> when(other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
            }
            GUARANTEED -> GUARANTEED
        }

        infix fun or(other: Occurrence): Occurrence = combineSequentialExecution(other)

        fun combineExclusiveBranch(other: Occurrence): Occurrence = when (this) {
            NEVER -> when (other) {
                NEVER -> NEVER
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
            }
            POSSIBLY -> when (other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
            }
            GUARANTEED -> when (other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
            }
        }

        /**
         * @return the [Occurrence] when executing code with **either** `this` **or** [other]
         * behavior, depending on a runtime value (used for conditions, loops).
         */
        fun combineBranch(other: Occurrence): Occurrence = when (this) {
            NEVER -> when (other) {
                NEVER -> NEVER
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
            }
            POSSIBLY -> when (other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
            }
            GUARANTEED -> when(other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
            }
        }
    }

    object Subject
}