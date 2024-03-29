package compiler.binding.context.effect

import compiler.InternalCompilerError
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.binding.BoundVariable
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.VariableUsedAfterLifetimeReporting

object VariableLifetime : EphemeralStateClass<BoundVariable, VariableLifetime.State, VariableLifetime.Effect> {
    override fun getInitialState(subject: BoundVariable): State {
        if (subject.ownershipAtDeclarationTime == VariableOwnership.CAPTURED && subject.typeAtDeclarationTime?.mutability == TypeMutability.EXCLUSIVE) {
            return State.AliveCapturedExclusive
        }

        return State.Untracked
    }

    override fun fold(state: State, effect: Effect): State {
        effect as Effect.ValueCaptured // only one as of now
        return when (state) {
            is State.Untracked,
            is State.Dead -> state
            is State.AliveCapturedExclusive -> State.Dead(effect.subject, effect.capturedAt)
        }
    }

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return advancedMaybe.maybe()
    }

    override fun intersect(stateOne: State, stateTwo: State): State {
        return when (stateOne) {
            is State.Untracked -> {
                check(stateTwo is State.Untracked) { "variables cannot suddenly become tracked" }
                stateOne
            }
            is State.AliveCapturedExclusive -> when (stateTwo) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveCapturedExclusive -> stateOne
                is State.Dead -> stateTwo.maybe()
            }
            is State.Dead -> when (stateTwo) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveCapturedExclusive -> stateOne.maybe()
                is State.Dead -> stateOne
            }
        }
    }

    sealed interface State {
        fun maybe(): State = this
        fun validateValueRead(readOccursAt: SourceLocation): Collection<Reporting> = emptySet()

        /**
         * No lifetime tracking is done, it lives for the entirety of its scope
         */
        object Untracked : State

        object AliveCapturedExclusive : State

        class Dead(
            val variable: BoundVariable,
            val lifetimeEndedAt: SourceLocation,
            val maybe: Boolean = false,
        ) : State {
            override fun maybe() = Dead(variable, lifetimeEndedAt, true)
            override fun validateValueRead(readOccursAt: SourceLocation): Collection<Reporting> {
                return setOf(VariableUsedAfterLifetimeReporting(variable.declaration, readOccursAt, lifetimeEndedAt, maybe))
            }
        }
    }

    sealed interface Effect : SideEffect<BoundVariable> {
        override val stateClass: EphemeralStateClass<*, *, *> get() = VariableLifetime

        class ValueCaptured(override val subject: BoundVariable, val capturedAt: SourceLocation) : Effect
        // TODO: resurrect variable when reassigned
    }
}