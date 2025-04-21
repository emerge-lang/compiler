package compiler.binding.context.effect

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.binding.BoundVariable
import compiler.binding.expression.BoundIdentifierExpression
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.borrowedVariableCaptured
import compiler.diagnostic.lifetimeEndingCaptureInLoop
import compiler.diagnostic.simultaneousIncompatibleBorrows
import compiler.diagnostic.variableUsedAfterLifetime
import compiler.lexer.Span

object VariableLifetime : EphemeralStateClass<BoundVariable, VariableLifetime.State, VariableLifetime.Effect> {
    override fun getInitialState(subject: BoundVariable): State {
        if (subject.typeAtDeclarationTime?.mutability == TypeMutability.EXCLUSIVE) {
            return State.AliveExclusive
        }

        return State.Untracked
    }

    override fun fold(state: State, effect: Effect): State {
        return when (effect) {
            is Effect.ValueCaptured -> {
                if (state is State.AliveExclusive && effect.withMutability != TypeMutability.READONLY) {
                    State.Dead(effect.subject, effect.capturedAt)
                } else {
                    state
                }
            }
            is Effect.NewValueAssigned -> return getInitialState(effect.subject)
            is Effect.BorrowStarted -> when (state) {
                is State.Untracked,
                is State.Dead -> state
                is State.AliveExclusive -> State.AliveExclusiveWithActiveBorrow(
                    effect.withMutability,
                    effect.borrowStartedAt,
                    false,
                )
                is State.AliveExclusiveWithActiveBorrow -> State.AliveExclusiveWithActiveBorrow(
                    state.withMutability.intersect(effect.withMutability),
                    state.borrowStartedAt,
                    false,
                )
            }
            is Effect.BorrowEnded -> when (state) {
                is State.Untracked,
                is State.Dead -> state
                is State.AliveExclusive -> state
                is State.AliveExclusiveWithActiveBorrow -> State.AliveExclusive
            }
        }
    }

    override fun combineMaybe(state: State, advancedMaybe: State): State {
        return when (state) {
            is State.Untracked -> {
                check(advancedMaybe is State.Untracked) { "variables cannot suddenly become tracked" }
                state
            }
            is State.AliveExclusive -> when (advancedMaybe) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveExclusive -> state
                is State.AliveExclusiveWithActiveBorrow -> state.maybe()
                is State.Dead -> advancedMaybe.maybe()
            }
            is State.AliveExclusiveWithActiveBorrow -> when (advancedMaybe) {
                is State.Dead -> advancedMaybe.maybe()
                is State.Untracked -> state.maybe()
                is State.AliveExclusive -> state.maybe()
                is State.AliveExclusiveWithActiveBorrow -> state
            }
            is State.Dead -> state
        }
    }

    override fun intersect(stateOne: State, stateTwo: State): State {
        return when (stateOne) {
            is State.Untracked -> {
                check(stateTwo is State.Untracked) { "variables cannot suddenly become tracked" }
                stateOne
            }
            is State.AliveExclusive -> when (stateTwo) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveExclusive -> stateOne
                is State.AliveExclusiveWithActiveBorrow -> stateTwo.maybe()
                is State.Dead -> stateTwo.maybe()
            }
            is State.AliveExclusiveWithActiveBorrow -> when (stateTwo) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveExclusive -> stateOne.maybe()
                is State.AliveExclusiveWithActiveBorrow -> stateOne
                is State.Dead -> stateTwo.maybe()
            }
            is State.Dead -> when (stateTwo) {
                is State.Untracked -> throw InternalCompilerError("this should be impossible, variables cannot suddenly become tracked")
                is State.AliveExclusive -> stateOne.maybe()
                is State.AliveExclusiveWithActiveBorrow -> stateOne.maybe()
                is State.Dead -> stateOne
            }
        }
    }

    sealed interface State {
        fun maybe(): State = this
        fun validateCapture(read: BoundIdentifierExpression, diagnosis: Diagnosis) = Unit
        fun validateRepeatedCapture(stateBeforeCapture: State, read: BoundIdentifierExpression, diagnosis: Diagnosis) = Unit
        fun validateNewBorrowStart(withMutability: TypeMutability, borrowedBy: BoundIdentifierExpression, subject: BoundVariable, diagnosis: Diagnosis): Boolean

        /**
         * No lifetime tracking is done, it lives for the entirety of its scope
         */
        data object Untracked : State {
            override fun validateNewBorrowStart(
                withMutability: TypeMutability,
                borrowedBy: BoundIdentifierExpression,
                subject: BoundVariable,
                diagnosis: Diagnosis
            ): Boolean {
                return true
            }
        }

        data object AliveExclusive : State {
            override fun validateNewBorrowStart(
                withMutability: TypeMutability,
                borrowedBy: BoundIdentifierExpression,
                subject: BoundVariable,
                diagnosis: Diagnosis,
            ): Boolean {
                return true
            }
        }

        data class AliveExclusiveWithActiveBorrow(
            val withMutability: TypeMutability,
            val borrowStartedAt: Span,
            val maybe: Boolean = false,
        ) : State {
            override fun maybe() = if (maybe) this else AliveExclusiveWithActiveBorrow(withMutability, borrowStartedAt, maybe = true)

            override fun validateCapture(
                read: BoundIdentifierExpression,
                diagnosis: Diagnosis,
            ) {
                diagnosis.borrowedVariableCaptured((read.referral as BoundIdentifierExpression.ReferringVariable).variable, read)
            }

            override fun validateRepeatedCapture(
                stateBeforeCapture: State,
                read: BoundIdentifierExpression,
                diagnosis: Diagnosis,
            ) {
                // nothing to do here; there shouldn't be a way to even trigger this situation; and even if, the diagnostic from validateCapture should handle it
            }

            override fun validateNewBorrowStart(
                withMutability: TypeMutability,
                borrowedBy: BoundIdentifierExpression,
                subject: BoundVariable,
                diagnosis: Diagnosis
            ): Boolean {
                if (withMutability.isAssignableTo(this.withMutability) || this.withMutability.isAssignableTo(withMutability)) {
                    return true
                }

                diagnosis.simultaneousIncompatibleBorrows(subject, borrowStartedAt, this.withMutability, borrowedBy.declaration.span, withMutability)
                return false
            }
        }

        data class Dead(
            val variable: BoundVariable,
            val lifetimeEndedAt: Span,
            val maybe: Boolean = false,
        ) : State {
            override fun maybe() = if (maybe) this else Dead(variable, lifetimeEndedAt, true)
            override fun validateCapture(read: BoundIdentifierExpression, diagnosis: Diagnosis) {
                diagnosis.variableUsedAfterLifetime(variable, read, this)
            }

            override fun validateRepeatedCapture(stateBeforeCapture: State, read: BoundIdentifierExpression, diagnosis: Diagnosis) {
                if (stateBeforeCapture is Dead) {
                    // the looping isn't causing the problem; don't report anything here. validateCapture should report it
                    return
                }

                diagnosis.lifetimeEndingCaptureInLoop(variable, read)
            }

            override fun validateNewBorrowStart(
                withMutability: TypeMutability,
                borrowedBy: BoundIdentifierExpression,
                subject: BoundVariable,
                diagnosis: Diagnosis
            ): Boolean {
                diagnosis.variableUsedAfterLifetime(variable, borrowedBy, this)
                return false
            }
        }
    }

    sealed interface Effect : SideEffect<BoundVariable> {
        override val stateClass: EphemeralStateClass<*, *, *> get() = VariableLifetime

        data class ValueCaptured(
            override val subject: BoundVariable,
            val withMutability: TypeMutability,
            val capturedAt: Span,
        ) : Effect

        data class NewValueAssigned(
            override val subject: BoundVariable
        ) : Effect

        data class BorrowStarted(
            override val subject: BoundVariable,
            val withMutability: TypeMutability,
            val borrowStartedAt: Span,
        ) : Effect

        data class BorrowEnded(
            override val subject: BoundVariable,
        ) : Effect
    }
}