package compiler.binding.context.effect

import compiler.InternalCompilerError
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.binding.BoundVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.ValueUsage
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
                    state.withMutability.union(effect.withMutability),
                    state.borrowStartedAt,
                    false,
                )
            }
            is Effect.EndAllBorrows -> when (state) {
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

    override fun combineExclusiveBranches(stateOne: State, stateTwo: State): State {
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

        /**
         * to be invoked by [BoundIdentifierExpression.ReferringVariable]; will verify whether the [usage] is
         * semantically valid in the current [State], and issue [compiler.diagnostic.Diagnostic]s as necessary.
         * @param repetition repetition of the usage relative to the variable declaration; see [compiler.binding.context.ExecutionScopedCTContext.getRepetitionBehaviorRelativeTo].
         * @return an effect that needs to be propagated to [compiler.binding.context.MutableExecutionScopedCTContext.trackSideEffect]
         * to resemble the effects of the [usage]; or `null` if not needed.
         */
        fun handleUsage(
            subject: BoundIdentifierExpression.ReferringVariable,
            usage: ValueUsage,
            repetition: ExecutionScopedCTContext.Repetition,
            diagnosis: Diagnosis
        ): Effect?

        /**
         * No lifetime tracking is done, it lives for the entirety of its scope
         */
        data object Untracked : State {
            override fun handleUsage(subject: BoundIdentifierExpression.ReferringVariable, usage: ValueUsage, repetition: ExecutionScopedCTContext.Repetition, diagnosis: Diagnosis): Effect? {
                if (subject.variable.ownershipAtDeclarationTime == VariableOwnership.BORROWED && usage.usageOwnership != VariableOwnership.BORROWED) {
                    diagnosis.borrowedVariableCaptured(subject.variable, subject.span)
                }

                return null
            }
        }

        data object AliveExclusive : State {
            override fun handleUsage(subject: BoundIdentifierExpression.ReferringVariable, usage: ValueUsage, repetition: ExecutionScopedCTContext.Repetition, diagnosis: Diagnosis): Effect? {
                return when (usage.usageOwnership) {
                    VariableOwnership.BORROWED -> Effect.BorrowStarted(subject.variable, usage.usedWithMutability, subject.span)
                    VariableOwnership.CAPTURED -> {
                        if (repetition.mayRepeat) {
                            diagnosis.lifetimeEndingCaptureInLoop(subject)
                        }
                        Effect.ValueCaptured(subject.variable, usage.usedWithMutability, subject.span)
                    }
                }
            }
        }

        data class AliveExclusiveWithActiveBorrow(
            val withMutability: TypeMutability,
            val borrowStartedAt: Span,
            val maybe: Boolean = false,
        ) : State {
            override fun maybe() = if (maybe) this else AliveExclusiveWithActiveBorrow(withMutability, borrowStartedAt, maybe = true)

            override fun handleUsage(subject: BoundIdentifierExpression.ReferringVariable, usage: ValueUsage, repetition: ExecutionScopedCTContext.Repetition, diagnosis: Diagnosis): Effect? {
                return when (usage.usageOwnership) {
                    VariableOwnership.CAPTURED -> {
                        diagnosis.borrowedVariableCaptured(subject.variable, subject.span)
                        null
                    }
                    VariableOwnership.BORROWED -> if (usage.usedWithMutability.isAssignableTo(this.withMutability) || this.withMutability.isAssignableTo(usage.usedWithMutability)) {
                        Effect.BorrowStarted(subject.variable, usage.usedWithMutability, subject.span)
                    } else {
                        diagnosis.simultaneousIncompatibleBorrows(subject.variable, borrowStartedAt, this.withMutability, subject.span, usage.usedWithMutability)
                        null
                    }
                }
            }
        }

        data class Dead(
            val variable: BoundVariable,
            val lifetimeEndedAt: Span,
            val maybe: Boolean = false,
        ) : State {
            override fun maybe() = if (maybe) this else Dead(variable, lifetimeEndedAt, true)

            override fun handleUsage(subject: BoundIdentifierExpression.ReferringVariable, usage: ValueUsage, repetition: ExecutionScopedCTContext.Repetition, diagnosis: Diagnosis): Effect? {
                when (usage.usageOwnership) {
                    VariableOwnership.BORROWED -> {
                        diagnosis.variableUsedAfterLifetime(subject, this)
                    }
                    VariableOwnership.CAPTURED -> if (repetition.mayRepeat) {
                        diagnosis.lifetimeEndingCaptureInLoop(subject)
                    } else {
                        diagnosis.variableUsedAfterLifetime(subject, this)
                    }
                }

                return null
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

        data class EndAllBorrows(
            override val subject: BoundVariable,
        ) : Effect
    }
}