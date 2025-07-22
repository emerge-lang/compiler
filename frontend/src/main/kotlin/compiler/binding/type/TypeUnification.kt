package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.MissingTypeArgumentDiagnostic
import compiler.diagnostic.SuperfluousTypeArgumentsDiagnostic
import compiler.diagnostic.TypeArgumentOutOfBoundsDiagnostic
import compiler.diagnostic.TypeArgumentVarianceMismatchDiagnostic
import compiler.diagnostic.TypeArgumentVarianceSuperfluousDiagnostic
import compiler.diagnostic.UnsatisfiableTypeVariableConstraintsDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span

/* TODO: optimization potential
 * Have a custom collection class that optimizes the get-a-copy-plus-one-element use-case
 * Set-properties are probably not needed because we can track changes there explicitly
 * and answer the question "Did this unification produce any errors?" without the set-contains
 * operation done now
 */
class TypeUnification private constructor(
    private val variableStates: Map<BoundTypeParameter, TypeUnification.VariableState>,
    val diagnostics: Set<Diagnostic>,
) {
    fun getErrorsNotIn(previous: TypeUnification): Sequence<Diagnostic> {
        return diagnostics.asSequence()
            .filter { it.severity >= Diagnostic.Severity.ERROR }
            .filter { it !in previous.diagnostics }
    }

    fun plusDiagnostic(diagnostic: Diagnostic): TypeUnification {
        return TypeUnification(variableStates, this.diagnostics + diagnostic)
    }

    /**
     * @return `this`, plus the constraint that `value(parameter).isAssignableTo(upperBound)`.
     */
    fun plusSubtypeConstraint(
        parameter: BoundTypeParameter,
        upperBound: BoundTypeReference,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        if (stateBefore.isExact) {
            return upperBound.unify(stateBefore.upperBound, assignmentLocation, this)
        }

        val newUpperBound = stateBefore.upperBound.intersect(upperBound)
        if (newUpperBound.isNonNullableNothing) {
            // incompatible constraints. The question is: is the incompatibility from other constraints, or the default upper bound?
            val unificationWithDefaultBound = stateBefore.staticUpperBound.unify(upperBound, assignmentLocation, this)
            return if (unificationWithDefaultBound.getErrorsNotIn(this).any()) {
                unificationWithDefaultBound
            } else {
                this.plusDiagnostic(UnsatisfiableTypeVariableConstraintsDiagnostic.forSubtypeConstraint(parameter, stateBefore, upperBound, assignmentLocation))
            }
        }

        val unificationWithLowerBound = newUpperBound.unify(stateBefore.lowerBound, assignmentLocation, this)
        if (unificationWithLowerBound.getErrorsNotIn(this).any()) {
            return this.plusDiagnostic(UnsatisfiableTypeVariableConstraintsDiagnostic.forSubtypeConstraint(parameter, stateBefore, upperBound, assignmentLocation))
        }

        return TypeUnification(
            unificationWithLowerBound.variableStates + mapOf(parameter to stateBefore.copy(upperBound = newUpperBound)),
            diagnostics,
        )
    }

    /**
     * @return `this`, plus the constraint that `lowerBound.isAssignableTo(value(parameter))`.
     */
    fun plusSupertypeConstraint(
        parameter: BoundTypeParameter,
        lowerBound: BoundTypeReference,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        if (stateBefore.isExact) {
            return stateBefore.lowerBound.unify(lowerBound, assignmentLocation, this)
        }
        val newLowerBound = stateBefore.lowerBound.closestCommonSupertypeWith(lowerBound)
        val unificationWithUpperBound = stateBefore.upperBound.unify(newLowerBound, assignmentLocation, this)
        if (unificationWithUpperBound.getErrorsNotIn(this).any()) {
            // incompatible constraints. The question is: is the incompatibility from other constraints, or the default upper bound?
            val unificationWithDefaultBound = stateBefore.staticUpperBound.unify(lowerBound, assignmentLocation, this)
            if (unificationWithDefaultBound.getErrorsNotIn(this).any()) {
                return unificationWithDefaultBound
            }

            return this.plusDiagnostic(UnsatisfiableTypeVariableConstraintsDiagnostic.forSupertypeConstraint(parameter, stateBefore, lowerBound, assignmentLocation))
        }

        return TypeUnification(
            unificationWithUpperBound.variableStates + mapOf(parameter to stateBefore.copy(lowerBound = newLowerBound)),
            diagnostics,
        )
    }

    /**
     * @return `this`, plus the constraint that [parameter] should be bound to exactly [binding]. Use for explicit type
     * arguments only.
     */
    fun plusExactBinding(
        parameter: BoundTypeParameter,
        binding: BoundTypeArgument,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        val unificationWithUpperBound = stateBefore.upperBound.unify(binding, assignmentLocation, this)
        val errorWithUpperBound = unificationWithUpperBound.getErrorsNotIn(this).filterIsInstance<ValueNotAssignableDiagnostic>().firstOrNull()
        if (errorWithUpperBound != null) {
            return this.plusDiagnostic(TypeArgumentOutOfBoundsDiagnostic(parameter.astNode, binding, errorWithUpperBound.reason))
        }

        val unificationWithLowerBound = binding.unify(stateBefore.lowerBound, assignmentLocation, this)
        if (unificationWithLowerBound.getErrorsNotIn(this).any()) {
            return unificationWithLowerBound
        }

        return TypeUnification(
            unificationWithLowerBound.variableStates + mapOf(parameter to stateBefore.copy(upperBound = binding, lowerBound = binding, isExact = true)),
            diagnostics,
        )
    }

    fun mergedWith(other: TypeUnification, dupeHandler: (BoundTypeParameter, VariableState, VariableState, Diagnosis) -> VariableState): TypeUnification {
        val diagnosis = CollectingDiagnosis()
        val resultStates = this.variableStates.toMutableMap()
        for ((param, otherState) in other.variableStates) {
            resultStates.merge(param, otherState) { selfState, _ ->
                if (selfState == otherState) {
                    selfState
                } else {
                    dupeHandler(param, selfState, otherState, diagnosis)
                }
            }
        }
        return TypeUnification(
            resultStates,
            this.diagnostics + other.diagnostics + diagnosis.findings,
        )
    }

    fun getFinalValueFor(parameter: BoundTypeParameter): BoundTypeReference {
        val state = variableStates[parameter] ?: return parameter.bound.instantiateAllParameters(this)

        val raw = state.lowerBound.takeUnless { it.isNonNullableNothing }
            ?: state.upperBound

        return raw.instantiateFreeVariables(this)
    }

    val bindings: Iterable<Pair<BoundTypeParameter, BoundTypeReference>> = object : Iterable<Pair<BoundTypeParameter, BoundTypeReference>> {
        override fun iterator(): Iterator<Pair<BoundTypeParameter, BoundTypeReference>> {
            return variableStates.keys
                .map { param -> param to getFinalValueFor(param) }
                .iterator()
        }
    }

    override fun toString(): String {
        val bindingsStr = variableStates.entries.asSequence()
            .flatMap { (param, state) ->
                if (state.isExact || state.lowerBound == state.upperBound) return@flatMap sequenceOf("${param.name} = ${state.lowerBound}")
                sequenceOf("${param.name} : ${state.upperBound}") + (
                    sequenceOf(state.lowerBound)
                        .filterNot { it.isNonNullableNothing }
                        .map { "$it : ${param.name}" }
                )
            }
            .joinToString(
                prefix = "[",
                separator = ", ",
                postfix = "]",
            )
        val nErrors = diagnostics.count { it.severity >= Diagnostic.Severity.ERROR }

        return "$bindingsStr Errors:$nErrors"
    }

    companion object {
        val EMPTY = TypeUnification(emptyMap(), emptySet())

        fun forInferenceOf(parameters: Collection<BoundTypeParameter>): TypeUnification {
            return TypeUnification(
                parameters.associateWith {
                    val upperBound = it.bound.withTypeVariables(parameters)
                    VariableState(upperBound, upperBound, it.context.swCtx.getBottomType(it.astNode.span), false)
                },
                emptySet(),
            )
        }
        
        /**
         * For a type reference or function call, builds a [TypeUnification] that contains the explicit type arguments. E.g.:
         *
         *     class X<E, T> {}
         *
         *     val foo: X<Int, Boolean>
         *
         * Then you would call `fromExplicit(<params of base type X>, listOf(<int type arg, boolean type arg>), ...)`
         * and the return value would be `[E = Int, T = Boolean] Errors: 0`
         *
         * @param allTypeParameters all type parameters in play for the inference, see [compiler.binding.BoundFunction.allTypeParameters]
         * @param declaredTypeParameters the type parameters declared at the specific inference location, see [compiler.binding.BoundFunction.declaredTypeParameters]
         * @param argumentsLocation Location of where the type arguments are being supplied. Used as a fallback
         * for [Diagnostic]s if there are no type arguments and [allowZeroTypeArguments] is false
         * @param allowMissingTypeArguments Whether 0 type arguments is valid even if [declaredTypeParameters] is non-empty.
         * This is the case for function invocations, but type references always need to specify all type args.
         */
        fun fromExplicit(
            allTypeParameters: Collection<BoundTypeParameter>,
            declaredTypeParameters: List<BoundTypeParameter>,
            arguments: List<BoundTypeArgument>?,
            argumentsLocation: Span,
            allowMissingTypeArguments: Boolean = false,
        ): TypeUnification {
            var unification = forInferenceOf(allTypeParameters)

            if (arguments == null) {
                if (declaredTypeParameters.isNotEmpty() && !allowMissingTypeArguments) {
                    for (typeParam in declaredTypeParameters) {
                        unification = unification.plusDiagnostic(MissingTypeArgumentDiagnostic(typeParam.astNode, argumentsLocation))
                    }
                }

                return unification
            }

            for (i in 0..declaredTypeParameters.lastIndex.coerceAtMost(arguments.lastIndex)) {
                val parameter = declaredTypeParameters[i]
                val argument = arguments[i]
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        unification = unification.plusDiagnostic(TypeArgumentVarianceMismatchDiagnostic(parameter.astNode, argument))
                    } else {
                        unification = unification.plusDiagnostic(TypeArgumentVarianceSuperfluousDiagnostic(argument))
                    }
                }

                unification = unification.plusExactBinding(parameter, argument, argument.span ?: Span.UNKNOWN)
            }

            for (i in arguments.size..declaredTypeParameters.lastIndex) {
                unification = unification.plusDiagnostic(
                    MissingTypeArgumentDiagnostic(
                        declaredTypeParameters[i].astNode,
                        arguments.lastOrNull()?.span ?: argumentsLocation,
                    )
                )
            }
            if (arguments.size > declaredTypeParameters.size) {
                unification = unification.plusDiagnostic(
                    SuperfluousTypeArgumentsDiagnostic(
                        declaredTypeParameters.size,
                        arguments[declaredTypeParameters.size].astNode,
                    )
                )
            }

            return unification
        }
    }

    data class VariableState(
        val staticUpperBound: BoundTypeReference,
        val upperBound: BoundTypeReference,
        /**
         * TODO: this can become a union type as soon as that is implemented, and the ::closestCommonSupertype approximation can be yeeted
         */
        val lowerBound: BoundTypeReference,
        val isExact: Boolean,
    )
}

class TypeVariableNotUnderInferenceException(val parameter: BoundTypeParameter) : RuntimeException("Cannot work with type variable ${parameter.name} because of missing inference context")