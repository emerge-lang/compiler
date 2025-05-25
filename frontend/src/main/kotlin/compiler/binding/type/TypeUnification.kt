package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
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

interface TypeUnification {
    val diagnostics: Set<Diagnostic>

    //fun plus(parameter: BoundTypeParameter, binding: BoundTypeReference, assignmentLocation: Span): TypeUnification
    /**
     * @return `this`, plus the constraint that `value(parameter).isAssignableTo(upperBound)`.
     */
    fun plusSubtypeConstraint(parameter: BoundTypeParameter, upperBound: BoundTypeReference, assignmentLocation: Span): TypeUnification

    /**
     * @return `this`, plus the constraint that `lowerBound.isAssignableTo(value(parameter))`.
     */
    fun plusSupertypeConstraint(parameter: BoundTypeParameter, lowerBound: BoundTypeReference, assignmentLocation: Span): TypeUnification

    /**
     * @return `this`, plus the constraint that [parameter] should be bound to exactly [binding]. Use for explicit type
     * arguments only.
     */
    fun plusExactBinding(parameter: BoundTypeParameter, binding: BoundTypeArgument, assignmentLocation: Span): TypeUnification

    fun mergedWith(other: TypeUnification): TypeUnification

    fun getFinalValueFor(parameter: BoundTypeParameter): BoundTypeReference

    fun plusReporting(diagnostic: Diagnostic): TypeUnification = plusDiagnostics(setOf(diagnostic))
    fun plusDiagnostics(diagnostics: Iterable<Diagnostic>): TypeUnification

    val bindings: Iterable<Pair<BoundTypeParameter, BoundTypeReference>>

    fun doTreatingNonUnifiableAsOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(ValueNotAssignableAsArgumentOutOfBounds(this, parameter, argument), action)
    }

    fun getErrorsNotIn(previous: TypeUnification): Sequence<Diagnostic> {
        return diagnostics.asSequence()
            .filter { it.severity >= Diagnostic.Severity.ERROR }
            .filter { it !in previous.diagnostics }
    }

    companion object {
        val EMPTY: TypeUnification = DefaultTypeUnification.EMPTY

        fun forInferenceOf(parameters: Collection<BoundTypeParameter>): TypeUnification {
            return DefaultTypeUnification.forInferenceOf(parameters)
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
                        unification = unification.plusReporting(MissingTypeArgumentDiagnostic(typeParam.astNode, argumentsLocation))
                    }
                }

                return unification
            }

            for (i in 0..declaredTypeParameters.lastIndex.coerceAtMost(arguments.lastIndex)) {
                val parameter = declaredTypeParameters[i]
                val argument = arguments[i]
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        unification = unification.plusReporting(TypeArgumentVarianceMismatchDiagnostic(parameter.astNode, argument))
                    } else {
                        unification = unification.plusReporting(TypeArgumentVarianceSuperfluousDiagnostic(argument))
                    }
                }

                unification = unification.plusExactBinding(parameter, argument, argument.span ?: Span.UNKNOWN)
            }

            for (i in arguments.size..declaredTypeParameters.lastIndex) {
                unification = unification.plusReporting(
                    MissingTypeArgumentDiagnostic(declaredTypeParameters[i].astNode, arguments.lastOrNull()?.span ?: argumentsLocation)
                )
            }
            if (arguments.size > declaredTypeParameters.size) {
                unification = unification.plusReporting(
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

private class DefaultTypeUnification private constructor(
    private val variableStates: Map<BoundTypeParameter, TypeUnification.VariableState>,
    override val diagnostics: Set<Diagnostic>,
) : TypeUnification {
    override fun plusDiagnostics(diagnostics: Iterable<Diagnostic>): TypeUnification {
        return DefaultTypeUnification(variableStates, this.diagnostics + diagnostics)
    }

    override fun plusSubtypeConstraint(
        parameter: BoundTypeParameter,
        upperBound: BoundTypeReference,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        if (stateBefore.isExact) {
            return upperBound.unify(stateBefore.upperBound, assignmentLocation, this)
        }

        val newUpperBound = stateBefore.upperBound.intersect(upperBound)
        if (newUpperBound.isNothing) {
            // incompatible constraints. The question is: is the incompatibility from other constraints, or the default upper bound?
            val unificationWithDefaultBound = stateBefore.staticUpperBound.unify(upperBound, assignmentLocation, this)
            return if (unificationWithDefaultBound.getErrorsNotIn(this).any()) {
                unificationWithDefaultBound
            } else {
                this.plusDiagnostics(setOf(UnsatisfiableTypeVariableConstraintsDiagnostic.forSubtypeConstraint(parameter, stateBefore, upperBound, assignmentLocation)))
            }
        }

        val unificationWithLowerBound = newUpperBound.unify(stateBefore.lowerBound, assignmentLocation, this) as DefaultTypeUnification // TODO: get rid of this downcast
        if (unificationWithLowerBound.getErrorsNotIn(this).any()) {
            return this.plusDiagnostics(setOf(UnsatisfiableTypeVariableConstraintsDiagnostic.forSubtypeConstraint(parameter, stateBefore, upperBound, assignmentLocation)))
        }

        return DefaultTypeUnification(
            unificationWithLowerBound.variableStates + mapOf(parameter to stateBefore.copy(upperBound = newUpperBound)),
            diagnostics,
        )
    }

    override fun plusSupertypeConstraint(
        parameter: BoundTypeParameter,
        lowerBound: BoundTypeReference,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        if (stateBefore.isExact) {
            return stateBefore.lowerBound.unify(lowerBound, assignmentLocation, this)
        }
        val newLowerBound = stateBefore.lowerBound.closestCommonSupertypeWith(lowerBound)
        val unificationWithUpperBound = stateBefore.upperBound.unify(newLowerBound, assignmentLocation, this) as DefaultTypeUnification // TODO: get rid of this downcast
        if (unificationWithUpperBound.getErrorsNotIn(this).any()) {
            // incompatible constraints. The question is: is the incompatibility from other constraints, or the default upper bound?
            val unificationWithDefaultBound = stateBefore.staticUpperBound.unify(lowerBound, assignmentLocation, this)
            if (unificationWithDefaultBound.getErrorsNotIn(this).any()) {
                return unificationWithDefaultBound
            }

            return this.plusDiagnostics(setOf(UnsatisfiableTypeVariableConstraintsDiagnostic.forSupertypeConstraint(parameter, stateBefore, lowerBound, assignmentLocation)))
        }

        return DefaultTypeUnification(
            unificationWithUpperBound.variableStates + mapOf(parameter to stateBefore.copy(lowerBound = newLowerBound)),
            diagnostics,
        )
    }

    override fun plusExactBinding(
        parameter: BoundTypeParameter,
        binding: BoundTypeArgument,
        assignmentLocation: Span
    ): TypeUnification {
        val stateBefore = variableStates[parameter] ?: throw TypeVariableNotUnderInferenceException(parameter)
        val unificationWithUpperBound = stateBefore.upperBound.unify(binding, assignmentLocation, this)
        val errorWithUpperBound = unificationWithUpperBound.getErrorsNotIn(this).filterIsInstance<ValueNotAssignableDiagnostic>().firstOrNull()
        if (errorWithUpperBound != null) {
            return this.plusDiagnostics(setOf(TypeArgumentOutOfBoundsDiagnostic(parameter.astNode, binding, errorWithUpperBound.reason)))
        }

        val unificationWithLowerBound = binding.unify(stateBefore.lowerBound, assignmentLocation, this) as DefaultTypeUnification // TODO: get rid of this downcast
        val lowerBoundErrors = unificationWithLowerBound.getErrorsNotIn(this)
        if (lowerBoundErrors.any()) {
            return this.plusDiagnostics(lowerBoundErrors.asIterable())
        }

        return DefaultTypeUnification(
            unificationWithLowerBound.variableStates + mapOf(parameter to stateBefore.copy(upperBound = binding, lowerBound = binding, isExact = true)),
            diagnostics,
        )
    }

    override fun mergedWith(other: TypeUnification): TypeUnification {
        check(other is DefaultTypeUnification) // TODO: remove this assumption
        check(other.variableStates.keys.none { it in this.variableStates }) // TODO: remove this assumption
        return DefaultTypeUnification(
            this.variableStates + other.variableStates,
            this.diagnostics + other.diagnostics,
        )
    }

    override fun getFinalValueFor(parameter: BoundTypeParameter): BoundTypeReference {
        val state = variableStates[parameter] ?: return parameter.bound.instantiateAllParameters(this)

        val raw = state.lowerBound.takeUnless { it.isNothing }
            ?: state.upperBound

        return raw.instantiateFreeVariables(this)
    }

    override val bindings: Iterable<Pair<BoundTypeParameter, BoundTypeReference>> = object : Iterable<Pair<BoundTypeParameter, BoundTypeReference>> {
        override fun iterator(): Iterator<Pair<BoundTypeParameter, BoundTypeReference>> {
            return variableStates.keys
                .map { param -> param to getFinalValueFor(param) }
                .iterator()
        }
    }

    override fun toString(): String {
        val bindingsStr = variableStates.entries.asSequence()
            .flatMap { (param, state) ->
                if (state.isExact) return@flatMap sequenceOf("${param.name} = ${state.lowerBound}")
                sequenceOf("${param.name} : ${state.upperBound}") + (
                    sequenceOf(state.lowerBound)
                        .filterNot { it.isNothing }
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
        val EMPTY = DefaultTypeUnification(emptyMap(), emptySet())

        fun forInferenceOf(parameters: Collection<BoundTypeParameter>): DefaultTypeUnification {
            return DefaultTypeUnification(
                parameters.associateWith {
                    val upperBound = it.bound.withTypeVariables(parameters)
                    TypeUnification.VariableState(upperBound, upperBound, it.context.swCtx.bottomTypeRef, false)
                },
                emptySet(),
            )
        }
    }
}

private abstract class DecoratingTypeUnification<Self : DecoratingTypeUnification<Self>> : TypeUnification {
    abstract val undecorated: TypeUnification

    abstract override fun plusSubtypeConstraint(
        parameter: BoundTypeParameter,
        upperBound: BoundTypeReference,
        assignmentLocation: Span
    ): Self

    abstract override fun plusSupertypeConstraint(
        parameter: BoundTypeParameter,
        lowerBound: BoundTypeReference,
        assignmentLocation: Span
    ): Self

    abstract override fun plusExactBinding(
        parameter: BoundTypeParameter,
        binding: BoundTypeArgument,
        assignmentLocation: Span
    ): Self

    companion object {
        inline fun <reified T : DecoratingTypeUnification<*>> doWithDecorated(modified: T, action: (TypeUnification) -> TypeUnification): TypeUnification {
            val result = action(modified)
            return (result as T).undecorated
        }
    }
}

private class ValueNotAssignableAsArgumentOutOfBounds(
    override val undecorated: TypeUnification,
    private val parameter: BoundTypeParameter,
    private val argument: BoundTypeArgument,
) : DecoratingTypeUnification<ValueNotAssignableAsArgumentOutOfBounds>() {
    override val diagnostics get() = undecorated.diagnostics

    override fun plusDiagnostics(diagnostics: Iterable<Diagnostic>): TypeUnification {
        val mappedDiagnostics = diagnostics
            .map { diagnostic ->
                if (diagnostic !is ValueNotAssignableDiagnostic) diagnostic else {
                    TypeArgumentOutOfBoundsDiagnostic(parameter.astNode, argument, diagnostic.reason)
                }
            }
            .toSet()

        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusDiagnostics(mappedDiagnostics), parameter, argument)
    }

    override fun plusSubtypeConstraint(
        parameter: BoundTypeParameter,
        upperBound: BoundTypeReference,
        assignmentLocation: Span
    ): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusSubtypeConstraint(parameter, upperBound, assignmentLocation), parameter, argument)
    }

    override fun plusSupertypeConstraint(
        parameter: BoundTypeParameter,
        lowerBound: BoundTypeReference,
        assignmentLocation: Span
    ): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusSupertypeConstraint(parameter, lowerBound, assignmentLocation), parameter, argument)
    }

    override fun plusExactBinding(
        parameter: BoundTypeParameter,
        binding: BoundTypeArgument,
        assignmentLocation: Span
    ): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusExactBinding(parameter, binding, assignmentLocation), parameter, argument)
    }

    override fun mergedWith(other: TypeUnification): TypeUnification {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.mergedWith(other), parameter, argument)
    }

    override fun getFinalValueFor(parameter: BoundTypeParameter): BoundTypeReference {
        return undecorated.getFinalValueFor(parameter)
    }

    override val bindings get()= undecorated.bindings
}

class TypeVariableNotUnderInferenceException(val parameter: BoundTypeParameter) : RuntimeException("Cannot work with type variable ${parameter.name} because of missing inference context")