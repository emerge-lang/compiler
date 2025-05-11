package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.MissingTypeArgumentDiagnostic
import compiler.diagnostic.SuperfluousTypeArgumentsDiagnostic
import compiler.diagnostic.TypeArgumentOutOfBoundsDiagnostic
import compiler.diagnostic.TypeArgumentVarianceMismatchDiagnostic
import compiler.diagnostic.TypeArgumentVarianceSuperfluousDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span

/* TODO: optimization potential
 * Have a custom collection class that optimized the get-a-copy-plus-one-element use-case
 * Set-properties are probably not needed because we can track changes there explicitly
 * and answer the question "Did this unification produce any errors?" without the set-contains
 * operation done now
 */

interface TypeUnification {
    val constraints: Map<TypeVariable, BoundTypeReference>
    val diagnostics: Set<Diagnostic>

    fun plus(variable: TypeVariable, binding: BoundTypeReference, assignmentLocation: Span): TypeUnification
    fun plusReporting(diagnostic: Diagnostic): TypeUnification = plusDiagnostics(setOf(diagnostic))
    fun plusDiagnostics(diagnostics: Set<Diagnostic>): TypeUnification

    fun doTreatingNonUnifiableAsOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(ValueNotAssignableAsArgumentOutOfBounds(this, parameter, argument), action)
    }

    fun doWithIgnoringReportings(action: (TypeUnification) -> TypeUnification): TypeUnification

    fun getErrorsNotIn(previous: TypeUnification): Sequence<Diagnostic> {
        return diagnostics.asSequence()
            .filter { it.severity >= Diagnostic.Severity.ERROR }
            .filter { it !in previous.diagnostics }
    }

    companion object {
        val EMPTY: TypeUnification = DefaultTypeUnification.EMPTY

        /**
         * For a type reference or function call, builds a [TypeUnification] that contains the explicit type arguments. E.g.:
         *
         *     class X<E, T> {}
         *
         *     val foo: X<Int, Boolean>
         *
         * Then you would call `fromExplicit(<params of base type X>, <int ant boolean type args>, ...)`
         * and the return value would be `[E = Int, T = Boolean] Errors: 0`
         *
         * @param argumentsLocation Location of where the type arguments are being supplied. Used as a fallback
         * for [Diagnostic]s if there are no type arguments and [allowZeroTypeArguments] is false
         * @param allowZeroTypeArguments Whether 0 type arguments is valid even if [typeParameters] is non-empty.
         * This is the case for function invocations, but type references always need to specify all type args.
         */
        fun fromExplicit(
            typeParameters: List<BoundTypeParameter>,
            arguments: List<BoundTypeArgument>?,
            argumentsLocation: Span,
            allowMissingTypeArguments: Boolean = false,
        ): TypeUnification {
            var unification = EMPTY

            if (arguments == null) {
                if (typeParameters.isNotEmpty() && !allowMissingTypeArguments) {
                    for (typeParam in typeParameters) {
                        unification = unification.plusReporting(MissingTypeArgumentDiagnostic(typeParam.astNode, argumentsLocation))
                    }
                }

                return unification
            }

            for (i in 0..typeParameters.lastIndex.coerceAtMost(arguments.lastIndex)) {
                val parameter = typeParameters[i]
                val argument = arguments[i]
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        unification = unification.plusReporting(TypeArgumentVarianceMismatchDiagnostic(parameter.astNode, argument))
                    } else {
                        unification = unification.plusReporting(TypeArgumentVarianceSuperfluousDiagnostic(argument))
                    }
                }

                val nextUnification = unification.doTreatingNonUnifiableAsOutOfBounds(parameter, argument) { subUnification ->
                    parameter.bound.unify(argument, argument.span ?: Span.UNKNOWN, subUnification)
                }
                val hadErrors = nextUnification.getErrorsNotIn(unification).any()
                unification = nextUnification.plus(TypeVariable(parameter), if (!hadErrors) argument else parameter.bound, argument.span ?: Span.UNKNOWN)
            }

            for (i in arguments.size..typeParameters.lastIndex) {
                unification = unification.plusReporting(
                    MissingTypeArgumentDiagnostic(typeParameters[i].astNode, arguments.lastOrNull()?.span ?: argumentsLocation)
                )
            }
            if (arguments.size > typeParameters.size) {
                unification = unification.plusReporting(
                    SuperfluousTypeArgumentsDiagnostic(
                        typeParameters.size,
                        arguments[typeParameters.size].astNode,
                    )
                )
            }

            return unification
        }
    }
}

private class DefaultTypeUnification private constructor(
    override val constraints: Map<TypeVariable, BoundTypeReference>,
    override val diagnostics: Set<Diagnostic>,
) : TypeUnification {
    override fun plusDiagnostics(diagnostics: Set<Diagnostic>): TypeUnification {
        return DefaultTypeUnification(constraints, this.diagnostics + diagnostics)
    }

    override fun plus(variable: TypeVariable, binding: BoundTypeReference, assignmentLocation: Span): TypeUnification {
        val previousConstraint = constraints[variable] ?: variable.parameter.bound
        if (previousConstraint is BoundTypeArgument) {
            // type has been fixed explicitly -> no rebinding
            return this
        }

        val newConstraint = previousConstraint.intersect(binding)
        val assignabilityError = binding.evaluateAssignabilityTo(previousConstraint, assignmentLocation)

        return DefaultTypeUnification(
            constraints.plus(variable to newConstraint),
            diagnostics + setOfNotNull(assignabilityError)
        )
    }

    override fun doWithIgnoringReportings(action: (TypeUnification) -> TypeUnification): TypeUnification {
        val result = action(this)
        return DefaultTypeUnification(
            result.constraints,
            this.diagnostics,
        )
    }

    override fun toString(): String {
        val bindingsStr = constraints.entries.joinToString(
            prefix = "[",
            transform = { (key, value) ->
                var keyStr = ""
                if (key.mutability != key.parameter.bound.mutability) {
                    keyStr += key.mutability.keyword.text + " "
                }
                keyStr += key.parameter.name
                "$keyStr = $value"
            },
            separator = ", ",
            postfix = "]",
        )
        val nErrors = diagnostics.count { it.severity >= Diagnostic.Severity.ERROR }

        return "$bindingsStr Errors:$nErrors"
    }

    companion object {
        val EMPTY = DefaultTypeUnification(emptyMap(), emptySet())
    }
}

private abstract class DecoratingTypeUnification<Self : DecoratingTypeUnification<Self>> : TypeUnification {
    abstract val undecorated: TypeUnification

    abstract override fun plus(variable: TypeVariable, binding: BoundTypeReference, assignmentLocation: Span): Self

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
    override val constraints get() = undecorated.constraints
    override val diagnostics get() = undecorated.diagnostics

    override fun plusDiagnostics(diagnostics: Set<Diagnostic>): TypeUnification {
        val mappedDiagnostics = diagnostics
            .map { diagnostic ->
                if (diagnostic !is ValueNotAssignableDiagnostic) diagnostic else {
                    TypeArgumentOutOfBoundsDiagnostic(parameter.astNode, argument, diagnostic.reason)
                }
            }
            .toSet()

        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusDiagnostics(mappedDiagnostics), parameter, argument)
    }

    override fun plus(variable: TypeVariable, binding: BoundTypeReference, assignmentLocation: Span): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plus(variable, binding, assignmentLocation), parameter, argument)
    }

    override fun doWithIgnoringReportings(action: (TypeUnification) -> TypeUnification): TypeUnification {
        return ValueNotAssignableAsArgumentOutOfBounds(
            doWithIgnoringReportings(action),
            parameter,
            argument,
        )
    }
}