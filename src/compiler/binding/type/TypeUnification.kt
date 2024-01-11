package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

/* TODO: optimization potential
 * Have a custom collection class that optimized the get-a-copy-plus-one-element use-case
 * Set-properties are probably not needed because we can track changes there explicitly
 * and answer the question "Did this unification produce any errors?" without the set-contains
 * operation done now
 */

interface TypeUnification {
    val bindings: Map<TypeVariable, ResolvedTypeReference>
    val reportings: Set<Reporting>

    fun plus(variable: TypeVariable, binding: ResolvedTypeReference, assignmentLocation: SourceLocation): TypeUnification
    fun plusReporting(reporting: Reporting): TypeUnification

    fun doTreatingNonUnifiableAsOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(ValueNotAssignableAsArgumentOutOfBounds(this, parameter, argument), action)
    }

    fun doWithIgnoringReportings(action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(IgnoreReportingsUnification(this), action)
    }

    fun getErrorsNotIn(previous: TypeUnification): Sequence<Reporting> {
        return previous.reportings.asSequence()
            .filter { it.level >= Reporting.Level.ERROR }
            .filter { it !in previous.reportings }
    }

    companion object {
        val EMPTY: TypeUnification = DefaultTypeUnification.EMPTY

        /**
         * For a type reference or function call, builds a [TypeUnification] that contains the explicit type arguments. E.g.:
         *
         *     struct X<E, T> {}
         *
         *     val foo: X<Int, Boolean>
         *
         * Then you would call `fromExplicit(<params of base type X>, <int ant boolean type args>, ...)`
         * and the return value would be `[E = Int, T = Boolean] Errors: 0`
         *
         * @param argumentsLocation Location of where the type arguments are being supplied. Used as a fallback
         * for [Reporting]s if there are no type arguments and [allowZeroTypeArguments] is false
         * @param allowZeroTypeArguments Whether 0 type arguments is valid even if [typeParameters] is non-empty.
         * This is the case for function invocations, but type references always need to specify all type args.
         */
        fun fromExplicit(
            typeParameters: List<BoundTypeParameter>,
            arguments: List<BoundTypeArgument>,
            argumentsLocation: SourceLocation,
            allowZeroTypeArguments: Boolean = false,
        ): TypeUnification {
            if (arguments.isEmpty() && allowZeroTypeArguments) {
                return EMPTY
            }

            var unification = EMPTY
            for (i in 0..typeParameters.lastIndex.coerceAtMost(arguments.lastIndex)) {
                val parameter = typeParameters[i]
                val argument = arguments[i]
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        unification = unification.plusReporting(Reporting.typeArgumentVarianceMismatch(parameter, argument))
                    } else {
                        unification = unification.plusReporting(Reporting.typeArgumentVarianceSuperfluous(argument))
                    }
                }

                val nextUnification = unification.doTreatingNonUnifiableAsOutOfBounds(parameter, argument) { subUnification ->
                    parameter.bound.unify(argument, argument.sourceLocation ?: SourceLocation.UNKNOWN, subUnification)
                }
                val hadErrors = nextUnification.getErrorsNotIn(unification).any()
                unification = nextUnification.plus(TypeVariable(parameter), if (!hadErrors) argument else parameter.bound, argument.sourceLocation ?: SourceLocation.UNKNOWN)
            }

            for (i in arguments.size..typeParameters.lastIndex) {
                unification = unification.plusReporting(
                    Reporting.missingTypeArgument(typeParameters[i], arguments.lastOrNull()?.sourceLocation ?: argumentsLocation)
                )
            }
            if (arguments.size > typeParameters.size) {
                unification = unification.plusReporting(
                    Reporting.superfluousTypeArguments(
                        typeParameters.size,
                        arguments[typeParameters.size],
                    )
                )
            }

            return unification
        }
    }
}

private class DefaultTypeUnification private constructor(
    override val bindings: Map<TypeVariable, ResolvedTypeReference>,
    override val reportings: Set<Reporting>,
) : TypeUnification {
    override fun plusReporting(reporting: Reporting): TypeUnification {
        return DefaultTypeUnification(bindings, reportings + setOf(reporting))
    }

    override fun plus(variable: TypeVariable, binding: ResolvedTypeReference, assignmentLocation: SourceLocation): TypeUnification {
        val previousBinding = bindings[variable]
        if (previousBinding is BoundTypeArgument) {
            // type has been fixed explicitly -> no rebinding
            return this
        }

        val newBinding = when {
            binding is BoundTypeArgument -> binding
            else -> previousBinding?.closestCommonSupertypeWith(binding) ?: binding
        }

        return variable.parameter.bound.unify(
            newBinding,
            assignmentLocation,
            DefaultTypeUnification(bindings.plus(variable to newBinding), reportings),
        )
    }

    override fun toString(): String {
        val bindingsStr = bindings.entries.joinToString(
            prefix = "[",
            transform = { (key, value) -> "$key = $value" },
            separator = ", ",
            postfix = "]",
        )
        val nErrors = reportings.count { it.level >= Reporting.Level.ERROR }

        return "$bindingsStr Errors:$nErrors"
    }

    companion object {
        val EMPTY = DefaultTypeUnification(emptyMap(), emptySet())
    }
}

private abstract class DecoratingTypeUnification<Self : DecoratingTypeUnification<Self>> : TypeUnification {
    abstract val undecorated: TypeUnification

    abstract override fun plus(variable: TypeVariable, binding: ResolvedTypeReference, assignmentLocation: SourceLocation): Self

    companion object {
        inline fun <reified T : DecoratingTypeUnification<*>> doWithDecorated(modified: T, action: (TypeUnification) -> TypeUnification): TypeUnification {
            val result = action(modified)
            return (result as T).undecorated
        }
    }
}

private class IgnoreReportingsUnification(
    override val undecorated: TypeUnification,
) : DecoratingTypeUnification<IgnoreReportingsUnification>() {
    override val bindings get() = undecorated.bindings
    override val reportings: Set<Reporting> get() = undecorated.reportings

    override fun plus(variable: TypeVariable, binding: ResolvedTypeReference, assignmentLocation: SourceLocation): IgnoreReportingsUnification {
        return IgnoreReportingsUnification(undecorated.plus(variable, binding, assignmentLocation))
    }

    override fun plusReporting(reporting: Reporting): TypeUnification {
        return this
    }
}

private class ValueNotAssignableAsArgumentOutOfBounds(
    override val undecorated: TypeUnification,
    private val parameter: BoundTypeParameter,
    private val argument: BoundTypeArgument,
) : DecoratingTypeUnification<ValueNotAssignableAsArgumentOutOfBounds>() {
    override val bindings get() = undecorated.bindings
    override val reportings get() = undecorated.reportings

    override fun plusReporting(reporting: Reporting): TypeUnification {
        val reportingToAdd = if (reporting !is ValueNotAssignableReporting) reporting else {
            Reporting.typeArgumentOutOfBounds(parameter, argument, reporting.reason)
        }

        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusReporting(reportingToAdd), parameter, argument)
    }

    override fun plus(variable: TypeVariable, binding: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plus(variable, binding, assignmentLocation), parameter, argument)
    }
}