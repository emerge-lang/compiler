package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting
import java.util.IdentityHashMap

/* TODO: optimization potential
 * Have a custom collection class that optimized the get-a-copy-plus-one-element use-case
 * Set-properties are probably not needed because we can track changes there explicitly
 * and answer the question "Did this unification produce any errors?" without the set-contains
 * operation done now
 */

abstract class TypeUnification {
    abstract val left: Map<String, ResolvedTypeReference>
    abstract val right: Map<String, ResolvedTypeReference>
    abstract val reportings: Set<Reporting>
    abstract fun plusLeft(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification

    abstract fun plusRight(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification

    abstract fun plusReporting(reporting: Reporting): TypeUnification

    fun doWithMirrored(action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(MirroredTypeUnification(this), action)
    }

    fun doWithIgnoringReportings(action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(IgnoreReportingsUnification(this), action)
    }

    fun doTreatingNonUnifiableAsOutOfBounds(parameter: BoundTypeParameter, argument: BoundTypeArgument, action: (TypeUnification) -> TypeUnification): TypeUnification {
        return DecoratingTypeUnification.doWithDecorated(ValueNotAssignableAsArgumentOutOfBounds(this, parameter, argument), action)
    }

    fun getErrorsNotIn(previous: TypeUnification): Sequence<Reporting> {
        return previous.reportings.asSequence()
            .filter { it.level >= Reporting.Level.ERROR }
            .filter { it !in previous.reportings }
    }

    companion object {
        val EMPTY: TypeUnification = DefaultTypeUnification.EMPTY

        /**
         * see [fromLeftExplicit], except that the instantiations will go into [TypeUnification.right] instead of
         * [left].
         */
        fun fromRightExplicit(
            typeParameters: List<BoundTypeParameter>,
            arguments: List<BoundTypeArgument>,
            argumentsLocation: SourceLocation,
            allowZeroTypeArguments: Boolean = false,
        ): TypeUnification {
            return MirroredTypeUnification(fromLeftExplicit(typeParameters, arguments, argumentsLocation, allowZeroTypeArguments))
        }

        /**
         * For a type reference or function call, builds a [TypeUnification] that contains the explicit type arguments
         * given in [TypeUnification.left]. E.g.:
         *
         *     struct X<E, T> {}
         *
         *     val foo: X<Int, Boolean>
         *
         * Then you would call `fromLeftExplicit(<params of base type X>, <int ant boolean type args>, ...)`
         * and the return value would be `Left:[E = Int, T = Boolean] Right:[] Errors: 0`
         *
         * @param argumentsLocation Location of where the type arguments are being supplied. Used as a fallback
         * for reportings if there are no type arguments and [allowZeroTypeArguments] is false
         * @param allowZeroTypeArguments Whether 0 type arguments is valid even if [ŧypeParameters] is non-empty.
         * This is the case for function invocations, but type references always need to specify all type args.
         */
        fun fromLeftExplicit(
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
                unification = nextUnification.plusLeft(parameter.name, if (!hadErrors) argument else parameter.bound)
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

class DefaultTypeUnification private constructor(
    private val _left: IdentityHashMap<String, ResolvedTypeReference>,
    private val _right: IdentityHashMap<String, ResolvedTypeReference>,
    private val _reportings: Set<Reporting>,
) : TypeUnification() {
    override val left: Map<String, ResolvedTypeReference> = _left
    override val right: Map<String, ResolvedTypeReference> = _right
    override val reportings: Set<Reporting> = _reportings

    override fun plusLeft(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = DefaultTypeUnification(
            _left.clone() as IdentityHashMap<String, ResolvedTypeReference>,
            _right, // doesn't get modified here,
            _reportings,
        )
        bindInPlace(clone._left, param, binding)
        return clone
    }

    override fun plusRight(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = DefaultTypeUnification(
            _left, // doesn't get modified here
            _right.clone() as IdentityHashMap<String, ResolvedTypeReference>,
            _reportings,
        )
        bindInPlace(clone._right, param, binding)
        return clone
    }

    override fun plusReporting(reporting: Reporting): TypeUnification {
        return DefaultTypeUnification(
            _left,
            _right,
            _reportings + setOf(reporting),
        )
    }

    override fun toString(): String {
        return toString(_left, _right, _reportings)
    }

    companion object {
        val EMPTY = DefaultTypeUnification(IdentityHashMap(), IdentityHashMap(), emptySet())

        private fun bindInPlace(
            map: IdentityHashMap<String, ResolvedTypeReference>,
            param: String,
            binding: ResolvedTypeReference,
        ) {
            map.compute(param) { _, previousBinding ->
                when {
                    previousBinding is BoundTypeArgument -> previousBinding
                    binding is BoundTypeArgument -> binding
                    else -> previousBinding?.closestCommonSupertypeWith(binding) ?: binding
                }
            }
        }
    }
}

private abstract class DecoratingTypeUnification<Self : DecoratingTypeUnification<Self>> : TypeUnification() {
    abstract val undecorated: TypeUnification

    abstract override fun plusLeft(param: String, binding: ResolvedTypeReference): Self

    abstract override fun plusRight(param: String, binding: ResolvedTypeReference): Self

    companion object {
        inline fun <reified T : DecoratingTypeUnification<*>> doWithDecorated(modified: T, action: (TypeUnification) -> TypeUnification): TypeUnification {
            val result = action(modified)
            return (result as T).undecorated
        }
    }
}

private class MirroredTypeUnification(
    override val undecorated: TypeUnification,
) : DecoratingTypeUnification<MirroredTypeUnification>() {
    override val left: Map<String, ResolvedTypeReference> get() = undecorated.right
    override val right: Map<String, ResolvedTypeReference> get() = undecorated.left
    override val reportings: Set<Reporting> get() = undecorated.reportings

    override fun plusLeft(param: String, binding: ResolvedTypeReference): MirroredTypeUnification {
        return MirroredTypeUnification(undecorated.plusRight(param, binding))
    }

    override fun plusRight(param: String, binding: ResolvedTypeReference): MirroredTypeUnification {
        return MirroredTypeUnification(undecorated.plusLeft(param, binding))
    }

    override fun plusReporting(reporting: Reporting): TypeUnification {
        return MirroredTypeUnification(undecorated.plusReporting(reporting))
    }

    override fun toString(): String {
        return toString(undecorated.right, undecorated.left, undecorated.reportings)
    }
}

private class IgnoreReportingsUnification(
    override val undecorated: TypeUnification,
) : DecoratingTypeUnification<IgnoreReportingsUnification>() {
    override val left: Map<String, ResolvedTypeReference> get() = undecorated.left
    override val right: Map<String, ResolvedTypeReference> get() = undecorated.right
    override val reportings: Set<Reporting> get() = undecorated.reportings

    override fun plusLeft(param: String, binding: ResolvedTypeReference): IgnoreReportingsUnification {
        return IgnoreReportingsUnification(undecorated.plusLeft(param, binding))
    }

    override fun plusRight(param: String, binding: ResolvedTypeReference): IgnoreReportingsUnification {
        return IgnoreReportingsUnification(undecorated.plusRight(param, binding))
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
    override val left: Map<String, ResolvedTypeReference> get() = undecorated.left
    override val right: Map<String, ResolvedTypeReference> get() = undecorated.left
    override val reportings: Set<Reporting> get() = undecorated.reportings

    override fun plusReporting(reporting: Reporting): TypeUnification {
        val reportingToAdd = if (reporting !is ValueNotAssignableReporting) reporting else {
            Reporting.typeArgumentOutOfBounds(parameter, argument, reporting.reason)
        }

        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusReporting(reportingToAdd), parameter, argument)
    }

    override fun plusLeft(param: String, binding: ResolvedTypeReference): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusLeft(param, binding), parameter, argument)
    }

    override fun plusRight(param: String, binding: ResolvedTypeReference): ValueNotAssignableAsArgumentOutOfBounds {
        return ValueNotAssignableAsArgumentOutOfBounds(undecorated.plusRight(param, binding), parameter, argument)
    }
}

private fun toString(left: Map<String, ResolvedTypeReference>, right: Map<String, ResolvedTypeReference>, reportings: Collection<Reporting>): String {
    val bindingsStr = if (left.isEmpty() && right.isEmpty()) "EMPTY" else {
        fun sideToString(side: Map<String, ResolvedTypeReference>) = side.entries.joinToString(
            prefix = "[",
            transform = { (name, value) -> "$name = $value" },
            separator = ", ",
            postfix = "]",
        )

        "Left:${sideToString(left)} Right:${sideToString(right)}"
    }

    val nErrors = reportings.count { it.level >= Reporting.Level.ERROR }
    return "$bindingsStr Errors:$nErrors"
}