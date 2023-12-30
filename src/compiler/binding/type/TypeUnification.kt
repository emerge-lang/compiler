package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import java.util.IdentityHashMap

class TypeUnification private constructor (
    private val _left: IdentityHashMap<String, ResolvedTypeReference>,
    private val _right: IdentityHashMap<String, ResolvedTypeReference>,
    private var _reportings: Set<Reporting>,
) {
    val left: Map<String, ResolvedTypeReference> = _left
    val right: Map<String, ResolvedTypeReference> = _right
    val reportings: Collection<Reporting> = _reportings

    fun plusLeft(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left.clone() as IdentityHashMap<String, ResolvedTypeReference>,
            _right, // doesn't get modified here,
            _reportings,
        )
        bindInPlace(clone._left, param, binding)
        return clone
    }

    fun plusRight(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left, // doesn't get modified here
            _right.clone() as IdentityHashMap<String, ResolvedTypeReference>,
            _reportings,
        )
        bindInPlace(clone._right, param, binding)
        return clone
    }

    fun plusReporting(reporting: Reporting): TypeUnification {
        return TypeUnification(_left, _right, _reportings + listOf(reporting))
    }

    /**
     * TODO: docs
     */
    fun mirrored(): TypeUnification {
        return TypeUnification(_right, _left, _reportings)
    }

    fun getErrorsNotIn(previous: TypeUnification): Sequence<Reporting> {
        return previous.reportings.asSequence()
            .filter { it.level >= Reporting.Level.ERROR }
            .filter { it !in previous._reportings }
    }

    override fun toString(): String {
        val bindingsStr = if (left.isEmpty() && right.isEmpty()) "EMPTY" else {
            fun sideToString(side: Map<String, ResolvedTypeReference>) = side.entries.joinToString(
                prefix = "[",
                transform = { (name, value) -> "$name = $value" },
                separator = ", ",
                postfix = "]",
            )

            "Left:${sideToString(left)} Right:${sideToString(right)}"
        }

        val nErrors = _reportings.count { it.level >= Reporting.Level.ERROR }
        return "$bindingsStr Errors:$nErrors"
    }

    companion object {
        val EMPTY = TypeUnification(IdentityHashMap(), IdentityHashMap(), emptySet())

        fun fromRightExplicit(typeParameters: List<BoundTypeParameter>, arguments: List<BoundTypeArgument>): TypeUnification {
            return fromLeftExplicit(typeParameters, arguments).mirrored()
        }

        fun fromLeftExplicit(
            typeParameters: List<BoundTypeParameter>,
            arguments: List<BoundTypeArgument>,
        ): TypeUnification {
            if (arguments.isEmpty()) {
                return EMPTY
            }

            var unification = EMPTY
            val reportings = mutableSetOf<Reporting>()
            for (i in 0..typeParameters.lastIndex.coerceAtMost(arguments.lastIndex)) {
                val parameter = typeParameters[i]
                val argument = arguments[i]
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        reportings.add(Reporting.typeArgumentVarianceMismatch(parameter, argument))
                    } else {
                        reportings.add(Reporting.typeArgumentVarianceSuperfluous(argument))
                    }
                }

                val variance = argument.variance.takeUnless { it == TypeVariance.UNSPECIFIED } ?: parameter.variance
                when(variance) {
                    TypeVariance.UNSPECIFIED,
                    TypeVariance.OUT -> {
                        // this collects type mismatch errors
                        val nextUnification = parameter.bound.unify(argument, argument.sourceLocation ?: SourceLocation.UNKNOWN, unification)
                        val hadErrors = nextUnification.getErrorsNotIn(unification).any()
                        unification = nextUnification.plusLeft(parameter.name, if (!hadErrors) argument else parameter.bound)
                    }
                    TypeVariance.IN -> {
                        unification = argument.unify(parameter.bound, argument.sourceLocation ?: SourceLocation.UNKNOWN, unification.mirrored())
                            .mirrored()
                    }
                }
            }

            for (i in arguments.size..typeParameters.lastIndex) {
                reportings.add(Reporting.missingTypeArgument(typeParameters[i], arguments.last()))
            }
            if (arguments.size > typeParameters.size) {
                reportings.add(Reporting.superfluousTypeArguments(
                    typeParameters.size,
                    arguments[typeParameters.size],
                ))
            }

            return unification
        }

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