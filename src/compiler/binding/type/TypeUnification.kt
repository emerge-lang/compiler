package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import java.util.IdentityHashMap

class TypeUnification private constructor (
    private val _left: IdentityHashMap<String, ResolvedTypeReference>,
    private val _right: IdentityHashMap<String, ResolvedTypeReference>,
    private val _reportings: Set<Reporting>,
    private val saveReportings: Boolean,
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
            saveReportings,
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
            saveReportings,
        )
        bindInPlace(clone._right, param, binding)
        return clone
    }

    fun plusReporting(reporting: Reporting): TypeUnification {
        if (!saveReportings) {
            return this
        }

        return TypeUnification(_left, _right, _reportings + listOf(reporting), true)
    }

    /**
     * TODO: docs
     */
    fun mirrored(): TypeUnification {
        return TypeUnification(_right, _left, _reportings, saveReportings)
    }

    /**
     * @return a copy of this, except that any calls to [plusReporting] on the returned [TypeUnification] will be ignored.
     */
    fun ignoringReportings(): TypeUnification {
        check(saveReportings) {
            throw InternalCompilerError("Cannot nest ignoringReportings unifications, this one already ignores")
        }
        return TypeUnification(_left, _right, _reportings, false)
    }

    /**
     * @return a copy of this, making sure that reportings given to [plusReporting] will be reflected in [reportings],
     * effectively reversing [saveReportings].
     */
    fun savingReportings(): TypeUnification {
        check(!saveReportings) {
            throw InternalCompilerError("Cannot nest savingReportings unifications, this one already saves")
        }
        return TypeUnification(_left, _right, _reportings, true)
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
        val EMPTY = TypeUnification(IdentityHashMap(), IdentityHashMap(), emptySet(), true)

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