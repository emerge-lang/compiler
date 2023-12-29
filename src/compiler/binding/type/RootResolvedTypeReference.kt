package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

/**
 * A [TypeReference] where the root type is resolved
 */
class RootResolvedTypeReference private constructor(
    val original: TypeReference?,
    override val context: CTContext,
    override val isNullable: Boolean,
    private val explicitMutability: TypeMutability?,
    val baseType: BaseType,
    val arguments: List<BoundTypeArgument>,
) : ResolvedTypeReference {
    override val mutability = if (baseType.isAtomic) TypeMutability.IMMUTABLE else (explicitMutability ?: original?.mutability ?: TypeMutability.READONLY)
    override val simpleName = original?.simpleName ?: baseType.simpleName
    override val sourceLocation = original?.declaringNameToken?.sourceLocation

    constructor(original: TypeReference, context: CTContext, baseType: BaseType, parameters: List<BoundTypeArgument>) : this(
        original,
        context,
        original.nullability == TypeReference.Nullability.NULLABLE,
        original.mutability,
        baseType,
        parameters,
    )

    constructor(context: CTContext, baseType: BaseType, isNullable: Boolean, explicitModifier: TypeMutability?, parameters: List<BoundTypeArgument>) : this(
        null,
        context,
        isNullable,
        explicitModifier,
        baseType,
        parameters,
    )

    override fun withMutability(modifier: TypeMutability?): RootResolvedTypeReference {
        // todo: how to handle projected mutability? readonly Array<Foo> == readonly Array<readonly Foo>
        return RootResolvedTypeReference(
            context,
            baseType,
            isNullable,
            if (baseType.isAtomic) TypeMutability.IMMUTABLE else modifier,
            arguments.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): RootResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.combinedWith(it) } ?: this.mutability
        return RootResolvedTypeReference(
            context,
            baseType,
            isNullable,
            combinedMutability,
            arguments.map { it.defaultMutabilityTo(combinedMutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            context,
            when(nullability) {
                TypeReference.Nullability.NULLABLE -> true
                TypeReference.Nullability.NOT_NULLABLE -> false
                TypeReference.Nullability.UNSPECIFIED -> isNullable
            },
            explicitMutability,
            baseType,
            arguments
        )
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): RootResolvedTypeReference {
        if (mutability == null || original?.mutability != null || explicitMutability != null) {
            return this
        }

        return RootResolvedTypeReference(
            context,
            baseType,
            isNullable,
            mutability,
            arguments.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        arguments.forEach { reportings.addAll(it.validate(TypeUseSite.Irrelevant)) }
        if (arguments.size == baseType.typeParameters.size) {
            arguments.zip(baseType.typeParameters).forEach { (argument, parameter) ->
                if (argument.variance != TypeVariance.UNSPECIFIED && parameter.variance != TypeVariance.UNSPECIFIED) {
                    if (argument.variance != parameter.variance) {
                        reportings.add(Reporting.typeArgumentVarianceMismatch(parameter, argument))
                    } else {
                        reportings.add(Reporting.typeArgumentVarianceSuperfluous(argument))
                    }
                }

                val variance = argument.variance.takeUnless { it == TypeVariance.UNSPECIFIED } ?: parameter.variance
                val boundError = when(variance) {
                    TypeVariance.UNSPECIFIED,
                    TypeVariance.OUT -> argument.evaluateAssignabilityTo(parameter.bound, argument.sourceLocation ?: SourceLocation.UNKNOWN)?.let {
                        Reporting.typeArgumentOutOfBounds(parameter, argument, it.reason)
                    }
                    TypeVariance.IN -> parameter.bound.evaluateAssignabilityTo(argument, argument.sourceLocation ?: SourceLocation.UNKNOWN)?.let {
                        Reporting.typeArgumentOutOfBounds(parameter, argument, "${argument.type} is not a supertype of ${parameter.bound}")
                    }
                }
                boundError?.let(reportings::add)
            }
        } else {
            reportings.add(Reporting.typeArgumentCountMismatch(this))
        }

        return reportings
    }

    override fun evaluateAssignabilityTo(other: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting? {
        when(other) {
            is UnresolvedType -> return evaluateAssignabilityTo(other.standInType, assignmentLocation)
            is GenericTypeReference -> return when (other.variance) {
                TypeVariance.UNSPECIFIED,
                TypeVariance.IN -> evaluateAssignabilityTo(other.effectiveBound, assignmentLocation)
                TypeVariance.OUT -> Reporting.valueNotAssignable(other, this, "Cannot assign to an out-variant reference", assignmentLocation)
            }
            is RootResolvedTypeReference -> {
                // this must be a subtype of other
                if (!(this.baseType isSubtypeOf other.baseType)) {
                    return Reporting.valueNotAssignable(other, this, "${this.baseType.simpleName} is not a subtype of ${other.baseType.simpleName}", assignmentLocation)
                }

                // the modifiers must be compatible
                if (!(mutability isAssignableTo other.mutability)) {
                    return Reporting.valueNotAssignable(other, this, "cannot assign a $mutability value to a ${other.mutability} reference", assignmentLocation)
                }

                // in methods (further limited / specified on the method level)?
                if (this.isNullable && !other.isNullable) {
                    return Reporting.valueNotAssignable(other, this, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
                }

                check(arguments.size == other.arguments.size)
                arguments.asSequence()
                    .zip(other.arguments.asSequence()) { thisParam, otherParam ->
                        thisParam.evaluateAssignabilityTo(otherParam, assignmentLocation)
                    }
                    .filterNotNull()
                    .firstOrNull()
                    ?.let { return it }

                // seems all fine
                return null
            }
            is BoundTypeArgument -> return when (other.variance) {
                TypeVariance.UNSPECIFIED,
                TypeVariance.IN -> evaluateAssignabilityTo(other.type, assignmentLocation)
                TypeVariance.OUT -> Reporting.valueNotAssignable(other, this, "cannot assign to an out-variant reference", assignmentLocation)
            }
        }
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return other is RootResolvedTypeReference && this.baseType == other.baseType
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        return when (other) {
            is UnresolvedType -> other.closestCommonSupertypeWith(this)
            is RootResolvedTypeReference -> {
                val commonSupertype = BaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                check(commonSupertype.typeParameters.isEmpty()) { "Generic supertypes are not implemented, yet." }
                RootResolvedTypeReference(
                    context,
                    commonSupertype,
                    this.isNullable || other.isNullable,
                    this.mutability.combinedWith(other.mutability),
                    emptyList(),
                )
            }
            is GenericTypeReference -> other.closestCommonSupertypeWith(this)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
        }
    }

    override fun findMemberVariable(name: String): ObjectMember? = baseType.resolveMemberVariable(name)

    override val inherentTypeBindings by lazy {
        TypeUnification.fromInherent(this)
    }

    override fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification {
        when (other) {
            is RootResolvedTypeReference -> {
                if (other.baseType == this.baseType) {
                    return arguments.asSequence()
                        .zip(other.arguments.asSequence())
                        .fold(carry) { innerCarry, (left, right) -> left.unify(right, innerCarry) }
                } else throw TypesNotUnifiableException(this, other, "Different concrete types")
            }
            is UnresolvedType -> return unify(other.standInType, carry)
            is GenericTypeReference -> {
                // TODO: handle modifier complications?
                return carry.plusRight(other.simpleName, this)
            }
            is BoundTypeArgument -> {
                if (other.variance != TypeVariance.UNSPECIFIED) {
                    throw TypesNotUnifiableException(this, other, "Cannot unify concrete type with variant-type")
                }

                return unify(other.type, carry)
            }
        }
    }

    override fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, ResolvedTypeReference>): ResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            this.context,
            isNullable,
            explicitMutability,
            baseType,
            arguments.map { it.contextualize(context, side) },
        )
    }

    private val _string: String by lazy {
        var str = mutability.toString()
        str += " "

        str += baseType.fullyQualifiedName.removePrefix(BuiltinType.DEFAULT_MODULE_NAME_STRING + ".")

        if (arguments.isNotEmpty()) {
            str += arguments.joinToString(
                prefix = "<",
                separator = ", ",
                postfix = ">",
            )
        }

        if (isNullable) {
            str += '?'
        }

        str
    }
    override fun toString(): String = _string

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as RootResolvedTypeReference

        if (isNullable != other.isNullable) return false
        if (baseType != other.baseType) return false
        if (arguments != other.arguments) return false
        if (mutability != other.mutability) return false

        return true
    }

    override fun hashCode(): Int {
        var result = isNullable.hashCode()
        result = 31 * result + baseType.hashCode()
        result = 31 * result + arguments.hashCode()
        result = 31 * result + mutability.hashCode()
        return result
    }
}