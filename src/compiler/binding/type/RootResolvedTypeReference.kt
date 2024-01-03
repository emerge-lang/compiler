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

    override fun withMutability(modifier: TypeMutability?): RootResolvedTypeReference {
        // todo: how to handle projected mutability? readonly Array<Foo> == readonly Array<readonly Foo>
        return RootResolvedTypeReference(
            original,
            context,
            isNullable,
            if (baseType.isAtomic) TypeMutability.IMMUTABLE else modifier,
            baseType,
            arguments.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): RootResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.combinedWith(it) } ?: this.mutability
        return RootResolvedTypeReference(
            original,
            context,
            isNullable,
            combinedMutability,
            baseType,
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
            original,
            context,
            isNullable,
            mutability,
            baseType,
            arguments.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        arguments.forEach { reportings.addAll(it.validate(TypeUseSite.Irrelevant)) }
        reportings.addAll(inherentTypeBindings.reportings)

        return reportings
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
                    null,
                    context,
                    this.isNullable || other.isNullable,
                    this.mutability.combinedWith(other.mutability),
                    commonSupertype,
                    emptyList(),
                )
            }
            is GenericTypeReference -> other.closestCommonSupertypeWith(this)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
        }
    }

    override fun findMemberVariable(name: String): ObjectMember? = baseType.resolveMemberVariable(name)

    override val inherentTypeBindings by lazy {
        TypeUnification.fromLeftExplicit(baseType.typeParameters, arguments, sourceLocation ?: SourceLocation.UNKNOWN)
    }

    override fun unify(assigneeType: ResolvedTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        when (assigneeType) {
            is RootResolvedTypeReference -> {
                // this must be a subtype of other
                if (!(assigneeType.baseType isSubtypeOf this.baseType)) {
                    return carry.plusReporting(
                        Reporting.valueNotAssignable(this, assigneeType, "${assigneeType.baseType.simpleName} is not a subtype of ${this.baseType.simpleName}", assignmentLocation)
                    )
                }

                // the modifiers must be compatible
                if (!(assigneeType.mutability isAssignableTo this.mutability)) {
                    return carry.plusReporting(
                        Reporting.valueNotAssignable(this, assigneeType, "cannot assign a ${assigneeType.mutability} value to a ${this.mutability} reference", assignmentLocation)
                    )
                }

                if (!this.isNullable && assigneeType.isNullable) {
                    return carry.plusReporting(
                        Reporting.valueNotAssignable(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
                    )
                }

                return this.arguments
                    .zip(assigneeType.arguments)
                    .fold(carry) { innerCarry, (targetArg, sourceArg) ->
                        targetArg.unify(sourceArg, assignmentLocation, innerCarry)
                    }
            }
            is UnresolvedType -> return unify(assigneeType.standInType, assignmentLocation, carry)
            is GenericTypeReference -> {
                carry.right[assigneeType.simpleName]?.let { resolved ->
                    return this.unify(resolved, assignmentLocation, carry)
                }

                val boundError = this.evaluateAssignabilityTo(assigneeType.effectiveBound, assignmentLocation)
                if (boundError == null) {
                    return carry.plusRight(assigneeType.simpleName, this)
                } else {
                    return carry.plusReporting(boundError)
                }
            }
            is BoundTypeArgument -> {
                // this branch is PROBABLY only taken when verifying the bound of a type parameter against an argument
                // in this case this is the bound and assigneeType is the argument
                // variance is not important in that scenario because type arguments must be subtypes of the parameters bounds
                return unify(assigneeType.type, assignmentLocation, carry)
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