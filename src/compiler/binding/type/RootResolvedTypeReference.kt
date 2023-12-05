package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

/**
 * A [TypeReference] where the root type is resolved
 */
class RootResolvedTypeReference private constructor(
    private val original: TypeReference?,
    override val context: CTContext,
    override val isNullable: Boolean,
    private val explicitMutability: TypeMutability?,
    val baseType: BaseType,

    /**
     * Maps the [TypeReference.simpleName] of the [BaseType.parameters] to the resolved value
     */
    val parameters: List<ResolvedTypeReference>,
) : ResolvedTypeReference {
    override val mutability = explicitMutability ?: original?.mutability ?: baseType.impliedMutability ?: TypeMutability.READONLY
    override val simpleName = original?.simpleName ?: baseType.simpleName

    constructor(original: TypeReference, context: CTContext, baseType: BaseType, parameters: List<ResolvedTypeReference>) : this(
        original,
        context,
        original.nullability == TypeReference.Nullability.NULLABLE,
        original.mutability ?: baseType.impliedMutability,
        baseType,
        parameters,
    )

    constructor(context: CTContext, baseType: BaseType, isNullable: Boolean, explicitModifier: TypeMutability?, parameters: List<ResolvedTypeReference>) : this(
        null,
        context,
        isNullable,
        explicitModifier,
        baseType,
        parameters,
    )

    override fun modifiedWith(modifier: TypeMutability): RootResolvedTypeReference {
        // todo: how to handle projected mutability? readonly Array<Foo> == readonly Array<readonly Foo>
        return RootResolvedTypeReference(
            context,
            baseType,
            isNullable,
            modifier,
            parameters.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.combinedWith(it) } ?: this.mutability
        return RootResolvedTypeReference(
            context,
            baseType,
            isNullable,
            combinedMutability,
            parameters.map { it.defaultMutabilityTo(combinedMutability) },
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
            mutability.exceptExclusive,
            parameters.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun validate(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // verify whether the modifier on the reference is compatible with the modifier on the type
        if (original?.mutability != null && baseType.impliedMutability != null) {
            if (!(original.mutability!! isAssignableTo baseType.impliedMutability!!)) {
                val origMod = original.mutability?.toString()?.lowercase()
                val baseMod = baseType.impliedMutability?.toString()?.lowercase()

                reportings.add(
                    Reporting.modifierError(
                        "Cannot reference ${baseType.fullyQualifiedName} as $origMod; " +
                                "modifier $origMod is not assignable to the implied modifier $baseMod of ${baseType.simpleName}",
                        original.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN
                    )
                )
            }
        }

        return reportings
    }

    override fun evaluateAssignabilityTo(other: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting? {
        if (other is UnresolvedType) {
            return evaluateAssignabilityTo(other.standInType, assignmentLocation)
        }

        if (other !is RootResolvedTypeReference) {
            TODO("implement for ${other::class.simpleName}")
        }

        // this must be a subtype of other
        if (!(this.baseType isSubtypeOf other.baseType)) {
            return Reporting.valueNotAssignable(other, this, "${this.baseType.simpleName} is not a subtype of ${other.baseType.simpleName}", assignmentLocation)
        }

        // the modifiers must be compatible
        if (!(mutability isAssignableTo other.mutability)) {
            return Reporting.valueNotAssignable(other, this, "cannot assign a ${mutability.name.lowercase()} value to a ${other.mutability.name.lowercase()} reference", assignmentLocation)
        }

        // void-safety:
        // other  this  isCompatible
        // T      T     true
        // T?     T     true
        // T      T?    false
        // T?     T?    true
        // TODO: how to resolve nullability on references with bounds? How about class/struct-level parameters
        // in methods (further limited / specified on the method level)?
        if (this.isNullable && !other.isNullable) {
            return Reporting.valueNotAssignable(other, this, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
        }

        check(parameters.size == other.parameters.size)
        parameters.asSequence()
            .zip(other.parameters.asSequence()) { thisParam, otherParam ->
                thisParam.evaluateAssignabilityTo(otherParam, this.original?.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN)
            }
            .filterNotNull()
            .firstOrNull()
            ?.let { return it }

        // seems all fine
        return null
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? =
        when (other) {
            is RootResolvedTypeReference -> if (this isAssignableTo other) {
                this.baseType.hierarchicalDistanceTo(other.baseType)
            } else null
            else -> null
        }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        return when (other) {
            is UnresolvedType -> other.closestCommonSupertypeWith(this)
            is RootResolvedTypeReference -> {
                val commonSupertype = BaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                check(commonSupertype.parameters.isEmpty()) { "Generic supertypes are not implemented, yet." }
                RootResolvedTypeReference(
                    context,
                    commonSupertype,
                    this.isNullable || other.isNullable,
                    this.mutability.combinedWith(other.mutability),
                    emptyList(),
                )
            }
        }
    }

    private lateinit var _string: String
    override fun toString(): String {
        if (!this::_string.isInitialized) {
            var str = mutability.name.lowercase()
            str += " "

            str += baseType.fullyQualifiedName.removePrefix(BuiltinType.DEFAULT_MODULE_NAME_STRING + ".")

            // TODO: parameters

            val nullability = original?.nullability
                ?: if (isNullable) TypeReference.Nullability.NULLABLE else TypeReference.Nullability.UNSPECIFIED

            when (nullability) {
                TypeReference.Nullability.NULLABLE -> str += '?'
                TypeReference.Nullability.NOT_NULLABLE -> str += '!'
                TypeReference.Nullability.UNSPECIFIED -> {}
            }

            this._string = str
        }

        return this._string
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as RootResolvedTypeReference

        if (isNullable != other.isNullable) return false
        if (baseType != other.baseType) return false
        if (parameters != other.parameters) return false
        if (mutability != other.mutability) return false

        return true
    }

    override fun hashCode(): Int {
        var result = isNullable.hashCode()
        result = 31 * result + baseType.hashCode()
        result = 31 * result + parameters.hashCode()
        result = 31 * result + mutability.hashCode()
        return result
    }
}