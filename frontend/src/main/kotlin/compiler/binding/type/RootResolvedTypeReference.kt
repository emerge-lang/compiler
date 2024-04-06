package compiler.binding.type

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.StandardLibraryModule
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundOverloadSet
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * A [TypeReference] where the root type is resolved
 */
class RootResolvedTypeReference private constructor(
    val original: TypeReference?,
    override val isNullable: Boolean,
    private val explicitMutability: TypeMutability?,
    val baseType: BaseType,
    val arguments: List<BoundTypeArgument>,
) : BoundTypeReference {
    override val mutability = if (baseType.isAtomic) TypeMutability.IMMUTABLE else (explicitMutability ?: original?.mutability ?: TypeMutability.READONLY)
    override val simpleName = original?.simpleName ?: baseType.simpleName
    override val sourceLocation = original?.declaringNameToken?.sourceLocation

    override val inherentTypeBindings by lazy {
        TypeUnification.fromExplicit(baseType.typeParameters, arguments, sourceLocation ?: SourceLocation.UNKNOWN)
    }

    constructor(original: TypeReference, baseType: BaseType, parameters: List<BoundTypeArgument>) : this(
        original,
        original.nullability == TypeReference.Nullability.NULLABLE,
        original.mutability,
        baseType,
        parameters,
    )

    override fun withMutability(modifier: TypeMutability?): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
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
            isNullable,
            combinedMutability,
            baseType,
            arguments.map { it.defaultMutabilityTo(combinedMutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
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
            isNullable,
            mutability,
            baseType,
            arguments.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        arguments.forEach { reportings.addAll(it.validate(forUsage.deriveIrrelevant())) }
        reportings.addAll(inherentTypeBindings.reportings)
        reportings.addAll(baseType.validateAccessFrom(forUsage.usageLocation))

        return reportings
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return other is RootResolvedTypeReference && this.baseType == other.baseType
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (other) {
            is UnresolvedType -> other.closestCommonSupertypeWith(this)
            is RootResolvedTypeReference -> {
                val commonSupertype = BaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                check(commonSupertype.typeParameters.isEmpty()) { "Generic supertypes are not implemented, yet." }
                RootResolvedTypeReference(
                    null,
                    this.isNullable || other.isNullable,
                    this.mutability.combinedWith(other.mutability),
                    commonSupertype,
                    emptyList(),
                )
            }
            is GenericTypeReference -> other.closestCommonSupertypeWith(this)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
        }
    }

    override fun findMemberVariable(name: String): BoundClassMemberVariable? = baseType.resolveMemberVariable(name)

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet> {
        return baseType.resolveMemberFunction(name)
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            isNullable,
            explicitMutability,
            baseType,
            arguments.map { it.withTypeVariables(variables) },
        )
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
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
            is GenericTypeReference -> return unify(assigneeType.effectiveBound, assignmentLocation, carry)
            is BoundTypeArgument -> {
                // this branch is PROBABLY only taken when verifying the bound of a type parameter against an argument
                // in this case this is the bound and assigneeType is the argument
                // variance is not important in that scenario because type arguments must be subtypes of the parameters bounds
                return unify(assigneeType.type, assignmentLocation, carry)
            }
            is TypeVariable -> return assigneeType.flippedUnify(this, assignmentLocation, carry)
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            isNullable,
            explicitMutability,
            baseType,
            arguments.map { it.instantiateFreeVariables(context) },
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            isNullable,
            explicitMutability,
            baseType,
            arguments.map { it.instantiateAllParameters(context) },
        )
    }

    private val _string: String by lazy {
        var str = mutability.toString()
        str += " "

        str += when {
            CoreIntrinsicsModule.NAME.containsOrEquals(baseType.fullyQualifiedName) ||
            StandardLibraryModule.NAME.containsOrEquals(baseType.fullyQualifiedName) -> baseType.fullyQualifiedName.last
            else -> baseType.fullyQualifiedName.toString()
        }

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

    override fun toBackendIr(): IrType {
        val raw = IrSimpleTypeImpl(baseType.toBackendIr(), isNullable)
        if (arguments.isEmpty()) {
            return raw
        }

        return IrParameterizedTypeImpl(
            raw,
            baseType.typeParameters.zip(arguments).associate { (param, arg) ->
                param.name to arg.toBackendIrAsTypeArgument()
            }
        )
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

internal class IrSimpleTypeImpl(
    override val baseType: IrBaseType,
    override val isNullable: Boolean,
) : IrSimpleType {
    override fun toString() = "IrSimpleType[${baseType.fqn}]"
}

internal class IrParameterizedTypeImpl(
    override val simpleType: IrSimpleType,
    override val arguments: Map<String, IrParameterizedType.Argument>,
) : IrParameterizedType {
    override fun toString() = "IrParameterizedType[$simpleType" + arguments.entries.joinToString(
        prefix = "<",
        transform = { (name, value) -> "$name = $value" },
        postfix = ">]"
    )
}