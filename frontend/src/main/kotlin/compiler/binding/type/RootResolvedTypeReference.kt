package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.independentToString
import io.github.tmarsteel.emerge.common.EmergeConstants

/**
 * A [TypeReference] where the root type is resolved
 */
class RootResolvedTypeReference private constructor(
    val original: TypeReference?,
    private val explicitMutability: TypeMutability?,
    val baseType: BoundBaseType,
    val arguments: List<BoundTypeArgument>?,
) : BoundTypeReference {
    override val isNullable = false
    override val mutability = if (baseType.isCoreScalar) TypeMutability.IMMUTABLE else (explicitMutability ?: original?.mutability ?: TypeMutability.READONLY)
    override val simpleName = original?.simpleName ?: baseType.simpleName
    override val span = original?.declaringNameToken?.span

    override val inherentTypeBindings by lazy {
        TypeUnification.fromExplicit(baseType.typeParameters ?: emptyList(), arguments, span ?: Span.UNKNOWN)
    }

    constructor(original: TypeReference, baseType: BoundBaseType, parameters: List<BoundTypeArgument>?) : this(
        original,
        original.mutability,
        baseType,
        parameters,
    )

    override fun withMutability(modifier: TypeMutability?): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            if (baseType.isCoreScalar) TypeMutability.IMMUTABLE else modifier,
            baseType,
            arguments?.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): RootResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.combinedWith(it) } ?: this.mutability
        return RootResolvedTypeReference(
            original,
            combinedMutability,
            baseType,
            arguments?.map { it.defaultMutabilityTo(combinedMutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        if (nullability == TypeReference.Nullability.NULLABLE) {
            return NullableTypeReference(this)
        }
        return this
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): RootResolvedTypeReference {
        if (mutability == null || original?.mutability != null || explicitMutability != null) {
            return this
        }

        return RootResolvedTypeReference(
            original,
            mutability,
            baseType,
            arguments?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {

        arguments?.forEach { reportings.addAll(it.validate(forUsage.deriveIrrelevant())) }
        reportings.addAll(inherentTypeBindings.reportings)
        reportings.addAll(baseType.validateAccessFrom(forUsage.usageLocation))
        forUsage.exposedBy?.let { exposer ->
            if (exposer.visibility.isPossiblyBroaderThan(baseType.visibility)) {
                diagnosis.add(Reporting.hiddenTypeExposed(baseType, exposer, span ?: Span.UNKNOWN))
            }
        }

        return reportings
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return when (other) {
            is RootResolvedTypeReference -> this.baseType == other.baseType
            is NullableTypeReference -> hasSameBaseTypeAs(other.nested)
            else -> false
        }
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (other) {
            is UnresolvedType -> other.closestCommonSupertypeWith(this)
            is NullableTypeReference -> NullableTypeReference(closestCommonSupertypeWith(other.nested))
            is RootResolvedTypeReference -> {
                // TODO: these three special cases can be removed once generic supertypes are implemented
                if (this.baseType == this.baseType.context.swCtx.nothing) {
                    return other
                }
                if (other.baseType == other.baseType.context.swCtx.nothing) {
                    return this
                }
                if (this == other) {
                    return this
                }
                val commonSupertype = BoundBaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                check(commonSupertype.typeParameters.isNullOrEmpty()) { "Generic supertypes are not implemented, yet." }
                RootResolvedTypeReference(
                    null,
                    this.mutability.combinedWith(other.mutability),
                    commonSupertype,
                    null,
                )
            }
            is GenericTypeReference -> other.closestCommonSupertypeWith(this)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
        }
    }

    override fun findMemberVariable(name: String): BoundBaseTypeMemberVariable? = baseType.resolveMemberVariable(name)

    val memberFunctions: Collection<BoundOverloadSet<BoundMemberFunction>> get() = baseType.memberFunctions

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return baseType.resolveMemberFunction(name)
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            explicitMutability,
            baseType,
            arguments?.map { it.withTypeVariables(variables) },
        )
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
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

                // TODO: this special case can be removed once generic supertypes are implemented
                if (assigneeType.baseType == assigneeType.baseType.context.swCtx.nothing) {
                    return carry
                }

                check(this.baseType.typeParameters.isNullOrEmpty() || this.baseType == assigneeType.baseType) {
                    "generic inheritance not implemented yet"
                }

                val selfArgs = this.arguments ?: emptyList()
                val assigneeArgs = assigneeType.arguments ?: emptyList()
                return selfArgs
                    .zip(assigneeArgs)
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
            is NullableTypeReference -> return carry.plusReporting(
                Reporting.valueNotAssignable(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
            )
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateFreeVariables(context) },
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            original,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateAllParameters(context) },
        )
    }

    private val _string: String by lazy {
        var str = mutability.toString()
        str += " "

        str += when {
            baseType.canonicalName.packageName == EmergeConstants.CORE_MODULE_NAME ||
            baseType.canonicalName.packageName == EmergeConstants.STD_MODULE_NAME -> baseType.simpleName
            else -> baseType.canonicalName.toString()
        }

        if (arguments != null) {
            str += arguments.joinToString(
                prefix = "<",
                separator = ", ",
                postfix = ">",
            )
        }

        str
    }

    override fun toBackendIr(): IrType {
        val raw = IrSimpleTypeImpl(baseType.toBackendIr(), this.mutability.toBackendIr(), false)
        if (arguments.isNullOrEmpty() || baseType.typeParameters.isNullOrEmpty()) {
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

        if (baseType != other.baseType) return false
        if (arguments != other.arguments) return false
        if (mutability != other.mutability) return false

        return true
    }

    override fun hashCode(): Int {
        var result = baseType.hashCode()
        result = 31 * result + arguments.hashCode()
        result = 31 * result + mutability.hashCode()
        return result
    }
}

internal class IrSimpleTypeImpl(
    override val baseType: IrBaseType,
    override val mutability: IrTypeMutability,
    override val isNullable: Boolean,
) : IrSimpleType {
    override fun toString() = independentToString()
    override fun asNullable(): IrSimpleType = IrSimpleTypeImpl(baseType, mutability, true)
}

internal class IrParameterizedTypeImpl(
    override val simpleType: IrSimpleType,
    override val arguments: Map<String, IrParameterizedType.Argument>,
) : IrParameterizedType {
    override fun toString() = independentToString()

    override fun asNullable(): IrParameterizedType = IrParameterizedTypeImpl(simpleType.asNullable(), arguments)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IrParameterizedTypeImpl) return false

        if (simpleType != other.simpleType) return false
        if (arguments != other.arguments) return false

        return true
    }

    override fun hashCode(): Int {
        var result = simpleType.hashCode()
        result = 31 * result + arguments.hashCode()
        return result
    }
}