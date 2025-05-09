package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.hiddenTypeExposed
import compiler.lexer.Span
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
    private val context: CTContext,
    val original: NamedTypeReference?,
    private val explicitMutability: TypeMutability?,
    val baseType: BoundBaseType,
    val arguments: List<BoundTypeArgument>?,
) : BoundTypeReference {
    override val isNullable = false
    override val mutability = if (baseType.isCoreScalar) TypeMutability.IMMUTABLE else (explicitMutability ?: original?.mutability ?: TypeMutability.READONLY)
    override val simpleName = original?.simpleName ?: baseType.simpleName
    override val span = original?.span ?: original?.declaringNameToken?.span
    override val baseTypeOfLowerBound = baseType
    override val isNothing get()= baseType == context.swCtx.nothing

    override val inherentTypeBindings by lazy {
        TypeUnification.fromExplicit(baseType.typeParameters ?: emptyList(), arguments, span ?: Span.UNKNOWN)
    }

    constructor(context: CTContext, original: NamedTypeReference, baseType: BoundBaseType, parameters: List<BoundTypeArgument>?) : this(
        context,
        original,
        original.mutability,
        baseType,
        parameters,
    )

    override fun withMutability(mutability: TypeMutability?): RootResolvedTypeReference {
        val newMutability = if (baseType.isCoreScalar) TypeMutability.IMMUTABLE else mutability
        if (newMutability == this@RootResolvedTypeReference.mutability) {
            return this
        }

        return RootResolvedTypeReference(
            context,
            original,
            newMutability,
            baseType,
            arguments,
        )
    }

    override fun withMutabilityIntersectedWith(mutability: TypeMutability?): RootResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.union(it) } ?: this.mutability
        return RootResolvedTypeReference(
            context,
            original,
            combinedMutability,
            baseType,
            arguments,
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        val limitedMutability = mutability.limitedTo(limitToMutability)
        return RootResolvedTypeReference(
            context,
            original,
            limitedMutability,
            baseType,
            arguments,
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
            context,
            original,
            mutability,
            baseType,
            arguments,
        )
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        arguments?.forEach { it.validate(forUsage.deriveIrrelevant(), diagnosis) }
        inherentTypeBindings.diagnostics.forEach(diagnosis::add)
        baseType.validateAccessFrom(forUsage.usageLocation, diagnosis)
        forUsage.exposedBy?.let { exposer ->
            if (exposer.visibility.isPossiblyBroaderThan(baseType.visibility)) {
                diagnosis.hiddenTypeExposed(baseType, exposer, span ?: Span.UNKNOWN)
            }
        }
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
                if (this.equalsExceptMutability(other)) {
                    return withMutability(this.mutability.union(other.mutability))
                }
                // end of special cases until generic supertypes are implemented
                val commonSuperBaseType = BoundBaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                val transformedArguments = if (commonSuperBaseType.typeParameters.isNullOrEmpty()) null else {
                    check(commonSuperBaseType == this.baseType && commonSuperBaseType == other.baseType) { "Generic supertypes are not implemented, yet." }
                    commonSuperBaseType.typeParameters.mapIndexed { typeParameterIndex, typeParameter ->
                        val lhs = this.arguments?.getOrNull(typeParameterIndex) ?: typeParameter.createPlaceholderTypeArgument(this.context)
                        val rhs = other.arguments?.getOrNull(typeParameterIndex) ?: typeParameter.createPlaceholderTypeArgument(other.context)
                        lhs.intersect(rhs, typeParameter.bound)
                    }
                }
                RootResolvedTypeReference(
                    context = context,
                    original = null,
                    explicitMutability = this.mutability.union(other.mutability),
                    baseType = commonSuperBaseType,
                    arguments = transformedArguments,
                )
            }
            is GenericTypeReference,
            is UnresolvedType,
            is BoundIntersectionTypeReference,
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
            context,
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
                        ValueNotAssignableDiagnostic(this, assigneeType, "${assigneeType.baseType.simpleName} is not a subtype of ${this.baseType.simpleName}", assignmentLocation)
                    )
                }

                // the modifiers must be compatible
                if (!(assigneeType.mutability isAssignableTo this.mutability)) {
                    return carry.plusReporting(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a ${assigneeType.mutability} value to a ${this.mutability} reference", assignmentLocation)
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
                ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
            )
            is BoundIntersectionTypeReference -> {
                return assigneeType.flippedUnify(
                    this,
                    assignmentLocation,
                    carry,
                    reason = { "none of $assigneeType is a subtype of $this" },
                )
            }
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            this.context,
            original,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateFreeVariables(context) },
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            this.context,
            original,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateAllParameters(context) },
        )
    }

    override fun asAstReference(): TypeReference {
        return original ?: NamedTypeReference(
            simpleName,
            TypeReference.Nullability.of(this),
            mutability,
            null,
            arguments?.map { it.astNode },
            span,
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
    override fun toString(): String = _string

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

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as RootResolvedTypeReference

        if (mutability != other.mutability) return false
        return equalsExceptMutability(other)
    }

    private fun equalsExceptMutability(other: RootResolvedTypeReference): Boolean {
        if (baseType != other.baseType) return false
        if (arguments != other.arguments) return false

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