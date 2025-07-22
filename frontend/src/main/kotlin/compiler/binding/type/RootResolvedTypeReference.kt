package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.AstSimpleTypeReference
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
    override val context: CTContext,
    val original: AstSimpleTypeReference?,
    private val modifiedSinceOriginal: Boolean,
    private val explicitMutability: TypeMutability?,
    val baseType: BoundBaseType,
    val arguments: List<BoundTypeArgument>?,
) : BoundTypeReference {
    override val isNullable = false
    override val mutability = if (baseType.isCoreScalar) TypeMutability.IMMUTABLE else (explicitMutability ?: original?.mutability ?: TypeMutability.READONLY)
    override val simpleName = original?.simpleName ?: baseType.simpleName
    override val span = original?.span ?: (original as? NamedTypeReference)?.declaringNameToken?.span
    override val baseTypeOfLowerBound = baseType
    override val isNonNullableNothing get()= baseType == context.swCtx.nothing
    override val isPartiallyUnresolved get()= arguments?.any { it.isPartiallyUnresolved } == true

    override val inherentTypeBindings by lazy {
        val params = baseType.typeParameters ?: emptyList()
        TypeUnification.fromExplicit(params, params, arguments, span ?: Span.UNKNOWN)
    }

    constructor(
        context: CTContext,
        original: AstSimpleTypeReference,
        baseType: BoundBaseType,
        parameters: List<BoundTypeArgument>?
    ) : this(
        context,
        original,
        false,
        original.mutability,
        baseType,
        parameters,
    )

    constructor(context: CTContext, explicitMutability: TypeMutability, baseType: BoundBaseType, parameters: List<BoundTypeArgument>?) : this(
        context,
        null,
        false,
        explicitMutability,
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
            true,
            newMutability,
            baseType,
            arguments,
        )
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): RootResolvedTypeReference {
        val combinedMutability = mutability?.let { this.mutability.union(it) } ?: this.mutability
        if (combinedMutability == this.mutability) {
            return this
        }

        return RootResolvedTypeReference(
            context,
            original,
            true,
            combinedMutability,
            baseType,
            arguments,
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        val limitedMutability = mutability.limitedTo(limitToMutability)
        if (limitedMutability == this.mutability) {
            return this
        }

        return RootResolvedTypeReference(
            context,
            original,
            true,
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
            true,
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
            is BoundTypeArgument -> hasSameBaseTypeAs(other.type)
            else -> false
        }
    }

    /**
     * For example, given:
     *
     *     class Box<X> {
     *         nested: X = init
     *     }
     *
     *     interface A<T> {
     *     }
     *     interface B<U> : A<U> {
     *     }
     *     interface C<W> : B<Box<W>> {
     *     }
     *
     * then these are the return values of [getInstantiatedSupertype]:
     *
     * |`this`|`superBaseType`|return value|
     * |------|---------------|------------|
     * | `B<S32>` | `A`       | `A<S32>`   |
     * | `C<S32>` | `B`       | `B<Box<S32>>`   |
     * | `C<S32>` | `A`       | `A<Box<S32>>`   |
     * | `C<Box<E>>`   | `A`  | `A<Box<Box<E>>>` |
     *
     * @param superBaseType **must** be a supertype of [baseType] according to [BoundBaseType.isSubtypeOf]
     * @return a parameterized reference to that [superBaseType] where the arguments are in the namespace of [baseType].
     */
    fun getInstantiatedSupertype(superBaseType: BoundBaseType): RootResolvedTypeReference {
        return when (this.baseType) {
            superBaseType -> this
            context.swCtx.nothing -> superBaseType.getBoundReferenceAssertNoTypeParameters()
            else -> baseType.superTypes.getParameterizedSupertype(superBaseType).instantiateAllParameters(inherentTypeBindings)
        }
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (other) {
            is NullableTypeReference -> NullableTypeReference(closestCommonSupertypeWith(other.nested))
            is RootResolvedTypeReference -> {
                if (this.baseType == this.baseType.context.swCtx.nothing) {
                    return other.withMutability(this.mutability.union(other.mutability))
                }
                if (other.baseType == other.baseType.context.swCtx.nothing) {
                    return this.withMutability(this.mutability.union(other.mutability))
                }
                if (this == other) {
                    return this
                }
                if (this.equalsExceptMutability(other)) {
                    return withMutability(this.mutability.union(other.mutability))
                }
                val commonSuperBaseType = BoundBaseType.closestCommonSupertypeOf(this.baseType, other.baseType)
                val transformedArguments = if (commonSuperBaseType.typeParameters.isNullOrEmpty()) null else {
                    val commonSupertypeFromThis = this.getInstantiatedSupertype(commonSuperBaseType)
                    val commonSupertypeFromOther = other.getInstantiatedSupertype(commonSuperBaseType)
                    commonSupertypeFromThis.arguments?.zip(commonSupertypeFromOther.arguments ?: emptyList(), BoundTypeArgument::intersect)
                }
                RootResolvedTypeReference(
                    context,
                    this.mutability.union(other.mutability),
                    commonSuperBaseType,
                    transformedArguments,
                )
            }
            is GenericTypeReference,
            is ErroneousType,
            is BoundIntersectionTypeReference,
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
        }
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> = setOfNotNull(baseType.resolveMemberVariable(name))

    val memberFunctions: Collection<BoundOverloadSet<BoundMemberFunction>> get() = baseType.memberFunctions

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return baseType.resolveMemberFunction(name)
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            context,
            original,
            true,
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
                    return carry.plusDiagnostic(
                        ValueNotAssignableDiagnostic(this, assigneeType, "${assigneeType.baseType.simpleName} is not a subtype of ${this.baseType.simpleName}", assignmentLocation)
                    )
                }

                // the modifiers must be compatible
                if (!(assigneeType.mutability isAssignableTo this.mutability)) {
                    return carry.plusDiagnostic(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a ${assigneeType.mutability} value to a ${this.mutability} reference", assignmentLocation)
                    )
                }

                /*
                this special case is necessary. Nothing is a subtype of every other possible type,
                which is something that cannot actually be denoted in source code (class Foo : Other<*> is not legal)
                 */
                if (assigneeType.baseType == assigneeType.baseType.context.swCtx.nothing) {
                    return carry
                }

                val normalizedAssignee = assigneeType.getInstantiatedSupertype(this.baseType)
                val selfArgs = this.arguments ?: emptyList()
                val assigneeArgs = normalizedAssignee.arguments ?: emptyList()
                return selfArgs
                    .zip(assigneeArgs)
                    .fold(carry) { innerCarry, (targetArg, sourceArg) ->
                        targetArg.unify(sourceArg, assignmentLocation, innerCarry)
                    }
            }
            is ErroneousType -> return unify(assigneeType.asNothing, assignmentLocation, carry)
            is GenericTypeReference -> return unify(assigneeType.effectiveBound, assignmentLocation, carry)
            is BoundTypeArgument -> {
                // this branch is PROBABLY only taken when verifying the bound of a type parameter against an argument
                // in this case this is the bound and assigneeType is the argument
                // variance is not important in that scenario because type arguments must be subtypes of the parameters bounds
                return unify(assigneeType.type, assignmentLocation, carry)
            }
            is TypeVariable -> return assigneeType.flippedUnify(this, assignmentLocation, carry)
            is NullableTypeReference -> return carry.plusDiagnostic(
                ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
            )
            is BoundIntersectionTypeReference -> {
                return assigneeType.flippedUnify(
                    this,
                    assignmentLocation,
                    carry,
                    reason = { "no component of ($assigneeType) is a subtype of $this" },
                )
            }
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            this.context,
            original,
            true,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateFreeVariables(context) },
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            this.context,
            original,
            true,
            explicitMutability,
            baseType,
            arguments?.map { it.instantiateAllParameters(context) },
        )
    }

    override fun asAstReference(): AstSimpleTypeReference {
        return original.takeUnless { modifiedSinceOriginal } ?: NamedTypeReference(
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