package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.unknownType
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * Acts like both `Any` and `Nothing` at the same time.
 */
class UnresolvedType(
    override val context: CTContext,
    val astNode: AstSimpleTypeReference,
    val parameters: List<BoundTypeArgument>?,
) : BoundTypeReference {
    override val simpleName = "<ERROR>"
    override val isNullable get() = false
    override val mutability = astNode.mutability ?: TypeMutability.READONLY
    override val baseTypeOfLowerBound get() = context.swCtx.nothing
    override val span = astNode.span
    override val inherentTypeBindings = TypeUnification.EMPTY
    override val isNonNullableNothing = false
    override val isPartiallyUnresolved = true

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        diagnosis.unknownType(this)

        parameters?.forEach { it.validate(forUsage.deriveIrrelevant(), diagnosis) }
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters?.map { it.withMutabilityLimitedTo(limitToMutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters,
        )
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters?.map { it.withTypeVariables(variables) }
        )
    }

    val asAny: RootResolvedTypeReference by lazy {
        context.swCtx.any.baseReference.withMutability(this.mutability)
    }

    val asNothing: RootResolvedTypeReference by lazy {
        context.swCtx.nothing.baseReference.withMutability(this.mutability)
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        return when(assigneeType) {
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            else -> {
                /* act like any */
                asAny.unify(assigneeType, assignmentLocation, carry)
            }
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return UnresolvedType(
            context,
            astNode,
            emptyList(),
        )
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            this.context,
            astNode,
            parameters?.map { it.instantiateFreeVariables(context) },
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            this.context,
            astNode,
            parameters?.map { it.instantiateAllParameters(context) },
        )
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        // act like any AND nothing
        return true
    }

    override fun asAstReference(): TypeReference {
        return astNode
    }

    override fun toString() = simpleName

    override fun toBackendIr(): IrType {
        throw InternalCompilerError("Attempting to create backend IR from unresolved type at $span")
    }
}