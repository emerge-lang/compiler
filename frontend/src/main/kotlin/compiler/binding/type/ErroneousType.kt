package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ambiguousType
import compiler.diagnostic.unknownType
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * Acts like both `Any` and `Nothing` at the same time.
 */
class ErroneousType(
    override val context: CTContext,
    val astNode: AstSimpleTypeReference,
    val parameters: List<BoundTypeArgument>?,
    val candidates: List<BoundBaseType>,
) : BoundTypeReference {
    init {
        check(candidates.size != 1) {
            "not applicable if there is exactly one candidate; either 0 for 'unknown type' or 2+ for 'ambiguous type'"
        }
        assert(candidates.isEmpty() xor (candidates.map { it.simpleName }.distinct().size == 1)) {
            "all candidates must have the same name (signifies amiguous type)"
        }
    }
    override val simpleName = candidates.firstOrNull()?.simpleName ?: "<ERROR>"
    override val isNullable get() = false
    override val mutability = astNode.mutability ?: TypeMutability.READONLY
    override val baseTypeOfLowerBound get() = context.swCtx.nothing
    override val span = astNode.span
    override val inherentTypeBindings = TypeUnification.EMPTY
    override val isNonNullableNothing = false
    override val isPartiallyUnresolved = true

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        if (candidates.isEmpty()) {
            diagnosis.unknownType(this)
        } else {
            diagnosis.ambiguousType(this)
        }

        parameters?.forEach { it.validate(forUsage.deriveIrrelevant(), diagnosis) }
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
            candidates,
        )
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
            candidates,
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            parameters?.map { it.withMutabilityLimitedTo(limitToMutability) },
            candidates,
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            parameters,
            candidates,
        )
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            parameters?.map { it.withTypeVariables(variables) },
            candidates,
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
        return ErroneousType(
            context,
            astNode,
            parameters?.map { it.defaultMutabilityTo(mutability) },
            candidates,
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return ErroneousType(
            context,
            astNode,
            emptyList(),
            candidates,
        )
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return ErroneousType(
            this.context,
            astNode,
            parameters?.map { it.instantiateFreeVariables(context) },
            candidates,
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return ErroneousType(
            this.context,
            astNode,
            parameters?.map { it.instantiateAllParameters(context) },
            candidates,
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
        throw InternalCompilerError("Attempting to create backend IR from unresolved or ambiguous type at $span")
    }
}