package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

/**
 * A generic type in the process of being inferred. To understand the difference between [TypeVariable]
 * and [GenericTypeReference], consider this function:
 *
 *     fun <T> forEach(elements: List<out T>, action: (T) -> Unit) {
 *
 *     }
 *
 * When validating the `forEach` function definition (including the body), `T` is a [GenericTypeReference],
 * meaning that the concrete type of T can never be known and we can treat all mentions of `T` like mentions
 * of `T`s bound.
 *
 * When validating an invocation of `forEach`, the `T` of `forEach` becomes a type variable, because it can be
 * reasoned about from the types of the parameters (if you pass a `List<Int>` to `forEach`, the action has to accept
 * an `Int`, too).
 *
 * So, in the context of:
 *
 *     val x: List<Int>
 *     forEach(x, { someX -> TOOD() })
 *
 * `T` becomes a [TypeVariable] and thus can be inferred to be `Int` for the `x` argument; and as a result the compiler
 * can infer that `someX` in the lambda is of type `Int`.
 */
class TypeVariable(
    val parameter: BoundTypeParameter,
    override val sourceLocation: SourceLocation?,
) : BoundTypeReference {
    constructor(ref: GenericTypeReference) : this(ref.parameter, ref.sourceLocation)
    constructor(parameter: BoundTypeParameter) : this(parameter, parameter.astNode.name.sourceLocation)

    override val isNullable get() = parameter.bound.isNullable
    override val simpleName get() = parameter.name
    override val mutability get() = parameter.bound.mutability
    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeReference {
        return this
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: SourceLocation,
        carry: TypeUnification
    ): TypeUnification {
        return when (assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundTypeArgument -> {
                val newCarry = carry.plus(this, assigneeType, assignmentLocation)
                val selfBinding = newCarry.bindings[this] ?: return newCarry
                selfBinding.unify(assigneeType, assignmentLocation, newCarry)
            }
            is UnresolvedType -> unify(assigneeType.standInType, assignmentLocation, carry)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
        }
    }

    fun flippedUnify(targetType: BoundTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        val newCarry = carry.plus(this, targetType, assignmentLocation)
        val selfBinding = carry.bindings[this] ?: return newCarry
        return targetType.unify(selfBinding, assignmentLocation, newCarry)
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return context.bindings[this] ?: this
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return instantiateFreeVariables(context)
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return other == this
    }

    override fun toString() = simpleName

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeVariable) return false

        if (parameter != other.parameter) return false

        return true
    }

    override fun hashCode(): Int {
        return parameter.hashCode()
    }
}