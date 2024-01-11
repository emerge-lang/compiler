package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
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
    override val context: CTContext,
    val parameter: BoundTypeParameter,
    override val sourceLocation: SourceLocation?,
) : ResolvedTypeReference {
    constructor(ref: GenericTypeReference) : this(ref.context, ref.parameter, ref.sourceLocation)
    constructor(parameter: BoundTypeParameter) : this(parameter.context, parameter, parameter.astNode.name.sourceLocation)

    override val isNullable get() = parameter.bound.isNullable
    override val simpleName get() = parameter.name
    override val mutability get() = parameter.bound.mutability
    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun withMutability(modifier: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        TODO("Not yet implemented")
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): ResolvedTypeReference {
        return this
    }

    override fun unify(
        assigneeType: ResolvedTypeReference,
        assignmentLocation: SourceLocation,
        carry: TypeUnification
    ): TypeUnification {
        when (assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference -> {
                val newCarry = carry.plus(this, assigneeType, assignmentLocation)
                val selfBinding = newCarry.bindings[this] ?: return newCarry
                return selfBinding.unify(assigneeType, assignmentLocation, newCarry)
            }
            else -> TODO()
        }
    }

    fun flippedUnify(targetType: ResolvedTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        val newCarry = carry.plus(this, targetType, assignmentLocation)
        val selfBinding = carry.bindings[this] ?: return newCarry
        return targetType.unify(selfBinding, assignmentLocation, newCarry)
    }

    override fun instantiateVariables(context: TypeUnification): ResolvedTypeReference {
        return context.bindings[this] ?: this
    }

    override fun contextualize(context: TypeUnification): ResolvedTypeReference {
        return instantiateVariables(context)
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
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