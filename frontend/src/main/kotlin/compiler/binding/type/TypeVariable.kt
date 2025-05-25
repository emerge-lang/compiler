package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * A generic type in the process of being inferred. To understand the difference between [TypeVariable]
 * and [GenericTypeReference], consider this function:
 *
 *     n <T> forEach(elements: List<out T>, action: (T) -> Unit) {
 *
 *     }
 *
 * When validating the `forEach` function definition (including the body), `T` is a [GenericTypeReference],
 * meaning that the concrete type of T can never be known. When `T` is consumed, it acts as if `T` was equal to
 * its bound. When a value of type `T` is expected, only values of type `T` are accepted.
 *
 * When validating an invocation of `forEach`, the `T` of `forEach` becomes a [TypeVariable], because it can be
 * reasoned about from the types of the parameters (if you pass a `List<Int>` to `forEach`, the action has to accept
 * an `Int`, too).
 *
 * So, in the context of:
 *
 *     val x: List<Int>
 *     forEach(x, { someX -> ... })
 *
 * `T` becomes a [TypeVariable] and thus can be inferred to be `Int` for the `x` argument; and as a result the compiler
 * can infer that `someX` in the lambda is of type `Int`.
 */
class TypeVariable private constructor(
    override val context: CTContext,
    private val asGeneric: GenericTypeReference,
) : BoundTypeReference by asGeneric {
    constructor(ref: GenericTypeReference) : this(
        ref.context,
        ref,
    )
    constructor(parameter: BoundTypeParameter) : this(parameter.context, GenericTypeReference(
        NamedTypeReference(parameter.astNode.name),
        parameter,
    ) as GenericTypeReference)

    internal val parameter: BoundTypeParameter get()= asGeneric.parameter

    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): TypeVariable {
        return rewrap(asGeneric.defaultMutabilityTo(mutability))
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return rewrap(asGeneric.withMutability(mutability))
    }

    override fun withMutabilityIntersectedWith(mutability: TypeMutability?): BoundTypeReference {
        return rewrap(asGeneric.withMutabilityIntersectedWith(mutability))
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return rewrap(asGeneric.withMutabilityLimitedTo(limitToMutability))
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return when (nullability) {
            TypeReference.Nullability.NULLABLE -> NullableTypeReference(this)
            TypeReference.Nullability.NOT_NULLABLE,
            TypeReference.Nullability.UNSPECIFIED -> this
        }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        return this
    }

    private fun rewrap(newNested: GenericTypeReference): TypeVariable {
        if (newNested == asGeneric) {
            return this
        }

        return TypeVariable(newNested)
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification
    ): TypeUnification {
        return when (assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundIntersectionTypeReference,
            is BoundTypeArgument, -> {
                return carry.plusSupertypeConstraint(this.parameter, assigneeType, assignmentLocation)
            }
            is UnresolvedType -> unify(assigneeType.standInType, assignmentLocation, carry)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
            is NullableTypeReference -> {
                if (isNullable) {
                    return carry.plusSupertypeConstraint(this.parameter, assigneeType, assignmentLocation)
                } else {
                    val carry2 = carry.plusReporting(ValueNotAssignableDiagnostic(
                        this,
                        assigneeType,
                        "Cannot assign a possibly null value to a non-nullable reference",
                        assignmentLocation,
                    ))
                    unify(assigneeType.nested, assignmentLocation, carry2)
                }
            }
        }
    }

    fun flippedUnify(targetType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        return carry.plusSubtypeConstraint(this.parameter, targetType, assignmentLocation)
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return context.getFinalValueFor(this.parameter)
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return instantiateFreeVariables(context)
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return other == this
    }

    override fun asAstReference(): TypeReference {
        return asGeneric.asAstReference()
    }

    override fun toBackendIr(): IrType {
        throw InternalCompilerError("Attempting to create BackendIr from unresolved type variable $this at ${this.span}")
    }

    fun toStringForUnification(): String {
        return asGeneric.toString()
    }

    override fun toString(): String = "Var(${toStringForUnification()})"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeVariable) return false

        if (asGeneric != other.asGeneric) return false

        return true
    }

    override fun hashCode(): Int {
        return asGeneric.hashCode()
    }
}