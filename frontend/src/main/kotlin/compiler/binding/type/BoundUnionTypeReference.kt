package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.AstUnionType
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.basetype.BoundBaseType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Operator
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundUnionTypeReference(
    val astNode: AstUnionType?,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {
    override val span = astNode?.span
    override val isNullable get()= components.all { it.isNullable }
    override val mutability get()= components.asSequence().map { it.mutability }.reduce(TypeMutability::union)
    override val simpleName get()= components.joinToString(separator = " ${Operator.UNION.text} ", transform = { it.simpleName ?: it.toString() })

    override val baseTypeOfLowerBound by lazy {
        BoundBaseType.closestCommonSupertypeOf(components.map { it.baseTypeOfLowerBound })
    }

    override val inherentTypeBindings: TypeUnification by lazy {
        components.asSequence()
            .fold(TypeUnification.EMPTY) { carry, component ->
                val carry1 = carry.plusDiagnostics(component.inherentTypeBindings.diagnostics)
                component.inherentTypeBindings.bindings.entries.fold(carry1) { innerCarry, nextBinding ->
                    innerCarry.plus(nextBinding.key, nextBinding.value, component.span ?: Span.UNKNOWN)
                }
            }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundUnionTypeReference {
        return mapComponents { it.defaultMutabilityTo(mutability) }
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutability(mutability) }
    }

    override fun withMutabilityIntersectedWith(mutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutabilityIntersectedWith(mutability) }
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutabilityLimitedTo(limitToMutability) }
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return mapComponents { it.withCombinedNullability(nullability) }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        TODO("Not yet implemented")
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        if (other !is BoundUnionTypeReference) {
            return components.fold(other) { carry, component -> carry.closestCommonSupertypeWith(component) }
        }

        return mapComponents { it.closestCommonSupertypeWith(other) }
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeReference {
        return mapComponents { it.withTypeVariables(variables) }
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification,
    ): TypeUnification {
        when (assigneeType) {
            is NullableTypeReference -> {
                if (!this.isNullable) {
                    return carry.plusReporting(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
                    )
                }
                return unify(assigneeType.nested, assignmentLocation, carry)
            }
            is TypeVariable -> return assigneeType.flippedUnify(this, assignmentLocation, carry)
            is UnresolvedType -> return unify(assigneeType.standInType, assignmentLocation, carry)
            else -> {
                return components.fold(carry) { innerCarry, component ->
                    component.unify(assigneeType, assignmentLocation, carry)
                }
            }
        }
    }

    fun flippedUnify(
        targetType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification,
        reason: () -> String,
    ): TypeUnification {
        return components.asSequence()
            .map { unify(it, assignmentLocation, carry) }
            .filter { it.getErrorsNotIn(carry).none() }
            .firstOrNull()
            ?: carry.plusReporting(ValueNotAssignableDiagnostic(
                targetType,
                this,
                reason(),
                assignmentLocation,
            ))
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return mapComponents { it.instantiateAllParameters(context) }
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return components.any { it.hasSameBaseTypeAs(other) }
    }

    override fun asAstReference(): TypeReference {
        if (astNode != null) {
            return astNode
        }

        val astComponents = components.map { it.asAstReference() as NamedTypeReference }
        return AstUnionType(astComponents, Span.range(*astComponents.map { it.span }.toTypedArray()) ?: Span.UNKNOWN)
    }

    private inline fun mapComponents(crossinline componentTransform: (BoundTypeReference) -> BoundTypeReference): BoundUnionTypeReference {
        val newComponents = ArrayList<BoundTypeReference>(components.size)
        var anyChanged = false
        for (component in components) {
            val newComponent = componentTransform(component)
            newComponents.add(newComponent)
            if (newComponent === component || newComponent == component) {
                anyChanged = true
            }
        }
        if (!anyChanged) {
            newComponents.clear()
            return this
        }

        return BoundUnionTypeReference(astNode, newComponents)
    }

    override fun toBackendIr(): IrType {
        TODO("Not yet implemented")
    }

    companion object {
        /**
         * @return the type that represents the union of `this` and [other]. In the general case,
         * this is an instance of [BoundUnionTypeReference] holding `this` and [other]. However, this
         * method should try to simplify. The simplification will make error messages much easier to
         * digest (and probably helps debugging). E.g.:
         *
         * | input union           | simplification |
         * |-----------------------|----------------|
         * |`mut T & read Any`     | `mut T`        |
         * |`mut T & const T`      | `exclusive T`  |
         * |`read T & const Any`   | `mut T`        |
         *
         * TODO: implement simplification, at least for the easy example cases
         */
        fun BoundTypeReference.union(other: BoundTypeReference): BoundTypeReference {
            if (this is BoundUnionTypeReference) {
                if (other is BoundUnionTypeReference) {
                    return BoundUnionTypeReference(null, this.components + other.components)
                }
            } else if (other is BoundUnionTypeReference) {
                return other.union(this)
            }

            when (this) {
                is BoundUnionTypeReference -> {
                    throw InternalCompilerError("This case should never happen, is prevented by the guard code above")
                }
                is BoundTypeArgument -> {
                    val unionVariance = when(other) {
                        is BoundTypeArgument -> variance.union(other.variance)
                        else -> variance
                    }
                    val unionType = type.union(other)
                    return BoundTypeArgument(
                        context,
                        TypeArgument(unionVariance, unionType.asAstReference()),
                        unionVariance,
                        unionType,
                    )
                }
                is GenericTypeReference,
                is RootResolvedTypeReference,
                is NullableTypeReference,
                is TypeVariable,
                is UnresolvedType, -> {
                    return BoundUnionTypeReference(null, listOf(this, other))
                }
            }
        }
    }
}