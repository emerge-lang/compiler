package compiler.binding.type

import compiler.ast.type.AstUnionType
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.basetype.BoundBaseType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Operator
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundUnionTypeReference(
    val astNode: AstUnionType,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {
    override val span = astNode.span
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
        return astNode
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
}