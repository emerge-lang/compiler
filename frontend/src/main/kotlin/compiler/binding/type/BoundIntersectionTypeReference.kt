package compiler.binding.type

import compiler.ast.type.AstIntersectionType
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.illegalIntersectionType
import compiler.diagnostic.simplifiableIntersectionType
import compiler.lexer.Operator
import compiler.lexer.Span
import compiler.util.twoElementPermutationsUnordered
import io.github.tmarsteel.emerge.backend.api.ir.IrIntersectionType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability

class BoundIntersectionTypeReference private constructor(
    override val context: CTContext,
    val astNode: AstIntersectionType?,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {
    init {
        check(components.none { it.isNullable }) {
            """
                if only some components are nullable the intersection type is still not nullable.
                if all components are nullable, the canonical object structure is NullableTypeReference(IntersectionTypeReference),
                which leaves all the components to the intersection as non-nullable
            """.trimIndent()
        }
    }

    override val span = astNode?.span
    override val isNullable get()= false
    override val mutability get()= mutabilityOfComponents(components)
    override val simpleName get()= components.joinToString(separator = " ${Operator.INTERSECTION.text} ", transform = { it.simpleName ?: it.toString() })
    override val isNothing by lazy {
        components.any { it.isNothing } || simplifyIsEffectivelyBottomType(components)
    }

    override val baseTypeOfLowerBound by lazy {
        BoundBaseType.closestCommonSupertypeOf(components.map { it.baseTypeOfLowerBound })
    }

    override val inherentTypeBindings: TypeUnification by lazy {
        components.asSequence()
            .map { it.inherentTypeBindings }
            .fold(TypeUnification.EMPTY) { carry, bindings ->
                carry.mergedWith(bindings) { param, firstCome, _, diagnosis ->
                    val sourceType = components.first { c -> c.inherentTypeBindings.bindings.any { (cParam, _) -> param == cParam} }
                    diagnosis.illegalIntersectionType(this, "A single base type can only occur once in an intersection type, ${sourceType.baseTypeOfLowerBound} is mentioned more than once.")
                    firstCome
                }
            }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
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
        return when (nullability) {
            TypeReference.Nullability.UNSPECIFIED,
            TypeReference.Nullability.NOT_NULLABLE -> this
            TypeReference.Nullability.NULLABLE -> NullableTypeReference(this)
        }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        components.forEach { it.validate(forUsage, diagnosis) }
        inherentTypeBindings.diagnostics.forEach(diagnosis::add)
        if (astNode != null) {
            val simplified = simplify()
            if (simplified !== this) {
                diagnosis.simplifiableIntersectionType(astNode, simplified)
            }
        }
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return mapComponents(simplify = true) { it.closestCommonSupertypeWith(other) }
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
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
                    return carry.plusDiagnostic(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
                    )
                }
                return unify(assigneeType.nested, assignmentLocation, carry)
            }
            is TypeVariable -> return assigneeType.flippedUnify(this, assignmentLocation, carry)
            is UnresolvedType -> return unify(assigneeType.standInType, assignmentLocation, carry)
            else -> {
                /*
                one would think that this is just a case of unifying each component with the assignee. But there's more
                to it:
                Say this is an intersection of some type T and an unbound type variable _V, and assigneeType is also a variant
                of T. In that case, the naive approach would also unify _V with T. That's not necessarily incorrect,
                but it forces the binding for _V into a needlessly narrow corner, possibly preventing the unification
                from succeeding.
                Hence: this code sees types not as a set of possible values, but a set of promises a value makes to
                its users (effectively the inverse of the traditional concept of a type). And then, before unifying with
                the variable parts of the compound type, the promises already covered by the non-variable parts of the
                intersection are subtracted from the assigneeType. In a way, this improves the S/N ratio of the assigneeType
                before it is unified with the type variables.
                 */
                val (varComponents, nonVarComponents) = components.partition { it is TypeVariable }
                val carry2 = nonVarComponents.fold(carry) { innerCarry, component ->
                    component.unify(assigneeType, assignmentLocation, innerCarry)
                }
                val fullyCoveringComponent = nonVarComponents.firstOrNull { it.hasSameBaseTypeAs(assigneeType) }
                val newAssignee = if (fullyCoveringComponent == null) assigneeType else {
                    context.swCtx.any.baseReference
                        .withMutability(assigneeType.mutability.intersect(fullyCoveringComponent.mutability))
                        .withCombinedNullability(if (!fullyCoveringComponent.isNullable && assigneeType.isNullable) TypeReference.Nullability.NULLABLE else TypeReference.Nullability.UNSPECIFIED)
                }
                return varComponents.fold(carry2) { innerCarry, component ->
                    component.unify(newAssignee, assignmentLocation, innerCarry)
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
            .map { targetType.unify(it, assignmentLocation, carry) }
            .filter { it.getErrorsNotIn(carry).none() }
            .firstOrNull()
            ?: carry.plusDiagnostic(ValueNotAssignableDiagnostic(
                targetType,
                this,
                reason(),
                assignmentLocation,
            ))
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return mapComponents(simplify = true) { it.instantiateAllParameters(context) }
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return mapComponents(simplify = true) { it.instantiateFreeVariables(context) }
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return components.any { it.hasSameBaseTypeAs(other) }
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> {
        return components
            .flatMap { it.findMemberVariable(name) }
            .toSet()
    }

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return components.flatMap { it.findMemberFunction(name) }
    }

    override fun asAstReference(): AstIntersectionType {
        if (astNode != null) {
            return astNode
        }

        val astComponents = components.map { it.asAstReference() as NamedTypeReference }
        return AstIntersectionType(astComponents, Span.range(*astComponents.map { it.span }.toTypedArray()) ?: Span.UNKNOWN)
    }

    /**
     * @return [BoundIntersectionTypeReference] that represent the same type as `this`, but using fewer [components] if
     * possible. May return `this`.
     */
    fun simplify(): BoundTypeReference {
        val newComponents = simplifyComponents(components, context) ?: return this
        newComponents.singleOrNull()?.let { return it }
        return ofComponents(context, null, newComponents)
    }

    private inline fun mapComponents(simplify: Boolean = false, crossinline componentTransform: (BoundTypeReference) -> BoundTypeReference): BoundTypeReference {
        val mappedComponents = ArrayList<BoundTypeReference>(components.size)
        var anyChanged = false
        for (component in components) {
            val newComponent = componentTransform(component)
            mappedComponents.add(newComponent)
            if (newComponent !== component && newComponent != component) {
                anyChanged = true
            }
        }
        if (!anyChanged) {
            mappedComponents.clear()
            return this
        }

        if (!simplify) {
            return BoundIntersectionTypeReference(
                context,
                astNode,
                mappedComponents,
            )
        }

        val simplifiedMappedComponents = simplifyComponents(mappedComponents, context) ?: mappedComponents
        simplifiedMappedComponents.singleOrNull()?.let { return it }



        return BoundIntersectionTypeReference(
            context,
            null,
            simplifiedMappedComponents,
        )
    }

    private val _backendIr by lazy {
        val simplified = this.simplify()
        if (simplified !== this) {
            return@lazy simplified.toBackendIr()
        }

        IrIntersectionTypeImpl(
            components.map { it.toBackendIr() },
            this.isNullable,
            this.mutability.toBackendIr(),
        )
    }
    override fun toBackendIr(): IrType {
        return _backendIr
    }

    override fun toString() = toString(false)

    fun toString(nullableComponents: Boolean): String {
        return components.joinToString(
            transform = { it: BoundTypeReference -> NullableTypeReference(it).toString() }.takeIf { nullableComponents },
            separator = " ${Operator.INTERSECTION.text} ",
        )
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BoundIntersectionTypeReference) return false

        if (this.components != other.components) return false
        return true
    }

    override fun hashCode(): Int {
        return components.hashCode()
    }

    companion object {
        fun ofComponents(
            context: CTContext,
            ref: AstIntersectionType?,
            components: List<BoundTypeReference>,
            simplify: Boolean = false,
        ): BoundTypeReference {
            components.singleOrNull()?.let { return it }
            val isNullable = nullabilityOfComponents(components)
            var nonNullableIntersection: BoundTypeReference = BoundIntersectionTypeReference(context, ref, components.map { it.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)})
            if (simplify) {
                nonNullableIntersection = (nonNullableIntersection as BoundIntersectionTypeReference).simplify()
            }
            return if (isNullable) NullableTypeReference(nonNullableIntersection) else nonNullableIntersection
        }

        private fun nullabilityOfComponents(components: Iterable<BoundTypeReference>): Boolean = components.all { it.isNullable }
        private fun mutabilityOfComponents(components: Iterable<BoundTypeReference>): TypeMutability = components.asSequence().map { it.mutability }.reduce(TypeMutability::intersect)

        /**
         * @return the type that represents the union of `this` and [other]. In the general case,
         * this is an instance of [BoundIntersectionTypeReference] holding `this` and [other]. However, this
         * method should try to simplify. The simplification will make error messages much easier to
         * digest (and probably helps debugging). E.g.:
         *
         * | input type            | simplification |
         * |-----------------------|----------------|
         * |`mut T & read Any`     | `mut T`        |
         * |`mut T & const T`      | `exclusive T`  |
         * |`read T & const Any`   | `mut T`        |
         */
        fun BoundTypeReference.intersect(other: BoundTypeReference): BoundTypeReference {
            if (this is BoundIntersectionTypeReference) {
                if (other is BoundIntersectionTypeReference) {
                    return BoundIntersectionTypeReference(context, null, this.components + other.components).simplify()
                }
            } else if (other is BoundIntersectionTypeReference) {
                return other.intersect(this)
            }

            when (this) {
                is BoundIntersectionTypeReference -> {
                    check(other !is BoundIntersectionTypeReference) {
                        "This case should never happen, is prevented by the guard code above"
                    }
                    return BoundIntersectionTypeReference(context, null, this.components + other).simplify()
                }
                is BoundTypeArgument -> {
                    val compoundVariance = when(other) {
                        is BoundTypeArgument -> variance.intersect(other.variance)
                        else -> variance
                    }
                    val intersectionType = type.intersect(other).let {
                        (it as? BoundIntersectionTypeReference)?.simplify() ?: it
                    }
                    return BoundTypeArgument(
                        context,
                        TypeArgument(compoundVariance, intersectionType.asAstReference()),
                        compoundVariance,
                        intersectionType,
                    )
                }
                is GenericTypeReference,
                is RootResolvedTypeReference,
                is NullableTypeReference,
                is TypeVariable,
                is UnresolvedType, -> {
                    return ofComponents(context, null, listOf(this, other), true)
                }
            }
        }

        private fun simplifyIsEffectivelyBottomType(components: List<BoundTypeReference>): Boolean {
            return components
                .filterNot { it.baseTypeOfLowerBound.kind.allowsSubtypes }
                .twoElementPermutationsUnordered()
                .filter { (a, b) -> !a.hasSameBaseTypeAs(b) }
                .any()
        }

        /**
         * First step of simplifying a union type: remove any mentions of verbatim Any,
         * and only have nullable components iff all components are nullable.
         * @return first: new components, second: whether the result is nullable
         */
        private fun simplifyCollapseAnys(components: List<BoundTypeReference>, context: CTContext): List<BoundTypeReference>? {
            val (anys, nonAnys) = components.partition {
                val nonNullable = if (it is NullableTypeReference) it.nested else it
                nonNullable is RootResolvedTypeReference && nonNullable.baseType == context.swCtx.any
            }
            if (anys.isEmpty()) {
                return null
            }

            var newComponents = nonAnys.asSequence()

            val anyMutability = anys.asSequence()
                .map { it.mutability }
                .fold(TypeMutability.READONLY, TypeMutability::intersect)

            if (nonAnys.isEmpty()) {
                return listOf(
                    context.swCtx.any.baseReference
                        .withMutability(anyMutability)
                        .withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
                )
            }

            if (anyMutability != TypeMutability.READONLY) {
                newComponents = newComponents.map {
                    if (it.mutability == anyMutability) it else it.withMutability(it.mutability.intersect(anyMutability))
                }
            }

            return newComponents.toList()
        }

        /**
         * performs a single pass of removing components that are a supertype of any other component
         * @return whether the list was modified. If true, further calls to this method may be able to simplify
         * further.
         */
        private fun simplifyElideSupertypesSinglePass(components: MutableList<BoundTypeReference>): Boolean {
            val selfMutability = components.asSequence().map { it.mutability }.reduce(TypeMutability::intersect)

            var anySupertypesRemoved = false
            var pivotIndex = 0
            pivots@while (pivotIndex < components.size) {
                val pivotType = components[pivotIndex]
                val pivotTypeWithSelfMutability = pivotType.withMutability(selfMutability)

                var checkIndex = pivotIndex + 1
                checks@while (checkIndex < components.size) {
                    val checkType = components[checkIndex]
                    val checkTypeWithSelfMutability = checkType.withMutability(selfMutability)
                    if (checkTypeWithSelfMutability.isAssignableTo(pivotTypeWithSelfMutability)) {
                        // pivot is a supertype of checkType, so its superfluous
                        // make sure to retain the mutability of the compound type
                        if (checkType.mutability != checkTypeWithSelfMutability.mutability) {
                            components[checkIndex] = checkTypeWithSelfMutability
                        }
                        components.removeAt(pivotIndex)
                        pivotIndex = checkIndex - 1
                        anySupertypesRemoved = true
                        continue@pivots
                    } else if (pivotTypeWithSelfMutability.isAssignableTo(checkTypeWithSelfMutability)) {
                        // checkType is a supertype of pivot, so its superfluous
                        // make sure to retain the mutability of the compound type
                        if (pivotType.mutability != pivotTypeWithSelfMutability.mutability) {
                            components[pivotIndex] = pivotTypeWithSelfMutability
                        }
                        components.removeAt(checkIndex)
                        anySupertypesRemoved = true
                        continue@checks // DON'T increment checkIndex, the removal has the same effect
                    }

                    checkIndex++
                }

                pivotIndex++
            }

            return anySupertypesRemoved
        }

        private fun simplifyComponents(components: List<BoundTypeReference>, context: CTContext): List<BoundTypeReference>? {
            if (simplifyIsEffectivelyBottomType(components)) {
                val selfMutability = components.asSequence().map { it.mutability }.reduce(TypeMutability::intersect)
                return listOf(
                    context.swCtx.bottomTypeRef
                        .withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
                        .withMutability(selfMutability)
                )
            }

            val afterStep1 = simplifyCollapseAnys(components, context)

            val newComponents = (afterStep1 ?: components).toMutableList()
            var simplifiedBySupertypeElision = false
            do {
                val simplifiedThisPass = simplifyElideSupertypesSinglePass(newComponents)
                simplifiedBySupertypeElision = simplifiedBySupertypeElision || simplifiedThisPass
            } while (simplifiedThisPass)

            if (afterStep1 == null && !simplifiedBySupertypeElision) {
                return null
            }

            return newComponents
        }
    }
}

private class IrIntersectionTypeImpl(
    override val components: List<IrType>,
    override val isNullable: Boolean,
    override val mutability: IrTypeMutability,
) : IrIntersectionType {
    override fun asNullable(): IrType {
        if (isNullable) {
            return this
        }
        return IrIntersectionTypeImpl(
            components.map { it.asNullable() },
            true,
            mutability,
        )
    }
}