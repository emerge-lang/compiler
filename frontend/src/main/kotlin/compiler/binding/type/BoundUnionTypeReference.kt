package compiler.binding.type

import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.AstUnionType
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.simplifiableUnionType
import compiler.lexer.Operator
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrUnionType

/**
 * `A | B`: a value of it is a value of one of the [components]. What the type-system proofs model as `Model.Union`
 * (`Subtyping.unify_union` and friends), so the two have to agree.
 *
 * The components are no unions themselves (those are flattened), and not nullable: the union is nullable as a whole
 * where a component was (`A | B?` is `(A | B)?`), see [ofComponents]. The exception is a [TypeVariable], which cannot
 * be made non-null.
 */
class BoundUnionTypeReference private constructor(
    override val context: CTContext,
    val astNode: AstUnionType?,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {
    init {
        check(components.size >= 2) { "a union has at least two components" }
        check(components.none { it.unionedComponents().size > 1 }) { "the components of a union are flattened in ${Companion::ofComponents.name}" }
        check(components.none { it.isNullable && it !is TypeVariable }) { "the nullability of a union is decided in ${Companion::ofComponents.name}" }
    }

    override val span = astNode?.span ?: components.firstNotNullOfOrNull { it.span }
    override val isNullable get() = components.any { it.isNullable }

    /** what the components have in common: `mut A | const B` is referred to as `read` */
    override val mutability: TypeMutability = components.asSequence().map { it.mutability }.reduce(TypeMutability::union)
    override val assignmentMutability: TypeMutability = components.asSequence().map { it.assignmentMutability }.reduce(TypeMutability::union)
    override val simpleName get() = components.joinToString(separator = " ${Operator.PIPE.text} ", transform = { it.simpleName ?: it.toString() })
    override val isNonNullableNothing get() = components.all { it.isNonNullableNothing }

    override val baseTypeOfLowerBound by lazy {
        BoundBaseType.closestCommonSupertypeOf(components.map { it.baseTypeOfLowerBound })
    }

    /**
     * The members of a union are those every component has: the ones of the closest common supertype of the components.
     */
    private val commonSupertype: BoundTypeReference by lazy {
        components
            .map { if (it is TypeVariable) it.asGeneric else it }
            .reduce { carry, component -> carry.closestCommonSupertypeWith(component) }
    }

    override val isPartiallyUnresolved get() = components.any { it.isPartiallyUnresolved }
    override val mentionsTypeVariables: Boolean get() = components.any { it.mentionsTypeVariables }
    override fun mentionsTypeVariable(parameter: BoundTypeParameter): Boolean = components.any { it.mentionsTypeVariable(parameter) }
    override fun mentionsTypeParameter(parameter: BoundTypeParameter): Boolean = components.any { it.mentionsTypeParameter(parameter) }
    override val mentionsTypeParameters: Boolean get() = components.any { it.mentionsTypeParameters }
    // one component that is read in all instantiations makes the common mutability read, whatever the others are bound to
    override val isReadInAllInstantiations: Boolean get() = components.any { it.isReadInAllInstantiations }
    // the mutability of the reference is known only where that of each component is
    override val isOrIntersectsGenericTypeReference: Boolean get() = components.any { it.isOrIntersectsGenericTypeReference }
    override fun mayBeTokenUnless(nonTokenParameters: Collection<BoundTypeParameter>) = components.any { it.mayBeTokenUnless(nonTokenParameters) }

    override val inherentTypeBindings: TypeUnification get() = commonSupertype.inherentTypeBindings

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.defaultMutabilityTo(mutability) }
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutability(mutability) }
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutabilityUnionedWith(mutability) }
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return mapComponents { it.withMutabilityLimitedTo(limitToMutability) }
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return when (nullability) {
            TypeReference.Nullability.UNSPECIFIED -> this
            TypeReference.Nullability.NOT_NULLABLE -> if (isNullable) mapComponents { it.withCombinedNullability(nullability) } else this
            TypeReference.Nullability.NULLABLE -> NullableTypeReference(this)
        }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        components.forEach { it.validate(forUsage, diagnosis) }

        if (astNode != null) {
            val simplified = simplify()
            if (simplified !== this) {
                diagnosis.simplifiableUnionType(astNode, simplified)
            }
        }
    }

    /** the union of both: the least type above both, exactly */
    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return ofComponents(context, null, components + other.unionedComponents(), simplify = true)
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        return mapComponents { it.withTypeVariables(variables) }
    }

    /**
     * `Subtyping.unify_union` in the proofs
     */
    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification,
    ): TypeUnification {
        return when (assigneeType) {
            // each component of the assignee is a value of this union
            is BoundUnionTypeReference -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            is ErroneousType -> unify(assigneeType.asNothing, assignmentLocation, carry)
            is BoundIntersectionTypeReference -> {
                // every value of the intersection is one of each component, so one component below this union
                // suffices: `(A | B) & C` is below `A | B`. Where none is, a component of this union may take the
                // whole intersection
                val viaComponent = assigneeType.flippedUnify(this, assignmentLocation, carry) { "" }
                if (viaComponent.getErrorsNotIn(carry).none()) viaComponent else unifyWithComponents(assigneeType, assignmentLocation, carry)
            }
            is NullableTypeReference -> {
                if (!isNullable) {
                    return carry.plusDiagnostic(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign a possibly null value to a non-null reference", assignmentLocation)
                    )
                }
                unifyWithComponents(assigneeType, assignmentLocation, carry)
            }
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundTypeArgument -> unifyWithComponents(assigneeType, assignmentLocation, carry)
        }
    }

    /**
     * The first component that takes the assignee takes it for the union; the components that are type variables
     * come last, as they would take anything and get bound needlessly narrow. `Subtyping.union_body` in the proofs.
     */
    private fun unifyWithComponents(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        val (varComponents, nonVarComponents) = components.partition { it is TypeVariable }
        for (component in nonVarComponents + varComponents) {
            val candidate = component.unify(assigneeType, assignmentLocation, carry)
            if (candidate.getErrorsNotIn(carry).none()) {
                return candidate
            }
        }

        return carry.plusDiagnostic(ValueNotAssignableDiagnostic(
            this,
            assigneeType,
            "no component of $this takes a value of type $assigneeType",
            assignmentLocation,
        ))
    }

    /**
     * Unifies [targetType] with each component: a value of this union is one of any component, so each has to fit.
     * `Subtyping.union_flipped_unify` in the proofs.
     */
    fun flippedUnify(
        targetType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification,
    ): TypeUnification {
        var innerCarry = carry
        for (component in components) {
            val withComponent = targetType.unify(component, assignmentLocation, innerCarry)
            val error = withComponent.getErrorsNotIn(innerCarry).firstOrNull()
            if (error != null) {
                val reason = (error as? ValueNotAssignableDiagnostic)?.reason?.let { ": $it" } ?: ""
                return innerCarry.plusDiagnostic(ValueNotAssignableDiagnostic(
                    targetType,
                    this,
                    "the component $component of $this is not a subtype of $targetType$reason",
                    assignmentLocation,
                ))
            }
            innerCarry = withComponent
        }

        return innerCarry
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return unionMappedComponents { it.instantiateAllParameters(context) }
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return unionMappedComponents { it.instantiateFreeVariables(context) }
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return components.all { it.hasSameBaseTypeAs(other) }
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> = commonSupertype.findMemberVariable(name)

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> = commonSupertype.findMemberFunction(name)

    override fun possibleRuntimeTypes(): PossibleRuntimeTypes {
        val ofComponents = components.map {
            when (val possible = it.possibleRuntimeTypes()) {
                is PossibleRuntimeTypes.Open -> return possible
                is PossibleRuntimeTypes.Closed -> possible
            }
        }
        return PossibleRuntimeTypes.Closed(
            ofComponents.flatMapTo(LinkedHashSet()) { it.classes },
            ofComponents.any { it.includesNull },
        )
    }

    override fun asAstReference(): AstUnionType {
        if (astNode != null) {
            return astNode
        }

        val astComponents = components.map { it.asAstReference() }
        // components can come from different source files, of which there is no range
        val spans = astComponents.mapNotNull { it.span }.takeIf { spans -> spans.map { it.sourceFile }.distinct().size == 1 }
        return AstUnionType(astComponents, spans?.let { Span.range(*it.toTypedArray()) } ?: Span.UNKNOWN)
    }

    /**
     * @return a type of the same values with fewer components if possible: without the components that are subtypes
     * of another one (`A | Nothing` is `A`, `A | Any` is `Any`). May return `this`.
     */
    fun simplify(): BoundTypeReference {
        val newComponents = simplifyComponents() ?: return this
        newComponents.singleOrNull()?.let { return it }
        return BoundUnionTypeReference(context, null, newComponents)
    }

    /**
     * Removes the components that another one takes, both seen with the mutability of the union; the one kept takes
     * that mutability then, so that the union keeps its own: `mut A | read B` with `B : A` is `read A`.
     * @return null if nothing is to be removed
     */
    private fun simplifyComponents(): List<BoundTypeReference>? {
        val newComponents = components.toMutableList()
        var anyRemoved = false
        var subIndex = 0
        subs@while (subIndex < newComponents.size) {
            val sub = newComponents[subIndex]
            if (!sub.mentionsTypeVariables) {
                val subWithSelfMutability = sub.withMutability(mutability)
                for (superIndex in newComponents.indices) {
                    val superComponent = newComponents[superIndex]
                    if (superIndex == subIndex || superComponent.mentionsTypeVariables) {
                        continue
                    }
                    val superWithSelfMutability = superComponent.withMutability(mutability)
                    if (subWithSelfMutability isAssignableTo superWithSelfMutability) {
                        if (superComponent.mutability != superWithSelfMutability.mutability) {
                            newComponents[superIndex] = superWithSelfMutability
                        }
                        newComponents.removeAt(subIndex)
                        anyRemoved = true
                        continue@subs
                    }
                }
            }
            subIndex++
        }

        return if (anyRemoved) newComponents else null
    }

    /**
     * @return the union of the components, each transformed by [componentTransform]; `this` if none changed
     */
    private inline fun mapComponents(componentTransform: (BoundTypeReference) -> BoundTypeReference): BoundTypeReference {
        val mappedComponents = components.map(componentTransform)
        if (mappedComponents == components) {
            return this
        }

        return ofComponents(context, null, mappedComponents)
    }

    /**
     * Like [mapComponents] for instantiating; `Subtyping.union_instances` in the proofs: a component instantiated to a
     * variant type argument makes the union one: `out`, unless all are invariant; and what an `in`-variant one gives
     * out is known no closer than `read Any?`, which it becomes.
     */
    private inline fun unionMappedComponents(componentTransform: (BoundTypeReference) -> BoundTypeReference): BoundTypeReference {
        val mappedComponents = components.map(componentTransform)
        if (mappedComponents == components) {
            return this
        }

        if (mappedComponents.none { it is BoundTypeArgument }) {
            return ofComponents(context, null, mappedComponents, simplify = true)
        }

        val allInvariant = mappedComponents.all { it !is BoundTypeArgument || it.variance == TypeVariance.UNSPECIFIED }
        val variance = if (allInvariant) TypeVariance.UNSPECIFIED else TypeVariance.OUT
        val type = mappedComponents
            .map { component ->
                when {
                    component !is BoundTypeArgument -> component
                    component.variance == TypeVariance.IN -> context.swCtx.getTopType(component.span ?: Span.UNKNOWN)
                    else -> component.type
                }
            }
            .let { ofComponents(context, null, it, simplify = true) }
        if (variance == TypeVariance.UNSPECIFIED) {
            return type
        }

        return BoundTypeArgument(context, AstSpecificTypeArgument(variance, type.asAstReference()), variance, type)
    }

    private val _backendIr by lazy {
        val simplified = this.simplify()
        if (simplified !== this) {
            return@lazy simplified.toBackendIr()
        }

        IrUnionTypeImpl(
            components.map { it.toBackendIr() },
            this.isNullable,
            this.mutability.toBackendIr(),
        )
    }
    override fun toBackendIr(): IrType {
        return _backendIr
    }

    override fun toString() = components.joinToString(
        separator = " ${Operator.PIPE.text} ",
        transform = { component ->
            // an intersection binds tighter than a union, so it is unambiguous as it is; the parentheses are for the reader
            if (component is BoundIntersectionTypeReference) "($component)" else component.toString()
        },
    )

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BoundUnionTypeReference) return false

        return this.components == other.components
    }

    override fun hashCode(): Int {
        return components.hashCode()
    }

    companion object {
        /**
         * The union of [components]: the components flattened (`Subtyping.unioned_components`), the nullability pulled
         * out (`Subtyping.of_union`); the component alone if there is only one.
         */
        fun ofComponents(
            context: CTContext,
            ref: AstUnionType?,
            components: List<BoundTypeReference>,
            simplify: Boolean = false,
        ): BoundTypeReference {
            val flatComponents = components.flatMap { it.unionedComponents() }
            flatComponents.singleOrNull()?.let { return it }
            check(flatComponents.isNotEmpty()) { "a union has at least one component" }

            val isNullable = flatComponents.any { it.isNullable }
            var union: BoundTypeReference = BoundUnionTypeReference(
                context,
                ref,
                if (isNullable) flatComponents.map { it.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE) } else flatComponents,
            )
            if (simplify) {
                union = (union as BoundUnionTypeReference).simplify()
            }
            return if (isNullable) union.withCombinedNullability(TypeReference.Nullability.NULLABLE) else union
        }

        /**
         * The components of the union this type is, each nullable iff this type is; this type alone otherwise.
         * Unioning all of them amounts to unioning this type.
         */
        fun BoundTypeReference.unionedComponents(): List<BoundTypeReference> = when (this) {
            is BoundUnionTypeReference -> components
            is NullableTypeReference -> when (nested) {
                is BoundUnionTypeReference -> nested.components.map { it.withCombinedNullability(TypeReference.Nullability.NULLABLE) }
                else -> listOf(this)
            }
            else -> listOf(this)
        }
    }
}

private class IrUnionTypeImpl(
    override val components: List<IrType>,
    override val isNullable: Boolean,
    override val mutability: IrTypeMutability,
) : IrUnionType {
    override fun asNullable(): IrType {
        if (isNullable) {
            return this
        }
        return IrUnionTypeImpl(
            components.map { it.asNullable() },
            true,
            mutability,
        )
    }
}
