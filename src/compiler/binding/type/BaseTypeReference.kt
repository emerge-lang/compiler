package compiler.binding.type

import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

/**
 * A [TypeReference] with resolved [BaseType]
 */
open class BaseTypeReference(
    val original: TypeReference,
    open val context: CTContext,
    val baseType: BaseType
) : TypeReference(
    original.declaredName,
    original.isNullable,
    original.modifier,
    original.isInferred,
    original.declaringNameToken
) {
    override val modifier: TypeModifier? = original.modifier ?: baseType.impliedModifier

    override fun modifiedWith(modifier: TypeModifier): BaseTypeReference {
        // TODO: implement type modifiers
        return BaseTypeReference(original.modifiedWith(modifier), context, baseType)
    }

    override fun nonNull(): BaseTypeReference = BaseTypeReference(original.nonNull(), context, baseType)

    override fun nullable(): BaseTypeReference = BaseTypeReference(original.nullable(), context, baseType)

    override fun asInferred(): BaseTypeReference = BaseTypeReference(original.asInferred(), context, baseType)

    /**
     * Validates the type reference.
     *
     * @return Any reportings on the validated code
     */
    fun validate(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        // verify whether the modifier on the reference is compatible with the modifier on the type
        if (original.modifier != null && baseType.impliedModifier != null) {
            if (!(original.modifier!! isAssignableTo baseType.impliedModifier!!)) {
                val origMod = original.modifier?.toString()?.toLowerCase()
                val baseMod = baseType.impliedModifier?.toString()?.toLowerCase()

                reportings.add(Reporting.error(
                    "Cannot reference ${baseType.fullyQualifiedName} as $origMod; " +
                    "modifier $origMod is not assignable to the implied modifier $baseMod of ${baseType.simpleName}",
                    original.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN
                ))
            }
        }

        return reportings
    }

    /** @return Whether a value of this type can safely be referenced from a refence of the given type. */
    infix fun isAssignableTo(other: BaseTypeReference): Boolean {
        // this must be a subtype of other
        if (!(this.baseType isSubtypeOf other.baseType)) {
            return false
        }

        // the modifiers must be compatible
        val thisModifier = modifier ?: TypeModifier.MUTABLE
        val otherModifier = other.modifier ?: TypeModifier.MUTABLE
        if (!(thisModifier isAssignableTo otherModifier)) {
            return false
        }

        // void-safety:
        // other  this  isCompatible
        // T      T     true
        // T?     T     true
        // T      T?    false
        // T?     T?    true
        if (this.isNullable != other.isNullable && (this.isNullable && !other.isNullable)) {
            return false
        }

        // seems all fine
        return true
    }

    /**
     * Compares the two types when a value of this type should be referenced by the given type.
     * @return The hierarchic distance (see [BaseType.hierarchicalDistanceTo]) if the assignment is possible,
     *         null otherwise.
     */
    fun assignMatchQuality(other: BaseTypeReference): Int? =
        if (this isAssignableTo other)
            this.baseType.hierarchicalDistanceTo(other.baseType)
        else null

    override fun toString(): String {
        var str = ""
        if (modifier != null) {
            str += modifier!!.name.toLowerCase() + " "
        }

        return str + baseType.fullyQualifiedName
    }
}
