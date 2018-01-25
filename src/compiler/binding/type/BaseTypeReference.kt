/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding.type

import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import kotlinext.allEqual

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
        val reportings = mutableSetOf<Reporting>()

        // verify whether the modifier on the reference is compatible with the modifier on the type
        if (original.modifier != null && baseType.impliedModifier != null) {
            if (!(original.modifier!! isAssignableTo baseType.impliedModifier!!)) {
                val origMod = original.modifier?.toString()?.toLowerCase()
                val baseMod = baseType.impliedModifier?.toString()?.toLowerCase()

                reportings.add(Reporting.modifierError(
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

        str += baseType.fullyQualifiedName

        if (isNullable) {
            str += "?"
        }

        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as BaseTypeReference

        if (baseType != other.baseType) return false
        if (modifier != other.modifier) return false

        return true
    }

    override fun hashCode(): Int {
        var result = baseType.hashCode()
        result = 31 * result + (modifier?.hashCode() ?: 0)
        return result
    }


    companion object {
        fun closestCommonAncestorOf(types: List<BaseTypeReference>): BaseTypeReference {
            if (types.size == 0) throw IllegalArgumentException("At least one type must be provided")
            if (types.size == 1) return types[0]

            val typeModifiers = types.map { it.modifier ?: TypeModifier.MUTABLE }

            val modifier: TypeModifier

            when {
                typeModifiers.allEqual -> modifier = typeModifiers[0]
                types.any { it.modifier == TypeModifier.READONLY || it.modifier == TypeModifier.IMMUTABLE} -> modifier = TypeModifier.READONLY
                else -> modifier = TypeModifier.MUTABLE
            }

            return BaseType.closestCommonAncestorOf(types.map(BaseTypeReference::baseType))
                .baseReference(types[0].context)
                .modifiedWith(modifier)
        }

        fun closestCommonAncestorOf(vararg types: BaseTypeReference): BaseTypeReference {
            return closestCommonAncestorOf(types.asList())
        }
    }
}
