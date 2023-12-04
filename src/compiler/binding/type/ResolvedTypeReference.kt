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
open class ResolvedTypeReference(
    val original: TypeReference,
    open val context: CTContext,
    val isNullable: Boolean,
    val baseType: BaseType,
) {
    val modifier: TypeModifier? = original.modifier ?: baseType.impliedModifier

    fun modifiedWith(modifier: TypeModifier): ResolvedTypeReference {
        // TODO: implement type modifiers
        return ResolvedTypeReference(original.modifiedWith(modifier), context, isNullable, baseType)
    }

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
                val origMod = original.modifier?.toString()?.lowercase()
                val baseMod = baseType.impliedModifier?.toString()?.lowercase()

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
    infix fun isAssignableTo(other: ResolvedTypeReference): Boolean {
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
        // TODO: how to resolve nullability on references with bounds? How about class/struct-level parameters
        // in methods (further limited / specified on the method level)?
        /*if (this.isExplicitlyNullable != other.isExplicitlyNullable && (this.isExplicitlyNullable && !other.isExplicitlyNullable)) {
            return false
        }*/

        // seems all fine
        return true
    }

    /**
     * Compares the two types when a value of this type should be referenced by the given type.
     * @return The hierarchic distance (see [BaseType.hierarchicalDistanceTo]) if the assignment is possible,
     *         null otherwise.
     */
    fun assignMatchQuality(other: ResolvedTypeReference): Int? =
        if (this isAssignableTo other)
            this.baseType.hierarchicalDistanceTo(other.baseType)
        else null

    private lateinit var _string: String
    override fun toString(): String {
        if (!this::_string.isInitialized) {
            var str = ""
            if (modifier != null) {
                str += modifier.name.lowercase() + " "
            }

            str += baseType.fullyQualifiedName.removePrefix(BuiltinType.DEFAULT_MODULE_NAME_STRING)

            // TODO: parameters

            when (original.nullability) {
                TypeReference.Nullability.NULLABLE -> str += '?'
                TypeReference.Nullability.NOT_NULLABLE -> str += '!'
                TypeReference.Nullability.UNSPECIFIED -> {}
            }

            this._string = str
        }

        return this._string
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ResolvedTypeReference

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
        fun closestCommonAncestorOf(types: List<ResolvedTypeReference>): ResolvedTypeReference {
            if (types.size == 0) throw IllegalArgumentException("At least one type must be provided")
            if (types.size == 1) return types[0]

            val typeModifiers = types.map { it.modifier ?: TypeModifier.MUTABLE }

            val modifier: TypeModifier

            when {
                typeModifiers.allEqual -> modifier = typeModifiers[0]
                types.any { it.modifier == TypeModifier.READONLY || it.modifier == TypeModifier.IMMUTABLE} -> modifier = TypeModifier.READONLY
                else -> modifier = TypeModifier.MUTABLE
            }

            return BaseType.closestCommonAncestorOf(types.map(ResolvedTypeReference::baseType))
                .baseReference(types[0].context)
                .modifiedWith(modifier)
        }

        fun closestCommonAncestorOf(vararg types: ResolvedTypeReference): ResolvedTypeReference {
            return closestCommonAncestorOf(types.asList())
        }
    }
}
