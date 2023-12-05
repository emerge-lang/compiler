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
import compiler.reportings.ValueNotAssignableReporting

sealed interface ResolvedTypeReference {
    val context: CTContext
    val isNullable: Boolean
    val simpleName: String?

    /**
     * TODO: rename to mutability
     */
    val modifier: TypeModifier?

    fun modifiedWith(modifier: TypeModifier): ResolvedTypeReference

    /**
     * Validates the type reference.
     *
     * @return Any reportings on the validated code
     */
    fun validate(): Collection<Reporting>

    /**
     * Determines whether a value of type `this` can be assigned to a variable
     * of type [other].
     * @param assignmentLocation Will be used in the returned [Reporting]
     * @return `null` if the assignment is allowed, a reporting of level [Reporting.Level.ERROR] describing the
     * problem with the assignment in case it is not possible
     */
    fun evaluateAssignabilityTo(other: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting?

    /**
     * Compares the two types when a value of this type should be referenced by the given type.
     * @return The hierarchic distance (see [BaseType.hierarchicalDistanceTo]) if the assignment is possible,
     *         null otherwise.
     */
    fun assignMatchQuality(other: ResolvedTypeReference): Int?

    /**
     * @return `this` if the [modifier] set explicitly, a copy of `this` with the [modifier] set to [mutability] otherwise.
     */
    fun defaultMutabilityTo(mutability: TypeModifier?): ResolvedTypeReference

    /**
     * Finds the "greatest common denominator" of this type and the [other] type.
     * This method is associative:
     * * `a.closestCommonAncestorWith(b) == b.closestCommonAncestorWith(a)`
     * * `a.closestCommonAncestorWith(b).closestCommonAncestorWith(c) == b.closestCommonAncestorWith(c).closestCommonAncestorWith(a)`
     */
    fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference
}

infix fun ResolvedTypeReference.isAssignableTo(other: ResolvedTypeReference): Boolean {
    return evaluateAssignabilityTo(other, SourceLocation.UNKNOWN) == null
}