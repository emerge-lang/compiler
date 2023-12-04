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

package compiler.reportings

import compiler.ast.type.TypeModifier
import compiler.binding.type.BaseTypeReference

/**
 * @return A description of why the types don't match. null if they match or the reason cannot be described / is unknown.
 */
internal fun typeMismatchReason(targetType: BaseTypeReference, sourceType: BaseTypeReference): String? {
    // type inheritance
    if (!(sourceType.baseType isSubtypeOf targetType.baseType)) {
        return "${sourceType.baseType.simpleName} is not a subtype of ${targetType.baseType.simpleName}"
    }

    // mutability
    val targetModifier = targetType.modifier ?: TypeModifier.MUTABLE
    val validatedModifier = sourceType.modifier ?: TypeModifier.MUTABLE
    if (!(validatedModifier isAssignableTo targetModifier)) {
        return "cannot assign ${validatedModifier.name.lowercase()} to ${targetModifier.name.lowercase()}"
    }

    // TODO: void-safety
    /*if (sourceType.isExplicitlyNullable && !targetType.isExplicitlyNullable) {
        return "cannot assign nullable value to non-null target"
    }*/

    return null
}

internal fun List<BaseTypeReference?>.typeTupleToString(): String = joinToString(
    prefix = "(",
    transform = { it?.simpleName ?: "<unknown type>" },
    postfix = ")",
)