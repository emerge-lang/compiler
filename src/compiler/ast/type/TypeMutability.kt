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

package compiler.ast.type

enum class TypeMutability(
    val isMutable: Boolean,
) {
    MUTABLE(isMutable =true),
    READONLY(isMutable = false),
    IMMUTABLE(isMutable = false),

    /**
     * Cannot be mentioned in source explicitly. Constructors have the return type exlcusive T
     * to carry the information that there is no other reference to the value, and it can safely
     * be assigned any of the other mutabilities.
     */
    EXCLUSIVE(isMutable = true),
    ;

    val exceptExclusive: TypeMutability
        get() = if (this == EXCLUSIVE) MUTABLE else this

    infix fun isAssignableTo(targetMutability: TypeMutability): Boolean =
        this == targetMutability
            ||
        when (this) {
            EXCLUSIVE -> true
            MUTABLE, IMMUTABLE -> targetMutability == READONLY
            READONLY -> false
        }

    /**
     * When multiple values can be assigned to one location, that multitude of options
     * can be reasoned about by [Iterable.fold]ing the [TypeMutability] with this method.
     *
     * If both are identical, the same value will be returned. Otherwise, the return value is [READONLY],
     * as it is makes the least guarantees about the value. Hence, this method is associative.
     *
     * |`this`     |[other]    |result     |
     * |-----------|-----------|-----------|
     * |`MUTABLE`  |`MUTABLE`  |`MUTABLE`  |
     * |`MUTABLE`  |`READONLY` |`READONLY` |
     * |`MUTABLE`  |`IMMUTABLE`|`READONLY` |
     * |`MUTABLE`  |`EXCLUSIVE`|`MUTABLE`  |
     * |`READONLY` |`MUTABLE`  |`READONLY` |
     * |`READONLY` |`READONLY` |`READONLY` |
     * |`READONLY` |`IMMUTABLE`|`READONLY` |
     * |`READONLY` |`EXCLUSIVE`|`READONLY` |
     * |`IMMUTABLE`|`MUTABLE`  |`READONLY` |
     * |`IMMUTABLE`|`READONLY` |`READONLY` |
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE`|
     * |`IMMUTABLE`|`EXCLUSIVE`|`IMMUTABLE`|
     */
    fun combinedWith(other: TypeMutability): TypeMutability = when {
        this == other -> this
        this == EXCLUSIVE -> other
        other == EXCLUSIVE -> this
        else -> READONLY
    }

    override fun toString() = name.lowercase()
}
