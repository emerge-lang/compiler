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

import compiler.lexer.Keyword
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability

enum class TypeMutability(
    val keyword: Keyword,
    val isMutable: Boolean,
) {
    MUTABLE(Keyword.MUTABLE, isMutable = true),
    READONLY(Keyword.READONLY, isMutable = false),
    IMMUTABLE(Keyword.IMMUTABLE, isMutable = false),
    EXCLUSIVE(Keyword.EXCLUSIVE, isMutable = true),
    ;

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
     * |`READONLY` |`MUTABLE`  |`READONLY` |
     * |`READONLY` |`READONLY` |`READONLY` |
     * |`READONLY` |`IMMUTABLE`|`READONLY` |
     * |`IMMUTABLE`|`MUTABLE`  |`READONLY` |
     * |`IMMUTABLE`|`READONLY` |`READONLY` |
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE`|
     */
    fun combinedWith(other: TypeMutability?): TypeMutability = when {
        other == null || other == this -> this
        this == EXCLUSIVE -> other
        other == EXCLUSIVE -> this
        else -> READONLY
    }

    /**
     * |`this`     |[other]    |result     |
     * |-----------|-----------|-----------|
     * |`MUTABLE`  |`MUTABLE`  |`MUTABLE`  |
     * |`MUTABLE`  |`READONLY` |`MUTABLE`  |
     * |`MUTABLE`  |`IMMUTABLE`|`MUTABLE`  |
     * |`READONLY` |`MUTABLE`  |`MUTABLE`  |
     * |`READONLY` |`READONLY` |`READONLY` |
     * |`READONLY` |`IMMUTABLE`|`IMMUTABLE`|
     * |`IMMUTABLE`|`MUTABLE`  |`EXCLUSIVE`|
     * |`IMMUTABLE`|`READONLY` |`IMMUTABLE`|
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE`|
     * @return mutability that allows for everything/guarantees for everything that any of `this` and [other] do:
     */
    fun conjunctionWith(other: TypeMutability): TypeMutability = when(this) {
        MUTABLE -> when (other) {
            MUTABLE -> MUTABLE
            READONLY -> MUTABLE
            IMMUTABLE -> EXCLUSIVE
            EXCLUSIVE -> EXCLUSIVE
        }
        READONLY -> when (other) {
            READONLY -> READONLY
            IMMUTABLE -> READONLY
            else -> other.conjunctionWith(this)
        }
        IMMUTABLE -> when (other) {
            IMMUTABLE -> IMMUTABLE
            else -> other.conjunctionWith(this)
        }
        EXCLUSIVE -> EXCLUSIVE
    }

    fun toBackendIr(): IrTypeMutability = when (this) {
        IMMUTABLE -> IrTypeMutability.EXCLUSIVE
        READONLY -> IrTypeMutability.READONLY
        MUTABLE -> IrTypeMutability.MUTABLE
        EXCLUSIVE -> IrTypeMutability.EXCLUSIVE
    }

    override fun toString() = keyword.text
}
