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

import compiler.ast.type.TypeMutability.EXCLUSIVE
import compiler.ast.type.TypeMutability.IMMUTABLE
import compiler.ast.type.TypeMutability.MUTABLE
import compiler.lexer.Keyword
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability

/**
 * Models the mutability aspect of a type. The logic in this class works as if the enum instances were types
 * themselves, e.g.: [MUTABLE] is the set of all mutable objects, [IMMUTABLE] is the set of all immutable objects.
 * Hence, `MUTABLE.union(IMMUTABLE)` is the union-set of all mutable objects and all immutable objects; or, more simply,
 * the set of all [EXCLUSIVE] objects.
 */
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
     * |`MUTABLE`  |`EXCLUSIVE`|`MUTABLE`  |
     * |`READONLY` |`MUTABLE`  |`READONLY` |
     * |`READONLY` |`READONLY` |`READONLY` |
     * |`READONLY` |`IMMUTABLE`|`READONLY` |
     * |`READONLY` |`EXCLUSIVE`|`READONLY` |
     * |`IMMUTABLE`|`MUTABLE`  |`READONLY` |
     * |`IMMUTABLE`|`READONLY` |`READONLY` |
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE`|
     * |`IMMUTABLE`|`EXCLUSIVE`|`IMMUTABLE`|
     * |`EXCLUSIVE`|`MUTABLE`  |`MUTABLE`  |
     * |`EXCLUSIVE`|`READONLY` |`READONLY` |
     * |`EXCLUSIVE`|`IMMUTABLE`|`IMMUTABLE`|
     * |`EXCLUSIVE`|`EXCLUSIVE`|`EXCLUSIVE`|
     *
     * @return The [TypeMutability] that applies to the union of the sets of objects being described
     * by `this` and [other]. In other words: returns the mutability that expresses all abilities & guarantees that are
     * common to both `this` and [other].
     */
    fun union(other: TypeMutability?): TypeMutability = when {
        other == null || other == this -> this
        this == EXCLUSIVE -> other
        other == EXCLUSIVE -> this
        else -> READONLY
    }

    /**
     * When an object member with mutability `this` is accessed through a reference with mutability [limitingMutability],
     * the resulting value should have the mutability that is returned by this method. In other words: the mutability
     * of the object member (`this`) is limited to the mutability of the reference through which it is accessed ([limitingMutability]).
     */
    fun limitedTo(limitingMutability: TypeMutability?): TypeMutability {
        if (this == EXCLUSIVE) {
            // exclusive object members are not allowed, so this should never happen.
            // If it does happen still, READONLY mutability will limit the damage.
            return READONLY
        }

        if (limitingMutability == null) {
            return this
        }

        return when(this) {
            MUTABLE -> when(limitingMutability) {
                MUTABLE -> MUTABLE
                READONLY -> READONLY
                IMMUTABLE -> READONLY
                EXCLUSIVE -> MUTABLE
            }
            READONLY -> READONLY
            IMMUTABLE -> IMMUTABLE
            EXCLUSIVE -> error("unreachable")
        }
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
     * @return the [TypeMutability] that describes the intersection-set of `this` and [other]. In other words,
     * returns the mutability that describes the guarantees and constraints from both `this` and [other].
     */
    fun intersect(other: TypeMutability): TypeMutability = when(this) {
        MUTABLE -> when(other) {
            MUTABLE -> MUTABLE
            READONLY -> MUTABLE
            IMMUTABLE -> EXCLUSIVE
            EXCLUSIVE -> EXCLUSIVE
        }
        READONLY -> when(other) {
            READONLY -> READONLY
            IMMUTABLE -> IMMUTABLE
            else -> other.intersect(this)
        }
        IMMUTABLE -> when(other) {
            IMMUTABLE -> IMMUTABLE
            else -> other.intersect(this)
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
