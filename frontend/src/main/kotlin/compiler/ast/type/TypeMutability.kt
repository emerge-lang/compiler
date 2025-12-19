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
    val allowsMutation: Boolean,
) {
    MUTABLE(Keyword.MUTABLE, allowsMutation = true),
    READONLY(Keyword.READONLY, allowsMutation = false),
    IMMUTABLE(Keyword.IMMUTABLE, allowsMutation = false),
    EXCLUSIVE(Keyword.EXCLUSIVE, allowsMutation = true),
    READCONST(Keyword.READCONST, allowsMutation = false),
    ;

    infix fun isAssignableTo(targetMutability: TypeMutability): Boolean = when (this) {
        EXCLUSIVE, targetMutability -> true
        READCONST -> false // only assignable to itself, checked above
        MUTABLE, IMMUTABLE -> targetMutability == READONLY || targetMutability == READCONST
        READONLY -> targetMutability == READCONST
    }

    /**
     * When multiple values can be assigned to one location, that multitude of options
     * can be reasoned about by [Iterable.fold]ing the [TypeMutability] with this method.
     *
     * If both are identical, the same value will be returned. Otherwise, the return value is [READCONST],
     * as it is makes the least guarantees about the value. Hence, this method is associative.
     *
     * |`this`     |[other]    |result      |
     * |-----------|-----------|------------|
     * |`MUTABLE`  |`MUTABLE`  |`MUTABLE`   |
     * |`MUTABLE`  |`READONLY` |`READONLY`  |
     * |`MUTABLE`  |`IMMUTABLE`|`READONLY`  |
     * |`MUTABLE`  |`EXCLUSIVE`|`MUTABLE`   |
     * |`MUTABLE`  |`READCONST`|`READDCONST`|
     * |`READONLY` |`MUTABLE`  |`READONLY`  |
     * |`READONLY` |`READONLY` |`READONLY`  |
     * |`READONLY` |`IMMUTABLE`|`READONLY`  |
     * |`READONLY` |`EXCLUSIVE`|`READONLY`  |
     * |`READONLY` |`READCONST`|`READDCONST`|
     * |`IMMUTABLE`|`MUTABLE`  |`READONLY`  |
     * |`IMMUTABLE`|`READONLY` |`READONLY`  |
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE` |
     * |`IMMUTABLE`|`EXCLUSIVE`|`IMMUTABLE` |
     * |`IMMUTABLE`|`READCONST`|`READDCONST`|
     * |`EXCLUSIVE`|`MUTABLE`  |`MUTABLE`   |
     * |`EXCLUSIVE`|`READONLY` |`READONLY`  |
     * |`EXCLUSIVE`|`IMMUTABLE`|`IMMUTABLE` |
     * |`EXCLUSIVE`|`EXCLUSIVE`|`EXCLUSIVE` |
     * |`EXCLUSIVE`|`READCONST`|`READDCONST`|
     * |`READCONST`|`MUTABLE`  |`READCONST` |
     * |`READCONST`|`READONLY` |`READCONST` |
     * |`READCONST`|`IMMUTABLE`|`READCONST` |
     * |`READCONST`|`EXCLUSIVE`|`READDCONST`|
     * |`READCONST`|`READCONST`|`READDCONST`|
     *
     * @return The [TypeMutability] that applies to the union of the sets of objects being described
     * by `this` and [other]. In other words: returns the mutability that expresses all abilities & guarantees that are
     * common to both `this` and [other].
     */
    fun union(other: TypeMutability?): TypeMutability = when {
        other == null || other == this -> this
        this == EXCLUSIVE -> other
        other == EXCLUSIVE -> this
        this == READCONST || other == READCONST -> READCONST
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
            // If it does happen still, READCONST mutability will limit the damage.
            assert(false) { "exclusive object member!!" }
            return READCONST
        }

        if (limitingMutability == null) {
            return this
        }

        return when(this) {
            MUTABLE -> when(limitingMutability) {
                MUTABLE -> MUTABLE
                READONLY -> READONLY
                IMMUTABLE -> READCONST
                EXCLUSIVE -> MUTABLE
                READCONST -> READCONST
            }
            READONLY -> when (limitingMutability) {
                READCONST,
                IMMUTABLE -> READCONST
                else -> READONLY
            }
            IMMUTABLE -> IMMUTABLE
            READCONST -> READCONST
            EXCLUSIVE -> error("unreachable")
        }
    }

    /**
     * |`this`     |[other]    |result     |
     * |-----------|-----------|-----------|
     * |`MUTABLE`  |`MUTABLE`  |`MUTABLE`  |
     * |`MUTABLE`  |`READONLY` |`MUTABLE`  |
     * |`MUTABLE`  |`IMMUTABLE`|`EXCLUSIVE`|
     * |`MUTABLE`  |`EXCLUSIVE`|`EXCLUSIVE`|
     * |`MUTABLE`  |`READCONST`|`READCONST`|
     * |`READONLY` |`MUTABLE`  |`MUTABLE`  |
     * |`READONLY` |`READONLY` |`READONLY` |
     * |`READONLY` |`IMMUTABLE`|`IMMUTABLE`|
     * |`READONLY` |`EXCLUSIVE`|`EXCLUSIVE`|
     * |`READONLY` |`READCONST`|`READONLY` |
     * |`IMMUTABLE`|`MUTABLE`  |??         |
     * |`IMMUTABLE`|`READONLY` |??         |
     * |`IMMUTABLE`|`IMMUTABLE`|`IMMUTABLE`|
     * |`IMMUTABLE`|`EXCLUSIVE`|`EXCLUSIVE`|
     * |`IMMUTABLE`|`READCONST`|`IMMUTABLE`|
     * |`EXCLUSIVE`|`MUTABLE`  |`EXCLUSIVE`|
     * |`EXCLUSIVE`|`READONLY` |`EXCLUSIVE`|
     * |`EXCLUSIVE`|`IMMUTABLE`|`EXCLUSIVE`|
     * |`EXCLUSIVE`|`EXCLUSIVE`|`EXCLUSIVE`|
     * |`EXCLUSIVE`|`READCONST`|`EXCLUSIVE`|
     * |`READCONST`|`MUTABLE`  |`MUTABLE`  |
     * |`READCONST`|`READONLY` |`READONLY` |
     * |`READCONST`|`IMMUTABLE`|`IMMUTABLE`|
     * |`READCONST`|`EXCLUSIVE`|`EXCLUSIVE`|
     * |`READCONST`|`READCONST`|`READCONST`|
     *
     * @return the [TypeMutability] that describes the intersection-set of `this` and [other]. In other words,
     * returns the mutability that describes the guarantees and constraints from both `this` and [other].
     */
    fun intersect(other: TypeMutability): TypeMutability = when(this) {
        READCONST -> other
        MUTABLE -> when(other) {
            MUTABLE -> MUTABLE
            READONLY -> MUTABLE
            IMMUTABLE -> EXCLUSIVE
            EXCLUSIVE -> EXCLUSIVE
            else -> other.intersect(this)
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
        READCONST -> IrTypeMutability.READCONST
    }

    override fun toString() = keyword.text
}
