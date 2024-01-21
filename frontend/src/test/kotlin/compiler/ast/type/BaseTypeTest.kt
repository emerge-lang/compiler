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

package compiler.compiler.ast.type

import compiler.binding.type.BuiltinAny
import compiler.binding.type.BaseType
import compiler.binding.type.BuiltinNothing
import compiler.binding.type.BuiltinType
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BaseTypeTest : FreeSpec() { init {
    "Given a class hierarchy A; B: A; C : B" - {
        val typeA = fakeType("A")
        val typeB = fakeType("B", typeA)
        val typeC = fakeType("C", typeB)

        "then A is a subtype of A" {
            typeA.isSubtypeOf(typeA)
        }
        
        "Then B is a subtype of A" {
            typeB.isSubtypeOf(typeA)
        }
        "Then C is a subtype of A" {
            typeC.isSubtypeOf(typeA)
        }
        "Then B is a subtype of B" {
            typeB.isSubtypeOf(typeB)
        }
        "Then C is a subtype of B" {
            typeC.isSubtypeOf(typeB)
        }
        "Then C is a subtype of C" {
            typeA.isSubtypeOf(typeA)
        }
    }
    
    "Given a class hierarchy Z; A; B : A; C : A, D : B, E : B, F : A, Z; G: A, Z" - {
        val typeZ = fakeType("Z")
        val typeA = fakeType("A")
        val typeB = fakeType("B", typeA)
        val typeC = fakeType("C", typeA)
        val typeD = fakeType("D", typeB)
        val typeE = fakeType("E", typeB)
        val typeF = fakeType("F", typeA, typeZ)
        val typeG = fakeType("G", typeA, typeZ)

        "Then the closest common ancestor of" - {
            "B and A is A" {
                BaseType.closestCommonSupertypeOf(listOf(typeB, typeA)) shouldBe typeA
                BaseType.closestCommonSupertypeOf(listOf(typeA, typeB)) shouldBe typeA
            }

            "B and C is A" {
                BaseType.closestCommonSupertypeOf(listOf(typeB, typeC)) shouldBe typeA
                BaseType.closestCommonSupertypeOf(listOf(typeC, typeB)) shouldBe typeA
            }

            "D and E is B" {
                BaseType.closestCommonSupertypeOf(listOf(typeD, typeE)) shouldBe typeB
                BaseType.closestCommonSupertypeOf(listOf(typeE, typeD)) shouldBe typeB
            }

            "C and E is A" {
                BaseType.closestCommonSupertypeOf(listOf(typeC, typeE)) shouldBe typeA
                BaseType.closestCommonSupertypeOf(listOf(typeE, typeC)) shouldBe typeA
            }

            "F and G is Any" {
                BaseType.closestCommonSupertypeOf(listOf(typeF, typeG)) shouldBe BuiltinAny
                BaseType.closestCommonSupertypeOf(listOf(typeG, typeF)) shouldBe BuiltinAny
            }
        }
    }

    "Nothing" - {
        "is a subtype of all builtin types, including itself" - {
            BuiltinType.getNewSourceFile().context.types.forEach { builtinType ->
                "Nothing is subtype of $builtinType" {
                    BuiltinNothing.isSubtypeOf(builtinType) shouldBe true
                }
            }
        }

        "is not a subtype of all other builtin types" - {
            BuiltinType.getNewSourceFile().context.types.except(BuiltinNothing).forEach { builtinType ->
                "$builtinType is not a subtype of Nothing" {
                    builtinType.isSubtypeOf(BuiltinNothing) shouldBe false
                }
            }
        }

        "closest common supertype of any builtin type and Nothing is that builtin type" - {
            BuiltinType.getNewSourceFile().context.types.except(BuiltinNothing).forEach { builtinType ->
                "closest common supertype of Nothing and $builtinType is $builtinType" {
                    BaseType.closestCommonSupertypeOf(BuiltinNothing, builtinType) shouldBe builtinType
                    BaseType.closestCommonSupertypeOf(builtinType, BuiltinNothing) shouldBe builtinType
                }
            }
        }
    }
}}

fun <T> Iterable<T>.except(vararg es: T): Iterable<T> {
    val eSet = es.toSet()
    return asSequence().filter { it !in eSet }.asIterable()
}