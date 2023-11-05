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

import compiler.binding.type.Any
import compiler.binding.type.BaseType
import io.kotest.assertions.throwables.shouldThrow
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

        "Then distance between A and A is 0" {
            typeA.hierarchicalDistanceTo(typeA) shouldBe 0
        }
        "Then distance between B and A is 1" {
            typeB.hierarchicalDistanceTo(typeA) shouldBe 1
        }
        "Then distance between C and A is 2" {
            typeC.hierarchicalDistanceTo(typeA) shouldBe 2
        }
        "Then distance between C and B is 1" {
            typeC.hierarchicalDistanceTo(typeB) shouldBe 1
        }

        "Then distance between A and C is undefined" {
            shouldThrow<IllegalArgumentException> {
                typeA.hierarchicalDistanceTo(typeB)
            }
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
                BaseType.closestCommonAncestorOf(listOf(typeB, typeA)) shouldBe typeA
                BaseType.closestCommonAncestorOf(listOf(typeA, typeB)) shouldBe typeA
            }

            "B and C is A" {
                BaseType.closestCommonAncestorOf(listOf(typeB, typeC)) shouldBe typeA
                BaseType.closestCommonAncestorOf(listOf(typeC, typeB)) shouldBe typeA
            }

            "D and E is B" {
                BaseType.closestCommonAncestorOf(listOf(typeD, typeE)) shouldBe typeB
                BaseType.closestCommonAncestorOf(listOf(typeE, typeD)) shouldBe typeB
            }

            "C and E is A" {
                BaseType.closestCommonAncestorOf(listOf(typeC, typeE)) shouldBe typeA
                BaseType.closestCommonAncestorOf(listOf(typeE, typeC)) shouldBe typeA
            }

            "F and G is Any" {
                BaseType.closestCommonAncestorOf(listOf(typeF, typeG)) shouldBe Any
                BaseType.closestCommonAncestorOf(listOf(typeG, typeF)) shouldBe Any
            }
        }
    }
}}