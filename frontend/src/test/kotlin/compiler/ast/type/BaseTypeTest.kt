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

import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.context.SoftwareContext
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.mockk.every
import io.mockk.mockk

class BaseTypeTest : FreeSpec() { init {
    val swCtx = mockk<SoftwareContext> {
        every { any } returns fakeType("Any")
        every { nothing } returns fakeType("Nothing")
        every { s32 } returns fakeType("S32")
    }

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
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeB, typeA)) shouldBe typeA
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeA, typeB)) shouldBe typeA
            }

            "B and C is A" {
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeB, typeC)) shouldBe typeA
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeC, typeB)) shouldBe typeA
            }

            "D and E is B" {
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeD, typeE)) shouldBe typeB
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeE, typeD)) shouldBe typeB
            }

            "C and E is A" {
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeC, typeE)) shouldBe typeA
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeE, typeC)) shouldBe typeA
            }

            "F and G is Any" {
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeF, typeG)) shouldBe swCtx.any
                BoundBaseTypeDefinition.closestCommonSupertypeOf(listOf(typeG, typeF)) shouldBe swCtx.any
            }
        }
    }

    "Nothing" - {
        "Nothing is subtype of all types" {
            swCtx.nothing.isSubtypeOf(swCtx.s32) shouldBe true
        }

        "no type is a subtype of nothing" {
            swCtx.s32.isSubtypeOf(swCtx.nothing) shouldBe false
        }

        "closest common supertype of any builtin type and Nothing is that builtin type" - {
            BoundBaseTypeDefinition.closestCommonSupertypeOf(swCtx.nothing, swCtx.s32) shouldBe swCtx.s32
            BoundBaseTypeDefinition.closestCommonSupertypeOf(swCtx.s32, swCtx.nothing) shouldBe swCtx.s32
        }
    }
}}