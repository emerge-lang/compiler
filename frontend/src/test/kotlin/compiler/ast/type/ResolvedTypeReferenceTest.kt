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

import compiler.ast.type.TypeMutability
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class ResolvedTypeReferenceTest : FreeSpec() { init {
    "Given a type hierarchy A; B : A; C : A" - {
        val swCtx = validateModule("""
            interface A {}
            interface B : A {}
            interface C : A {}
        """.trimIndent())
            .shouldHaveNoDiagnostics()
            .first

        val typeA = swCtx.getTestType("A")
        val typeB = swCtx.getTestType("B")
        val typeC = swCtx.getTestType("C")

        val mutableA = typeA.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyA = mutableA.withMutability(TypeMutability.READONLY)
        val immutableA = readonlyA.withMutability(TypeMutability.IMMUTABLE)
        val exclusiveA = readonlyA.withMutability(TypeMutability.EXCLUSIVE)

        val mutableB = typeB.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyB = mutableB.withMutability(TypeMutability.READONLY)
        val immutableB = readonlyB.withMutability(TypeMutability.IMMUTABLE)

        val mutableC = typeC.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyC = mutableC.withMutability(TypeMutability.READONLY)
        val immutableC = readonlyC.withMutability(TypeMutability.IMMUTABLE)

        val readonlyNothing = swCtx.nothing.baseReference.withMutability(TypeMutability.READONLY)
        val mutableNothing = swCtx.nothing.baseReference.withMutability(TypeMutability.MUTABLE)
        val immutableNothing = swCtx.nothing.baseReference.withMutability(TypeMutability.IMMUTABLE)

        "the closest common ancestor of" - {
            "mut B and mut A is mut A" {
                mutableA.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableA) shouldBe mutableA
            }

            "mut B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "mut B and const A is read A" {
                immutableA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "read B and mut A is read A" {
                mutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "read B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "read B and const A is read A" {
                immutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "const B and mut A is read A" {
                mutableA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "const B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "const B and const A is const A" {
                immutableA.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableA) shouldBe immutableA
            }

            //----

            "mut B and mut C is mut A" {
                mutableC.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableC) shouldBe mutableA
            }

            "mut B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "mut B and const C is read A" {
                immutableC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "read B and mut C is read A" {
                mutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "read B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "read B and const C is read A" {
                immutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "const B and mut C is read A" {
                mutableC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "const B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "const B and const C is const A" {
                immutableC.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableC) shouldBe immutableA
            }
            
            // ----
            "mut A and read Nothing is read A" {
                mutableA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "mut A and mut Nothing is mut A" {
                mutableA.closestCommonSupertypeWith(mutableNothing) shouldBe mutableA
                mutableNothing.closestCommonSupertypeWith(mutableA) shouldBe mutableA
            }

            "const A and read Nothing is read A" {
                immutableA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "const A and const Nothing is const A" {
                immutableA.closestCommonSupertypeWith(immutableNothing) shouldBe immutableA
                immutableNothing.closestCommonSupertypeWith(immutableA) shouldBe immutableA
            }

            "exclusive A and read Nothing is read A" {
                exclusiveA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(exclusiveA) shouldBe readonlyA
            }
        }
    }
}}