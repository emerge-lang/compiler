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

import compiler.binding.context.ModuleRootContext
import compiler.binding.type.ResolvedTypeReference
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BaseTypeReferenceTest : FreeSpec() { init {
    "Given a type hierarchy A; B : A; C : A, Z; D : A, Z; E : A, Z" - {
        val context = ModuleRootContext()
        val typeA = fakeType("A")
        val typeB = fakeType("B", typeA)
        val typeC = fakeType("C", typeA)

        val mutableA = typeA.baseReference(context).modifiedWith(TypeModifier.MUTABLE)
        val readonlyA = mutableA.modifiedWith(TypeModifier.READONLY)
        val immutableA = readonlyA.modifiedWith(TypeModifier.IMMUTABLE)

        val mutableB = typeB.baseReference(context).modifiedWith(TypeModifier.MUTABLE)
        val readonlyB = mutableB.modifiedWith(TypeModifier.READONLY)
        val immutableB = readonlyB.modifiedWith(TypeModifier.IMMUTABLE)

        val mutableC = typeC.baseReference(context).modifiedWith(TypeModifier.MUTABLE)
        val readonlyC = mutableC.modifiedWith(TypeModifier.READONLY)
        val immutableC = readonlyC.modifiedWith(TypeModifier.IMMUTABLE)

        "the closest common ancestor of" - {
            "mutable B and mutable A is mutable A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableA, mutableB) shouldBe mutableA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, mutableA) shouldBe mutableA
            }

            "mutable B and readonly A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyA, mutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, readonlyA) shouldBe readonlyA
            }

            "mutable B and immutable A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableA, mutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, immutableA) shouldBe readonlyA
            }

            "readonly B and mutable A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableA, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, mutableA) shouldBe readonlyA
            }

            "readonly B and readonly A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyA, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, readonlyA) shouldBe readonlyA
            }

            "readonly B and immutable A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableA, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, immutableA) shouldBe readonlyA
            }

            "immutable B and mutable A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableA, immutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, mutableA) shouldBe readonlyA
            }

            "immutable B and readonly A is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyA, immutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, readonlyA) shouldBe readonlyA
            }

            "immutable B and immutable A is immutable A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableA, immutableB) shouldBe immutableA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, immutableA) shouldBe immutableA
            }

            //----

            "mutable B and mutable C is mutable A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableC, mutableB) shouldBe mutableA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, mutableC) shouldBe mutableA
            }

            "mutable B and readonly C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyC, mutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, readonlyC) shouldBe readonlyA
            }

            "mutable B and immutable C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableC, mutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(mutableB, immutableC) shouldBe readonlyA
            }

            "readonly B and mutable C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableC, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, mutableC) shouldBe readonlyA
            }

            "readonly B and readonly C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyC, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, readonlyC) shouldBe readonlyA
            }

            "readonly B and immutable C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableC, readonlyB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(readonlyB, immutableC) shouldBe readonlyA
            }

            "immutable B and mutable C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(mutableC, immutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, mutableC) shouldBe readonlyA
            }

            "immutable B and readonly C is readonly A" {
                ResolvedTypeReference.closestCommonAncestorOf(readonlyC, immutableB) shouldBe readonlyA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, readonlyC) shouldBe readonlyA
            }

            "immutable B and immutable C is immutable A" {
                ResolvedTypeReference.closestCommonAncestorOf(immutableC, immutableB) shouldBe immutableA
                ResolvedTypeReference.closestCommonAncestorOf(immutableB, immutableC) shouldBe immutableA
            }
        }
    }
}}