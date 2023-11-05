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
import compiler.binding.context.MutableCTContext
import compiler.binding.type.BaseTypeReference
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
                BaseTypeReference.closestCommonAncestorOf(mutableA, mutableB) shouldBe mutableA
                BaseTypeReference.closestCommonAncestorOf(mutableB, mutableA) shouldBe mutableA
            }

            "mutable B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, mutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, readonlyA) shouldBe readonlyA
            }

            "mutable B and immutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, mutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, immutableA) shouldBe readonlyA
            }

            "readonly B and mutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableA, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, mutableA) shouldBe readonlyA
            }

            "readonly B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, readonlyA) shouldBe readonlyA
            }

            "readonly B and immutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, immutableA) shouldBe readonlyA
            }

            "immutable B and mutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableA, immutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, mutableA) shouldBe readonlyA
            }

            "immutable B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, immutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, readonlyA) shouldBe readonlyA
            }

            "immutable B and immutable A is immutable A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, immutableB) shouldBe immutableA
                BaseTypeReference.closestCommonAncestorOf(immutableB, immutableA) shouldBe immutableA
            }

            //----

            "mutable B and mutable C is mutable A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, mutableB) shouldBe mutableA
                BaseTypeReference.closestCommonAncestorOf(mutableB, mutableC) shouldBe mutableA
            }

            "mutable B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, mutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, readonlyC) shouldBe readonlyA
            }

            "mutable B and immutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, mutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, immutableC) shouldBe readonlyA
            }

            "readonly B and mutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, mutableC) shouldBe readonlyA
            }

            "readonly B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, readonlyC) shouldBe readonlyA
            }

            "readonly B and immutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, readonlyB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, immutableC) shouldBe readonlyA
            }

            "immutable B and mutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, immutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, mutableC) shouldBe readonlyA
            }

            "immutable B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, immutableB) shouldBe readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, readonlyC) shouldBe readonlyA
            }

            "immutable B and immutable C is immutable A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, immutableB) shouldBe immutableA
                BaseTypeReference.closestCommonAncestorOf(immutableB, immutableC) shouldBe immutableA
            }
        }
    }
}}