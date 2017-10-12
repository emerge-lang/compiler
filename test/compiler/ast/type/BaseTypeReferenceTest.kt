package compiler.ast.type

import compiler.binding.context.MutableCTContext
import compiler.binding.type.BaseTypeReference
import io.kotlintest.matchers.shouldEqual
import io.kotlintest.specs.FreeSpec

class BaseTypeReferenceTest : FreeSpec() { init {
    "Given a type hierarchy A; B : A; C : A, Z; D : A, Z; E : A, Z" - {
        val context = MutableCTContext()
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
                BaseTypeReference.closestCommonAncestorOf(mutableA, mutableB) shouldEqual mutableA
                BaseTypeReference.closestCommonAncestorOf(mutableB, mutableA) shouldEqual mutableA
            }

            "mutable B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, mutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, readonlyA) shouldEqual readonlyA
            }

            "mutable B and immutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, mutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, immutableA) shouldEqual readonlyA
            }

            "readonly B and mutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableA, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, mutableA) shouldEqual readonlyA
            }

            "readonly B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, readonlyA) shouldEqual readonlyA
            }

            "readonly B and immutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, immutableA) shouldEqual readonlyA
            }

            "immutable B and mutable A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableA, immutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, mutableA) shouldEqual readonlyA
            }

            "immutable B and readonly A is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyA, immutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, readonlyA) shouldEqual readonlyA
            }

            "immutable B and immutable A is immutable A" {
                BaseTypeReference.closestCommonAncestorOf(immutableA, immutableB) shouldEqual immutableA
                BaseTypeReference.closestCommonAncestorOf(immutableB, immutableA) shouldEqual immutableA
            }

            //----

            "mutable B and mutable C is mutable A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, mutableB) shouldEqual mutableA
                BaseTypeReference.closestCommonAncestorOf(mutableB, mutableC) shouldEqual mutableA
            }

            "mutable B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, mutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, readonlyC) shouldEqual readonlyA
            }

            "mutable B and immutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, mutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(mutableB, immutableC) shouldEqual readonlyA
            }

            "readonly B and mutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, mutableC) shouldEqual readonlyA
            }

            "readonly B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, readonlyC) shouldEqual readonlyA
            }

            "readonly B and immutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, readonlyB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(readonlyB, immutableC) shouldEqual readonlyA
            }

            "immutable B and mutable C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(mutableC, immutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, mutableC) shouldEqual readonlyA
            }

            "immutable B and readonly C is readonly A" {
                BaseTypeReference.closestCommonAncestorOf(readonlyC, immutableB) shouldEqual readonlyA
                BaseTypeReference.closestCommonAncestorOf(immutableB, readonlyC) shouldEqual readonlyA
            }

            "immutable B and immutable C is immutable A" {
                BaseTypeReference.closestCommonAncestorOf(immutableC, immutableB) shouldEqual immutableA
                BaseTypeReference.closestCommonAncestorOf(immutableB, immutableC) shouldEqual immutableA
            }
        }
    }
}}