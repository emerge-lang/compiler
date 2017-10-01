package compiler.ast.type

import compiler.binding.type.Any
import compiler.binding.type.BaseType
import io.kotlintest.specs.FreeSpec

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
            typeA.hierarchicalDistanceTo(typeA) shouldEqual 0
        }
        "Then distance between B and A is 1" {
            typeB.hierarchicalDistanceTo(typeA) shouldEqual 1
        }
        "Then distance between C and A is 2" {
            typeC.hierarchicalDistanceTo(typeA) shouldEqual 2
        }
        "Then distance between C and B is 1" {
            typeC.hierarchicalDistanceTo(typeB) shouldEqual 1
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
                BaseType.closestCommonAncestorOf(typeB, typeA) shouldEqual typeA
                BaseType.closestCommonAncestorOf(typeA, typeB) shouldEqual typeA
            }

            "B and C is A" {
                BaseType.closestCommonAncestorOf(typeB, typeC) shouldEqual typeA
                BaseType.closestCommonAncestorOf(typeC, typeB) shouldEqual typeA
            }

            "D and E is B" {
                BaseType.closestCommonAncestorOf(typeD, typeE) shouldEqual typeB
                BaseType.closestCommonAncestorOf(typeE, typeD) shouldEqual typeB
            }

            "C and E is A" {
                BaseType.closestCommonAncestorOf(typeC, typeE) shouldEqual typeA
                BaseType.closestCommonAncestorOf(typeE, typeC) shouldEqual typeA
            }

            "F and G is Any" {
                BaseType.closestCommonAncestorOf(typeF, typeG) shouldEqual Any
                BaseType.closestCommonAncestorOf(typeG, typeF) shouldEqual Any
            }
        }
    }
}}