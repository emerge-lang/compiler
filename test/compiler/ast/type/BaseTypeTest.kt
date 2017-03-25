package compiler.ast.type

import compiler.binding.type.BaseType
import io.kotlintest.specs.BehaviorSpec

class BaseTypeTest : BehaviorSpec() { init {
    Given("a class hierarchy A <-- B <-- C <-- D") {
        val typeA = object : BaseType { }
        val typeB = object : BaseType { override val superTypes = setOf(typeA) }
        val typeC = object : BaseType { override val superTypes = setOf(typeB) }

        Then("A is a subtype of A") {
            typeA.isSubtypeOf(typeA)
        }
        Then("B is a subtype of A") {
            typeB.isSubtypeOf(typeA)
        }
        Then("C is a subtype of A") {
            typeC.isSubtypeOf(typeA)
        }
        Then("B is a subtype of B") {
            typeB.isSubtypeOf(typeB)
        }
        Then("C is a subtype of B") {
            typeC.isSubtypeOf(typeB)
        }
        Then("C is a subtype of C") {
            typeA.isSubtypeOf(typeA)
        }

        Then("distance between A and A is 0") {
            typeA.hierarchicalDistanceTo(typeA) shouldEqual 0
        }
        Then("distance between B and A is 1") {
            typeB.hierarchicalDistanceTo(typeA) shouldEqual 1
        }
        Then("distance between C and A is 2") {
            typeC.hierarchicalDistanceTo(typeA) shouldEqual 2
        }
        Then("distance between C and B is 1") {
            typeC.hierarchicalDistanceTo(typeB) shouldEqual 1
        }

        Then("distance between A and C is undefined") {
            shouldThrow<IllegalArgumentException> {
                typeA.hierarchicalDistanceTo(typeB)
            }
        }
    }
}}