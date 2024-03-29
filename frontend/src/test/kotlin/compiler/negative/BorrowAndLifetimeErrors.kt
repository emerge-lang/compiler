package compiler.compiler.negative

import compiler.reportings.VariableUsedAfterLifetimeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BorrowAndLifetimeErrors : FreeSpec({
    "initializing a variable ends the lifetime" - {
        "use by reading member" {
            validateModule("""
                class Test {
                    m: Int = 0
                }
                fun test() -> Int {
                    v: exclusive _ = Test()
                    v2 = v
                    return v.m
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by writing member" {
            validateModule("""
                class Test {
                    m: Int = 0
                }
                fun test() -> Int {
                    v: exclusive _ = Test()
                    v2 = v
                    set v.m = 1
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by return" {
            validateModule("""
                class Test {}
                fun test() -> immutable Int {
                    v: exclusive _ = Test()
                    v2 = v
                    return v
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }
    }

    "assigning to a variable ends the lifetime" {
        validateModule("""
            class Test {}
            fun test() -> Test {
                var v2: immutable _ = Test()
                v: exclusive _ = Test()
                v2 = v
                return v
            }
            fun capture(p: immutable Test) {}
        """.trimIndent())
            .shouldReport<VariableUsedAfterLifetimeReporting> {
                it.variable.name.value shouldBe "v"
                it.lifetimeEndedMaybe shouldBe false
            }
    }

    "passing to capturing function parameter ends lifetime" {
        validateModule("""
            class Test {}
            fun test() -> Test {
                v: exclusive _ = Test()
                capture(v)
                return v
            }
            fun capture(p: immutable Test) {}
        """.trimIndent())
            .shouldReport<VariableUsedAfterLifetimeReporting> {
                it.variable.name.value shouldBe "v"
                it.lifetimeEndedMaybe shouldBe false
            }
    }

    "branching" - {
        "lifetime ended in then-only if" {
            validateModule("""
                class Test {}
                fun capture(p: Test) {}
                fun test(cond: Boolean) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    }
                    capture(v)
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe true
                }
        }

        "lifetime ended in one branch of if" {
            validateModule("""
                class Test {}
                fun capture(p: Test) {}
                fun test(cond: Boolean) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    } else {
                    }
                    capture(v)
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe true
                }
        }

        "lifetime ended in both branches of if" {
            validateModule("""
                class Test {}
                fun capture(p: Test) {}
                fun test(cond: Boolean) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    } else {
                        v3 = v
                    }
                    capture(v)
                }
            """.trimIndent())
                .shouldReport<VariableUsedAfterLifetimeReporting> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }
    }
})