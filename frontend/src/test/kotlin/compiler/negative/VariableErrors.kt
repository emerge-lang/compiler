package compiler.compiler.negative

import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.GlobalVariableNotInitializedReporting
import compiler.reportings.IllegalAssignmentReporting
import compiler.reportings.MultipleVariableDeclarationsReporting
import compiler.reportings.TypeDeductionErrorReporting
import compiler.reportings.UndefinedIdentifierReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.ValueNotAssignableReporting
import compiler.reportings.VariableAccessedBeforeInitializationReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.types.shouldBeInstanceOf

class VariableErrors : FreeSpec({
    "toplevel" - {
        "Variable assignment type mismatch" {
            validateModule("""
                foo: Int = false
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.fullyQualifiedName.toString() shouldBe "emerge.core.Boolean"
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.fullyQualifiedName.toString() shouldBe "emerge.core.Int"
                }
        }

        "variable type must be known" {
            validateModule("""
                var foo
            """.trimIndent())
                .shouldReport<TypeDeductionErrorReporting>()
        }

        "unknown declared type" {
            validateModule("""
                foo: Foo
            """.trimIndent())
                .shouldReport<UnknownTypeReporting>()
        }
    }

    "in function" - {
        "cannot assign to final variable" {
            validateModule("""
                fun foo() {
                    a = 3
                    set a = 5
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to a type" {
            validateModule("""
                fun foo() {
                    set Int = 3
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to value" {
            validateModule("""
                fun foo() {
                    set false  = 3
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to parameter" {
            validateModule("""
                fun foo(p: Int) {
                    set p = 2
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "variable declared multiple times" {
            validateModule("""
                fun foo() {
                    x = 3
                    a = 1
                    x = true
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "x"
                    it.additionalDeclaration.name.value shouldBe "x"
                }
        }

        "accessing undeclared variable" {
            validateModule("""
                x = y
            """.trimIndent())
                .shouldReport<UndefinedIdentifierReporting> {
                    it.expr.identifier.value shouldBe "y"
                }
        }

        "unknown declared type" {
            validateModule("""
                fun test() {
                    foo: Foo
                }
            """.trimIndent())
                .shouldReport<UnknownTypeReporting>()
        }

        "assignment status tracking" - {
            "global variable must be assigned at declaration" {
                validateModule("""
                    a: Int
                """.trimIndent())
                    .shouldReport<GlobalVariableNotInitializedReporting>()
            }

            "local final variable can be assigned after declaration and then accessed" {
                validateModule("""
                    fun bar(p: Int) {
                    }
                    fun foo() {
                        a: Int
                        bar(1)
                        set a = 3
                        bar(a)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "local final variable cannot be accessed before initialization" {
                validateModule("""
                    fun bar(p: Int) {}
                    fun foo() {
                        a: Int
                        bar(a)
                        set a = 3
                    }
                """.trimIndent())
                    .shouldReport<VariableAccessedBeforeInitializationReporting>()
            }

            "local non-final variable can be assigned after declaration and then accessed, and reassigned" {
                validateModule("""
                    fun bar(p: Int) {
                    }
                    fun foo() {
                        var a: Int
                        bar(1)
                        set a = 3
                        bar(a)
                        set a = 4
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "local non-final variable cannot be accessed before initialization" {
                validateModule("""
                    fun bar(p: Int) {}
                    fun foo() {
                        var a: Int
                        bar(a)
                        a = 3
                    }
                """.trimIndent())
                    .shouldReport<VariableAccessedBeforeInitializationReporting> {
                        it.maybeInitialized shouldBe false
                    }
            }

            "cannot access variable that is only maybe initialized" {
                validateModule("""
                    readonly intrinsic fun random() -> Boolean
                    fun doStuff(p: Int) {}
                    readonly fun test() {
                        x: Int
                        if (random()) {
                            set x = 3
                        }
                        doStuff(x)
                    }
                """.trimIndent())
                    .shouldReport<VariableAccessedBeforeInitializationReporting> {
                        it.maybeInitialized shouldBe true
                    }
            }

            "accessing a variable that is initialized in two branches of an if-expression is okay" {
                validateModule("""
                    readonly intrinsic fun random() -> Boolean
                    fun doStuff(p: Int) {}
                    readonly fun test() {
                        x: Int
                        if (random()) {
                            set x = 3
                        } else {
                            set x = 4
                        }
                        doStuff(x)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "assigning to a assign-once variable that maybe have already been initialized is not allowed" {
                validateModule("""
                    readonly intrinsic fun random() -> Boolean
                    fun doStuff(p: Int) {}
                    readonly fun test() {
                        x: Int
                        if (random()) {
                            set x = 3
                        }
                        set x = 4
                    }
                """.trimIndent())
                    .shouldReport<IllegalAssignmentReporting> {
                        it.message shouldContain "may have already been initialized"
                    }
            }
        }
    }

    "shadowing" - {
        "in function - forbidden" {
            validateModule("""
                fun foo() {
                    a = 3
                    if true {
                        a = 3
                    }
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing parameter" {
            validateModule("""
                fun foo(a: Int) {
                    a = false
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing global" {
            validateModule("""
                a = 3
                fun foo() {
                    a = false
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - parameter shadowing global" {
            validateModule("""
                a = 3
                fun foo(a: Boolean) {
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }
    }

    "scoping" - {
        "variable accessed outside of its scope" {
            validateModule("""
                fun foo() -> Int {
                    if true {
                        a = 3
                    }
                    return a
                }
            """.trimIndent())
                .shouldReport<UndefinedIdentifierReporting>()
        }
    }
})