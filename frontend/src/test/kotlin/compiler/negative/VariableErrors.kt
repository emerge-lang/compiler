package compiler.compiler.negative

import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.CircularVariableInitializationDiagnostic
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.ExplicitOwnershipNotAllowedDiagnostic
import compiler.diagnostic.GlobalVariableNotInitializedDiagnostic
import compiler.diagnostic.IllegalAssignmentDiagnostic
import compiler.diagnostic.MultipleVariableDeclarationsDiagnostic
import compiler.diagnostic.TypeDeductionErrorDiagnostic
import compiler.diagnostic.UndefinedIdentifierDiagnostic
import compiler.diagnostic.UnknownTypeDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.VariableAccessedBeforeInitializationDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.types.shouldBeInstanceOf

class VariableErrors : FreeSpec({
    "toplevel" - {
        "Variable assignment type mismatch" {
            validateModule("""
                foo: S32 = false
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.canonicalName.toString() shouldBe "emerge.core.Bool"
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.canonicalName.toString() shouldBe "emerge.core.S32"
                }
        }

        "variable type must be known" {
            validateModule("""
                var foo
            """.trimIndent())
                .shouldFind<TypeDeductionErrorDiagnostic>()
        }

        "unknown declared type" {
            validateModule("""
                foo: Foo
            """.trimIndent())
                .shouldFind<UnknownTypeDiagnostic>()
        }

        "cannot declare ownership" {
            validateModule("""
                borrow x: String
            """.trimIndent())
                .shouldFind<ExplicitOwnershipNotAllowedDiagnostic>()
        }

        "circular type inference" {
            validateModule("""
                x = y
                y = x
            """.trimIndent())
                .shouldFind<CircularVariableInitializationDiagnostic>()
        }

        "circular initialization" {
            validateModule("""
                x: UWord = y
                y: UWord = x
            """.trimIndent())
                .shouldFind<CircularVariableInitializationDiagnostic>()
        }

        "double declare" - {
            "in single file" {
                validateModule("""
                    private x = 3
                    private x = 4
                """.trimIndent())
                    .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                        it.originalDeclaration.name.value shouldBe "x"
                    }
            }

            "in multiple files" - {
                "with visibility of more than the file" {
                    val file1 = IntegrationTestModule.of(
                        moduleName = "testmodule",
                        code = """
                            package testmodule
                            
                            x = 3
                        """.trimIndent()
                    ).parseAsOneSourceFileOfMultiple()

                    val file2 = IntegrationTestModule.of(
                        moduleName = "testmodule",
                        code = """
                            package testmodule
                            
                            x = 3
                        """.trimIndent()
                    ).parseAsOneSourceFileOfMultiple()

                    val swCtx = emptySoftwareContext(validate = false)
                    val module = swCtx.registerModule(file1.expectedPackageName, emptySet())
                    module.addSourceFile(file1)
                    module.addSourceFile(file2)

                    val diagnosis = CollectingDiagnosis()
                    swCtx.doSemanticAnalysis(diagnosis)
                    Pair(swCtx, diagnosis.findings.toList())
                        .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                            it.originalDeclaration.name.value shouldBe "x"
                        }
                }

                "with visibility limited to the respective files" {
                    val file1 = IntegrationTestModule.of(
                        moduleName = "testmodule",
                        code = """
                            package testmodule
                            
                            private x = 3
                        """.trimIndent()
                    ).parseAsOneSourceFileOfMultiple()

                    val file2 = IntegrationTestModule.of(
                        moduleName = "testmodule",
                        code = """
                            package testmodule
                            
                            private x = 3
                        """.trimIndent()
                    ).parseAsOneSourceFileOfMultiple()

                    val swCtx = emptySoftwareContext(validate = false)
                    val module = swCtx.registerModule(file1.expectedPackageName, emptySet())
                    module.addSourceFile(file1)
                    module.addSourceFile(file2)

                    val diagnosis = CollectingDiagnosis()
                    swCtx.doSemanticAnalysis(diagnosis)
                    Pair(swCtx, diagnosis.findings.toList())
                        .shouldNotFind<MultipleVariableDeclarationsDiagnostic>()
                }
            }
        }
    }

    "in function" - {
        "cannot assign to final variable" {
            validateModule("""
                fn foo() {
                    a = 3
                    set a = 5
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "cannot assign to a type" {
            validateModule("""
                fn foo() {
                    set S32 = 3
                }
            """.trimIndent())
                .shouldFind<UndefinedIdentifierDiagnostic>()
        }

        "cannot assign to literal" {
            validateModule("""
                fn foo() {
                    set false = 3
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()

            validateModule("""
                fn foo() {
                    set [1, 2] = 3
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()

            validateModule("""
                fn foo() {
                    set null = 3
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "cannot assign to not-null assertion" {
            validateModule("""
                fn foo() {
                    x: S32? = null
                    set x!! = 3
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "cannot assign to unary operator invocation" {
            validateModule("""
                fn foo() {
                    set -3 = 4
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "cannot assign to binary operator invocation" {
            validateModule("""
                fn foo() {
                    set 3 + 4 = 4
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "cannot assign to parameter" {
            validateModule("""
                fn foo(p: S32) {
                    set p = 2
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "variable declared multiple times" {
            validateModule("""
                fn foo() {
                    x = 3
                    a = 1
                    x = true
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                    it.originalDeclaration.name.value shouldBe "x"
                    it.additionalDeclaration.name.value shouldBe "x"
                }
        }

        "accessing undeclared variable" {
            validateModule("""
                x = y
            """.trimIndent())
                .shouldFind<UndefinedIdentifierDiagnostic> {
                    it.expr.value shouldBe "y"
                }
        }

        "unknown declared type" {
            validateModule("""
                fn test() {
                    foo: Foo
                }
            """.trimIndent())
                .shouldFind<UnknownTypeDiagnostic>()
        }

        "cannot declare ownership" {
            validateModule("""
                fn test() {
                    capture x: String
                }
            """.trimIndent())
                .shouldFind<ExplicitOwnershipNotAllowedDiagnostic>()
        }

        "assignment status tracking" - {
            "global variable must be assigned at declaration" {
                validateModule("""
                    a: S32
                """.trimIndent())
                    .shouldFind<GlobalVariableNotInitializedDiagnostic>()
            }

            "local final variable can be assigned after declaration and then accessed" {
                validateModule("""
                    fn bar(p: S32) {
                    }
                    fn foo() {
                        a: S32
                        bar(1)
                        set a = 3
                        bar(a)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "local final variable cannot be accessed before initialization" {
                validateModule("""
                    fn bar(p: S32) {}
                    fn foo() {
                        a: S32
                        bar(a)
                        set a = 3
                    }
                """.trimIndent())
                    .shouldFind<VariableAccessedBeforeInitializationDiagnostic>()
            }

            "local non-final variable can be assigned after declaration and then accessed, and reassigned" {
                validateModule("""
                    fn bar(p: S32) {
                    }
                    fn foo() {
                        var a: S32
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
                    fn bar(p: S32) {}
                    fn foo() {
                        var a: S32
                        bar(a)
                        a = 3
                    }
                """.trimIndent())
                    .shouldFind<VariableAccessedBeforeInitializationDiagnostic> {
                        it.maybeInitialized shouldBe false
                    }
            }

            "interaction with if expressions" - {
                "cannot access variable that is only maybe initialized" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        fn doStuff(p: S32) {}
                        read fn test() {
                            x: S32
                            if (random()) {
                                set x = 3
                            }
                            doStuff(x)
                        }
                    """.trimIndent())
                        .shouldFind<VariableAccessedBeforeInitializationDiagnostic> {
                            it.maybeInitialized shouldBe true
                        }
                }

                "accessing a variable that is initialized in two branches of an if-expression is okay" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        fn doStuff(p: S32) {}
                        read fn test() {
                            x: S32
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
                        read intrinsic fn random() -> Bool
                        fn doStuff(p: S32) {}
                        read fn test() {
                            x: S32
                            if (random()) {
                                set x = 3
                            }
                            set x = 4
                        }
                    """.trimIndent())
                        .shouldFind<IllegalAssignmentDiagnostic> {
                            it.message shouldContain "may have already been initialized"
                        }
                }
            }

            "interaction with while loops" - {
                "cannot access variable that is only maybe initialized" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        read fn test() {
                            var x: S32
                            while random() {
                                set x = 5
                            }
                            y = x
                        }
                    """.trimIndent())
                        .shouldFind<VariableAccessedBeforeInitializationDiagnostic> {
                            it.maybeInitialized shouldBe true
                            it.declaration.name.value shouldBe "x"
                        }
                }

                "cannot initialize single-assignment variable in loop" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        read fn test() {
                            x: S32
                            while random() {
                                set x = 5
                            }
                        }
                    """.trimIndent())
                        .shouldFind<IllegalAssignmentDiagnostic>()

                    validateModule("""
                        read intrinsic fn random() -> Bool
                        read fn test() {
                            x: S32
                            while random() {
                                y = 3
                                set x = 5
                            }
                        }
                    """.trimIndent())
                        .shouldFind<IllegalAssignmentDiagnostic>()
                }

                "execution uncertainty of loops doesn't persist to code after the loop" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        read fn test() {
                            x: S32
                            while random() {
                                unrelated = 3
                            }
                            set x = 5
                            y = x
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "execution uncertainty of loops doesn't affect nested loops" {
                    validateModule("""
                        read intrinsic fn random() -> Bool
                        read fn test() {
                            while random() {
                                x: S32
                                set x = 5
                                while random() {
                                    y = x
                                }
                                z = x
                            }
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }
            }

            "interaction with foreach loops" - {
                "cannot access variable that is only maybe initialized" {
                    validateModule("""
                        intrinsic fn getSomeArray() -> Array<S32>
                        fn test() {
                            var x: S32
                            while random() {
                                set x = 5
                            }
                            y = x
                        }
                    """.trimIndent())
                        .shouldFind<VariableAccessedBeforeInitializationDiagnostic> {
                            it.maybeInitialized shouldBe true
                            it.declaration.name.value shouldBe "x"
                        }
                }

                "cannot initialize single-assignment variable in loop" {
                    validateModule("""
                        intrinsic fn getSomeArray() -> Array<S32>
                        fn test() {
                            x: S32
                            foreach i in getSomeArray() {
                                set x = 5
                            }
                        }
                    """.trimIndent())
                        .shouldFind<IllegalAssignmentDiagnostic>()

                    validateModule("""
                        intrinsic fn getSomeArray() -> Array<S32>
                        fn test() {
                            x: S32
                            foreach i in getSomeArray() {
                                y = 3
                                set x = 5
                            }
                        }
                    """.trimIndent())
                        .shouldFind<IllegalAssignmentDiagnostic>()
                }

                "execution uncertainty of loops doesn't persist to code after the loop" {
                    validateModule("""
                        intrinsic fn getSomeArray() -> Array<S32>
                        fn test() {
                            x: S32
                            foreach i in getSomeArray() {
                                unrelated = 3
                            }
                            set x = 5
                            y = x
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "execution uncertainty of loops doesn't affect nested loops" {
                    validateModule("""
                        intrinsic fn getSomeArray() -> Array<S32>
                        fn test() {
                            foreach i in getSomeArray() {
                                x: S32
                                set x = 5
                                foreach j in getSomeArray() {
                                    y = x
                                }
                                z = x
                            }
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }
            }
        }
    }

    "shadowing" - {
        "in function - forbidden" {
            validateModule("""
                fn foo() {
                    a = 3
                    if true {
                        a = 3
                    }
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing parameter" {
            validateModule("""
                fn foo(a: S32) {
                    a = false
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing global" {
            validateModule("""
                a = 3
                fn foo() {
                    a = false
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - parameter shadowing global" {
            validateModule("""
                a = 3
                fn foo(a: Bool) {
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "generated constructor parameter shadowing global - ALLOWED" {
            validateModule("""
                x = 2
                class A {
                    x: String = init
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "scoping" - {
        "variable accessed outside of its scope" {
            validateModule("""
                fn foo() -> S32 {
                    if true {
                        a = 3
                    }
                    return a
                }
            """.trimIndent())
                .shouldFind<UndefinedIdentifierDiagnostic>()
        }
    }
})