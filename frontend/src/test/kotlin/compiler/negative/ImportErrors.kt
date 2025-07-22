package compiler.compiler.negative

import compiler.diagnostic.AmbiguousImportsDiagnostic
import compiler.diagnostic.AmbiguousTypeReferenceDiagnostic
import compiler.diagnostic.RedundantImportsDiagnostic
import compiler.diagnostic.UnresolvableImportDiagnostic
import compiler.diagnostic.UnresolvablePackageNameDiagnostic
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class ImportErrors : FreeSpec({
    "unresolvable unused import" - {
        "unknown package" {
            validateModule("""
                import foo.bar.unused
                
                fn foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldFind<UnresolvablePackageNameDiagnostic>()
        }

        "unknown symbol in known package" {
            validateModule("""
                import emerge.core.asdoghwegsdfas
                
                fn foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldFind<UnresolvableImportDiagnostic>()
        }
    }

    "ambiguous wildcard import on use" {
        validateModules(
            IntegrationTestModule.of("test.a", """
                package test.a
                
                export interface SomeType {}
            """.trimIndent()),
            IntegrationTestModule.of("test.b", """
                package test.b
                
                export interface SomeType {}
            """.trimIndent()),
            IntegrationTestModule.of(
                "test.c",
                """
                    package test.c
                    
                    import test.a.*
                    import test.b.*
                    
                    fn foo(p: SomeType) {}
                """.trimIndent(),
                uses = setOf(
                    CanonicalElementName.Package(listOf("test", "a")),
                    CanonicalElementName.Package(listOf("test", "b")),
                )
            ),
        )
            .shouldFind<AmbiguousTypeReferenceDiagnostic> {
                it.reference.simpleName shouldBe "SomeType"
                it.candidates should haveSize(2)
                it.candidates.forOne { candidate ->
                    candidate.toString() shouldBe "test.a.SomeType"
                }
                it.candidates.forOne { candidate ->
                    candidate.toString() shouldBe "test.b.SomeType"
                }
            }
    }

    "ambiguous imports" - {
        val exportingModuleA = IntegrationTestModule.of("module_a", """
            package module_a
            
            export interface I {}
            export interface AX {}
            export interface AY {}
        """.trimIndent())
        val exportingModuleB = IntegrationTestModule.of("module_b", """
            package module_b
            
            export interface I {}
            export interface BX {}
            export interface BY {}
        """.trimIndent())

        "single-symbol x single-symbol is ambiguous" {
            validateModules(
                exportingModuleA,
                exportingModuleB,
                IntegrationTestModule.of(
                    moduleName = "testmodule",
                    uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                    code = """
                        package testmodule
                        
                        import module_a.I
                        import module_b.I
                        
                        fn dummy() {}
                    """.trimIndent(),
                )
            )
                .shouldFind<AmbiguousImportsDiagnostic> { diag ->
                    diag.imports.forAll { import ->
                        import.declaredAt.sourceFile.packageName shouldBe CanonicalElementName.Package(listOf("testmodule"))
                    }
                    diag.commonSimpleName shouldBe "I"
                }
        }

        "single-symbol x multi-symbol is ambiguous" {
            validateModules(
                exportingModuleA,
                exportingModuleB,
                IntegrationTestModule.of(
                    moduleName = "testmodule",
                    uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                    code = """
                        package testmodule
                        
                        import module_a.I
                        import module_b.{BX, I, BY}
                        
                        fn dummy() {}
                    """.trimIndent(),
                )
            )
                .shouldFind<AmbiguousImportsDiagnostic> { diag ->
                    diag.imports.forAll { import ->
                        import.declaredAt.sourceFile.packageName shouldBe CanonicalElementName.Package(listOf("testmodule"))
                    }
                    diag.commonSimpleName shouldBe "I"
                }
        }

        "multi-symbol x multi-symbol is ambiguous" {
            validateModules(
                exportingModuleA,
                exportingModuleB,
                IntegrationTestModule.of(
                    moduleName = "testmodule",
                    uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                    code = """
                        package testmodule
                        
                        import module_a.{AX, AY, I}
                        import module_b.{BX, I, BY}
                        
                        fn dummy() {}
                    """.trimIndent(),
                )
            )
                .shouldFind<AmbiguousImportsDiagnostic> { diag ->
                    diag.imports.forAll { import ->
                        import.declaredAt.sourceFile.packageName shouldBe CanonicalElementName.Package(listOf("testmodule"))
                    }
                    diag.commonSimpleName shouldBe "I"
                }
        }

        "importing the same element twice is not ambiguous but redundant" - {
            "single-symbol x single-symbol" {
                validateModules(
                    exportingModuleA,
                    exportingModuleB,
                    IntegrationTestModule.of(
                        moduleName = "testmodule",
                        uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                        code = """
                            package testmodule
                            
                            import module_a.I
                            import module_a.I
                            import module_b.BX
                            
                            fn dummy() {}
                        """.trimIndent(),
                    )
                )
                    .shouldNotFind<AmbiguousImportsDiagnostic>()
                    .shouldFind<RedundantImportsDiagnostic> {
                        it.commonSimpleName shouldBe "I"
                    }
            }

            "single-symbol x multi-symbol" {
                validateModules(
                    exportingModuleA,
                    exportingModuleB,
                    IntegrationTestModule.of(
                        moduleName = "testmodule",
                        uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                        code = """
                            package testmodule
                            
                            import module_a.I
                            import module_a.{AX, I}
                            import module_b.BX
                            
                            fn dummy() {}
                        """.trimIndent(),
                    )
                )
                    .shouldNotFind<AmbiguousImportsDiagnostic>()
                    .shouldFind<RedundantImportsDiagnostic> {
                        it.commonSimpleName shouldBe "I"
                    }
            }

            "multi-symbol x multi-symbol" {
                validateModules(
                    exportingModuleA,
                    exportingModuleB,
                    IntegrationTestModule.of(
                        moduleName = "testmodule",
                        uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                        code = """
                            package testmodule
                            
                            import module_a.{I, AX}
                            import module_a.{AY, I}
                            
                            fn dummy() {}
                        """.trimIndent(),
                    )
                )
                    .shouldNotFind<AmbiguousImportsDiagnostic>()
                    .shouldFind<RedundantImportsDiagnostic> {
                        it.commonSimpleName shouldBe "I"
                    }
            }

            "one multi-symbol import" {
                validateModules(
                    exportingModuleA,
                    exportingModuleB,
                    IntegrationTestModule.of(
                        moduleName = "testmodule",
                        uses = setOf(exportingModuleA.moduleName, exportingModuleB.moduleName),
                        code = """
                            package testmodule
                            
                            import module_a.{I, AX, I}
                            
                            fn dummy() {}
                        """.trimIndent(),
                    )
                )
                    .shouldNotFind<AmbiguousImportsDiagnostic>()
                    .shouldFind<RedundantImportsDiagnostic> {
                        it.commonSimpleName shouldBe "I"
                    }
            }
        }
    }
})