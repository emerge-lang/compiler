package compiler.compiler.negative

import compiler.diagnostic.AmbiguousTypeReferenceDiagnostic
import compiler.diagnostic.UnresolvableImportDiagnostic
import compiler.diagnostic.UnresolvablePackageNameDiagnostic
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
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
})