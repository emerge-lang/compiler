package compiler.compiler.negative

import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.reportings.EntryNotAllowedInBaseTypeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class InterfaceErrors : FreeSpec({
    "constructors are not allowed" {
        validateModule("""
            interface Foo {
                constructor {
                }
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseTypeDefinition.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundClassConstructor>()
            }
    }

    "destructors are not allowed" {
        validateModule("""
            interface Foo {
                destructor {
                }
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseTypeDefinition.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundClassDestructor>()
            }
    }

    "member variables not allowed" {
        validateModule("""
            interface Foo {
                x: Int = 3
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseTypeDefinition.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundBaseTypeMemberVariable>()
            }
    }
})