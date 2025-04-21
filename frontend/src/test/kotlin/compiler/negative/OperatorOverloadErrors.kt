package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.OperatorNotDeclaredDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class OperatorOverloadErrors : FreeSpec({
    "unary minus not declared" {
        validateModule("""
            fn foo() {
                a = - false
            }
        """.trimIndent())
            .shouldFind<OperatorNotDeclaredDiagnostic>()
    }

    "binary plus not declared" {
        validateModule("""
            fn foo() {
                a = false + true
            }
        """.trimIndent())
            .shouldFind<OperatorNotDeclaredDiagnostic>()
    }

    "unary minus declared without operator modifier" {
        validateModule("""
            intrinsic fn unaryMinus(self: Bool) -> Bool
            fn foo() {
                x = -false
            }
        """.trimIndent())
            .shouldFind<FunctionMissingAttributeDiagnostic> {
                it.function.name shouldBe "unaryMinus"
                it.attribute should beInstanceOf<AstFunctionAttribute.Operator>()
            }
    }

    "index access read requires operator modifier" {
        validateModule("""
            class Foo {
                fn getAtIndex(self, index: UWord) {
                }
            }
            
            fn test() {
                v = Foo()
                y = v[3]
            }
        """.trimIndent())
            .shouldFind<FunctionMissingAttributeDiagnostic> {
                it.function.name shouldBe "getAtIndex"
                it.attribute should beInstanceOf< AstFunctionAttribute.Operator>()
            }
    }

    "index access write requires operator modifier" {
        validateModule("""
            class Foo {
                fn setAtIndex(self, index: UWord, value: S32) {
                }
            }
            
            fn test() {
                v = Foo()
                set v[3] = 5 
            }
        """.trimIndent())
            .shouldFind<FunctionMissingAttributeDiagnostic> {
                it.function.name shouldBe "setAtIndex"
                it.attribute should beInstanceOf< AstFunctionAttribute.Operator>()
            }
    }
})