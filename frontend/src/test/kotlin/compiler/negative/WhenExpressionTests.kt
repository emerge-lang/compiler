package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.OperatorNotDeclaredDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.UndefinedIdentifierDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class WhenExpressionTests : FreeSpec({
    "as a statement" {
        validateModule("""
            intrinsic fn sideEffect(n: S32)
            fn test(p: S32) {
                when p {
                    1 -> sideEffect(1)
                    2 -> {
                        sideEffect(2)
                        sideEffect(3)
                    }
                    else -> sideEffect(4)
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "as a statement without else" {
        validateModule("""
            intrinsic fn sideEffect(n: S32)
            fn test(p: S32) {
                when p {
                    1 -> sideEffect(1)
                    2 -> sideEffect(2)
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "as an expression" {
        validateModule("""
            fn test(p: String) -> S32 {
                x = when p {
                    "a" -> 1
                    "b" -> 2
                    else -> 3
                }
                return x
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "as a single-expression function body" {
        validateModule("""
            fn test(p: S32) -> String = when p {
                1 -> "a"
                else -> "b"
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "with only an else branch" {
        validateModule("""
            fn test(p: S32) -> S32 {
                return when p {
                    else -> 3
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "branches can return" {
        validateModule("""
            fn test(p: S32) -> S32 {
                when p {
                    1 -> return 10
                    2 -> {
                        return 20
                    }
                    else -> return 30
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "nested" {
        validateModule("""
            fn test(p: S32, q: S32) -> S32 {
                return when p {
                    1 -> when q {
                        1 -> 11
                        else -> 10
                    }
                    else -> when q {
                        1 -> 1
                        else -> 0
                    }
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "more than once in the same scope" {
        validateModule("""
            fn test(p: S32) -> S32 {
                a = when p {
                    1 -> 1
                    else -> 0
                }
                b = when p {
                    2 -> 1
                    else -> 0
                }
                return a + b
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "user-defined equals" {
        validateModule("""
            class Foo {
                n: S32 = init
                nothrow operator fn equals(self, borrow other: read Foo) -> Bool = self.n == other.n
            }
            fn test(borrow a: read Foo, borrow b: read Foo) -> S32 = when a {
                b -> 1
                else -> 0
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "does not consume the subject" {
        validateModule("""
            class Foo {
                n: S32 = init
                nothrow operator fn equals(self, borrow other: read Foo) -> Bool = self.n == other.n
            }
            intrinsic fn consume(p: own Foo)
            fn test(capture a: own Foo, borrow b: read Foo) {
                when a {
                    b -> {}
                }
                consume(a)
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "branch value is typed against the equals parameter" {
        validateModule("""
            fn test(p: S32) -> S32 = when p {
                "a" -> 1
                else -> 0
            }
        """.trimIndent())
            .shouldFind<ValueNotAssignableDiagnostic> {
                it.sourceType.toString() shouldBe "const String"
                it.targetType.toString() shouldBe "const S32"
            }
    }

    "equals not defined" {
        validateModule("""
            class Foo {}
            fn test(borrow a: read Foo, borrow b: read Foo) -> S32 = when a {
                b -> 1
                else -> 0
            }
        """.trimIndent())
            .shouldFind<OperatorNotDeclaredDiagnostic>()
    }

    "equals declared without operator modifier" {
        validateModule("""
            class Foo {
                fn equals(self, borrow other: read Foo) -> Bool = true
            }
            fn test(borrow a: read Foo, borrow b: read Foo) -> S32 = when a {
                b -> 1
                else -> 0
            }
        """.trimIndent())
            .shouldFind<FunctionMissingAttributeDiagnostic> {
                it.function.name shouldBe "equals"
                it.attribute should beInstanceOf<AstFunctionAttribute.Operator>()
            }
    }

    "branch types are unified" {
        validateModule("""
            fn test(p: S32) -> S32 = when p {
                1 -> 1
                else -> "b"
            }
        """.trimIndent())
            .shouldFind<ReturnTypeMismatchDiagnostic>()
    }

    "branches can mutate and capture the subject" {
        validateModule("""
            class Foo {
                var n: S32 = init
                nothrow operator fn equals(self, borrow other: read Foo) -> Bool = self.n == other.n
            }
            intrinsic fn mutate(borrow p: mut Foo)
            intrinsic fn consume(p: own Foo)
            fn test(capture a: own Foo, borrow b: read Foo) {
                when a {
                    b -> mutate(a)
                    else -> consume(a)
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "subject that is not a variable" {
        validateModule("""
            class Foo {
                var n: S32 = init
                nothrow operator fn equals(self, borrow other: read Foo) -> Bool = self.n == other.n
            }
            class Holder {
                foo: own Foo = init
            }
            intrinsic fn mutate(borrow p: mut Holder)
            fn test(capture h: own Holder, borrow b: read Foo) {
                when Foo(1) {
                    b -> {}
                }
                when h.foo {
                    b -> mutate(h)
                }
                mutate(h)
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "unknown subject" {
        validateModule("""
            fn test() -> S32 = when nope {
                else -> 1
            }
        """.trimIndent())
            .shouldFind<UndefinedIdentifierDiagnostic>()
    }
})
