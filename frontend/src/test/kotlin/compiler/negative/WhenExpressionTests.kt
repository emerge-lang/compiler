package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.diagnostic.*
import compiler.lexer.Keyword
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

    "without else" - {
        "as a value" {
            validateModule("""
                fn test(p: S32) -> S32 {
                    x = when p {
                        1 -> 1
                        2 -> 2
                    }
                    return x
                }
            """.trimIndent())
                .shouldFind<MissingElseBranchDiagnostic> {
                    it.keyword.keyword shouldBe Keyword.WHEN
                }
        }

        "as a value with an expected type" {
            validateModule("""
                fn test(p: S32) -> S32 = when p {
                    1 -> 1
                }
            """.trimIndent())
                .shouldFind<MissingElseBranchDiagnostic>()
        }

        "as a Unit value" {
            validateModule("""
                intrinsic fn sideEffect(n: S32)
                fn test(p: S32) = when p {
                    1 -> sideEffect(1)
                    2 -> sideEffect(2)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "as a statement, with branches that return" {
            validateModule("""
                fn test(p: S32) -> S32 {
                    when p {
                        1 -> return 1
                    }
                    when p {
                        2 -> {
                            return 2
                        }
                    }
                    return 0
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
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

    "named subject" - {
        "is accessible in the branches" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 = when x = compute() {
                    1 -> x + 10
                    2 -> {
                        y = x + 20
                        y
                    }
                    else -> x
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "is accessible in the branch values" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test(p: S32) -> S32 = when x = compute() {
                    x + p -> 1
                    else -> 0
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "with only an else branch" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 = when x = compute() {
                    else -> x
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "with a declared type" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 = when x: S32 = compute() {
                    1 -> x + 10
                    else -> x
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()

            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 = when x: String = compute() {
                    else -> 0
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const S32"
                    it.targetType.toString() shouldBe "const String"
                }
        }

        "is not accessible after the when" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 {
                    when x = compute() {
                        1 -> {}
                    }
                    return x
                }
            """.trimIndent())
                .shouldFind<UndefinedIdentifierDiagnostic> {
                    it.expr.value shouldBe "x"
                }
        }

        "the same name can be used by consecutive and nested whens" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() -> S32 {
                    when x = compute() {
                        1 -> return x
                    }
                    return when x = compute() {
                        2 -> when y = compute() {
                            3 -> x + y
                            else -> y
                        }
                        else -> x
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "cannot redeclare an existing variable" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test(x: S32) -> S32 = when x = compute() {
                    else -> x
                }
            """.trimIndent())
                .shouldFind<MultipleVariableDeclarationsDiagnostic>()
        }

        "is not re-assignable" {
            validateModule("""
                intrinsic fn compute() -> S32
                fn test() {
                    when x = compute() {
                        1 -> {
                            set x = 2
                        }
                    }
                }
            """.trimIndent())
                .shouldFind<IllegalAssignmentDiagnostic>()
        }

        "branches can mutate and capture it" {
            validateModule("""
                class Foo {
                    var n: S32 = init
                    nothrow operator fn equals(self, borrow other: read Foo) -> Bool = self.n == other.n
                }
                intrinsic fn mutate(borrow p: mut Foo)
                intrinsic fn consume(p: own Foo)
                fn test(borrow b: read Foo) {
                    when a: own Foo = Foo(1) {
                        b -> mutate(a)
                        else -> consume(a)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "without a subject" - {
        "as a statement" {
            validateModule("""
                intrinsic fn sideEffect(n: S32)
                fn test(p: S32, q: Bool) {
                    when {
                        p == 1 -> sideEffect(1)
                        q -> {
                            sideEffect(2)
                            sideEffect(3)
                        }
                        else -> sideEffect(4)
                    }
                    when {
                        p > 5 -> sideEffect(5)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "as an expression" {
            validateModule("""
                fn test(p: S32, q: S32) -> String = when {
                    p > q -> "greater"
                    p < q -> "less"
                    else -> "equal"
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "with only an else branch" {
            validateModule("""
                fn test() -> S32 = when {
                    else -> 3
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "nested in a when with a subject" {
            validateModule("""
                fn test(p: S32, q: Bool) -> S32 = when p {
                    1 -> when {
                        q -> 11
                        else -> 10
                    }
                    else -> 0
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "conditions must be Bool" {
            validateModule("""
                fn test(p: S32) -> S32 = when {
                    p -> 1
                    else -> 0
                }
            """.trimIndent())
                .shouldFind<ConditionNotBooleanDiagnostic>()
        }

        "as a value without else" {
            validateModule("""
                fn test(p: S32) -> S32 = when {
                    p == 1 -> 1
                }
            """.trimIndent())
                .shouldFind<MissingElseBranchDiagnostic> {
                    it.keyword.keyword shouldBe Keyword.WHEN
                }
        }

        "branch types are unified" {
            validateModule("""
                fn test(p: S32) -> S32 = when {
                    p == 1 -> 1
                    else -> "b"
                }
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }
    }

    "instanceof checks" {
        validateModule("""
            interface I {}
            class A : I {
                p1: S32 = 1
            }
            class B : I {
                p2: S32 = 2
            }
            
            fn test(p: I) -> S32 = when p {
                is A -> p.p1
                is B -> p.p2
                else -> 0
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "binary ops" {
        validateModule("""
            fn test(p: S32) -> UWord = when p {
                < 0 -> 0
                1 -> 100
                else -> 1
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }
})
