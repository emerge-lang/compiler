package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.reportings.IllegalFunctionAttributeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.types.shouldBeInstanceOf

class FunctionTypeErrors : FreeSpec({
    "cannot be declared external(C)" {
        // there's no good reason not to support this - but it takes effort which hasn't been spent yet
        validateModule("""
            fn foo(p: external(C) () -> Unit) {}
        """.trimIndent())
            .shouldReport<IllegalFunctionAttributeReporting> {
                it.attribute.shouldBeInstanceOf<AstFunctionAttribute.External>()
            }
    }

    "cannot be declared operator" {
        // there's no good reason not to support this - but it takes effort which hasn't been spent yet
        validateModule("""
            fn foo(p: operator () -> Unit) {}
        """.trimIndent())
            .shouldReport<IllegalFunctionAttributeReporting> {
                it.attribute.shouldBeInstanceOf<AstFunctionAttribute.Operator>()
            }
    }

    "cannot be declared override" {
        // there's no good reason not to support this - but it takes effort which hasn't been spent yet
        validateModule("""
            fn foo(p: override () -> Unit) {}
        """.trimIndent())
            .shouldReport<IllegalFunctionAttributeReporting> {
                it.attribute.shouldBeInstanceOf<AstFunctionAttribute.Override>()
            }
    }

    "cannot be declared intrinsic" {
        // there's no good reason not to support this - but it takes effort which hasn't been spent yet
        validateModule("""
            fn foo(p: intrinsic () -> Unit) {}
        """.trimIndent())
            .shouldReport<IllegalFunctionAttributeReporting> {
                it.attribute.shouldBeInstanceOf<AstFunctionAttribute.Intrinsic>()
            }
    }
})