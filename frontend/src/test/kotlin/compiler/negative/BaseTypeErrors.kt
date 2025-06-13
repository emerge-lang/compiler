package compiler.compiler.negative

import compiler.diagnostic.ParametricDiamondInheritanceWithDifferentTypeArgumentsDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BaseTypeErrors : FreeSpec({
    "diamond inheritance with with parametric root type, given different type arguments" - {
        "one is a subtype of the other" {
            validateModule("""
                interface A<TA, XA> {}
                interface B<TB, XB> : A<TB, XB> {}
                interface C<TC, XC> : A<TC, XC> {}
                interface D : A<S32, UWord> & B<Any, UWord> {}
            """.trimIndent())
                .shouldFind<ParametricDiamondInheritanceWithDifferentTypeArgumentsDiagnostic> {
                    it.diamondRoot.canonicalName.toString() shouldBe "testmodule.A"
                    it.parameter.name.value shouldBe "TA"
                }
        }

        "disjoint types" {
            validateModule("""
                interface A<TA, XA> {}
                interface B<TB, XB> : A<TB, XB> {}
                interface C<TC, XC> : A<TC, XC> {}
                interface D : A<S32, UWord> & B<S64, UWord> {}
            """.trimIndent())
                .shouldFind<ParametricDiamondInheritanceWithDifferentTypeArgumentsDiagnostic> {
                    it.diamondRoot.canonicalName.toString() shouldBe "testmodule.A"
                    it.parameter.name.value shouldBe "TA"
                }
        }
    }
})