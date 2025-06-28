package compiler.compiler.negative

import compiler.binding.type.TypeUnification
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.nulls.shouldNotBeNull

class InheritingMemberFnsWithParametricReceiver : FreeSpec({
    "foo" {
        val swCtx = useValidModule("""
            interface Extra {}
            interface A {
                fn copyWithExtra<S : A>(self: S) -> exclusive S
            }
            interface B : A {}
        """.trimIndent())
        val pkg = swCtx.getPackage(CanonicalElementName.Package(listOf("testmodule"))).shouldNotBeNull()
        val basetypeA = pkg.resolveBaseType("A").shouldNotBeNull()
        val basetypeB = pkg.resolveBaseType("B").shouldNotBeNull()

        val copyFn = basetypeA.resolveMemberFunction("copyWithExtra").shouldNotBeNull().single().overloads.single()
        val receiverTypeParam = copyFn.declaredTypeParameters.single()
        var unification = TypeUnification.forInferenceOf(copyFn.allTypeParameters)
        unification = unification.plusSubtypeConstraint(receiverTypeParam, basetypeB.baseReference, Span.UNKNOWN)
        println(unification)
    }
})