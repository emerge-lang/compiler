package compiler.compiler.binding.type

import compiler.compiler.negative.validateModule
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec

class WrapperMutabilityTests : FreeSpec({
    "playground" {
        val swCtx = validateModule("""
            import emerge.platform.panic
            
            class Inner {}
            class Outer {}
            
            fn wrapperCtor<A, I : Inner & A, O: Outer & A>(inner: I) -> O {
                panic("not implemented")
            }
            fn wrapperInvoker() {
                val inner: mut Inner = Inner()
                val b = wrapperCtor(inner)
            }
        """.trimIndent())
            .first

        val moduleCtx = swCtx.getRegisteredModule(CanonicalElementName.Package(listOf("testmodule")))
        val ctorFn = moduleCtx
            .sourceFiles
            .flatMap { it.context.getToplevelFunctionOverloadSetsBySimpleName("wrapperCtor") }
            .single()
            .overloads
            .single()
    }
})