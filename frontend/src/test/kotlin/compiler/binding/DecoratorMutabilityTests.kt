package compiler.compiler.binding

import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec

class DecoratorMutabilityTests : FreeSpec({
    "can infer mutability of decorator object" {
        validateModule("""
            class Nested {}
            interface Wrapper {}
            intrinsic fn wrapperCtor<_M, _Nested : Nested & _M, _Wrapper : Wrapper & _M>(n: _Nested) -> _Wrapper
            
            fn test() {
                mN: mut Nested = Nested()
                mW: mut Wrapper = wrapperCtor(mN)
                trigger(mW)
            }
            fn trigger(p: exclusive Wrapper) {} 
        """.trimIndent())
            .shouldHaveNoDiagnostics()

        // TODO: this test has to fail; its just here to play around with the semantics
    }
})