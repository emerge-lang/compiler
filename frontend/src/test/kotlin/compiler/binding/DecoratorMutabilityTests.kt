package compiler.compiler.binding

import compiler.compiler.negative.shouldFind
import compiler.compiler.negative.validateModule
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec

class DecoratorMutabilityTests : FreeSpec({
    "can infer mutability of decorator object" - {
        "for single nested parameter" - {
            "infer mutable wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M, _Wrapper : Wrapper & _M>(n: _Nested) -> _Wrapper
                    
                    fn test() {
                        mutNested: mut Nested = Nested()
                        var wrapper = wrapperCtor(mutNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the mut Wrapper type was inferred correctly
                        it.sourceType.toString() == "mut testmodule.Wrapper"
                        it.targetType.toString() == "exclusive testmodule.Wrapper"
                    }
            }

            "infer const wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M, _Wrapper : Wrapper & _M>(n: _Nested) -> _Wrapper
                    
                    fn test() {
                        constNested: const Nested = Nested()
                        wrapper = wrapperCtor(constNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the const Wrapper type was inferred correctly
                        it.sourceType.toString() == "const testmodule.Wrapper"
                        it.targetType.toString() == "exclusive testmodule.Wrapper"
                    }
            }
        }
    }
})