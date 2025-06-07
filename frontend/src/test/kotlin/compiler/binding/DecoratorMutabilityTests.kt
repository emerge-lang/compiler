package compiler.compiler.binding

import compiler.compiler.negative.shouldFind
import compiler.compiler.negative.validateModule
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class DecoratorMutabilityTests : FreeSpec({
    "can infer mutability of decorator object" - {
        "for single nested parameter" - {
            "infer mutable wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M>(n: _Nested) -> Wrapper & _M
                    
                    fn test() {
                        mutNested: mut Nested = Nested()
                        var wrapper = wrapperCtor(mutNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the mut Wrapper type was inferred correctly
                        it.sourceType.toString() shouldBe "mut testmodule.Wrapper"
                        it.targetType.toString() shouldBe "exclusive testmodule.Wrapper"
                    }
            }

            "infer const wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M>(n: _Nested) -> Wrapper & _M
                    
                    fn test() {
                        constNested: const Nested = Nested()
                        wrapper = wrapperCtor(constNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the const Wrapper type was inferred correctly
                        it.sourceType.toString() shouldBe "const testmodule.Wrapper"
                        it.targetType.toString() shouldBe "exclusive testmodule.Wrapper"
                    }
            }
        }

        "for two nested parameters" - {
            "infer mutable wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M>(n1: _Nested, n2: _Nested) -> Wrapper & _M
                    
                    fn test() {
                        mutNested: mut Nested = Nested()
                        var wrapper = wrapperCtor(mutNested, mutNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the mut Wrapper type was inferred correctly
                        it.sourceType.toString() shouldBe "mut testmodule.Wrapper"
                        it.targetType.toString() shouldBe "exclusive testmodule.Wrapper"
                    }
            }

            "infer const wrapper" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M>(n1: _Nested, n2: _Nested) -> Wrapper & _M
                    
                    fn test() {
                        constNested: const Nested = Nested()
                        wrapper = wrapperCtor(constNested, constNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the const Wrapper type was inferred correctly
                        it.sourceType.toString() shouldBe "const testmodule.Wrapper"
                        it.targetType.toString() shouldBe "exclusive testmodule.Wrapper"
                    }
            }

            "falls back to read wrapper for mut&const components" {
                validateModule("""
                    class Nested {}
                    interface Wrapper {}
                    intrinsic fn wrapperCtor<_M, _Nested : Nested & _M>(n1: _Nested, n2: _Nested) -> Wrapper & _M
                    
                    fn test() {
                        constNested: const Nested = Nested()
                        mutNested: mut Nested = Nested()
                        wrapper = wrapperCtor(constNested, mutNested)
                        trigger(wrapper)
                    }
                    fn trigger(p: exclusive Wrapper) {} 
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        // this checks that the const Wrapper type was inferred correctly
                        it.sourceType.toString() shouldBe "read testmodule.Wrapper"
                        it.targetType.toString() shouldBe "exclusive testmodule.Wrapper"
                    }
            }
        }
    }
})