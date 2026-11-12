package compiler.compiler.negative

import compiler.diagnostic.ConstTokenDiagnostic
import compiler.diagnostic.MissingTokenModifierDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.types.shouldBeInstanceOf

/**
 * A token type is one whose instances stand for state outside of themselves. The `token` modifier marks them;
 * these are the rules that keep a token visible in the type of every reference to it.
 */
class TokenErrors : FreeSpec({
    "declaration" - {
        "token class and token interface are accepted" {
            validateModule("""
                token interface Stream {
                    fn put(self: mut _, value: S32)
                }
                token class Sink : Stream {
                    var total: S32 = 0
                    override fn put(self: mut _, value: S32) {
                        set self.total = self.total + value
                    }
                }
                token class Decorator : Stream {
                    inner: mut Stream = init
                    override fn put(self: mut _, value: S32) {
                        self.inner.put(value)
                    }
                }
                fn test() {
                    sink: mut Sink = Sink()
                    stream: mut Stream = Decorator(sink)
                    stream.put(3)
                    readStream: read Stream = stream
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a token class needs neither a token member variable nor a token supertype" {
            validateModule("""
                token class Counters {
                    var requests: S32 = 0
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "token is still usable as a name where it is delimited" {
            validateModule("""
                fn test(`token`: S32) -> S32 = `token`
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "explicit propagation" - {
        "class implementing a token interface must be declared token" {
            validateModule("""
                token interface Stream {}
                class Sink : Stream {}
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Sink"
                    it.reason.shouldBeInstanceOf<MissingTokenModifierDiagnostic.Reason.Supertype>().supertype.simpleName shouldBe "Stream"
                }
        }

        "interface extending a token interface must be declared token" {
            validateModule("""
                token interface Stream {}
                interface BufferedStream : Stream {}
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "BufferedStream"
                }
        }

        "through a supertype that is not token itself" {
            validateModule("""
                token interface Stream {}
                interface Other {}
                class Sink : Other & Stream {}
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Sink"
                }
        }

        "class with a member variable of a token type must be declared token" {
            validateModule("""
                token class Clock {}
                class Timer {
                    clock: read Clock = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Timer"
                    it.reason.shouldBeInstanceOf<MissingTokenModifierDiagnostic.Reason.MemberVariable>().memberVariable.name shouldBe "clock"
                }
        }

        "nullable member variable" {
            validateModule("""
                token class Clock {}
                class Timer {
                    clock: read Clock? = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Timer"
                }
        }

        "member variable with inferred type" {
            validateModule("""
                token class Clock {}
                class Timer {
                    clock = Clock()
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Timer"
                }
        }

        "member variable of a type that is missing the modifier itself" {
            validateModule("""
                token interface Stream {}
                class Sink : Stream {}
                class Holder {
                    sink: read Sink = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic>(allowMultiple = true) {
                    it.baseType.name.value shouldBe "Holder"
                }
        }
    }

    "never const" - {
        "const reference to a token class" {
            validateModule("""
                token class Clock {}
                fn test(c: const Clock) {}
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "const reference to a token interface" {
            validateModule("""
                token interface Stream {}
                fn test(c: const Stream?) {}
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Stream"
                }
        }

        "const member variable" {
            validateModule("""
                token class Clock {}
                token class Timer {
                    clock: const Clock = init
                }
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "const return type" {
            validateModule("""
                token class Clock {}
                intrinsic fn getClock() -> const Clock
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "token class cannot be declared const" {
            validateModule("""
                token class Clock : const Any {}
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "token class cannot inherit const" {
            validateModule("""
                interface Value : const Any {}
                token class Clock : Value {}
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "own token does not freeze into an inferred const" {
            validateModule("""
                token class Clock {}
                class Plain {}
                fn takeConst<T : const Any>(v: T) {}
                fn test() {
                    takeConst(Plain())
                    takeConst(Clock())
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldContain "Clock"
                }
        }

        "non-token own still freezes" {
            validateModule("""
                class Plain {}
                fn test() {
                    p: const Plain = Plain()
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "variables of a token type default to mut where others default to const" - {
        "inferred from an own value" {
            validateModule("""
                token class Clock {}
                fn test() {
                    c = Clock()
                    d: mut Clock = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "inferred from a read value, stays read" {
            validateModule("""
                token class Clock {}
                fn test(p: read Clock) {
                    c = p
                    d: mut Clock = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read testmodule.Clock"
                }
        }

        "declared without mutability" {
            validateModule("""
                token class Clock {}
                fn test() {
                    c: Clock = Clock()
                    d: mut Clock = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "declared without mutability, read initializer" {
            validateModule("""
                token class Clock {}
                fn test(p: read Clock) {
                    c: Clock = p
                    d: read Clock = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "inferred base type" {
            validateModule("""
                token class Clock {}
                fn test() {
                    c: _ = Clock()
                    d: mut Clock = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "member variable with an initializer" {
            validateModule("""
                token class Clock {}
                token class Timer {
                    clock = Clock()
                }
                fn test() {
                    t = Timer()
                    d: mut Clock = t.clock
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "member variable initialized by the constructor is read, like that of any other type" {
            validateModule("""
                token class Clock {}
                token class Timer {
                    clock: Clock = init
                }
                fn test(c: mut Clock) {
                    t = Timer(c)
                    d: mut Clock = t.clock
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read testmodule.Clock"
                }
        }

        "non-token variables still default to const" {
            validateModule("""
                class Plain {}
                fn test() {
                    c = Plain()
                    d: mut Plain = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const testmodule.Plain"
                }
        }
    }

    "no forgetting" - {
        "token class to Any" {
            validateModule("""
                token class Clock {}
                fn test(c: read Clock) {
                    a: read Any = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Clock is a token type and Any is not; a token cannot be assigned to a non-token type"
                }
        }

        "own token to mut Any" {
            validateModule("""
                token class Clock {}
                fn test() {
                    a: mut Any = Clock()
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "nullable token to nullable Any" {
            validateModule("""
                token class Clock {}
                fn test(c: read Clock?) {
                    a: read Any? = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "token class to a non-token interface it implements" {
            validateModule("""
                interface Named {
                    fn name(self) -> String
                }
                token class Clock : Named {
                    override fn name(self) -> String = "clock"
                }
                fn test(c: read Clock) {
                    n: read Named = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Clock is a token type and Named is not; a token cannot be assigned to a non-token type"
                }
        }

        "as an argument" {
            validateModule("""
                token class Clock {}
                fn observe(a: read Any) {}
                fn test(c: read Clock) {
                    observe(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "as a return value" {
            validateModule("""
                token class Clock {}
                fn forget(c: read Clock) -> read Any {
                    return c
                }
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic> {
                    it.message shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "into a member variable of a non-token type" {
            validateModule("""
                token class Clock {}
                class Holder {
                    value: read Any = init
                }
                fn test(c: read Clock) {
                    h = Holder(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "to a plain type parameter" {
            validateModule("""
                token class Clock {}
                class Box<T> {
                    value: T = init
                }
                fn test(c: read Clock) {
                    b = Box(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "intersection with a token component to the non-token component" {
            validateModule("""
                interface Named {}
                token interface Stream {}
                fn test(v: read Stream & Named) {
                    n: read Named = v
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot be assigned to a non-token type"
                }
        }

        "token to a token supertype is fine" {
            validateModule("""
                token interface Stream {}
                token interface BufferedStream : Stream {}
                token class Sink : BufferedStream {}
                fn test(s: mut Sink) {
                    a: mut BufferedStream = s
                    b: mut Stream = a
                    c: read Stream = s
                    d: read Stream? = s
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "methods of a token class are callable" {
            validateModule("""
                token class Counters {
                    var requests: S32 = 0
                    fn increment(self: mut _) {
                        set self.requests = self.requests + 1
                    }
                    fn current(self) -> S32 = self.requests
                }
                fn test() -> S32 {
                    c = Counters()
                    c.increment()
                    return c.current()
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }
})
