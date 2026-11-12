package compiler.compiler.negative

import compiler.diagnostic.ConstTokenDiagnostic
import compiler.diagnostic.MissingTokenModifierDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.TokenInheritsNonTokenDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.matchers.types.shouldBeInstanceOf

/**
 * A token is an object that stands for state outside of itself; a `token class` makes them. A type says whether
 * its values are tokens (`token class`, `token interface`), are none (any other class, `NonToken` and what
 * inherits from it), or may be either (any other interface, `Any`). These are the rules that keep a token from
 * being forgotten or frozen.
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

        "token class cannot inherit from NonToken" {
            validateModule("""
                token class Clock : NonToken {}
            """.trimIndent())
                .shouldFind<TokenInheritsNonTokenDiagnostic> {
                    it.tokenTypeName shouldBe "Clock"
                }
        }

        "token class cannot implement an interface that inherits from NonToken" {
            validateModule("""
                interface Shape : NonToken {}
                token class Clock : Shape {}
            """.trimIndent())
                .shouldFind<TokenInheritsNonTokenDiagnostic> {
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
    }

    "an interface says nothing by default" - {
        "a token class and another class implement the same interface" {
            validateModule("""
                interface Named {
                    fn getName(self) -> String
                }
                token class Clock : Named {
                    override fn getName(self) -> String = "clock"
                }
                class Person : Named {
                    override fn getName(self) -> String = "person"
                }
                fn nameOf(n: read Named) -> String = n.getName()
                fn test(c: read Clock, p: read Person) {
                    nameOf(c)
                    nameOf(p)
                    a: read Any = c
                    b: read Any = p
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "through an intersection and through a bound" {
            validateModule("""
                interface Named {
                    fn getName(self) -> String
                }
                token interface SomeToken {}
                fn viaIntersection(t: read SomeToken & Named) -> String = t.getName()
                fn viaBound<T : SomeToken & Named>(t: T) -> String = t.getName()
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "no forgetting" - {
        "token class to NonToken" {
            validateModule("""
                token class Clock {}
                fn test(c: read Clock) {
                    a: read NonToken = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Clock is not a subtype of NonToken"
                }
        }

        "a class that is no token class is a NonToken" {
            validateModule("""
                class Plain {}
                fn test(p: read Plain) {
                    a: read NonToken = p
                    b: read NonToken? = p
                    c: read Any = a
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "Any to NonToken" {
            validateModule("""
                fn test(a: read Any) {
                    n: read NonToken = a
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Any is not a subtype of NonToken"
                }
        }

        "an interface to NonToken" {
            validateModule("""
                interface Named {}
                fn test(n: read Named) {
                    a: read NonToken = n
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Named is not a subtype of NonToken"
                }
        }

        "an interface that inherits from NonToken" {
            validateModule("""
                interface Shape : NonToken {}
                interface Square : Shape {}
                class UnitSquare : Square {}
                fn test(s: read Square) {
                    a: read NonToken = s
                    b: read Shape = UnitSquare()
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "narrowed with & NonToken" {
            validateModule("""
                interface Named {}
                class Person : Named {}
                fn test(n: read Named & NonToken, p: read Person) {
                    a: read NonToken = n
                    b: read Named & NonToken = p
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a token does not fit a type narrowed with & NonToken" {
            validateModule("""
                interface Named {}
                token class Clock : Named {}
                fn test(c: read Clock) {
                    n: read Named & NonToken = c
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "as an argument" {
            validateModule("""
                token class Clock {}
                fn observe(a: read NonToken) {}
                fn test(c: read Clock) {
                    observe(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "as a return value" {
            validateModule("""
                interface Named {}
                fn forget(n: read Named) -> read NonToken {
                    return n
                }
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "through a type argument: a box of tokens is no NonToken" {
            validateModule("""
                token class Clock {}
                class Box<T> {
                    value: T = init
                }
                fn test(b: read Box<read Clock>) {
                    n: read NonToken = b
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "a value of type read testmodule.Box<read testmodule.Clock> may be a token, and read NonToken cannot be one"
                }
        }

        "a box of what is no token is a NonToken" {
            validateModule("""
                class Plain {}
                class Box<T> {
                    value: T = init
                }
                fn test(b: read Box<read Plain>, c: read Box<S32>) {
                    n: read NonToken = b
                    m: read NonToken = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a type parameter may be bound to a token type" {
            validateModule("""
                token class Clock {}
                class Box<T> {
                    value: T = init
                }
                fn test(c: mut Clock) {
                    b = Box(c)
                    d: mut Clock = b.value
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "generic code cannot forget a T" {
            validateModule("""
                fn forget<T>(v: T) {
                    n: read NonToken? = v
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "generic code can forget a T : NonToken" {
            validateModule("""
                fn forget<T : NonToken>(v: T) {
                    n: read NonToken = v
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a token type does not fit T : NonToken" {
            validateModule("""
                token class Clock {}
                fn take<T : NonToken>(v: T) {}
                fn test(c: read Clock) {
                    take(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }
    }

    "a token is never frozen" - {
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

        "const reference to an interface is fine, and is no token" {
            validateModule("""
                interface Named {}
                class Holder {
                    name: const Named = init
                }
                fn test(n: const Named) {
                    h: const Holder = Holder(n)
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "an own value of a class freezes" {
            validateModule("""
                class Plain {}
                fn test() {
                    p: const Plain = Plain()
                    a: const Any = Plain()
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "an own value of an interface type does not freeze" {
            validateModule("""
                interface Named {}
                intrinsic fn create() -> own Named
                fn test() {
                    n: const Named = create()
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "a value of type own testmodule.Named may be a token, and a token cannot become const"
                }
        }

        "an own value of an interface type narrowed with & NonToken freezes" {
            validateModule("""
                interface Named {}
                intrinsic fn create() -> own Named & NonToken
                fn test() {
                    n: const Named = create()
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "an own box of tokens does not freeze" {
            validateModule("""
                token class Clock {}
                class Box<T> {
                    value: T = init
                }
                intrinsic fn create() -> own Box<mut Clock>
                fn test() {
                    b: const Box<mut Clock> = create()
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot become const"
                }
        }

        "generic code cannot freeze a T" {
            validateModule("""
                fn freeze<T>(v: own T) {
                    c: const T = v
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldContain "a token cannot become const"
                }
        }

        "generic code can freeze a T : NonToken" {
            validateModule("""
                fn freeze<T : NonToken>(v: own T) {
                    c: const T = v
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "variables default to mut where their type may be a token, to const otherwise" - {
        "inferred from an own token" {
            validateModule("""
                token class Clock {}
                fn test() {
                    c = Clock()
                    d: mut Clock = c
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "inferred from an own value of an interface type" {
            validateModule("""
                interface Named {}
                intrinsic fn create() -> own Named
                fn test() {
                    n = create()
                    m: mut Named = n
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

        "a variable of a class that is no token class still defaults to const" {
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

    "a class says what it holds" - {
        "member variable of a token type" {
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

        "member variable of an interface type" {
            validateModule("""
                interface Animal {}
                class Person {
                    pet: read Animal = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Person"
                }
        }

        "member variable of type Any" {
            validateModule("""
                class Holder {
                    value: read Any? = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Holder"
                }
        }

        "member variable with a type argument that may be a token" {
            validateModule("""
                interface Animal {}
                class Box<T> {
                    value: T = init
                }
                class Person {
                    pets: read Box<read Animal> = init
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic> {
                    it.baseType.name.value shouldBe "Person"
                }
        }

        "member variable with inferred type" {
            validateModule("""
                token class Clock {}
                class Timer {
                    clock = Clock()
                }
            """.trimIndent())
                .shouldFind<MissingTokenModifierDiagnostic>(allowMultiple = true) {
                    it.baseType.name.value shouldBe "Timer"
                }
        }

        "a token class holds what it likes" {
            validateModule("""
                interface Animal {}
                token class Clock {}
                token class Person {
                    pet: read Animal = init
                    clock: mut Clock = init
                    anything: read Any? = init
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a member variable of the type of a type parameter needs nothing" {
            validateModule("""
                class Box<T> {
                    value: T = init
                }
                class Pair<A, B> {
                    first: Box<A> = init
                    second: B = init
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "types that cannot be tokens need nothing" {
            validateModule("""
                interface Shape : NonToken {}
                interface Named {}
                class Plain {}
                class Holder {
                    shape: read Shape = init
                    plain: mut Plain = init
                    number: S32 = init
                    name: const Named = init
                    narrowed: read Named & NonToken = init
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "inheriting from NonToken narrows the member variables" - {
            "is accepted" {
                validateModule("""
                    interface Animal {}
                    class Dog : Animal {}
                    class Person : NonToken {
                        pet: read Animal = init
                    }
                    fn test(d: read Dog) {
                        p = Person(d)
                        n: read NonToken = p.pet
                        a: read Animal = p.pet
                        f: const Person = Person(d)
                    }
                """.trimIndent()) should haveNoDiagnostics()
            }

            "through an interface that inherits from it" {
                validateModule("""
                    interface Animal {}
                    interface Shape : NonToken {}
                    class Person : Shape {
                        pet: read Animal = init
                    }
                """.trimIndent()) should haveNoDiagnostics()
            }

            "the constructor does not take a token" {
                validateModule("""
                    interface Animal {}
                    token class Robot : Animal {}
                    class Person : NonToken {
                        pet: read Animal = init
                    }
                    fn test(r: read Robot) {
                        p = Person(r)
                    }
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic>()
            }

            "the constructor does not take what may be a token" {
                validateModule("""
                    interface Animal {}
                    class Person : NonToken {
                        pet: read Animal = init
                    }
                    fn test(a: read Animal) {
                        p = Person(a)
                    }
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic>()
            }

            "an assignment does not take what may be a token" {
                validateModule("""
                    interface Animal {}
                    class Person : NonToken {
                        var pet: read Animal = init
                    }
                    fn test(p: mut Person, a: read Animal) {
                        set p.pet = a
                    }
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic>()
            }
        }
    }

    "common supertype" - {
        "of a token and a value that is none is Any" {
            validateModule("""
                token class Clock {}
                class Plain {}
                fn test(c: read Clock, p: read Plain, cond: Bool) {
                    x = if cond c else p
                    a: read Any = x
                    n: read NonToken = x
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "Any is not a subtype of NonToken"
                }
        }

        "of two values that are no tokens is NonToken" {
            validateModule("""
                class Plain {}
                class Other {}
                fn test(o: read Other, p: read Plain, cond: Bool) {
                    x = if cond o else p
                    n: read NonToken = x
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "the rule holds of inferred types" - {
        // while a type variable is not bound, the rule doesn't judge the types that mention it. These are the
        // checks that come after the inference.
        "a box inferred to hold a token is no NonToken" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) {
                    n: read NonToken = Box(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "as a return value" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) -> read NonToken = Box(c)
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>(allowMultiple = true)
        }

        "as an argument" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) {
                    observe(Box(c))
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "nested" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) {
                    n: read NonToken = Box(Box(c))
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "through a generic function" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) {
                    n: read NonToken = id(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a type variable bound to a token and to what is none, token last" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock, p: read Plain) {
                    n: read NonToken = pick(p, c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a type variable bound to a token and to what is none, token first" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock, p: read Plain) {
                    n: read NonToken = pick(c, p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "with an explicit type argument" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: read Clock) {
                    n: read NonToken = id::<read Clock>(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a box inferred to hold a token does not freeze" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: mut Clock) {
                    n: const Any = Box(c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a box inferred to hold what may be a token does not freeze" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(a: read Any) {
                    n: const Box<read Any> = Box(a)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "an own value that may be a token is not inferred to be const" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test() {
                    b: mut Box<const Named> = Box(createNamed())
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "an own value that may be a token is not inferred to be const, by a parameter" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn take(b: read Box<const Named>) {}
                fn test() {
                    take(Box(createNamed()))
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a token does not fit a type variable with the bound NonToken" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn store<T : NonToken>(b: mut Box<T>, v: T) {}
                fn test(b: mut Box<read Any>, c: read Clock) {
                    store(b, c)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>(allowMultiple = true)
        }

        "a box inferred to hold what is no token is a NonToken" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(p: read Plain) {
                    n: read NonToken = Box(p)
                    m: read NonToken = Box(Box(3))
                    observe(Box(p))
                    o: read NonToken = id(p)
                    q: read NonToken = pick(p, 3)
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a box inferred to hold what is no token freezes" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test() {
                    n: const Any = Box(Plain())
                    m: const Box<const Plain> = Box(Plain())
                    o: const Box<S32> = Box(3)
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "a box inferred to hold a token is one, and defaults to mut" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test(c: mut Clock) {
                    x = Box(c)
                    y: mut Box<mut Clock> = x
                    a: read Any = Box(c)
                    z = id(c)
                    w: mut Clock = z
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "an own value that is no token is inferred to be const" {
            validateModule("""
                token class Clock {}
                class Plain {}
                interface Named {}
                class Box<T> {
                    value: T = init
                }
                fn id<T>(v: T) -> T = v
                fn pick<T>(a: T, b: T) -> T = a
                fn observe(n: read NonToken) {}
                intrinsic fn createNamed() -> own Named
                fn test() {
                    b: mut Box<const Plain> = Box(Plain())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "casts are not checked for tokens yet" {
        // a cast doesn't check type arguments at runtime, so it can forget a token; that is left to the day casts
        // become sound
        validateModule("""
            interface Animal {}
            interface Named {}
            interface Shape : NonToken {}
            class Dog : Animal {}
            class Box<T> {
                value: T = init
            }
            token interface Stream {}
            fn test(a: read Animal, any: read Any, s: read Stream) {
                d: read Dog = a as read Dog
                n = any as read NonToken
                sh = any as read Shape
                b = any as read Box<S32>
                named = s as read Named
                isNamed = s is Named
            }
        """.trimIndent()) should haveNoDiagnostics()
    }

    "a stack trace collector is obtained from the root and passed to fillStackTrace" {
        validateModule("""
            import emerge.platform.World
            import emerge.platform.StackTraceCollector
            read fn test(world: read World, e: mut Throwable) {
                collector = StackTraceCollector.create(world)
                e.fillStackTrace(collector)
            }
        """.trimIndent()) should haveNoDiagnostics()
    }

    "an address is read through an AddressSpace, which is obtained from the root" {
        validateModule("""
            import emerge.platform.World
            fn test(world: read World, value: Any) -> UWord {
                space = AddressSpace.create(world)
                return space.addressOf(value)
            }
        """.trimIndent()) should haveNoDiagnostics()
    }
})
