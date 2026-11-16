package casts

import emerge.core.range.Iterable
import emerge.core.reflection.Type
import emerge.core.reflection.typeOf
import emerge.core.reflection.isSubtypeOf
import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

interface Animal {}
interface Named {}
class Dog : Animal & Named {}
class Cat : Animal {}

class Box<T> {
    v: T = init
}

interface Seq<E> {}
class Nest<E> : Seq<Box<E>> {
    v: E = init
}

token interface Stream {}
token class Channel : Stream & Named {}
interface Shape : NonToken {}
class Square : Shape {}
class Wrapper<T> : Named {
    v: T = init
}

fn show(stdout: mut PrintStream, what: String, result: Bool) {
    stdout.println(what + ": " + (if result "yes" else "no"))
}

// the type argument is known only at runtime
fn isA<T>(borrow value: Any?) -> Bool = value is T

fn isBoxOf<T>(borrow value: Any?) -> Bool = value is Box<T>

fn isMutDog(borrow value: read Any) -> Bool = value is mut Dog

// like isA, but with a mut reference to the value
fn isAThroughMut<T>(borrow value: mut Any) -> Bool = value is T

fn isBoth<A, B>(borrow value: Any?) -> Bool = value is A & B

// types that are put together at runtime
fn constOf<T>() -> const Type = typeOf::<const T>()
fn bothOf<A, B>() -> const Type = typeOf::<A & B>()

fn castTo<T>(value: Any) -> T = value as T

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    // type arguments are checked
    strings: Array<String> = ["a", "b"]
    stringsAny: Any = strings
    show(stdout, "Array<String> is Array<String>", stringsAny is Array<String>)
    show(stdout, "Array<String> is Array<S8>", stringsAny is Array<S8>)
    show(stdout, "Array<String> is Array<out Any>", stringsAny is Array<out Any>)
    show(stdout, "Array<String> is Array<Any>", stringsAny is Array<Any>)
    show(stdout, "Array<String> is Array<*>", stringsAny is Array<*>)
    show(stdout, "Array<String> is Iterable<String>", stringsAny is Iterable<String>)
    show(stdout, "Array<String> is Iterable<S32>", stringsAny is Iterable<S32>)
    noBytes: Array<S8>? = stringsAny as? Array<S8>
    show(stdout, "Array<String> as? Array<S8> is null", isNull(noBytes))
    bytes: Array<S8> = [1, 2, 3]
    bytesAny: Any = bytes
    stdout.println("Array<S8> as Array<S8>: " + (bytesAny as Array<S8>).size.toString() + " elements")

    // classes, variance, nested arguments
    dogBox: Any = Box::<Dog>(Dog())
    show(stdout, "Box<Dog> is Box<Dog>", dogBox is Box<Dog>)
    show(stdout, "Box<Dog> is Box<Cat>", dogBox is Box<Cat>)
    show(stdout, "Box<Dog> is Box<Animal>", dogBox is Box<Animal>)
    show(stdout, "Box<Dog> is Box<out Animal>", dogBox is Box<out Animal>)
    show(stdout, "Box<Dog> is Box<in Dog>", dogBox is Box<in Dog>)
    show(stdout, "Box<Dog> is Box<in Animal>", dogBox is Box<in Animal>)
    nested: Any = Box::<Box<Dog>>(Box::<Dog>(Dog()))
    show(stdout, "Box<Box<Dog>> is Box<Box<Dog>>", nested is Box<Box<Dog>>)
    show(stdout, "Box<Box<Dog>> is Box<Box<Cat>>", nested is Box<Box<Cat>>)
    show(stdout, "Box<Box<Dog>> is Box<out Box<out Animal>>", nested is Box<out Box<out Animal>>)
    show(stdout, "Box<Box<Dog>> is Box<Box<out Animal>>", nested is Box<Box<out Animal>>)

    // the type arguments of supertypes
    nest: Any = Nest::<Dog>(Dog())
    show(stdout, "Nest<Dog> is Seq<Box<Dog>>", nest is Seq<Box<Dog>>)
    show(stdout, "Nest<Dog> is Seq<Box<Cat>>", nest is Seq<Box<Cat>>)
    show(stdout, "Nest<Dog> is Seq<Dog>", nest is Seq<Dog>)
    show(stdout, "Nest<Dog> is Seq<out Box<out Animal>>", nest is Seq<out Box<out Animal>>)

    // nullable types and null
    nothing: Any? = null
    show(stdout, "null is Dog", nothing is Dog)
    show(stdout, "null is Dog?", nothing is Dog?)
    show(stdout, "null is Box<Dog>?", nothing is Box<Dog>?)
    show(stdout, "Box<Dog> is Box<Dog>?", dogBox is Box<Dog>?)
    show(stdout, "Box<Dog> is Box<Dog?>", dogBox is Box<Dog?>)
    show(stdout, "Box<Dog> is Box<out Dog?>", dogBox is Box<out Dog?>)

    // intersections
    dog: Any = Dog()
    cat: Any = Cat()
    show(stdout, "Dog is Animal & Named", dog is Animal & Named)
    show(stdout, "Cat is Animal & Named", cat is Animal & Named)
    show(stdout, "Box<Dog> is Box<Dog> & Animal", dogBox is Box<Dog> & Animal)

    // type parameters
    show(stdout, "Dog is T = Animal", isA::<Animal>(dog))
    show(stdout, "Dog is T = Cat", isA::<Cat>(dog))
    show(stdout, "Box<Dog> is T = Box<out Animal>", isA::<Box<out Animal>>(dogBox))
    show(stdout, "Box<Dog> is T = Box<Cat>", isA::<Box<Cat>>(dogBox))
    show(stdout, "null is T = Dog?", isA::<Dog?>(nothing))
    show(stdout, "null is T = Dog", isA::<Dog>(nothing))
    show(stdout, "Box<Dog> is Box<T = Dog>", isBoxOf::<Dog>(dogBox))
    show(stdout, "Box<Dog> is Box<T = Cat>", isBoxOf::<Cat>(dogBox))

    // mutability: objects know that of their type arguments
    mutDogBox: Any = Box::<mut Dog>(Dog())
    show(stdout, "Box<mut Dog> is Box<mut Dog>", mutDogBox is Box<mut Dog>)
    show(stdout, "Box<mut Dog> is Box<Dog>", mutDogBox is Box<Dog>)
    show(stdout, "Box<mut Dog> is Box<const Dog>", mutDogBox is Box<const Dog>)
    show(stdout, "Box<mut Dog> is Box<out Dog>", mutDogBox is Box<out Dog>)
    show(stdout, "Box<mut Dog> is Box<out mut Animal>", mutDogBox is Box<out mut Animal>)
    show(stdout, "Box<Dog> is Box<mut Dog>", dogBox is Box<mut Dog>)
    show(stdout, "Box<Dog> is Box<out mut Animal>", dogBox is Box<out mut Animal>)
    show(stdout, "Box<Dog> is Box<out Animal>", dogBox is Box<out Animal>)
    show(stdout, "Box<mut Dog> is T = Box<mut Dog>", isA::<Box<mut Dog>>(mutDogBox))
    show(stdout, "Box<mut Dog> is T = Box<Dog>", isA::<Box<Dog>>(mutDogBox))
    show(stdout, "Box<mut Dog> is Box<T = mut Dog>", isBoxOf::<mut Dog>(mutDogBox))
    show(stdout, "Box<mut Dog> is Box<T = Dog>", isBoxOf::<Dog>(mutDogBox))

    // mutability: objects don't know that of the references to them, the type of the reference does
    mutDog: mut Dog = Dog()
    show(stdout, "Dog through a read reference is T = Dog", isA::<Dog>(mutDog))
    show(stdout, "Dog through a read reference is T = mut Dog", isA::<mut Dog>(mutDog))
    show(stdout, "Dog through a read reference is T = const Dog", isA::<const Dog>(mutDog))
    show(stdout, "Dog through a mut reference is T = Dog", isAThroughMut::<Dog>(mutDog))
    show(stdout, "Dog through a mut reference is T = mut Dog", isAThroughMut::<mut Dog>(mutDog))
    show(stdout, "Dog through a mut reference is T = const Dog", isAThroughMut::<const Dog>(mutDog))
    show(stdout, "Dog through a read reference is mut Dog", isMutDog(mutDog))
    show(stdout, "String through a read reference is T = String", isA::<String>("a string"))

    // tokens: a class is below NonToken unless it is a token class, and an object that holds a token is no NonToken
    square: Any = Square()
    channel: Any = Channel()
    channelBox: Any = Box::<Channel>(Channel())
    dogWrapper: Any = Wrapper::<Dog>(Dog())
    channelWrapper: Any = Wrapper::<Channel>(Channel())
    show(stdout, "Dog is NonToken", dog is NonToken)
    show(stdout, "Square is Shape", square is Shape)
    show(stdout, "Channel is NonToken", channel is NonToken)
    show(stdout, "Channel is Stream", channel is Stream)
    show(stdout, "Channel is Named", channel is Named)
    show(stdout, "Channel is Named & NonToken", channel is Named & NonToken)
    show(stdout, "Box<Dog> is NonToken", dogBox is NonToken)
    show(stdout, "Box<Channel> is NonToken", channelBox is NonToken)
    show(stdout, "Box<Channel> is Box<Channel>", channelBox is Box<Channel>)
    show(stdout, "Box<Channel> is Box<out Named>", channelBox is Box<out Named>)
    show(stdout, "Box<Channel> is Box<out NonToken>", channelBox is Box<out NonToken>)
    show(stdout, "Box<Dog> is Box<out NonToken>", dogBox is Box<out NonToken>)
    show(stdout, "Wrapper<Dog> is Named", dogWrapper is Named)
    show(stdout, "Wrapper<Dog> is Named & NonToken", dogWrapper is Named & NonToken)
    show(stdout, "Wrapper<Channel> is Named", channelWrapper is Named)
    show(stdout, "Wrapper<Channel> is Named & NonToken", channelWrapper is Named & NonToken)
    show(stdout, "Dog is T = NonToken", isA::<NonToken>(dog))
    show(stdout, "Channel is T = NonToken", isA::<NonToken>(channel))
    show(stdout, "Wrapper<Channel> is T = NonToken", isA::<NonToken>(channelWrapper))
    show(stdout, "Wrapper<Dog> is A & B = Named & NonToken", isBoth::<Named, NonToken>(dogWrapper))
    show(stdout, "Wrapper<Channel> is A & B = Named & NonToken", isBoth::<Named, NonToken>(channelWrapper))
    show(stdout, "Wrapper<Channel> is A & B = Named & Wrapper<Channel>", isBoth::<Named, Wrapper<Channel>>(channelWrapper))
    forgotten: NonToken? = channelBox as? NonToken
    show(stdout, "Box<Channel> as? NonToken is null", isNull(forgotten))

    // tokens: what is const is no token. Where mutabilities combine to own, the type keeps saying so
    stdout.println("const T, T = mut Animal: " + constOf::<mut Animal>().toString())
    show(stdout, "const T, T = mut Animal is below NonToken", constOf::<mut Animal>().isSubtypeOf(typeOf::<NonToken>()))
    show(stdout, "const T, T = mut Animal is below const Animal", constOf::<mut Animal>().isSubtypeOf(typeOf::<const Animal>()))
    stdout.println("A & B, A = const Animal, B = mut Named: " + bothOf::<const Animal, mut Named>().toString())
    show(stdout, "A & B, A = const Animal, B = mut Named is below NonToken", bothOf::<const Animal, mut Named>().isSubtypeOf(typeOf::<NonToken>()))
    stdout.println("A & B, A = Animal, B = mut Named: " + bothOf::<Animal, mut Named>().toString())
    show(stdout, "A & B, A = Animal, B = mut Named is below NonToken", bothOf::<Animal, mut Named>().isSubtypeOf(typeOf::<NonToken>()))

    // no object is of two classes: such an intersection is Nothing by another name, null aside
    show(stdout, "Dog & Cat is below String", typeOf::<Dog & Cat>().isSubtypeOf(typeOf::<String>()))
    show(stdout, "Dog & Animal is below String", typeOf::<Dog & Animal>().isSubtypeOf(typeOf::<String>()))
    show(stdout, "Dog? & Cat? is below String?", typeOf::<Dog? & Cat?>().isSubtypeOf(typeOf::<String?>()))
    show(stdout, "Dog? & Cat? is below String", typeOf::<Dog? & Cat?>().isSubtypeOf(typeOf::<String>()))
    show(stdout, "Box<Dog & Cat> is below Box<own Nothing>", typeOf::<Box<Dog & Cat>>().isSubtypeOf(typeOf::<Box<own Nothing>>()))
    show(stdout, "Box<own Nothing> is below Box<Dog & Cat>", typeOf::<Box<own Nothing>>().isSubtypeOf(typeOf::<Box<Dog & Cat>>()))
    show(stdout, "A & B, A = Dog, B = Cat is below String", bothOf::<Dog, Cat>().isSubtypeOf(typeOf::<String>()))

    // casts
    asBox = dogBox as Box<Dog>
    stdout.println("cast to Box<Dog> succeeded")
    safe: Box<Cat>? = dogBox as? Box<Cat>
    show(stdout, "Box<Dog> as? Box<Cat> is null", isNull(safe))
    safeNull: Box<Dog>? = nothing as? Box<Dog>
    show(stdout, "null as? Box<Dog> is null", isNull(safeNull))
    nullableBox: Box<Dog>? = nothing as Box<Dog>?
    show(stdout, "null as Box<Dog>? is null", isNull(nullableBox))
    viaParameter: Box<Dog> = castTo::<Box<Dog>>(dogBox)
    stdout.println("cast to T = Box<Dog> succeeded")

    readDog: Dog = castTo::<Dog>(mutDog)
    stdout.println("cast to T = Dog succeeded")

    // a CastError is an Error, it is not caught: the program ends here.
    // castTo takes a read reference, which cannot become a mut one
    stdout.println("casting a read reference to a Dog to T = mut Dog")
    wrong: mut Dog = castTo::<mut Dog>(mutDog)
    stdout.println("unreachable")
}
