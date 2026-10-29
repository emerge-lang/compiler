package compiler.compiler.binding.type

import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.useValidModule

/**
 * A set of types to check properties of the type system over, by pairs and triples: of the fragments the proofs in
 * `type-system-proofs/theories` cover (see `fragments.kt`), and some just outside of them. The types are written
 * within `Ctx`, so they can mention its type parameters.
 */
internal object TypeGrid {
    val swCtx = useValidModule("""
        interface A {}
        interface B {}
        interface C : A {}
        interface Ord<T> {}
        class N : Ord<N> {}
        class Box<E> {}
        class H<X> {}
        class Ctx<P, Q : A, R : A?, F : Ord<in F>> {}
    """.trimIndent())

    /** the type parameters of `Ctx`, with their bounds */
    val ctxBounds = listOf("P" to "Any?", "Q" to "A", "R" to "A?", "F" to "Ord<in F>")

    val ctxParameters = ctxBounds.map { it.first }.toSet()

    val types: List<Pair<String, BoundTypeReference>> = listOf(
        "A", "mut A", "const A", "exclusive A", "A?", "mut A?",
        "B", "const B?",
        "C", "mut C", "exclusive C?",
        "N", "mut N", "Ord<N>", "Ord<in N>",
        "Any", "Any?", "mut Any", "exclusive Nothing", "exclusive Nothing?", "read Nothing", "mut Nothing?",
        "Box<A>", "Box<C>", "Box<in A>", "Box<out A>", "Box<in C>", "Box<out C>", "Box<mut A>", "Box<A?>", "mut Box<out A>?",
        "Box<A & B>", "Box<out A & Q>", "Box<exclusive Nothing>", "Box<read Nothing>", "Box<out const Nothing>",
        "P", "P?", "P!", "mut P", "Q", "const Q", "Q?", "R", "R!", "R?", "read R", "mut R?",
        "F", "F?", "mut F", "Ord<in F>",
        "Box<P>", "Box<P?>", "Box<out Q>", "Box<R!>", "Box<R?>", "Box<mut R>", "Box<F>",
        "A & B", "mut A & B", "A? & B?", "C & Q", "Q & B", "A & B & Q", "A & P", "mut A & R", "B & F", "A? & R?",
        // components that keep their nullability (coverage #15)
        "A? & P", "P & R",
    ).map { it to swCtx.parseTypeIn("Ctx", it) }

    /** the type parameters of Ctx, bound in ways that tell their mutability and nullability apart, each within its bound */
    val instantiations = listOf(
        "Ctx<mut A, mut C, A?, N>",
        "Ctx<const A, C, mut C, mut N>",
        "Ctx<A?, const A, const C?, const N>",
        "Ctx<exclusive C, exclusive C, exclusive Nothing?, exclusive N>",
        "Ctx<mut Box<A>?, mut A, mut A?, N>",
    ).map { it to swCtx.parseType(it).inherentTypeBindings }
}
