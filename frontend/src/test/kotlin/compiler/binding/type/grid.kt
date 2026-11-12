package compiler.compiler.binding.type

import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.useValidModule

/**
 * A set of types to check properties of the type system over, by pairs and triples: of the fragments the proofs in
 * `type-system-proofs/theories` cover (`OracleGrid.v` checks which), and some just outside of them. The types are written
 * within `Ctx`, so they can mention its type parameters.
 */
internal object TypeGrid {
    val swCtx = useValidModule("""
        interface A {}
        interface B {}
        interface C : A {}
        interface D : C & B {}
        interface Ord<T> {}
        class N : Ord<N> {}
        class M : Ord<A> & A {}
        class Box<E> {}
        class H<X> {}
        interface Duo<K, V> {}
        interface Seq<E> {}
        class IntSeq : Seq<A> {}
        class Nest<E> : Seq<Box<E>> {}
        class Swap<K, V> : Duo<V, K> {}
        class Ctx<P, Q : A, R : A?, F : Ord<in F>, S : Seq<out P>, T : A & B, U : R> {}
    """.trimIndent())

    /** the type parameters of `Ctx`, with their bounds */
    val ctxBounds = listOf("P" to "Any?", "Q" to "A", "R" to "A?", "F" to "Ord<in F>", "S" to "Seq<out P>", "T" to "A & B", "U" to "R")

    val ctxParameters = ctxBounds.map { it.first }.toSet()

    val types: List<Pair<String, BoundTypeReference>> = listOf(
        "A", "mut A", "const A", "own A", "A?", "mut A?",
        "B", "const B?",
        "C", "mut C", "own C?",
        "N", "mut N", "Ord<N>", "Ord<in N>",
        "Any", "Any?", "mut Any", "own Nothing", "own Nothing?", "read Nothing", "mut Nothing?",
        "Box<A>", "Box<C>", "Box<in A>", "Box<out A>", "Box<in C>", "Box<out C>", "Box<mut A>", "Box<A?>", "mut Box<out A>?",
        "Box<A & B>", "Box<out A & Q>", "Box<own Nothing>", "Box<read Nothing>", "Box<out const Nothing>",
        "P", "P?", "P!", "mut P", "Q", "const Q", "Q?", "R", "R!", "R?", "read R", "mut R?",
        "F", "F?", "mut F", "Ord<in F>",
        "Box<P>", "Box<P?>", "Box<out Q>", "Box<R!>", "Box<R?>", "Box<mut R>", "Box<F>",
        "A & B", "mut A & B", "A? & B?", "C & Q", "Q & B", "A & B & Q", "A & P", "mut A & R", "B & F", "A? & R?",
        // components that keep their nullability (coverage #15)
        "A? & P", "P & R",
        // subtypes through more than one supertype, and through parameterized ones
        "D", "mut D", "D?", "const D", "M", "mut M", "M?",
        "Seq<A>", "Seq<out A>", "Seq<in C>", "Seq<C>", "IntSeq", "mut IntSeq", "IntSeq?",
        "Nest<A>", "Nest<C>", "Nest<P>", "Nest<out Q>",
        "Seq<Box<A>>", "Seq<out Box<out A>>", "Seq<Box<P>>", "Seq<in Box<C>>", "Seq<P>", "Seq<out P>", "Seq<out R>",
        "Duo<A, B>", "Duo<B, A>", "Duo<out A, in B>", "Duo<in B, out A>", "Duo<P, Q>", "Duo<in P, out R?>",
        "Duo<A? & P, F>", "Duo<Box<P>, out Box<Q>>", "Duo<A, B>?",
        "Swap<A, B>", "Swap<B, A>", "Swap<C, P>", "Swap<out A, in B>", "mut Swap<A, B>",
        "const Any", "own Any", "read Any?", "const Any?",
        // nested, and variant around type parameters
        "Box<Box<A>>", "Box<Box<out A>>", "Box<out Box<A>>", "Box<out Box<out A>>", "Box<in Box<A>>", "Box<Box<in C>>",
        "Box<Box<P?>>", "Box<out Box<P>>", "Box<Box<R>>", "Box<in Box<out Q>>", "Box<Box<A? & P>>",
        "Ord<in P>", "Ord<in R?>", "Ord<out Q>", "Ord<P>", "Ord<out P?>",
        "Box<in P>", "Box<out P>", "Box<in R>", "Box<out R?>", "Box<in Q?>", "Box<out P!>", "Box<in mut P>", "Box<out const Q>",
        "Box<in A?>", "Box<out A?>", "Box<in mut A>", "Box<out own C>", "Box<Any?>", "Box<out Any?>", "Box<in Any>",
        "Box<in A>?", "Box<out P>?", "Box<P>?",
        // F-bounded
        "F!", "const F", "own F", "read F", "Box<in F>", "Box<out F>", "Box<F?>",
        "Ord<F>", "Ord<out F>", "Ord<in F?>", "Ord<in F>?", "Box<Ord<in F>>", "Ord<in Ord<in F>>",
        // Nothing, in variant arguments and intersections
        "Box<in own Nothing>", "Box<out own Nothing>", "Box<Nothing?>", "Box<in Nothing?>", "Box<out Nothing?>",
        "own Nothing & A", "read Nothing & P", "Nothing? & A?", "Nothing? & P",
        "Box<own Nothing & A>", "Box<out Nothing? & P>",
        // intersections of three components and more, of disjoint classes, of type parameters
        "A? & R? & P", "mut A & Q & F", "A & B & P", "A? & B? & P", "P & R & A?", "Q & F & B", "C & B & P",
        "mut A & mut B & Q", "const A & B", "own A & Q", "A & Box<A>", "N & A", "N & Box<A>", "Box<A> & Box<C>",
        "A? & C?", "A? & Q?", "Q? & B?", "P? & A?", "R! & B", "P! & A", "mut P & A", "F & N", "F & A", "F? & A?",
        "F & Q", "Q & R", "P & F", "P & Q", "R & B?", "R? & B?", "mut R & mut B?",
        "N & M", "N? & M?", "N & M & P", "Box<P> & N", "D & Q", "mut D & P", "D? & R?", "D? & P",
        // in-variant arguments of unrelated types, which the closest common supertype intersects
        "Box<in B>", "Box<in N>", "Box<in M>", "Box<in D>", "Box<in N?>", "Seq<in A>", "Seq<in B>", "Ord<in A>", "Ord<in M>",
        "Duo<in A, in B>", "Duo<in A, out B>", "Duo<P, P>", "Duo<in Q, in R>", "Swap<in P, out Q>", "Swap<P, Q>",
        "Box<in Box<in A>>", "Box<in Box<in P>>", "Box<out Box<in P?>>", "Box<in Ord<in F>>", "Ord<in Ord<in N>>",
        "Box<in T>", "Box<in S>", "Box<in U>", "Box<in R!>", "Box<out U?>", "Ord<in U>", "Box<in A? & B?>",
        // intersections in type arguments
        "Box<in A & B>", "Box<out A? & P>", "Box<A? & P>", "Box<in A? & P>", "Box<out P & R>", "Box<P & R>", "Box<in P & R>",
        "Box<A? & B?>", "Box<out A? & B?>", "Box<in Q & B>", "Box<F & A>", "Box<in mut A & B>", "Box<out C & Q>",
        "Box<A? & R? & P>",
        // type parameters bounded by another (S, U) and by an intersection (T)
        "S", "S?", "mut S", "S!", "Box<S>", "Box<out S>", "S & B", "Seq<out P> & S",
        "T", "T?", "mut T", "T!", "T & Q", "Box<out T>", "Box<T>",
        "U", "U!", "U?", "mut U", "U & R", "A? & U", "Box<U>", "Box<in U!>", "U & P", "U & T",
    ).map { it to swCtx.parseTypeIn("Ctx", it) }

    /** the type parameters of Ctx, bound in ways that tell their mutability and nullability apart, each within its bound */
    val instantiations = listOf(
        "Ctx<mut A, mut C, A?, N, Seq<mut A>, D, A?>",
        "Ctx<const A, C, mut C, mut N, Seq<out const A>, const D, mut C>",
        "Ctx<A?, const A, const C?, const N, Seq<A?>, D, const C?>",
        "Ctx<own C, own C, own Nothing?, own N, Seq<own C>, own D, own Nothing?>",
        "Ctx<mut Box<A>?, mut A, mut A?, N, Seq<mut Box<A>?>, mut D, mut C?>",
        "Ctx<A & B, D, A? & B?, M, Seq<D>, A & B, D?>",
        "Ctx<read Nothing, own Nothing, read Nothing?, N, own Nothing, own Nothing, own Nothing?>",
        "Ctx<own Nothing, mut D, A? & B?, mut M, Seq<own Nothing>, D & C, own Nothing>",
        "Ctx<Box<in A> & B, M, mut M?, const M, Seq<Box<in A> & B>, mut D, mut M>",
        "Ctx<Box<A>, C & B, D?, N, Nest<A>, D, D>",
        "Ctx<A, mut M, mut A?, N, IntSeq, D, mut M?>",
    ).map { it to swCtx.parseType(it).inherentTypeBindings }
}
