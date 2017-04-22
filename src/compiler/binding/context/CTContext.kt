package compiler.binding.context

import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.type.BaseType

/**
 * Compile-Time context. A compile-time context knows all available symbols (through imports and explicit definition).
 * Context in which order of symbol declaration is irrelevant are mutable, context in which the order of declaration
 * *is* relevant are immutable. Context that mix these two parts are implemented by referring to a mutable context from a
 * immutable one (e.g. immutable context within function code refers to mutable context of the enclosing class/file).
 *
 * Consider this example (mutable, file level)
 *
 *     // mutable context A
 *     val x = 3 + y // x is added to A, A is mutated
 *     val y = 3     // y is added to A, A is mutated
 *
 * When x has to be evaluated, y is present because order of declaration is not important on file level.
 *
 * Another example (function scope, immutable):
 *
 *     fun fn(e: Int, f: Int) {
 *         // the immutable context A is initialized with e and f
 *         val g = e + f // a new context B is derived from A with g added to it
 *         val h = g + 1 // OK, h is evaluated in context B in which g is present
 *                       // context C is derived from B with h added to it
 *         val i = k + 1 // ERROR when evaluating i because k is not defined in context C
 *         val k = f + 1
 *     }
 *
 * The naming for (im)mutable context is coherent with Kotlin collections: CTContext is immutable, MutableCTContext
 * is mutable.
 * All contexts in use are [MutableCTContext]s; this interface contains only the immutable operations. It is used
 * to convey that the context must not be modified to assure correct compilation, CTFE or interpretation. Much like
 * the `immutable` keyword in the language this program compiles.
 */
interface CTContext
{
    /** The [SoftwareContext] the imports are resolved from */
    val swCtx: SoftwareContext?
        get() = null

    /**
     * @param onlyOwn If true, does not attempt to resolve variables through imports.
     * @return The variable accessible under the given name, shadowing included.
     */
    fun resolveVariable(name: String, onlyOwn: Boolean = false): BoundVariable?

    /**
     * Returns the [BaseType] with the given simple name defined in this context or null if a [BaseType] with the
     * given simple name has been defined within this context (see [addBaseType])
     */
    fun resolveDefinedType(simpleName: String): BaseType?

    /**
     * Attempts to resolve the reference within this context considering imports and FQN references.
     * @param ref the reference to resolve
     * TODO: maybe return multiple types in case of ambiguity?
     */
    fun resolveAnyType(ref: TypeReference): BaseType?

    /**
     * Returns the function overloads with the given simple name defined in this context.
     */
    fun resolveDefinedFunctions(name: String): Collection<BoundFunction>

    /**
     * Attempts to resolve all functions with the simple name or FQN and receiver type; also includes imported
     * functions.
     * @return The resolved functions
     */
    fun resolveAnyFunctions(name: String): Collection<BoundFunction>

    companion object {
        /**
         * A [CTContext] that does not resolve anything. This is used as the parent context for all toplevel code.
         */
        val EMPTY = object : CTContext {
            override fun resolveVariable(name: String, onlyOwn: Boolean): BoundVariable? = null

            override fun resolveDefinedType(simpleName: String): BaseType? = null

            override fun resolveAnyType(ref: TypeReference): BaseType? = null

            override fun resolveDefinedFunctions(name: String): Collection<BoundFunction> = emptySet()

            override fun resolveAnyFunctions(name: String): Collection<BoundFunction> = emptySet()
        }
    }
}