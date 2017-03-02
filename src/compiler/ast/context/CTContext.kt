package compiler.ast.context

import compiler.ast.FunctionDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.type.BaseType
import compiler.ast.type.TypeReference

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
 *         // the immutable context A is initialized with x and y
 *         val g = e + f // a new context B is derived from A with g added to it
 *         val h = g + 1 // OK, h is evaluated in context B in which g is present
 *                       // context C is derived from B with h added to it
 *         val i = i + 1 // ERROR when evaluating i because k is not defined in context C
 *         val k = f + 1
 *     }
 *
 * The naming for (im)mutable context is coherent with Kotlin collections: CTContext is immutable, MutableCTContext
 * is mutable.
 * All contexts in use are [MutableCTContext]s; this interface contains only the immutable operations. It is used
 * to convey that the context must not be modified to assure correct compilation, CTFE or interpretation. Much like
 * the `immutable` keyword in the language this program compiles.
 */
interface CTContext {
    /**
     * @return A copy of this [CTContext] with the given context added to it; The given context will shadow colliding
     * symbols.
     */
    fun including(context: CTContext): CTContext

    /**
     * Creates a copy of this [CTContext], adds the given declaration to it and returns that copy. If the
     * given variable is already defined in this context, overwrites that.
     */
    fun withVariable(declaration: VariableDeclaration, overrideType: TypeReference? = null): CTContext

    /**
     * Creates a copy of this [CTContext], adds the given declaration to it and returns that copy. If the
     * given function is already defined in this context, overwrites that.
     */
    fun withFunction(declaration: FunctionDeclaration): CTContext

    /**
     * @return The variable accessible under the given name, shadowing included.
     */
    fun resolveVariable(name: String): Variable?

    /**
     * @return The [BaseType] in this context identified by the given reference or null if no such [BaseType] is defined
     * in the context.
     * TODO: maybe return multiple types in case of ambiguity?
     */
    fun resolveBaseType(ref: TypeReference): BaseType?

    /**
     * Returns all known functions overloads with the given name, sorted by proximity to the given type (closer => earlier)
     * @see BaseType.hierarchicalDistanceTo
     * @param receiverType Limits the returned functions to those with a receiver of the given type. Null => no receiver
     */
    fun resolveFunctions(name: String, receiverType: TypeReference? = null): List<FunctionDeclaration>
}