/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding.context

import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.AstTypeArgument
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.effect.EphemeralStateClass
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * Compile-Time context. A compile-time context knows all available symbols (through imports and explicit definition).
 * Contexts in which order of symbol declaration is irrelevant are mutable, contexts in which the order of declaration
 * *is* relevant are immutable. Contexts that mix these two parts are implemented by referring to a mutable context from
 * an immutable one (e.g. immutable context within function code refers to mutable context of the enclosing class/file).
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
 * the `immutable` keyword in Emerge.
 */
interface CTContext {
    val swCtx: SoftwareContext get() = moduleContext.softwareContext

    val moduleContext: ModuleContext

    val packageName: CanonicalElementName.Package

    /** The file this context belongs to, right beneath the module context in the tree */
    val sourceFile: SourceFile

    val imports: Iterable<BoundImportDeclaration>

    /**
     * E.g. when inside a class context, this is the visibility of the class
     */
    val visibility: BoundVisibility

    fun resolveBaseType(simpleName: String): Sequence<BoundBaseType>

    /**
     * @return whether this context has a [BoundImportDeclaration] that refers to [simpleName] (or is a import-all)
     * and that is erroneous (no symbol for [simpleName] found or package not found).
     */
    fun hasUnresolvableImportForSimpleName(simpleName: String): Boolean

    /**
     * @return whether resolving [simpleName] in this context is ambiguous simply due to the imports
     * (if so, the fault is in the import, and references just suffer along).
     */
    fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean

    fun resolveTypeParameter(simpleName: String): BoundTypeParameter?

    val allTypeParameters: Sequence<BoundTypeParameter>

    fun resolveTypeArgument(ref: AstTypeArgument, parameter: BoundTypeParameter?): BoundTypeArgument {
        return when (ref) {
            is AstSpecificTypeArgument -> BoundTypeArgument(this, ref, ref.variance, resolveType(ref.type))
            is AstWildcardTypeArgument -> if (parameter == null) {
                BoundTypeArgument(this, ref, TypeVariance.OUT, swCtx.getTopType(ref.span ?: Span.UNKNOWN))
            } else {
                BoundTypeArgument(
                    this,
                    ref,
                    when (parameter.variance) {
                        TypeVariance.UNSPECIFIED -> TypeVariance.OUT
                        else -> TypeVariance.UNSPECIFIED
                    },
                    parameter.bound,
                )
            }
        }
    }

    fun resolveType(ref: TypeReference): BoundTypeReference

    /**
     * @return first: the variable accessible under the given name
     */
    fun resolveVariable(name: String, fromOwnFileOnly: Boolean = false): BoundVariable?

    /**
     * @return a variable name that is guaranteed to not be occupied ([resolveVariable] will return `null`),
     * contains markers as an internal variable (prefix of `__`) and contains [namePayload]
     */
    fun findInternalVariableName(namePayload: String): String {
        var i = 0
        var name: String
        do {
            name = "__${namePayload}$i"
            i++
        } while (resolveVariable(name) != null)

        return name
    }

    /**
     * @return a type parameter name that is guaranteed to not be occupied ([resolveTypeParameter] and [resolveBaseType] will return `null`),
     * contains markers as an internal variable (prefix of `__`) and contains [namePayload]
     */
    fun findInternalTypeParameterName(namePayload: String): String {
        var i = 0
        var name: String
        do {
            name = "__${namePayload}$i"
            i++
        } while (resolveTypeParameter(name) != null || resolveBaseType(name).any())

        return name
    }

    fun <Subject : Any, State> getEphemeralState(stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        return stateClass.getInitialState(subject)
    }

    fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet<*>>
}