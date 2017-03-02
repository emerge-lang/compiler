package compiler.ast.context

import compiler.ast.FunctionDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.type.BaseType
import compiler.ast.type.TypeReference
import java.util.*

/**
 * Mutable compile-time context; for explanation, see the doc of [CTContext].
 */
open class MutableCTContext : CTContext
{
    /**
     * All the contexts that are included in this one (through imports, derivation, ...)
     * in the order of shadowing (earlier in the list shadows later in the list)
     */
    private val parentContexts: MutableList<CTContext> = LinkedList()

    /** Maps variable names to their metadata; holds only variables defined in this context */
    private val variables: MutableMap<String,Variable> = HashMap()

    /** Holds all the toplevel functions defined in this context */
    private val functions: MutableSet<FunctionDeclaration> = HashSet()

    /** Holds all the base types defined in this context */
    private val types: MutableSet<BaseType> = HashSet()

    /**
     * Includes the given [CTContext] in this one. If the given context contains duplicate
     * definitions symbols the ones that existed in this context previously will be shadowed.
     */
    open fun include(context: CTContext) {
        parentContexts.add(0, context)
    }

    override fun including(context: CTContext): CTContext {
        val copy = this.mutableCopy()
        copy.include(context)

        return copy
    }

    /**
     * Adds the given variable to this context; possibly overriding its type with the given type.
     */
    open fun addVariable(declaration: VariableDeclaration, overrideType: TypeReference? = null) {
        variables[declaration.name.value] = Variable(this, declaration, overrideType)
    }

    override fun withVariable(declaration: VariableDeclaration, overrideType: TypeReference?): CTContext {
        val copy = this.mutableCopy()
        copy.addVariable(declaration, overrideType)

        return copy
    }

    /**
     * Adds the given [FunctionDeclaration] to this context, possibly overriding
     */
    open fun addFunction(declaration: FunctionDeclaration) {
        functions.add(declaration)
    }

    override fun withFunction(declaration: FunctionDeclaration): CTContext {
        val copy = mutableCopy()
        copy.addFunction(declaration)

        return copy
    }

    /**
     * Adds the given [BaseType] to this context, possibly overriding
     */
    open fun addBaseType(type: BaseType) {
        types.add(type)
    }

    override fun resolveVariable(name: String): Variable? =
        variables[name] ?:
        parentContexts.firstNotNull { it.resolveVariable(name) }

    override fun resolveBaseType(ref: TypeReference): BaseType? =
        types.find { it.simpleName == ref.declaredName } ?:
        types.find { it.fullyQualifiedName == ref.declaredName } ?:
        parentContexts.firstNotNull { it.resolveBaseType(ref) }

    /** @return An unmodified copy of this context */
    fun mutableCopy(): MutableCTContext {
        val copy = MutableCTContext()

        copy.variables.putAll(this.variables)

        return copy
    }

    /** @return An unmodified copy of this context */
    fun copy(): CTContext = mutableCopy()
}

private fun <T, R> Iterable<T>.firstNotNull(transform: (T) -> R?): R? = map(transform).filterNot{ it == null }.first()