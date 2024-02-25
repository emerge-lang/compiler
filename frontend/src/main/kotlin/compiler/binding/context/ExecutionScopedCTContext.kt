package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.VariableDeclaration
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import java.util.Collections
import java.util.IdentityHashMap

/**
 * A [CTContext] that is also associated with an execution scope. All code that actually _does_
 * stuff lives in an [ExecutionScopedCTContext]; Pure [CTContext] is for declaration-only situations.
 */
interface ExecutionScopedCTContext : CTContext {
    /**
     * @return The variable accessible under the given name, shadowing included.
     */
    fun resolveVariable(name: String, fromOwnFileOnly: Boolean = false): BoundVariable?

    /**
     * **This is a helper method for [BoundVariable.isInitializedInContext]! You likely want to use that one.**
     * @return whether this context or any of its parents initializes the given variable.
     *
     * If the [BoundVariable] wasn't obtained from [resolveVariable] on the same context, the return value is undefined.
     */
    fun initializesVariable(variable: BoundVariable): Boolean

    /**
     * @return Whether this context contains the given variable. Only parent contexts up to and including the
     *         given `boundary` will be searched.
     */
    fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean

    /**
     * @return all code that has been deferred in the scope of *this very* [ExecutionScopedCTContext], in the
     * **reverse** order of how it was added to [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getLocalDeferredCode(): Sequence<BoundExecutable<*>>

    /**
     * @return all code that has been deferred in this scope and all of its parent [ExecutionScopedCTContext]s, in the
     * **reverse** order of how it was added to [MutableExecutionScopedCTContext.addDeferredCode].
     */
    fun getAllDeferredCode(): Sequence<BoundExecutable<*>>
}

open class MutableExecutionScopedCTContext(
    val parentContext: CTContext,
) : MutableCTContext(parentContext), ExecutionScopedCTContext {
    private val hierarchy: Sequence<CTContext> = generateSequence(this as CTContext) { (it as? MutableExecutionScopedCTContext)?.parentContext }

    private val localDeferredCode = ArrayList<BoundExecutable<*>>()

    /**
     * Adds code to be returned from [getLocalDeferredCode] and [getAllDeferredCode]
     */
    open fun addDeferredCode(code: BoundExecutable<*>) {
        localDeferredCode.add(code)
    }

    override fun getLocalDeferredCode(): Sequence<BoundExecutable<*>> {
        return localDeferredCode.asReversed().asSequence()
    }

    override fun getAllDeferredCode(): Sequence<BoundExecutable<*>> {
        val fromParent = (parentContext as? ExecutionScopedCTContext)?.getAllDeferredCode() ?: emptySequence()
        return fromParent + getLocalDeferredCode()
    }

    /**
     * Adds the given variable to this context; possibly overriding its type with the given type.
     */
    fun addVariable(declaration: VariableDeclaration): BoundVariable {
        val bound = declaration.bindTo(this)

        return addVariable(bound)
    }

    fun addVariable(boundVariable: BoundVariable): BoundVariable {
        if (boundVariable.context in hierarchy) {
            _variables[boundVariable.name] = boundVariable
            return boundVariable
        }

        throw InternalCompilerError("Cannot add a variable that has been bound to a different context")
    }

    private val initializedVariables: MutableSet<BoundVariable> = Collections.newSetFromMap(IdentityHashMap())
    fun markVariableInitialized(variable: BoundVariable) {
        initializedVariables.add(variable)
    }

    override fun initializesVariable(variable: BoundVariable): Boolean {
        return variable in initializedVariables || ((parentContext as? ExecutionScopedCTContext)?.initializesVariable(variable) ?: false)
    }

    override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
        _variables[name]?.let { return it }

        val fromImport = if (fromOwnFileOnly) null else {
            val importedVars = importsForSimpleName(name)
                .mapNotNull { it.resolveVariable(name) }

            // TODO: if importedVars.size is > 1 the name is ambiguous; how to handle that?
            importedVars.firstOrNull()
        }

        return fromImport ?: (parentContext as? ExecutionScopedCTContext)?.resolveVariable(name, fromOwnFileOnly)
    }

    override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean {
        if (_variables.containsValue(variable)) return true

        if (this === boundary) {
            return false
        }

        return (parentContext as? ExecutionScopedCTContext)?.containsWithinBoundary(variable, boundary) ?: false
    }
}