package compiler.ast.context

import compiler.InternalCompilerError
import java.util.*

/**
 * Connects all elements that make up a piece of software. Is able to resolve fully-qualified names across
 * contained [Module]s.
 */
class SoftwareContext {
    /**
     * All the modules. These don't nest!
     */
    private val modules: MutableMap<String,CTContext> = HashMap()

    /**
     * @return The [CTContext] of the module with the given name or null if no such module is defined.
     */
    fun module(vararg name: String): CTContext? = modules[name.joinToString(".")]

    fun module(name: Iterable<String>): CTContext? = module(name.joinToString("."))

    /**
     * Defines a new module with the given name and the given context.
     * @throws InternalCompilerError If such a module is already defined.
     * TODO: Create & use a more specific exception
     */
    fun defineModule(context: CTContext, vararg name: String) {
        val strName = name.joinToString(".")
        if (strName in modules) {
            throw InternalCompilerError("Module $strName is already defined")
        }

        modules[strName] = context
    }
}