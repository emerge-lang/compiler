package compiler.ast.context

import java.util.*

/**
 * Just a bunch of modules with all their contents; all elements that make up a piece of software.
 */
class SoftwareContext {
    private val definedModules: MutableSet<Module> = HashSet()

    /**
     * Looks for a module with the given name in this context. If none is defined, creates it.
     * @return The module with the given name within this context.
     */
    fun module(vararg name: String): Module {
        val existing = definedModules.find { Arrays.equals(it.name, name) }
        if (existing != null) {
            return existing
        }

        val module = Module(name, MutableCTContext())
        this.definedModules.add(module)
        return module
    }
}