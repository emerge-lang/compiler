package compiler.ast.context

import java.util.*

/**
 * Connects all elements that make up a piece of software. Is able to resolve fully-qualified names across
 * contained [Module]s.
 */
class SoftwareContext {
    /**
     * All the modules. These don't nest!
     */
    private val modules: MutableSet<Module> = HashSet()

    /**
     * Looks for a module with the given name in this context. If none is defined, creates it.
     * @return The module with the given name within this context.
     */
    fun module(vararg name: String): Module {
        val existing = modules.find { Arrays.equals(it.name, name) }
        if (existing != null) {
            return existing
        }

        val module = Module(name, MutableCTContext())
        this.modules.add(module)
        return module
    }
}