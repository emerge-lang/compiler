package compiler.binding.context

import compiler.InternalCompilerError
import compiler.parser.Reporting
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
     * @param names The single names of the module; e.g. for module `foo.bar.x` pass `["foo", "bar", "x"]`
     * @return The [CTContext] of the module with the given name or null if no such module is defined.
     */
    fun module(vararg names: String): Module? = modules.find { Arrays.equals(it.name, names) }

    fun module(name: Iterable<String>): Module? = module(*name.toList().toTypedArray())

    /**
     * Defines a new module with the given name and the given context.
     * @throws InternalCompilerError If such a module is already defined.
     * TODO: Create & use a more specific exception
     */
    fun addModule(module: Module) {
        modules.add(module)
    }

    private var semanticAnaylsisReults: Collection<Reporting>? = null

    fun doSemanticAnalysis(): Collection<Reporting> {
        if (semanticAnaylsisReults == null) {
            semanticAnaylsisReults =
                modules.flatMap(Module::semanticAnalysisPhase1) +
                modules.flatMap(Module::semanticAnalysisPhase2) +
                modules.flatMap(Module::semanticAnalysisPhase3)
        }

        return semanticAnaylsisReults!!
    }
}