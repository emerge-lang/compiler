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

import compiler.InternalCompilerError
import compiler.binding.type.BaseType
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext

/**
 * Bundles all modules that are part of a piece of software (e.g. an application), so it also
 * groups pre-defined modules like the core builtin types, dependencies and code that is specific
 * to the application/project currently being compiled.
 */
class SoftwareContext {
    private val modules: MutableList<ModuleContext> = ArrayList()

    /**
     * Creates and register a new [ModuleContext] in this software.
     * @return the new context so [SourceFile]s can be bound to it (see [ModuleContext.addSourceFile])
     */
    fun registerModule(name: PackageName): ModuleContext {
        modules.find { it.moduleName.containsOrEquals(name) }?.let { conflictingModule ->
            throw IllegalArgumentException("Cannot add module $name to this ${this::class.simpleName}, because it already contains a module with conflicting name: $conflictingModule")
        }

        val moduleContext = ModuleContext(name, this)
        modules.add(moduleContext)
        return moduleContext
    }

    fun getRegisteredModule(name: PackageName): ModuleContext {
        return modules.find { it.moduleName == name } ?: throw IllegalStateException("Module $name has not been registered")
    }

    private val packages = HashMap<PackageName, PackageContext>()

    /**
     * @return a reference to the requested package in this software context, or null if no module is known that
     * contains the package (see [registerModule]).
     */
    fun getPackage(name: PackageName): PackageContext? {
        packages[name]?.let { return it }
        // there is no source file in the package, but the requested package may still be in the responsibility
        // of one of the known modules, so we should return an empty package context
        val emptyPackage = modules
            .find { name.containsOrEquals(it.moduleName) }
            ?.let { PackageContext(it, name) }
            ?: return null

        packages[name] = emptyPackage
        return emptyPackage
    }

    fun doSemanticAnalysis(): Collection<Reporting> {
        modules
            .asSequence()
            .flatMap { it.sourceFiles }
            .onEach {
                check(it.packageName in packages) {
                    "All packages explicitly mentioned in package declarations should have been registered until now"
                }
            }

        return (modules.flatMap { it.semanticAnalysisPhase1() } +
                packages.values.flatMap { it.semanticAnalysisPhase1() } +
                modules.flatMap { it.semanticAnalysisPhase2() } +
                modules.flatMap { it.semanticAnalysisPhase3() } +
                packages.values.flatMap { it.semanticAnalysisPhase3() })
            .toSet()
    }

    /**
     * @returns the IR representation of this software for the backend to process.
     * @throws InternalCompilerError if this software is not valid (semantic analysis not done, or it produced errors)
     */
    fun toBackendIr(): IrSoftwareContext {
        return IrSoftwareContextImpl(modules)
    }

    val unitBaseType: BaseType by lazy {
        getPackage(PackageName(listOf("emerge", "core")))!!
            .types
            .single { it.fullyQualifiedName.last == "Unit" }
    }
}