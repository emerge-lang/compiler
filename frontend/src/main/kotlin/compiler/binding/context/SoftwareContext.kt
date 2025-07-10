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
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.basetype.BoundBaseType
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.UnresolvedType
import compiler.diagnostic.Diagnosis
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import textutils.capitalizeFirst
import kotlin.reflect.KProperty

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
    fun registerModule(
        name: CanonicalElementName.Package,
        dependsOnModules: Set<CanonicalElementName.Package>,
    ): ModuleContext {
        modules.find { it.moduleName.containsOrEquals(name) }?.let { conflictingModule ->
            throw IllegalArgumentException("Cannot add module $name to this ${this::class.simpleName}, because it already contains a module with conflicting name: $conflictingModule")
        }

        val moduleContext = ModuleContext(name, dependsOnModules, this)
        modules.add(moduleContext)
        return moduleContext
    }

    fun getRegisteredModule(name: CanonicalElementName.Package): ModuleContext {
        return modules.find { it.moduleName == name } ?: throw IllegalStateException("Module $name has not been registered")
    }

    fun getModuleOfPackage(packageName: CanonicalElementName.Package): ModuleContext {
        return modules.find { it.moduleName.containsOrEquals(packageName) } ?: throw IllegalStateException("Package $packageName is not part of any registered module")
    }

    private val packages = HashMap<CanonicalElementName.Package, PackageContext>()

    /**
     * @return a reference to the requested package in this software context, or null if no module is known that
     * contains the package (see [registerModule]).
     */
    fun getPackage(name: CanonicalElementName.Package): PackageContext? {
        packages[name]?.let { return it }
        // there is no source file in the package, but the requested package may still be in the responsibility
        // of one of the known modules, so we should return an empty package context
        val emptyPackage = modules
            .find { it.moduleName.containsOrEquals(name) }
            ?.let { PackageContext(it, name) }
            ?: return null

        packages[name] = emptyPackage
        return emptyPackage
    }

    fun resolveBaseType(canonicalName: CanonicalElementName.BaseType): BoundBaseType? {
        return getPackage(canonicalName.packageName)?.resolveBaseType(canonicalName.simpleName)
    }

    fun doSemanticAnalysis(diagnosis: Diagnosis) {
        modules
            .asSequence()
            .flatMap { it.sourceFiles }
            .onEach {
                check(it.packageName in packages) {
                    "All packages explicitly mentioned in package declarations should have been registered until now"
                }
            }

        modules.forEach { it.semanticAnalysisPhase1(diagnosis) }
        packages.values.forEach() { it.semanticAnalysisPhase1(diagnosis) }
        modules.forEach { it.semanticAnalysisPhase2(diagnosis) }
        packages.values.forEach() { it.semanticAnalysisPhase2(diagnosis) }
        modules.forEach { it.semanticAnalysisPhase3(diagnosis) }
        packages.values.forEach() { it.semanticAnalysisPhase3(diagnosis) }
    }

    /**
     * @returns the IR representation of this software for the backend to process.
     * @throws InternalCompilerError if this software is not valid (semantic analysis not done, or it produced errors)
     */
    fun toBackendIr(): IrSoftwareContext {
        return IrSoftwareContextImpl(modules)
    }

    val emergeCorePackage: PackageContext by lazy {
        getPackage(EmergeConstants.CORE_MODULE_NAME)
            ?: throw InternalCompilerError("Core package ${EmergeConstants.CORE_MODULE_NAME} is not registered")
    }

    private fun lazyBaseTypeFromSource(name: CanonicalElementName.BaseType) = object {
        private lateinit var value: BoundBaseType
        operator fun getValue(thisRef: Any, p: KProperty<*>): BoundBaseType {
            if (!this::value.isInitialized) {
                value = resolveBaseType(name)
                    ?: throw InternalCompilerError("Did not find core type $name")
            }
            return value
        }
    }

    private fun coreType(name: String? = null) = object {
        private lateinit var value: BoundBaseType
        operator fun getValue(thisRef: Any, p: KProperty<*>): BoundBaseType {
            if (!this::value.isInitialized) {
                val simpleTypeName = name ?: p.name.capitalizeFirst()
                value = emergeCorePackage.resolveBaseType(simpleTypeName)
                    ?: throw InternalCompilerError("Did not find core type $name")
            }
            return value
        }
    }

    val any: BoundBaseType by coreType()
    val nothing: BoundBaseType by coreType()
    val unit: BoundBaseType by coreType()
    val bool: BoundBaseType by coreType()
    val s8: BoundBaseType by coreType()
    val u8: BoundBaseType by coreType()
    val s16: BoundBaseType by coreType()
    val u16: BoundBaseType by coreType()
    val s32: BoundBaseType by coreType()
    val u32: BoundBaseType by coreType()
    val s64: BoundBaseType by coreType()
    val u64: BoundBaseType by coreType()
    val sword: BoundBaseType by coreType("SWord")
    val uword: BoundBaseType by coreType("UWord")
    val string: BoundBaseType by coreType()
    val f32: BoundBaseType by coreType()
    val f64: BoundBaseType by coreType()
    val weak: BoundBaseType by coreType()
    val array: BoundBaseType by coreType()
    val throwable: BoundBaseType by lazyBaseTypeFromSource(EmergeConstants.THROWABLE_TYPE_NAME)
    val error: BoundBaseType by coreType()
    val reflectionBaseType: BoundBaseType by lazy {
        val reflectPackageName = CanonicalElementName.Package(listOf(
            "emerge", "core", "reflection"
        ))
        val reflectPackage = getPackage(reflectPackageName)
            ?: throw InternalCompilerError("reflect package not found!")

        reflectPackage.types
            .filter { it.simpleName == "ReflectionBaseType" }
            .singleOrNull()
            ?: throw InternalCompilerError("Could not find typeinfo type in emerge source")
    }

    val iterable by lazyBaseTypeFromSource(EmergeConstants.IterableContract.ITERABLE_TYPE_NAME)

    /**
     * the absolute bottom type, `exclusive Nothing`. Note that just `Nothing` is **not** the bottom type because
     * it has `read` mutability, so it's neither a subtype of `const Any` nor of `mut Any`
     */
    val bottomTypeRef by lazy {
        nothing.baseReference.withMutability(TypeMutability.EXCLUSIVE)
    }

    /**
     * the absolute top type (the type that is a supertype of all possible types), `read Any?`.
     */
    val topTypeRef by lazy {
        any.baseReference
            .withMutability(TypeMutability.READONLY)
            .withCombinedNullability(TypeReference.Nullability.NULLABLE)
    }

    /** the type to use when a type cannot be determined, see [UnresolvedType] */
    val unresolvableReplacementType: BoundTypeReference get() = topTypeRef
}