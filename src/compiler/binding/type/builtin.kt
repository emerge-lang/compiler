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

package compiler.binding.type

import compiler.ast.ASTModule
import compiler.ast.FunctionDeclaration
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.context.Module
import compiler.binding.context.ModuleRootContext
import compiler.parseFromClasspath

/*
 * This file contains raw definitions of the builtin types.
 * Actual operations on these types are defined in the source
 * language in the stdlib as external functions with receiver.
 * The actual implementations are defined within the stdlib
 * package.
 */

val Any = object : BuiltinType("Any") {}

val Unit = object : BuiltinType("Unit", Any) {}

val Number = object : BuiltinType("Number", Any) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}

val Float = object : BuiltinType("Float", Number) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}

val Int = object : BuiltinType("Int", Number) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}

val BuiltinBoolean = object : BuiltinType("Boolean", Any) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}


/**
 * A BuiltinType is defined in the ROOT package.
 */
abstract class BuiltinType(final override val simpleName: String, vararg superTypes: BaseType) : BaseType {
    final override val fullyQualifiedName = "$DEFAULT_MODULE_NAME_STRING.$simpleName"

    final override val superTypes: Set<BaseType> = superTypes.toSet()

    /**
     * BaseTypes do not define anything themselves. All of that is defined in source language in the
     * stdlib and implementation is provided from elsewhere, probably platform-specific.
     */
    final override fun resolveMemberFunction(name: String) = emptySet<FunctionDeclaration>()

    companion object {
        val DEFAULT_MODULE_NAME = arrayOf("dotlin", "lang")
        val DEFAULT_MODULE_NAME_STRING = DEFAULT_MODULE_NAME.joinToString(".")

        private val stdlib: ASTModule = parseFromClasspath("builtin.dt")
        fun getNewModule(): Module {
            val moduleContext = ModuleRootContext()
            val module = Module(DEFAULT_MODULE_NAME, moduleContext)

            module.context.addBaseType(Any)
            module.context.addBaseType(Unit)
            module.context.addBaseType(Number)
            module.context.addBaseType(Float)
            module.context.addBaseType(Int)
            module.context.addBaseType(BuiltinBoolean)

            stdlib.functions.forEach { module.context.addFunction(it) }
            stdlib.variables.forEach { module.context.addVariable(it) }

            return module
        }
    }
}