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

package compiler.ast

import compiler.ast.struct.StructDeclaration
import compiler.binding.context.Module
import compiler.binding.context.MutableCTContext
import compiler.binding.context.SoftwareContext
import compiler.reportings.Reporting

/**
 * AST representation of a module
 */
class ASTModule {
    var selfDeclaration: ModuleDeclaration? = null

    val imports: MutableList<ImportDeclaration> = mutableListOf()

    val variables: MutableList<VariableDeclaration> = mutableListOf()

    val functions: MutableList<FunctionDeclaration> = mutableListOf()

    val structs: MutableList<StructDeclaration> = mutableListOf()

    /**
     * Works by the same principle as [Bindable.bindTo]; but since binds to a [SoftwareContext] (rather than a
     * [CTContext]) this has its own signature.
     */
    fun bindTo(context: SoftwareContext): Module {
        val moduleContext = MutableCTContext()
        val reportings = mutableSetOf<Reporting>()

        imports.forEach(moduleContext::addImport)
        functions.forEach { moduleContext.addFunction(it) }
        structs.forEach { moduleContext.addStruct(it.bindTo(moduleContext)) }

        variables.forEach { declaredVariable ->
            // check double declare
            val existingVariable = moduleContext.resolveVariable(declaredVariable.name.value, true)
            if (existingVariable == null || existingVariable.declaration === declaredVariable) {
                moduleContext.addVariable(declaredVariable)
            }
            else {
                // variable double-declared
                reportings.add(Reporting.variableDeclaredMoreThanOnce(existingVariable.declaration, declaredVariable))
            }
        }

        moduleContext.swCtx = context

        return Module(selfDeclaration?.name ?: emptyArray(), moduleContext, reportings)
    }
}