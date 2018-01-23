package compiler.ast

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

    /**
     * Works by the same principle as [Bindable.bindTo]; but since binds to a [SoftwareContext] (rather than a
     * [CTContext]) this has its own signature.
     */
    fun bindTo(context: SoftwareContext): Module {
        val moduleContext = MutableCTContext()
        val reportings = mutableSetOf<Reporting>()

        imports.forEach(moduleContext::addImport)
        functions.forEach { moduleContext.addFunction(it) }

        variables.forEach { declaredVariable ->
            // check double declare
            val existingVariable = moduleContext.resolveVariable(declaredVariable.name.value, true)
            if (existingVariable == null || existingVariable.declaration === declaredVariable) {
                moduleContext.addVariable(declaredVariable)
            }
            else {
                // variable double-declared
                reportings.add(Reporting.error("Variable ${declaredVariable.name.value} has already been defined in ${existingVariable.declaration.declaredAt.fileLineColumnText}", declaredVariable.name))
            }
        }

        moduleContext.swCtx = context

        return Module(selfDeclaration?.name ?: emptyArray(), moduleContext, reportings)
    }
}