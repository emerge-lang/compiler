package compiler.ast

import compiler.binding.context.Module
import compiler.binding.context.MutableCTContext
import compiler.binding.context.SoftwareContext

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

        imports.forEach(moduleContext::addImport)
        variables.forEach { moduleContext.addVariable(it) }
        functions.forEach { moduleContext::addFunction }

        moduleContext.swCtx = context

        return Module(selfDeclaration?.name ?: emptyArray(), moduleContext)
    }
}