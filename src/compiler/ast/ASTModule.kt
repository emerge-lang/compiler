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
     * Works by the same principle as [Bindable.bindTo]; but since it does not yield any reportings and binds to
     * a [SoftwareContext] (rather than a [CTContext]) this has its own signature.
     */
    fun bindTo(context: SoftwareContext): Module {
        val moduleContext = MutableCTContext()
        moduleContext.swCtx = context

        for (import in imports)

        val module = Module(selfDeclaration?.name ?: emptyArray(), moduleContext)
    }
}