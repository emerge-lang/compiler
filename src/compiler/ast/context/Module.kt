package compiler.ast.context

import compiler.ast.ModuleDeclaration
import compiler.ast.type.BuiltinType
import compiler.lexer.SourceLocation

/**
 * A module, as declared by a source file.
 */
class Module(
    val declaration: ModuleDeclaration,
    val context: CTContext
) {
    companion object {
        /** The ROOT module to which all actual modules are added */
        val ROOT: Module
        init {
            val rootDeclaration = ModuleDeclaration(SourceLocation.UNKNOWN, arrayOf())
            val context = MutableCTContext()
            context.include(BuiltinType.Context)
            ROOT = Module(rootDeclaration, context)
        }
    }
}