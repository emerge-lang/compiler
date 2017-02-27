package compiler.ast.context

import compiler.ast.ModuleDeclaration

/**
 * A module, as declared by a source file.
 */
class Module(
    val declaration: ModuleDeclaration,
    val context: CTContext
)