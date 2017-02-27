package compiler.ast

import compiler.lexer.IdentifierToken

/**
 * The module declaration on top of a file.
 */
class ModuleDeclaration(
    /** The identifiers in order of the source: `module module.submodule.submodule2` => `[module, submodule, submodule2]` */
    val identifiers: List<IdentifierToken>
)