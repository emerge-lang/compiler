package compiler.ast

import compiler.lexer.SourceLocation

/**
 * The module declaration on top of a file.
 */
class ModuleDeclaration(
    override val declaredAt: SourceLocation,
    /** The identifiers in order of the source: `module module.submodule.submodule2` => `[module, submodule, submodule2]` */
    val name: Array<String>
) : Declaration