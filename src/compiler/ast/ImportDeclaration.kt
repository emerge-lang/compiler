package compiler.ast

import compiler.lexer.IdentifierToken

/**
 * An import statement
 */
class ImportDeclaration(
    /** The identifiers in order of the source: `import module1.module2.component` => `[module1, module2, component]` */
    val identifiers: List<IdentifierToken>
)