package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

/**
 * An import statement
 */
class ImportDeclaration(
    override val declaredAt: SourceLocation,
    /** The identifiers in order of the source: `import module1.module2.component` => `[module1, module2, component]` */
    val identifiers: List<IdentifierToken>
) : Declaration {

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as ImportDeclaration

        if (identifiers != other.identifiers) return false

        return true
    }

    override fun hashCode(): Int {
        return identifiers.hashCode()
    }
}