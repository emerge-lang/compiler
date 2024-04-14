package compiler.binding.basetype

import compiler.ast.BaseTypeEntryDeclaration
import compiler.binding.SemanticallyAnalyzable
import compiler.lexer.SourceLocation

sealed interface BoundBaseTypeEntry<AstNode : BaseTypeEntryDeclaration> : SemanticallyAnalyzable {
    val declaredAt: SourceLocation
}