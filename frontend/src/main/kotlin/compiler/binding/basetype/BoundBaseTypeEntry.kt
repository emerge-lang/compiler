package compiler.binding.basetype

import compiler.ast.BaseTypeEntryDeclaration
import compiler.binding.SemanticallyAnalyzable
import compiler.lexer.Span

sealed interface BoundBaseTypeEntry<AstNode : BaseTypeEntryDeclaration> : SemanticallyAnalyzable {
    val entryDeclaration: AstNode
    val declaredAt: Span
}