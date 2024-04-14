package compiler.binding.basetype

import compiler.ast.ClassEntryDeclaration
import compiler.binding.SemanticallyAnalyzable
import compiler.lexer.SourceLocation

sealed interface BoundBaseTypeEntry<AstNode : ClassEntryDeclaration> : SemanticallyAnalyzable {
    val declaredAt: SourceLocation
}