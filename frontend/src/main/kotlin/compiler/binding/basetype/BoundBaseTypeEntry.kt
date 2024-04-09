package compiler.binding.basetype

import compiler.ast.ClassEntryDeclaration
import compiler.binding.BoundElement
import compiler.binding.SemanticallyAnalyzable

sealed interface BoundBaseTypeEntry<AstNode : ClassEntryDeclaration> : BoundElement<AstNode>, SemanticallyAnalyzable {
}