package compiler.diagnostic

import compiler.InternalCompilerError
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.BaseTypeEntryDeclaration
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.binding.basetype.BoundBaseType
import textutils.capitalizeFirst

class EntryNotAllowedInBaseTypeDiagnostic(
    val typeKind: BoundBaseType.Kind,
    val violatingEntry: BaseTypeEntryDeclaration,
) : Diagnostic(
    Severity.ERROR,
    run {
        val entryDesc = when (violatingEntry) {
            is BaseTypeConstructorDeclaration -> "constructors"
            is BaseTypeDestructorDeclaration -> "destructors"
            is BaseTypeMemberVariableDeclaration -> "member variables"
            else -> throw InternalCompilerError("The base type entry ${violatingEntry::class.simpleName} should be allowed in all base types")
        }
        "${entryDesc.capitalizeFirst()} are not allowed in ${typeKind.namePlural}"
    },
    violatingEntry.span,
)