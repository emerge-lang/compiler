package compiler.diagnostic

import compiler.binding.basetype.BoundBaseTypeMemberVariable

class ClassMemberVariableDefaultValueNotAssignableDiagnostic(val member: BoundBaseTypeMemberVariable, base: ValueNotAssignableDiagnostic) : Diagnostic(
    base.level,
    "Cannot assign this default value to class member ${member.name}: ${base.reason}",
    base.span,
)