package compiler.reportings

import compiler.binding.basetype.BoundBaseTypeMemberVariable

class ClassMemberVariableDefaultValueNotAssignableReporting(val member: BoundBaseTypeMemberVariable, base: ValueNotAssignableReporting) : Reporting(
    base.level,
    "Cannot assign this default value to class member ${member.name}: ${base.reason}",
    base.sourceLocation,
)