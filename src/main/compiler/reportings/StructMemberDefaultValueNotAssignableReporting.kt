package compiler.reportings

import compiler.binding.struct.StructMember

class StructMemberDefaultValueNotAssignableReporting(val member: StructMember, base: ValueNotAssignableReporting) : Reporting(
    base.level,
    "Cannot assign this default value to struct member ${member.name}: ${base.reason}",
    base.sourceLocation,
)