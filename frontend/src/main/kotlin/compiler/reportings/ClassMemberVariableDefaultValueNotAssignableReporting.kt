package compiler.reportings

import compiler.binding.classdef.BoundClassMemberVariable

class ClassMemberVariableDefaultValueNotAssignableReporting(val member: BoundClassMemberVariable, base: ValueNotAssignableReporting) : Reporting(
    base.level,
    "Cannot assign this default value to class member ${member.name}: ${base.reason}",
    base.sourceLocation,
)