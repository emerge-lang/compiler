package compiler.reportings

import compiler.binding.classdef.ClassMemberVariable

class ClassMemberVariableDefaultValueNotAssignableReporting(val member: ClassMemberVariable, base: ValueNotAssignableReporting) : Reporting(
    base.level,
    "Cannot assign this default value to class member ${member.name}: ${base.reason}",
    base.sourceLocation,
)