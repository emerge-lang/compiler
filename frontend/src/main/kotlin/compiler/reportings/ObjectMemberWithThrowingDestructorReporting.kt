package compiler.reportings

import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable

class ObjectMemberWithThrowingDestructorReporting(
    val memberVariable: BoundBaseTypeMemberVariable,
    val ownedBy: BoundBaseType,
    val boundary: SideEffectBoundary.Function,
) : Reporting(
    Level.ERROR,
    "The destructor of this member may throw, but the destructor of the enclosing ${ownedBy.kind} is declared ${boundary.function.attributes.firstNothrowAttribute!!.attributeName.keyword.text}",
    memberVariable.declaration.span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(
        SourceHint(boundary.function.attributes.firstNothrowAttribute!!.sourceLocation, "destructor declared ${boundary.function.attributes.firstNothrowAttribute!!.attributeName.keyword.text}", relativeOrderMatters = true),
        SourceHint(memberVariable.declaration.span, "when destructing ${ownedBy.simpleName}, this value of type ${memberVariable.type?.simpleName ?: "<UNKNOWN>"} may get destructed, too, and that may throw an exception", relativeOrderMatters = true),
    )}"
}