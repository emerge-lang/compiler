package compiler.reportings

import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundFunction
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.Span

open class NothrowViolationReporting(
    level: Level,
    message: String,
    sourceLocation: Span,
) : Reporting(level, message, sourceLocation) {
    class PotentialThrowingDestruction(
        /** just for deduping diagnostics */
        val reference: Any,
        val referenceDescription: String,
        val referenceDroppedOrDeclaredAt: Span,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationReporting(
        Level.ERROR,
        "When $referenceDescription is dropped, the destructor may throw. This is not allowed in a nothrow context ($boundary).",
        referenceDroppedOrDeclaredAt,
    ) {
        override fun toString() = "$levelAndMessage\n${illustrateHints(
            SourceHint(boundary.nothrowDeclaredAt, "function declared nothrow here"),
            SourceHint(referenceDroppedOrDeclaredAt, "potentially throwing destructor execution here"),
        )}"
    }

    class NotNullAssertion(
        val assertion: NotNullExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationReporting(
        Level.ERROR,
        "Cannot use !! in in nothrow $boundary; it can throw a NullPointerError",
        assertion.notNullOperator.span,
    )

    class ObjectMemberWithThrowingDestructor(
        val memberVariable: BoundBaseTypeMemberVariable,
        val ownedBy: BoundBaseType,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationReporting(
        Level.ERROR,
        "The destructor of this member may throw, but $boundary is declared nothrow",
        memberVariable.declaration.span,
    ) {
        override fun toString() = "$levelAndMessage\n${illustrateHints(
            SourceHint(boundary.nothrowDeclaredAt, "destructor declared nothrow here", relativeOrderMatters = true),
            SourceHint(memberVariable.declaration.span, "when destructing ${ownedBy.simpleName}, this value of type ${memberVariable.type?.simpleName ?: "<UNKNOWN>"} may get destructed, too, and that may throw an exception", relativeOrderMatters = true),
        )}"
    }

    class ThrowingInvocation(
        val invocation: BoundInvocationExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationReporting(
        Level.ERROR,
        "Cannot invoke possibly-throwing function ${invocation.functionToInvoke!!.canonicalName} in nothrow $boundary",
        invocation.declaration.span,
    )

    sealed interface SideEffectBoundary {
        val nothrowDeclaredAt: Span
        class Function(
            val fn: BoundFunction
        ) : SideEffectBoundary {
            override val nothrowDeclaredAt get() = fn.attributes.firstNothrowAttribute!!.sourceLocation

            override fun toString() = when (fn) {
                is BoundClassConstructor -> "constructor of ${fn.classDef.simpleName}"
                is BoundClassDestructor -> "destructor of ${fn.classDef.simpleName}"
                else -> "function ${fn.name}"
            }
        }
    }
}