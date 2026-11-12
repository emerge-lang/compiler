package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span

/**
 * A value that may be a token ([BoundTypeReference.mayBeToken]) is not assignable to a type that cannot be one:
 * a token is never forgotten, and never frozen. This is that check, for the implementations of
 * [BoundTypeReference.unify] that decide assignability by more than delegating to another one.
 */
internal object TokenRule {
    /**
     * @return the reason why a value of [assigneeType] cannot be assigned to [targetType] by this rule, `null` if
     * the rule has no objection.
     */
    fun check(targetType: BoundTypeReference, assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): ValueNotAssignableDiagnostic? {
        if (carry.assigneeIsKnownToBeNoToken || !assigneeType.mayBeToken || targetType.mayBeToken) {
            return null
        }
        if (targetType.mentionsTypeVariables() || assigneeType.mentionsTypeVariables()) {
            // not decided as long as a variable is not bound. The types of a call are checked again once they are
            // inferred; until then this rule must not fail the unification that is to find the bindings.
            return null
        }

        val reason = if (targetType.mutability == TypeMutability.IMMUTABLE && assigneeType.assignmentMutability == TypeMutability.OWN) {
            "a value of type $assigneeType may be a token, and a token cannot become const"
        } else {
            "a value of type $assigneeType may be a token, and $targetType cannot be one"
        }
        return ValueNotAssignableDiagnostic(targetType, assigneeType, reason, assignmentLocation)
    }
}
