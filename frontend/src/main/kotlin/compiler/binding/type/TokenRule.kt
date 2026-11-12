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
    private val assigneeKnownToBeNoToken: ThreadLocal<Int> = ThreadLocal.withInitial { 0 }

    /**
     * Runs [action], in which the components of an intersection are assigned one by one. Where the intersection
     * as a whole cannot be a token (`Animal & NonToken`), neither can the value, though a component alone
     * (`Animal`) doesn't say so.
     */
    fun <R> forComponentsOf(intersection: BoundIntersectionTypeReference, action: () -> R): R {
        if (intersection.mayBeToken) {
            return action()
        }

        assigneeKnownToBeNoToken.set(assigneeKnownToBeNoToken.get() + 1)
        try {
            return action()
        } finally {
            assigneeKnownToBeNoToken.set(assigneeKnownToBeNoToken.get() - 1)
        }
    }

    /**
     * @return the reason why a value of [assigneeType] cannot be assigned to [targetType] by this rule, `null` if
     * the rule has no objection.
     */
    fun check(targetType: BoundTypeReference, assigneeType: BoundTypeReference, assignmentLocation: Span): ValueNotAssignableDiagnostic? {
        if (assigneeKnownToBeNoToken.get() > 0 || !assigneeType.mayBeToken || targetType.mayBeToken) {
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
