package compiler

import compiler.reportings.Reporting

class OnceAction {
    private val actionResults = mutableMapOf<ActionToken<*>, Any?>()

    fun <ActionResult> getResult(token: ActionToken<ActionResult>, impl: () -> ActionResult): ActionResult {
        // do not use computeIfAbsent to avoid ConcurrentModificationException in case of cyclic logic in the source

        if (actionResults.containsKey(token)) {
            @Suppress("UNCHECKED_CAST")
            return actionResults[token] as ActionResult
        }

        val result = impl()
        actionResults[token] = result
        return result
    }

    fun requireActionDone(action: ActionToken<*>) {
        if (!actionResults.containsKey(action)) {
            throw InternalCompilerError("Action ${action.javaClass.simpleName} is required but has not been executed yet.")
        }
    }

    fun requireActionNotDone(action: ActionToken<*>) {
        if (actionResults.containsKey(action)) {
            throw InternalCompilerError("Action ${action.javaClass.simpleName} must not have been executed yed.")
        }
    }

    interface ActionToken<Result>
    object SemanticAnalysisPhase1 : ActionToken<Collection<Reporting>>
    object SemanticAnalysisPhase2 : ActionToken<Collection<Reporting>>
    object SemanticAnalysisPhase3 : ActionToken<Collection<Reporting>>
}
