package compiler

import java.util.Objects

private fun getInvocationStackFrame(): StackTraceElement = Thread.currentThread().stackTrace[3]

private class ContextAtStackFrame(
    val context: Any,
    val stackFrame: StackTraceElement,
) {
    override fun equals(other: Any?): Boolean {
        if (other !is ContextAtStackFrame) {
            return false
        }

        return other.context === this.context && other.stackFrame == this.stackFrame
    }

    override fun hashCode(): Int {
        return Objects.hash(System.identityHashCode(context), stackFrame.hashCode())
    }

    override fun toString() = "$context at $stackFrame"
}

private class EarlyStackOverflowException(val context: ContextAtStackFrame? = null) : RuntimeException("Stack overflow") {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is EarlyStackOverflowException) return false

        if (context != other.context) return false

        return true
    }

    override fun hashCode(): Int {
        return context?.hashCode() ?: 0
    }
}

private val contexts: ThreadLocal<MutableSet<ContextAtStackFrame>> = ThreadLocal.withInitial(::HashSet)

fun <R> handleCyclicInvocation(
    context: Any,
    action: () -> R,
    onCycle: () -> R,
): R {
    val invocationContext = ContextAtStackFrame(context, getInvocationStackFrame())
    val threadContexts = contexts.get()
    if (invocationContext in threadContexts) {
        throw EarlyStackOverflowException(invocationContext)
    }
    threadContexts.add(invocationContext)

    return try {
        action()
    } catch (ex: EarlyStackOverflowException) {
        if (ex.context == invocationContext) {
            return onCycle()
        }

        throw ex
    } finally {
        threadContexts.remove(invocationContext)
        if (threadContexts.isEmpty()) {
            contexts.remove()
        }
    }
}
