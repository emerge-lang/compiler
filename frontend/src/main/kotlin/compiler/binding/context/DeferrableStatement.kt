package compiler.binding.context

import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

/**
 * Code that can be executed with defer semantics (will always be executed when the scope in which it was deferred
 * exits).
 * @see ExecutionScopedCTContext.addDeferredCode
 */
interface DeferrableExecutable {
    val span: Span
    fun toBackendIrStatement(): IrExecutable
}