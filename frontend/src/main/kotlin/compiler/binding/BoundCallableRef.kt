package compiler.binding

import compiler.binding.type.BoundFunctionType
import compiler.lexer.Span

/**
 * A reference to either a [BoundDeclaredFunction] or a [BoundFunctionType]
 */
sealed interface BoundCallableRef {
    val span: Span

    class DeclaredFn(
        /** for passing a forward reference */
        private val getInstance: () -> BoundFunction
    ) : BoundCallableRef {
        val boundElement: BoundFunction get() = getInstance()
        override val span: Span get()= boundElement.declaredAt

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is DeclaredFn) return false

            if (boundElement != other.boundElement) return false

            return true
        }

        override fun hashCode(): Int {
            return boundElement.hashCode()
        }
    }

    class FunctionType(
        /** for passing a forward reference */
        private val getInstance: () -> BoundFunctionType
    ): BoundCallableRef {
        val boundElement: BoundFunctionType get() = getInstance()
        override val span: Span get()= boundElement.span

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is FunctionType) return false

            if (boundElement != other.boundElement) return false

            return true
        }

        override fun hashCode(): Int {
            return boundElement.hashCode()
        }
    }
}