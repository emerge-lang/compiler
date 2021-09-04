package matchers.compiler

import compiler.EarlyStackOverflowException
import compiler.throwOnCycle
import io.kotlintest.matchers.shouldThrow
import org.junit.Test

class ThrowOnCycleTest {
    @Test
    fun should_throw_on_cyclic_invocation() {
        shouldThrow<EarlyStackOverflowException> {
            a(Any())
        }
    }
}

private fun b(c: Any) {
    a(c)
}

private fun a(c: Any) {
    throwOnCycle(c) {
        b(c)
    }
}
