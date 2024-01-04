package compiler

import io.kotest.matchers.shouldBe
import org.junit.jupiter.api.Test

class CyclicInvocationHandlerTest {
    @Test
    fun should_throw_on_cyclic_invocation() {
        a(Any()) shouldBe "cycle"
    }
}

private fun b(c: Any) : String {
    return a(c)
}

private fun a(c: Any) : String {
    return handleCyclicInvocation(
        context = c,
        action = { b(c) },
        onCycle = { "cycle" },
    )
}
