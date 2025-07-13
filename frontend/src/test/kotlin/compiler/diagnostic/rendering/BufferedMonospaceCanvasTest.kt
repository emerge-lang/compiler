package compiler.compiler.diagnostic.rendering

import compiler.diagnostic.rendering.TextSpan
import compiler.diagnostic.rendering.createBufferedMonospaceCanvas
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BufferedMonospaceCanvasTest : FreeSpec({
    "foo" {
        val canvas = createBufferedMonospaceCanvas()
        canvas.toString() shouldBe ""

        val insertsFirst = canvas.createViewAppendingToBlankLine()
        insertsFirst.toString() shouldBe ""

        val insertsSecond = canvas.createViewAppendingToBlankLine()
        insertsSecond.toString() shouldBe ""

        canvas.append(TextSpan("to the root"))
        val insertsFourth = canvas.createViewAppendingToBlankLine()

        insertsFirst.append(TextSpan("a"))
        insertsFirst.appendLineBreak()
        insertsFirst.append(TextSpan("b"))

        insertsSecond.append(TextSpan("c"))
        insertsSecond.appendLineBreak()
        insertsSecond.append(TextSpan("d"))

        insertsFourth.append(TextSpan("e"))
        insertsFourth.appendLineBreak()
        insertsFourth.append(TextSpan("f"))

        insertsFirst.toString() shouldBe "a\nb\n"
        insertsSecond.toString() shouldBe "c\nd\n"

        insertsFourth.toString() shouldBe "e\nf\n"

        canvas.toString() shouldBe "a\nb\nc\nd\nto the root\ne\nf\n"
    }
})