package compiler.compiler.binding

import compiler.compiler.negative.moduleBackendIrAssumingNoErrors
import compiler.compiler.negative.validateModule
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrUnreachableStatement
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.shouldBe

class WhenExhaustivenessIrTests : FreeSpec({
    val module: IrModule = validateModule("""
        interface I {}
        class A : I {}
        class B : I {}
        intrinsic fn sideEffect()

        fn exhaustive(p: I) -> S32 = when p {
            is A -> 1
            is B -> 2
        }
        fn notExhaustive(p: I) {
            when p {
                is A -> sideEffect()
            }
        }
    """.trimIndent()).moduleBackendIrAssumingNoErrors()

    fun body(name: String): IrCodeChunk = module.packages
        .flatMap { it.functions }
        .single { it.canonicalName.simpleName == name }
        .overloads.single()
        .body!!

    /** the unreachable code the frontend adds after code that doesn't complete normally is provably unreachable */
    fun unreachableFallbacksIn(name: String) = collectIr(body(name))
        .filterIsInstance<IrUnreachableStatement>()
        .filter { !it.isProvablyUnreachable }

    "the implicit else branch of an exhaustive when is unreachable" {
        unreachableFallbacksIn("exhaustive") shouldHaveSize 1

        val ifs = collectIr(body("exhaustive")).filterIsInstance<IrIfExpression>()
        ifs shouldHaveSize 2
        ifs.forEach { it.elseBranch.shouldNotBeNull() }
        val innermostElse = ifs.last().elseBranch!!
        collectIr(innermostElse).filterIsInstance<IrUnreachableStatement>().any { !it.isProvablyUnreachable } shouldBe true
    }

    "the implicit else branch of a non-exhaustive when does nothing" {
        unreachableFallbacksIn("notExhaustive").shouldBeEmpty()
    }
})
