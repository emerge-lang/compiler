package compiler.compiler.negative

import compiler.ast.AstThrowExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.binding.context.effect.CallFrameExit
import compiler.diagnostic.UnreachableCodeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class TerminationAnalysisErrors : FreeSpec({
    "unreachable code in code block" - {
        "by throw" {
            validateModule("""
                intrinsic fn makeEx() -> exclusive Throwable
                fn test() {
                    throw makeEx()
                    other()
                }
                intrinsic fn other()
            """.trimIndent())
                .shouldFind<UnreachableCodeDiagnostic> {
                    it.previousCodeThatTerminates.shouldBeInstanceOf<AstThrowExpression>()
                    it.unreachableCode.shouldBeInstanceOf<InvocationExpression>().targetExpression.shouldBeInstanceOf<IdentifierExpression>().identifier.value shouldBe "other"
                }
        }

        "by calling a definitely throwing function" {
            validateModule("""
                intrinsic fn definitelyThrows() -> Nothing
                fn test() {
                    definitelyThrows()
                    other()
                }
                intrinsic fn other()
            """.trimIndent())
                .shouldFind<UnreachableCodeDiagnostic> {
                    it.previousCodeThatTerminates.shouldBeInstanceOf<InvocationExpression>().targetExpression.shouldBeInstanceOf<IdentifierExpression>().identifier.value shouldBe "definitelyThrows"
                    it.unreachableCode.shouldBeInstanceOf<InvocationExpression>().targetExpression.shouldBeInstanceOf<IdentifierExpression>().identifier.value shouldBe "other"
                }
        }

        "by calling a function that terminates the program (panic)" {
            val state1 = CallFrameExit.initialState
            val state2 = CallFrameExit.fold(state1, CallFrameExit.Effect.InvokesFunction(
                CallFrameExit.FunctionBehavior(
                    throws = CallFrameExit.Occurrence.NEVER,
                    terminates = CallFrameExit.Occurrence.GUARANTEED,
                )
            ))

            validateModule("""
                intrinsic nothrow fn terminateProgram() -> Nothing
                fn test() {
                    terminateProgram()
                    other()
                }
                intrinsic fn other()
            """.trimIndent())
                .shouldFind<UnreachableCodeDiagnostic> {
                    it.previousCodeThatTerminates.shouldBeInstanceOf<InvocationExpression>().targetExpression.shouldBeInstanceOf<IdentifierExpression>().identifier.value shouldBe "terminateProgram"
                    it.unreachableCode.shouldBeInstanceOf<InvocationExpression>().targetExpression.shouldBeInstanceOf<IdentifierExpression>().identifier.value shouldBe "other"
                }
        }
    }
})