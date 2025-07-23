package compiler.compiler.binding.context

import compiler.binding.context.DeferrableExecutable
import compiler.binding.context.ModuleContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.PackageContext
import compiler.binding.context.SourceFileRootContext
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forNone
import io.kotest.matchers.shouldBe
import io.mockk.mockk

class ExecutionScopedCTContextTest : FreeSpec({
    "single lineage" - {
        val functionBoundary = MutableExecutionScopedCTContext.functionRootIn(mockSourceFileContext())
        val functionDeferredOne = mockk<DeferrableExecutable>()
        functionBoundary.addDeferredCode(functionDeferredOne)
        val functionDeferredTwo = mockk<DeferrableExecutable>()
        functionBoundary.addDeferredCode(functionDeferredTwo)

        val scopeBoundary = MutableExecutionScopedCTContext.deriveNewScopeFrom(functionBoundary)
        val scopeBoundaryDeferredOne = mockk<DeferrableExecutable>()
        scopeBoundary.addDeferredCode(scopeBoundaryDeferredOne)
        val scopeBoundaryDeferredTwo = mockk<DeferrableExecutable>()
        scopeBoundary.addDeferredCode(scopeBoundaryDeferredTwo)

        val leafContext = MutableExecutionScopedCTContext.deriveFrom(scopeBoundary)
        val leafDeferredOne = mockk<DeferrableExecutable>()
        leafContext.addDeferredCode(leafDeferredOne)
        val leafDeferredTwo = mockk<DeferrableExecutable>()
        leafContext.addDeferredCode(leafDeferredTwo)

        "defer in single context" {
            val deferreds = leafContext.getContextLocalDeferredCode().toList()
            deferreds shouldBe listOf(
                leafDeferredTwo,
                leafDeferredOne
            )
        }

        "defer up to scope boundary" {
            val deferreds = leafContext.getScopeLocalDeferredCode().toList()
            deferreds shouldBe listOf(
                leafDeferredTwo,
                leafDeferredOne,
                scopeBoundaryDeferredTwo,
                scopeBoundaryDeferredOne,
            )
        }

        "defer up to function boundary" {
            val deferreds = leafContext.getFunctionDeferredCode().toList()
            deferreds shouldBe listOf(
                leafDeferredTwo,
                leafDeferredOne,
                scopeBoundaryDeferredTwo,
                scopeBoundaryDeferredOne,
                functionDeferredTwo,
                functionDeferredOne,
            )
        }
    }
    "split lineage" - {
        val functionBoundary = MutableExecutionScopedCTContext.functionRootIn(mockSourceFileContext())
        val functionDeferred = mockk<DeferrableExecutable>()
        functionBoundary.addDeferredCode(functionDeferred)

        val stepOne = MutableExecutionScopedCTContext.deriveFrom(functionBoundary)
        val branchOne = MutableExecutionScopedCTContext.deriveNewScopeFrom(stepOne)
        val branchOneDeferred = mockk<DeferrableExecutable>()
        branchOne.addDeferredCode(branchOneDeferred)
        val branchTwo = MutableExecutionScopedCTContext.deriveNewScopeFrom(stepOne)
        val branchTwoDeferred = mockk<DeferrableExecutable>()
        branchTwo.addDeferredCode(branchTwoDeferred)

        val continueStep = MutableExecutionScopedCTContext.deriveFrom(stepOne)
        val commonDeferrableLast = mockk<DeferrableExecutable>()
        continueStep.addDeferredCode(commonDeferrableLast)

        "branch one" - {
            "scope local" {
                val deferreds = branchOne.getScopeLocalDeferredCode().toList()
                deferreds shouldBe listOf(
                    branchOneDeferred
                )
            }

            "all function" {
                val deferreds = branchOne.getFunctionDeferredCode().toList()
                deferreds shouldBe listOf(
                    branchOneDeferred,
                    functionDeferred
                )
            }
        }

        "branch two" - {
            "scope local" {
                val deferreds = branchTwo.getScopeLocalDeferredCode().toList()
                deferreds shouldBe listOf(
                    branchTwoDeferred
                )
            }

            "all function" {
                val deferreds = branchTwo.getFunctionDeferredCode().toList()
                deferreds shouldBe listOf(
                    branchTwoDeferred,
                    functionDeferred
                )
            }
        }

        "continuation scope" - {
            "scope local should exclude branches" {
                val deferreds = continueStep.getScopeLocalDeferredCode()
                deferreds.forNone {
                    it shouldBe branchOneDeferred
                }
                deferreds.forNone {
                    it shouldBe branchTwoDeferred
                }
            }

            "all function should exclude branches" {
                val deferreds = continueStep.getScopeLocalDeferredCode()
                deferreds.forNone {
                    it shouldBe branchOneDeferred
                }
                deferreds.forNone {
                    it shouldBe branchTwoDeferred
                }
            }
        }
    }
})

private fun mockSourceFileContext(): SourceFileRootContext {
    val name = CanonicalElementName.Package(listOf("mock"))
    return SourceFileRootContext(PackageContext(ModuleContext(name, emptySet(), mockk()), name), name)
}
