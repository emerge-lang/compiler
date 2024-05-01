package compiler.compiler.binding.context

import compiler.ast.Statement
import compiler.binding.BoundStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.ModuleContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.PackageContext
import compiler.binding.context.SourceFileRootContext
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forNone
import io.kotest.matchers.shouldBe
import io.mockk.mockk
import kotlin.reflect.KProperty

class ExecutionScopedCTContextTest : FreeSpec({
    "single lineage" - {
        val functionBoundary = MutableExecutionScopedCTContext.functionRootIn(mockSourceFileContext())
        val functionDeferredOne by mockDeferrable()
        functionBoundary.addDeferredCode(functionDeferredOne)
        val functionDeferredTwo by mockDeferrable()
        functionBoundary.addDeferredCode(functionDeferredTwo)

        val scopeBoundary = MutableExecutionScopedCTContext.deriveNewScopeFrom(functionBoundary)
        val scopeBoundaryDeferredOne by mockDeferrable()
        scopeBoundary.addDeferredCode(scopeBoundaryDeferredOne)
        val scopeBoundaryDeferredTwo by mockDeferrable()
        scopeBoundary.addDeferredCode(scopeBoundaryDeferredTwo)

        val leafContext = MutableExecutionScopedCTContext.deriveFrom(scopeBoundary)
        val leafDeferredOne by mockDeferrable()
        leafContext.addDeferredCode(leafDeferredOne)
        val leafDeferredTwo by mockDeferrable()
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
        val functionDeferred by mockDeferrable()
        functionBoundary.addDeferredCode(functionDeferred)

        val stepOne = MutableExecutionScopedCTContext.deriveFrom(functionBoundary)
        val branchOne = MutableExecutionScopedCTContext.deriveNewScopeFrom(stepOne)
        val branchOneDeferred by mockDeferrable()
        branchOne.addDeferredCode(branchOneDeferred)
        val branchTwo = MutableExecutionScopedCTContext.deriveNewScopeFrom(stepOne)
        val branchTwoDeferred by mockDeferrable()
        branchTwo.addDeferredCode(branchTwoDeferred)

        val continueStep = MutableExecutionScopedCTContext.deriveFrom(stepOne)
        val commonDeferrableLast by mockDeferrable()
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
    return SourceFileRootContext(PackageContext(ModuleContext(name, mockk()), name))
}

private fun mockDeferrable() = object {
    private lateinit var instance: Statement
    operator fun getValue(thisRef: Any?, prop: KProperty<*>): Statement {
        if (!this::instance.isInitialized) {
            this.instance = object : Statement, BoundStatement<Statement> by mockk() {
                val span: Span
                    get() = mockk()

                override lateinit var modifiedContext: ExecutionScopedCTContext
                    private set
                override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
                    modifiedContext = context
                    return this
                }

                override fun toString() = "Mock[${prop.name}]"
            }
        }
        return this.instance
    }
}
