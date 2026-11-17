package compiler.compiler.binding

import compiler.compiler.negative.moduleBackendIrAssumingNoErrors
import compiler.compiler.negative.validateModule
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntersectionType
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldContainExactly
import io.kotest.matchers.collections.shouldContainExactlyInAnyOrder
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf
import java.lang.reflect.Modifier
import java.util.Collections
import java.util.IdentityHashMap

/**
 * The backends rely on the types in the IR to choose the representation of values (e.g. pointer to a class vs. to
 * any object, boxed vs. unboxed), so the types refined by the frontend (smart casts, `!!`) have to show in the IR.
 */
class SmartCastIrTests : FreeSpec({
    val module: IrModule = validateModule("""
        interface Foo {}
        class Bar : Foo {
            p: String = init
        }
        fn takeFoo(v: Foo) {}
        fn takeBar(v: Bar) {}
        fn produce() -> Foo = Bar("x")

        fn fieldRead(v: Foo) -> String {
            if v is Bar {
                return v.p
            }
            return "not a bar"
        }
        fn elseAndAfter(v: Foo) {
            if v is Bar {
                takeBar(v)
            } else {
                takeFoo(v)
            }
            takeFoo(v)
        }
        fn reassigned(v: Foo) {
            var w = v
            if w is Bar {
                takeBar(w)
                set w = produce()
                takeFoo(w)
            }
        }
        fn refinedToValueType(v: Any) -> S32 {
            if v is S32 {
                return v
            }
            return 0
        }
        fn notNull(v: S32?) -> S32 = v!!
        class Holder : NonToken {
            f: Foo = init
        }
        fn memberField(h: Holder) -> String {
            if h.f is Bar {
                return h.f.p
            }
            return "not a bar"
        }
        fn isNullFalse(v: S32?) -> S32 {
            if isNull(v) {
                return 0
            } else {
                return v
            }
        }
        fn generic<T>(v: T) -> String {
            if v is Bar {
                return v.p
            }
            return "not a bar"
        }
        fn rhsOfAnd(v: Bar?) -> Bool = not isNull(v) and v.p == "x"
        fn rhsOfOr(v: Bar?) -> Bool = isNull(v) or v.p == "x"
    """.trimIndent()).moduleBackendIrAssumingNoErrors()

    fun body(name: String): IrCodeChunk = module.packages
        .flatMap { it.functions }
        .single { it.canonicalName.simpleName == name }
        .overloads.single()
        .body!!

    fun readsOf(variableName: String, fnName: String): List<IrVariableAccessExpression> = collectIr(body(fnName))
        .filterIsInstance<IrVariableAccessExpression>()
        .filter { it.variable.name == variableName }

    fun argumentTypesOfCallsTo(calledFnName: String, inFn: String): List<String> = collectIr(body(inFn))
        .filterIsInstance<IrInvocationExpression>()
        .filter { it.function.canonicalName.simpleName == calledFnName }
        .map { it.arguments.single().type.simpleName }

    "a variable read inside the branch of an is-check has the refined type" {
        val fieldAccess = collectIr(body("fieldRead"))
            .filterIsInstance<IrClassFieldAccessExpression>()
            .single()

        fieldAccess.base.type.simpleName shouldBe "Bar"
        val read = fieldAccess.base.declaration.value.shouldBeInstanceOf<IrVariableAccessExpression>()
        read.variable.type.simpleName shouldBe "Foo"
        read.evaluatesTo.simpleName shouldBe "Bar"
    }

    "the refinement does not reach the else branch and the code after the if" {
        argumentTypesOfCallsTo("takeBar", "elseAndAfter") shouldContainExactly listOf("Bar")
        argumentTypesOfCallsTo("takeFoo", "elseAndAfter") shouldContainExactly listOf("Foo", "Foo")
    }

    "a new value assigned to the variable ends the refinement" {
        argumentTypesOfCallsTo("takeBar", "reassigned") shouldContainExactly listOf("Bar")
        argumentTypesOfCallsTo("takeFoo", "reassigned") shouldContainExactly listOf("Foo")
    }

    "a variable refined to a value type reads as the value type" {
        // the others are the is-check and reads that the frontend adds, e.g. for reference counting
        val refinedReads = readsOf("v", "refinedToValueType").filter { it.evaluatesTo.simpleName != "Any" }
        refinedReads.map { it.evaluatesTo.simpleName } shouldContainExactly listOf("S32")
        refinedReads.single().evaluatesTo.isNullable shouldBe false
    }

    "not-null assertion evaluates to the non-nullable type" {
        val notNullResults = collectIr(body("notNull"))
            .filterIsInstance<IrImplicitEvaluationExpression>()
            .filter { it.implicitValue.declaration.type.isNullable }
        notNullResults shouldHaveSize 1
        val result = notNullResults.single()
        result.evaluatesTo.isNullable shouldBe false
        result.evaluatesTo.simpleName shouldBe "S32"
    }

    "a variable read where isNull returned false has the non-nullable type" {
        val refinedReads = readsOf("v", "isNullFalse").filter { !it.evaluatesTo.isNullable }
        refinedReads.map { it.evaluatesTo.simpleName } shouldContainExactly listOf("S32")
    }

    "a member variable read inside the branch of an is-check has the refined type" {
        val fieldAccesses = collectIr(body("memberField")).filterIsInstance<IrClassFieldAccessExpression>()
        val readOfP = fieldAccesses.single { it.evaluatesTo.simpleName == "String" }
        readOfP.base.type.simpleName shouldBe "Bar"
        val readsOfF = fieldAccesses.filter { it !== readOfP }
        // Foo & NonToken: the member variable of a NonToken class
        readsOfF.map { it.evaluatesTo.simpleName } shouldContainExactlyInAnyOrder listOf("Foo & NonToken", "Bar")
    }

    "the right-hand side of and is evaluated only in the then-branch, with the refinement from the left-hand side" {
        val ifExpr = collectIr(body("rhsOfAnd")).filterIsInstance<IrIfExpression>().single()
        val fieldAccess = collectIr(ifExpr.thenBranch).filterIsInstance<IrClassFieldAccessExpression>().single()
        fieldAccess.base.type.simpleName shouldBe "Bar"
        fieldAccess.base.type.isNullable shouldBe false
        collectIr(ifExpr.elseBranch!!).filterIsInstance<IrBooleanLiteralExpression>().single().value shouldBe false
    }

    "the right-hand side of or is evaluated only in the else-branch, with the refinement from the left-hand side" {
        val ifExpr = collectIr(body("rhsOfOr")).filterIsInstance<IrIfExpression>().single()
        val fieldAccess = collectIr(ifExpr.elseBranch!!).filterIsInstance<IrClassFieldAccessExpression>().single()
        fieldAccess.base.type.simpleName shouldBe "Bar"
        fieldAccess.base.type.isNullable shouldBe false
        collectIr(ifExpr.thenBranch).filterIsInstance<IrBooleanLiteralExpression>().single().value shouldBe true
    }

    "a variable of a generic type refined to a class can access its fields" {
        val fieldAccess = collectIr(body("generic"))
            .filterIsInstance<IrClassFieldAccessExpression>()
            .single()

        val baseType = fieldAccess.base.type
        if (baseType is IrIntersectionType) {
            baseType.components.map { it.simpleName } shouldContainExactlyInAnyOrder listOf("T", "Bar")
        } else {
            baseType.simpleName shouldBe "Bar"
        }
    }
})

private val IrType.simpleName: String get() = when (this) {
    is IrSimpleType -> baseType.canonicalName.simpleName
    is io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType -> simpleType.simpleName
    is io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference -> parameter.name
    is IrIntersectionType -> components.joinToString(" & ") { it.simpleName }
}

/**
 * @return all [IrExecutable]s and [IrExpression]s below [root], in a pre-order traversal
 */
private fun collectIr(root: Any): List<Any> {
    val visited: MutableSet<Any> = Collections.newSetFromMap(IdentityHashMap())
    val result = ArrayList<Any>()
    fun visit(node: Any) {
        if (!visited.add(node)) {
            return
        }
        result.add(node)
        node.javaClass.methods
            .asSequence()
            .filter { it.parameterCount == 0 && !Modifier.isStatic(it.modifiers) && it.name.startsWith("get") }
            .filter { it.declaringClass.name.startsWith("io.github.tmarsteel.emerge.backend.api.ir.") || it.declaringClass == node.javaClass }
            .sortedBy { it.name }
            .forEach { getter ->
                getter.isAccessible = true
                val children = when (val value = getter.invoke(node)) {
                    is IrExecutable, is IrExpression, is IrInvocationExpression.Landingpad -> listOf(value)
                    is Iterable<*> -> value.filter { it is IrExecutable || it is IrExpression || it is IrInvocationExpression.Landingpad }
                    else -> emptyList()
                }
                children.forEach { visit(it!!) }
            }
    }
    visit(root)
    return result
}
