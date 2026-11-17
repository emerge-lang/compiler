package compiler.compiler.binding

import compiler.compiler.negative.moduleBackendIrAssumingNoErrors
import compiler.compiler.negative.validateModule
import io.github.tmarsteel.emerge.backend.api.ir.IrCatchExceptionStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDropStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrThrowStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTryCatchExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldContain
import io.kotest.matchers.collections.shouldContainAll
import io.kotest.matchers.collections.shouldNotBeEmpty
import io.kotest.matchers.collections.shouldNotContain
import java.lang.reflect.Modifier

/**
 * A throwable that is not caught leaves the function. Before it does, the references that the local variables and the
 * parameters hold have to be dropped, those of the scopes around a `try` included. That goes for `Error`s, too,
 * which pass by the `catch`. A program cannot observe this, an `Error` ends it; hence these tests look at the IR.
 */
class TryCatchCleanupIrTests : FreeSpec({
    val module: IrModule = validateModule("""
        class Thing {}
        class Oops : Throwable {
            constructor {
                mixin ThrowableTrait("oops")
            }
        }
        class Fatal : Error {
            constructor {
                mixin ThrowableTrait("fatal")
            }
        }
        fn mayThrow() {}
        fn pick() -> mut Throwable = Oops()

        fn viaCall(a: Thing) {
            try {
                b = Thing()
                mayThrow()
            } catch e {}
        }
        fn viaCast(a: Thing, x: Any) {
            try {
                b = Thing()
                s = x as String
            } catch e {}
        }
        fn viaThrowOfError(a: Thing) {
            try {
                b = Thing()
                throw Fatal()
            } catch e {}
        }
        fn viaThrowOfThrowable(a: Thing) {
            try {
                b = Thing()
                throw pick()
            } catch e {}
        }
        fn throwIsFirstStatement(a: Thing) {
            try {
                throw pick()
            } catch e {}
        }
        fn nested(a: Thing) {
            try {
                b = Thing()
                try {
                    c = Thing()
                    throw pick()
                } catch inner {}
            } catch outer {}
        }
        fn noTry(a: Thing) {
            b = Thing()
            throw pick()
        }
    """.trimIndent()).moduleBackendIrAssumingNoErrors()

    fun exitsOf(functionName: String): List<ExceptionalExit> {
        val fn = module.packages.single().functions
            .single { it.canonicalName.simpleName == functionName }
            .overloads.single()
        val exits = ArrayList<ExceptionalExit>()
        collectExceptionalExits(fn.body!!, HashSet(), tryDepth = 0, exits)
        return exits
    }

    // a is a parameter: it is released on every way out of the function, and never on the way to a catch
    for (functionName in listOf("viaCall", "viaCast", "viaThrowOfError", "viaThrowOfThrowable", "throwIsFirstStatement", "nested", "noTry")) {
        "$functionName: the parameter is released iff the throwable leaves the function" {
            val exits = exitsOf(functionName)
            exits.filter { it.leavesFunction }.shouldNotBeEmpty()
            for (exit in exits) {
                if (exit.leavesFunction) {
                    exit.droppedVariables shouldContain "a"
                } else {
                    exit.droppedVariables shouldNotContain "a"
                }
            }
        }
    }

    for (functionName in listOf("viaCall", "viaCast", "viaThrowOfError", "viaThrowOfThrowable")) {
        "$functionName: an Error passes by the catch, after the variables of the try block and the parameter are released" {
            exitsOf(functionName)
                .filter { it.passesByCatch }
                .map { it.droppedVariables }
                .filter { "b" in it }
                .shouldNotBeEmpty()
        }
    }

    "a failing cast and the throw of an Error never go to the catch" {
        // calls in the try block can, with whatever they throw that is no Error
        for (functionName in listOf("viaCast", "viaThrowOfError")) {
            exitsOf(functionName).filter { !it.leavesFunction && it.viaThrowStatement }.shouldBeEmpty()
        }
    }

    "a throw of a Throwable goes to the catch after the variables of the try block are released" {
        val toCatch = exitsOf("viaThrowOfThrowable").filter { !it.leavesFunction && it.viaThrowStatement }
        toCatch.shouldNotBeEmpty()
        toCatch.forEach { it.droppedVariables shouldContain "b" }
    }

    "a throw as the first statement of a try block" {
        val exits = exitsOf("throwIsFirstStatement")
        exits.filter { !it.leavesFunction && it.viaThrowStatement }.shouldNotBeEmpty()
        exits.filter { it.passesByCatch }.shouldNotBeEmpty()
    }

    "nested try blocks: an Error passes by both, all scopes are cleaned up" {
        val exits = exitsOf("nested")
        val pastCatch = exits.filter { it.passesByCatch && it.viaThrowStatement }
        pastCatch.shouldNotBeEmpty()
        pastCatch.forEach { it.droppedVariables shouldContainAll listOf("a", "b", "c") }

        val toInnerCatch = exits.filter { !it.leavesFunction && it.viaThrowStatement }
        toInnerCatch.shouldNotBeEmpty()
        toInnerCatch.forEach {
            it.droppedVariables shouldContain "c"
            it.droppedVariables shouldNotContain "b"
        }
    }

    "without a try, a throw releases everything" {
        val viaThrow = exitsOf("noTry").filter { it.viaThrowStatement }
        viaThrow.shouldNotBeEmpty()
        viaThrow.forEach { it.droppedVariables shouldContainAll listOf("a", "b") }
        exitsOf("noTry").filter { !it.leavesFunction }.shouldBeEmpty()
    }
})

private class ExceptionalExit(
    /** the variables whose references were dropped on the way here, as far as that is certain */
    val droppedVariables: Set<String>,
    /** whether this is in the fallible code of a try */
    val inTry: Boolean,
    val viaThrowStatement: Boolean,
    val ignoresLocalCatchBlock: Boolean,
) {
    val leavesFunction: Boolean get() = !inTry || ignoresLocalCatchBlock
    val passesByCatch: Boolean get() = inTry && ignoresLocalCatchBlock
}

/**
 * Walks all the IR below [node], finds all [IrThrowStatement]s and [IrCatchExceptionStatement]s. Keeps track of the
 * variables whose references are dropped: in a chunk, what one component drops is dropped for those after it. Other
 * nodes are taken as branches, what is dropped in them is not counted outside. So [ExceptionalExit.droppedVariables]
 * can lack variables, but has none that is not dropped.
 */
private fun collectExceptionalExits(node: Any, dropped: MutableSet<String>, tryDepth: Int, exits: MutableList<ExceptionalExit>) {
    when (node) {
        is IrCodeChunk -> {
            node.components.forEach { collectExceptionalExits(it, dropped, tryDepth, exits) }
            return
        }
        is IrDropStrongReferenceStatement -> {
            (node.reference.declaration.value as? IrVariableAccessExpression)?.let { dropped.add(it.variable.name) }
            return
        }
        is IrThrowStatement -> {
            exits.add(ExceptionalExit(dropped.toSet(), tryDepth > 0, viaThrowStatement = true, node.ignoreLocalCatchBlock))
            return
        }
        is IrCatchExceptionStatement -> {
            exits.add(ExceptionalExit(dropped.toSet(), tryDepth > 0, viaThrowStatement = false, ignoresLocalCatchBlock = false))
            return
        }
        is IrTryCatchExpression -> {
            collectExceptionalExits(node.fallibleCode, HashSet(dropped), tryDepth + 1, exits)
            collectExceptionalExits(node.catchpad, HashSet(dropped), tryDepth, exits)
            return
        }
        is IrInvocationExpression.Landingpad -> {
            collectExceptionalExits(node.code, HashSet(dropped), tryDepth, exits)
            return
        }
    }

    // any other node: go into everything that holds code
    node.javaClass.methods
        .asSequence()
        .filter { it.parameterCount == 0 && !Modifier.isStatic(it.modifiers) && it.name.startsWith("get") }
        .filter { it.declaringClass.name.startsWith("io.github.tmarsteel.emerge.backend.api.ir.") || it.declaringClass == node.javaClass }
        .sortedBy { it.name }
        .forEach { getter ->
            getter.isAccessible = true
            val children = when (val value = getter.invoke(node)) {
                is IrExecutable, is IrExpression, is IrInvocationExpression.Landingpad -> listOf(value)
                is Iterable<*> -> value.filter { it is IrExecutable || it is IrExpression }
                else -> emptyList()
            }
            children.forEach { collectExceptionalExits(it!!, HashSet(dropped), tryDepth, exits) }
        }
}
