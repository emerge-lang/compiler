package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import java.math.BigInteger

/**
 * The single way to nest expressions or pass values between expressions and statements. This is done so that the
 * frontend can take care of the reference counting logic (when and what to count, how is the backends task). Temporaries
 * are required so the frontend can express the needed reference counting with the required level of detail. Consider
 * this code:
 *
 *     struct Holder {
 *         held: Held
 *     }
 *     struct Held {
 *         value: Int
 *     }
 *     val globalVar: Holder = Holder(Held(3))
 *     fun main() {
 *         doSomething(globalVar.held, foo())
 *     }
 *     fun foo() -> Int {
 *         val num = globalVar.held.value
 *         globalVar.held = Held(5)
 *         return num
 *     }
 *     fun doSomething(held: Held, num: Int) {
 *         val useAfterFree = held.value
 *     }
 *
 * Here, `globalVar.held` must be evaluated before `foo()` as per language semantics. Anything else would be confusing
 * as fuck. But the stack frame in `main` is then holding a temporary reference to it. When `foo` reassigns `globalVar`,
 * the reference count of the initial `Held(3)` must be decremented, and if 0, it must be finalized. If the frontend
 * wouldn't emit reference counting instructions for the temporary value, it would be finalized after the call to
 * `foo()` returns, and we'd have a use-after-free error in `doSomething()` - BAD!
 * So, in this scenario, reference counting must be done. Centralizing the IR around [IrTemporaryValueReference] allows
 * the frontend to make the decision when temporaries must be refcounted.
 * Also, consider this optimization: if `foo` was declared `readonly`, there is no way that the reference to the `Held`
 * become invalid in between the access and the call to `doSomething`, so the reference counting on the temporary could
 * be elided.
 *
 * -> Benefit: that logic can be kept out of the backend(s).
 */
interface IrTemporaryValueReference {
    val declaration: IrCreateTemporaryValue

    /**
     * The type this value is known to have at compile-time. May differ from [IrCreateTemporaryValue.type]
     * when the frontend can infer additional information on the value, e.g `if (myVal != null) { ... }`
     */
    val type: IrType get() = declaration.type
}

sealed interface IrExpression {
    val evaluatesTo: IrType
}

interface IrStringLiteralExpression : IrExpression {
    val utf8Bytes: ByteArray
}

interface IrArrayLiteralExpression : IrExpression {
    /**
     * The type of the elements. The same information is also in [evaluatesTo], but
     * [elementType] doesn't contain variance information.
     */
    val elementType: IrType

    val elements: List<IrTemporaryValueReference>
}

interface IrBooleanLiteralExpression : IrExpression {
    val value: Boolean
}

interface IrNullLiteralExpression : IrExpression

interface IrStaticDispatchFunctionInvocationExpression : IrExpression {
    val function: IrFunction
    val arguments: List<IrTemporaryValueReference>
}

interface IrStructMemberAccessExpression : IrExpression {
    val base: IrTemporaryValueReference
    val member: IrStruct.Member
}

interface IrVariableAccessExpression : IrExpression {
    val variable: IrVariableDeclaration

    /**
     * True iff, at this point in time, the variable has been definitely initialized
     */
    val isInitialized: Boolean

    override val evaluatesTo: IrType
        get() = variable.type
}

interface IrIntegerLiteralExpression : IrExpression {
    val value: BigInteger
}

/**
 * A code chunk needs to be executed to obtain the value of this expression. [implicitValue] should be used as the
 * value of this expression. The [IrCreateTemporaryValue] referenced by [implicitValue] is guaranteed to be an
 * element of [IrCodeChunk]:
 *
 *     assert(implicitEval.code.components.count { it === implicitEval.implicitValue.declaration } == 1)
 */
interface IrImplicitEvaluationExpression : IrExpression {
    val code: IrCodeChunk
    val implicitValue: IrTemporaryValueReference
    override val evaluatesTo get() = implicitValue.type
}

interface IrIfExpression : IrExpression {
    val condition: IrTemporaryValueReference
    val thenBranch: IrImplicitEvaluationExpression
    val elseBranch: IrImplicitEvaluationExpression?
}

/**
 * Interface for all IrTypes that have to implement [IrExpression] for semantic-analysis reasons
 * but are not actually expressions. Prime candidate: assignment statements.
 *
 * [EmergeBackend]s are expected to simply abort with a [CodeGenerationException] when encountering this
 * type in a context where they need an actual expression.
 */
interface IrNotReallyAnExpression : IrExpression {
    override val evaluatesTo: IrType get() = throw CodeGenerationException("${this::class.simpleName} is not actually an expression.")
}