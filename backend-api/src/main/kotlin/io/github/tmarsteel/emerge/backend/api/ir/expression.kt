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

/**
 * The result of this expression is a fully functional object/reference as per the backend implementation. However,
 * the state of the member variables is undefined. It is the frontends responsibility to pair this expression with
 * more code that initializes the object to a known-good state, as specified by the input program.
 *
 * In more detail this means: this expression allocates memory for an object of the given type and initializes
 * the backend-specific elements of it:
 * * reference counter initialized to `1`
 * * runtime type-information as applicable, including e.g.:
 *    * dynamic dispatch structures, e.g. a vtable
 *    * reference to reflection data
 */
interface IrAllocateObjectExpression : IrExpression {
    val clazz: IrClass
}

interface IrStringLiteralExpression : IrExpression {
    val utf8Bytes: ByteArray
}

/**
 * Creates a new array for elements of type [elementType] and initializes it to 0/null.
 *  It is the responsibility of the frontend to pair this instruction with others that will
 *  initialize the array as required by the input program. The 0/null initialization is so
 *  that the finalizer of the array, invoked in case of an exception, can still clean up
 *  the partially initialized array.
 *
 *  The reference count of the newly allocated array has to be `1`.
 */
interface IrNullInitializedArrayExpression : IrExpression {
    /**
     * The type of the elements. The same information is also in [evaluatesTo], but
     * [elementType] doesn't contain variance information.
     */
    val elementType: IrType
    val size: ULong
}

interface IrBooleanLiteralExpression : IrExpression {
    val value: Boolean
}

interface IrNullLiteralExpression : IrExpression

/**
 * Calls the given function with the given arguments. Control flow resumes to the next [IrExecutable]
 * after this [IrInvocationExpression] on a regular return.
 * If the called function throws an exception, control flow passes to the [landingpad], if present, or
 * up the stack instead. The [landingpad] is supposed to carry out cleanup work that is needed regardless
 * of whether the exception is caught or not. Afterward it has two options:
 * * continue the stack unwinding by executing another [IrThrowStatement]
 * * transfer control to the [IrTryCatchExpression.catchpad] of the lexically closest
 *   parent [IrTryCatchExpression] by executing an [].
 */
sealed interface IrInvocationExpression : IrExpression {
    val function: IrFunction
    val arguments: List<IrTemporaryValueReference>

    /**
     * For each type argument of the function contains the compile-time resolved type at the call-site. E.g.
     * if you have:
     *
     *     fn bla<T : mut Any, E : read Any>(a: T, b: T) -> Int
     *
     * and this invocation
     *
     *     bla([1, 2], "foo")
     *
     * then this map will be
     *
     * | key | value                            |
     * |-----|----------------------------------|
     * | T   | `exclusive Array<const Int>`     |
     * | E   | `const String`                   |
     *
     * Contains type parameters declared on the function itself, **and** ones inherited from
     * parent lexical scopes.
     */
    val typeArgumentsAtCallSite: Map<String, IrType>

    /**
     * Cleanup code for exceptions, plus possibly triggering a catch mechanism
     */
    val landingpad: Landingpad?

    class Landingpad(
        /**
         * The variable that [code] uses to refer to the throwable that is being handled, either for catching
         * or for rethrowing.
         */
        val throwableVariable: IrVariableDeclaration,
        val code: IrExecutable,
    )
}

/**
 * Introduces a new nesting of try-catch context, in which [fallibleCode] is executed.
 * The sole purpose of this is so that [IrInvocationExpression.landingpad]s and [catchpad]s can transfer
 * control to after the _entire_ try+catch source language construct.
 *
 * Note that there is no `finally` concept here. Frontends must implement this by incorporating the cleanupcode
 * from a source-level finally block into the (potentially many) branches of [catchpad].
 */
interface IrTryCatchExpression : IrExpression {
    /**
     * Code that the source program expects to fail
     */
    val fallibleCode: IrExpression

    /**
     * The variable that [catchpad] uses to refer to the throwable being caught
     */
    val throwableVariable: IrVariableDeclaration

    val catchpad: IrExpression
}

interface IrStaticDispatchFunctionInvocationExpression : IrInvocationExpression

interface IrDynamicDispatchFunctionInvocationExpression : IrInvocationExpression {
    val dispatchOn: IrTemporaryValueReference
    override val function: IrMemberFunction
}

interface IrClassMemberVariableAccessExpression : IrExpression {
    val base: IrTemporaryValueReference
    val memberVariable: IrClass.MemberVariable
}

interface IrVariableAccessExpression : IrExpression {
    val variable: IrVariableDeclaration

    override val evaluatesTo: IrType
        get() = variable.type
}

interface IrIntegerLiteralExpression : IrExpression {
    val value: BigInteger
}

/**
 * Compares two numeric values according to [predicate]. The frontend must guarantee
 * that both [lhs] and [rhs] have an identical, not-nullable type and that this type
 * is one of the core numeric types.
 * This expression must evaluate to a boolean, and hence [evaluatesTo] must always
 * point to `emerge.core.Bool`.
 */
interface IrNumericComparisonExpression : IrExpression {
    val lhs: IrTemporaryValueReference
    val rhs: IrTemporaryValueReference
    val predicate: Predicate

    enum class Predicate {
        EQUAL,
        GREATER_THAN,
        GREATER_THAN_OR_EQUAL,
        LESS_THAN,
        LESS_THAN_OR_EQUAL,
        ;
    }
}

/**
 * Always evaluates to a boolean, [evaluatesTo] must always be `IrSimpleType(emerge.core.Bool)`.
 *
 * Evaluates to true iff the value in [nullableValue] is `null`
 */
interface IrIsNullExpression : IrExpression {
    val nullableValue: IrTemporaryValueReference
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
 * Evaluates to the runtime type information object about [baseType].
 */
interface IrBaseTypeReflectionExpression : IrExpression {
    val baseType: IrBaseType
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