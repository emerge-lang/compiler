package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrExecutable

interface IrCodeChunk : IrExecutable {
    val components: List<IrExecutable>
}

/**
 * Temporary values behave just like `val` variables in emerge source. Additionally, any compound expression, e.g.
 * `a + 3` can only reference temporaries for the nested parts. This makes expressions in this IR [SSA](https://en.wikipedia.org/wiki/Static_single-assignment_form).
 *
 * The purpose of this is to allow the frontend to do the heavy lifting of figuring out when and which references
 * need to be counted, including all the optimizations on that. This allows backend code to be much simpler and simply
 * rely on [IrCreateStrongReferenceStatement] and [IrDropStrongReferenceStatement] nodes to generate correctly reference-counted
 * code.
 */
interface IrCreateTemporaryValue : IrExecutable {
    val value: IrExpression
    val type: IrType get() = value.evaluatesTo
}

/**
 * The reference-count on an object needs to be incremented.
 *
 * **Caveats:**
 * * the frontend will emit these for values of **all** types.
 * * the frontend may omit [IrCreateStrongReferenceStatement] and [IrDropStrongReferenceStatement] IR nodes when it can prove
 *   that the mutation of the reference counter cannot be observed by the input program.
 */
interface IrCreateStrongReferenceStatement : IrExecutable {
    /** the temporary holding the reference to the object whose reference count needs to be increased */
    val reference: IrCreateTemporaryValue
}

/**
 * A reference has reached the end of its lifetime. The reference counter of the referred object must be
 * decremented and if it reaches 0, the object must be finalized.
 *
 * **Attention!!:** there are caveats, see [IrCreateStrongReferenceStatement]
 */
interface IrDropStrongReferenceStatement : IrExecutable {
    val reference: IrTemporaryValueReference
}

/**
 * The declaration of a re-assignable or not-re-assignable variable. The frontend may choose to convert any
 * not-re-assignable variable into a [IrCreateTemporaryValue] and corresponding [IrTemporaryValueReference.Temporary]s,
 * as the semantics are identical.
 */
interface IrVariableDeclaration : IrExecutable {
    val name: String
    val type: IrType
    val isBorrowed: Boolean

    /**
     * if false, the backend can assume that at runtime, at most one [IrAssignmentStatement] to this variable
     * will ever be executed
     */
    val isReAssignable: Boolean

    /**
     * If true, the backend may assume that
     * * a single write to this variable will be placed in the IR and executed at runtime before the first access to the variable
     * * only ever one [IrAssignmentStatement] to this variable will ever be executed at runtime
     *
     * [isSSA] implies [isReAssignable] `== false`.
     */
    val isSSA: Boolean

    val declaredAt: IrSourceLocation

    /**
     * The [Scope] in which this variable is valid.
     */
    val scope: Scope

    interface Scope {
        interface Lexical : Scope {
            val beginMarker: BeginMarker
            val endMarker: EndMarker

            /**
             * No-op executable that just marks the start of a [Scope].
             */
            interface BeginMarker : IrExecutable {
                val scope: Scope
            }

            /**
             * No-op executable that just marks the end of a [Scope].
             */
            interface EndMarker : IrExecutable {
                val scope: Scope
            }
        }

        interface File : Scope {
            val file: IrSourceFile
        }
    }
}

interface IrAssignmentStatement : IrExecutable {
    val target: Target
    val value: IrTemporaryValueReference

    sealed interface Target {
        val type: IrType

        interface Variable : Target {
            val declaration: IrVariableDeclaration
            override val type: IrType get() = declaration.type
        }
        interface ClassField : Target {
            val objectValue: IrTemporaryValueReference
            val field: IrClass.Field
            override val type: IrType get() = this.field.type
        }
    }
}

interface IrReturnStatement : IrExecutable {
    val value: IrTemporaryValueReference
}

/**
 * The semantics are identical to [IrIfExpression] wrapped in an [IrImplicitEvaluationExpression] where both
 * branches evaluate to `emerge.core.Unit`. This optimizes(=reduces) complexity of code generation and reference counting.
 */
interface IrConditionalBranch : IrExecutable {
    val condition: IrTemporaryValueReference
    val thenBranch: IrExecutable
    val elseBranch: IrExecutable?
}

/**
 * [body] is executed infinitely. Different kinds of loops (for, while, do-while, ...) can be implemented
 * using [IrConditionalBranch], [IrBreakStatement] and [IrContinueStatement] in [body].
 */
interface IrLoop : IrExecutable {
    val body: IrExecutable
}

/**
 * Stop executing the loop body and jump to the code after the loop
 */
interface IrBreakStatement : IrExecutable {
    /**
     * the loop to break out from; is guaranteed to be a parent of this statement. Or in
     * other words, `this` statement is guaranteed to be located in the [IrLoop.body] of the loop it is breaking out from
     */
    val fromLoop: IrLoop
}

/**
 * Stop executing the loop body and jump back to the beginning of the body.
 */
interface IrContinueStatement : IrExecutable {
    /**
     * the loop to continue; is guaranteed to be a parent of this statement. Or in
     * other words, `this` statement is guaranteed to be located in the [IrLoop.body] of the loop it is breaking out from
     */
    val loop: IrLoop
}

/**
 * Throw the given temporary.
 */
interface IrThrowStatement : IrExecutable {
    /**
     * the object to throw; must reference a non-null object of type `emerge.core.Throwable`
     */
    val throwable: IrTemporaryValueReference

    /**
     * Relevant in these two scenarios:
     *
     *     1.
     *     IrTryCatchExpression(
     *       fallibleCode = IrThrowStatement(...) // or somewhere nested
     *     )
     *
     * and
     *
     *     2.
     *     IrTryCatchExpression(
     *       catchpad = IrThrowStatement(...) // or somehwere nested
     *     )
     *
     * In the first case, the [IrThrowStatement] will be a direct jump to the catchpad if [ignoreLocalCatchBlock] is false.
     * In the second case, the [IrThrowStatement] will be a direct jump to an enclosing catchpad, if any, if [ignoreLocalCatchBlock] is false.
     * However, if [ignoreLocalCatchBlock] is true, the [IrThrowStatement] will immediately exit from the current function
     * with the [throwable] as the exceptional result.
     *
     * In the emerge frontend, this is used to implement immediate propagation of uncatchable throwables (subclasses
     * of emerge.core.Error).
     */
    val ignoreLocalCatchBlock: Boolean
}

/**
 * May only be used inside [IrInvocationExpression.landingpad] to transfer control to the [IrTryCatchExpression.catchpad]
 * of the lexically closest [IrTryCatchExpression].
 */
interface IrCatchExceptionStatement : IrExecutable {
    /**
     * The exception to be caught. The type of this value must be a subtype of `emerge.core.Throwable`
     */
    val exceptionReference: IrTemporaryValueReference
}

/**
 * The counterpart to [IrDeallocateObjectStatement]. It makes the memory occupied by the given reference.
 *
 * The frontend must emit code prior to this statement that ensures that
 * * any references stored/nested in the object are dropped (see [IrDropStrongReferenceStatement])
 * * no other references ot the object, including weak ones, exist. This is usually the job of the backend as
 *   part of [IrDropStrongReferenceStatement]; Hence, the only safe place for the frontend to put this code is in the
 *   finalizer of a class (see [IrClass.destructor]). Backends *may* emit code that throws an exception if this
 *   statement is called on an object that still has live references.
 *
 * The backend must emit code that achieves these things for this statement:
 * * make the memory available for use by other [IrAllocateObjectExpression]s again.
 */
interface IrDeallocateObjectStatement : IrExecutable {
    val value: IrTemporaryValueReference
}

/**
 * The frontend must emit these alongside the construction of `emerge.core.Weak` instances. A weak
 * reference needs to be registered with the referred object.
 */
interface IrRegisterWeakReferenceStatement : IrExecutable {
    val referenceStoredIn: IrAssignmentStatement.Target.ClassField
    val referredObject: IrTemporaryValueReference
}

/**
 * The frontend must emit these alongside the destruction of `emerge.core.Weak` instances. A weak
 * reference needs to be de-registered with the referred object.
 */
interface IrUnregisterWeakReferenceStatement : IrExecutable {
    val referenceStoredIn: IrAssignmentStatement.Target.ClassField
    val referredObject: IrTemporaryValueReference
}

/**
 * Evaluate an expression solely for its side effects, the result value is unused. Reference counting is not
 * part of the semantics of [IrExpressionSideEffectsStatement]. E.g. unused return values from invocations must not
 * be implemented using this statement because those require reference counting.
 */
interface IrExpressionSideEffectsStatement : IrExecutable {
    val expression: IrExpression
}

/**
 * Used by the frontend when either the frontend or the input program is sure that this instruction is never reached.
 * Backends can do whatever they like with this info; most likely optimize or insert code that aids in debugging
 * when this statement is actually reached.
 */
interface IrUnreachableStatement : IrExecutable {
    /**
     * `true` iff the frontend can mathematically prove that this instruction is unreachable. This allows the backend
     * to elide debugging code or turn up optimization aggressiveness.
     */
    val isProvablyUnreachable: Boolean
}