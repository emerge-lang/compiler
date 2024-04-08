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
 * rely on [IrCreateReferenceStatement] and [IrDropReferenceStatement] nodes to generate correctly reference-counted
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
 * * the frontend may omit [IrCreateReferenceStatement] and [IrDropReferenceStatement] IR nodes when it can prove
 *   that the mutation of the reference counter cannot be observed by the input program.
 */
interface IrCreateReferenceStatement : IrExecutable {
    /** the temporary holding the reference to the object whichs reference count needs to increase */
    val reference: IrCreateTemporaryValue
}

/**
 * A reference has reached the end of its lifetime. The reference counter of the referred object must be
 * decremented and if it reaches 0, the object must be finalized.
 *
 * **Attention!!:** there are caveats, see [IrCreateReferenceStatement]
 */
interface IrDropReferenceStatement : IrExecutable {
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
}

interface IrAssignmentStatement : IrExecutable {
    val target: Target
    val value: IrTemporaryValueReference

    sealed interface Target {
        interface Variable : Target {
            val declaration: IrVariableDeclaration
        }
        interface ClassMemberVariable : Target {
            val objectValue: IrTemporaryValueReference
            val memberVariable: IrClass.MemberVariable
        }
    }
}

interface IrReturnStatement : IrExecutable {
    val value: IrTemporaryValueReference
}

/**
 * The counterpart to [IrDeallocateObjectStatement]. It makes the memory occupied by the given reference.
 *
 * The frontend must emit code prior to this statement that ensures that
 * * any references stored/nested in the object are dropped (see [IrDropReferenceStatement])
 * * no other references ot the object, including weak ones, exist. This is usually the job of the backend as
 *   part of [IrDropReferenceStatement]; Hence, the only safe place for the frontend to put this code is in the
 *   finalizer of a class (see [IrClass.destructor]). Backends *may* emit code that throws an exception if this
 *   statement is called on an object that still has live references.
 *
 * The backend must emit code that achieves these things for this statement:
 * * make the memory available for use by other [IrAllocateObjectExpression]s again.
 */
interface IrDeallocateObjectStatement : IrExecutable {
    val value: IrTemporaryValueReference
}