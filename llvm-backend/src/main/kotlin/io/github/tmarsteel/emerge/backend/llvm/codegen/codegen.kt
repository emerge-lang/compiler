package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticByteArrayExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStructMemberAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAssignment
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableReferenceExpression
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.ValueArrayType
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.tackState

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitCode(
    code: IrCodeChunk,
): BasicBlockBuilder.Termination? {
    return code.components.fold<_, BasicBlockBuilder.Termination?>(null) { terminationCarry, component ->
        emitCode(component) ?: terminationCarry
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitCode(
    code: IrExecutable,
): BasicBlockBuilder.Termination? {
    when (code) {
        is IrCodeChunk -> return emitCode(code)
        is IrVariableDeclaration -> {
            val type = context.getAllocationSiteType(code.type)
            code.typeForAllocationSite = type
            code.allocation = alloca(type)
            return null
        }
        is IrVariableAssignment -> {
            val toAssign = emitExpressionCode(code.value)
            store(toAssign, code.declaration.allocation!!)
            return null
        }
        is IrReturnStatement -> {
            // TODO: unit return to unit declaration
            val toReturn = emitExpressionCode(code.value)
            return ret(toReturn)
        }
        is IrExpression -> {
            emitExpressionCode(code)
            return null
        }
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
): LlvmValue<LlvmType> {
    println("Emitting $expression")
    when (expression) {
        is IrStaticByteArrayExpression -> {
            expression.globalThreadLocal?.let { return it }
            val global = ValueArrayType.i8s.insertThreadLocalGlobalInto(
                context,
                expression.content.asList(),
                context::i8,
            )
            expression.globalThreadLocal = global
            return global
        }
        is IrStructMemberAccessExpression -> {
            // TODO: throw + catch
            val baseStructPtr = emitExpressionCode(expression.base) as LlvmValue<LlvmPointerType<EmergeStructType>>
            val memberPtr = getelementptr(baseStructPtr)
                .member(expression.member)
                .get()

            return memberPtr
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            return call(expression.function.llvmRef!!, expression.arguments.map { emitExpressionCode(it) })
        }
        is IrVariableReferenceExpression -> {
            return expression.variable.allocation!!.dereference()
        }
        else -> TODO("code generation for ${expression::class.simpleName}")
    }
}

internal var IrVariableDeclaration.typeForAllocationSite: LlvmType? by tackState { null }
/** For locals on the stack, globals on the globals space */
internal var IrVariableDeclaration.allocation: LlvmValue<LlvmPointerType<LlvmType>>? by tackState { null }

internal var IrStaticByteArrayExpression.globalThreadLocal: LlvmValue<ValueArrayType<LlvmI8Type>>? by tackState { null }