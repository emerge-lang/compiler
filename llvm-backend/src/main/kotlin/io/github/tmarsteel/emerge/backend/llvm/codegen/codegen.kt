package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
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
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.ValueArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmValueType
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
            val stackAllocation = alloca(type)
            code.emitRead = {
                stackAllocation.dereference()
            }
            code.emitWrite = { newValue ->
                store(newValue, stackAllocation)
            }
            return null
        }
        is IrVariableAssignment -> {
            val toAssign = emitExpressionCode(code.value)
            code.declaration.emitWrite!!(this, toAssign)
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

internal fun BasicBlockBuilder<EmergeLlvmContext, out LlvmType>.emitExpressionCode(
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

            if (!expression.member.isCPointerPointed || expression.evaluatesTo.llvmValueType == null) {
                return memberPtr
            }
            return  memberPtr.dereference()
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            return call(expression.function.llvmRef!!, expression.arguments.map { emitExpressionCode(it) })
        }
        is IrVariableReferenceExpression -> {
            return expression.variable.emitRead!!()
        }
        is IrIntegerLiteralExpression -> {
            // TODO: these conversions are not correct; just to get it working for now
            val value = when ((expression.evaluatesTo as IrSimpleType).baseType.fqn.toString()) {
                "emerge.core.Byte" -> i8(expression.value.byteValueExact())
                "emerge.core.UByte" -> TODO()
                "emerge.core.Short" -> i16(expression.value.shortValueExact())
                "emerge.core.UShort" -> TODO()
                "emerge.core.Int" -> i32(expression.value.intValueExact())
                "emerge.core.UInt" -> TODO()
                "emerge.core.Long" -> i64(expression.value.longValueExact())
                "emerge.core.ULong" -> TODO()
                "emerge.core.iword" -> word(expression.value.intValueExact())
                "emerge.core.uword" -> TODO()
                else -> throw CodeGenerationException("Unsupport integer literal type ${expression.evaluatesTo}")
            }

            return value
        }
        else -> TODO("code generation for ${expression::class.simpleName}")
    }
}

internal var IrVariableDeclaration.typeForAllocationSite: LlvmType? by tackState { null }
/**
 * for locals: loads from the alloca'd location
 * for globals: loads from the result of LLVM.LLVMAddGlobal
 * for parameters: result of LLVM.LLVMGetParam
 */
internal var IrVariableDeclaration.emitRead: (BasicBlockBuilder<EmergeLlvmContext, *>.() -> LlvmValue<LlvmType>)? by tackState { null }

/**
 * for locals: stores to the alloca'd location
 * for globals: stores to the result of LLVM.LLVMAddGlobal
 * for parameters: throws an exception
 */
internal var IrVariableDeclaration.emitWrite: (BasicBlockBuilder<EmergeLlvmContext, *>.(v: LlvmValue<LlvmType>) -> Unit)? by tackState { null }

internal var IrStaticByteArrayExpression.globalThreadLocal: LlvmValue<ValueArrayType<LlvmI8Type>>? by tackState { null }