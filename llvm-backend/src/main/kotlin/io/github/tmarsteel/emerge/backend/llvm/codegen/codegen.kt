package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrArrayLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStructMemberAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAssignment
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableReferenceExpression
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
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
            val type = context.getReferenceSiteType(code.type)
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
    when (expression) {
        is IrStringLiteralExpression -> {
            val llvmStructWrapper = context.getAllocationSiteType(expression.evaluatesTo) as EmergeStructType
            val byteArrayPtr = expression.assureByteArrayConstantIn(context)
            val ctor = llvmStructWrapper.defaultConstructor.getInContext(context)
            return call(ctor, listOf(byteArrayPtr))
        }
        is IrStructMemberAccessExpression -> {
            val baseStructPtr = emitExpressionCode(expression.base) as LlvmValue<LlvmPointerType<EmergeStructType>>
            return getelementptr(baseStructPtr)
                .member(expression.member)
                .get()
                .dereference()
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            return call(expression.function.llvmRef!!, expression.arguments.map { emitExpressionCode(it) })
        }
        is IrVariableReferenceExpression -> {
            return expression.variable.emitRead!!()
        }
        is IrIntegerLiteralExpression -> {
            val value = when ((expression.evaluatesTo as IrSimpleType).baseType.fqn.toString()) {
                "emerge.core.Byte" -> context.i8(expression.value.byteValueExact())
                "emerge.core.UByte" -> context.i8(expression.value.shortValueExact().toUByte())
                "emerge.core.Short" -> context.i16(expression.value.shortValueExact())
                "emerge.core.UShort" -> context.i16(expression.value.intValueExact().toUShort())
                "emerge.core.Int" -> context.i32(expression.value.intValueExact())
                "emerge.core.UInt" -> context.i32(expression.value.longValueExact().toUInt())
                "emerge.core.Long" -> context.i64(expression.value.longValueExact())
                "emerge.core.ULong" -> context.i64(expression.value.toLong())
                "emerge.core.iword" -> context.word(expression.value.longValueExact())
                "emerge.core.uword" -> context.word(expression.value.toLong())
                else -> throw CodeGenerationException("Unsupported integer literal type ${expression.evaluatesTo}")
            }

            return value
        }
        is IrBooleanLiteralExpression -> {
            return context.i1(expression.value)
        }
        is IrArrayLiteralExpression -> {
            val elementCount = context.word(expression.elements.size)
            val arrayType = context.getAllocationSiteType(expression.evaluatesTo) as EmergeArrayType<*>
            val arrayPtr = call(arrayType.constructorOfUndefEntries.getInContext(context), listOf(elementCount))
            expression.elements.forEachIndexed { index, elementExpr ->
                val elementValue = emitExpressionCode(elementExpr).reinterpretAs(arrayType.elementType)
                val slotPtr = getelementptr(arrayPtr)
                    .member { elements }
                    .index(context.word(index))
                    .get()
                store(elementValue, slotPtr)
            }

            return arrayPtr
        }
    }
}

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

internal var IrStringLiteralExpression.byteArrayGlobal: LlvmGlobal<EmergeArrayType<LlvmI8Type>>? by tackState { null }
internal fun IrStringLiteralExpression.assureByteArrayConstantIn(context: EmergeLlvmContext): LlvmGlobal<EmergeArrayType<LlvmI8Type>> {
    byteArrayGlobal?.let { return it }
    val constant = EmergeS8ArrayType.buildConstantIn(
        context,
        utf8Bytes.asList(),
        { context.i8(it) }
    )
    val untypedGlobal = context.addGlobal(constant, LlvmGlobal.ThreadLocalMode.SHARED)
    val global = LlvmGlobal(untypedGlobal.raw, EmergeS8ArrayType)
    byteArrayGlobal = global
    return global
}