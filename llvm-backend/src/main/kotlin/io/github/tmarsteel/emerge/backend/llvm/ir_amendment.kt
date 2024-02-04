package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import org.bytedeco.llvm.LLVM.LLVMTypeRef

/*
Amendmends to the backend-api IR using tack.kt
Once the LLVM backend is somewhat stable all of this should move into a new set of AST classes
 */

internal var IrStruct.rawLlvmRef: LLVMTypeRef? by tackState { null }
internal var IrStruct.llvmType: EmergeStructType? by tackState { null }
internal var IrStruct.Member.indexInLlvmStruct: Int? by tackState { null }

internal var IrFunction.llvmRef: LlvmFunction<LlvmType>? by tackState { null }
internal var IrFunction.bodyDefined: Boolean by tackState { false }
