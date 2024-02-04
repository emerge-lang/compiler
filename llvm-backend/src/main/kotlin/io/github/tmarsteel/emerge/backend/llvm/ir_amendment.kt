package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.LLVM.LLVMValueRef

/*
Amendmends to the backend-api IR using tack.kt
Once the LLVM backend is somewhat stable all of this should move into a new set of AST classes
 */

var IrStruct.llvmDefinition: LLVMTypeRef? by tackState { null }

var IrFunction.llvmRef: LLVMValueRef? by tackState { null }
var IrFunction.bodyDefined: Boolean by tackState { false }
