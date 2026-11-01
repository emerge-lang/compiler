package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrSourceFile
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import java.nio.file.Paths

class JvmStackFrameIrSourceLocation(frame: StackTraceElement) : IrSourceLocation {
    override val file = object : IrSourceFile {
        override val path = Paths.get(frame.fileName)
    }
    override val lineNumber = frame.lineNumber.toUInt()
    override val columnNumber = 1u
}