package io.github.tmarsteel.emerge.backend.api.ir

import java.nio.file.Path

/**
 * Identity is important on these to keep the debug information passed to LLVM
 * small.
 */
interface IrSourceFile {
    val path: Path
}

interface IrSourceLocation {
    val file: IrSourceFile
    val lineNumber: UInt
    val columnNumber: UInt
}

/**
 * To be placed into [IrCodeChunk]s whenever the following statements are at a
 * different location in the input program.
 */
interface IrUpdateSourceLocationStatement : IrExecutable {
    val lineNumber: UInt
    val columnNumber: UInt
}

