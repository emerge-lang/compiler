package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.ToolDiscoverer
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmCodeGenOptModel
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmCodeModel
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmRelocMode
import io.github.tmarsteel.emerge.backend.llvm.runSyncCapturing
import java.nio.file.Path

/**
 * A convenient way around invoking `llc`. Necessary because llc gives access
 * to configuration options not available through the C interface, e.g. use-init-array.
 */
class LlvmCompiler(private val llcBinary: Path) {
    fun compileBitcodeFile(
        input: Path,
        output: Path,
        codeModel: LlvmCodeModel = LlvmCodeModel.SMALL,
        relocationModel: LlvmRelocMode = LlvmRelocMode.POSITION_INDEPENDENT,
        outputType: OutputType = OutputType.OBJECT_FILE,
        optimizationLevel: LlvmCodeGenOptModel = LlvmCodeGenOptModel.DEFAULT,
    ) {
        val command = mutableListOf(
            llcBinary.toString(),
            "-o", output.toString(),
            "--relocation-model", relocationModel.llcName,
            "--filetype", outputType.llcName,
            "-O", "${optimizationLevel.numeric}"
        )

        if (codeModel.llcName != null) {
            command += "--code-model"
            command += codeModel.llcName
        }

        command += "--"
        command += input.toString()

        val result = runSyncCapturing(command)
        if (result.exitCode == 0) {
            return
        }

        throw LlvmCompilerException(
            "llc command: $command\nError:\n" + result.standardErrorAsString(),
            result.exitCode,
        )
    }

    companion object {
        fun fromLlvmInstallationDirectory(llvmInstallationDirectory: Path): LlvmCompiler {
            return LlvmCompiler(
                ToolDiscoverer.INSTANCE.discover(llvmInstallationDirectory.resolve("bin").resolve("llc").toString(), "llc-20")
            )
        }
    }
}

class LlvmCompilerException(message: String, val exitCode: Int) : CodeGenerationException(message)

enum class OutputType(val llcName: String) {
    ASSEMBLY("asm"),
    OBJECT_FILE("obj")
}