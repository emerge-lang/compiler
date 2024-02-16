package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.ToolDiscoverer
import io.github.tmarsteel.emerge.backend.llvm.runSyncCapturing
import org.bytedeco.llvm.global.LLVM
import java.nio.file.Path

/**
 * A convenient way around invoking `llc`. Necessary because llc gives access
 * to configuration options not available through the C interface, e.g. use-init-array.
 */
object LlvmCompiler {
    private val executable by lazy {
        ToolDiscoverer.INSTANCE.discover("llc-17")
    }

    fun compileBitcodeFile(
        input: Path,
        output: Path,
        codeModel: CodeModel = CodeModel.SMALL,
        relocationModel: RelocationModel = RelocationModel.POSITION_INDEPENDENT,
        outputType: OutputType = OutputType.OBJECT_FILE,
        optimizationLevel: OptimizationLevel = OptimizationLevel.DEFAULT,
    ) {
        val command = mutableListOf(
            executable.toString(),
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
}

class LlvmCompilerException(message: String, val exitCode: Int) : CodeGenerationException(message)

enum class CodeModel(val numeric: Int, val llcName: String?) {
    DEFAULT(LLVM.LLVMCodeModelDefault, null),
    TINY(LLVM.LLVMCodeModelTiny, "tiny"),
    SMALL(LLVM.LLVMCodeModelSmall, "small"),
    KERNEL(LLVM.LLVMCodeModelKernel, "kernel"),
    MEDIUM(LLVM.LLVMCodeModelMedium, "medium"),
    LARGE(LLVM.LLVMCodeModelLarge, "large"),

    // JIT_DEFAULT omitted because its not available in llc-17
}

enum class OutputType(val llcName: String) {
    ASSEMBLY("asm"),
    OBJECT_FILE("obj")
}

enum class RelocationModel(val numeric: Int, val llcName: String) {
    /** Non-relocatable code */
    STATIC(LLVM.LLVMRelocStatic, "static"),
    /** Fully relocatable, position independent code */
    POSITION_INDEPENDENT(LLVM.LLVMRelocPIC, "pic"),
    /** Relocatable external references, non-relocatable code **/
    RELOCATABLE_EXTERNAL_REFERENCES(LLVM.LLVMRelocDynamicNoPic, "dynamic-no-pic"),
    /** Code and read-only data relocatable, accessed PC-relative */
    ROPI(LLVM.LLVMRelocROPI, "ropi"),
    /** Read-write data relocatable, accessed relative to static base */
    RWPI(LLVM.LLVMRelocRWPI, "rwpi"),
    /** Combination of ropi and rwpi */
    ROPI_RWPI(LLVM.LLVMRelocROPI_RWPI,"ropi-rwpi"),
}

enum class OptimizationLevel(val numeric: Int) {
    NONE(LLVM.LLVMCodeGenLevelNone),
    LESS(LLVM.LLVMCodeGenLevelLess),
    DEFAULT(LLVM.LLVMCodeGenLevelDefault),
    AGGRESSIVE(LLVM.LLVMCodeGenLevelAggressive),
}