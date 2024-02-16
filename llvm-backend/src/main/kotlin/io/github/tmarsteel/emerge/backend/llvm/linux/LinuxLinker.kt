package io.github.tmarsteel.emerge.backend.llvm.linux

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.ToolDiscoverer
import io.github.tmarsteel.emerge.backend.llvm.runSyncCapturing
import java.nio.file.Path

object LinuxLinker {
    private val executable by lazy {
        ToolDiscoverer.INSTANCE.discover("ld.lld-17", "ld")
    }

    fun linkObjectFilesToELF(
        objectFiles: List<Path>,
        outputFile: Path,
        dynamicallyLinkAtRuntime: List<String> = emptyList(),
        runtimeDynamicLinker: UnixPath = UnixPath("/lib64/ld-linux-x86-64.so.2"),
        runtimeLibraryPaths: List<UnixPath> = listOf(UnixPath("/usr/lib/x86_64-linux-gnu/")),
    ) {
        val command = mutableListOf(
            executable.toString(),
            "-o", outputFile.toString(),
            "--dynamic-linker=${runtimeDynamicLinker.path}",
        )

        runtimeLibraryPaths.forEach {
            command += "--library-path"
            command += it.path
        }
        dynamicallyLinkAtRuntime.forEach {
            command += "--library"
            command += it
        }

        objectFiles.forEach {
            command += it.toString()
        }

        val result = runSyncCapturing(command)
        if (result.exitCode == 0) {
            return
        }

        throw LinuxLinkerException(
            "linker failed; command: $command\nerror:\n" + result.standardErrorAsString(),
            result.exitCode,
        )
    }
}

class LinuxLinkerException(message: String, val exitCode: Int) : CodeGenerationException(message)

/**
 * Some type-safety for unix paths, because [java.nio.file.Path] can't be used reliably; unix-specific
 * implementations are private to the JVM.
 */
data class UnixPath(val path: String)