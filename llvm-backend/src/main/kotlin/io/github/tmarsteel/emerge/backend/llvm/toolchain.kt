package io.github.tmarsteel.emerge.backend.llvm

import java.io.ByteArrayOutputStream
import java.nio.ByteBuffer
import java.nio.file.FileSystems
import java.nio.file.Path
import java.nio.file.Paths

class ToolNotFoundException(names: Array<out String>) : RuntimeException(run {
    val prefix = "The command ${names[0]} was not found on this machine"
    prefix + (if (names.size == 1) "." else " (also looked for ${names.drop(1).joinToString()}).")
})

data class CommandResult(
    val exitCode: Int,
    val standardOut: ByteBuffer,
    val standardError: ByteBuffer,
) {
    fun standardErrorAsString(): String {
        return String(standardError.array(), standardError.position(), standardError.limit())
    }
}

fun runSyncCapturing(command: List<String>): CommandResult {
    val process = ProcessBuilder().command(command).start()

    val outBuffer = ByteBufferOutputStream()
    val errBuffer = ByteBufferOutputStream()
    process.inputStream.copyTo(outBuffer)
    process.errorStream.copyTo(errBuffer)

    val exitCode = process.waitFor()
    return CommandResult(
        exitCode,
        outBuffer.closeAndGetBuffer(),
        errBuffer.closeAndGetBuffer(),
    )
}

interface ToolDiscoverer {
    /**
     * Discovers a single tool on the system running this code.
     * Multiple command names can be specified, and the first to match will
     * be returned. Intended use is to fall back on more general/less optiomal
     * tools, e.g. `lld-18` to `ld`.
     * @throws ToolNotFoundException
     */
    fun discover(vararg commandNames: String): Path

    companion object {
        val INSTANCE: ToolDiscoverer by lazy {
            when (FileSystems.getDefault().separator) {
                "/" -> LinuxToolDiscoverer()
                "\\" -> WindowsToolDiscoverer()
                else -> throw IllegalStateException("Unsupported host OS")
            }
        }
    }
}

private class LinuxToolDiscoverer : ToolDiscoverer {
    override fun discover(vararg commandNames: String): Path {
        val process = ProcessBuilder()
            .command(*(arrayOf("which") + commandNames.asList()))
            .start()

        val chosen = process.inputReader().lineSequence()
            .filterNot { it.isBlank() }
            .firstOrNull()
            ?: throw ToolNotFoundException(commandNames)

        // no need to wait for which to exit

        return Paths.get(chosen)
    }
}

private class WindowsToolDiscoverer : ToolDiscoverer {
    override fun discover(vararg commandNames: String): Path {
        return sequenceOf(*commandNames)
            .mapNotNull(this::findSingle)
            .map(Paths::get)
            .firstOrNull()
            ?: throw ToolNotFoundException(commandNames)
    }

    private fun findSingle(commandName: String): String? {
        val process = ProcessBuilder()
            .command("powershell", "-Command", "gcm $commandName | % { \$_.Source }")
            .start()

        process.waitFor()

        return process.inputReader().lineSequence()
            .filterNot { it.isBlank() }
            .firstOrNull()
    }
}

private class ByteBufferOutputStream : ByteArrayOutputStream() {
    fun closeAndGetBuffer(): ByteBuffer {
        super.close()
        return ByteBuffer.wrap(super.buf, 0, super.count)
    }
}