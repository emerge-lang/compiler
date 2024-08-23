package io.github.tmarsteel.emerge.toolchain

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.CliktError
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.path
import io.github.tmarsteel.emerge.toolchain.config.ConfigParseException
import io.github.tmarsteel.emerge.toolchain.config.ToolchainConfig
import io.github.tmarsteel.emerge.toolchain.config.parseAsConfig
import java.nio.file.Path

object ToolchainMain : CliktCommand() {
    private val toolchainConfigFile: Path by option("--toolchain-config", help = "Configuration file for the toolchain; created during setup")
        .path(mustExist = true, canBeFile = true, canBeDir = false, mustBeReadable = true, canBeSymlink = true)
        .required()

    init {
        subcommands(ProjectCommand)
    }

    override fun run() {
        val toolchainConfig = try {
            toolchainConfigFile.parseAsConfig<ToolchainConfig>()
        } catch (ex: ConfigParseException) {
            ex.illustrate(currentContext.terminal)
            throw CliktError("Failed to read configuration")
        }
        currentContext.obj = toolchainConfig
    }
}

fun main(args: Array<String>) {
    ToolchainMain.main(args)
}