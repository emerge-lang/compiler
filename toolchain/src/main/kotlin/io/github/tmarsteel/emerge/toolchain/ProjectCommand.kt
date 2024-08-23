package io.github.tmarsteel.emerge.toolchain

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.CliktError
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.path
import io.github.tmarsteel.emerge.toolchain.config.ConfigParseException
import io.github.tmarsteel.emerge.toolchain.config.ProjectConfig
import io.github.tmarsteel.emerge.toolchain.config.parseAsConfig
import java.nio.file.Path

object ProjectCommand : CliktCommand() {
    private val projectConfigFile: Path by option("--project-config", help = "Configuration file for the project; usually created by the build system")
        .path(mustExist = true, canBeFile = true, canBeDir = false, mustBeReadable = true, canBeSymlink = true)
        .required()

    init {
        subcommands(CompileCommand)
    }

    override fun run() {
        val projectConfig = try {
            projectConfigFile.parseAsConfig<ProjectConfig>()
        } catch (ex: ConfigParseException) {
            ex.illustrate(currentContext.terminal)
            throw CliktError("Failed to read configuration")
        }
        currentContext.obj = projectConfig
    }
}