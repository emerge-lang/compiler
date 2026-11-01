package io.github.tmarsteel.emerge.backend.noop

import com.fasterxml.jackson.databind.annotation.JsonDeserialize
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition
import io.github.tmarsteel.emerge.common.config.DirectoryDeserializer
import java.nio.file.Path

class NoopBackend : EmergeBackend<NoopBackend.Config, Unit> {
    override val targetName = "noop"

    override val toolchainConfigKClass = Config::class
    override val projectConfigKClass = Unit::class

    override fun getTargetSpecificModules(
        toolchainConfig: Config,
        projectConfig: Unit
    ): Iterable<ConfigModuleDefinition> {
        return listOf(ConfigModuleDefinition(
            EmergeConstants.PlatformModule.NAME,
            toolchainConfig.platformSources,
        ))
    }

    override fun emit(toolchainConfig: Config, projectConfig: Unit, softwareContext: IrSoftwareContext) {

    }

    data class Config(
        @param:JsonDeserialize(using = DirectoryDeserializer::class)
        val platformSources: Path
    )
}