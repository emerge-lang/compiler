package io.github.tmarsteel.emerge.toolchain.config

import com.fasterxml.jackson.annotation.JsonProperty
import com.fasterxml.jackson.databind.annotation.JsonDeserialize
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.common.config.DirectoryDeserializer
import java.nio.file.Path

data class ToolchainConfig(
    val frontend: FrontendConfig,
    @param:JsonProperty("backends")
    @param:JsonDeserialize(using = BackendToolchainConfigsDeserializer::class)
    val backendConfigs: Map<EmergeBackend<*, *>, Any>,
) {
    data class FrontendConfig(
        @param:JsonDeserialize(using = DirectoryDeserializer::class)
        val stdModuleSources: Path,

        @param:JsonDeserialize(using = DirectoryDeserializer::class)
        val coreModuleSources: Path,
    )
}