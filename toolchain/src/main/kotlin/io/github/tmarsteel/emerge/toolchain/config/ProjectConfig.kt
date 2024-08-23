package io.github.tmarsteel.emerge.toolchain.config

import com.fasterxml.jackson.databind.annotation.JsonDeserialize
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition

data class ProjectConfig(
    val modules: List<ConfigModuleDefinition>,

    @param:JsonDeserialize(using = BackendProjectConfigsDeserializer::class)
    val targets: Map<EmergeBackend<*, *>, Any>
)