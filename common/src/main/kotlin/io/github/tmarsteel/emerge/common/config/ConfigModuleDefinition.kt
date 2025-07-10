package io.github.tmarsteel.emerge.common.config

import com.fasterxml.jackson.annotation.JsonProperty
import com.fasterxml.jackson.databind.annotation.JsonDeserialize
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import java.nio.file.Path

data class ConfigModuleDefinition(
    @param:JsonProperty("name")
    val name: CanonicalElementName.Package,

    @param:JsonProperty("sources")
    @param:JsonDeserialize(using = DirectoryDeserializer::class)
    val sourceDirectory: Path,

    @param:JsonProperty("uses")
    val uses: Set<CanonicalElementName.Package> = emptySet()
) {
    val implicitlyUses: Set<CanonicalElementName.Package> = when (this.name) {
        EmergeConstants.CORE_MODULE_NAME -> emptySet()
        EmergeConstants.STD_MODULE_NAME -> setOf(EmergeConstants.CORE_MODULE_NAME)
        else -> setOf(EmergeConstants.CORE_MODULE_NAME, EmergeConstants.STD_MODULE_NAME)
    }
}