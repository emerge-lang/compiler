package io.github.tmarsteel.emerge.backend.api

import java.nio.file.Path

/**
 * A reference to the sources of a module.
 */
data class ModuleSourceRef(
    val path: Path,
    val moduleName: PackageName,
)