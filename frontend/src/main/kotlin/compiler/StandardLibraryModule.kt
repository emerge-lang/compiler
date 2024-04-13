package compiler

import io.github.tmarsteel.emerge.backend.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.api.PackageName
import java.nio.file.Path
import java.nio.file.Paths

data object StandardLibraryModule {
    val NAME: PackageName = PackageName(listOf("emerge", "std"))
    val SRC_DIR: Path by systemProperty("emerge.frontend.std.sources", Paths::get)
}