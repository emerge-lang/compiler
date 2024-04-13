package compiler

import io.github.tmarsteel.emerge.backend.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import java.nio.file.Path
import java.nio.file.Paths

data object StandardLibraryModule {
    val NAME: CanonicalElementName.Package = CanonicalElementName.Package(listOf("emerge", "std"))
    val SRC_DIR: Path by systemProperty("emerge.frontend.std.sources", Paths::get)
}