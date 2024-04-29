package compiler

import io.github.tmarsteel.emerge.backend.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import java.nio.file.Paths

/**
 * The very core module of the language, defining intrinsic elements that are implemented by the
 * compiler/backends, rather than source code from the standard library.
 */
object CoreIntrinsicsModule {
    val NAME = CanonicalElementName.Package(listOf("emerge", "core"))
    val ANY_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Any")
    val SRC_DIR by systemProperty("emerge.frontend.core.sources", Paths::get)
}