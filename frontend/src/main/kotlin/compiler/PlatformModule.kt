package compiler

import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * The very core module of the language, defining intrinsic elements that are implemented by the
 * compiler/backends, rather than source code from the standard library.
 */
object PlatformModule {
    val NAME = CanonicalElementName.Package(listOf("emerge", "platform"))
}