package io.github.tmarsteel.emerge.common

/**
 * Necessary, "magic" constants that are chosen arbitrarily
 */
data object EmergeConstants {
    val CORE_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "core"))
    val STD_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "std"))
    val PLATFORM_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "platform"))
}