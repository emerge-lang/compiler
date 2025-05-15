package io.github.tmarsteel.emerge.common

/**
 * Necessary, "magic" constants that are chosen arbitrarily
 */
data object EmergeConstants {
    val CORE_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "core"))
    val STD_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "std"))
    val PLATFORM_MODULE_NAME = CanonicalElementName.Package(listOf("emerge", "platform"))

    /**
     * the identifier to use in the initialization expression for member variables to indicate that the
     * initial value for the member variable is obtained through the constructor invocation
     *
     *     class A {
     *       var n: S32 = init
     *     }
     *     myA = A(5) // n is initialized to 5
     */
    val MAGIC_IDENTIFIER_CONSTRUCTOR_INITIALIZED_MEMBER_VARIABLE = "init"
}