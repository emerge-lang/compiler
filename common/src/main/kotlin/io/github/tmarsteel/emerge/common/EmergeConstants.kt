package io.github.tmarsteel.emerge.common

import io.github.tmarsteel.emerge.common.EmergeConstants.IterableContract.RANGE_FRONT_FUNCTION_NAME


/**
 * Necessary, "magic" constants that are chosen arbitrarily
 */
data object EmergeConstants {
    data object CoreModule {
        val NAME = CanonicalElementName.Package(listOf("emerge", "core"))
        val ANY_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Any")
        val UNIT_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Unit")
        val THROWABLE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Throwable")
        val ERROR_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Error")
        val CAST_ERROR_TYPE_NAME = CanonicalElementName.BaseType(NAME, "CastError")
        val ARITHMETIC_ERROR_TYPE_NAME = CanonicalElementName.BaseType(NAME, "ArithmeticError")

        val BOOLEAN_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Boolean")
        val S8_TYPE_NAME = CanonicalElementName.BaseType(NAME, "S8")
        val U8_TYPE_NAME = CanonicalElementName.BaseType(NAME, "U8")
        val S16_TYPE_NAME = CanonicalElementName.BaseType(NAME, "S16")
        val U16_TYPE_NAME = CanonicalElementName.BaseType(NAME, "U16")
        val S32_TYPE_NAME = CanonicalElementName.BaseType(NAME, "S32")
        val U32_TYPE_NAME = CanonicalElementName.BaseType(NAME, "U32")
        val S64_TYPE_NAME = CanonicalElementName.BaseType(NAME, "S64")
        val U64_TYPE_NAME = CanonicalElementName.BaseType(NAME, "U64")
        val F32_TYPE_NAME = CanonicalElementName.BaseType(NAME, "F32")
        val F64_TYPE_NAME = CanonicalElementName.BaseType(NAME, "F64")
        val SWORD_TYPE_NAME = CanonicalElementName.BaseType(NAME, "SWord")
        val UWORD_TYPE_NAME = CanonicalElementName.BaseType(NAME, "UWord")
    }

    data object ReflectionModule {
        val NAME = CoreModule.NAME + "reflection"
        val REFLECTION_BASE_TYPE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "ReflectionBaseType")
    }

    data object StdModule {
        val NAME = CanonicalElementName.Package(listOf("emerge", "std"))
    }

    data object PlatformModule {
        val NAME = CanonicalElementName.Package(listOf("emerge", "platform"))
    }

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

    data object IterableContract {
        /**
         * The name of the function on `emerge.core.range.Iterable` that returns a new
         * `emerge.core.range.InputRange`; signature is `<T>(capture self: read Iterable<T>) -> exclusive InputRange<T>`
         */
        val ITERABLE_AS_RANGE_FUNCTION_NAME = "asRange"

        /**
         * The name of the function on `emerge.core.range.InputRange` that returns the ranges
         * front value; signature is `(self) -> T`
         */
        val RANGE_FRONT_FUNCTION_NAME = "front"

        /**
         * The name of the function on `emerge.core.range.InputRange` that advances the `front`
         * pointer; signature is `(self: mut _) -> Unit`
         */
        val RANGE_POP_FRONT_FUNCTION_NAME = "popFront"

        /**
         * The canonical name of the execption type thrown from [RANGE_FRONT_FUNCTION_NAME] when the
         * range is empty.
         */
        val EMPTY_RANGE_EXCEPTION_NAME = CanonicalElementName.BaseType(
            CoreModule.NAME.plus("range"),
            "EmptyRangeException",
        )

        /**
         * The canonical name of the type that resembles something that is iterable. As per contract has
         * one type parameter: `T : Any?` which denotes the type of the elements that can be iterated over.
         */
        val ITERABLE_TYPE_NAME = CanonicalElementName.BaseType(
            CoreModule.NAME.plus("range"),
            "Iterable",
        )
    }
}