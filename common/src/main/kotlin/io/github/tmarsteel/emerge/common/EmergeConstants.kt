package io.github.tmarsteel.emerge.common


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

        val BOOL_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Bool")
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
        val ARRAY_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Array")
        val STRING_TYPE_NAME = CanonicalElementName.BaseType(NAME, "String")
        val ANNOTATABLE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Annotatable")
    }

    data object ReflectionModule {
        val NAME = CoreModule.NAME + "reflection"
        val REFLECTION_BASE_TYPE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "ReflectionBaseType")
        val TYPE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "Type")
        val NAMED_TYPE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "NamedType")
        val INTERSECTION_TYPE_TYPE_NAME = CanonicalElementName.BaseType(NAME, "IntersectionType")
        val TYPE_ARGUMENT_TYPE_NAME = CanonicalElementName.BaseType(NAME, "TypeArgument")
        val TYPE_WITH_NULLABILITY_FN_NAME = "withNullability"
        val INTERSECTION_OF_FN_NAME = CanonicalElementName.Function(NAME, "intersectionOf")
        val TYPEOF_FN_NAME = CanonicalElementName.Function(NAME, "typeOf")

        /** values of `TypeArgument.variance` */
        const val VARIANCE_INVARIANT: UByte = 0u
        const val VARIANCE_IN: UByte = 1u
        const val VARIANCE_OUT: UByte = 2u
    }

    data object StdModule {
        val NAME = CanonicalElementName.Package(listOf("emerge", "std"))
    }

    data object PlatformModule {
        val NAME = CanonicalElementName.Package(listOf("emerge", "platform"))

        /**
         * The root token: a token class with one instance per process, which the platform constructs and passes
         * to the main function of the program if that declares a parameter for it.
         */
        val WORLD_TYPE_NAME = CanonicalElementName.BaseType(NAME, "World")

        /**
         * A token class that collects stack traces. The runtime holds an instance per thread and passes it to
         * `Throwable.fillStackTrace` on `throw`.
         */
        val STACK_TRACE_COLLECTOR_TYPE_NAME = CanonicalElementName.BaseType(NAME, "StackTraceCollector")
    }

    /**
     * The name of the static function the compiler adds to every `unique class`. It hands out the one instance of
     * the class; signature is `(world: mut emerge.platform.World, <constructor parameters>) -> own C?`
     */
    const val UNIQUE_CLASS_TAKE_FUNCTION_NAME = "take"

    /**
     * Identifiers the compiler generates for its own use start with this, e.g. the variable that knows whether the
     * instance of a `unique class` was handed out.
     */
    const val COMPILER_INTERNAL_IDENTIFIER_PREFIX = "__"

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
         * `emerge.core.range.InputRange`; signature is `<T>(capture self: read Iterable<T>) -> own InputRange<T>`
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