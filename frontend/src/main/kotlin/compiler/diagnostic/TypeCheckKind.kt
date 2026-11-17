package compiler.diagnostic

/**
 * the ways to check a value against a type at runtime
 */
enum class TypeCheckKind {
    /** `x is T` */
    INSTANCE_OF,
    /** `x as T` */
    CAST,
    /** `x as? T` */
    SAFE_CAST,
}
