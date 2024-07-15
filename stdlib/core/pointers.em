package emerge.core

// impure because addresses can change with every execution the program, without affecting
// functional correctness in any way
// @return the address of [value], or `0` in case the object is `null`. Undefined values for
// integral types such as [S8].
export intrinsic read nothrow fn addressOf(value: Any?) -> UWord

// whether [value] is null. Defined separately from [addressOf] because a null-check
// is pure, whereas inspecting the address more deeply isn't anymore.
export intrinsic nothrow fn isNull(value: Any?) -> Bool