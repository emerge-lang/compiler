package emerge.core

import emerge.platform.World

// Stands for the layout of the memory of the process: where an object lives can change with every execution of
// the program, without affecting functional correctness in any way. So reading an address takes this token.
// Having two of them does no harm; any code that holds the root can create one.
export token class AddressSpace {
    private nothrow constructor {}

    export nothrow fn create(borrow world: read World) -> own AddressSpace = AddressSpace()

    // @return the address of [value], or `0` in case the object is `null`. Undefined values for
    // integral types such as [S8].
    export intrinsic nothrow fn addressOf(self: read _, value: Any?) -> UWord
}

// whether [value] is null. Defined separately from [addressOf] because a null-check
// tells nothing about the layout of the memory, whereas inspecting the address more deeply does.
export intrinsic nothrow fn isNull(value: Any?) -> Bool