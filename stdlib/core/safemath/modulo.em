package emerge.core.safemath

// adds the two numbers, overflowing from (2^7)-1 to -(2^7), and from -(2^7) back to 0.
export nothrow intrinsic fn plusModulo(self: S8, summand: S8) -> S8

// adds the two numbers, overflowing from (2^8)-1 to 0
export nothrow intrinsic fn plusModulo(self: U8, summand: U8) -> U8

// adds the two numbers, overflowing from (2^15)-1 to -(2^15), and from -(2^15) back to 0.
export nothrow intrinsic fn plusModulo(self: S16, summand: S16) -> S16

// adds the two numbers, overflowing from (2^16)-1 to 0
export nothrow intrinsic fn plusModulo(self: U16, summand: U16) -> U16

// adds the two numbers, overflowing from (2^31)-1 to -(2^31), and from -(2^31) back to 0.
export nothrow intrinsic fn plusModulo(self: S32, summand: S32) -> S32

// adds the two numbers, overflowing from (2^32)-1 to 0
export nothrow intrinsic fn plusModulo(self: U32, summand: U32) -> U32

// adds the two numbers, overflowing from (2^63)-1 to -(2^63), and from -(2^63) back to 0.
export nothrow intrinsic fn plusModulo(self: S64, summand: S64) -> S64

// adds the two numbers, overflowing from (2^64)-1 to 0
export nothrow intrinsic fn plusModulo(self: U64, summand: U64) -> U64

// adds the two numbers, overflowing from MAX to MIN and from MIN back to 0. 
export nothrow intrinsic fn plusModulo(self: SWord, summand: SWord) -> SWord

// adds the two numbers, overflowing from MAX to 0.
export nothrow intrinsic fn plusModulo(self: UWord, summand: UWord) -> UWord