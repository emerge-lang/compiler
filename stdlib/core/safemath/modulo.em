package emerge.core.safemath

// ------- PLUS -------

// adds the two numbers, overflowing from (2^7)-1 to -(2^7), and from -(2^7) back to 0.
export nothrow intrinsic fn plusModulo(borrow self: S8, borrow summand: S8) -> S8

// adds the two numbers, overflowing from (2^8)-1 to 0
export nothrow intrinsic fn plusModulo(borrow self: U8, borrow summand: U8) -> U8

// adds the two numbers, overflowing from (2^15)-1 to -(2^15), and from -(2^15) back to 0.
export nothrow intrinsic fn plusModulo(borrow self: S16, borrow summand: S16) -> S16

// adds the two numbers, overflowing from (2^16)-1 to 0
export nothrow intrinsic fn plusModulo(borrow self: U16, borrow summand: U16) -> U16

// adds the two numbers, overflowing from (2^31)-1 to -(2^31), and from -(2^31) back to 0.
export nothrow intrinsic fn plusModulo(borrow self: S32, borrow summand: S32) -> S32

// adds the two numbers, overflowing from (2^32)-1 to 0
export nothrow intrinsic fn plusModulo(borrow self: U32, borrow summand: U32) -> U32

// adds the two numbers, overflowing from (2^63)-1 to -(2^63), and from -(2^63) back to 0.
export nothrow intrinsic fn plusModulo(borrow self: S64, borrow summand: S64) -> S64

// adds the two numbers, overflowing from (2^64)-1 to 0
export nothrow intrinsic fn plusModulo(borrow self: U64, borrow summand: U64) -> U64

// adds the two numbers, overflowing from MAX to MIN and from MIN back to 0. 
export nothrow intrinsic fn plusModulo(borrow self: SWord, borrow summand: SWord) -> SWord

// adds the two numbers, overflowing from MAX to 0.
export nothrow intrinsic fn plusModulo(borrow self: UWord, borrow summand: UWord) -> UWord

// ------- MINUS -------

// subtracts the two numbers, overflowing from -(2^7) to 2^7-1
export nothrow intrinsic fn minusModulo(borrow self: S8, borrow summand: S8) -> S8

// subtracts the two numbers, overflowing from 0 to 2^8-1
export nothrow intrinsic fn minusModulo(borrow self: U8, borrow summand: U8) -> U8

// subtracts the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: S16, borrow summand: S16) -> S16

// subtracts the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: U16, borrow summand: U16) -> U16

// subtracts the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: S32, borrow summand: S32) -> S32

// subtracts the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: U32, borrow summand: U32) -> U32

// subtracts the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: S64, borrow summand: S64) -> S64

// subtracts the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: U64, borrow summand: U64) -> U64

// subtracts the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: SWord, borrow summand: SWord) -> SWord

// subtracts the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn minusModulo(borrow self: UWord, borrow summand: UWord) -> UWord

// ------- TIMES -------

// multiplies the two numbers, overflowing from -(2^7) to 2^7-1
export nothrow intrinsic fn timesModulo(borrow self: S8, borrow factor: S8) -> S8

// multiplies the two numbers, overflowing from 0 to 2^8-1
export nothrow intrinsic fn timesModulo(borrow self: U8, borrow factor: U8) -> U8

// multiplies the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: S16, borrow factor: S16) -> S16

// multiplies the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: U16, borrow factor: U16) -> U16

// multiplies the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: S32, borrow factor: S32) -> S32

// multiplies the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: U32, borrow factor: U32) -> U32

// multiplies the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: S64, borrow factor: S64) -> S64

// multiplies the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: U64, borrow factor: U64) -> U64

// multiplies the two numbers, overflowing from -(2^16) to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: SWord, borrow factor: SWord) -> SWord

// multiplies the two numbers, overflowing from 0 to 2^16-1
export nothrow intrinsic fn timesModulo(borrow self: UWord, borrow factor: UWord) -> UWord