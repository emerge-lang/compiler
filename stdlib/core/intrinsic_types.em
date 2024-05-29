package emerge.core

export class Unit {
    private constructor {}
}

export interface Any {}

export class Nothing {
    private constructor {}
}

export class F32 {
    private constructor {}
}

export class F64 {
    private constructor {}
}

export class S8 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S8
    export intrinsic operator fn negate(self) -> S8

    export intrinsic operator fn plus(self, summand: S8) -> S8
    export intrinsic operator fn minus(self, operand: S8) -> S8
    export intrinsic operator fn times(self, factor: S8) -> S8
    export intrinsic operator fn divideBy(self, divisor: S8) -> S8
    export intrinsic operator fn rem(self, divisor: S8) -> S8

    export intrinsic operator fn compareTo(self, other: S8) -> S8
    export intrinsic operator fn equals(self, other: S8) -> Bool

    export fn abs(self) = if self < 0 -self else self

    export intrinsic fn toS64(self) -> S64
}

export class U8 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U8

    export intrinsic operator fn plus(self, summand: U8) -> U8
    export intrinsic operator fn minus(self, operand: U8) -> U8
    export intrinsic operator fn times(self, factor: U8) -> U8
    export intrinsic operator fn divideBy(self, divisor: U8) -> U8
    export intrinsic operator fn rem(self, divisor: U8) -> U8

    export intrinsic operator fn compareTo(self, other: U8) -> S8
    export intrinsic operator fn equals(self, other: U8) -> Bool

    export intrinsic fn toU64(self) -> U64
}

export class S16 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S16
    export intrinsic operator fn negate(self) -> S16

    export intrinsic operator fn plus(self, summand: S16) -> S16
    export intrinsic operator fn minus(self, operand: S16) -> S16
    export intrinsic operator fn times(self, factor: S16) -> S16
    export intrinsic operator fn divideBy(self, divisor: S16) -> S16
    export intrinsic operator fn rem(self, divisor: S16) -> S16

    export intrinsic operator fn compareTo(self, other: S16) -> S16
    export intrinsic operator fn equals(self, other: S16) -> Bool

    export fn abs(self) = if self < 0 -self else self

    export intrinsic fn toS64(self) -> S64
}

export class U16 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U16

    export intrinsic operator fn plus(self, summand: U16) -> U16
    export intrinsic operator fn minus(self, operand: U16) -> U16
    export intrinsic operator fn times(self, factor: U16) -> U16
    export intrinsic operator fn divideBy(self, divisor: U16) -> U16
    export intrinsic operator fn rem(self, divisor: U16) -> U16

    export intrinsic operator fn compareTo(self, other: U16) -> S16
    export intrinsic operator fn equals(self, other: U16) -> Bool

    export intrinsic fn toU64(self) -> U64
}

export class S32 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S32
    export intrinsic operator fn negate(self) -> S32

    export intrinsic operator fn plus(self, summand: S32) -> S32
    export intrinsic operator fn minus(self, operand: S32) -> S32
    export intrinsic operator fn times(self, factor: S32) -> S32
    export intrinsic operator fn divideBy(self, divisor: S32) -> S32
    export intrinsic operator fn rem(self, divisor: S32) -> S32

    export intrinsic operator fn compareTo(self, other: S32) -> S32
    export intrinsic operator fn equals(self, other: S32) -> Bool

    export fn abs(self) = if self < 0 -self else self

    export intrinsic fn toS64(self) -> S64
}

export class U32 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U32

    export intrinsic operator fn plus(self, summand: U32) -> U32
    export intrinsic operator fn minus(self, operand: U32) -> U32
    export intrinsic operator fn times(self, factor: U32) -> U32
    export intrinsic operator fn divideBy(self, divisor: U32) -> U32
    export intrinsic operator fn rem(self, divisor: U32) -> U32

    export intrinsic operator fn compareTo(self, other: U32) -> S32
    export intrinsic operator fn equals(self, other: U32) -> Bool

    export intrinsic fn toU64(self) -> U64
}

export class S64 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S64
    export intrinsic operator fn negate(self) -> S64

    export intrinsic operator fn plus(self, summand: S64) -> S64
    export intrinsic operator fn minus(self, operand: S64) -> S64
    export intrinsic operator fn times(self, factor: S64) -> S64
    export intrinsic operator fn divideBy(self, divisor: S64) -> S64
    export intrinsic operator fn rem(self, divisor: S64) -> S64

    export intrinsic operator fn compareTo(self, other: S64) -> S64
    export intrinsic operator fn equals(self, other: S64) -> Bool

    export fn abs(self) = if self < 0 -self else self
}

export class U64 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U64

    export intrinsic operator fn plus(self, summand: U64) -> U64
    export intrinsic operator fn minus(self, operand: U64) -> U64
    export intrinsic operator fn times(self, factor: U64) -> U64
    export intrinsic operator fn divideBy(self, divisor: U64) -> U64
    export intrinsic operator fn rem(self, divisor: U64) -> U64

    export intrinsic operator fn compareTo(self, other: U64) -> S64
    export intrinsic operator fn equals(self, other: U64) -> Bool
}

export class SWord {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> SWord
    export intrinsic operator fn negate(self) -> SWord

    export intrinsic operator fn plus(self, summand: SWord) -> SWord
    export intrinsic operator fn minus(self, operand: SWord) -> SWord
    export intrinsic operator fn times(self, factor: SWord) -> SWord
    export intrinsic operator fn divideBy(self, divisor: SWord) -> SWord
    export intrinsic operator fn rem(self, divisor: SWord) -> SWord

    export intrinsic operator fn compareTo(self, other: SWord) -> SWord
    export intrinsic operator fn equals(self, other: SWord) -> Bool

    export fn abs(self) = if self < 0 -self else self
}

export class UWord {
    private constructor {}

    export intrinsic operator fn negate(self) -> UWord

    export intrinsic operator fn plus(self, summand: UWord) -> UWord
    export intrinsic operator fn minus(self, operand: UWord) -> UWord
    export intrinsic operator fn times(self, factor: UWord) -> UWord
    export intrinsic operator fn divideBy(self, dividend: UWord) -> UWord
    export intrinsic operator fn rem(self, divisor: UWord) -> UWord

    export intrinsic operator fn compareTo(self, other: UWord) -> SWord
    export intrinsic operator fn equals(self, other: UWord) -> Bool
}

export class Bool {
    private constructor {}

    export intrinsic operator fn negate(self) -> Bool

    export intrinsic operator fn and(self, other: Bool) -> Bool
    export intrinsic operator fn or(self, other: Bool) -> Bool
    export intrinsic operator fn xor(self, other: Bool) -> Bool
}

export class Array<Element> {
    export size: UWord = init

    private constructor {}

    export operator intrinsic fn get(self: read _<out Element>, index: UWord) -> Element

    export operator intrinsic fn set(self: mut _<in Element>, index: UWord, value: Element) -> Unit

    export intrinsic fn size(self: read _) -> UWord

    export intrinsic fn new<T>(size: UWord, initialValue: T) -> exclusive Array<T>

    export fn copy<T>(borrow source: read Array<out T>, sourceOffset: UWord, borrow dest: mut Array<in T>, destOffset: UWord, length: UWord) {
        if sourceOffset + length > source.size {
            panic("length overflows source")
        }

        if destOffset + length > dest.size {
            panic("length overflows dest")
        }

        var sourceIndex = sourceOffset
        var destIndex = destOffset
        var nCopied: UWord = 0
        while nCopied < length {
            element: T = source[sourceIndex]
            set dest[destIndex] = element
            set sourceIndex = sourceIndex + 1
            set destIndex = destIndex + 1
            set nCopied = nCopied + 1
        }
    }
}