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
    export intrinsic operator fn divideBy(self, dividend: S8) -> S8
}

export class U8 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U8

    export intrinsic operator fn plus(self, summand: U8) -> U8
    export intrinsic operator fn minus(self, operand: U8) -> U8
    export intrinsic operator fn times(self, factor: U8) -> U8
    export intrinsic operator fn divideBy(self, dividend: U8) -> U8
}

export class S16 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S16
    export intrinsic operator fn negate(self) -> S16

    export intrinsic operator fn plus(self, summand: S16) -> S16
    export intrinsic operator fn minus(self, operand: S16) -> S16
    export intrinsic operator fn times(self, factor: S16) -> S16
    export intrinsic operator fn divideBy(self, dividend: S16) -> S16
}

export class U16 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U16

    export intrinsic operator fn plus(self, summand: U16) -> U16
    export intrinsic operator fn minus(self, operand: U16) -> U16
    export intrinsic operator fn times(self, factor: U16) -> U16
    export intrinsic operator fn divideBy(self, dividend: U16) -> U16
}

export class S32 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S32
    export intrinsic operator fn negate(self) -> S32

    export intrinsic operator fn plus(self, summand: S32) -> S32
    export intrinsic operator fn minus(self, operand: S32) -> S32
    export intrinsic operator fn times(self, factor: S32) -> S32
    export intrinsic operator fn divideBy(self, dividend: S32) -> S32
}

export class U32 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U32

    export intrinsic operator fn plus(self, summand: U32) -> U32
    export intrinsic operator fn minus(self, operand: U32) -> U32
    export intrinsic operator fn times(self, factor: U32) -> U32
    export intrinsic operator fn divideBy(self, dividend: U32) -> U32
}

export class S64 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S64
    export intrinsic operator fn negate(self) -> S64

    export intrinsic operator fn plus(self, summand: S64) -> S64
    export intrinsic operator fn minus(self, operand: S64) -> S64
    export intrinsic operator fn times(self, factor: S64) -> S64
    export intrinsic operator fn divideBy(self, dividend: S64) -> S64
}

export class U64 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U64

    export intrinsic operator fn plus(self, summand: U64) -> U64
    export intrinsic operator fn minus(self, operand: U64) -> U64
    export intrinsic operator fn times(self, factor: U64) -> U64
    export intrinsic operator fn divideBy(self, dividend: U64) -> U64
}

export class SWord {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> SWord
    export intrinsic operator fn negate(self) -> SWord

    export intrinsic operator fn plus(self, summand: SWord) -> SWord
    export intrinsic operator fn minus(self, operand: SWord) -> SWord
    export intrinsic operator fn times(self, factor: SWord) -> SWord
    export intrinsic operator fn divideBy(self, dividend: SWord) -> SWord
}

export class UWord {
    private constructor {}

    export intrinsic operator fn negate(self) -> UWord

    export intrinsic operator fn plus(self, summand: UWord) -> UWord
    export intrinsic operator fn minus(self, operand: UWord) -> UWord
    export intrinsic operator fn times(self, factor: UWord) -> UWord
    export intrinsic operator fn divideBy(self, dividend: UWord) -> UWord
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
}

export interface Throwable {}
export interface Error : Throwable {}
export interface Exception : Throwable {}