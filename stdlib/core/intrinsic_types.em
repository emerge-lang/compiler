package emerge.core

import emerge.platform.panic
import emerge.std.io.PrintStream
import emerge.std.collections.ArrayList
import emerge.core.range.ArrayRange
import emerge.core.range.Iterable
import emerge.core.range.UWordRange
import emerge.core.safemath.plusModulo

export class Unit : const Any {
    private nothrow constructor {}

    export nothrow intrinsic fn instance() -> Unit
}

export interface Any {}

// the supertype of everything that is no token. Every class that is not declared `token` is a subtype
// without saying so, an interface is one where it inherits from it.
export interface NonToken {}

export class Nothing : const Any {
    private nothrow constructor {
        panic("Cannot create instances of emerge.core.Nothing")
    }
}

export class F32 : const Any {
    private nothrow constructor {}
}

export class F64 : const Any {
    private nothrow constructor {}
}

export class S8 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn unaryMinus(self) -> S8
    export intrinsic nothrow operator fn bitwiseNot(self) -> S8

    export intrinsic operator fn plus(self, borrow summand: S8) -> S8
    export intrinsic operator fn minus(self, borrow operand: S8) -> S8
    export intrinsic operator fn times(self, borrow factor: S8) -> S8
    export intrinsic operator fn divideBy(self, borrow divisor: S8) -> S8
    export intrinsic nothrow fn rem(self, borrow divisor: S8) -> S8
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> S8
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> S8
    export intrinsic nothrow fn arithmeticBitShiftRight(self, borrow amount: U8) -> S8
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: S8) -> S8
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: S8) -> S8
    export intrinsic nothrow operator fn `xor`(self, borrow other: S8) -> S8

    export intrinsic nothrow operator fn compareTo(self, borrow other: S8) -> S8
    export intrinsic nothrow operator fn equals(self, borrow other: S8) -> Bool

    export nothrow fn abs(self) = if self < 0 -self else self.copy()

    export intrinsic nothrow fn asU8(self) -> U8

    export intrinsic nothrow fn toS16(self) -> S16
    export intrinsic nothrow fn toS32(self) -> S32
    export intrinsic nothrow fn toS64(self) -> S64
    export intrinsic nothrow fn toSWord(self) -> SWord

    export fn toString(self) = self.toS64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toS64().printTo(stream)
    }

    export intrinsic nothrow fn copy(self) -> S8

    export nothrow fn min() -> S8 = -128
    export nothrow fn max() -> S8 = 127
}

export class U8 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> U8

    export intrinsic operator fn plus(self, borrow summand: U8) -> U8
    export intrinsic operator fn minus(self, borrow operand: U8) -> U8
    export intrinsic operator fn times(self, borrow factor: U8) -> U8
    export intrinsic operator fn divideBy(self, borrow divisor: U8) -> U8
    export intrinsic nothrow fn rem(self, borrow divisor: U8) -> U8
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> U8
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> U8
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: U8) -> U8
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: U8) -> U8
    export intrinsic nothrow operator fn `xor`(self, borrow other: U8) -> U8

    export intrinsic nothrow operator fn compareTo(self, borrow other: U8) -> S8
    export intrinsic nothrow operator fn equals(self, borrow other: U8) -> Bool

    export intrinsic nothrow fn asS8(self) -> S8

    export intrinsic nothrow fn toU16(self) -> U16
    export intrinsic nothrow fn toU32(self) -> U32
    export intrinsic nothrow fn toU64(self) -> U64
    export intrinsic nothrow fn toUWord(self) -> UWord

    export fn toString(self) = self.toU64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toU64().printTo(stream)
    }

    export nothrow fn min() -> U8 = 0
    export nothrow fn max() -> U8 = 255
}

export class S16 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn unaryMinus(self) -> S16
    export intrinsic nothrow operator fn bitwiseNot(self) -> S16

    export intrinsic operator fn plus(self, borrow summand: S16) -> S16
    export intrinsic operator fn minus(self, borrow operand: S16) -> S16
    export intrinsic operator fn times(self, borrow factor: S16) -> S16
    export intrinsic operator fn divideBy(self, borrow divisor: S16) -> S16
    export intrinsic nothrow fn rem(self, borrow divisor: S16) -> S16
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> S16
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> S16
    export intrinsic nothrow fn arithmeticBitShiftRight(self, borrow amount: U8) -> S16
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: S16) -> S16
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: S16) -> S16
    export intrinsic nothrow operator fn `xor`(self, borrow other: S16) -> S16

    export intrinsic nothrow operator fn compareTo(self, borrow other: S16) -> S16
    export intrinsic nothrow operator fn equals(self, borrow other: S16) -> Bool

    export nothrow fn abs(self) = if self < 0 -self else self.copy()

    export intrinsic nothrow fn asU16(self) -> U16

    export intrinsic nothrow fn toS32(self) -> S32
    export intrinsic nothrow fn toS64(self) -> S64
    export intrinsic nothrow fn toSWord(self) -> SWord

    export fn toString(self) = self.toS64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toS64().printTo(stream)
    }

    export intrinsic nothrow fn copy(self) -> S16

    export nothrow fn min() -> S16 = -32768
    export nothrow fn max() -> S16 = 32767
}

export class U16 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> U16

    export intrinsic operator fn plus(self, borrow summand: U16) -> U16
    export intrinsic operator fn minus(self, borrow operand: U16) -> U16
    export intrinsic operator fn times(self, borrow factor: U16) -> U16
    export intrinsic operator fn divideBy(self, borrow divisor: U16) -> U16
    export intrinsic nothrow fn rem(self, borrow divisor: U16) -> U16
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> S16
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> S16
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: U16) -> U16
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: U16) -> U16
    export intrinsic nothrow operator fn `xor`(self, borrow other: U16) -> U16

    export intrinsic nothrow operator fn compareTo(self, borrow other: U16) -> S16
    export intrinsic nothrow operator fn equals(self, borrow other: U16) -> Bool

    export intrinsic nothrow fn asS16(self) -> S16

    export intrinsic nothrow fn toU32(self) -> U32
    export intrinsic nothrow fn toU64(self) -> U64
    export intrinsic nothrow fn toUWord(self) -> UWord

    export fn toString(self) = self.toU64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toU64().printTo(stream)
    }

    export nothrow fn min() -> U16 = 0
    export nothrow fn max() -> U16 = 65535
}

export class S32 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn unaryMinus(self) -> S32
    export intrinsic nothrow operator fn bitwiseNot(self) -> S32

    export intrinsic operator fn plus(self, borrow summand: S32) -> S32
    export intrinsic operator fn minus(self, borrow operand: S32) -> S32
    export intrinsic operator fn times(self, borrow factor: S32) -> S32
    export intrinsic operator fn divideBy(self, borrow divisor: S32) -> S32
    export intrinsic nothrow fn rem(self, borrow divisor: S32) -> S32
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> S32
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> S32
    export intrinsic nothrow fn arithmeticBitShiftRight(self, borrow amount: U8) -> S32
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: S32) -> S32
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: S32) -> S32
    export intrinsic nothrow operator fn `xor`(self, borrow other: S32) -> S32

    export intrinsic nothrow operator fn compareTo(self, borrow other: S32) -> S32
    export intrinsic nothrow operator fn equals(self, borrow other: S32) -> Bool

    export nothrow fn abs(self) = if self < 0 -self else self.copy()

    export intrinsic nothrow fn asU32(self) -> U32

    export intrinsic nothrow fn toS64(self) -> S64
    export intrinsic nothrow fn toSWord(self) -> SWord

    export fn toString(self) = self.toS64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toS64().printTo(stream)
    }

    export intrinsic nothrow fn copy(self) -> S32

    export nothrow fn min() -> S32 = -2147483648
    export nothrow fn max() -> S32 = 2147483647
}

export class U32 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> U32

    export intrinsic operator fn plus(self, borrow summand: U32) -> U32
    export intrinsic operator fn minus(self, borrow operand: U32) -> U32
    export intrinsic operator fn times(self, borrow factor: U32) -> U32
    export intrinsic operator fn divideBy(self, borrow divisor: U32) -> U32
    export intrinsic nothrow fn rem(self, borrow divisor: U32) -> U32
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> U32
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> U32
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: U32) -> U32
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: U32) -> U32
    export intrinsic nothrow operator fn `xor`(self, borrow other: U32) -> U32

    export intrinsic nothrow operator fn compareTo(self, borrow other: U32) -> S32
    export intrinsic nothrow operator fn equals(self, borrow other: U32) -> Bool

    export intrinsic nothrow fn asS32(self) -> S32

    export intrinsic nothrow fn toU64(self) -> U64
    export intrinsic nothrow fn toUWord(self) -> UWord

    export fn toString(self) = self.toU64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.toU64().printTo(stream)
    }

    export nothrow fn min() -> S32 = -2147483648
    export nothrow fn max() -> S32 = 2147483647
}

export class S64 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn unaryMinus(self) -> S64
    export intrinsic nothrow operator fn bitwiseNot(self) -> S64

    export intrinsic operator fn plus(self, borrow summand: S64) -> S64
    export intrinsic operator fn minus(self, borrow operand: S64) -> S64
    export intrinsic operator fn times(self, borrow factor: S64) -> S64
    export intrinsic operator fn divideBy(self, borrow divisor: S64) -> S64
    export intrinsic nothrow fn rem(self, borrow divisor: S64) -> S64
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> S64
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> S64
    export intrinsic nothrow fn arithmeticBitShiftRight(self, borrow amount: U8) -> S64
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: S64) -> S64
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: S64) -> S64
    export intrinsic nothrow operator fn `xor`(self, borrow other: S64) -> S64

    export intrinsic nothrow operator fn compareTo(self, borrow other: S64) -> S64
    export intrinsic nothrow operator fn equals(self, borrow other: S64) -> Bool

    export nothrow fn abs(self) = if self < 0 -self else self.copy()

    export intrinsic nothrow fn asU64(self) -> U64

    // converts this number to an SWord, loosing information if SWord is smaller than S64 on the target platform
    export intrinsic nothrow fn asSWord(self) -> SWord

    export fn toString(self) = if self >= 0 self.asU64().toString() else self.abs().asU64().toString(true)
    export override fn printTo(self, borrow stream: mut PrintStream) {
        if self < 0 {
            self.abs().asU64().printTo(stream, true)
        } else {
            self.asU64().printTo(stream, false)
        }
    }

    export intrinsic nothrow fn copy(self) -> S64

    export nothrow fn min() -> S64 = -9223372036854775808
    export nothrow fn max() -> S64 = 9223372036854775807
}

export class U64 : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> U64

    export intrinsic operator fn plus(self, borrow summand: U64) -> U64
    export intrinsic operator fn minus(self, borrow operand: U64) -> U64
    export intrinsic operator fn times(self, borrow factor: U64) -> U64
    export intrinsic operator fn divideBy(self, borrow divisor: U64) -> U64
    export intrinsic nothrow fn rem(self, borrow divisor: U64) -> U64
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> U64
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> U64
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: U64) -> U64
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: U64) -> U64
    export intrinsic nothrow operator fn `xor`(self, borrow other: U64) -> U64

    export intrinsic nothrow operator fn compareTo(self, borrow other: U64) -> S64
    export intrinsic nothrow operator fn equals(self, borrow other: U64) -> Bool

    export intrinsic nothrow fn asS64(self) -> S64

    // converts this number to a UWord, loosing information if UWord is smaller than U64 on the target platform
    export intrinsic nothrow fn asUWord(self) -> UWord

    export fn toString(self) = self.toString(false)

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.printTo(stream, false)
    }

    private fn printTo(self, borrow stream: mut PrintStream, addMinusSign: Bool) {
        stream.put(self.toString(addMinusSign))
    }
    
    private fn toString(self: U64, addMinusSign: Bool) -> const String {
        if self == 0 {
            return "0"
        }

        // 2^64-1 plus sign is at MOST 21 chars
        var buf = Array.new::<S8>(21, SPACE_CODEPOINT)
        var insertionIndex: UWord = buf.size - 1
        var remainingNumber = self + 0
        while remainingNumber != 0 {
            digitAsNumber = remainingNumber.rem(10)
            digitCodepoint = DIGIT_CODEPOINTS_FOR_TO_STRING[digitAsNumber.asUWord()]
            set buf[insertionIndex] = digitCodepoint

            set remainingNumber = remainingNumber / (10 as U64)
            set insertionIndex = insertionIndex - 1
        }

        if addMinusSign {
            set buf[insertionIndex] = MINUS_SIGN_CODEPOINT
            set insertionIndex = insertionIndex - 1
        }

        return String.fromUtf8(buf.sliceOrPanic(insertionIndex + 1, buf.size))
    }

    export nothrow fn min() -> U64 = 0
    export nothrow fn max() -> U64 = 18446744073709551615
}

export class SWord : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn unaryMinus(self) -> SWord
    export intrinsic nothrow operator fn bitwiseNot(self) -> SWord

    export intrinsic operator fn plus(self, borrow summand: SWord) -> SWord
    export intrinsic operator fn minus(self, borrow operand: SWord) -> SWord
    export intrinsic operator fn times(self, borrow factor: SWord) -> SWord
    export intrinsic operator fn divideBy(self, borrow divisor: SWord) -> SWord
    export intrinsic nothrow fn rem(self, borrow divisor: SWord) -> SWord
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> SWord
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> SWord
    export intrinsic nothrow fn arithmeticBitShiftRight(self, borrow amount: U8) -> SWord
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: SWord) -> SWord
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: SWord) -> SWord
    export intrinsic nothrow operator fn `xor`(self, borrow other: SWord) -> SWord

    export intrinsic nothrow operator fn compareTo(self, borrow other: SWord) -> SWord
    export intrinsic nothrow operator fn equals(self, borrow other: SWord) -> Bool

    export intrinsic nothrow fn asUWord(self) -> UWord

    export nothrow fn abs(self) = if self < 0 -self else self.copy()

    export intrinsic nothrow fn asS64(self) -> S64
    export intrinsic nothrow fn asU64(self) -> U64

    export fn toString(self) = self.asS64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.asS64().printTo(stream)
    }

    export intrinsic nothrow fn copy(self) -> SWord

    export intrinsic nothrow fn min() -> SWord
    export intrinsic nothrow fn max() -> SWord
}

export class UWord : const Any & Printable {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> UWord

    export intrinsic operator fn plus(self, borrow summand: UWord) -> UWord
    export intrinsic operator fn minus(self, borrow operand: UWord) -> UWord
    export intrinsic operator fn times(self, borrow factor: UWord) -> UWord
    export intrinsic operator fn divideBy(self, borrow dividend: UWord) -> UWord
    export intrinsic nothrow fn rem(self, borrow divisor: UWord) -> UWord
    
    export intrinsic nothrow fn bitShiftLeft(self, borrow amount: U8) -> UWord
    export intrinsic nothrow fn logicalBitShiftRight(self, borrow amount: U8) -> UWord
    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: UWord) -> UWord
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: UWord) -> UWord
    export intrinsic nothrow operator fn `xor`(self, borrow other: UWord) -> UWord

    export intrinsic nothrow operator fn compareTo(self, borrow other: UWord) -> SWord
    export intrinsic nothrow operator fn equals(self, borrow other: UWord) -> Bool

    export intrinsic nothrow fn asSWord(self) -> SWord

    export intrinsic nothrow fn asS64(self) -> S64
    export intrinsic nothrow fn asU64(self) -> U64

    export operator fn rangeToExclusive(capture self, endExclusive: UWord) -> own UWordRange = UWordRange(self, endExclusive)

    export fn toString(self) = self.asU64().toString()
    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.asU64().printTo(stream)
    }

    export nothrow fn min() -> UWord = 0
    export intrinsic nothrow fn max() -> UWord
}

export class Bool : const Any {
    private nothrow constructor {}

    export intrinsic nothrow operator fn bitwiseNot(self) -> Bool

    export intrinsic nothrow operator fn bitwiseAnd(self, borrow other: Bool) -> Bool
    export intrinsic nothrow operator fn bitwiseOr(self, borrow other: Bool) -> Bool
    export intrinsic nothrow operator fn `xor`(self, borrow other: Bool) -> Bool
    export intrinsic nothrow operator fn equals(self, borrow other: Bool) -> Bool

    export nothrow fn toString(self) = if self "true" else "false"
}

export class Array<Element> : Iterable<Element> {
    export size: UWord = init

    private nothrow constructor {}

    export operator intrinsic fn getAtIndex(self: read _<out Element>, index: UWord) -> Element
    export operator intrinsic fn setAtIndex(self: mut _<in Element>, index: UWord, value: Element) -> Unit
    export operator fn getAtIndex<A : read Array<out Any?>>(capture self: A, borrow range: read UWordRange) -> A = self.slice(range.start, range.endExclusive)
    
    export nothrow intrinsic fn getOrPanic(self: read _<out Element>, index: UWord) -> Element
    export nothrow intrinsic fn setOrPanic(self: mut _<in Element>, index: UWord, value: Element) -> Unit

    export operator intrinsic fn slice<A : read Array<out Any?>>(capture self: A, fromIndex: UWord, toIndexExclusive: UWord) -> A
    export nothrow intrinsic fn sliceOrPanic<A : read Array<out Any?>>(capture self: A, fromIndex: UWord, toIndexExclusive: UWord) -> A

    export nothrow intrinsic fn new<T>(size: UWord, initialValue: T) -> own Array<T>

    export nothrow fn copy<T>(borrow source: read Array<out T>, sourceOffset: UWord, borrow dest: mut Array<in T>, destOffset: UWord, length: UWord) {
        sourceEnd = sourceOffset.plusModulo(length)
        if sourceEnd < sourceOffset or sourceEnd > source.size {
            panic("length overflows source")
        }

        destEnd = destOffset.plusModulo(length)
        if destEnd < destOffset or destEnd > dest.size {
            panic("length overflows dest")
        }

        // the bounds are checked above, so the indices below cannot overflow
        var nCopied: UWord = 0
        while nCopied < length {
            element: T = source.getOrPanic(sourceOffset.plusModulo(nCopied))
            dest.setOrPanic(destOffset.plusModulo(nCopied), element)
            set nCopied = nCopied.plusModulo(1 as UWord)
        }
    }

    export override fn asRange(capture self) -> own ArrayRange<Element> = ArrayRange(self)
    
    // TODO: equals. Due to lack of a Any::equals (and its good that this isn't present!!)
    // this needs the equals fn as a parameter. The signature would be
    // fn Array<T>.equals(self, borrow other: Array<T>, equals: (T, T) -> Bool) -> Bool
    // and could be invoked like so:
    // str1.utf8Bytes.equals(str2.utf8Bytes, U8::equals)
}

export class ArrayIndexOutOfBoundsError : Error {
    export invalidIndex: UWord = init
    
    export nothrow constructor {
        mixin ThrowableTrait(null)
    }
}

private SPACE_CODEPOINT: S8 = 32
private MINUS_SIGN_CODEPOINT: S8 = 45
private DIGIT_CODEPOINTS_FOR_TO_STRING: Array<S8> = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102]