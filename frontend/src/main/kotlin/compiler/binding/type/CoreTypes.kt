package compiler.binding.type

import java.math.BigDecimal
import java.math.BigInteger

object CoreTypes {
    val F32_RANGE: ClosedRange<BigDecimal> = BigDecimal.valueOf(Float.MIN_VALUE.toDouble()) .. BigDecimal.valueOf(Float.MAX_VALUE.toDouble())
    val S8_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(Byte.MIN_VALUE.toLong()) .. BigInteger.valueOf(Byte.MAX_VALUE.toLong())
    val U8_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(UByte.MIN_VALUE.toLong()) .. BigInteger.valueOf(UByte.MAX_VALUE.toLong())
    val S16_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(Short.MIN_VALUE.toLong()) .. BigInteger.valueOf(Short.MAX_VALUE.toLong())
    val U16_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(UShort.MIN_VALUE.toLong()) .. BigInteger.valueOf(UShort.MAX_VALUE.toLong())
    val S32_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(Int.MIN_VALUE.toLong()) .. BigInteger.valueOf(Int.MAX_VALUE.toLong())
    val U32_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(UInt.MIN_VALUE.toLong()) .. BigInteger.valueOf(UInt.MAX_VALUE.toLong())
    val S64_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(Long.MIN_VALUE) .. BigInteger.valueOf(Long.MAX_VALUE)
    val U64_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(ULong.MIN_VALUE.toLong()) .. BigInteger.valueOf(ULong.MAX_VALUE.toLong())
    val SWORD_SAFE_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(Int.MIN_VALUE.toLong()) .. BigInteger.valueOf(Int.MAX_VALUE.toLong())
    val UWORD_SAFE_RANGE: ClosedRange<BigInteger> = BigInteger.valueOf(UInt.MIN_VALUE.toLong()) .. BigInteger.valueOf(UInt.MAX_VALUE.toLong())
}