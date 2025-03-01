package compiler.compiler.binding.expression

import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundIntegerLiteral
import compiler.binding.type.CoreTypes
import compiler.compiler.negative.FailTestOnFindingDiagnosis
import compiler.lexer.Span
import io.kotest.core.spec.style.FreeSpec
import io.mockk.Runs
import io.mockk.every
import io.mockk.just
import io.mockk.mockk
import java.math.BigInteger
import kotlin.random.Random

class BoundIntegerLiteralTest : FreeSpec({
    val mockCtx = mockk<ExecutionScopedCTContext> {
        every { swCtx } returns mockk {
            every { s8 } returns mockNumericBaseType(8, 'S')
            every { u8 } returns mockNumericBaseType(8, 'U')
            every { s16 } returns mockNumericBaseType(16, 'S')
            every { u16 } returns mockNumericBaseType(16, 'U')
            every { s32 } returns mockNumericBaseType(32, 'S')
            every { u32 } returns mockNumericBaseType(32, 'U')
            every { s64 } returns mockNumericBaseType(64, 'S')
            every { u64 } returns mockNumericBaseType(64, 'U')
            every { sword } returns mockk()
            every { uword } returns mockk()
        }
    }
    val signedRanges = listOf(CoreTypes.S8_RANGE, CoreTypes.S16_RANGE, CoreTypes.S32_RANGE, CoreTypes.S64_RANGE)
    val unsignedRanges = listOf(CoreTypes.U8_RANGE, CoreTypes.U16_RANGE, CoreTypes.U32_RANGE, CoreTypes.U64_RANGE)
    check(CoreTypes.SWORD_SAFE_RANGE in signedRanges && CoreTypes.UWORD_SAFE_RANGE in unsignedRanges)
    val signedBaseTypes = listOf(mockCtx.swCtx.s8, mockCtx.swCtx.s16, mockCtx.swCtx.s32, mockCtx.swCtx.s64)

    "accepts bit-length-wise fitting numbers" - {
        for (base in listOf(2u, 16u)) {
            for ((signedRange, unsignedRange, baseType) in signedRanges.tripleZip(unsignedRanges, signedBaseTypes)) {
                "type S${unsignedRange.endInclusive.bitLength()}, source base $base" {
                    val rangeToTest = (signedRange.endInclusive + BigInteger.ONE) .. unsignedRange.endInclusive
                    for (largeFittingValue in rangeToTest.randomSample()) {
                        val boundNode = BoundIntegerLiteral(
                            mockCtx,
                            mockk {
                                every { span } returns Span.UNKNOWN
                            },
                            largeFittingValue,
                            base,
                            emptySet(),
                        )
                        boundNode.semanticAnalysisPhase1(FailTestOnFindingDiagnosis)
                        boundNode.setExpectedEvaluationResultType(baseType.baseReference)
                        boundNode.semanticAnalysisPhase2(FailTestOnFindingDiagnosis)
                        boundNode.semanticAnalysisPhase3(FailTestOnFindingDiagnosis)
                    }
                }
            }
        }
    }
})

private fun ClosedRange<BigInteger>.randomSample(): Sequence<BigInteger> = sequence {
    check(start >= BigInteger.ZERO && endInclusive > BigInteger.ZERO)
    val yielded = mutableSetOf<BigInteger>(start)
    yield(start)
    while (yielded.size < 30) {
        val next = BigInteger(1, Random.nextBytes(endInclusive.bitLength() / 8))
        if (next in this@randomSample && yielded.add(next)) {
            yield(next)
        }
    }
    if (yielded.add(endInclusive)) {
        yield(endInclusive)
    }
}

private fun <A, B, C> List<A>.tripleZip(bs: List<B>, cs: List<C>): Sequence<Triple<A, B, C>> = sequence {
    val aIt = this@tripleZip.iterator()
    val bIt = bs.iterator()
    val cIt = cs.iterator()

    while (aIt.hasNext() && bIt.hasNext() && cIt.hasNext()) {
        yield(Triple(aIt.next(), bIt.next(), cIt.next()))
    }
}

private fun mockNumericBaseType(nBits: Int, prefix: Char): BoundBaseType {
    return mockk {
        every { semanticAnalysisPhase1(any()) } just Runs
        every { semanticAnalysisPhase2(any()) } just Runs
        every { semanticAnalysisPhase3(any()) } just Runs
        every { isCoreScalar } returns true
        every { isCoreNumericType } returns true
        every { simpleName } returns prefix.toString() + nBits.toString()
        every { typeParameters } returns null
        every { baseReference } answers { callOriginal() }
    }
}