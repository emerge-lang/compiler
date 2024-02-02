package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType

internal class TypeinfoType(
    context: LlvmContext,
) : LlvmStructType(context, "typeinfo") {
    val shiftRightAmount by structMemberRaw { wordTypeRaw }
    val supertypes by structMember {
        LlvmPointerType(
            ValueArrayType(
                LlvmPointerType(this@TypeinfoType),
                this@TypeinfoType.name,
            )
        )
    }
    val vtableBlob by structMember { LlvmArrayType(this, 0L, functionAddress) }
}