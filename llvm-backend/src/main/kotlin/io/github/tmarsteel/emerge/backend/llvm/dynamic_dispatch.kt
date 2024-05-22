package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType

internal var IrMemberFunction.llvmFunctionType: LlvmFunctionType<*> by tackLateInitState()
internal val IrMemberFunction.rootSignatureHash: ULong by tackLazyVal {
    check(overrides.isEmpty())
    calculateSignatureHash(this)
}
internal val IrMemberFunction.signatureHashes: Set<ULong> by tackLazyVal {
    if (overrides.isEmpty()) {
        setOf(rootSignatureHash)
    } else {
        overrides.flatMap { it.signatureHashes }.toSet()
    }
}

private fun calculateSignatureHash(fn: IrMemberFunction): ULong {
    // TODO: this is totally preliminary, needs to be redone to account for ultra low collision rate (and performance?)
    var signatureString = fn.ownerBaseType.toStringForSignature()
    fn.parameters.forEach {
        signatureString += it.type.toStringForSignature()
    }
    signatureString += fn.returnType.toStringForSignature()

    val loPart = signatureString.substring(0, signatureString.length / 2)
    val hiPart = signatureString.substring(loPart.length)
    val lo = loPart.hashCode()
    val hi = hiPart.hashCode()

    return lo.toULong() or (hi.toULong() shl 32)
}

private fun IrBaseType.toStringForSignature(): String = canonicalName.toString().lengthEncode()
private fun IrType.toStringForSignature(): String = when(this) {
    is IrGenericTypeReference -> effectiveBound.toStringForSignature()
    is IrParameterizedType -> simpleType.toStringForSignature() + arguments.entries
        .sortedBy { (name, _) -> simpleType.baseType.parameters.indexOfFirst { it.name == name } }
        .joinToString(
            prefix = "<",
            transform = { (_, arg) -> arg.variance.name.lowercase() + "$" + arg.type.toStringForSignature() },
            separator = ",",
            postfix = ">"
        )
    is IrSimpleType -> baseType.toStringForSignature()
}

private fun String.lengthEncode(): String = length.toString(36).lowercase() + "$" + this

