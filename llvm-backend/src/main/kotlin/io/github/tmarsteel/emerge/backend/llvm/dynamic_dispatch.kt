package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.*
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.common.EmergeConstants

internal var IrMemberFunction.llvmFunctionType: LlvmFunctionType<*> by tackLateInitState()

internal var IrMemberFunction.rootSignatureHash: ULong by tackLateInitState()

/**
 * Sets [rootSignatureHash] for all non-inherited virtual functions on interfaces, and the virtual functions on `emerge.core.Array`.
 * This needs the entire application context so clashes between interfaces used on the same class can be avoided reliably.
 *
 * After this method has run, all the [IrMemberFunction] from that [IrSoftwareContext] will have [signatureHashes]
 * available.
 */
internal fun IrSoftwareContext.assignVirtualFunctionHashes() {
    val interfacePooler = Pooler<IrInterface>()
    this.modules
        .flatMap { it.packages }
        .flatMap { it.classes }
        .map { it.allDistinctSupertypesExceptAny }
        .forEach(interfacePooler::mustBeInSamePool)

    interfacePooler.pools.forEach { interfacePool ->
        interfacePool
            .flatMap { it.memberFunctions }
            .flatMap { it.overloads }
            .filter { it.overrides.isEmpty() }
            .forEachIndexed { index, memberFn ->
                var hash = memberFn.canonicalName.simpleName.hashCode().toULong()
                for (param in memberFn.parameters) {
                    hash = 31u * hash + param.type.toStringForSignature().hashCode().toULong()
                }

                memberFn.rootSignatureHash = (hash shl 32) or (index.toULong())
            }
    }

    // array special case
    this.modules
        .flatMap { it.packages }
        .single { it.name == EmergeConstants.CORE_MODULE_NAME }
        .classes
        .single { it.canonicalName.simpleName == "Array" }
        .memberFunctions
        .flatMap { it.overloads }
        .forEach { arrayMemberFn ->
            if (arrayMemberFn.canonicalName.simpleName == "get" && arrayMemberFn.parameters.size == 2) {
                arrayMemberFn.rootSignatureHash = EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT_FALLIBLE
            }
            if (arrayMemberFn.canonicalName.simpleName == "set" && arrayMemberFn.parameters.size == 3) {
                arrayMemberFn.rootSignatureHash = EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT_FALLIBLE
            }
            if (arrayMemberFn.canonicalName.simpleName == "getOrPanic" && arrayMemberFn.parameters.size == 2) {
                arrayMemberFn.rootSignatureHash = EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT_PANIC
            }
            if (arrayMemberFn.canonicalName.simpleName == "setOrPanic" && arrayMemberFn.parameters.size == 3) {
                arrayMemberFn.rootSignatureHash = EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT_PANIC
            }
        }
}


internal val IrMemberFunction.signatureHashes: Set<ULong> by tackLazyVal {
    when {
        this is IrFullyInheritedMemberFunction -> superFunction.signatureHashes
        overrides.isEmpty() -> setOf(rootSignatureHash)
        else -> overrides.flatMap { it.signatureHashes }.toSet()
    }
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