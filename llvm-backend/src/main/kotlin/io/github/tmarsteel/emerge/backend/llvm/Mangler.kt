package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrConstructor
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrIntersectionType
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendNonReferenceBaseType
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendPackageName
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendType
import io.github.tmarsteel.emerge.common.CanonicalElementName

object Mangler {
    fun computeMangledNameFor(function: IrFunction): String {
        val context = Context()
        val builder = StringBuilder()
        builder.append(EMERGE_PREFIX)
        when (function) {
            is IrBaseTypeFunction -> {
                builder.append(if (function is IrConstructor) SIGIL_CONSTRUCTOR else SIGIL_MEMBER_FUNCTION)
                builder.appendNonReferenceBaseType(context, function.ownerBaseType)
            }

            else -> {
                builder.append(SIGIL_TOPLEVEL_FUNCTION)
                val packageName = when (val parentName = function.canonicalName.parent) {
                    is CanonicalElementName.BaseType -> parentName.packageName
                    is CanonicalElementName.Package -> parentName
                    else -> throw CodeGenerationException("this should never happen")
                }

                builder.appendPackageName(context, packageName)
            }
        }

        if (function !is IrConstructor) {
            builder.appendLengthDelimitedText(function.canonicalName.simpleName)
            for (parameter in function.parameters) {
                builder.appendType(context, parameter.type, null)
            }
        }

        return builder.toString()
    }

    private fun StringBuilder.appendLengthDelimitedText(text: String) {
        // 0-length names are not a thing, so we can also save one number symbol
        check(text.isNotEmpty())
        appendEncodedNumber(text.length.toUInt() - 1u)
        append(text)
    }

    private fun StringBuilder.appendEncodedNumber(value: UInt) {
        val nDigits = DIGITS.size.toUInt()
        var remainingNumber = value
        do {
            val digit = DIGITS[(remainingNumber % nDigits).toInt()]
            remainingNumber /= nDigits
            if (remainingNumber > 0u) {
                append(digit)
            } else {
                append(digit.uppercase())
            }
        } while (remainingNumber > 0u)
    }

    private val DIGITS: CharArray = charArrayOf(
        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
        'w', 'x', 'y', 'z'
    )

    private const val EMERGE_PREFIX = "\$EM"

    private class Context {
        /* can probably be optimized by using a tree instead of the map+linear search, but doing that on
           the first iteration would be premature IMO
         */
        private val knownPackageNames = HashMap<CanonicalElementName.Package, UInt>()
        init {
            knownPackageNames[CanonicalElementName.Package(listOf("emerge", "core"))] = 0u
            knownPackageNames[CanonicalElementName.Package(listOf("emerge", "std"))] = 1u
            knownPackageNames[CanonicalElementName.Package(listOf("emerge", "platform"))] = 2u
        }

        private val knownBaseTypeNames = HashMap<CanonicalElementName.BaseType, UInt>()
        private val knownGenericTypeNames = HashMap<String, UInt>()

        companion object {
            private val SIGIL_NEW_PACKAGE_NAME = 'N'
            private val SIGIL_PACKAGE_NAME_REFERENCE = 'R'
            private val SIGIL_NEW_PACKAGE_NAME_WITH_REFERENCE_PREFIX = 'W'

            private fun getTypeSigil(
                isReference: Boolean,
                isGeneric: Boolean,
                variance: IrTypeVariance?,
                mutability: IrTypeMutability
            ): Char {
                val varianceCode = when (variance) {
                    IrTypeVariance.IN -> 0
                    IrTypeVariance.OUT -> 1
                    IrTypeVariance.INVARIANT -> 2
                    null -> 3
                }
                val mutabilityCode = when (mutability) {
                    IrTypeMutability.IMMUTABLE -> 0
                    IrTypeMutability.READONLY -> 1
                    IrTypeMutability.MUTABLE -> 2
                    IrTypeMutability.EXCLUSIVE -> 3
                    IrTypeMutability.READCONST -> 4
                }
                var asciiCode = 1 // prevent 0 to avoid interpretation as nullterminator
                asciiCode = asciiCode or (if (isReference) 1 else 0) shl 1
                asciiCode = asciiCode or (if (isGeneric) 1 else 0 shl 2)
                asciiCode = asciiCode or (varianceCode shl 3)
                asciiCode = asciiCode or (mutabilityCode shl 7)

                return Char(asciiCode)
            }

            fun StringBuilder.appendPackageName(context: Context, name: CanonicalElementName.Package) {
                val existingMatch = context.knownPackageNames
                    .filter { (existingName, _) ->
                        existingName.containsOrEquals(name)
                    }
                    .maxByOrNull { (existingName, _) -> existingName.components.size }

                if (existingMatch?.key?.components?.size == name.components.size) {
                    // identical
                    append(SIGIL_PACKAGE_NAME_REFERENCE)
                    appendEncodedNumber(existingMatch.value)
                    return
                }

                context.knownPackageNames[name] = context.knownPackageNames.size.toUInt()
                val nameAsString = name.toString()

                if (existingMatch == null) {
                    append(SIGIL_NEW_PACKAGE_NAME)
                    appendLengthDelimitedText(nameAsString)
                    return
                }

                val nameSuffix = nameAsString.substring(existingMatch.key.toString().length)
                append(SIGIL_NEW_PACKAGE_NAME_WITH_REFERENCE_PREFIX)
                appendEncodedNumber(existingMatch.value)
                appendLengthDelimitedText(nameSuffix)
            }

            fun StringBuilder.appendNonReferenceBaseType(context: Context, type: IrBaseType) {
                appendPackageName(context, type.canonicalName.packageName)
                appendLengthDelimitedText(type.canonicalName.simpleName)
                context.knownBaseTypeNames[type.canonicalName] = context.knownBaseTypeNames.size.toUInt()
            }

            fun StringBuilder.appendType(context: Context, type: IrType, argumentVariance: IrTypeVariance?) {
                when (type) {
                    is IrSimpleType -> {
                        val existingTypeValue = context.knownBaseTypeNames[type.baseType.canonicalName]
                        if (existingTypeValue != null) {
                            append(getTypeSigil(isReference = true, isGeneric = false, mutability = type.mutability, variance = argumentVariance))
                            appendEncodedNumber(existingTypeValue)
                        } else {
                            append(getTypeSigil(isReference = false, isGeneric = false, mutability = type.mutability, variance = argumentVariance))
                            appendNonReferenceBaseType(context, type.baseType)
                        }
                    }
                    is IrGenericTypeReference -> {
                        val asString = type.parameter.name
                        val existingTypeValue = context.knownGenericTypeNames[asString]
                        if (existingTypeValue != null) {
                            append(getTypeSigil(isReference = true, isGeneric = true, mutability = type.mutability, variance = argumentVariance))
                            appendEncodedNumber(existingTypeValue)
                        } else {
                            append(getTypeSigil(isReference = false, isGeneric = true, mutability = type.mutability, variance = argumentVariance))
                            appendLengthDelimitedText(type.parameter.name)
                            context.knownGenericTypeNames[asString] = context.knownGenericTypeNames.size.toUInt()
                        }

                    }
                    is IrParameterizedType -> {
                        appendType(context, type.simpleType, argumentVariance)
                        append('<')
                        type.arguments.entries
                            .sortedBy { (name, _) -> name }
                            .forEach { (_, argument) ->
                                appendType(context, argument.type, argument.variance)
                            }
                        append('>')
                    }
                    is IrIntersectionType -> {
                        val componentIt = type.components.iterator()
                        while (componentIt.hasNext()) {
                            appendType(context, componentIt.next(), argumentVariance)
                            if (componentIt.hasNext()) {
                                append('&')
                            }
                        }
                    }
                }
            }
        }
    }

    private val SIGIL_TOPLEVEL_FUNCTION = 'T'
    private val SIGIL_MEMBER_FUNCTION = 'M'
    private val SIGIL_CONSTRUCTOR = 'C'
}