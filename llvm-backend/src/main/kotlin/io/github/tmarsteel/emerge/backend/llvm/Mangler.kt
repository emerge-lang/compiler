package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrConstructor
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendNonReferenceBaseType
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendPackageName
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendType

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
        appendEncodedNumber(text.length.toUInt())
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
                return when (isReference) {
                    true -> when (isGeneric) {
                        true -> when (variance) {
                            IrTypeVariance.IN -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'a'
                                IrTypeMutability.READONLY  -> 'b'
                                IrTypeMutability.MUTABLE -> 'c'
                                IrTypeMutability.EXCLUSIVE -> 'd'
                            }
                            IrTypeVariance.OUT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'e'
                                IrTypeMutability.READONLY  -> 'f'
                                IrTypeMutability.MUTABLE -> 'g'
                                IrTypeMutability.EXCLUSIVE -> 'h'
                            }
                            IrTypeVariance.INVARIANT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'i'
                                IrTypeMutability.READONLY  -> 'j'
                                IrTypeMutability.MUTABLE -> 'k'
                                IrTypeMutability.EXCLUSIVE -> 'l'
                            }
                            null -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'm'
                                IrTypeMutability.READONLY  -> 'n'
                                IrTypeMutability.MUTABLE -> 'o'
                                IrTypeMutability.EXCLUSIVE -> 'p'
                            }
                        }
                        false -> when (variance) {
                            IrTypeVariance.IN -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'q'
                                IrTypeMutability.READONLY  -> 'r'
                                IrTypeMutability.MUTABLE -> 's'
                                IrTypeMutability.EXCLUSIVE -> 't'
                            }
                            IrTypeVariance.OUT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'u'
                                IrTypeMutability.READONLY  -> 'v'
                                IrTypeMutability.MUTABLE -> 'w'
                                IrTypeMutability.EXCLUSIVE -> 'x'
                            }
                            IrTypeVariance.INVARIANT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'y'
                                IrTypeMutability.READONLY  -> 'z'
                                IrTypeMutability.MUTABLE -> '0'
                                IrTypeMutability.EXCLUSIVE -> '1'
                            }
                            null -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> '2'
                                IrTypeMutability.READONLY  -> '3'
                                IrTypeMutability.MUTABLE -> '4'
                                IrTypeMutability.EXCLUSIVE -> '5'
                            }
                        }
                    }
                    false -> when (isGeneric) {
                        true -> when (variance) {
                            IrTypeVariance.IN -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'A'
                                IrTypeMutability.READONLY  -> 'B'
                                IrTypeMutability.MUTABLE -> 'C'
                                IrTypeMutability.EXCLUSIVE -> 'D'
                            }
                            IrTypeVariance.OUT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'E'
                                IrTypeMutability.READONLY  -> 'F'
                                IrTypeMutability.MUTABLE -> 'G'
                                IrTypeMutability.EXCLUSIVE -> 'H'
                            }
                            IrTypeVariance.INVARIANT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'I'
                                IrTypeMutability.READONLY  -> 'J'
                                IrTypeMutability.MUTABLE -> 'K'
                                IrTypeMutability.EXCLUSIVE -> 'L'
                            }
                            null -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'M'
                                IrTypeMutability.READONLY  -> 'N'
                                IrTypeMutability.MUTABLE -> 'O'
                                IrTypeMutability.EXCLUSIVE -> 'P'
                            }
                        }
                        false -> when (variance) {
                            IrTypeVariance.IN -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'Q'
                                IrTypeMutability.READONLY  -> 'R'
                                IrTypeMutability.MUTABLE -> 'S'
                                IrTypeMutability.EXCLUSIVE -> 'T'
                            }
                            IrTypeVariance.OUT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'U'
                                IrTypeMutability.READONLY  -> 'V'
                                IrTypeMutability.MUTABLE -> 'W'
                                IrTypeMutability.EXCLUSIVE -> 'X'
                            }
                            IrTypeVariance.INVARIANT -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> 'Y'
                                IrTypeMutability.READONLY  -> 'Z'
                                IrTypeMutability.MUTABLE -> '6'
                                IrTypeMutability.EXCLUSIVE -> '7'
                            }
                            null -> when(mutability) {
                                IrTypeMutability.IMMUTABLE -> '8'
                                IrTypeMutability.READONLY  -> '9'
                                IrTypeMutability.MUTABLE -> '.'
                                IrTypeMutability.EXCLUSIVE -> '_'
                            }
                        }
                    }
                }
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
                }
            }
        }
    }

    private val SIGIL_TOPLEVEL_FUNCTION = 'T'
    private val SIGIL_MEMBER_FUNCTION = 'M'
    private val SIGIL_CONSTRUCTOR = 'C'
}