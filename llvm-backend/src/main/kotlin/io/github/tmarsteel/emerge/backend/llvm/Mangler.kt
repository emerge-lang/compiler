package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendPackageName
import io.github.tmarsteel.emerge.backend.llvm.Mangler.Context.Companion.appendTypeName
import io.github.tmarsteel.emerge.backend.llvm.codegen.findSimpleTypeBound

object Mangler {
    fun computeMangledNameFor(function: IrFunction): String {
        val context = Context()
        val builder = StringBuilder()
        if (function is IrMemberFunction) {
            builder.append(SIGIL_MEMBER_FUNCTION)
        } else {
            builder.append(SIGIL_TOPLEVEL_FUNCTION)
        }

        val parentName = function.canonicalName.parent
        val parentPackageName = when (parentName) {
            is CanonicalElementName.BaseType -> parentName.packageName
            is CanonicalElementName.Package -> parentName
            else -> throw CodeGenerationException("this should never happen")
        }

        builder.appendPackageName(context, parentPackageName)
        builder.appendLengthDelimitedText(function.canonicalName.simpleName)
        for (parameter in function.parameters) {
            builder.appendTypeName(context, parameter.type.findSimpleTypeBound().baseType.canonicalName)
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

    private class Context {
        /* can probably be optimized by using a tree instead of the map+linear search, but doing that on
           the first iteration would be premature IMO
         */
        private val knownPackageNames = HashMap<CanonicalElementName.Package, UInt>()
        init {
            knownPackageNames[CanonicalElementName.Package(listOf("emerge", "core"))] = 0u
            knownPackageNames[CanonicalElementName.Package(listOf("emerge", "std"))] = 1u
        }

        private val knownTypeNames = HashMap<CanonicalElementName.BaseType, UInt>()

        companion object {
            private val SIGIL_NEW_PACKAGE_NAME = 'N'
            private val SIGIL_PACKAGE_NAME_REFERENCE = 'R'
            private val SIGIL_NEW_PACKAGE_NAME_WITH_REFERENCE_PREFIX = 'W'
            private val SIGIL_NEW_TYPE_NAME = SIGIL_NEW_PACKAGE_NAME
            private val SIGIL_TYPE_NAME_REFERENCE = SIGIL_PACKAGE_NAME_REFERENCE

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

            fun StringBuilder.appendTypeName(context: Context, name: CanonicalElementName.BaseType) {
                val existingTypeValue = context.knownTypeNames[name]
                if (existingTypeValue != null) {
                    append(SIGIL_TYPE_NAME_REFERENCE)
                    appendEncodedNumber(existingTypeValue)
                    return
                }

                append(SIGIL_NEW_TYPE_NAME)
                appendPackageName(context, name.packageName)
                appendLengthDelimitedText(name.simpleName)
            }
        }
    }

    private val SIGIL_TOPLEVEL_FUNCTION = 'T'
    private val SIGIL_MEMBER_FUNCTION = 'M'
}