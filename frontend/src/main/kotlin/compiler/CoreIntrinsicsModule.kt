package compiler

import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFile
import compiler.binding.context.SourceFileRootContext
import compiler.binding.type.BuiltinAny
import compiler.binding.type.BuiltinArray
import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.BuiltinByte
import compiler.binding.type.BuiltinFloat
import compiler.binding.type.BuiltinInt
import compiler.binding.type.BuiltinLong
import compiler.binding.type.BuiltinNothing
import compiler.binding.type.BuiltinNumber
import compiler.binding.type.BuiltinShort
import compiler.binding.type.BuiltinSignedWord
import compiler.binding.type.BuiltinUByte
import compiler.binding.type.BuiltinUInt
import compiler.binding.type.BuiltinULong
import compiler.binding.type.BuiltinUShort
import compiler.binding.type.BuiltinUnsignedWord
import io.github.tmarsteel.emerge.backend.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.api.PackageName
import java.nio.file.Paths

/**
 * The very core module of the language, defining intrinsic elements that are implemented by the
 * compiler/backends, rather than source code from the standard library.
 */
object CoreIntrinsicsModule {
    fun amendCoreModuleIn(softwareContext: SoftwareContext) {
        val coreModule = softwareContext.getRegisteredModule(NAME)
        val fileContext = SourceFileRootContext(softwareContext.getPackage(NAME)!!)
        val file = SourceFile(compiler.lexer.MemorySourceFile(CoreIntrinsicsModule::class.simpleName!!, NAME, ""), NAME, fileContext)

        file.context.addBaseType(BuiltinAny)
        file.context.addBaseType(BuiltinNumber)
        file.context.addBaseType(BuiltinFloat)
        file.context.addBaseType(BuiltinByte)
        file.context.addBaseType(BuiltinUByte)
        file.context.addBaseType(BuiltinShort)
        file.context.addBaseType(BuiltinUShort)
        file.context.addBaseType(BuiltinInt)
        file.context.addBaseType(BuiltinUInt)
        file.context.addBaseType(BuiltinLong)
        file.context.addBaseType(BuiltinULong)
        file.context.addBaseType(BuiltinSignedWord)
        file.context.addBaseType(BuiltinUnsignedWord)
        file.context.addBaseType(BuiltinBoolean)
        file.context.addBaseType(BuiltinArray(softwareContext))
        file.context.addBaseType(BuiltinNothing)

        coreModule.addSourceFile(file)
    }

    val NAME = PackageName(listOf("emerge", "core"))
    val SRC_DIR by systemProperty("emerge.frontend.core.sources", Paths::get)
}