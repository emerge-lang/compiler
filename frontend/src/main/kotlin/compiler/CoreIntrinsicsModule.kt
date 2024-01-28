package compiler

import compiler.ast.ASTSourceFile
import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFile
import compiler.binding.context.SourceFileRootContext
import compiler.binding.type.BuiltinAny
import compiler.binding.type.BuiltinArray
import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.BuiltinByte
import compiler.binding.type.BuiltinFloat
import compiler.binding.type.BuiltinInt
import compiler.binding.type.BuiltinNothing
import compiler.binding.type.BuiltinNumber
import compiler.binding.type.BuiltinSignedWord
import compiler.binding.type.BuiltinUnit
import compiler.binding.type.BuiltinUnsignedWord
import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import java.nio.file.Paths

/**
 * The very core module of the language, defining intrinsic elements that are implemented by the
 * compiler/backends, rather than source code from the standard library.
 */
object CoreIntrinsicsModule {
    fun amendCoreModuleIn(softwareContext: SoftwareContext) {
        val coreModule = softwareContext.getRegisteredModule(NAME)
        val fileContext = SourceFileRootContext(softwareContext.getPackage(NAME)!!)
        val file = SourceFile(NAME, fileContext)

        file.context.addBaseType(BuiltinAny)
        file.context.addBaseType(BuiltinUnit)
        file.context.addBaseType(BuiltinNumber)
        file.context.addBaseType(BuiltinFloat)
        file.context.addBaseType(BuiltinInt)
        file.context.addBaseType(BuiltinBoolean)
        file.context.addBaseType(BuiltinArray(softwareContext))
        file.context.addBaseType(BuiltinNothing)
        file.context.addBaseType(BuiltinByte)
        file.context.addBaseType(BuiltinSignedWord)
        file.context.addBaseType(BuiltinUnsignedWord)

        coreModule.addSourceFile(file)
    }

    val NAME = PackageName(listOf("emerge", "core"))
    /* TODO: evaluate need for this */
    val NAME_STRING = NAME.toString()

    val SRC_DIR by systemProperty("emerge.frontend.core.sources", Paths::get)
}