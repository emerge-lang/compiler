package io.github.tmarsteel.emerge.backend.llvm.linux_x86_64

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.packagesSeq
import org.bytedeco.javacpp.BytePointer
import org.bytedeco.llvm.global.LLVM
import java.nio.file.Path
import java.nio.file.Paths

class Linux_x68_64_Backend : EmergeBackend {
    override val targetName = "linux-x86_64"

    override val targetSpecificModules: Collection<ModuleSourceRef> = setOf(
        ModuleSourceRef(FFI_C_SOURCES_PATH, DotName(listOf("emerge", "ffi", "c"))),
        ModuleSourceRef(LINUX_LIBC_SOURCES_PATH, DotName(listOf("emerge", "linux", "libc"))),
        ModuleSourceRef(LINUX_PLATFORM_PATH, DotName(listOf("emerge", "platform"))),
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        LLVM.LLVMInitializeAllTargetInfos()
        LLVM.LLVMInitializeAllTargets()
        LLVM.LLVMInitializeAllTargetMCs()
        LLVM.LLVMInitializeAllAsmPrinters()
        LLVM.LLVMInitializeAllAsmParsers()

        EmergeLlvmContext.createDoAndDispose(LlvmTarget.fromTriple("x86_64-pc-linux-unknown")) { llvmContext ->
            softwareContext.packagesSeq.forEach { pkg ->
                pkg.structs.forEach(llvmContext::registerStruct)
            }
            softwareContext.modules.flatMap { it.packages }.forEach { pkg ->
                pkg.functions
                    .flatMap { it.overloads }
                    .forEach {
                        val fn = llvmContext.registerFunction(it)
                        if (it.fqn == allocatorFunctionName) {
                            @Suppress("UNCHECKED_CAST")
                            llvmContext.allocateFunction = fn as LlvmFunction<LlvmPointerType<LlvmVoidType>>
                        }
                        if (it.fqn == freeFunctionName) {
                            @Suppress("UNCHECKED_CAST")
                            llvmContext.freeFunction = fn as LlvmFunction<LlvmVoidType>
                        }
                    }
            }
            softwareContext.modules.flatMap { it.packages }
                .flatMap { it.variables }
                .forEach {
                    llvmContext.registerGlobal(it.declaration)
                }
            softwareContext.modules.flatMap { it.packages }
                .flatMap { it.variables }
                .forEach {
                    llvmContext.defineGlobalInitializer(it.declaration, it.initializer)
                }
            softwareContext.modules.flatMap { it.packages }.forEach { pkg ->
                pkg.functions
                    .flatMap { it.overloads }
                    .filterIsInstance<IrImplementedFunction>()
                    .forEach(llvmContext::defineFunctionBody)
            }

            llvmContext.complete()

            val errorMessage = BytePointer(2048)
            val errorCode = LLVM.LLVMPrintModuleToFile(
                llvmContext.module,
                directory.resolve("out.ll").toAbsolutePath().toString(),
                errorMessage,
            )
            if (errorCode != 0) {
                val message = errorMessage.string
                LLVM.LLVMDisposeMessage(errorMessage)
                throw CodeGenerationException(message)
            }
        }
    }

    companion object {
        val FFI_C_SOURCES_PATH by systemProperty("emerge.compiler.native.c-ffi-sources", Paths::get)
        val LINUX_LIBC_SOURCES_PATH by systemProperty("emerge.compiler.native.libc-wrapper.sources", Paths::get)
        val LINUX_PLATFORM_PATH by systemProperty("emerge.compiler.native.linux-platform.sources", Paths::get)

        private val allocatorFunctionName = DotName(listOf("emerge", "linux", "libc", "malloc"))
        private val freeFunctionName = DotName(listOf("emerge", "linux", "libc", "free"))
    }
}

