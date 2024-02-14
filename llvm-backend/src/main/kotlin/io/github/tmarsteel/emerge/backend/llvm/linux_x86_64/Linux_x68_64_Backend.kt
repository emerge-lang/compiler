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
import io.github.tmarsteel.emerge.backend.llvm.dsl.PassBuilderOptions
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.linux.EmergeEntrypoint
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
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
        val objectFilePath = directory.resolve("out.o").toAbsolutePath()
        writeSoftwareToObjectFile(softwareContext, objectFilePath)

        val executablePath = directory.resolve("runnable").toAbsolutePath()
        createExecutableFromObjectFile(objectFilePath, executablePath)
    }

    private fun writeSoftwareToObjectFile(softwareContext: IrSoftwareContext, objectFilePath: Path) {
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
                        storeCoreFunctionReference(llvmContext, it.fqn, fn)
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

            // assure the entrypoint is in the object file
            EmergeEntrypoint.getInContext(llvmContext)

            val errorMessageBuffer = BytePointer(1024 * 10)

            errorMessageBuffer.position(0)
            errorMessageBuffer.limit(errorMessageBuffer.capacity())
            if (LLVM.LLVMPrintModuleToFile(
                llvmContext.module,
                objectFilePath.parent.resolve("out.ll").toString(),
                errorMessageBuffer,
            ) != 0) {
                // null-terminated, this makes the .getString() function behave correctly
                errorMessageBuffer.limit(0)
                throw CodeGenerationException(errorMessageBuffer.string)
            }

            errorMessageBuffer.position(0)
            errorMessageBuffer.limit(errorMessageBuffer.capacity())
            if (LLVM.LLVMVerifyModule(llvmContext.module, LLVM.LLVMReturnStatusAction, errorMessageBuffer) != 0) {
                // null-terminated, this makes the .getString() function behave correctly
                errorMessageBuffer.limit(0)
                throw CodeGenerationException(errorMessageBuffer.string)
            }

            PassBuilderOptions().use { pbo ->
                LLVM.LLVMRunPasses(
                    llvmContext.module,
                    null as String?,
                    llvmContext.targetMachine.ref,
                    pbo.ref,
                )
            }

            errorMessageBuffer.position(0)
            errorMessageBuffer.limit(errorMessageBuffer.capacity())
            if (LLVM.LLVMTargetMachineEmitToFile(
                    llvmContext.targetMachine.ref,
                    llvmContext.module,
                    objectFilePath.parent.resolve("out.s").toString(),
                    LLVM.LLVMAssemblyFile,
                    errorMessageBuffer,
                ) != 0) {
                // null-terminated, this makes the .getString() function behave correctly
                errorMessageBuffer.limit(0)
                throw CodeGenerationException(errorMessageBuffer.string)
            }

            errorMessageBuffer.position(0)
            errorMessageBuffer.limit(errorMessageBuffer.capacity())
            if (LLVM.LLVMTargetMachineEmitToFile(
                llvmContext.targetMachine.ref,
                llvmContext.module,
                objectFilePath.toString(),
                LLVM.LLVMObjectFile,
                errorMessageBuffer,
            ) != 0) {
                // null-terminated, this makes the .getString() function behave correctly
                errorMessageBuffer.limit(0)
                throw CodeGenerationException(errorMessageBuffer.string)
            }
        }
    }

    private fun createExecutableFromObjectFile(objectFilePath: Path, executablePath: Path) {

    }

    private fun findMainFunction(softwareContext: IrSoftwareContext): LlvmFunction<*> {
        return softwareContext.modules
            .flatMap { it.packages }
            .flatMap { it.functions }
            .flatMap { it.overloads }
            .single { it.fqn.last == "main" }
            .llvmRef!!
    }

    private fun storeCoreFunctionReference(context: EmergeLlvmContext, functionName: DotName, fn: LlvmFunction<*>) {
        when (functionName) {
            ALLOCATOR_FUNCTION_NAME -> {
                @Suppress("UNCHECKED_CAST")
                context.allocateFunction = fn as LlvmFunction<LlvmPointerType<LlvmVoidType>>
            }
            FREE_FUNCTION_NAME -> {
                @Suppress("UNCHECKED_CAST")
                context.freeFunction = fn as LlvmFunction<LlvmVoidType>
            }
            EXIT_FUNCTION_NAME -> {
                @Suppress("UNCHECKED_CAST")
                context.exitFunction = fn as LlvmFunction<LlvmVoidType>
            }
        }
    }

    companion object {
        val FFI_C_SOURCES_PATH by systemProperty("emerge.compiler.native.c-ffi-sources", Paths::get)
        val LINUX_LIBC_SOURCES_PATH by systemProperty("emerge.compiler.native.libc-wrapper.sources", Paths::get)
        val LINUX_PLATFORM_PATH by systemProperty("emerge.compiler.native.linux-platform.sources", Paths::get)

        private val ALLOCATOR_FUNCTION_NAME = DotName(listOf("emerge", "linux", "libc", "malloc"))
        private val FREE_FUNCTION_NAME = DotName(listOf("emerge", "linux", "libc", "free"))
        private val EXIT_FUNCTION_NAME = DotName(listOf("emerge", "linux", "libc", "exit"))
    }
}

