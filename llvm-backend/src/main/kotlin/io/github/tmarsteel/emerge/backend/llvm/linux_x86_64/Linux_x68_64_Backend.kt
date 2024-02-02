package io.github.tmarsteel.emerge.backend.llvm.linux_x86_64

import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.packagesSeq
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM
import java.nio.channels.AsynchronousFileChannel
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardOpenOption

class Linux_x68_64_Backend : EmergeBackend {
    override val targetName = "linux-x86_64"

    override val targetSpecificModules: Collection<ModuleSourceRef> = setOf(
        ModuleSourceRef(FFI_C_SOURCES_PATH, DotName(listOf("emerge", "ffi", "c"))),
        ModuleSourceRef(LINUX_LIBC_SOURCES_PATH, DotName(listOf("emerge", "linux", "libc"))),
        ModuleSourceRef(LINUX_PLATFORM_PATH, DotName(listOf("emerge", "platform"))),
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        LLVM.LLVMInitializeX86Target()
        LLVM.LLVMInitializeX86TargetInfo()

        EmergeLlvmContext.createDoAndDispose("x86_64-pc-linux-unknown") { llvmContext ->
            softwareContext.packagesSeq.forEach { pkg ->
                pkg.structs.forEach(llvmContext::registerStruct)
            }
            softwareContext.modules.flatMap { it.packages }.forEach { pkg ->
                pkg.functions.flatMap { it.overloads }.forEach { function ->
                    val functionType = LLVM.LLVMFunctionType(
                        llvmContext.getType(function.returnType),
                        PointerPointer(*function.parameters.map { llvmContext.getType(it.type) }.toTypedArray()),
                        function.parameters.size,
                        0,
                    )
                    LLVM.LLVMAddFunction(llvmContext.module, function.llvmName, functionType)
                }
            }
            LLVM.LLVMDumpModule(llvmContext.module)
            LLVM.LLVMPrintModuleToString(llvmContext.module).let { moduleBytes ->
                AsynchronousFileChannel.open(directory.resolve("out.bin"), StandardOpenOption.CREATE, StandardOpenOption.WRITE).use {
                    it.write(moduleBytes.asBuffer(), 0L).get()
                }
                LLVM.LLVMDisposeMessage(moduleBytes)
            }
        }
    }

    companion object {
        val FFI_C_SOURCES_PATH by systemProperty("emerge.compiler.native.c-ffi-sources", Paths::get)
        val LINUX_LIBC_SOURCES_PATH by systemProperty("emerge.compiler.native.libc-wrapper.sources", Paths::get)
        val LINUX_PLATFORM_PATH by systemProperty("emerge.compiler.native.linux-platform.sources", Paths::get)
    }
}

