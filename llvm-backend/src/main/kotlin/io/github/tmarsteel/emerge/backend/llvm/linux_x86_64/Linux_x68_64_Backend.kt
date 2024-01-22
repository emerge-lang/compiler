package io.github.tmarsteel.emerge.backend.llvm.linux_x86_64

import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import java.nio.file.Path
import java.nio.file.Paths

class Linux_x68_64_Backend : EmergeBackend {
    override val targetName = "linux-x86_64"

    override val targetSpecificModules: Collection<ModuleSourceRef> = setOf(
        ModuleSourceRef(FFI_C_SOURCES_PATH, PackageName(listOf("emerge", "ffi", "c"))),
        ModuleSourceRef(LINUX_LIBC_SOURCES_PATH, PackageName(listOf("emerge", "linux", "libc"))),
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        TODO("Not yet implemented")
    }

    companion object {
        val FFI_C_SOURCES_PATH by systemProperty("emerge.compiler.native.c-ffi-sources", Paths::get)
        val LINUX_LIBC_SOURCES_PATH by systemProperty("emerge.compiler.native.libc-wrapper.sources", Paths::get)
    }
}