package io.github.tmarsteel.emerge.backend.noop

import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import java.nio.file.Path
import java.nio.file.Paths

class NoopBackend : EmergeBackend {
    override val targetName = "noop"

    override val targetSpecificModules: Collection<ModuleSourceRef> = listOf(
        ModuleSourceRef(SRC_DIR, PackageName(listOf("emerge", "platform")))
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        
    }

    companion object {
        val SRC_DIR: Path by systemProperty("emerge.backend.noop.platform.sources", Paths::get)
    }
}