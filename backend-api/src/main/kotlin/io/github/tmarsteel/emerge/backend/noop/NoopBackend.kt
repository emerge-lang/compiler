package io.github.tmarsteel.emerge.backend.noop

import io.github.tmarsteel.emerge.backend.SystemPropertyDelegate
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import java.nio.file.Path
import java.nio.file.Paths

class NoopBackend : EmergeBackend {
    override val targetName = "noop"

    override val targetSpecificModules: Collection<ModuleSourceRef> = listOf(
        ModuleSourceRef(SRC_DIR, CanonicalElementName.Package(listOf("emerge", "platform")))
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {

    }

    companion object {
        val SRC_DIR: Path by SystemPropertyDelegate.Companion.systemProperty(
            "emerge.backend.noop.platform.sources",
            Paths::get
        )
    }
}