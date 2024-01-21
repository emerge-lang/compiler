package io.github.tmarsteel.emerge.backend.noop

import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import java.nio.file.Path

class NoopBackend : EmergeBackend {
    override val targetName = "noop"

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        
    }
}