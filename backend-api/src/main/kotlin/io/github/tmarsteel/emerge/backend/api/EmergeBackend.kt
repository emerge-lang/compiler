package io.github.tmarsteel.emerge.backend.api

import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import java.nio.file.Path

interface EmergeBackend {
    /**
     * The target that this backend compiles, e.g. unix-x86_64
     */
    val targetName: String

    /**
     * Additional modules that must be considered by the frontend for code to be compiled to this target
     */
    val targetSpecificModules: Collection<ModuleSourceRef>
        get() = emptySet()

    /**
     * Generates all the code necessary for this software into [directory]. The backend implementation can further
     * structure this directory as needed / wanted.
     */
    @Throws(CodeGenerationException::class)
    fun emit(softwareContext: IrSoftwareContext, directory: Path)
}