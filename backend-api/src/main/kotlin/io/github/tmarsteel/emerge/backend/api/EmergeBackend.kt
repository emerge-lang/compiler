package io.github.tmarsteel.emerge.backend.api

import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition
import kotlin.reflect.KClass

/**
 * @param ToolchainConfig a class describing the toolchain-level configuration for this backend. This is information
 * that varies as per the computer the compiler is running on.
 * @param ProjectConfig a class describing the project-level configuration for this backend.
 */
interface EmergeBackend<ToolchainConfig : Any, ProjectConfig : Any> {
    /**
     * The target that this backend compiles, e.g. x86_64-pc-linux-gnu
     */
    val targetName: String

    val toolchainConfigKClass: KClass<ToolchainConfig>
    val projectConfigKClass: KClass<ProjectConfig>

    fun getTargetSpecificModules(toolchainConfig: ToolchainConfig, projectConfig: ProjectConfig): Iterable<ConfigModuleDefinition>

    /**
     * Generates all the code necessary for this software
     */
    @Throws(CodeGenerationException::class)
    fun emit(toolchainConfig: ToolchainConfig, projectConfig: ProjectConfig, softwareContext: IrSoftwareContext)
}