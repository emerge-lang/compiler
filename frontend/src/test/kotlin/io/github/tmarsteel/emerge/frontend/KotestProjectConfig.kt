package compiler.io.github.tmarsteel.emerge.frontend

import compiler.compiler.CompilerSystemPropertiesListener
import io.kotest.core.config.AbstractProjectConfig
import io.kotest.core.extensions.Extension
import io.kotest.core.spec.IsolationMode

object KotestProjectConfig : AbstractProjectConfig() {
    override val parallelism = Runtime.getRuntime().availableProcessors()
    override fun extensions(): List<Extension> = listOf(CompilerSystemPropertiesListener)
    override val isolationMode = IsolationMode.InstancePerLeaf
}