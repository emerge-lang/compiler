package compiler.compiler

import io.kotest.core.config.AbstractProjectConfig
import io.kotest.core.extensions.Extension

object KotestProjectConfig : AbstractProjectConfig() {
    override fun extensions(): List<Extension> = listOf(CompilerSystemPropertiesListener)
}