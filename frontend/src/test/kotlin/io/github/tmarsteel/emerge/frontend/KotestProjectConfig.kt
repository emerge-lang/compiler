package compiler.io.github.tmarsteel.emerge.frontend

import io.kotest.core.config.AbstractProjectConfig

class KotestProjectConfig : AbstractProjectConfig() {
    override val parallelism = Runtime.getRuntime().availableProcessors()
}