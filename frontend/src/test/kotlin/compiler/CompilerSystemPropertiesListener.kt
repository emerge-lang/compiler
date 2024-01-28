package compiler.compiler

import io.kotest.core.annotation.AutoScan
import io.kotest.core.listeners.ProjectListener
import io.kotest.extensions.system.OverrideMode
import io.kotest.extensions.system.SystemPropertyProjectListener
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.exists

object CompilerSystemPropertiesListener : ProjectListener {
    private val projectBaseDir = run {
        var assumedRoot = Paths.get(".").toAbsolutePath().parent
        require(assumedRoot.hasPom()) { "The tests musts execute with a CWD that is one of the maven modules." }
        var assumedRootParent = assumedRoot.parent
        while (assumedRootParent.resolve("pom.xml").exists()) {
            assumedRoot = assumedRootParent
            assumedRootParent = assumedRoot.parent
        }

        assumedRoot
    }

    override val name = "Default Module Sources Locations in System Properties"

    private val impl = SystemPropertyProjectListener(mapOf<String, String>(
        "emerge.frontend.core.sources" to projectBaseDir.resolve("stdlib/core").toString(),
        "emerge.frontend.std.sources" to projectBaseDir.resolve("stdlib/std").toString(),
        "emerge.backend.noop.platform.sources" to projectBaseDir.resolve("backend-api/src/main/emerge/noop-backend-platform").toString(),
    ), OverrideMode.SetOrIgnore)

    override suspend fun afterProject() {
        impl.afterProject()
    }

    override suspend fun beforeProject() {
        impl.beforeProject()
    }
}

private fun Path.hasPom() = resolve("pom.xml").exists()