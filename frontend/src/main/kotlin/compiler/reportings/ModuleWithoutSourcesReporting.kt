package compiler.reportings

import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.PackageName
import java.nio.file.Path

class ModuleWithoutSourcesReporting(
    val moduleName: PackageName,
    val srcDir: Path,
) : Reporting(
    Reporting.Level.WARNING,
    "Found no source files for module $moduleName in $srcDir",
    SourceLocation.UNKNOWN,
)