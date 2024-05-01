package compiler.reportings

import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import java.nio.file.Path

class ModuleWithoutSourcesReporting(
    val moduleName: CanonicalElementName.Package,
    val srcDir: Path,
) : Reporting(
    Reporting.Level.WARNING,
    "Found no source files for module $moduleName in $srcDir",
    Span.UNKNOWN,
)