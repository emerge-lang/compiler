package compiler.reportings

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.nio.file.Path

class ModuleWithoutSourcesDiagnostic(
    val moduleName: CanonicalElementName.Package,
    val srcDir: Path,
) : Diagnostic(
    Diagnostic.Level.WARNING,
    "Found no source files for module $moduleName in $srcDir",
    Span.UNKNOWN,
)