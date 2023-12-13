package compiler.reportings

import compiler.ast.type.TypeParameter

data class VarianceOnFunctionTypeParameterReporting(
    val parameter: TypeParameter,
) : Reporting(
    Level.ERROR,
    "Type parameters on functions cannot have variance",
    parameter.name.sourceLocation,
)