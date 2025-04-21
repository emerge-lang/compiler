package compiler.diagnostic

interface InvocationCandidateNotApplicableDiagnostic {
    fun asDiagnostic(): Diagnostic
    val inapplicabilityHint: SourceHint
}