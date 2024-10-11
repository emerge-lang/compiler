LlvmTargetTriple = provider(
    fields = {
        "triple": "string; the triple",
    },
)

def _selected_target_triple_impl(ctx):
    return LlvmTargetTriple(triple = ctx.attr.triple)

selected_target_triple = rule(
    attrs = {
        "triple": attr.string(
            mandatory = True,
        ),
    },
    implementation = _selected_target_triple_impl,
)
