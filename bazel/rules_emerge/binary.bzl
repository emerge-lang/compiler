load("//:emerge_module.bzl", "emerge_module_internal")

def _emerge_binary_impl(ctx):
    print(ctx.toolchains["//:toolchain"])
    pass

emerge_binary = rule(
    toolchains = ["//:toolchain"],
    implementation = _emerge_binary_impl,
    attrs = {
        "root_module": attr.label(mandatory = True, allow_files = False, allow_rules = ["emerge_module_internal"]),
    },
)
