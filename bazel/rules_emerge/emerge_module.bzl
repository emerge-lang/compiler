ModuleInfo = provider(
    doc = "describes an emerge module; either with sources on the filesystem or expected to be supplied by the toolchain",
    fields = {
        "name": "name of the emerge module, e.g. com.acme.foo",
        "source_directory": "",
    },
)

def _emerge_module_impl(ctx):
    return ModuleInfo(
        name = ctx.name,
    )

emerge_module_internal = rule(
    implementation = _emerge_module_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = ["*.em"]),
        "source_directory": attr.label(allow_single_file = True, allow_rules = []),
    },
)

def emerge_module(name, source_directory, **kwargs):
    srcs = []
    if source_directory != "":
        srcs = native.glob([source_directory + "/**/*.em"], allow_empty = False)

    emerge_module_internal(
        name = name,
        source_directory = source_directory,
        srcs = srcs,
        **kwargs
    )
