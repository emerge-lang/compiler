ModuleInfo = provider(
    doc = "describes an emerge module; either with sources on the filesystem or expected to be supplied by the toolchain",
    fields = {
        "name": "name of the emerge module, e.g. com.acme.foo",
        "uses": "depset of the ModuleInfos that this one directly depends on",
        "source_directory": "Label; the directory where the sources for this module are located",
        "source_files": "File[]; the emerge source files in source_directory",
    },
)

def _emerge_module_internal_impl(ctx):
    uses_modules = [u[ModuleInfo] for u in ctx.attr.uses]
    src_dir = ctx.attr.source_directory
    if src_dir != None:
        src_dir = src_dir.files.to_list()[0]

    return ModuleInfo(
        name = ctx.attr.emerge_package_name,
        uses = depset(uses_modules, transitive = [m.uses for m in uses_modules]),
        source_directory = src_dir,
        source_files = ctx.files.srcs,
    )

emerge_module_internal = rule(
    implementation = _emerge_module_internal_impl,
    attrs = {
        "emerge_package_name": attr.string(mandatory = True),
        "srcs": attr.label_list(allow_files = [".em"], default = []),
        "source_directory": attr.label(allow_single_file = True, allow_rules = [], default = None),
        "uses": attr.label_list(allow_files = False, allow_rules = ["emerge_module_internal"], default = []),
    },
)

def emerge_module(name, source_directory, uses = [], emerge_package_name = None, **kwargs):
    srcs = []
    if source_directory != "":
        srcs = native.glob([source_directory + "/**/*.em"], allow_empty = False)

    emerge_module_internal(
        name = name,
        source_directory = native.package_relative_label(source_directory),
        srcs = srcs,
        uses = uses,
        emerge_package_name = emerge_package_name or name,
        **kwargs
    )
