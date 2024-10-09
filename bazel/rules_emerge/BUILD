load(":toolchain.bzl", "register_emerge_toolchains")

exports_files(srcs = [
    "binary.bzl",
    "emerge_module.bzl",
    "toolchain.bzl",
])

toolchain_type(name = "toolchain")

register_emerge_toolchains(module_version())
