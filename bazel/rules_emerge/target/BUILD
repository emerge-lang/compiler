load("@bazel_skylib//lib:selects.bzl", "selects")
load("//target:triple.bzl", "selected_target_triple")

exports_files(["triple.bzl"])

config_setting(
    name = "is_amd64",
    constraint_values = [
        "@platforms//cpu:x86_64",
    ],
)

config_setting(
    name = "is_linux",
    constraint_values = [
        "@platforms//os:linux",
    ],
)

selects.config_setting_group(
    name = "linux_amd64",
    match_all = [
        ":is_linux",
        ":is_amd64",
    ],
)

selected_target_triple(
    name = "selected_target_triple",
    triple = select({
        ":linux_amd64": "x86_64-pc-linux-gnu",
    }),
    visibility = ["//visibility:public"],
)
