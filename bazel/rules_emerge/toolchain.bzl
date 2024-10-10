EmergeToolsInfo = provider(
    doc = "location of the emerge toolchain and how to invoke it",
    fields = {
        "version": "the version of the emerge toolchain; the official release version",
        "base_command": "list of strings; the base command to invoke the toolchain",
    },
)

def _emerge_toolchain_on_linux_impl(ctx):
    directory = "/opt/emerge-toolchain/" + ctx.attr.version
    toolchain_info = platform_common.ToolchainInfo(
        emerge_toolchain_info = EmergeToolsInfo(
            version = ctx.attr.version,
            base_command = [
                directory + "/jre/bin/java",
                "-jar",
                directory + "/bin/toolchain.jar",
                "--toolchain-config",
                directory + "/toolchain-config.yml",
            ],
        ),
    )
    return [toolchain_info]

emerge_toolchain_on_linux = rule(
    implementation = _emerge_toolchain_on_linux_impl,
    attrs = {
        "version": attr.string(mandatory = True),
    },
)

def register_emerge_toolchains(version):
    emerge_toolchain_on_linux(
        name = "emerge_toolchain_on_linux",
        version = version,
    )

    native.toolchain(
        name = "emerge_linux_toolchain",
        exec_compatible_with = [
            "@platforms//os:linux",
        ],
        target_compatible_with = [
            "@platforms//os:linux",
        ],
        toolchain = "@rules_emerge//:emerge_toolchain_on_linux",
        toolchain_type = "@rules_emerge//:toolchain",
    )
