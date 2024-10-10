load("//:emerge_module.bzl", "ModuleInfo", "emerge_module_internal")
load("//target:triple.bzl", "LlvmTargetTriple")

def _build_project_config_json(
        path_from_project_config_toolchain_cwd,
        target_triple,
        output_directory,
        all_modules):
    return {
        "modules": [{
            "name": module.name,
            "sources": path_from_project_config_toolchain_cwd + module.source_directory.path,
            "uses": [dep.name for dep in module.uses.to_list()],
        } for module in all_modules if module.source_directory != None],
        "targets": {
            target_triple: {
                "output-directory": path_from_project_config_toolchain_cwd + output_directory,
            },
        },
    }

def _emerge_binary_impl(ctx):
    llvm_target_triple = ctx.attr._triple[LlvmTargetTriple].triple

    root_module = ctx.attr.root_module[ModuleInfo]
    all_modules = depset([root_module], transitive = [root_module.uses]).to_list()
    project_config_file = ctx.actions.declare_file("project-config.json")
    path_from_project_config_toolchain_cwd = "../" * (project_config_file.root.path.count("/") + 1)
    output_file = ctx.actions.declare_file(llvm_target_triple + "/runnable")
    ctx.actions.write(
        output = project_config_file,
        content = json.encode(_build_project_config_json(
            path_from_project_config_toolchain_cwd,
            llvm_target_triple,
            output_file.dirname,
            all_modules,
        )),
    )

    all_src_files = depset(transitive = [depset([f for f in m.source_files]) for m in all_modules])
    toolchain = ctx.toolchains["//:toolchain"].emerge_toolchain_info

    ctx.actions.run(
        executable = toolchain.base_command[0],
        arguments = toolchain.base_command[1:] + [
            "project",
            "--project-config",
            project_config_file.path,
            "compile",
            "--target",
            llvm_target_triple,
        ],
        inputs = all_src_files.to_list() + [project_config_file],
        outputs = [output_file],
        progress_message = "Compiling binary {}; {} emerge modules: {}".format(output_file.path, len(all_modules), [m.name for m in all_modules]),
        toolchain = Label("//:toolchain"),
    )
    return DefaultInfo(files = depset([output_file]))

emerge_binary = rule(
    toolchains = ["//:toolchain"],
    implementation = _emerge_binary_impl,
    attrs = {
        "root_module": attr.label(mandatory = True, allow_files = False, allow_rules = ["emerge_module_internal"]),
        "_triple": attr.label(
            default = "//target:selected_target_triple",
        ),
    },
)
