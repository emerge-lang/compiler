# Emerge Lang (Toy language, working title)

I am building a toy language here with the main goal of entertaining myself.
You're invited to talk, exchange ideas, contribute, ... in case it entertains you, too.

## Dependencies for running the compiler

### LLVM

#### Linux host

To run the compiler on Ubuntu, install `llvm-18` and `lld-18` so that e.g. `llc-18` is available as a command.

#### Windows host

The windows distributions of LLVM don't include some important tools, e.g. a linker (`lld`). This project
contains [a GitHub action to compile a windows build of LLVM](.github/workflows/build-llvm-windows.yaml)
that includes the `lld` linker as a Windows executable.  You need to copy the build outputs of that action
to the Windows machine you want to run the compiler on and then point the emerge compiler to that LLVM
distribution. Say you extract the files to `F:\LLVM\18.1.5` so that e.g. `llc` is located at
`F:\LLVM\18.1.5\bin\llc.exe`. Then you need to set `backends.x86_64-pc-linux-gnu.llvm-installation-directory`
in toolchain-config.yml to `F:\LLVM\18.1.5` (copy from [](./toolchain-config.yml.dist))

## Development

This being a Kotlin/JVM codebase, you need the typical tools for that:

* A JDK version 21 or newer (see [](.java-version))
* Maven 3
* maven will handle all JVM-ecosystem dependencies for you

### Dependencies

As this project works with binaries entirely outside the JVM world, its not possible to satisfy
all dependencies from there. You need a couple more things:

#### C-runtime startup files ("crtstuff", to quote gcc)

For all linux targets you need some binaries from GNU libc and gcc, so the emerge compiler can link them
into the linux executables. You can grab them from linux distro images compatible with the target, or [build
them yourself (see the GitHub Actions Workflow)](.github/workflows/build-emerge.yaml).
Store the binaries in you development/build environment (e.g. in `/local-resources`) and put their paths
into `toolchain-config.yml` in the project root (copy from [](./toolchain-config.yml.dist))

### Building

With the dependencies available, you can use standard maven commands:

```bash
# compile and package
mvn clean package

# compile, package and run all tests
mvn clean verify
```

## Running the compiler

This codebase builds one main executable, called `emerge toolchain`, that houses all commands necessary
to work with emerge code. They are designed for machine consumption, and long-term there should be integrations
with popular build tools (i'm fancying bazel currently) as an interface to the user.

To run the compiler you need two things:

1. `toolchain-config.yml` - this tells the compiler where its static resources are located (stdlib code,
   pre-built binaries, ...). See "Dependencies for running the compiler" on how to fill that file.
2. A `project-config.yml` for the codebase you want to compile. This tells the compiler all it needs to know
   about the specific build it has to carry out. An example:
   ```
   modules:
     - name: compilertest
       sources: ./src
       uses:
         - emerge.ffi.c
   targets:
     x86_64-pc-linux-gnu:
       output-directory: ../emerge-out
   ```
   This tells the compiler that:
   * your project consists of one emerge module, called `compilertest`
     * with its sources located at `./src` (paths are always relative to the yml file)
     * this module depends on the `emerge.ffi.c` module, enabling your code to use the C FFI
   * you want to build the `x86_64-pc-linux-gnu` target. The output should be put into `../emerge-out`