# How to invoke the emerge toolchain without bazel

This is relevant for you if you don't want to or can't use bazel to build your emerge project.

After you have the toolchain installed, you need to collect the constituents of the compiler invocation
1. the JRE executable. After installation, there is a convenient symlink in the directory of the toolchain,
   so you can confidently hard-code the JRE executable to be this:
   `/opt/emerge-toolchain/$VERSION/jre/bin/java`
2. the JAR file that contains the actual toolchain and compiler code. This can always be found here:
   `/opt/emerge-toolchain/$VERSION/bin/toolchain.jar`
3. the `toolchain-config.yml` that tells the compiler where its static resources are. This is also installed
   and set up automatically, so you can also hardcode this one:
   `/opt/emerge-toolchain/$VERSION/toolchain-config.yml`
4. **A `project-config.yml` for the codebase you want to compile.** This tells the compiler all it needs to know
   about the specific build it has to carry out. An example:
   ```yaml
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

So an example invocation of the compiler would look like so:

```bash
/opt/emerge-toolchain/0.1.0/jre/bin/java \
   -jar /opt/emerge-toolchain/0.1.0/bin/toolchain.jar \
   --toolchain-config /opt/emerge-toolchain/0.1.0/toolchain-config.yml \
   project --project-config ./emerge-test-project/project-config.yml \
   compile --target x86_64-pc-linux-gnu
```

**!! Keep in mind that this is intended for computer consumption. Humans should always get a much nicer UX from a build tool.**