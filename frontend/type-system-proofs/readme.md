# Type system proofs

Machine-checked proofs about the Emerge type system, written in [Rocq](https://rocq-prover.org/)
(the prover formerly called Coq).

Nothing here is compiled into the compiler yet; the proofs are a specification of what the type
system implemented in `../src/main/kotlin/compiler/binding/type` is supposed to do, checked by a
machine instead of by review.

## Running the proofs

Rocq runs out of the official `rocq/rocq-prover` Docker image, so the only prerequisite is a
working Docker (on Windows: Docker Desktop, and run the script from Git Bash).

```sh
./rocq.sh          # compile all proofs, then check them
./rocq.sh build    # compile only - the fast inner loop while writing a proof
./rocq.sh check    # re-check the compiled proofs, and gate on unproven claims
./rocq.sh clean    # delete the build directory
./rocq.sh repl     # a Rocq REPL with the compiled theory on its load path
./rocq.sh shell    # a shell inside the container
```

The first run pulls the image (~1 GB). CI runs `./rocq.sh verify` too — the same script, the same
container — so a green run here means a green run there.

`ROCQ_IMAGE` overrides the image, `JOBS` the number of parallel compile jobs. The Rocq version is
pinned in `rocq.sh`; bumping it there is the whole upgrade, CI included.

Every artifact of the build lands in `_build/`, so the source tree stays free of `.vo` clutter and
`./rocq.sh clean` is just a directory removal.

## What "check" checks

**`rocqchk`**, Rocq's separate — and much smaller, hence more trustworthy — proof checker,
re-verifies the compiled proofs from the `.vo` files and reports everything they assume rather than
prove: axioms, uses of type-in-type, unsafe fixpoints and assumed positivity. It only *reports*; it
never fails over what it finds. Read its `CONTEXT SUMMARY` in the build log when you want to know
what a proof actually rests on.

**A grep for unproven claims** is what turns that into a gate, because compiling proves less than
it looks like: a theorem closed with `Admitted` compiles without complaint and merely becomes an
axiom, so "it builds" says nothing about whether anything was proven. So `check` also fails on
`Admitted`, `Axiom`, `Conjecture` and the `admit` tactic anywhere under `theories/`. When an
assumption is deliberate, mark the line and it is allowed through:

```coq
Axiom subtyping_is_decidable : ... (* allow-axiom: proof in progress, see #123 *)
```

It is blunt — it cannot see axioms inherited from an imported library, which is why the `rocqchk`
report above it is worth reading — but it reads our own sources rather than Rocq's console output,
so it cannot quietly stop working when a future Rocq rephrases a message. (`Parameter`,
`Hypothesis` and `Variable` are deliberately not flagged: inside sections and module types they are
discharged rather than assumed.)

`rocqchk` re-checks the whole dependency closure including the parts of the standard library in
use, so `check` is noticeably slower than `build` and gets slower as the proofs grow. That is the
price of the second, independent kernel; use `build` while iterating.

## Layout

| path                                     | what                                                |
|------------------------------------------|-----------------------------------------------------|
| [`theories/`](theories)                  | the proofs                                          |
| [`theories/dune`](theories/dune)         | build configuration: theory name and dependencies   |
| [`dune-project`](dune-project)           | dune version and the Rocq build language it uses    |
| [`_CoqProject`](_CoqProject)             | load path **for editors only**, not for the build   |
| [`rocq.sh`](rocq.sh)                     | host entry point, deals with Docker                 |
| [`tools/verify.sh`](tools/verify.sh)     | the build and the checks, run inside the container   |

`theories/Foo/Bar.v` is the module `EmergeTypeSystem.Foo.Bar` and is imported as
`From EmergeTypeSystem Require Import Foo.Bar.`. New files under `theories/` are picked up
automatically — dune discovers them, so nothing needs registering.

The theory name is unfortunately stated twice, in `theories/dune` for the build and in
`_CoqProject` for editors; renaming it means changing both.

Note that the standard library is a separate package since Rocq 9, so its modules are imported as
`From Stdlib Require Import List.`, not `Require Import Coq.Lists.List.`.

`theories/Sanity.v` is a placeholder that only exists so the build has something to do; delete it
once real theories exist.

## Editor support

Any Rocq IDE picks up `_CoqProject` for the load path, but needs a local Rocq installation to talk
to — the Docker image only serves the command line. For VS Code that is
[VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq), which expects
`rocq-language-server`; install Rocq 9.2 via opam to match the pinned image. Such an IDE compiles
in place rather than into `_build/`, which is why `.gitignore` covers `.vo` files next to the
sources as well.

With a local Rocq and dune, `dune rocq top theories/Foo.v` opens a REPL set up for exactly that
file, which `./rocq.sh repl` cannot do from inside the container.

## Generating Kotlin from the proofs

The eventual goal is to derive parts of the Kotlin implementation from the proven definitions, so
that the code the compiler runs is the code that was proven correct. Rocq has no Kotlin backend, so
this will take some work. The options, most promising first:

1. **Extract to JSON, emit Kotlin from that.** `Extraction Language JSON` (verified present in
   9.2) dumps the extracted program as a declaration tree — inductives, constructors, fixpoints,
   matches. A Kotlin emitter for that tree could live in this repo as a small tool and is plain
   data processing, no Rocq plugin needed. The catch is that extraction erases types down to an
   ML-ish core, so the generated Kotlin would need its types reconstructed to be idiomatic.
2. **Pretty-print Kotlin inside Rocq.** Deep-embed the fragment of Kotlin that is needed as an
   inductive type, write the emitter as a Rocq function and `Compute` the result into a `.kt` file.
   More upfront work, but the emitter itself becomes provable, and full control over the output.
3. **A Rocq plugin with a Kotlin extraction backend**, in OCaml, alongside the existing OCaml and
   Haskell ones. Most faithful, by far the most work, and ties the project to Rocq internals.

Until one of these lands, the proofs and the Kotlin implementation are connected by review only,
and the definitions in `theories/` should be kept recognisably close to their Kotlin counterparts
to keep that review tractable.
