#!/bin/sh
#
# Compiles and verifies the proofs. Runs INSIDE the rocq/rocq-prover container; start it through
# ../rocq.sh, which takes care of Docker. Plain POSIX sh on purpose - the container's /bin/sh is
# dash.
#
# dune drives the build (see ../theories/dune), which keeps every artifact in ../_build and the
# source tree clean. `check` then adds two things on top:
#
#   rocqchk    Rocq's separate - and much smaller, hence more trustworthy - proof checker
#              re-verifies the compiled proofs and reports everything they assume rather than
#              prove: axioms, type-in-type, unsafe fixpoints, assumed positivity. It only
#              reports; it never fails over what it finds.
#
#   the gate   compiling proves less than it looks like: a theorem closed with `Admitted`
#              compiles without complaint and merely turns into an axiom. So the theories are
#              also grepped for the commands that introduce something unproven. Blunt, but it
#              reads our own sources rather than Rocq's console output, so it cannot quietly
#              stop working when a future Rocq rephrases a message.

set -eu

cd "$(dirname -- "$0")/.."

THEORIES=theories
DUNE_FILE="$THEORIES/dune"
BUILD_DIR=_build/default/theories

# Rocq commands that introduce something unproven. Deliberately conservative: Parameter,
# Hypothesis and Variable are left out, as they are ordinary inside sections and module types,
# where they get discharged instead of assumed.
UNPROVEN='(^|[^[:alnum:]_])(Admitted[[:space:]]*\.|Axiom[[:space:]]|Conjecture[[:space:]]|admit[[:space:]]*[.;])'

# opt-out marker for a line that is meant to introduce an axiom, e.g.
#   Axiom subtyping_is_decidable : ... (* allow-axiom: see #123, proof in progress *)
ALLOW_MARKER='allow-axiom'

# the logical name of the theory, read from theories/dune so that renaming it there is enough
theory_name() {
  sed -n 's/^[[:space:]]*(name[[:space:]]\{1,\}\([A-Za-z0-9_.]\{1,\}\)).*/\1/p' "$DUNE_FILE" \
    | head -n 1
}

v_files() {
  find "$THEORIES" -type f -name '*.v' | LC_ALL=C sort
}

# An editor with a local Rocq compiles in place, next to the sources. dune refuses to build while
# any of its outputs also exists in the source tree, so those are removed first; the editor
# recreates them the next time it compiles.
remove_in_place_artifacts() {
  find "$THEORIES" -type f \
    \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) \
    -exec rm -f {} +
}

do_build() {
  remove_in_place_artifacts
  echo "> compiling with $(rocq --version | head -n 1), into $BUILD_DIR"
  if [ -n "${JOBS:-}" ]; then
    dune build -j "$JOBS"
  else
    dune build
  fi
}

do_validate() {
  vo_files=$(find "$BUILD_DIR" -type f -name '*.vo' 2> /dev/null | LC_ALL=C sort || true)
  if [ -z "$vo_files" ]; then
    echo "no compiled proofs in $BUILD_DIR; nothing to re-check"
    return 0
  fi
  echo "> re-checking with rocqchk, and reporting what the proofs assume"
  # word splitting intended: $vo_files is a newline separated list of paths without spaces
  # shellcheck disable=SC2086
  rocq check -silent -o -Q "$BUILD_DIR" "$(theory_name)" $vo_files
}

do_check_unproven() {
  files=$(v_files)
  if [ -z "$files" ]; then
    return 0
  fi
  # shellcheck disable=SC2086
  hits=$(grep -nE "$UNPROVEN" $files | grep -v "$ALLOW_MARKER" || true)
  if [ -n "$hits" ]; then
    {
      echo "ERROR: these lines state something instead of proving it:"
      printf '%s\n' "$hits" | sed -e 's/^/  /'
      echo "Prove it, or, if the assumption is deliberate, append a comment"
      echo "  (* $ALLOW_MARKER: <why, ideally with an issue link> *)"
      echo "to the line. Assumptions also show up in the rocqchk report above."
    } >&2
    return 1
  fi
  echo "> no unproven assumptions in $(printf '%s\n' "$files" | wc -l | tr -d ' ') file(s)"
}

do_clean() {
  # `dune clean` fails on a Docker Desktop bind mount (ftruncate on its own lock file), so the
  # build directory goes the blunt way
  rm -rf _build
  echo "removed all build artifacts"
}

command=${1:-verify}
if [ $# -gt 0 ]; then
  shift
fi

case "$command" in
  build) do_build ;;
  check)
    do_validate
    do_check_unproven
    ;;
  verify)
    do_build
    do_validate
    do_check_unproven
    ;;
  clean) do_clean ;;
  repl)
    remove_in_place_artifacts
    dune build
    exec rocq repl -Q "$BUILD_DIR" "$(theory_name)" "$@"
    ;;
  *)
    echo "verify.sh: unknown command '$command'" >&2
    exit 2
    ;;
esac
