#!/usr/bin/env bash
#
# Runs the Rocq prover from the rocq/rocq-prover Docker image on the proofs in this directory,
# so that nobody has to install Rocq, opam or OCaml locally.
#
# This is the one entry point for checking the proofs; the GitHub Actions workflow
# (.github/workflows/build-emerge.yaml) runs the very same script, so a green local run means
# a green CI run.
#
#   ./rocq.sh              compile all proofs, then check them
#   ./rocq.sh build        compile all proofs only
#   ./rocq.sh check        re-check the compiled proofs, and gate on unproven claims
#   ./rocq.sh clean        delete all build artifacts
#   ./rocq.sh repl [args]  open a Rocq REPL with this project's load path
#   ./rocq.sh shell        open a shell in the container, for poking around
#
# Environment:
#   ROCQ_IMAGE   Docker image to use (default below). Bumping the Rocq version is a one-line
#                change here, and CI picks it up automatically.
#   JOBS         number of parallel compile jobs (default: number of cores in the container)
#
# On Windows, run this from Git Bash (it ships with git); Docker Desktop must be running.

set -euo pipefail

ROCQ_IMAGE="${ROCQ_IMAGE:-rocq/rocq-prover:9.2}"

proofs_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mount_source="$proofs_dir"
docker_args=()

case "$(uname -s)" in
  MINGW* | MSYS* | CYGWIN*)
    # Git Bash/Cygwin rewrite arguments that look like unix paths ('/proofs' would turn into
    # 'C:/Program Files/Git/proofs'), and Docker needs a Windows path for the bind mount.
    export MSYS_NO_PATHCONV=1
    export MSYS2_ARG_CONV_EXCL='*'
    mount_source="$(cd -- "$proofs_dir" && pwd -W)"
    ;;
  *)
    # The image's default user is uid 1000; where the checkout belongs to anyone else (GitHub
    # runners use uid 1001) the container could not write its build artifacts. Running as the
    # invoking user fixes that; HOME keeps opam pointed at its switch.
    docker_args+=(--user "$(id -u):$(id -g)" --env "HOME=/home/rocq")
    ;;
esac

docker_args+=(--rm --volume "${mount_source}:/proofs" --workdir /proofs)

if [ -t 0 ] && [ -t 1 ]; then
  docker_args+=(--interactive --tty)
fi

if [ -n "${JOBS:-}" ]; then
  docker_args+=(--env "JOBS=${JOBS}")
fi

command="${1:-verify}"
if [ $# -gt 0 ]; then
  shift
fi

if ! command -v docker > /dev/null 2>&1; then
  echo "rocq.sh: 'docker' not found on PATH; it is needed to run $ROCQ_IMAGE" >&2
  exit 1
fi

case "$command" in
  verify | build | check | clean | repl)
    # The work itself happens inside the container, in tools/verify.sh: that keeps every step of
    # the check running in the exact same environment, no matter which host started it.
    exec docker run "${docker_args[@]}" "$ROCQ_IMAGE" \
      /bin/sh /proofs/tools/verify.sh "$command" "$@"
    ;;
  shell)
    exec docker run "${docker_args[@]}" "$ROCQ_IMAGE" /bin/bash "$@"
    ;;
  -h | --help | help)
    sed -n '3,25p' -- "${BASH_SOURCE[0]}" | sed -e 's/^# \{0,1\}//' -e 's/^#$//'
    ;;
  *)
    echo "rocq.sh: unknown command '$command'; try 'rocq.sh --help'" >&2
    exit 2
    ;;
esac
