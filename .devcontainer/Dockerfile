FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

RUN apt-get update \
    && apt-get install -y --no-install-recommends build-essential ca-certificates curl git python3 \
    && rm -rf /var/lib/apt/lists/*

USER vscode
ENV PATH="/home/vscode/.elan/bin:${PATH}"

# The repository's lean-toolchain selects Lean when the workspace is created.
RUN curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none
