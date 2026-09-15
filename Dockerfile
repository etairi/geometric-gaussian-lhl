# syntax=docker/dockerfile:1
FROM debian:bookworm-slim

ARG DEBIAN_FRONTEND=noninteractive
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get update \
    && apt-get install --no-install-recommends -y ca-certificates curl git \
    && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home --shell /bin/bash lean \
    && mkdir -p /workspace/.lake \
    && chown -R lean:lean /workspace

USER lean
ENV ELAN_HOME=/home/lean/.elan
ENV PATH=/home/lean/.elan/bin:${PATH}
ENV LEAN_ABORT_ON_PANIC=1
ENV MATHLIB_CACHE_DIR=/workspace/.lake/mathlib-cache
WORKDIR /workspace

RUN curl --proto '=https' --tlsv1.2 --fail --silent --show-error \
        https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none

COPY --chown=lean:lean lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)"
COPY --chown=lean:lean . .

CMD ["bash", "-c", "lake exe cache get && lake build"]
