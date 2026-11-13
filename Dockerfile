# Reproducible environment for building, testing and verifying Junco.
#
#   docker build -t junco .
#   docker run --rm junco                     # verify every configuration (scripts/verify-all.sh)
#   docker run --rm junco cargo test --locked --workspace --features junco-policy/test-util
#   docker run --rm -it junco bash            # interactive; `cargo verus verify ...` is on PATH
#
# Ubuntu 24.04 provides the glibc 2.39 that the pinned Z3 release requires.
FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        build-essential ca-certificates curl git libssl-dev pkg-config python3 unzip \
    && rm -rf /var/lib/apt/lists/*

ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    PATH=/opt/verus:/opt/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --no-modify-path --profile minimal \
        --default-toolchain 1.98.1-x86_64-unknown-linux-gnu \
        --component rustc-dev --component llvm-tools --component rustfmt

WORKDIR /junco
COPY . .

# Download the pinned Verus and Z3 (sha256-checked) and check the whole toolchain; then expose
# Verus at /opt/verus and Z3 on PATH so `cargo verus` works without the script.
RUN scripts/verify-all.sh --download /opt/verus-tools --list \
    && ln -s "$(dirname "$(find /opt/verus-tools/verus-dist -type f -name verus -perm -u+x | head -n1)")" /opt/verus \
    && ln -s "$(find /opt/verus-tools/z3 -type f -name z3 -perm -u+x | head -n1)" /usr/local/bin/z3
ENV VERUS_DIST=/opt/verus

RUN cargo fetch --locked && cargo build --locked --workspace

CMD ["scripts/verify-all.sh"]
