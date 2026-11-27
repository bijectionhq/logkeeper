# Consensus keeper image. Build from the repository root:
#   docker build -f deploy/consensus/Dockerfile -t logkeeper-consensus:dev .
# The healthcheck uses the keeper's admin listener on 127.0.0.1:5741, as in
# deploy/consensus/keeper.example.json.

FROM rust:1.94.1-slim-bookworm@sha256:cf9dd0ec73e75f827fe59123fff9dc65af1a1c8363c3c31ee8d7f8ad0b6a5fb2 AS toolchain
FROM toolchain AS build
ARG TARGETARCH
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry,id=logkeeper-registry,sharing=locked \
    --mount=type=cache,target=/src/target,id=logkeeper-target-${TARGETARCH},sharing=locked \
    cargo build --locked --release --features stream --bin logkeeper \
    && install -m 0555 target/release/logkeeper /usr/local/bin/logkeeper

FROM debian:bookworm-slim@sha256:e67eeead736ff7bbe258ef088bff683635c561b1fcfefad0806c1df4ab49ce0e
# The dated Debian archives fix curl, ca-certificates, and their dependencies.
# APT verifies the archived Release signatures using Debian's system keyring.
ARG DEBIAN_SNAPSHOT=20261127T000000Z
RUN --mount=type=bind,from=toolchain,source=/etc/ssl/certs/ca-certificates.crt,target=/tmp/build-ca-certificates.crt \
    sed -i \
        -e "s|^URIs: http://deb.debian.org/\(.*\)|URIs: https://snapshot.debian.org/archive/\1/${DEBIAN_SNAPSHOT}/|" \
        -e '/^Signed-By:/a Check-Valid-Until: no' /etc/apt/sources.list.d/debian.sources \
    && apt-get -o Acquire::https::CaInfo=/tmp/build-ca-certificates.crt update \
    && apt-get -o Acquire::https::CaInfo=/tmp/build-ca-certificates.crt install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/* /var/log/apt/* /var/log/dpkg.log /var/log/alternatives.log \
    && groupadd --system --gid 10001 logkeeper \
    && useradd --system --no-log-init --uid 10001 --gid 10001 --home-dir /var/lib/logkeeper \
        --shell /usr/sbin/nologin logkeeper \
    && chage --lastday 0 logkeeper \
    && install -d -o 10001 -g 10001 -m 0700 \
        /var/lib/logkeeper /var/lib/logkeeper/media /var/lib/logkeeper/registry
COPY --from=build /usr/local/bin/logkeeper /usr/local/bin/logkeeper
USER 10001:10001
# Media (WAL, segments, snapshots) and the enrollment registry live on
# separate volumes: the registry must survive loss of the media.
VOLUME ["/var/lib/logkeeper/media", "/var/lib/logkeeper/registry"]
# Application, control (peer) and bulk lanes.
EXPOSE 5441/tcp 5541/tcp 5641/tcp
HEALTHCHECK --interval=10s --timeout=3s --start-period=120s --retries=3 \
    CMD curl -fsS -o /dev/null http://127.0.0.1:5741/live || exit 1
STOPSIGNAL SIGTERM
ENTRYPOINT ["/usr/local/bin/logkeeper", "keeper"]
CMD ["--config", "/etc/logkeeper/keeper.json"]
