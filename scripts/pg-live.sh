#!/usr/bin/env bash
# One-off dockerized postgres + the live conformance checklist.
#
#   scripts/pg-live.sh [17|18] [trust|scram|password|md5] [plain|tls|tls-verify|tls-cb]
#
# `plain` and `tls` run the full `pg_live_test` checklist against a disposable
# container. `tls-verify` runs the server-identity matrix with throwaway keys,
# certificates, and containers. `tls-cb` runs the SCRAM channel-binding matrix
# and requires the `scram` auth mode. md5 only makes sense on 17 (deprecated
# in 18).
set -euo pipefail

VERSION="${1:-17}"
AUTH="${2:-trust}"
TRANSPORT="${3:-plain}"
PORT="${PG_LIVE_PORT:-54399}"
NAME="pg-lean-live-$$"
PASS="pg-lean-läuft"
WORK=""

case "$AUTH" in
  trust)
    ARGS=(-e POSTGRES_HOST_AUTH_METHOD=trust)
    URL="postgres://postgres@localhost:${PORT}/postgres"
    ;;
  scram)
    ARGS=(-e POSTGRES_PASSWORD="$PASS")
    URL="postgres://postgres:pg-lean-l%C3%A4uft@localhost:${PORT}/postgres"
    ;;
  password)
    ARGS=(-e POSTGRES_PASSWORD="$PASS" -e POSTGRES_INITDB_ARGS="--auth-host=password")
    URL="postgres://postgres:pg-lean-l%C3%A4uft@localhost:${PORT}/postgres"
    ;;
  md5)
    ARGS=(-e POSTGRES_PASSWORD="$PASS" -e POSTGRES_INITDB_ARGS="--auth-host=md5 -c password_encryption=md5")
    URL="postgres://postgres:pg-lean-l%C3%A4uft@localhost:${PORT}/postgres"
    ;;
  *)
    echo "unknown auth mode: $AUTH" >&2
    exit 2
    ;;
esac

case "$TRANSPORT" in
  plain) ;;
  tls) URL="${URL}?sslmode=require" ;;
  tls-verify) ;;
  tls-cb)
    if [[ "$AUTH" != "scram" ]]; then
      echo "tls-cb requires the scram auth mode" >&2
      exit 2
    fi
    ;;
  *)
    echo "unknown transport: $TRANSPORT (plain, tls, tls-verify, or tls-cb)" >&2
    exit 2
    ;;
esac

cleanup() {
  docker rm -f "$NAME" >/dev/null 2>&1 || true
  if [[ -n "$WORK" ]]; then
    rm -rf "$WORK"
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

if [[ "$TRANSPORT" == "tls" || "$TRANSPORT" == "tls-verify" ||
    "$TRANSPORT" == "tls-cb" ]]; then
  command -v openssl >/dev/null || {
    echo "openssl is required for ${TRANSPORT}" >&2
    exit 2
  }
fi

wait_for_postgres() {
  # Check over TCP: the docker entrypoint's init-phase server only listens on
  # the unix socket, and the port proxy accepts before the real server is up.
  for _ in $(seq 1 120); do
    if docker exec "$NAME" pg_isready -h 127.0.0.1 -U postgres >/dev/null 2>&1; then
      return 0
    fi
    sleep 0.5
  done
  echo "postgres did not become ready" >&2
  docker logs "$NAME" >&2 || true
  return 1
}

start_tls_server() {
  local cert="$1"
  local key="$2"
  docker rm -f "$NAME" >/dev/null 2>&1 || true
  docker run --rm -d --name "$NAME" -p "${PORT}:5432" "${ARGS[@]}" \
    -v "${WORK}:/certs:ro" --entrypoint bash "postgres:${VERSION}" -ceu '
      install -o postgres -g postgres -m 0644 "$1" /tmp/server.crt
      install -o postgres -g postgres -m 0600 "$2" /tmp/server.key
      exec docker-entrypoint.sh postgres -c ssl=on \
        -c ssl_cert_file=/tmp/server.crt -c ssl_key_file=/tmp/server.key
    ' bash "/certs/${cert}" "/certs/${key}" >/dev/null
  wait_for_postgres
}

if [[ "$TRANSPORT" == "tls-verify" ]]; then
  WORK="$(mktemp -d /tmp/pg-lean-tls-verify.XXXXXX)"

  cat >"$WORK/good.ext" <<'EOF'
[server_ext]
basicConstraints = critical,CA:FALSE
keyUsage = critical,digitalSignature,keyEncipherment
extendedKeyUsage = serverAuth
subjectAltName = DNS:localhost,IP:127.0.0.1
EOF
  cat >"$WORK/mismatch.ext" <<'EOF'
[server_ext]
basicConstraints = critical,CA:FALSE
keyUsage = critical,digitalSignature,keyEncipherment
extendedKeyUsage = serverAuth
subjectAltName = DNS:not-localhost.example.test
EOF

  openssl req -x509 -newkey rsa:2048 -nodes -sha256 \
    -subj /CN=pg-lean-live-root -days 2 \
    -addext basicConstraints=critical,CA:TRUE,pathlen:0 \
    -addext keyUsage=critical,keyCertSign,cRLSign \
    -keyout "$WORK/root.key" -out "$WORK/root.crt" >/dev/null 2>&1
  openssl req -x509 -newkey rsa:2048 -nodes -sha256 \
    -subj /CN=pg-lean-live-unrelated-root -days 2 \
    -addext basicConstraints=critical,CA:TRUE,pathlen:0 \
    -addext keyUsage=critical,keyCertSign,cRLSign \
    -keyout "$WORK/unrelated.key" -out "$WORK/unrelated.crt" >/dev/null 2>&1

  make_leaf() {
    local name="$1"
    local ext="$2"
    local days="$3"
    openssl req -new -newkey rsa:2048 -nodes -sha256 -subj /CN=localhost \
      -keyout "$WORK/${name}.key" -out "$WORK/${name}.csr" >/dev/null 2>&1
    openssl x509 -req -sha256 -in "$WORK/${name}.csr" \
      -CA "$WORK/root.crt" -CAkey "$WORK/root.key" -CAcreateserial \
      -days "$days" -extfile "$WORK/${ext}.ext" -extensions server_ext \
      -out "$WORK/${name}.crt" >/dev/null 2>&1
  }
  make_leaf good good 2
  make_leaf mismatch mismatch 2
  # `-days 0` makes notAfter equal notBefore. Fixture generation and server
  # startup take the clock past that instant before the verification probe.
  make_leaf expired good 0
  openssl req -x509 -newkey rsa:2048 -nodes -sha256 -subj /CN=localhost \
    -days 2 -addext basicConstraints=critical,CA:FALSE \
    -addext keyUsage=critical,digitalSignature,keyEncipherment \
    -addext extendedKeyUsage=serverAuth \
    -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
    -keyout "$WORK/self.key" -out "$WORK/self.crt" >/dev/null 2>&1

  # Build once. Subsequent `bazel run` calls are no-op analyses and keep this
  # script independent of Bazel's platform-specific binary output layout.
  bazel build //Integration:pg_live_test

  LAST_OUTPUT=""
  LAST_STATUS=0
  run_probe() {
    local url="$1"
    set +e
    LAST_OUTPUT="$(bazel run --noshow_progress //Integration:pg_live_test -- --connect "$url" 2>&1)"
    LAST_STATUS=$?
    set -e
  }
  expect_pass() {
    local label="$1"
    local url="$2"
    run_probe "$url"
    if [[ "$LAST_STATUS" -ne 0 ]]; then
      echo "FAIL ${label}: expected connection success" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    echo "PASS ${label}"
  }
  expect_fail() {
    local label="$1"
    local url="$2"
    local reason="$3"
    run_probe "$url"
    if [[ "$LAST_STATUS" -eq 0 ]]; then
      echo "FAIL ${label}: connection unexpectedly succeeded" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    if ! grep -Eiq "$reason" <<<"$LAST_OUTPUT"; then
      echo "FAIL ${label}: refusal did not report ${reason}" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    echo "PASS ${label}"
  }
  uri() {
    local mode="$1"
    local root="$2"
    printf '%s?sslmode=%s&sslrootcert=%s' "$URL" "$mode" "$root"
  }

  echo "TLS identity matrix against postgres:${VERSION} (${AUTH}) on :${PORT}"

  start_tls_server good.crt good.key
  expect_pass "tls.verify_full.trusted_root" \
    "$(uri verify-full "$WORK/root.crt")"
  expect_fail "tls.verify_full.rejects_unrelated_root" \
    "$(uri verify-full "$WORK/unrelated.crt")" "unknown issuer"

  start_tls_server mismatch.crt mismatch.key
  expect_fail "tls.verify_full.rejects_hostname_mismatch" \
    "$(uri verify-full "$WORK/root.crt")" "hostname"
  expect_pass "tls.verify_ca.hostname_independent" \
    "$(uri verify-ca "$WORK/root.crt")"

  start_tls_server self.crt self.key
  expect_pass "tls.require.self_signed" "${URL}?sslmode=require"
  expect_fail "tls.verify_ca.rejects_self_signed" \
    "$(uri verify-ca "$WORK/root.crt")" "unknown issuer"
  expect_fail "tls.verify_full.rejects_self_signed" \
    "$(uri verify-full "$WORK/root.crt")" "unknown issuer"

  # The zero-day certificate has one-second ASN.1 time precision. Cross its
  # notAfter boundary explicitly so this negative is independent of host speed.
  sleep 2
  start_tls_server expired.crt expired.key
  expect_fail "tls.verify_full.rejects_expired" \
    "$(uri verify-full "$WORK/root.crt")" "expired"

  echo "TLS VERIFY MATRIX PASS"
  exit 0
fi

if [[ "$TRANSPORT" == "tls-cb" ]]; then
  WORK="$(mktemp -d /tmp/pg-lean-tls-cb.XXXXXX)"
  openssl req -x509 -newkey rsa:2048 -nodes -sha256 \
    -subj /CN=localhost -days 1 \
    -addext basicConstraints=critical,CA:FALSE \
    -addext keyUsage=critical,digitalSignature,keyEncipherment \
    -addext extendedKeyUsage=serverAuth \
    -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
    -keyout "$WORK/server.key" -out "$WORK/server.crt" >/dev/null 2>&1

  start_tls_server server.crt server.key
  bazel build //Integration:pg_live_test

  LAST_OUTPUT=""
  LAST_STATUS=0
  run_connect_probe() {
    local url="$1"
    shift
    set +e
    LAST_OUTPUT="$(
      bazel run --noshow_progress //Integration:pg_live_test -- \
        --connect "$url" "$@" 2>&1
    )"
    LAST_STATUS=$?
    set -e
  }
  expect_mechanism() {
    local label="$1"
    local url="$2"
    local mechanism="$3"
    set +e
    LAST_OUTPUT="$(
      bazel run --noshow_progress //Integration:pg_live_test -- \
        --connect-expect-mechanism "$url" "$mechanism" 2>&1
    )"
    LAST_STATUS=$?
    set -e
    if [[ "$LAST_STATUS" -ne 0 ]]; then
      echo "FAIL ${label}: expected ${mechanism}" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    echo "PASS ${label} (${mechanism})"
  }
  expect_connect_failure() {
    local label="$1"
    local url="$2"
    local reason="$3"
    run_connect_probe "$url"
    if [[ "$LAST_STATUS" -eq 0 ]]; then
      echo "FAIL ${label}: connection unexpectedly succeeded" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    if ! grep -Eiq "$reason" <<<"$LAST_OUTPUT"; then
      echo "FAIL ${label}: refusal did not report ${reason}" >&2
      echo "$LAST_OUTPUT" >&2
      exit 1
    fi
    echo "PASS ${label}"
  }

  echo "SCRAM channel-binding matrix against postgres:${VERSION} on :${PORT}"
  expect_mechanism "channel_binding.require.tls_plus" \
    "${URL}?sslmode=require&channel_binding=require" "SCRAM-SHA-256-PLUS"
  expect_connect_failure "channel_binding.require.plaintext_rejected" \
    "${URL}?sslmode=disable&channel_binding=require" \
    "channel_binding=require requires TLS"
  expect_mechanism "channel_binding.prefer.tls_plus" \
    "${URL}?sslmode=require&channel_binding=prefer" "SCRAM-SHA-256-PLUS"
  expect_mechanism "channel_binding.prefer.plaintext_scram" \
    "${URL}?sslmode=disable&channel_binding=prefer" "SCRAM-SHA-256"
  echo "SKIP channel_binding.tampered_live (the CB1 wrong-binding KAT covers this; no MITM injection hook)"
  echo "SCRAM CHANNEL BINDING MATRIX PASS"
  exit 0
fi

echo "starting postgres:${VERSION} (${AUTH}, ${TRANSPORT}) on :${PORT}"
if [[ "$TRANSPORT" == "tls" ]]; then
  WORK="$(mktemp -d /tmp/pg-lean-tls.XXXXXX)"
  # TLS 1.3 uses RSA-PSS for CertificateVerify; the self-signed certificate
  # itself is PKCS#1-signed. It is intentionally untrusted under `require`.
  openssl req -x509 -newkey rsa:2048 -nodes -subj /CN=localhost -days 1 \
    -keyout "$WORK/server.key" -out "$WORK/server.crt" >/dev/null 2>&1
  start_tls_server server.crt server.key
else
  docker run --rm -d --name "$NAME" -p "${PORT}:5432" \
    "${ARGS[@]}" "postgres:${VERSION}" >/dev/null
  wait_for_postgres
fi

PG_URL="$URL" bazel run //Integration:pg_live_test
