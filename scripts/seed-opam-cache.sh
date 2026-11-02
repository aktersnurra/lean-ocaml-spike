#!/usr/bin/env bash
# Environment workaround, NOT part of the pipeline. Only needed where GitHub's HTTP archive
# endpoint (github.com/<o>/<r>/archive/...) is blocked but git reads are allowed (as in the
# sandbox this spike was run in). For each named opam package whose url.src is a GitHub
# archive, rebuild the tarball from the git tag with `git archive | gzip -cn` (which is how
# GitHub produces it, byte for byte), VERIFY it against the opam checksum, and only then put
# it in opam's download cache. A tarball that does not match is not used; nothing about
# versions or checksums changes.
#
#   scripts/seed-opam-cache.sh SWITCH PKG.VERSION...
set -euo pipefail
SWITCH="$1"; shift
OPAMROOT="${OPAMROOT:-$HOME/.opam}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
for pkg in "$@"; do
  raw="$(opam show --switch "$SWITCH" --raw "$pkg")"
  src="$(sed -n 's/^ *src: *"\(.*\)"/\1/p; /^ *src:$/{n;s/^ *"\(.*\)"/\1/p}' <<<"$raw" | head -1)"
  sum="$(grep -oE '(sha512|sha256)=[0-9a-f]+' <<<"$raw" | head -1)"
  algo="${sum%%=*}"; hash="${sum#*=}"
  if [ -f "$OPAMROOT/download-cache/$algo/${hash:0:2}/$hash" ]; then echo "cached  $pkg"; continue; fi
  if [[ ! "$src" =~ ^https://github.com/([^/]+)/([^/]+)/archive/(refs/tags/|refs/heads/)?(.+)\.tar\.gz$ ]]; then
    echo "SKIP    $pkg (not a GitHub archive: $src)"; continue
  fi
  owner="${BASH_REMATCH[1]}"; repo="${BASH_REMATCH[2]}"; ref="${BASH_REMATCH[4]}"
  git init -q --bare "$WORK/$repo-$ref.git"
  git -C "$WORK/$repo-$ref.git" fetch -q --depth=1 "https://github.com/$owner/$repo" "$ref"
  ok=""
  # GitHub's top-level directory: <repo>-<ref with a leading v dropped, '+' and '/' -> '-'>.
  r1="${ref#v}"; for prefix in "$repo-${r1//[+\/]/-}" "$repo-$r1" "$repo-${ref//[+\/]/-}" "$repo-$ref"; do
    git -C "$WORK/$repo-$ref.git" archive --format=tar --prefix="$prefix/" FETCH_HEAD | gzip -cn > "$WORK/t.tar.gz"
    got="$("${algo}sum" "$WORK/t.tar.gz" | cut -d' ' -f1)"
    if [ "$got" = "$hash" ]; then ok=1; break; fi
  done
  if [ -n "$ok" ]; then
    mkdir -p "$OPAMROOT/download-cache/$algo/${hash:0:2}"
    mv "$WORK/t.tar.gz" "$OPAMROOT/download-cache/$algo/${hash:0:2}/$hash"
    echo "seeded  $pkg ($algo verified, prefix $prefix/)"
  else
    echo "NOMATCH $pkg: rebuilt archive does not match $algo from opam; not seeded" >&2
  fi
done
