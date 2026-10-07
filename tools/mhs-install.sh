#!/bin/sh
# Provision the pinned MicroHs environment ychr's MicroHs build needs.
#
# Run through `make mhs-install`, which is what CI runs before
# `make mhs-build`, so CI and a developer compile against one environment
# instead of each against whatever it happens to have. The pins are the
# three revisions below and the package versions in mhs-packages.txt
# beside this script; they are the state dev-docs/MICROHS_GAPS.md was
# re-verified against. Everything installs into $MHS_HOME (default
# ~/.mcabal), the package database mhs searches first.
#
# The script is skipped entirely while $MHS_HOME/.ychr-mhs-install still
# records what it installs — the revisions, the git package names, the
# package list and this script itself — as already in place, so a machine
# that is up to date runs it in no time. Changing any of them reinstalls
# the lot: an installed MicroHs revision cannot be read back out of the
# compiler, and a package installed at the same version from different
# sources is indistinguishable, so "what this script installs changed" is
# the only safe trigger.
#
# Installing replaces the mhs, mcabal and cpphs binaries in
# $MHS_HOME/bin as well as the packages, and replaces
# $MHS_HOME/packages.txt — mcabal's only source of versions, and also the
# Stackage list `mcabal update` writes. A developer's own file is put back
# on the way out, including on failure, and packages set aside for a
# version change are put back too.
#
# The package set is the subset of MicroHs's Makefile.packages that ychr
# needs, in that file's order (dependency order: mcabal installs one
# package per invocation and refuses one whose dependencies are missing).
# https://github.com/augustss/MicroHs/blob/master/Makefile.packages

set -eu

MICROHS_REV=${MICROHS_REV:-f65d3c65cb1c31f6ab3e33d409ac3af60369eaef}
MICROHS_GIT=${MICROHS_GIT:-https://github.com/augustss/MicroHs.git}
PRETTYPRINTER_REV=${PRETTYPRINTER_REV:-37d2d263cfbc4839fa51e205a4be066916a24c49}
PRETTYPRINTER_GIT=${PRETTYPRINTER_GIT:-https://github.com/haskell-prettyprinter/prettyprinter.git}
OPTPARSE_REV=${OPTPARSE_REV:-a6ca1a25bfad06f660cd67df75349cfcda567a8f}
OPTPARSE_GIT=${OPTPARSE_GIT:-https://github.com/pcapriotti/optparse-applicative.git}
MHS_HOME=${MHS_HOME:-$HOME/.mcabal}
here=$(dirname "$0")
MHS_PACKAGES=${MHS_PACKAGES:-$here/mhs-packages.txt}

# The wrappers and mcabal's own CABALDIR need an absolute path: the git
# packages are built from within a subshell that has changed directory.
case "$MHS_HOME" in
  /*) : ;;
  *) MHS_HOME="$PWD/$MHS_HOME" ;;
esac

# mhs shells out to the tools installed beside it — cpphs for every
# package that uses CPP, and hsc2hs when one needs it — so the install
# directory goes on PATH for everything below. CI has not put it there
# yet: the workflow adds it to $GITHUB_PATH, which applies to the steps
# after this one.
PATH="$MHS_HOME/bin:$PATH"
export PATH

[ -f "$MHS_PACKAGES" ] || {
  echo "no package list at $MHS_PACKAGES" >&2
  exit 1
}

# The two repositories MicroHs's Makefile.packages takes from git rather
# than from a release. mcabal cannot fetch those at a commit — its
# '--git-ref' expands to 'git clone --depth 1 --branch <ref>', which
# takes a branch or tag — so they are cloned here and built in place,
# which is the same build mcabal runs for a package it fetched itself.
MHS_GIT_NAMES="prettyprinter prettyprinter-ansi-terminal optparse-applicative"
# Space-separated: MHS_ALL_NAMES is matched as " name " below, and awk
# would otherwise hand each name over on its own line.
MHS_HACKAGE_NAMES=$(awk '{ print $1 }' "$MHS_PACKAGES" | tr '\n' ' ')
MHS_ALL_NAMES=" $MHS_HACKAGE_NAMES $MHS_GIT_NAMES "

[ -n "$MHS_HACKAGE_NAMES" ] || {
  echo "no packages in $MHS_PACKAGES" >&2
  exit 1
}

mhs() { "$MHS_HOME/bin/mhs" "$@"; }
mcabal() { CABALDIR="$MHS_HOME" MHS="$MHS_HOME/bin/mhs" "$MHS_HOME/bin/mcabal" "$@"; }

work=$(mktemp -d)
saved=
pkgs=
stamp="$MHS_HOME/.ychr-mhs-install"
restore() {
  case "$saved" in
    "") : ;;
    none) rm -f "$MHS_HOME/packages.txt" ;;
    *) mv "$saved" "$MHS_HOME/packages.txt" ;;
  esac
  # On a run that did not reach the stamp — a failure, or an interrupt —
  # put back the packages set aside for a version change, so the
  # environment is left as it was rather than a package short.
  if [ -d "$work/removed" ] && [ "$(cat "$stamp" 2>/dev/null || :)" != "${sig:-}" ]; then
    mv "$work/removed"/*.pkg "$pkgs/" 2>/dev/null || :
  fi
  rm -rf "$work"
}
trap restore EXIT

# The stamp records what this script installs: the three revisions, the
# git package names, the package list (whose Hackage names and versions
# both come from it) and the script itself, so any change to the installer
# re-provisions rather than being skipped by a stamp that still matches.
list_sig=$(cksum < "$MHS_PACKAGES")
self_sig=$(cksum < "$0")
sig="$MICROHS_REV $PRETTYPRINTER_REV $OPTPARSE_REV $MHS_GIT_NAMES $list_sig $self_sig"
if [ "$(cat "$stamp" 2>/dev/null || :)" = "$sig" ]; then
  echo "MicroHs environment already at the pinned revisions"
  exit 0
fi

# The toolchain, from a checkout at the pinned revision. Everything is
# built from that revision's sources rather than taken from the prebuilt
# artifacts it commits, which lag behind them:
#
#   * `bootstrap` is MicroHs's own self-hosting path. It builds the
#     committed bin/mhs, uses it to compile src/ to C, compiles that with
#     the C compiler, checks that a second round compiles identically and
#     leaves the fixed point in bin/mhs and generated/mhs.c. A C compiler
#     and make are the whole requirement: no Haskell compiler, no GHC.
#   * base is then rebuilt from lib/. Its committed generated/base.pkg
#     predates lib/Control/Exception.hs's type-variable-order fix to
#     `try`, and ychr does not typecheck against the old signature.
#   * `minstall` installs bin/{mhs,cpphs,mcabal}, the runtime, and the
#     base package just rebuilt. MCABAL is MicroHs's own install
#     directory variable; it defaults to ~/.mcabal, so passing MHS_HOME
#     is what makes an override work.
echo "Building and installing MicroHs $MICROHS_REV in $MHS_HOME"
git -C "$work" init --quiet
git -C "$work" remote add origin "$MICROHS_GIT"
git -C "$work" fetch --depth 1 --quiet origin "$MICROHS_REV"
git -C "$work" checkout --quiet --detach FETCH_HEAD
make -C "$work" bootstrap
CABALDIR="$MHS_HOME" MHS="$work/bin/mhs" \
  make -C "$work" generated/base.pkg
make -C "$work" minstall MCABAL="$MHS_HOME"

# mhs calls a package name with two versions installed ambiguous, and
# mcabal then reports it as missing, so every package this script
# installs is first set aside at whatever version is there — set aside,
# not deleted, so the trap can put it back if the run does not finish.
# The name is the file name without its "-<version>" tail, which is
# exact: a package whose name merely starts the same (ansi-terminal-types
# for ansi-terminal, prettyprinter-compat-* for prettyprinter) is a
# different name and keeps its file.
pkgs="$MHS_HOME/mhs-$(mhs --numeric-version)/packages"
for f in "$pkgs"/*.pkg; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .pkg | sed 's/-[0-9][0-9.]*$//')
  case "$MHS_ALL_NAMES" in
    *" $name "*)
      echo "  setting aside $name (reinstalling it below)"
      mkdir -p "$work/removed"
      mv "$f" "$work/removed/"
      ;;
  esac
done

echo "Installing the pinned package set"
if [ -f "$MHS_HOME/packages.txt" ]; then
  cp "$MHS_HOME/packages.txt" "$work/packages.txt.orig"
  saved="$work/packages.txt.orig"
else
  saved=none
fi
cp "$MHS_PACKAGES" "$MHS_HOME/packages.txt"

for name in $MHS_HACKAGE_NAMES; do
  echo "  $name"
  mcabal -q install "$name"
done

echo "  prettyprinter (pinned)"
git clone --quiet "$PRETTYPRINTER_GIT" "$work/prettyprinter"
git -C "$work/prettyprinter" checkout --quiet --detach "$PRETTYPRINTER_REV"
( cd "$work/prettyprinter/prettyprinter" && mcabal -q install )
( cd "$work/prettyprinter/prettyprinter-ansi-terminal" && mcabal -q install )

echo "  optparse-applicative (pinned)"
git clone --quiet "$OPTPARSE_GIT" "$work/optparse-applicative"
git -C "$work/optparse-applicative" checkout --quiet --detach "$OPTPARSE_REV"
( cd "$work/optparse-applicative" && mcabal -q install )

printf '%s\n' "$sig" > "$stamp"
echo "MicroHs environment ready in $MHS_HOME"
