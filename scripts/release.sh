#!/bin/bash
set -e
if ! git diff-index --quiet HEAD --; then
  echo "Please commit all changes first" >&2
  exit 1
fi
VERSION=$(grep '^version' Cargo.toml | cut -d '"' -f2)
TAG="v$VERSION"
if git tag | grep "$TAG"; then
  echo "$VERSION appears to have already been released" >&2
  exit 1
fi
git pull --rebase
cargo build
cargo test --all
cargo publish
git tag "$TAG"
git push --tags
