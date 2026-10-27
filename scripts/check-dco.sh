#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The Developer Certificate of Origin check (CONTRIBUTING.md, Licensing and
# sign-off): every commit in BASE..HEAD, apart from merges, must carry a
# `Signed-off-by:` trailer naming its author, as `git commit -s` writes it.
# The trailer is matched by the author's email: a squash merge made on
# GitHub keeps the sign-offs but writes the author's login as their name.
#
#   scripts/check-dco.sh BASE HEAD
set -euo pipefail
base=$1 head=$2
status=0
for c in $(git rev-list --no-merges "$base..$head"); do
  author=$(git log -1 --format='%an <%ae>' "$c")
  email=$(git log -1 --format='%ae' "$c")
  if ! git log -1 --format='%(trailers:key=Signed-off-by,valueonly)' "$c" | grep -qiF "<$email>"; then
    echo "dco: $(git log -1 --format='%h %s' "$c")"
    echo "  has no 'Signed-off-by: $author'"
    status=1
  fi
done
if [ $status = 1 ]; then
  echo
  echo "Sign off each commit with git commit -s; to add it to commits already made,"
  echo "run: git rebase --signoff $base, then push with --force-with-lease."
  echo "See CONTRIBUTING.md, Licensing and sign-off."
fi
exit $status
