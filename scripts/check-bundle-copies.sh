#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# lint/bundle-copies: the bundle's type is one module, bundle/Bundle.lean,
# copied into both shipped packages, which may have no Lake dependencies
# (DESIGN §4, constraint 6), under the module name the extractor gives it, so
# that the splicer's model and the extractor share it when the paper is
# built. The copies must be the source, byte for byte.
cd "$(dirname "$0")/.."
status=0
for copy in extract/Imprimatur/Bundle.lean splice/Imprimatur/Bundle.lean; do
  if ! cmp -s bundle/Bundle.lean "$copy"; then
    echo "lint/bundle-copies: $copy differs from bundle/Bundle.lean; run: cp bundle/Bundle.lean $copy" >&2
    status=1
  fi
done
exit $status
