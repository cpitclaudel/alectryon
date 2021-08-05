#!/usr/bin/env sh
# Check for incorrect commit IDs in
grep --only-matching "\[[a-z0-9, ]\+\]" "$1" |\
    grep --only-matching "[a-z0-9]\+" |\
    { while read -r sha; do
          if ! git merge-base --is-ancestor "$sha" HEAD 2>/dev/null; then
              echo "$sha is not an ancestor of HEAD";
              if git cat-file -e "$sha^{commit}" 2>/dev/null; then
                  msg=$(git log --format=%s -n 1 "$sha")
                  echo "          $msg"
                  git log --format="%h %s" | grep --fixed-strings "$msg" | sed 's/^/  /'
              fi
          fi
      done; }
