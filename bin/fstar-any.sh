#!/bin/bash
if which greadlink >/dev/null 2>&1; then
  READLINK=greadlink
else
  READLINK=readlink
fi
FSTAR=$(dirname $($READLINK -f $0))/fstar.exe
if [ ! -f "$FSTAR" ]; then
  echo "fstar.exe not found"
  exit 1
elif file "$FSTAR" | grep Mono >/dev/null 2>&1; then
  mono --debug "$FSTAR" "$@" || exit 1
else
  "$FSTAR" "$@" || exit 1
fi
