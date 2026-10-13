#!/bin/sh
# Reproduce the C/Python certificate verification. Default: the full original range.
set -eu
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 BLIS_NUM_THREADS=1
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
limit=${1:-10000000}
compiler=${CC:-gcc}
build="$here/build"
mkdir -p "$build"
"$compiler" -O2 -o "$build/check" "$here/check.c"
cd "$build"
for L in 420 60 12; do
    output=$(python3 "$here/verify.py" "$here/cert_L$L.json" "$limit")
    printf '%s\n' "$output"
    case "$output" in
        *'NOT VERIFIED'*) exit 1 ;;
        *'VERIFIED: rho(n)'*) ;;
        *) exit 1 ;;
    esac
done
