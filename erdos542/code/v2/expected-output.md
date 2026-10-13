# Expected output and execution record

Version 2, 13 October 2026.

## C/Python reproduction (expected output; an independent run on all three certificates to N = 10^7 reproduced it byte for byte)

Run `sh code/v2/run.sh` from the bundle root. Requirements: GCC (or set `CC` to a compatible compiler), 64-bit `long`, signed `__int128`, Python 3, and NumPy. No LP solver is needed. The script restricts numerical libraries to one thread, builds in `code/v2/build/`, and runs the certificates sequentially. An optional first argument replaces the default finite limit of 10000000; 100000 is already sufficient with the certified tails. The two supplied Python files should be kept together.

For the default limit, the expected output is exactly:

```text
L=420 T0=40: exact check N<=10000000: nviol=0 namb=0; tail valid for N>=70483
  tau_upper <= 1.001890528110611 (rounded upward); K_c=2081454577/500000 <= 4162.909154
  VERIFIED: rho(n) <= 1.001890528110611 + 4162.909154/n for all n>=1
L=60 T0=40: exact check N<=10000000: nviol=0 namb=0; tail valid for N>=16255
  tau_upper <= 1.002711678024969 (rounded upward); K_c=127600737/200000 <= 638.003685
  VERIFIED: rho(n) <= 1.002711678024969 + 638.003685/n for all n>=1
L=12 T0=40: exact check N<=10000000: nviol=0 namb=0; tail valid for N>=5185
  tau_upper <= 1.004479665243758 (rounded upward); K_c=2091444/15625 <= 133.852416
  VERIFIED: rho(n) <= 1.004479665243758 + 133.852416/n for all n>=1
```

These are predictions from the exact certificate arithmetic, not a captured C/Python transcript from this write-up. The earlier independent reviews replayed all 420000000 pairs `(N,g)` through 10000000; a separate earlier verifier ran the C source with an alternative C compiler. The current environment has neither a C compiler nor Python.

`tail2.py` also supports direct invocation and optional JSON output. Its fields `tau_upper`, `K_c`, `Finf_lower`, `Psi`, and `R` rendered as binary floating-point numbers are supplementary diagnostic displays, not certified decimal inequalities. Its `tau_upper_exact` and `K_c_exact` are exact rational strings. `verify.py` uses those strings for every printed certified objective bound. The C program's `F~` and minimum-margin decimals are also supplementary; its proof decisions use integers only.

## Independent exact Node run (actually executed)

Run `node --single-threaded code/v2/audit.mjs > audit-rerun.json` from the bundle root. Node.js standard library only. Default limit: 100000. The stored `audit-output.json` is the actual output of that invocation. Resource fields can differ on another machine.

Checks performed:

- Nonnegative integer arrays, all divisor columns, 39 rows, denominator 1000000, and maximum numerator at most 1500031.
- Directed BigInt floor/ceiling enclosures for every `1 <= N <= 100000` and every divisor `g`: 600000 pairs for L=12, 1200000 for L=60, and 2400000 for L=420; zero violations and zero ambiguous cases.
- Independent direct-sum enclosures at N=1,2,5,11,40,41,997,2586 for every divisor class: 336 checks. The direct and incremental enclosures overlap, and each direct lower bound proves feasibility.
- All 42 tail rows, using an integer sawtooth recurrence, exact 40-term rational logarithm enclosures, and positive rational slack at the retained onsets 5185, 16255, and 70483. Also checks both conservative tail summary tables in the paper.
- Exact K values and upward objective roundings; all six pairwise crossovers among version 1 and the new decimal bounds; four comparisons against Chen's explicit bound, with exact endpoint polynomial signs.

The finite range overlaps all tails, so it suffices for all positive integers N. This run is independent code, not execution of the supplied C/Python programs. No floating-point inequality is used to accept a certificate. The earlier LP search and floating-point sanity checks remain supplementary and were not rerun.

## Source repair record

The two independently repaired copies of each source were compared byte for byte and agree. Their SHA-256 hashes are:

| File | SHA-256 of repaired source before the output change |
|---|---|
| check.c | `aff42f05d337f551827ec9a2fb1c4b27dfd520ad5e640af46cb4474ddbdb74fa` |
| verify.py | `ae7d28f1246bf9e072f1473395427dda6a1bfb56a84f3a0f1e070c0cfe363dc5` |
| tail2.py | `f21535d437b81c9d7e4b188db2f3478a04836c09159e77a2addca2d2e837386a` |

Reconstructing the original stored code blocks and replacing only actual newlines inside quoted strings by literal `\n` reproduces those repaired copies exactly: four replacements in `check.c`, five in `verify.py`, and zero in `tail2.py`.

`check.c` and `tail2.py` are deposited unchanged from those repaired copies. In `verify.py`, a private provenance tag was removed from the header comment. After that comment-only removal, `printing.patch` records the complete diff: import `Fraction`, add integer upward-decimal formatting, and replace the two objective-output lines. For rational p/q and decimal scale s, the formatter computes `-((-p*s)//q) = ceil(p*s/q)`. Fifteen places are used for tau_upper and six for K. It never converts to a binary float. The feasibility logic, tail logic, `ok` decision, and all certificate values are unchanged. The script and independent Node audit are additional reproduction aids.

## TeX build

No TeX engine is installed in the preparation environment, so a version 2 PDF and its page count are unavailable. `main.tex` is the version 2 manuscript. The nine-page `main-v1.pdf` preserves the earlier published PDF and must not be presented as version 2. On a TeX-equipped machine, run `latexmk -pdf main.tex`, inspect the result, and regenerate `SHA256SUMS` after adding the PDF. No PDF rebuild is claimed here.
