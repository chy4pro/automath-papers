# An explicit upper bound for reciprocal sums of sets with large pairwise least common multiples

**Version 2, 13 October 2026; supersedes version 1.** Prepared for a new version of the same record; this bundle has not been uploaded or pushed during preparation.

For every integer n ≥ 1, let ρ(n) be the maximum of Σ(1/a) over A ⊆ {1,…,n} with lcm(a,b) > n for distinct members. This version proves all three bounds:

| Modulus | Bound for every n ≥ 1 | Exact coefficient K before rounding |
|---|---|---|
| 420 | ρ(n) ≤ 1.00189053 + 4162.91/n | 2081454577/500000 |
| 60 | ρ(n) ≤ 1.00271168 + 638.004/n | 127600737/200000 |
| 12 | ρ(n) ≤ 1.00447967 + 133.853/n | 2091444/15625 |

The leading constant improves the strongest bound we located in a literature search of 12 October 2026, including our own version 1 and Chen (1996). This was a bounded search, not a priority determination. The contribution is three specific periodic weight certificates and their numerical costs; weighted counting over disjoint multiple sets is prior methodology. The conjecture ρ(n) ≤ 1 + o(1) is not proved. No general limit-LP theorem is stated.

- Version 2 manuscript: [`main.tex`](main.tex). Build with `latexmk -pdf main.tex`.
- Version 2 paper: [`main.pdf`](main.pdf), 8 pages, built from `main.tex` with pdfTeX 1.40.29 (TeX Live 2026).
- Archived version 1: [`main-v1.pdf`](main-v1.pdf), 9 pages. This is the earlier published PDF, not version 2. Its code and certificate are preserved byte for byte in [`code/v1/`](code/v1/).
- Published: version 2 [10.5281/zenodo.23328540](https://doi.org/10.5281/zenodo.23328540) (13 October 2026); version 1 [10.5281/zenodo.23311400](https://doi.org/10.5281/zenodo.23311400); all versions [10.5281/zenodo.23311399](https://doi.org/10.5281/zenodo.23311399).
- Version 2 certificates: [`cert_L420.json`](code/v2/cert_L420.json), [`cert_L60.json`](code/v2/cert_L60.json), [`cert_L12.json`](code/v2/cert_L12.json), with 282, 167 and 99 nonzero integer numerators respectively; all denominators are 1000000.
- C/Python verifier: [`check.c`](code/v2/check.c), [`verify.py`](code/v2/verify.py), [`tail2.py`](code/v2/tail2.py). Run `sh code/v2/run.sh`. Requires a C compiler with signed 128-bit integers, 64-bit `long`, Python 3, and NumPy. No solver is required. An independent check compiled `check.c` and ran `verify.py` on all three certificates up to N = 10^7; the output equals the block in `code/v2/expected-output.md`.
- Independent exact Node audit: [`audit.mjs`](code/v2/audit.mjs), actual output [`audit-output.json`](code/v2/audit-output.json). Run `node --single-threaded code/v2/audit.mjs`. The default finite range is 100000 and overlaps every tail. All 4200000 finite pairs, 42 tails and 336 direct checks passed. No floating-point decision is used.
- [`Expected output and repairs`](code/v2/expected-output.md) distinguishes the pending C/Python replay from checks actually performed, records source agreement and the four C/five Python escape repairs, and explains [`printing.patch`](code/v2/printing.patch). Certified output is now rounded upward from exact rational strings; feasibility logic is unchanged.
- [`zenodo_description.html`](zenodo_description.html) is prepared deposit metadata. [`SHA256SUMS`](SHA256SUMS) covers all deposited files except itself.

The corrected L=420 tail values are Ψ₁ = 3518369257/52500000 and R₁ = 232154535249/50000, retaining onset 70483. The onsets for L=60 and 12 remain 16255 and 5185. Two independent proof reviews returned PASS-WITH-REPAIRS, and a separate exact verifier check passed. The documentary repairs are incorporated; the updated C/Python wrapper has not been executed in this preparation environment. Floating-point experiments are supplementary. No formal proof-assistant verification is claimed.

Version 1 remains the valid bound B₀(n) = 1.0087578638 + 87.5686331624/n. Each new displayed bound is strictly smaller than B₀ precisely for n ≥ 10819 (L=12), n ≥ 91039 (L=60), and n ≥ 593439 (L=420), respectively. The manuscript gives exact rational crossings for every pair, and comparisons with Chen's bound. The smallest of the four displayed bounds is:

| Integer range | Smallest bound |
|---|---|
| 1–10818 | version 1 |
| 10819–285154 | L=12 |
| 285155–4292645 | L=60 |
| n ≥ 4292646 | L=420 |

The literature search retained access limits: one citation index was rate-limited, another did not resolve Chen's 1996 record, and community discussion archives were searched only in part. This remains a small result: an improved explicit constant for a known bound.
