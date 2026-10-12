# An explicit upper bound for reciprocal sums of sets with large pairwise least common multiples

For n ≥ 1 let ρ(n) be the maximum of Σ_{a∈A} 1/a over all sets A ⊆ {1,…,n} in which every two distinct
elements have least common multiple greater than n (Erdős Problem #542). This note proves
ρ(n) ≤ 1.0087578638 + 87.5686331624/n for every integer n ≥ 1. In particular ρ(n) ≤ 1.0170 for n ≥ 10625
and ρ(n) ≤ 1.01 for n ≥ 70499. As n → ∞ this improves the leading constant 1.0170166 of Y.-G. Chen (1996),
the strongest bound we located in a literature search of 12 October 2026. For 70 ≤ n ≤ 8871, Chen's explicit
bound 1.0170166 + 14.21/(n − 58) remains smaller. The proof is weak LP duality with dual weights that depend
on m/n and on gcd(m,6). It is certified by 67 dyadic rationals checked in exact integer and rational
arithmetic. The conjecture ρ(n) ≤ 1 + o(1) is not proved, and the constant is not claimed to be sharp.

- Paper: [`main.pdf`](main.pdf) (source [`main.tex`](main.tex), 9 pages)
- DOI: [10.5281/zenodo.23311400](https://doi.org/10.5281/zenodo.23311400)
- Certificate: [`code/cert_main.txt`](code/cert_main.txt) (67 nonzero entries, also printed in Appendix A of
  the paper; SHA-256 `361c296fad7662dadc53699aead4f2eb33fdbff7e0d18efd3971535acec8534e`)
- Exact verifier: [`code/verify.py`](code/verify.py) (Python 3 standard library; integers and
  `fractions.Fraction` only), output [`code/verify_output.txt`](code/verify_output.txt).
  Independent cross-check for concrete n: [`code/crosscheck.py`](code/crosscheck.py), output
  [`code/crosscheck_output.txt`](code/crosscheck_output.txt).
  The rounding step that produced the certificate from a floating-point LP solution is
  [`code/mkcert.py`](code/mkcert.py). It is not part of the proof, and it needs NumPy and the LP output,
  which is not included.
- Reproduce, from this directory:
  - `python3 code/verify.py code/cert_main.txt` takes about 2 CPU s and 72 MiB and ends with `RESULT OK`.
    It reproduces the stored output except for the last line, which reports the CPU time.
  - `python3 code/crosscheck.py code/cert_main.txt 1 2 5 11 100 997 1000 5040 20011` takes about 0.5 s
    and reproduces the stored output byte for byte, ending with `CROSSCHECK OK`.
  - `SOURCE_DATE_EPOCH=1791763200 FORCE_SOURCE_DATE=1 latexmk -pdf main.tex` rebuilds `main.pdf`.
    With TeX Live 2026 the result is byte-identical.
- Verification status: the result was found by a Claude Opus 5.5 agent (Anthropic). Two cross-vendor referees
  (GPT-6 Astra, OpenAI) reviewed it. The first round required repairs: an exact-arithmetic verifier replaced
  a floating-point check, and decimals are now rounded outward. Both referee reports returned
  PASS-WITH-REPAIRS, and all requested repairs have been made. One referee carried out the repair
  confirmation, re-verified the certificate exactly with an independent program, and again returned
  PASS-WITH-REPAIRS with a single wording correction, now applied (not re-reviewed). Each referee recomputed
  the finite check with an independent implementation. A separate Claude verifier checked the certificate
  exactly, against the first version of the report and again on the final files; both checks passed.
  Literature: bounded search, 12 October 2026; not exhaustive (one citation index was rate-limited, another
  did not resolve Chen's 1996 paper, and the community chat archive was searched only in part).
  No Lean formalisation.
- Grade: small result (an improved explicit constant for a known bound).

`SHA256SUMS` lists the published files (paper, code, this README and the Zenodo description).
