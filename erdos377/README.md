# The density interpretation of Theorem 4 of Erdős, Graham, Ruzsa and Straus

Theorem 4 of Erdős–Graham–Ruzsa–Straus, *On the prime factors of C(2n,n)*, Math. Comp. 29 (1975) 83–92,
counts the m ≤ n^α that do not divide C(2n,n). As printed it has no "almost all n" qualifier, and the constant it says
tends to 1 is in fact the divisor constant. For each fixed 0 < α ≤ 1/2 this note proves natural-density limits for both
proportions, with an explicit alternating series of simplex integrals and an effective truncation bound. It shows that
no limit exists along all n, and gives certified rational enclosures at α = 1/2, 1/3, 1/4, 1/5
(e.g. c_N(1/2) ∈ [0.160401041573, 0.160401748642]). Nothing is claimed for 1/2 < α < 1. The note does not address
Erdős Problem #377 itself.

- Paper: [`main.pdf`](main.pdf) (source [`main.tex`](main.tex))
- DOI: pending
- Certificate program: [`code/density_intervals.py`](code/density_intervals.py) (exact rationals, Python 3 standard library);
  outputs [`code/density_4096.txt`](code/density_4096.txt) and [`code/density_16384.txt`](code/density_16384.txt);
  self-test [`code/check_convolution.py`](code/check_convolution.py); exact consistency checks [`code/revision_checks.js`](code/revision_checks.js) (Node).
- Reproduce: `python3 code/density_intervals.py --mesh 4096` (about 10 s) and `--mesh 16384` (a few minutes). Each
  reproduces the stored output byte for byte.
- Verification status: two cross-vendor referees (Claude Opus; the proof is by GPT-6 Astra), three rounds, final PASS;
  an independent verifier reproduced the certificates and checked the table and code. Literature: bounded search,
  10 October 2026, with no earlier correction or evaluation located (MathSciNet review not accessible). No Lean formalisation.
- Grade: small result (correction of a printed theorem, with explicit constants).

`SHA256SUMS` lists the published files.
