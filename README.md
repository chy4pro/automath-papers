# automath — machine-verified mathematics papers

Papers produced by an automated multi-agent research pipeline (Claude +
OpenAI Codex + cross-vendor adversarial review + Lean 4 formalization).

The Lean 4 proof library formerly at `lean/` has migrated to its own
repository: [chy4pro/automath-lean-proofs](https://github.com/chy4pro/automath-lean-proofs)
(history preserved in this repo's git log; see `lean/README.md`).

## Erdős Problem #34 — explicit upper and lower bounds for distinct consecutive sums in permutations (important milestone)

**Claim.** Let f(n) be the maximum, over permutations of {1,…,n}, of the number of distinct consecutive sums. Then
f(n) ≤ 0.4435834 n² + 1100 n for every n ≥ 1 (so f(n) ≤ 0.4436 n² for n ≥ 66,265,061). For every prime p ≥ 2^16 an explicit
complementary-triple permutation of length 3p has at least (803/288)p² − 50000 p^{7/4}(log p+3)^8 distinct sums, hence
≥ 0.309799 (3p)² for p ≥ 2^416; with Dusart's prime-interval theorem, f(n) ≥ 0.309799 n² for every n ≥ 2^4096. This improves
both coefficients of the strongest bounds we located (Konieczny: 3/2 − 2/√e ≈ 0.28694 and 1/4 + π/16 ≈ 0.44635); bounded search,
no priority claim. The lower bound's onset is astronomically large.

- Paper and code: [`erdos34/`](erdos34/) — DOI [10.5281/zenodo.23322918](https://doi.org/10.5281/zenodo.23322918)
- Status: two cross-vendor referees per bound (PASS), independent exact verifier (PASS; wording repair applied), transcription check; bounded literature search; no Lean

## Erdős Problem #1179 — balanced random subset sums with explicit corrections (important milestone)

**Claim.** For every finite abelian group of order N, q = log₂N: k = ⌈q + 1000q/log₂q⌉ (N ≥ 2^(2^20)), k = ⌈q + 3400q^{4/5}⌉
(N ≥ 2^64) and every k ≥ q + 8400√(q log₂q) (N ≥ 2^64; 200 in place of 8400 for N ≥ 2^486018750) random elements make all
subset-sum counts within a factor 1 ± 1/2 of 2^k/N, with failure probability ≤ 1/(2q) (independent entries) or ≤ 1/q
(uniform k-subset; k ≤ 2^(q/2) for the last statement). Explicit constants and onsets; Erdős–Hall (1976) gave the
qualitative q(1 + O(log log q/log q)). Each bound beats the trivial 2q + log₂q + 3 only in the range stated in the paper.

- Paper and code: [`erdos1179/`](erdos1179/) — DOI [10.5281/zenodo.23322923](https://doi.org/10.5281/zenodo.23322923)
- Status: two cross-vendor referees per proof (PASS / PASS-WITH-REPAIRS, repairs applied and re-verified), exact verifier, transcription check; bounded literature search (Hall 1977 not accessible); no Lean

## Erdős Problem #542 — explicit upper bound for reciprocal sums of lcm-separated sets (small result)

**Claim (version 2).** If A ⊆ {1,…,n} and lcm(a,b) > n for all distinct a, b ∈ A, then Σ_{a∈A} 1/a ≤ 1.00189053 + 4162.91/n
for every n ≥ 1 (periodic weak-duality certificate at modulus 420, exact check to 10^7 plus a proved tail; also
1.00271168 + 638.004/n and 1.00447967 + 133.853/n at moduli 60 and 12). Version 1 proved 1.0087578638 + 87.5686331624/n
(leading constant below Chen's 1.0170166 from 1996). The conjecture ρ(n) ≤ 1 + o(1) is not proved.

- Paper and code: [`erdos542/`](erdos542/) — version 2 DOI [10.5281/zenodo.23328540](https://doi.org/10.5281/zenodo.23328540), version 1 [10.5281/zenodo.23311400](https://doi.org/10.5281/zenodo.23311400), all versions [10.5281/zenodo.23311399](https://doi.org/10.5281/zenodo.23311399)
- Status: version 2 — two cross-vendor referees (PASS-WITH-REPAIRS, documentary repairs applied), exact verifier replay, transcription check; bounded literature search; no Lean

## Erdős–Graham–Ruzsa–Straus 1975, Theorem 4 — density interpretation (small result)

**Claim.** For each fixed 0 < α ≤ 1/2, the proportions of m ≤ n^α that divide / do not divide C(2n,n) converge in
natural density to explicit constants (alternating simplex-integral series, effective truncation); no limit exists along
all n; certified enclosures at α = 1/2, 1/3, 1/4, 1/5. This corrects the printed Theorem 4 (missing almost-all qualifier;
the constant tending to 1 is the divisor constant). It does not address Erdős Problem #377 itself.

- Paper and code: [`erdos377/`](erdos377/) — DOI [10.5281/zenodo.23274211](https://doi.org/10.5281/zenodo.23274211)
- Status: two cross-vendor referees (three rounds, PASS), verifier reproduction; bounded literature search; no Lean

## A211417 — Bala's general divisibility conjecture (resolved)

**Claim.** For the integral factorial ratio sequence
a(n) = (30n)! n! / ((15n)! (10n)! (6n)!) (OEIS A211417) and every r ≥ 1,
there is an explicit D(r) > 0 such that D(r)·a(n) is divisible by
∏ (30n − i) over 1 ≤ i ≤ r with gcd(i, 30) = 1, for all n ≥ 0.

- Paper: [`a211417/A211417-Bala-general-divisibility.pdf`](a211417/A211417-Bala-general-divisibility.pdf) (~29 pp, explicit sharp D(r) = ∏ p^E(p,r), plus the sister family C(k,r), k = 2,3,5)
- DOI: [10.5281/zenodo.21995715](https://doi.org/10.5281/zenodo.21995715)
- Lean 4 formalization: [google-deepmind/formal-conjectures PR #5023](https://github.com/google-deepmind/formal-conjectures/pull/5023) — 0 sorry among added declarations, axioms {propext, Classical.choice, Quot.sound}, compiled under the repository's own toolchain
- Verification suite: [`a211417/a211417_verify.py`](a211417/a211417_verify.py)
- **Note:** `a211417/main.tex` and `a211417/A211417-Bala-Paper.md` carry a
  correction (the computational coverage for Corollary 3.8 is six values of `r`,
  not all `r <= 3200`) that the **published PDF does not contain**; no corrected
  PDF has been published. See [`a211417/README.md`](a211417/README.md).
- Prior work: r = 1 case by AlphaProof Nexus (FC PR #5010); an unpublished general claim is discussed honestly in the paper's §7 (no public proof text known as of 2026-08-17)

All results carry per-theorem verification status (dual cross-vendor review + Lean / computational).

## Lean 4 proof library (`lean/`)

Kernel-checked Lean 4 proofs from the same pipeline. Each file compiles under
`leanprover/lean4:v4.34.0-rc1` + mathlib `v4.34.0-rc1` (manifest included),
contains **no `sorry`**, and `#print axioms` for every main theorem reports only
`propext`, `Classical.choice`, `Quot.sound`.

| File | Result | Status |
|---|---|---|
| `A108211.lean` (509 lines) | OEIS A108211 floor formula `a(n) = ⌊1/(1/(4n) − log 2 + H(2n) − H(n))⌋` for all `n ≥ 1` | open upstream as of 2026-08-18 |
| `A114362.lean` (577 lines) | Ordowski's conjecture 2 (A114362/A348829): `(1−t(n))/(1+t(n)) = 2^{−n}+3^{−n}+5^{−n}+7^{−n}+O(11^{−n})`, `t(n)=ζ(2n)/ζ(n)²` | open upstream as of 2026-08-18 |
| `A100434.lean` (282 lines) | Dement's three identities for A100434, proved for the sign-corrected `b` (the upstream formalization has a sign error — see [formal-conjectures issue #5025](https://github.com/google-deepmind/formal-conjectures/issues/5025)) | open upstream as of 2026-08-18 |
| `A211417.lean` (607 lines) | Bala's general divisibility conjecture, all `r ≥ 1` (strong form `D > 0`) | submitted upstream as [PR #5023](https://github.com/google-deepmind/formal-conjectures/pull/5023) |
| `A114831.lean` (327 lines) | `a(n+1)/a(n) → √3` for A114831 | **independent proof; priority belongs to [KitaKen1](https://github.com/KitaKen1/oeis-a114831-asymptotic)** ([FC PR #4969](https://github.com/google-deepmind/formal-conjectures/pull/4969), opened 2026-08-15, merged 2026-08-16, before this pipeline produced its proof) |
| `Fernandes.lean` (507 lines) | Fernandes (arXiv:2605.12342) Conjecture 1: the parity subgroup of `Sym m × Sym n` is 2-generated outside the four exceptional pairs | **independent proof; priority belongs to [KitaKen1](https://github.com/KitaKen1)** ([FC PR #4868](https://github.com/google-deepmind/formal-conjectures/pull/4868), opened 2026-08-11, before this pipeline started) |

To build: place the `.lean` files in a lake project with the included
`lakefile.toml` / `lake-manifest.json` / `lean-toolchain` and run `lake build`.

AI Usage Disclosure: all proofs were produced by an automated multi-agent
pipeline (Claude + OpenAI models) with cross-vendor adversarial review;
statements were checked against their sources by the pipeline operator.

## OEIS quartet — A100434, A108211, A114362, A114831 (paper)

Machine-verified resolutions of four OEIS conjectures, each with a full Lean 4
formalization (see `lean/`). [`batch1/OEIS-quartet-A100434-A108211-A114362-A114831.pdf`](batch1/OEIS-quartet-A100434-A108211-A114362-A114831.pdf) (25 pp).
DOI: [10.5281/zenodo.21995453](https://doi.org/10.5281/zenodo.21995453).
A114831: independent, essentially simultaneous proof — priority ceded to
K. Kitamura (FC PR #4969); the other three are, to our knowledge, unclaimed
upstream as of 2026-08-18.

## Fernandes conjecture (arXiv:2605.12342, Conjecture 1) — independent proof (paper)

[`fernandes/Fernandes-conjecture1-independent-proof.pdf`](fernandes/Fernandes-conjecture1-independent-proof.pdf) (14 pp) + `Fernandes.lean` (507 lines, 0 sorry).
DOI: [10.5281/zenodo.21995604](https://doi.org/10.5281/zenodo.21995604).
Priority for the formal resolution belongs to K. Kitamura (FC PR #4868,
opened 2026-08-11); our proof and formalization were found independently and
are recorded for their expository value (Goursat + normal-quotient
classification argument).

## Structure Theory of Finite 677 Magmas (working paper) — current: v8_2

[`etp677_structure/Structure-Theory-of-Finite-677-Magmas-v8_2.pdf`](etp677_structure/Structure-Theory-of-Finite-677-Magmas-v8_2.pdf) (~110 pp).
DOI: [10.5281/zenodo.22070405](https://doi.org/10.5281/zenodo.22070405)
(concept DOI, always latest: [10.5281/zenodo.21995799](https://doi.org/10.5281/zenodo.21995799)).
Partial-results working paper on the last open finite implication of Tao's
Equational Theories Project (E677 => E255): structure theorems, a nine-model
zoo (including the order-77 minimal non-right-cancellative models m77/m77D),
refutations of the transport/kernel-law programme, the round-9/round-10 extremal
branch, and an honest paper-wide retraction chain. Every numbered claim carries a
verification marker (proved / machine-verified / computational / partial /
conjecture). The main implication (P) remains OPEN.

v8_2 is a correction release: it removes a fabricated quotation that v8 attributed
to an independent third-party project, corrects two misprinted real-person author
names in a reference, downgrades an uncertified SAT computation from a certified
marker, and withdraws an overstated verification claim. **Read v8_2.**
Earlier published versions (v8, v7.2) are kept in the directory because they carry
their own DOIs; see [`etp677_structure/README.md`](etp677_structure/README.md) for
the full version table with per-file md5s.

`etp677_structure/main.tex` is the source of the published v8_2 PDF, verified by
recompilation.

## WOWII-61 — Graffiti conjecture 61 (partial results) — current: v2

[`wowii61/Partial-Results-WOWII-61-Graffiti-v2.pdf`](wowii61/Partial-Results-WOWII-61-Graffiti-v2.pdf) (44 pp).
DOI: [10.5281/zenodo.22069069](https://doi.org/10.5281/zenodo.22069069)
(concept DOI, always latest: [10.5281/zenodo.22054650](https://doi.org/10.5281/zenodo.22054650)).
`residue(G) + ceil(diam(G)/3) <= f(G)`: not resolved. Unconditional for
`diam(G)` in {1,2,3,5,6,9}; at diameter 4 reduced to a dichotomy, of which
`tau <= 3` is settled.

v2 is a correction release: seven statements that v1 marked "certified: two review
rounds" did not have that review history and are re-marked as elementary
arguments given in full; the `tau = 3` claim is qualified as a skeleton rather than
a complete case analysis. **Read v2.** v1 (DOI
[10.5281/zenodo.22054651](https://doi.org/10.5281/zenodo.22054651)) is kept in the
directory because it was published, and should not be relied on. See
[`wowii61/README.md`](wowii61/README.md).

## WOWII-133 — Graffiti conjecture 133 (partial results)

[`wowii133/Partial-Results-WOWII-133-Graffiti.pdf`](wowii133/Partial-Results-WOWII-133-Graffiti.pdf).
DOI: [10.5281/zenodo.22054835](https://doi.org/10.5281/zenodo.22054835).
Only version; no correction has been published. See
[`wowii133/README.md`](wowii133/README.md).
