# automath — machine-verified mathematics papers

Papers produced by an automated multi-agent research pipeline (Claude +
OpenAI Codex + cross-vendor adversarial review + Lean 4 formalization).

The Lean 4 proof library formerly at `lean/` has migrated to its own
repository: [chy4pro/automath-lean-proofs](https://github.com/chy4pro/automath-lean-proofs)
(history preserved in this repo's git log; see `lean/README.md`).

## A211417 — Bala's general divisibility conjecture (resolved)

**Claim.** For the integral factorial ratio sequence
a(n) = (30n)! n! / ((15n)! (10n)! (6n)!) (OEIS A211417) and every r ≥ 1,
there is an explicit D(r) > 0 such that D(r)·a(n) is divisible by
∏ (30n − i) over 1 ≤ i ≤ r with gcd(i, 30) = 1, for all n ≥ 0.

- Paper: [`a211417/A211417-Bala-general-divisibility.pdf`](a211417/A211417-Bala-general-divisibility.pdf) (~29 pp, explicit sharp D(r) = ∏ p^E(p,r), plus the sister family C(k,r), k = 2,3,5)
- Lean 4 formalization: [google-deepmind/formal-conjectures PR #5023](https://github.com/google-deepmind/formal-conjectures/pull/5023) — 0 sorry among added declarations, axioms {propext, Classical.choice, Quot.sound}, compiled under the repository's own toolchain
- Verification suite: [`a211417/a211417_verify.py`](a211417/a211417_verify.py)
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
A114831: independent, essentially simultaneous proof — priority ceded to
K. Kitamura (FC PR #4969); the other three are, to our knowledge, unclaimed
upstream as of 2026-08-18.

## Fernandes conjecture (arXiv:2605.12342, Conjecture 1) — independent proof (paper)

[`fernandes/Fernandes-conjecture1-independent-proof.pdf`](fernandes/Fernandes-conjecture1-independent-proof.pdf) (14 pp) + `Fernandes.lean` (507 lines, 0 sorry).
Priority for the formal resolution belongs to K. Kitamura (FC PR #4868,
opened 2026-08-11); our proof and formalization were found independently and
are recorded for their expository value (Goursat + normal-quotient
classification argument).

## Structure Theory of Finite 677 Magmas (working paper, v7.2)

[`etp677_structure/Structure-Theory-of-Finite-677-Magmas-v7.2.pdf`](etp677_structure/Structure-Theory-of-Finite-677-Magmas-v7.2.pdf) (~90 pp).
Partial-results working paper on the last open finite implication of Tao's
Equational Theories Project (E677 ⇒ E255): structure theorems, a nine-model
zoo (including the order-77 minimal non-right-cancellative models m77/m77D),
refutations of the transport/kernel-law programme, and an honest paper-wide
retraction chain. Every numbered claim carries a verification marker
(proved / machine-verified / computational / conjecture). Adversarial review:
round 1 INVALID → repairs v7.1/v7.2 → round 2 CLEAN (cross-vendor, 2026-08-18).
The main implication (P) remains OPEN.
