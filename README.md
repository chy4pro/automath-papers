# automath — machine-verified mathematics papers

Papers produced by an automated multi-agent research pipeline (Claude +
OpenAI Codex + cross-vendor adversarial review + Lean 4 formalization).

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
