# A211417 — Bala's general divisibility conjecture

| file | Zenodo record | DOI | published | md5 (verified against the Zenodo record) | status |
|---|---|---|---|---|---|
| `A211417-Bala-general-divisibility.pdf` | 21995715 | [10.5281/zenodo.21995715](https://doi.org/10.5281/zenodo.21995715) | 2026-08-18 | `1972e572368b68af3979336ca9dfdd97` | **CURRENT — the only published version** |

## ⚠ The source here is AHEAD of the published PDF

`main.tex` and `A211417-Bala-Paper.md` carry a correction that the **published PDF
does not contain**. On 2026-08-23 three passages describing the computational
evidence for Corollary 3.8 were found to overstate their coverage: they said the
inequality `E(p,r) ≥ ⌊(r−1)/(30p)⌋ + 1` had been checked "for all primes and all
r ≤ 3200", when the check had actually been run at the six values
`r ∈ {100, 200, 400, 800, 1600, 3200}` (and, at each, for every prime `p` with
`7 ≤ p ≤ r`). A similar drift affected the description of the per-prime deficiency
check. The source files now state the six values.

**No corrected PDF has been published for this paper as of 2026-08-23.** The PDF in
this directory, and the artifact behind DOI 10.5281/zenodo.21995715, both predate
this fix and still contain the overstated sentences. Nothing about the mathematical
results changes — only the description of how far the computation was carried.
