DONE — complete paper source and public description prepared; independent source-formula audit PASS. TeX compilation is assigned to the coordinator and was not run in this task.

# Interval capacity and second-order bounds for distinct-difference configurations

- `main.tex`: self-contained article, using the same standard packages as the ordinary Sidon paper.
- `zenodo_description.html`: public metadata, with exact bounds and scope qualifications.
- Licence: CC0 1.0.

The headline is the cosine sonar bound: for every integer n ≥ 160³, a sonar sequence with n rows and m columns satisfies

m ≤ n + 3(π²/36)^(1/3) n^(2/3) + 4 n^(1/3).

The note also includes the triangular sonar bound (+2n^(2/3)+3n^(1/3), n≥48³), weak Sidon, bounded difference multiplicity, difference triangle sets, Manhattan configurations, general integer boxes, and the all-N square supplement with coefficient (8/3)^(1/3) and remainder 18N^(1/3). Every explicit theorem retains its domain, diagonal convention, onset and remainder from the corresponding proof.

The horizontal functional has attained optimum π²/32 for autocorrelations of nonnegative factors. The explicit perturbation proves a strictly smaller value in the full nonnegative positive-definite class. Its exact infimum remains open. The paper makes no barrier claim for arbitrary two-dimensional kernels.

## Mathematical source map

The English proofs and exact checkers are in the repository directory `problems/capacity_transfer/`:

| Paper section | Proof sources |
| --- | --- |
| 1, exact statements | REPORT.md and the individual proof notes |
| 2, signed certificate | COMMON_CAPACITY.md; the matching typeset analytic proof in the ordinary Sidon paper |
| 3, sonar and functional | SONAR.md, SONAR_COSINE.md, KERNEL_FUNCTIONAL.md, KERNEL_PERTURBATION.md |
| 4, scalar corollaries | WEAK_SIDON.md, G_THIN.md, DIFFERENCE_TRIANGLES.md |
| 5, product kernels | MANHATTAN.md, BOXES.md, BOXES_ALL_N.md |
| Bibliographic comparisons | G2_TRANSFER_20261002.md and the corrections in the associated source audit |

Comparisons distinguish primary readings, secondary quotations and unread relevant sources. The weak-Sidon citation is to BFR arXiv version 2. The DTS and square comparisons are secondary. The main Chen–Kløve 1996 theorem, Robinson's sonar discussion, and the Caicedo thesis remain access gaps. No novelty or priority claim is made.

## Review and formalisation status

The proofs were written by GPT-6 Astra from a Claude scout's outline, with new explicit remainders, the cosine analysis and the admissible perturbation. Independent OpenAI in-team reviews were followed by isolated Claude mathematical reports:

- REFEREE_SONAR_CLAUDE_A_20261002.md: cosine sonar theorem, capacity input and functional inequalities PASS; scope and editorial repairs applied.
- REFEREE_1D_CLAUDE_20261002.md: weak Sidon, g-thin and DTS PASS.
- REFEREE_2D_CLAUDE_20261002.md: triangular sonar, Manhattan, general boxes, kernel admissibility and functional inequalities PASS; perturbed sonar PASS with editorial repairs applied.

The all-N square supplement has in-team review and manuscript formula checking; it was not included in the Claude referees' file lists. The scout's initial ideas and the Claude reviewers share a vendor; the review of the Astra proofs and repairs is cross-vendor. No human referee report is claimed.

`\RefereeStatus` near the top of `main.tex` holds the current referee summary for the coordinator to update. The description's corresponding review paragraph is already factual and usable as written.

Only the earlier ordinary Sidon bound, with coefficient 2√2/3, additive 1 and onset 120⁴, has been Lean-checked. None of the new transfers, kernel functional claims or analytic arguments in this note is claimed to be formalised.

## Checks and their limits

All nine dependency-free Node checkers in the proof directory were executed and passed in the proof task. They cover exact marginal identities, lattice formulas, combinatorial difference accounting, rational error envelopes, onsets and scalar algebra. The six principal combinatorial checkers record 127840 energy-accounting cases; the all-N supplement additionally records 3180 window identities, 1194 Sidon energy inequalities and 1004 ceiling checks.

These counts are not numerical evidence for the capacity step. The Manhattan and box scripts do not evaluate the capacity certificate. The small-parameter sonar sandwich tests use a generous exponential term and cannot meaningfully stress that step. The capacity inequality rests on the self-contained analytic proof. The referees report additional floating-point capacity tests; these are not proofs and were not rerun for the manuscript.

A structural source check passed: balanced environments and braces, 86 unique labels, 70 resolved internal references, 10 bibliography entries and 16 resolved citations. Metadata/privacy marker checks also passed. These are source checks, not a TeX compilation or a mathematical proof. A separate informed OpenAI reviewer independently compared every display in all six sections with the proof notes and returned PASS, then checked the README and corrected HTML quantifiers. Compilation and PDF inspection remain with the coordinator, as requested.

Audited `main.tex` SHA-256: `8f502fa6d4adc47591ea0f94fba4003345fda867ffd43ae1da612b09b7bffcb1`.

No publication, upload, repository push, dependency installation or local TeX compilation was performed by this task.
