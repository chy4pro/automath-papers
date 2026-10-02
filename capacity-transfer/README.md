## Repairs applied — 2026-10-02 (task 040b)

- R1–R4: stated the triangular scale `T = V`; replaced undefined `a_y,b_y` with `a_2,b`; defined the horizontal factors and the general signed-kernel energy notation in Section 3.
- R5–R6: stated the unit-mass normalization in the abstract and corrected the central perturbation term's variation bound from 2 to 4. The displayed total variation bound is unchanged.
- R7–R9: specified the second-order terms in the source comparisons, added the exact integer threshold `N ≥ 32433` for comparison with the attributed all-N square bound, and limited the functional conclusion to the AM–GM minimum of the stated leading expression.
- R10–R11: corrected same-vendor review wording and recorded the fourth isolated Claude report, the whole-paper **PASS-WITH-REPAIRS**, with its repairs applied. Claude also supplied the original scout derivations; the reviews are cross-vendor relative to Astra's proofs, not vendor-independent of the scout.
- R12: introduced `k = |A|` and the strong Sidon hypothesis in the all-N square proof.
- Optional E2–E4 and E6–E9: removed the dimension/difference symbol clash, added capacity and theorem references, explained the sonar coefficient comparison, removed defensive wording and an internal workflow comment, clarified Lean scope, and located the checkers. Broader symbol renaming and a reformulation of the all-N theorem were left out to preserve the mathematical statements; the elementary all-N bound already appears in its proof.

All theorem, lemma and proposition statements and their constants are unchanged. The adjacent threshold signs at `N = 32432,32433` were independently certified with BigInt rational cube-root brackets of denominator `10^30`; convexity below `x = 17` and strict monotonicity above it prove the claimed threshold over all positive integer N. The referee's other floating-point and exhaustive tests remain reported referee work, not newly reproduced tests.

DONE — paper-level repairs applied to the source and public description. TeX compilation and publication remain assigned to the coordinator; neither was performed in this task.

# Interval capacity and second-order bounds for distinct-difference configurations

- `main.tex`: self-contained article, using the same standard packages as the ordinary Sidon paper.
- `zenodo_description.html`: public metadata, with exact bounds and scope qualifications.
- Licence: CC0 1.0.

The headline is the cosine sonar bound: for every integer n ≥ 160³, a sonar sequence with n rows and m columns satisfies

m ≤ n + 3(π²/36)^(1/3) n^(2/3) + 4 n^(1/3).

The note also includes the triangular sonar bound (+2n^(2/3)+3n^(1/3), n≥48³), weak Sidon, bounded difference multiplicity, difference triangle sets, Manhattan configurations, general integer boxes, and the all-N square supplement with coefficient (8/3)^(1/3) and remainder 18N^(1/3). Every explicit theorem retains its domain, diagonal convention, onset and remainder from the corresponding proof.

The horizontal functional has attained optimum π²/32 for autocorrelations of nonnegative unit-mass factors. The explicit perturbation proves a strictly smaller value in the full nonnegative positive-definite unit-mass class. Its exact infimum remains open. The paper makes no barrier claim for arbitrary two-dimensional kernels.

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

The proofs were written by GPT-6 Astra (OpenAI) from a Claude (Anthropic) scout's outline, with new explicit remainders, the cosine analysis and the admissible perturbation. Separate same-vendor (OpenAI) reviews in the same workflow were followed by four isolated Claude mathematical reports:

- REFEREE_SONAR_CLAUDE_A_20261002.md: cosine sonar theorem, capacity input and functional inequalities PASS; scope and editorial repairs applied.
- REFEREE_1D_CLAUDE_20261002.md: weak Sidon, g-thin and DTS PASS.
- REFEREE_2D_CLAUDE_20261002.md: triangular sonar, Manhattan, general boxes, kernel admissibility and functional inequalities PASS; perturbed sonar PASS with editorial repairs applied.
- REFEREE_PAPER_CLAUDE_20261002.md: the whole paper, including the all-N square supplement, PASS-WITH-REPAIRS; no mathematical error found in any theorem, proposition or lemma. All twelve required notational and wording repairs are applied.

The all-N square supplement has same-vendor review, manuscript formula checking and the whole-paper Claude review. The scout's initial ideas and the Claude reviewers share a vendor; the reviews of the Astra proofs and repairs are cross-vendor. No vendor-independent or human referee report is claimed.

`\RefereeStatus` near the top of `main.tex` and the description's provenance paragraph both record these four reports and the applied repairs.

Only the earlier ordinary Sidon bound, with coefficient 2√2/3, additive 1 and onset 120⁴, has been Lean-checked. None of the new transfers, kernel functional claims or analytic arguments in this note is claimed to be formalised.

## Checks and their limits

All nine dependency-free Node checkers in the proof directory were executed and passed in the proof task. They cover exact marginal identities, lattice formulas, combinatorial difference accounting, rational error envelopes, onsets and scalar algebra. The six principal combinatorial checkers record 127840 energy-accounting cases; the all-N supplement additionally records 3180 window identities, 1194 Sidon energy inequalities and 1004 ceiling checks.

These counts are not numerical evidence for the capacity step. The Manhattan and box scripts do not evaluate the capacity certificate. The small-parameter sonar sandwich tests use a generous exponential term and cannot meaningfully stress that step. The capacity inequality rests on the self-contained analytic proof. The referees report additional floating-point capacity tests; these are not proofs and were not rerun for the manuscript.

A structural source check after the paper repairs passed: balanced environments and braces, 86 unique labels, 80 resolved internal references, 10 bibliography entries and 16 resolved citations. All 15 theorem, lemma and proposition statements, all 117 display blocks, the analytic capacity proof and the bibliography are byte-for-byte unchanged from the pre-repair source. HTML tags and public theorem descriptions were also checked. These are source checks, not a TeX compilation or a mathematical proof. The earlier separate informed OpenAI review compared every display in all six sections with the proof notes and returned PASS, then checked the README and corrected HTML quantifiers. Compilation and PDF inspection remain with the coordinator, as requested.

Audited `main.tex` SHA-256 after task 040b: `c4c5a2dec85e144e37289750dee3f8ca360ab81e97986b49a9a8240f4aba5916`.

No publication, upload, repository push, dependency installation or local TeX compilation was performed by this task.
