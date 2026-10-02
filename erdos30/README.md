# An explicit second-order bound for Sidon sets

Zenodo: v1 https://doi.org/10.5281/zenodo.23103980 (2026-10-02 13:37 UTC); v2 adds the optimality theorem v2 https://doi.org/10.5281/zenodo.23105891 ; concept DOI (always the latest) https://doi.org/10.5281/zenodo.23103979.

Haoyu Chen — independent researcher.

**Published.** Zenodo, all versions: [10.5281/zenodo.23103979](https://doi.org/10.5281/zenodo.23103979) (v1 10.5281/zenodo.23103980; v2 10.5281/zenodo.23105891, which adds the optimality section). `main.pdf` in this directory is v2.

## Statement

Let $F(N)$ be the largest cardinality of a Sidon subset of $\{1,\ldots,N\}$, where all sums $a+b$ with $a\le b$ are distinct, including the doubled sums $a+a$. The note proves

$$
F(N)\le \sqrt N+\frac{2\sqrt2}{3}N^{1/4}+1
\qquad\text{for every integer }N\ge120^4=207\,360\,000.
$$

The proof uses a weighted Erdős–Turán energy argument with $h(t)=2(1-t)\mathbf1_{[0,1]}(t)$ and its autocorrelation. An exact half-line construction gives a total boundary correction of $2/3$. The proof derives the additive constant and onset explicitly, with a monotonicity argument covering every larger $N$.

Erdős's conjecture $F(N)=\sqrt N+O_\varepsilon(N^\varepsilon)$ for every $\varepsilon>0$ remains open. The optimality discussion concerns only the retained scalar inequalities with this kernel and these estimates; it gives no general barrier for Sidon methods or other kernels.

## Comparison and numerical evidence

The [dated source comparison](../../../problems/erdos30/G2_SIDON_20261002.md) found no statement subsuming the displayed theorem within the public sources searched. Located comparison coefficients include $0.9434925907\ldots$ in the [Hou–Zhao preprint, v3](https://arxiv.org/abs/2607.01169v3) and the unrefereed [repository claim $0.943006169985179\ldots$](https://github.com/wustep/maths/blob/da2440b68979b78d201182118d30ca418e3c2001/problems/sidon-second-term/compute/q2/README.md), both with an $O(1)$ remainder. The repository certificate was not replayed. This bounded comparison does not establish priority or novelty of the proof mechanism.

The number $2\sqrt2/3$ also occurs in a different [LM-ruler diameter theorem of Gupta–O'Bryant](https://arxiv.org/abs/2605.14229); the objects and conclusion differ. The paper records this numerical coincidence without claiming a transfer of that theorem.

The [exploratory kernel scan](../../../problems/erdos30/KERNEL_SCAN_20261002.md) uses floating-point discretization. It is non-rigorous numerical evidence, supplies no step of the proof, and does not certify local or global optimality over a family of kernels.

## Reproducing the checks

From this paper directory, with Python 3.8 or later and the standard library:

```sh
python3 ../../../problems/erdos30/check_sidon_bound.py
```

The script checks exact rational enclosures of the final numerical inequalities at the onset and a larger grid, using a proved rational majorant for the exponential error. It also checks the polynomial identity in $\mathbb Q[\sqrt2]$, independently enumerates every subset for $N\le12$, and uses complete branch-and-bound to determine maxima for every $1\le N\le60$. Finite checks cover the sum/difference convention and the universal energy inequalities; they do not extend the theorem below its onset or replace its all-$N$ proof.

The default exact-search budget is 5,000,000 nodes and 120 seconds. A budget stop reports unresolved entries as `INCOMPLETE` and exits with status 2. To request completion without either search budget:

```sh
python3 ../../../problems/erdos30/check_sidon_bound.py --max-n 60 --node-budget 0 --seconds 0
```

The Python deliverable was not executed in the drafting environment; the coordinator and both cross-vendor referees later ran it (exit code 0). Before that, executed JavaScript translations separately completed the $N\le60$ search in 91,104 nodes, agreed with literal subset enumeration through $N=18$, and passed exact-rational numerical and finite-energy checks, including the adaptive-precision regression at $N=2^{400}$. These are translation checks, not an execution of the Python file. Details and counts are recorded in the [standalone proof](../../../problems/erdos30/SIDON_BOUND_PROOF.md).

## Review and provenance

The argument was found by a clean-room GPT-6 Astra agent. The proof and audit code received informed same-vendor adversarial review; the current standalone proof and code received a PASS after a precision repair in the checker. The LaTeX conversion also passed same-vendor formula comparison and static structure checks; the PDF in this directory was compiled from it afterwards. These reviews and finite computations are distinct from kernel formalization.

**Cross-vendor referees (Claude Opus, two isolated reports, 2026-10-02): PASS and PASS, no repair required.** Reports: `problems/erdos30/REFEREE_CLAUDE_A_20261002.md`, `problems/erdos30/REFEREE_CLAUDE_B_20261002.md` in https://github.com/chy4pro/automath .

**Lean formalization (2026-10-02): the upper-bound theorem is kernel-checked.** `sidon_second_order` in [`lean/sidon30`](https://github.com/chy4pro/automath/tree/main/lean/sidon30) states the bound for every natural $N\ge120^4$ and every Sidon set $A\subseteq\{1,\dots,N\}$ (diagonal sums included), with coefficient $2\sqrt2/3$ and additive constant $1$; it builds against a pinned Mathlib on GitHub Actions ([run 37060176909](https://github.com/chy4pro/automath/actions/runs/37060176909), commit `f8e9766`) and depends only on `propext`, `Classical.choice`, `Quot.sound`. The formal proof was written by GPT-6 Astra (Codex) after the paper; the kernel-optimality theorem of v2 is **not** formalized. Independent human verification is not asserted. Haoyu Chen takes responsibility for the paper's mathematical claims, exposition, and attribution.

## Files

| File | Contents |
| --- | --- |
| `main.tex` | LaTeX paper source; coordinator compilation pending. |
| `README.md` | Statement, scope, reproducibility instructions, and review status. |
| `zenodo_description.html` | Text of the Zenodo record description (v2). |

The proof, checker, dated source comparison, and exploratory numerical scan are in the repository's `problems/erdos30/` directory, linked above.

## License

CC0 (public domain dedication), following the collection's default.


## Version 2 (2026-10-02)

Adds the optimality theorem (the constant 2√2/3 is the limit of the fixed-kernel scalar capacity method), with two further cross-vendor referee reports: `problems/erdos30/REFEREE_KERNEL_A_20261002.md` (PASS-WITH-REPAIRS, applied) and `REFEREE_KERNEL_B_20261002.md` (PASS). `main_v1.tex` is the v1 source.
