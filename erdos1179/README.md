# Balanced random subset sums in finite abelian groups: explicit corrections of order √(q log q)

For a finite abelian group G of order N, put q = log₂ N and L = log₂ q. For a sample A of size k, let R_A(g) count its subset sums, including the empty subset. Balance means max_g |N R_A(g)/2^k − 1| ≤ 1/2. Model (I) is an independent uniform k-tuple, with repeated entries retaining distinct indices; model (U) is a uniform k-element subset.

The main result is Theorem 3. For every finite abelian group with N ≥ 2^64, every integer k ≥ q + 8400√(qL) has model-(I) failure probability at most 1/(2q). If also k ≤ 2^(q/2), its model-(U) failure probability is at most 1/q. For N ≥ 2^486018750 the constant is 200. Both subset intervals are nonempty.

The paper also proves the following exact statements, with tuple failure at most 1/(2q) and subset failure at most 1/q:

| Statement | Onset | Sample size |
| --- | --- | --- |
| Theorem 1 | N ≥ 2^(2^20) | k = ⌈q + 1000q/log₂ q⌉ |
| Theorem 2 | N ≥ 2^64 | k = ⌈q + 3400q^(4/5)⌉ |
| Corollary C | N ≥ 2^486018750 | k = ⌈q + 3q^(4/5)⌉ |

These fixed sizes satisfy k ≤ N. All logarithms in the statements are real; no power-of-two assumption on N is made.

- Paper: [`main.pdf`](main.pdf), **14 pages**, with source [`main.tex`](main.tex), in `amsart` format.
- Author: Haoyu Chen, independent researcher. AI use and review history are disclosed in the paper.
- Exact checks (identical to the reviewed versions except for the removal of an internal output path and of project labels in comments; the archived JSON outputs are unchanged): [`code/cr19-exact-checks.mjs`](code/cr19-exact-checks.mjs), [`code/cr19-exact-checks.json`](code/cr19-exact-checks.json), [`code/cr19b_checks.py`](code/cr19b_checks.py), [`code/cr19b_checks.json`](code/cr19b_checks.json).
- Portable runner: [`code/run-checks.mjs`](code/run-checks.mjs). It executes copies in a separate directory and compares mathematical output with the archived JSON, ignoring timing fields.
- Deposit text: [`zenodo_description.html`](zenodo_description.html).
- Checksums: [`SHA256SUMS`](SHA256SUMS).

The elementary L² estimate already gives the tuple bound at k ≥ 2q + L + 3. Theorems 1, 2, and 3(a) are guaranteed to improve its minimal sample requirement, respectively, when q ≥ 2^1000, q ≥ 3400^5 = 454354240000000000, and q/L ≥ 8400² = 70560000; Theorem 3(b) improves it throughout its range. Below the first three comparison conditions the minimal size exceeds 2q, so any gain is less than L + 4, if there is a gain at all. The paper gives the exact integer comparison with the ceilings included. The large constants and onsets have not been optimized.

The leading-coefficient-one question recorded as Erdős Problem #1179 was already settled by Erdős–Hall (1976). Within a literature search of 12 October 2026 we did not locate an explicit bound of this form for all finite abelian groups. This is a bounded search statement, not a priority claim. Hall (1977) remained unread, and forward-citation coverage was incomplete. The paper discusses the explicit Erdős–Rényi benchmark and the stronger finite-field results of Dhar–Dvir (TheoretiCS 2024) and Lund (arXiv:2609.20351), whose domain does not include every finite abelian group.

To reproduce the exact checks, use Node.js and Python 3 (standard libraries only), from this directory:

```sh
UV_THREADPOOL_SIZE=1 node --single-threaded code/run-checks.mjs results
```

Choose a new output directory such as `results`; to use a run-owned scratch directory, pass its path instead. Set `PYTHON` to a Python 3 executable if it is not named `python3`. The runner runs the two suites sequentially with one computation thread. Individual suites can be run with:

```sh
UV_THREADPOOL_SIZE=1 node --single-threaded code/run-checks.mjs results --only=cr19
UV_THREADPOOL_SIZE=1 node --single-threaded code/run-checks.mjs results --only=cr19b
```

The first suite reports **7,072 assertions**. It enumerates all ordered character tuples of lengths 2 and 4 in the 15 groups listed in Section 8, checks relation-pattern bounds and fourth-moment counts, and checks exact subset-sum moment identities for sample sizes 0 through 3. It also checks the stated finite induction range. The second reports **53,325 assertions**: numerical endpoints, elementary integer sweeps, six complete small lattice enumerations with counts 2, 3, 4, 7, 31, 64, and sampled parameter checks. Both suites were rerun for this bundle; mathematical outputs match the archived results. Finite checks supplement the analytic proof; they do not sample the theorem onsets or substitute for the proof over all real q.

The original stored runtimes are about 0.12 and 50.34 CPU seconds. Runtime depends on the machine; the second suite includes a long linear parameter search in its last sanity sample. No SAT/ILP solver, external package, or floating-point acceptance test is involved. The original JavaScript program has a legacy fixed output destination, and the Python program writes next to its own source. **Use the portable runner** to preserve the archived outputs: it changes only the output destination in the derived JavaScript copy and copies the Python source as is.

To compile with a conventional TeX installation:

```sh
SOURCE_DATE_EPOCH=1791763200 FORCE_SOURCE_DATE=1 latexmk -pdf main.tex
```

The supplied PDF was built with pdfTeX 1.40.29 (TeX Live 2026) by the `latexmk` command above. An earlier draft was built with Tectonic 0.15.0:

```sh
SOURCE_DATE_EPOCH=1791763200 RAYON_NUM_THREADS=1 tectonic main.tex
```

The epoch fixes the document date metadata; byte-identical PDFs across different TeX engines are not promised. Build intermediates and rerun outputs are not part of the publication manifest. On a system with `sha256sum`, run `sha256sum -c SHA256SUMS` to verify the deposit.

Verification status: the first bound received two independent Claude proof reviews with verdict PASS and a separate exact-arithmetic verification. The sharper bounds received two independent GPT-6 Astra reviews with verdict PASS-WITH-REPAIRS and a separate numerical verification with verdict PASS. Repairs corrected a parameter citation, restricted the methodological claims, and clarified rounding and scope; a subsequent delta verification returned PASS. No theorem constant, onset, group quantifier, or sampling restriction changed. All editorial notes are incorporated in the manuscript. These were AI reviews, not human peer review. The bundle contains the author checks, not the separate reviewer programs. No Lean or other proof-assistant formalization of these explicit bounds is supplied.

The proved limitation in Section 7 concerns only the displayed sufficient conditions of Proposition M. Other discussion of a possible method barrier is explicitly heuristic. A separate necessary correction is proved only in model (I) for elementary abelian two-groups. Neither is represented as an optimal general threshold.

Published: Zenodo DOI [10.5281/zenodo.23322923](https://doi.org/10.5281/zenodo.23322923) (12 October 2026).
