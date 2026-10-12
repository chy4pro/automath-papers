# Explicit upper and lower bounds for distinct consecutive sums in permutations

Haoyu Chen — Independent researcher. Prepared 12 October 2026.

For a permutation a of {1,…,n}, let S(a) be the set of nonempty linear consecutive sums, counted by distinct values, and let f(n) = max_a |S(a)|. The paper proves:

- For every integer n ≥ 1, f(n) ≤ (4435834/10^7)n² + 1100n. Hence f(n) ≤ 0.4436n² for every n ≥ 66,265,061.
- For every prime p ≥ 2^16, the complementary-triple family, with its final zero field label retained, has average and maximum at least (803/288)p² − 50000p^(7/4)(log p + 3)^8 over c ≠ 0 and t ∈ {k−m,…,k+m}, where k = (p−1)/2 and m = floor(p^(3/4)). Logarithms are natural. The bound is positive exactly when p > exp(u*), where u* > 29 is the unique root of 50000 exp(−u*/4)(u*+3)^8 = 803/288. The supplemental exact check encloses u*/log(2) between 304.219 and 304.221. The technical condition 2^16 is not an onset of content. For p ≥ 2^416 the family gives 0.309799(3p)² distinct sums; for p ≥ 2^448 it gives 0.3097993(3p)².
- For every integer n ≥ 2^4096, f(n) ≥ 0.309799n². The extension uses exactly Dusart (1998), Théorème 1.9, printed p.35: for real x ≥ 3275 there is a prime in (x, x(1 + 1/(2 log²x))].

Thus 0.309799 ≤ liminf f(n)/n² ≤ limsup f(n)/n² ≤ 0.4435834. The leading prime-length lower coefficient is 803/2592 = 0.309799382716… with an explicit error. It is not asserted to hold eventually with zero error. The bounds 0.44 above and 0.31 below, and the existence and value of a limit, are not established.

Both coefficients improve those of Konieczny, *On consecutive sums in permutations*, J. Combin. 12 (2021), 413–477, Theorem 1.2: 3/2 − 2/√e and 1/4 + π/16. These are the strongest coefficients we located in a bounded literature search completed on 12 October 2026. The search was not exhaustive and does not establish priority. Hegyvári's quadratic-residue construction gives coefficient 1/18, as explained in Konieczny §1.5. Primitive-root fixed-lag injectivity is a classical ingredient. The original o(n²) assertion was already disproved; this paper does not claim to solve Problem 34.

## Paper and build status

- [`main.pdf`](main.pdf): the paper, 16 pages, built from `main.tex` with pdfTeX 1.40.29 (TeX Live 2026) by the `latexmk` command below.
- [`main.tex`](main.tex): complete `amsart` source, with proofs, explicit errors and onsets, references, limitations and AI-use disclosure.
- Build locally with a TeX distribution containing AMS-LaTeX, `geometry`, `fontenc` and `hyperref`:

  ```sh
  SOURCE_DATE_EPOCH=1791763200 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
  ```

  Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error main.tex` twice. Byte-identical PDFs across TeX installations are not promised.

- [`zenodo_description.html`](zenodo_description.html): deposit description.
- Published: Zenodo DOI [10.5281/zenodo.23322918](https://doi.org/10.5281/zenodo.23322918) (12 October 2026).
- [`SHA256SUMS`](SHA256SUMS): all supplied files except the manifest itself. Verify with `sha256sum -c SHA256SUMS`.

## Code and data

The following 17 source/data files are byte-identical to the supplied reviewed versions. Their historical filenames are retained to keep existing commands and dependencies valid. They are not manuscript theorem labels.

| File | Purpose |
|---|---|
| [`code/cr17d-table.json`](code/cr17d-table.json) | 892-bin upper-bound certificate |
| [`code/cr17d-certificate.cjs`](code/cr17d-certificate.cjs) | Exact BigInt verifier, including a Machin-series enclosure of π |
| [`code/cr17d-certificate.json`](code/cr17d-certificate.json) | Complete per-row verifier output |
| [`code/cr17d-small-checks.cjs`](code/cr17d-small-checks.cjs) | Exhaustive small permutations and structured/random checks |
| [`code/cr17d-small-checks.json`](code/cr17d-small-checks.json) | Preserved finite-check output and retained permutations |
| [`code/cr23c-verifier.cjs`](code/cr23c-verifier.cjs) | Direct construction, permutation check and bitset count |
| [`code/cr23c-audit.cjs`](code/cr23c-audit.cjs) | Structural audit, domains, volumes, restoration and exact onset checks |
| [`code/cr23c-max-scan.cjs`](code/cr23c-max-scan.cjs) | Rotating-window exhaustive affine scan |
| [`code/cr23c-block-scan.cjs`](code/cr23c-block-scan.cjs) | Exploratory four/five-row alternatives; not part of the proof |
| [`code/cr23c-small-output.jsonl`](code/cr23c-small-output.jsonl) | All parameters at p = 5, 7, 11, 17, 31, 61, 101 |
| [`code/cr23c-audit-output.jsonl`](code/cr23c-audit-output.jsonl) | 3190 exact structural checks and related counts |
| [`code/cr23c-max-output.jsonl`](code/cr23c-max-output.jsonl) | Exhaustive scans through p = 1009 on the listed primes |
| [`code/cr23c-translations-output.jsonl`](code/cr23c-translations-output.jsonl) | Four multipliers × eight translations at five primes |
| [`code/cr23c-block-output.jsonl`](code/cr23c-block-output.jsonl) | 576 exploratory row-order counts |
| [`code/cr23c-large-block-output.jsonl`](code/cr23c-large-block-output.jsonl) | 18 larger exploratory counts |
| [`code/cr23c-padding-10000.jsonl`](code/cr23c-padding-10000.jsonl) | Exact padded count at n = 10000 |
| [`code/cr23c-padding-15010.jsonl`](code/cr23c-padding-15010.jsonl) | Exact padded count at n = 15010 |

The additional [`code/publication-checks.cjs`](code/publication-checks.cjs) and [`code/publication-checks.json`](code/publication-checks.json) check all 892 positive exterior signs, the stored rational row and linear bounds with an outward π bound, the exact upper onset, both lower onsets, padding, a directed-series enclosure of the positivity threshold, and static LaTeX structure/privacy. The explicit exterior sign check addresses the review's robustness suggestion without modifying the original verifier. It is supplemental; replay the original certificate for its cell-by-cell proof.

## Reproduction

Node.js with BigInt support and its standard library suffice; no packages or solver are needed. The finite counters use fixed-width arrays and JavaScript integer arithmetic within the exact range at the documented sizes. Do not interpret them as implementations at the theorem's enormous onsets. The mathematical construction is defined by finite maximization and can use arbitrary-precision integers.

Run commands **sequentially**, from this directory. Fresh outputs go to `reproduced/` so that the preserved outputs remain unchanged. Timing and memory fields depend on the machine. Compare mathematical JSON fields after omitting `cost`; JSONL files have a final cost-only record to omit.

```sh
mkdir -p reproduced
export UV_THREADPOOL_SIZE=1
node --single-threaded code/cr17d-certificate.cjs code/cr17d-table.json reproduced/upper-certificate.json
node --single-threaded code/cr17d-small-checks.cjs reproduced/upper-small-checks.json
node --single-threaded code/cr23c-audit.cjs > reproduced/lower-audit.jsonl
node --single-threaded code/cr23c-verifier.cjs small > reproduced/lower-small.jsonl
node --single-threaded code/cr23c-verifier.cjs translations > reproduced/lower-translations.jsonl
node --single-threaded code/cr23c-verifier.cjs one 3331 3 1665 10000 > reproduced/padding-10000.jsonl
node --single-threaded code/cr23c-verifier.cjs one 5003 2 2501 15010 > reproduced/padding-15010.jsonl
node --single-threaded code/publication-checks.cjs > reproduced/publication-checks.json
```

The optional complete recorded scan and exploratory checks are:

```sh
node --single-threaded code/cr23c-max-scan.cjs 5 7 11 17 31 101 251 503 1009 > reproduced/lower-max.jsonl
node --single-threaded code/cr23c-block-scan.cjs > reproduced/blocks.jsonl
node --single-threaded code/cr23c-block-scan.cjs large > reproduced/large-blocks.jsonl
```

The recorded exhaustive affine scan took about 305 CPU seconds; it is numerical evidence, not a premise of the analytic lower bound. The upper certificate took about 34 CPU seconds in the preparation replay. Runtime varies by machine.

For this source bundle, the upper certificate, upper finite checker, lower structural audit, lower direct small scan, both padded examples, and supplemental publication checks were rerun. All mathematical outputs match the preserved results. Larger exhaustive and exploratory outputs are included unchanged from the reviewed material; they were not rerun during manuscript preparation. The copied files were checked byte for byte. No numerical test verifies the analytic lower error in its non-vacuous range.

## Provenance and limits of review

The proofs and original programs were developed with GPT-6 Astra (OpenAI). Two isolated Claude (Anthropic) referees reviewed each proof; all four reports returned PASS. A separate Claude verifier returned PASS for the upper result and PASS-WITH-REPAIRS for the lower result, requiring wording about the vacuity of its error-bearing inequality. The manuscript applies that correction and the expository review items, including the exact Dusart citation subsequently verified in the literature search. The original code and outputs were kept unchanged; the extra exterior sign assertion is in the supplemental checker. The manuscript was assembled with GPT-6 Astra; a separate Claude transcription, code and privacy check compared it with the reviewed proofs and returned PASS-WITH-REPAIRS (two typographical repairs, applied). No Lean formalization or human mathematical verification is claimed by these AI reviews.

Deviation from the certified theorem statements: **none**. All three constants, quantifiers, prime/integer restrictions, logarithm convention, zero-label convention, and stated onsets are preserved. 
