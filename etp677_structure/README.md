# Structure Theory of Finite 677 Magmas — working paper

**Current published version: v8_2.**
Read `Structure-Theory-of-Finite-677-Magmas-v8_2.pdf`.

| file | Zenodo record | DOI | published | md5 (verified against the Zenodo record) | status |
|---|---|---|---|---|---|
| `Structure-Theory-of-Finite-677-Magmas-v8_2.pdf` | 22070405 | [10.5281/zenodo.22070405](https://doi.org/10.5281/zenodo.22070405) | 2026-08-23 | `a9a287468bc53255bc6d45b7bebecfec` | **CURRENT** |
| *(not stored here)* `…-v8_1.pdf` | 22069570 | [10.5281/zenodo.22069570](https://doi.org/10.5281/zenodo.22069570) | 2026-08-23 | `52539cd2a6c42b8e7c788367dd383183` | published, superseded within the day |
| `Structure-Theory-of-Finite-677-Magmas-v8.pdf` | 22054879 | [10.5281/zenodo.22054879](https://doi.org/10.5281/zenodo.22054879) | 2026-08-22 | `ff4fc4464bc3f7ca9e44d3c0b13c981e` | superseded |
| `Structure-Theory-of-Finite-677-Magmas-v7.2.pdf` | 21995800 | [10.5281/zenodo.21995800](https://doi.org/10.5281/zenodo.21995800) | 2026-08-18 | `45211748b8f1542066118de9da9a7011` | superseded |

Naming note: Zenodo keeps the record title at "(v8)" and distinguishes the
correction releases by filename suffix. `v8_1` and `v8_2` are the first and second
correction releases over `v8`; internal campaign notes call the same three
artifacts v8, v9 and v10 respectively.

All versions share the Zenodo concept DOI
[10.5281/zenodo.21995799](https://doi.org/10.5281/zenodo.21995799), which always
resolves to the latest.

v8_1 and v8_2 are correction releases over v8. Differences below were read off the
published PDFs of v8 and v8_2, not off local source:

- **A fabricated quotation attributed to a named third party is removed.** v8
  carried a "third-party corroboration" remark asserting that an independent
  project on the same problem had "independently established that all rows of a
  finite E677 magma are permutations", quoting it as reporting that "local
  mechanisms are systematically insufficient", and calling this "the strongest
  evidence available". The project does not say that. v8_2 replaces the remark
  with a neutral "related work" note recording only that the project describes
  itself as active research, not a finished proof, and makes no claim about its
  results. The bibliography entry was corrected the same way.
- **Two real-person author names, misprinted in v8, are corrected** in the
  Equational Theories Project reference: `J. Bolan` → `M. Bolan` and
  `F. Carlini` → `N. Carlini`.
- **An uncertified computation is no longer marked certified.** The UNSAT rows of
  the exact robustness profile (`prop:robust`) were marked as a completed
  computation in v8. No DRAT certificate was produced for any of them and the SAT
  solver is not shipped with the scripts, so v8_2 marks them PARTIAL and adds an
  explicit status note recording them as uncertified.
- **An overstated verification claim is withdrawn.** v8's "verified through four
  mutually independent code paths" becomes a plain "controls" remark listing what
  was actually run.

**Cite and read v8_2.**

## `main.tex`

`main.tex` is the source of the **published v8_2 PDF**. This was verified, not
assumed: recompiling it with `tectonic` produces a PDF whose extracted text is
identical, page for page, to the text of the PDF downloaded from Zenodo record
22070405 (the PDF bytes differ only in embedded creation metadata).

Before 2026-08-23 this file held the **v7.2** source (`\date{17 August 2026}`),
i.e. it did not correspond to the newest PDF in this directory. That source is
preserved in this repository's git history at commit `dfed437` and earlier; it has
not been deleted from the record, only superseded here.
