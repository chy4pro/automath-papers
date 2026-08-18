# Machine-Verified Resolutions of Four OEIS Conjectures

**AutoMath Collaboration**
*(Claude Fable 5, GPT-5.6, Qwen3.8-Max, operated autonomously)*

16 August 2026

> **Disclosure of the production pipeline.** Every mathematical step reported in this paper was
> produced by automated systems; no human supplied a definition, a lemma, a proof idea, or a
> correction. The proof of Theorem 2.1 was found by Claude (Fable 5) after an earlier attempt was
> refuted in adversarial review. Theorem 3.1 was solved twice independently: once by Claude
> (Fable 5) and once, blind to the first solution, by OpenAI GPT-5.6 through the `codex`
> command-line interface; the second derivation is the one reproduced here. Theorem 4.1 was found
> by Claude (Fable 5) after a numerical reconnaissance run refuted the statement as literally
> transcribed in an existing formal corpus. Theorem 5.1 was solved by Claude (Fable 5), refuted in
> adversarial review by two independent reviewers who located the same defect, and then repaired
> by GPT-5.6 ("Pro" effort) --- the reviewer that had supplied the counterexample --- with the
> repair itself independently re-validated by two further reviewers before being accepted
> (Section 5). Adversarial review was carried out in separate sessions by GPT-5.6 ("Pro" effort,
> web interface), Qwen3.8-Max (web interface), and GPT-5.6 through `codex`, under a protocol
> requiring the reviewing model to differ from the solving model, except for the one repair step
> just noted. All four theorems were then formalized in Lean 4 against `mathlib`; the Lean
> compiler is the final arbiter of every claim below, and the files are listed in Section 6.
> Orchestration --- problem selection, task routing, review scheduling, and the drafting of this
> paper --- was likewise automated. Responsibility for what follows rests with the reader who
> checks the Lean files.

*This file is a faithful plain-text mirror of `main.tex`. Numbering here follows the section
structure; in the compiled PDF the theorems are numbered 2.1 (A108211), 3.1 (A114831),
4.1 (A100434), 5.1 (A114362).*

---

## Abstract

We resolve four conjectures recorded in the On-Line Encyclopedia of Integer Sequences and
formalize each resolution in Lean 4. First, we prove a conjecture of C. Kimberling (2014,
A108211): for every integer n ≥ 1,

  ⌊ ( 1/(4n) − log 2 + Σ_{k=n+1}^{2n} 1/k )^{−1} ⌋ = 16n² + 1.

The proof is entirely certificate-based: a rational telescoping majorant locates the tail of the
paired alternating harmonic series to within O(n^{−7}), comfortably inside a target window of
width Θ(n^{−4}), and all five auxiliary inequalities are reduced to polynomials whose
coefficients, after the substitution x = 1 + t, are nonnegative; the coefficient lists are
reproduced in full in Appendix A. Second, we answer the asymptotic question posed with A114831
(J. V. Post, 2006): the sequence defined by a(1) = 1, a(2) = 2,
a(n) = a(n−1) + ⌊2a(n−1)a(n−2)/(a(n−1)+a(n−2))⌋ satisfies a(n+1)/a(n) → √3, with the explicit
rate |a(n)/a(n−1) − √3| ≤ (2−√3)·2^{−(n−2)} + 4/n + 2^{−(n−2)/2} for n ≥ 4. An independent,
essentially simultaneous kernel-checked Lean proof of this limit was posted by K. Kitamura
shortly before ours; we make no claim to priority for this theorem (see the Prior work remark in
Section 3). Third, we prove the
three linear-recurrence identities conjectured by C. Dement (2004, A100434), in the sign-corrected
form that the source's own "apart from signs" convention dictates; the literal transcription is
refutable at n = 0. Fourth, we prove the asymptotic conjectured by T. Ordowski (2022, A114362 and
A348829): writing t(n) := ζ(2n)/ζ(n)², the quantity y(n) := (1−t(n))/(1+t(n)) satisfies
y(n) = 2^{−n}+3^{−n}+5^{−n}+7^{−n}+O(11^{−n}); we obtain the explicit bound
|y(n)−(2^{−n}+3^{−n}+5^{−n}+7^{−n})| ≤ 24·11^{−n} for n≥2 from the Euler product for ζ by an exact
identity for a nested composition of Möbius maps together with an elementary tail estimate; the
Lean development proves the same O(11^{−n}) statement with an explicit, weaker witness constant
of 56. This theorem's first proof was independently refuted by two reviewers before a second,
corrected proof was found and dual-reviewed as valid. Each theorem is accompanied by a Lean 4
development whose axiom audit reports dependence only on `propext`, `Classical.choice`, and
`Quot.sound`. As a by-product we report two mis-formalizations in the `formal-conjectures` corpus
(A109074 and A100434).

---

## 1. Introduction

### 1.1 Four conjectures

The On-Line Encyclopedia of Integer Sequences [1] carries, alongside its sequence data, a large
stock of conjectural comments contributed over three decades. Most are elementary in the sense
that no deep machinery is expected to be needed; many are nevertheless unproved, because nobody
has taken the time. This paper resolves four of them.

**(A108211)** Clark Kimberling observed on 9 September 2014 [2] that the sequence a(n) = 16n² + 1
appears to be given by

  a(n) = ⌊ 1 / ( 1/(4n) − log 2 + 1/(n+1) + 1/(n+2) + ⋯ + 1/(2n) ) ⌋.

This is Theorem 2.1 below. It is the substantive result of the paper: the quantity being inverted
is a difference of two quantities that agree to relative order n^{−1}, and the floor is pinned
only if the difference is located inside an interval of width Θ(n^{−4}).

**(A114831)** Jonathan Vos Post contributed on 19 February 2006 the sequence

  1, 2, 3, 5, 8, 14, 24, 41, 71, 122, 211, …

given by a(1) = 1, a(2) = 2 and a(n) = a(n−1) + ⌊2a(n−1)a(n−2)/(a(n−1)+a(n−2))⌋ for n ≥ 3,
together with the question: *what is this sequence, asymptotically?* The heuristic answer √3 is
immediate --- if the ratio of consecutive terms converges to L then L = 1 + 2/(L+1), so L² = 3 ---
but the existence of the limit is the whole content of the question. Theorem 3.1 settles it with
an explicit error bound; an independent, essentially simultaneous kernel-checked Lean proof of
the same limit was found by another author, and we cede priority for it (Section 3).

**(A100434)** Creighton Dement contributed on 18 December 2004 [3], in the context of his
"floretion" calculus, a family of auxiliary sequences attached to the linear recurrence
x(n+4) = −6x(n+2) − x(n) and conjectured three identities among them. Theorem 4.1 proves them. As
discussed in Section 4, the identities must be read with the sign convention that Dement's comment
announces but does not carry through its own notation; under the literal reading they fail at
n = 0.

**(A114362)** Thomas Ordowski commented on 13 November 2022 [4] that, writing
t(n) := ζ(2n)/ζ(n)²,

  (1−t(n))/(1+t(n)) = 1/2ⁿ + 1/3ⁿ + 1/5ⁿ + 1/7ⁿ + O(1/11ⁿ).

This is Theorem 5.1 below. The identity ζ(2n)/ζ(n)² = Π_p (1−p^{−n})/(1+p^{−n}) turns the
asymptotic into a statement about an infinite product of Möbius transformations of the primes;
the argument is a case study in extracting an explicit error bound, polynomial in 1/11ⁿ, from a
convergent Euler product, and is the one theorem in this paper whose first proof was
independently refuted by two reviewers before being repaired.

### 1.2 Verification methodology

All four of these statements had been transcribed into Lean 4 by the `formal-conjectures`
project [5], a corpus of open conjectures stated formally with `sorry` in place of a proof. That
corpus supplied both our problem list and, for A108211, A114831, and A114362, the exact formal
statement to be proved, which removes the usual risk that an autoformalization proves something
other than what was asked; A100434 is the exception, discussed in Section 1.3.

Our working protocol had three independent gates, and a claim was recorded as resolved only after
all three were passed.

**Adversarial review.** A completed argument was submitted, in separate sessions and without the
solver's reasoning trace, to models from a different vendor than the solver, with instructions to
classify every objection as *critical error* or *justification gap* and to return a verdict. This
gate did real work. The first proof of Theorem 2.1 was killed by it: the reviewer produced an
explicit counterexample at m = 2 to a comparison inequality on which the argument rested, and,
more damagingly, showed that even had the inequality been true its precision --- an uncertainty of
order 3/(256n⁴) against a permitted window of order 1/(256n⁴) --- would have been insufficient.
The proof presented in Section 2 is the replacement, designed to have precision O(n^{−7}) against
the same window. Two further rounds of review, in separate sessions, returned VALID --- one
recomputing every certificate symbolically from scratch, the other (GPT-5.6 at "Pro" effort)
additionally supplying, unprompted, the exact rational 12743/21656250 for the tightest of them at
n = 1. A third round, by Qwen3.8-Max, returned INCOMPLETE with eight presentation objections, all
of the form "the certificate is asserted, not exhibited". Section 2 and Appendix A are written to answer those
eight objections: every certificate polynomial is displayed, every quantity is an exact rational,
the pairing step is justified by an explicit subsequence argument, and the strictness of the
inequality that survives the infinite summation is obtained by retaining the first-term deficit
rather than by appeal to term-wise strictness.

A parallel failure recurred with Theorem 5.1: an initial proof asserted uniform pointwise bounds
on a nested composition of Möbius maps that fail already at n = 2; two reviewers, working
independently, isolated the same defect, one of them supplying an exact rational counterexample.
Section 5 records the repair and its own independent re-validation. Taken together, these are the
two cases in this paper where the adversarial gate, and not the solver, is the reason the final
theorem is true.

**Formal verification.** Each proof was then formalized in Lean 4 against `mathlib` [6,7], and the
resulting theorem's axiom dependencies were audited. The Lean compiler is the arbiter: no informal
step in this paper is load-bearing that is not also present in the corresponding `.lean` file.

**Statement fidelity.** Because a formal proof of the wrong statement is worthless, the final
theorem statement of each Lean file was compared, by hand-transcription, against the OEIS comment
it is supposed to formalize. The comparison is recorded in Section 6; where our statement differs
from `formal-conjectures`' (as it must for A100434, and as it does cosmetically for A114831), we
say exactly how.

### 1.3 Two mis-formalizations found as a by-product

Running numerical reconnaissance against formal statements before attempting to prove them turned
up two files in `formal-conjectures` whose Lean statement does not express the OEIS conjecture it
cites, and which are in fact refutable.

- The file `OEIS/109074.lean` defines b(n) = C(3n,n)/(2n+1) and asserts
  C(6n−2,2n) / (2·C(4n−1,2n)) = b(n+1)/b(n) for n ≥ 1. Two errors compound. First,
  C(3n,n)/(2n+1) is A001764 (ternary tree numbers 1,1,3,12,55,…), not A005156 (vertically
  symmetric alternating sign matrices, 1,1,3,26,646,…) as the surrounding documentation states.
  Second, the OEIS conjecture uses the ratio A005156(n)/A005156(n−1), not b(n+1)/b(n). The
  statement as written is false at n = 1: the left-hand side is C(4,2)/(2·C(3,2)) = 1 while
  b(2)/b(1) = 3. With the intended sequence and shift the numerical agreement is exact:
  1, 3, 26/3, 323/13, … on both sides for n = 1,2,3,4. We record also that, granted Kuperberg's
  product formula for A005156, the OEIS conjecture reduces to a factorial identity, so that its
  substance is Kuperberg's theorem rather than the displayed ratio. We have not formalized a
  corrected version.

- The file `OEIS/100434.lean` defines b(n) = c(n+1) for even n, omitting a minus sign. All three
  of its conjectures are then false at n = 0, where c(0)+d(0) = 3 but c(1) = −3. Section 4
  discusses the intended reading and proves the three identities in the corrected form.

Consistent with a policy of reporting rather than silently patching third-party corpora, we have
not modified those files; our corrected A100434 development lives in a separate namespace.

---

## 2. The Kimberling floor formula (A108211)

### 2.1 Statement and notation

**Theorem 2.1 (Kimberling's conjecture).** *For every integer n ≥ 1,*

  ⌊ 1/D(n) ⌋ = 16n² + 1,  where  D(n) := 1/(4n) − log 2 + Σ_{k=n+1}^{2n} 1/k.

Throughout this section we work with the following functions of a real variable x ≥ 1. Put

  (2.1)  A(x) := 1024x⁵ + 5888x⁴ + 12928x³ + 13312x² + 6148x + 843,
  (2.2)  B(x) := 4(4x+1)(2x+1)(4x+3)(4x+5)(2x+3)(4x+7),
  (2.3)  h(x) := A(x)/B(x),   g(x) := 60/(4x+1)⁷,

and

  (2.4)  f₁(x) := 1/(4x) − 1/(16x²+1),   f₂(x) := 1/(4x) − 1/(16x²+2).

Both A and B have positive coefficients, so h(x) > 0 and g(x) > 0 for x ≥ 0. Finally, for an
integer n ≥ 1 set

  (2.5)  T(n) := Σ_{m ≥ n} 1/((2m+1)(2m+2)).

The series converges, being dominated by Σ m^{−2}.

The shape of the proof is this. Step 1 identifies D(n) = 1/(4n) − T(n). Steps 2 and 3 sandwich
T(n) between h(n) and h(n)+g(n) by a telescoping certificate. Step 4 shows that this sandwich lies
strictly inside (f₁(n), f₂(n)), which is exactly what pins the floor. The reader should note the
margin at stake: the interval (f₁(n), f₂(n)) has width

  f₂(n) − f₁(n) = 1/(16n²+1) − 1/(16n²+2) = 1/((16n²+1)(16n²+2)) = Θ(n^{−4}),

while the sandwich supplied by Step 3 has width g(n) = 60/(4n+1)⁷ = Θ(n^{−7}). The whole design of
the certificate h --- a ratio of a quintic by a sextic --- is dictated by the need to beat n^{−4};
a cruder telescoping certificate produces an uncertainty of the same order as the window and
proves nothing.

### 2.2 Step 1: reduction to the tail of the paired alternating harmonic series

**Lemma 2.2 (Catalan's identity).** *For every integer n ≥ 0,*
Σ_{k=n+1}^{2n} 1/k = Σ_{j=1}^{2n} (−1)^{j+1}/j.

*Proof.* Writing H_N = Σ_{j≤N} 1/j, the left side is H_{2n} − H_n. Since H_n = 2 Σ_{i=1}^{n} 1/(2i)
is twice the sum of the reciprocals of the even integers up to 2n,

  H_{2n} − H_n = Σ_{j=1}^{2n} 1/j − 2 Σ_{j ≤ 2n, j even} 1/j = Σ_{j=1}^{2n} (−1)^{j+1}/j. ∎

**Lemma 2.3 (Mercator's series at x = 1).** *log 2 = Σ_{j≥1} (−1)^{j+1}/j, and for every N ≥ 0,*
|log 2 − Σ_{j=1}^{N} (−1)^{j+1}/j| ≤ 1/(N+1).

*Proof.* For x ∈ [0,1] and N ≥ 0, summing the finite geometric series gives the exact identity

  1/(1+x) = Σ_{j=1}^{N} (−1)^{j+1} x^{j−1} + (−1)^N x^N/(1+x).

Integrating over [0,1] yields log 2 = Σ_{j=1}^{N} (−1)^{j+1}/j + (−1)^N ∫₀¹ x^N/(1+x) dx, and
0 ≤ ∫₀¹ x^N/(1+x) dx ≤ ∫₀¹ x^N dx = 1/(N+1). ∎

**Lemma 2.4.** *For every integer n ≥ 1, D(n) = 1/(4n) − T(n).*

*Proof.* Let S_N := Σ_{j=1}^{N} (−1)^{j+1}/j, so S_N → log 2 by Lemma 2.3. By Lemma 2.2,
D(n) = 1/(4n) − (log 2 − S_{2n}), so it suffices to prove log 2 − S_{2n} = T(n).

Consider the partial sums of the paired series (2.5). For M ≥ 0,

  Σ_{m=n}^{n+M−1} 1/((2m+1)(2m+2)) = Σ_{m=n}^{n+M−1} ( 1/(2m+1) − 1/(2m+2) ) = S_{2n+2M} − S_{2n},

because the M consecutive pairs of terms (+1/(2m+1), −1/(2m+2)), m = n, …, n+M−1, are precisely
the terms of index 2n+1, 2n+2, …, 2n+2M of the alternating series, in order. Thus the M-th partial
sum of the paired series equals S_{2n+2M} − S_{2n}: the partial sums of the paired series form
(a shift of) a *subsequence* of the partial sums of the alternating series, namely the
even-indexed one. A subsequence of a convergent sequence converges to the same limit, so letting
M → ∞ gives T(n) = log 2 − S_{2n}. ∎

**Remark.** This is the point at which the review objected to the phrase "grouping the tail in
consecutive pairs is legitimate since the partial sums converge". Consecutive grouping of a
convergent series does preserve the sum, but the reason is the subsequence argument just given,
not absolute convergence --- which the alternating harmonic series does not have. In the Lean
development the issue disappears entirely: the identity
Σ_{m<n} 1/((2m+1)(2m+2)) = H_{2n} − H_n is proved there by a finite induction on n, so no
regrouping of an infinite series is ever performed (Section 6).

### 2.3 Step 2: the telescoping certificate

**Lemma 2.5 (Defect identity).** *For every real m ≥ 0,*

  Δ(m) := 1/((2m+1)(2m+2)) − ( h(m) − h(m+1) ) = 63(16m² + 120m + 119) / (2 P(m)),

*where*

  P(m) := (m+1)(2m+1)(2m+3)(2m+5)(4m+1)(4m+3)(4m+5)(4m+7)(4m+9)(4m+11).

*In particular Δ(m) > 0 for every m ≥ 0.*

*Proof.* This is an identity between rational functions. Clearing denominators turns it into an
identity between polynomials of degree 12, which is verified by expansion; the verification is
mechanical and was performed independently three times (by computer algebra over ℚ, by an
adversarial reviewer recomputing it symbolically, and by Lean's `field_simp; ring` in the file
`A108211.lean`, where the same identity appears as `delta_eq` with the numerator written
126(16m²+120m+119) over 4P(m)).

Positivity is immediate: for m ≥ 0 every factor of P(m) is positive and 16m²+120m+119 ≥ 119 > 0. ∎

**Lemma 2.6 (Majorant certificate).** *For every real m ≥ 1,*

  0 < Δ(m) < g(m) − g(m+1) = 60/(4m+1)⁷ − 60/(4m+5)⁷.

*More precisely, with*

  D₂(m) := 2(m+1)(2m+1)(2m+3)(2m+5)(4m+1)⁷(4m+3)(4m+5)⁷(4m+7)(4m+9)(4m+11),

*which is positive for m ≥ 0, one has g(m) − g(m+1) − Δ(m) = N₂(m)/D₂(m), where N₂ is a polynomial
of degree 14 all of whose coefficients in the shifted variable t = m−1 --- that is, the
coefficients of N₂(1+t) --- are the positive integers listed in Table A.1. Consequently N₂(m) > 0
for every m ≥ 1.*

*Proof.* The displayed rational identity is verified by clearing denominators and expanding,
exactly as in Lemma 2.5; note that g(m+1) = 60/(4(m+1)+1)⁷ = 60/(4m+5)⁷. Substituting m = 1+t with
t ≥ 0 turns N₂(m) into N₂(1+t) = Σ_{k=0}^{14} c_k t^k with every c_k > 0 (Table A.1); the smallest
coefficient is c₁₄ = 11,274,289,152 and the constant term is c₀ = 1,646,809,468,266,375. A sum of
nonnegative multiples of nonnegative quantities, with a positive constant term, is positive; hence
N₂(1+t) > 0 for all t ≥ 0, i.e. N₂(m) > 0 for all m ≥ 1. Since D₂(m) > 0 there, the claim follows.
The lower bound Δ(m) > 0 is Lemma 2.5. ∎

**Remark.** The device of exhibiting a univariate polynomial positivity certificate by shifting to
x = 1+t and displaying nonnegative coefficients is what makes these lemmas checkable both by hand
and by a proof assistant: after the shift, positivity is a *linear* consequence of the facts
t^k ≥ 0, so no nonlinear arithmetic is needed. This is exploited in Section 6.

### 2.4 Step 3: the sandwich, with the first-term deficit retained

**Lemma 2.7 (Decay certificate).** *For every real x ≥ 1, 0 < h(x) ≤ 1/x. In particular h(x) → 0
as x → ∞.*

*Proof.* Positivity is clear. The inequality h(x) ≤ 1/x is equivalent to x·A(x) ≤ B(x), both sides
being polynomials of degree 6 and B(x) > 0 for x ≥ 1. Substituting x = 1+t,

  B(1+t) − (1+t)A(1+t) = 3072t⁶ + 37120t⁵ + 184448t⁴ + 482304t³ + 699916t² + 534509t + 167757,

all of whose coefficients are positive (Table A.4); hence the difference is positive for t ≥ 0. ∎

**Lemma 2.8 (Sandwich).** *For every integer n ≥ 1,*

  h(n) < T(n) ≤ h(n) + g(n) − δ(n) < h(n) + g(n),   δ(n) := N₂(n)/D₂(n) > 0,

*with N₂, D₂ as in Lemma 2.6.*

*Proof.* By Lemma 2.5, for every integer m ≥ n,

  (2.6)  1/((2m+1)(2m+2)) = ( h(m) − h(m+1) ) + Δ(m).

Summing (2.6) over n ≤ m ≤ M and telescoping,

  (2.7)  Σ_{m=n}^{M} 1/((2m+1)(2m+2)) = h(n) − h(M+1) + Σ_{m=n}^{M} Δ(m).

The terms Δ(m) are positive (Lemma 2.5) and, by Lemma 2.6, bounded above by g(m) − g(m+1), whose
partial sums telescope to g(n) − g(M+1) ≤ g(n). Hence Σ_{m≥n} Δ(m) converges, say to Σ_n ≥ 0; and
h(M+1) → 0 by Lemma 2.7. Letting M → ∞ in (2.7),

  (2.8)  T(n) = h(n) + Σ_n.

*Lower bound.* Σ_n ≥ Δ(n) > 0, so T(n) > h(n).

*Upper bound, with the deficit retained.* Set δ(m) := ( g(m) − g(m+1) ) − Δ(m) = N₂(m)/D₂(m),
which is **strictly** positive for every m ≥ 1 by Lemma 2.6. For any M ≥ n,

  Σ_{m=n}^{M} Δ(m) = Σ_{m=n}^{M} ( g(m) − g(m+1) ) − Σ_{m=n}^{M} δ(m)
                   = g(n) − g(M+1) − Σ_{m=n}^{M} δ(m) ≤ g(n) − δ(n),

where the last step drops −g(M+1) ≤ 0 and all terms δ(m) ≥ 0 with m > n, keeping only the term
m = n. The bound g(n) − δ(n) does not depend on M, so letting M → ∞ gives Σ_n ≤ g(n) − δ(n) < g(n),
and (2.8) finishes the proof. ∎

**Remark.** The last paragraph is deliberately fussy. Term-wise strict inequalities between
infinitely many pairs of terms do *not* imply a strict inequality between the sums --- the deficits
may tend to 0 fast enough for the sums to agree. Retaining the single deficit δ(n), an explicit
positive rational, before passing to the limit removes the difficulty. (For the purposes of
Theorem 2.1 the non-strict bound T(n) ≤ h(n)+g(n) would in fact suffice, because Lemma 2.9 is
strict; this is the route taken in the Lean file. We give the strict version because it is what
the informal statement asserts.)

### 2.5 Step 4: the window inequalities and the proof of Theorem 2.1

**Lemma 2.9 (Window).** *For every real x ≥ 1, f₁(x) < h(x) and h(x) + g(x) < f₂(x).*

*Proof.* **Lower window.** Since f₁(x) = (16x²−4x+1)/(4x(16x²+1)) and h(x) = A(x)/B(x) with both
denominators positive for x ≥ 1, the inequality f₁(x) < h(x) is equivalent to N₃(x) > 0, where

  N₃(x) := A(x)·4x(16x²+1) − (16x²−4x+1)·B(x),

a polynomial of degree 5 once the degree-8 terms cancel. Explicitly, after the substitution
x = 1+t,

  N₃(1+t) = 256t⁵ + 2816t⁴ + 12096t³ + 24688t² + 22223t + 6756,

all of whose coefficients are positive (Table A.2); hence N₃(1+t) > 0 for t ≥ 0. Equivalently,
over the positive common denominator D₃(x) = 4x(2x+1)(2x+3)(4x+1)(4x+3)(4x+5)(4x+7)(16x²+1) one
has h(x) − f₁(x) = N₃(x)/D₃(x) > 0; at x = 1 the exact value is h(1) − f₁(1) = 563/294525 > 0.

**Upper window.** Since f₂(x) = (8x²−2x+1)/(4x(8x²+1)) and

  h(x) + g(x) = [ A(x)(4x+1)⁶ + 240(2x+1)(4x+3)(4x+5)(2x+3)(4x+7) ]
                / [ 4(4x+1)⁷(2x+1)(4x+3)(4x+5)(2x+3)(4x+7) ],

the inequality h(x)+g(x) < f₂(x) is equivalent to N₄(x) > 0 where N₄ is the numerator of
f₂ − h − g over the positive common denominator
D₄(x) = 4x(2x+1)(2x+3)(4x+1)⁷(4x+3)(4x+5)(4x+7)(8x²+1). Substituting x = 1+t,

  N₄(1+t) = 393216t⁹ + 6291456t⁸ + 43757568t⁷ + 169863168t⁶ + 404609280t⁵
            + 614989440t⁴ + 598254960t³ + 359583120t² + 120914895t + 17203050,

all of whose coefficients are positive (Table A.3); hence N₄(1+t) > 0 for t ≥ 0. At x = 1 the exact
value of the difference is

  f₂(1) − h(1) − g(1) = 12743/21656250 > 0.

(This exact rational replaces the decimal "0.000588…" of an earlier draft; no decimal
approximation occurs anywhere in the present argument.) ∎

**Proof of Theorem 2.1.** Fix an integer n ≥ 1. Chaining Lemmas 2.8 and 2.9 at x = n,

  f₁(n) < h(n) < T(n) ≤ h(n) + g(n) − δ(n) < h(n) + g(n) < f₂(n),

so f₁(n) < T(n) < f₂(n). By Lemma 2.4, D(n) = 1/(4n) − T(n), and subtracting the chain from 1/(4n)
reverses it:

  1/(4n) − f₂(n) < D(n) < 1/(4n) − f₁(n),  that is,  1/(16n²+2) < D(n) < 1/(16n²+1)

by the definitions (2.4). In particular D(n) > 1/(16n²+2) > 0, so we may invert; inversion of
positive reals reverses strict inequalities, giving

  16n² + 1 < 1/D(n) < 16n² + 2.

Since 16n²+1 is an integer and 1/D(n) lies strictly between it and its successor,
⌊1/D(n)⌋ = 16n²+1. ∎

**Remark.** The positivity of D(n), established here *before* inversion, is not a formality. By
Lemma 2.4 the assertion D(n) > 0 says exactly that T(n) < 1/(4n), i.e. that
Σ_{k=n+1}^{2n} 1/k > log 2 − 1/(4n), and since T(n) = 1/(4n) − 1/(16n²) + O(n^{−4}) this is a
genuine inequality, delivered here by the upper window bound. Note also that no appeal to the
irrationality of log 2 is made anywhere: every inequality above is strict by certificate, so the
possibility of 1/D(n) landing exactly on an integer is excluded outright rather than by an
arithmetic argument.

---

## 3. The asymptotics of A114831

**Theorem 3.1.** *Define a : ℤ_{≥1} → ℤ_{≥1} by a(1) = 1, a(2) = 2 and*

  a(n) = a(n−1) + ⌊ 2·a(n−1)·a(n−2) / (a(n−1)+a(n−2)) ⌋   (n ≥ 3),

*so that a = 1, 2, 3, 5, 8, 14, 24, 41, 71, 122, 211, …. Then*

  lim_{n→∞} a(n+1)/a(n) = √3,

*and for every n ≥ 4 one has the explicit bound*

  (3.1)  | a(n)/a(n−1) − √3 | ≤ (2−√3)·2^{−(n−2)} + 4/n + 2^{−(n−2)/2}.

Write A_n := a(n) and, for n ≥ 2, R_n := A_n/A_{n−1}.

*Proof.* **Linear growth.** For positive integers x, y,

  2xy − x − y = x(y−1) + y(x−1) ≥ 0,

so 2xy/(x+y) ≥ 1 and therefore the integer ⌊2xy/(x+y)⌋ is at least 1. Hence A_n ≥ A_{n−1} + 1 for
n ≥ 3, and since A₁ = 1, A₂ = 2,

  (3.2)  A_n ≥ n   (n ≥ 1).

In particular A_n > A_{n−1} ≥ 1, so R_n > 1 for every n ≥ 2.

**The exact ratio recursion.** For n ≥ 3 let

  θ_n := 2A_{n−1}A_{n−2}/(A_{n−1}+A_{n−2}) − ⌊ 2A_{n−1}A_{n−2}/(A_{n−1}+A_{n−2}) ⌋ ∈ [0,1)

be the fractional defect of the floor. Since R_{n−1} = A_{n−1}/A_{n−2},

  2A_{n−1}A_{n−2}/(A_{n−1}+A_{n−2}) = 2A_{n−1} / ((A_{n−1}+A_{n−2})/A_{n−2}) = 2A_{n−1}/(R_{n−1}+1),

so dividing the defining recurrence
A_n = A_{n−1} + 2A_{n−1}A_{n−2}/(A_{n−1}+A_{n−2}) − θ_n by A_{n−1} gives the exact identity

  (3.3)  R_n = 1 + 2/(R_{n−1}+1) − θ_n/A_{n−1} = F(R_{n−1}) − θ_n/A_{n−1},   F(x) := 1 + 2/(x+1).

**Fixed point and contraction.** Put s := √3. Since (s−1)(s+1) = s²−1 = 2, we have 2/(s+1) = s−1
and therefore

  (3.4)  F(s) = 1 + (s−1) = s.

Moreover, for all x, y ≥ 1,

  (3.5)  |F(x) − F(y)| = 2|x−y| / ((x+1)(y+1)) ≤ |x−y|/2,

because (x+1)(y+1) ≥ 4. Thus F is a ½-contraction on [1,∞), a set that contains both s = 1.732…
and every R_m with m ≥ 2.

**Error recursion.** Let E_n := |R_n − s|. Combining (3.3), (3.4), (3.5), R_{n−1} ≥ 1, s ≥ 1,
0 ≤ θ_n < 1, and (3.2), we obtain for every n ≥ 3

  (3.6)  E_n ≤ |F(R_{n−1}) − F(s)| + θ_n/A_{n−1} ≤ ½E_{n−1} + 1/A_{n−1} ≤ ½E_{n−1} + 1/(n−1).

Since R₂ = A₂/A₁ = 2, we have E₂ = 2 − √3, and iterating (3.6) gives

  (3.7)  E_n ≤ 2^{−(n−2)}(2−√3) + Σ_{j=3}^{n} 2^{−(n−j)}/(j−1).

**Explicit tail bound.** Let n ≥ 4 and put K := ⌊(n−2)/2⌋. Substituting k = n−j,

  Σ_{j=3}^{n} 2^{−(n−j)}/(j−1) = Σ_{k=0}^{n−3} 2^{−k}/(n−k−1).

For 0 ≤ k ≤ K we have n−k−1 ≥ n−K−1 ≥ n/2 (because K ≤ (n−2)/2), while for K+1 ≤ k ≤ n−3 we have
n−k−1 ≥ 2. Therefore

  (3.8)  Σ_{k=0}^{n−3} 2^{−k}/(n−k−1) ≤ (2/n)Σ_{k=0}^{K} 2^{−k} + ½Σ_{k=K+1}^{∞} 2^{−k}
         ≤ 4/n + 2^{−K−1} ≤ 4/n + 2^{−(n−2)/2},

using Σ_{k≥0} 2^{−k} = 2 and K+1 ≥ (n−2)/2. Combining (3.7) and (3.8) gives exactly (3.1). Each of
the three terms on the right of (3.1) tends to 0, so E_n → 0, i.e. R_n → √3. Replacing n by n+1
gives lim_{n→∞} a(n+1)/a(n) = √3. ∎

**Remark (Two independent derivations).** Theorem 3.1 was proved twice, independently and without
communication between the two solvers. The first derivation (Claude, Fable 5) established an
invariant interval R_n ∈ [1.59, 2] for n large, used the exact algebraic contraction identity

  F(r) − √3 = (r−√3)(1−√3)/(1+r),

which gives a contraction factor (√3−1)/(1+r) ≤ 0.283 on that interval, and controlled the forcing
term by the Fibonacci lower bound A_n ≥ F_n (valid because ⌊2xy/(x+y)⌋ ≥ min(x,y), so
A_n ≥ A_{n−1}+A_{n−2}). The second derivation, reproduced above, was obtained by OpenAI GPT-5.6 and
is strictly simpler: the Lipschitz bound (3.5) is global on [1,∞), so no invariant interval is
needed, and the crude linear bound (3.2) suffices in place of the Fibonacci one. Cross-checking the
two line by line --- both reach √3 through the same fixed-point equation but with different
contraction constants (0.283 versus 1/2) and different growth inputs --- is the reason we adopted
the second for formalization. The stronger Fibonacci growth would improve (3.1) from O(1/n) to a
geometric rate; we did not pursue this, since the conjecture asks only for the limit.

**Remark (Prior work).** While this paper was in preparation, Kenta Kitamura (GitHub user
`KitaKen1`) independently proved OEIS A114831's `conjecture3` --- the same statement,
a(n+1)/a(n) → √3 --- with a kernel-checked Lean 4 proof (repository
https://github.com/KitaKen1/oeis-a114831-asymptotic), submitted as
`google-deepmind/formal-conjectures` pull request #4969, opened 15 August 2026 and merged
16 August 2026, which marked the conjecture `research solved` upstream. That submission predates
our own derivation and formalization, completed the same day; we became aware of it only after
our proof was finished. We therefore regard Theorem 3.1 as an independent, essentially
simultaneous proof, obtained by a different argument --- the global ½-Lipschitz contraction (3.5)
used above, rather than Kitamura's method --- and we make no claim to priority.

---

## 4. The Dement identities (A100434)

### 4.1 The sequences and the sign convention

A100434 is the expansion of (1+x)(3+x)/(1+6x²+x⁴), i.e. the integer sequence

  (4.1)  a(0)=3, a(1)=4, a(2)=−17, a(3)=−24,   a(n+4) = −6a(n+2) − a(n),

beginning 3, 4, −17, −24, 99, 140, −577, −816, 3363, …. Dement's comment introduces two further
solutions of the same recurrence,

  (4.2)  c : c(0)=1, c(1)=−3, c(2)=−7, c(3)=17,
  (4.3)  d : d(0)=2, d(1)=4, d(2)=−10, d(3)=−24,

each extended by x(n+4) = −6x(n+2) − x(n), and four derived sequences

  (4.4)  e(2k) = ½d(2k),  e(2k+1) = −½d(2k),
         f(2k) = f(2k+1) = ½d(2k+1),
         g(2k) = 0,  g(2k+1) = c(2k+1),

together with a sequence b described as "c with even- and odd-indexed terms reversed". The
conjecture is

  c(n) + d(n) = e(n) + f(n) = g(n) + a(n) = b(n)   (n ≥ 0).

The comment writes this reversal as b(2k) = c(2k+1), b(2k+1) = c(2k). Taken literally the
conjecture is false, and at once: c(0) + d(0) = 1 + 2 = 3 while c(1) = −3. The intended reading is
however unambiguous from the surrounding text, which introduces c as "the sequence A001333, apart
from signs" and d as "A052542, apart from signs", and which summarises the three identities as
saying that all three sums "represent the sequence c with even- and odd-indexed terms reversed".
The sign pattern of c is +, −, −, +, +, −, −, +, … with period four; reversing terms within
consecutive pairs necessarily disturbs it, so a statement about the reversal is a statement about
|c|, i.e. one made "apart from signs". Restoring the sign so that the identities hold requires
exactly one change,

  (4.5)  b(2k) := −c(2k+1),   b(2k+1) := c(2k),

and this choice is independently corroborated: −c(2k+1) = a(2k) is a known identity for this family
(it is stated in the OEIS comment itself, as "a(2n) = −c(2n+1)"), so (4.5) makes b the interleaving
of the even part of a with the even part of c,

  b = 3, 1, −17, −7, 99, 41, −577, −239, 3363, 1393, …

which is |c| = 1, 3, 7, 17, 41, 99, … with consecutive terms transposed, carrying the sign pattern
of a. With (4.5) the three identities hold for every n; they were verified numerically for n < 600
before any proof was attempted, and are proved below.

### 4.2 The identities

**Theorem 4.1.** *Let a, c, d be given by (4.1)–(4.3), let e, f, g be given by (4.4), and let b be
given by (4.5). Then for every integer n ≥ 0,*

  c(n) + d(n) = b(n),   e(n) + f(n) = b(n),   g(n) + a(n) = b(n).

*Proof.* All of a, c, d satisfy the same order-four recurrence x(n+4) = −6x(n+2) − x(n), which
couples indices of equal parity only. Consequently every statement below splits into an even and an
odd case, and each case is proved by two-step induction on k (base cases k = 0, 1, inductive step
from k, k+1 to k+2), the step being a linear identity among the four values involved. We record the
six auxiliary facts; each is proved by exactly this scheme, and the base cases are the displayed
initial values.

  (4.6)  c(2k) + d(2k) = −c(2k+1),
  (4.7)  c(2k+1) + d(2k+1) = c(2k),
  (4.8)  a(2k) = −c(2k+1),  a(2k+1) = d(2k+1),
  (4.9)  d(2k) ≡ 0,  d(2k+1) ≡ 0  (mod 2),
  (4.10) d(2k) + d(2k+1) = −2c(2k+1),
  (4.11) d(2k+1) − d(2k) = 2c(2k).

For instance, (4.6) at k = 0 reads c(0)+d(0) = 1+2 = 3 = −c(1), and at k = 1 it reads
c(2)+d(2) = −7 + (−10) = −17 = −c(3); the inductive step is

  c(2k+4) + d(2k+4) = −6(c(2k+2)+d(2k+2)) − (c(2k)+d(2k))
                    = −6(−c(2k+3)) − (−c(2k+1)) = −c(2k+5),

using the induction hypotheses at k+1 and k and then the recurrence for c. The remaining five are
identical in form; (4.9) is the same induction carried out for divisibility, with base cases
d(0) = 2, d(2) = −10, d(1) = 4, d(3) = −24.

**First identity.** If n = 2k, then c(n)+d(n) = −c(2k+1) = b(2k) by (4.6) and (4.5). If n = 2k+1,
then c(n)+d(n) = c(2k) = b(2k+1) by (4.7) and (4.5).

**Second identity.** By (4.9) the halvings in (4.4) are exact. If n = 2k, then by (4.4) and (4.10),

  e(2k) + f(2k) = ½d(2k) + ½d(2k+1) = ½(d(2k)+d(2k+1)) = −c(2k+1) = b(2k).

If n = 2k+1, then f(2k+1) = ½d(2k+1) and e(2k+1) = −½d(2k), so by (4.11),

  e(2k+1) + f(2k+1) = ½(d(2k+1) − d(2k)) = c(2k) = b(2k+1).

**Third identity.** If n = 2k, then g(2k) = 0 and a(2k) = −c(2k+1) = b(2k) by (4.8). If n = 2k+1,
then g(2k+1) + a(2k+1) = c(2k+1) + d(2k+1) = c(2k) = b(2k+1) by (4.8) and (4.7). ∎

**Remark.** The identities are, as OEIS's own `easy` keyword suggests, not deep: they are six
parallel two-step inductions. The interest of the case lies elsewhere. First, the conjecture as it
stands in a formal corpus was refutable at the very first index, and this was found by evaluating
the formal statement numerically before attempting a proof --- a cheap check that we now run
routinely. Second, deciding *which* corrected statement is "the intended one" is a judgement about
a natural-language source, not a mathematical deduction; we have set out the evidence for (4.5)
above and flag it as the one interpretive step in this paper.

---

## 5. The Ordowski tanh-sum asymptotic (A114362)

### 5.1 Statement and the Euler-product reduction

**Theorem 5.1 (Ordowski's conjecture).** *For an integer n ≥ 2 let*

  t(n) := ζ(2n)/ζ(n)²,  y(n) := (1−t(n))/(1+t(n)),  S(n) := 1/2ⁿ+1/3ⁿ+1/5ⁿ+1/7ⁿ.

*Then*

  y(n) = S(n) + O(11^{−n}),  explicitly  |y(n) − S(n)| ≤ 24·11^{−n}  (n ≥ 2).

For a prime p and n ≥ 2 write x_p := p^{−n} ∈ (0, ¼] (the bound holding since p ≥ 2, n ≥ 2) and

  q_p := (1−x_p)/(1+x_p) ∈ (0,1).

**Lemma 5.2 (Euler-product form).** *For every integer n ≥ 2, t(n) = Π_p q_p, the product being
absolutely convergent.*

*Proof.* For s>1, ζ(s) = Π_p (1−p^{−s})^{−1}, the Euler product converging absolutely because
Σ_p p^{−s} ≤ Σ_{m≥2} m^{−s} < ∞ and −log(1−u) ≤ (4/3)u for 0 ≤ u ≤ ¼ bounds Σ_p |log(1−p^{−s})|.
Applying this at s=n and s=2n,

  t(n) = ζ(2n)/ζ(n)² = Π_p (1−p^{−n})²/(1−p^{−2n}) = Π_p (1−p^{−n})/(1+p^{−n}) = Π_p q_p.

Absolute convergence of the last product follows from |log q_p| ≤ x_p + (4/3)x_p = (7/3)x_p (using
log(1+u) ≤ u for both factors) and Σ_p x_p < ∞. ∎

### 5.2 Peeling off the primes 2, 3, 5, 7

**Definition 5.3.** For a,b ∈ [0,1) put a ⊕ b := (a+b)/(1+ab), and for u ∈ (0,1] put
Φ(u) := (1−u)/(1+u).

The operation ⊕ is the familiar relativistic velocity addition; it is commutative and associative,
and maps [0,1)² into [0,1) since 1−(a⊕b) = (1−a)(1−b)/(1+ab) > 0. It is related to Φ by the exact
identity, valid for a ∈ [0,1) and R ∈ (0,1],

  (5.1)  Φ(q(a)R) = a ⊕ Φ(R),  q(a) := (1−a)/(1+a),

checked by clearing denominators on both sides: both equal
((1+a)−(1−a)R) / ((1+a)+(1−a)R).

**Lemma 5.4 (Peeling).** *For n ≥ 2 let R₁₁ := Π_{p≥11} q_p ∈ (0,1) and r := Φ(R₁₁), and put
A := x₂ ⊕ x₃ ⊕ x₅ ⊕ x₇ (associativity makes the bracketing immaterial). Then*

  y(n) = A ⊕ r.

*Proof.* By Lemma 5.2, t(n) = q₂q₃q₅q₇R₁₁ = q(x₂)q(x₃)q(x₅)q(x₇)R₁₁, since q_p = q(x_p) by
definition. Applying (5.1) four times, innermost first,

  y(n) = Φ(t(n)) = x₂ ⊕ (x₃ ⊕ (x₅ ⊕ (x₇ ⊕ r))) = A ⊕ r

by associativity of ⊕. ∎

### 5.3 The tail bound and the four-prime defect

**Lemma 5.5 (Tail bound).** *For every integer n ≥ 2, 0 ≤ r ≤ 24·11^{−n}.*

*Proof.* For u_j ∈ [0,1], 1 − Π_{j≤m} u_j ≤ Σ_{j≤m}(1−u_j), by induction from
1−uv = (1−u)+u(1−v) ≤ (1−u)+(1−v); passing to the limit over the (absolutely convergent) tail
product gives 1−R₁₁ ≤ Σ_{p≥11}(1−q_p). Since 1−q_p = 2x_p/(1+x_p) ≤ 2x_p,

  1 − R₁₁ ≤ 2Σ_{p≥11} p^{−n} ≤ 2Σ_{k=11}^{∞} k^{−n} ≤ 2·11^{−n}(1+11/(n−1)) ≤ 24·11^{−n}  (n ≥ 2),

the middle inequality by the integral comparison Σ_{k≥11}k^{−n} ≤ 11^{−n}+∫_{11}^{∞}u^{−n}du and
the last because 1+11/(n−1) ≤ 12 for n ≥ 2. Since R₁₁ ≥ 0, r = (1−R₁₁)/(1+R₁₁) ≤ 1−R₁₁ ≤ 24·11^{−n};
and r≥0 since R₁₁≤1. ∎

**Lemma 5.6 (Four-prime defect).** *Let δ(a,b) := a+b−(a⊕b) = ab(a+b)/(1+ab) ≥ 0 for a,b ≥ 0, and
set b₅ := x₅⊕x₇, b₃ := x₃⊕b₅, F := S(n) − A. Then*

  F = δ(x₅,x₇) + δ(x₃,b₅) + δ(x₂,b₃) ≤ 20·12^{−n}  (n≥2).

*Proof.* Telescoping,
F = (x₅+x₇−b₅)+(x₃+b₅−b₃)+(x₂+b₃−A) = δ(x₅,x₇)+δ(x₃,b₅)+δ(x₂,b₃). Since 0 < x₇ ≤ x₅ ≤ x₃ ≤ x₂
(as p ↦ p^{−n} is decreasing), b₅ ≤ x₅+x₇ ≤ 2x₅ and b₃ ≤ x₃+b₅ ≤ x₃+x₅+x₇ ≤ 3x₃. Hence

  δ(x₅,x₇) ≤ x₅x₇(x₅+x₇) ≤ 2x₅²x₇ = 2·175^{−n},
  δ(x₃,b₅) ≤ x₃b₅(x₃+b₅) ≤ x₃(2x₅)(3x₃) = 6x₃²x₅ = 6·45^{−n},

and, since x₂+b₃ ≤ x₂+3x₃ ≤ 4x₂,

  δ(x₂,b₃) ≤ x₂b₃(x₂+b₃) ≤ x₂(3x₃)(4x₂) = 12x₂²x₃ = 12·12^{−n}.

Since 45^{−n}, 175^{−n} ≤ 12^{−n}, summing gives F ≤ 12·12^{−n}+6·45^{−n}+2·175^{−n} ≤ 20·12^{−n}. ∎

**Proof of Theorem 5.1.** For a,b ≥ 0 with a ∈ [0,1), a⊕b − a = b(1−a²)/(1+ab) ≥ 0, and
a⊕b = (a+b)/(1+ab) ≤ a+b; applying both to y(n) = A⊕r (Lemma 5.4) gives A ≤ y(n) ≤ A+r. Since
S(n) = A+F,

  −F ≤ y(n)−S(n) ≤ r.

By Lemma 5.6, F ≤ 20·12^{−n} ≤ 20·11^{−n} ≤ 24·11^{−n}, and by Lemma 5.5, r ≤ 24·11^{−n}. Hence
|y(n)−S(n)| ≤ 24·11^{−n}. ∎

**Remark (Exact check at n=2, cross-checked three ways).** At n=2, t(2) = ζ(4)/ζ(2)² =
(π⁴/90)/(π²/6)² = 2/5 (this is also `OeisA114362.t_two` in the Lean file), so y(2) = 3/7 ---
matching the value w(2)=3/7 recorded independently in the `EXAMPLE` line of OEIS A348829, whose
author's w is the same quantity as our y under a different name. With S(2) = ¼+⅑+1/25+1/49 =
18589/44100, the exact defect is

  y(2)−S(2) = 3/7 − 18589/44100 = 311/44100,

positive and below 11^{−2}=1/121 since 311·121 = 37631 < 44100. The reviewer of the repaired proof
recomputed every intermediate quantity at n=2 as an exact rational: A = 4669/11581,
F = 9376309/510722100, R₁₁ = 1625/1728, r = 103/3353 --- values that chain together correctly
(r=(1−R₁₁)/(1+R₁₁) recovers 103/3353 from R₁₁=1625/1728) and that satisfy every inequality of
Lemmas 5.5 and 5.6 at the exact value n=2, the case at which the first proof attempt had failed
(Section 5.4 below).

**Remark (A sharper asymptotic, not formalized).** The repaired proof establishes, by the same
method with the further prime p=13 peeled from R₁₁, the stronger limit

  lim_{n→∞} (y(n)−S(n))/11^{−n} = 1,

which refines Theorem 5.1 from a big-O bound to an exact leading asymptotic. We record it because
it is part of the reviewed proof, but it is not part of the OEIS comment being formalized, and we
have not formalized it; Section 6 formalizes only the O(11^{−n}) statement of Theorem 5.1,
matching `formal-conjectures`'s `conjecture2` verbatim.

**Remark (What is *not* proved here).** Theorem 5.1 leaves the sign of y(n)−S(n) unresolved for
general n; at n=2 it is positive, but nothing above rules out the reverse. This is weaker than a
related conjecture Ordowski recorded the same day in OEIS A348829, restricted to even arguments:
0 < w(2n) − S(2n) < 11^{−2n} for every n>0, a strict two-sided pin with no leading constant. That
statement, and Ordowski's further 2024 remark that the prime-zeta tail satisfies
P(2n)−w(2n) ~ 12^{−2n} (consistent in order of magnitude with, though not implied by, the
O(12^{−n}) defect bound F of Lemma 5.6), are neither proved nor formalized here; we cite them in
Section 7 only as context for the same author's closely related conjectures.

### 5.4 The review chain

**Remark (Two refutations, two validations).** Theorem 5.1 was proved, refuted, repaired, and
re-validated in that order. A first draft (Claude, Fable 5) reached the correct overall shape ---
the Euler product, the ⊕-peeling identity, and the O(11^{−n}) conclusion --- but asserted uniform
bounds on the intermediate ⊕-corrections, such as x₅·(x₇⊕r) ≤ 2·35^{−n}, that are simply false for
small n. Two reviewers, working independently and without sight of each other's report, located
the same defect: Qwen3.8-Max showed the bound fails already at n=2 by bounding the finite tail
product over p∈{11,13,17,19,23} below 23/24, giving r > 1/47 and hence x₅·(x₇⊕r) > 2/1225 =
2·35^{−2}; GPT-5.6 ("Pro" effort) went further and exhibited the exact witness, inverting the
⊕-relations at n=2 to obtain x₃⊕(x₅⊕(x₇⊕r)) = 1/5, x₅⊕(x₇⊕r) = 1/11, and x₇⊕r = 7/137, so that
x₅·(x₇⊕r) = 7/3425 exceeds the claimed bound 2·35^{−2}=2/1225 by 69/167825. Both reviewers
returned INVALID.

The repair --- Lemmas 5.5 and 5.6 above, which replace the uniform pointwise bound on each nested
correction with the single exact telescoping identity F = δ(x₅,x₇)+δ(x₃,b₅)+δ(x₂,b₃) and a size
comparison between the x_p rather than an asymptotic estimate of each nested term --- was produced
by GPT-5.6 ("Pro" effort), the same model that had supplied the counterexample. Because the repair
therefore did not pass through an independent solver, we treat its own review as the operative
gate: it was checked, in separate sessions and blind to each other, by GPT-5.6 through `codex` and
by Qwen3.8-Max. Both returned VALID; the `codex` review is the source of the exact rationals
reproduced in the remark above, obtained by recomputing A, F, R₁₁, and r symbolically at n=2
rather than accepting the small-n estimates on faith.

---

## 6. Formal verification

### 6.1 Files, environment, and axiom audits

The four developments are self-contained Lean 4 files, each importing all of `mathlib`. The
toolchain is `leanprover/lean4:v4.34.0-rc1` with `mathlib` pinned at revision `v4.34.0-rc1`.
Elaboration times are wall-clock for `lake env lean <file>` on an Apple-silicon laptop with a warm
module cache and exclude the one-off cost of building `mathlib`.

| File | Main theorem | Lines | Elaboration |
|---|---|---:|---:|
| `A108211.lean` | `a108211` | 509 | 5.6 s |
| `A114831.lean` | `a114831` | 327 | 4.3 s |
| `A100434.lean` | `conjecture1/2/3` | 282 | 2.4 s |
| `A114362.lean` | `conjecture2` | 577 | 34.6 s |

No file contains `sorry`, `native_decide`, or any `axiom` declaration.

`A114362.lean` is markedly the slowest of the four to elaborate, consistent with its being the
only development that unfolds `mathlib`'s Euler-product theorem for the Riemann zeta function; the
figure above is the mean of three warm-cache runs (35.3 s, 31.1 s, 37.5 s), and the first,
cold-cache invocation in a fresh shell took 61.9 s.

Every file ends with an axiom audit. The complete output is:

```
'a108211' depends on axioms: [propext, Classical.choice, Quot.sound]
'a114831' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA100434Corrected.conjecture1' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA100434Corrected.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA100434Corrected.conjecture3' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA114362.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard axioms of Lean's classical foundation, on which `mathlib` itself
rests; in particular nothing is assumed beyond them, and no result is imported from an unverified
oracle. We note explicitly that `native_decide`, which would place the compiler's evaluator in the
trusted base, is used nowhere.

### 6.2 Statement fidelity

**A108211.** The Lean statement is

```lean
theorem a108211 (n : ℕ) (hn : 0 < n) :
    (16 * (n : ℤ) ^ 2 + 1 : ℤ) =
      ⌊ 1 / ((4 * (n : ℝ))⁻¹ - Real.log 2 +
        ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹) ⌋
```

which is, up to the harmless replacement of `(a n : ℝ) = (⌊·⌋ : ℝ)` by an equation in ℤ,
character-for-character the statement carried in `formal-conjectures` for this conjecture. The sum
is over `Finset.Icc (n+1) (2*n)`, i.e. Σ_{k=n+1}^{2n} 1/k, matching Kimberling's comment.

**A114831.** The `formal-conjectures` file defines the sequence through ℚ-valued division followed
by `Int.toNat` of the floor. We define it instead by ℕ-valued division,

```lean
a (n+3) = a (n+2) + (2 * a (n+2) * a (n+1)) / (a (n+2) + a (n+1))
```

which is the same function, since truncating division on ℕ *is* the floor of the rational quotient
of nonnegative integers. The conclusion,

```lean
Tendsto (fun n ↦ (a (n+1) : ℝ) / (a n : ℝ)) atTop (nhds (Real.sqrt 3))
```

is identical to the corpus statement. The first terms are checked against OEIS by `decide`:
a(3)=3, a(4)=5, a(5)=8, a(6)=14.

**A100434.** Here our statement necessarily differs from the corpus, since the corpus statement is
false; the difference is exactly the minus sign of (4.5), and it is documented in the file header.
The development lives in the namespace `OeisA100434Corrected` to keep it distinguishable. All other
definitions (a, c, d, e, f, g) are transcribed unchanged, including the integer-division form of e
and f.

**A114362.** The Lean statement is verbatim `formal-conjectures`'s `conjecture2`, including the
definition of `t`:

```lean
theorem conjecture2 :
    (fun n : ℕ => (1 - t n) / (1 + t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n)
```

character-for-character identical to the corpus file. Because an `isBigO` statement only asserts
*some* witness constant, the explicit value is not part of the statement being formalized; the
file supplies 56 (lemma `main_bound`), weaker than the 24 established informally in Theorem 5.1.
The gap is a formalization choice, not a mathematical one: the Lean proof bounds |y(n)−S(n)| by
two applications of the triangle inequality (`abs_sub_le`, then `abs_le`) through the auxiliary
quantity (1−Q₄(n))/(1+Q₄(n)), where Q₄(n) is the finite product over {2,3,5,7}, rather than the
signed one-sided bound −F ≤ y(n)−S(n) ≤ r used in the proof above; the two routes give 56 and 24
respectively for the same underlying estimates. We did not tighten the Lean constant, since the
corpus statement only asks for *some* C.

### 6.3 Notable techniques and `mathlib` workarounds

**The alternating harmonic series is not in `mathlib`.** The informal proof of Theorem 2.1 passes
through Mercator's series log 2 = Σ_{j≥1} (−1)^{j+1}/j (Lemma 2.3). At the pinned revision,
`mathlib` has `Real.hasSum_log_sub_log_of_abs_lt_one` for |x| < 1 but no statement of the series at
the boundary point, and no general alternating-series (Leibniz) test in `Analysis/SpecificLimits`.
Rather than formalize Abel's theorem or the integral-remainder argument, the Lean development
replaces the whole of Step 1 by an elementary squeeze, which we consider the most instructive part
of the formalization:

- `sum_ffun`: Σ_{m<n} 1/((2m+1)(2m+2)) = H_{2n} − H_n, proved by induction on n. This is
  Lemmas 2.2 and 2.4 fused into a *finite* identity, so the delicate regrouping of a conditionally
  convergent series never occurs.
- `harm_upper` and `harm_lower`: the two-sided estimate
  log((2n+1)/(n+1)) ≤ H_{2n} − H_n ≤ log 2 (n ≥ 1), each obtained by applying
  `Real.log_le_sub_one_of_pos` to the ratios (n+i)/(n+i+1) and (n+i+2)/(n+i+1) respectively and
  telescoping with `Finset.sum_range_sub`.
- Since log((2n+1)/(n+1)) → log 2, the squeeze
  (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`) gives H_{2n} − H_n → log 2;
  `summable_of_sum_range_le` then gives summability from the upper bound, and
  `hasSum_iff_tendsto_nat_of_nonneg` upgrades the partial-sum limit to `HasSum ffun (Real.log 2)`.

In effect the Lean proof *derives* the alternating harmonic sum as a by-product, using only
log x ≤ x − 1.

**Polynomial certificates are discharged by `linarith`, not `nlinarith`.** The five certificates of
Appendix A are degree 5 to 16 polynomial inequalities in one real variable with coefficients up to
sixteen digits. General nonlinear arithmetic does not cope with these. The shift x = 1+t, t ≥ 0
converts each into a claim that a specific nonnegative combination of the monomials t⁰, …, t¹⁶ is
positive --- a *linear* claim in the atoms t^k. Each certificate lemma therefore begins

```lean
obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
```

and closes with `linarith [ht, pow_nonneg ht 2, …, pow_nonneg ht 16]`. This is the single most
important implementation decision in `A108211.lean`: it is what allows a degree-16 certificate with
a leading coefficient of 1.1 × 10¹⁰ to be checked in a few seconds. The file also raises
`maxHeartbeats` to 2,000,000 for the largest of them.

**Telescoping to the limit.** The sandwich of Lemma 2.8 is formalized without ever forming the
series Σ Δ(m): both estimates are proved for every finite partial sum, via the telescoping lemma
`Finset.sum_range_sub'` applied to m ↦ h(n+m) and m ↦ g(n+m), and then transported to the limit
with `le_of_tendsto_of_tendsto'` and `le_of_tendsto'`. The convergence h(n+m) → 0 needed for the
lower estimate comes from the decay certificate h(x) ≤ 1/x (Lemma 2.7, `cert7` in the file)
combined with `squeeze_zero`. Because the window lemmas `window_low` and `window_high` are
themselves strict, the formal sandwich is stated non-strictly, as
`hf n ≤ T n ∧ T n ≤ hf n + gf n`, and strictness of the final chain is inherited from them; the
deficit-retention argument of Lemma 2.8 is therefore present in the paper but not needed in the
file.

**Floors via Euclidean division.** In `A114831.lean` the fractional defect θ_n of (3.3) is never
introduced. Instead the ℕ-level identity `Nat.div_add_mod` --- p = mq + r with 0 ≤ r < m, for
m = a(k+2)+a(k+1) and p = 2a(k+2)a(k+1) --- is cast to ℝ and fed to a purely algebraic lemma
`ratio_bound_core`, which yields the two-sided bound F(R_{k+1}) − 1/a(k+2) < R_{k+2} ≤ F(R_{k+1})
in one step. This is both shorter and more robust than reasoning about `Int.floor` of a rational.

**A general contraction-with-forcing lemma.** `mathlib` has Banach fixed points but nothing
directly applicable to a perturbed contraction e_{k+1} ≤ ½e_k + b_k with b_k → 0 and no a priori
bound on Σ b_k. `A114831.lean` proves the needed statement from scratch (`aux_geom`,
`tendsto_e_zero`) by an explicit ε/N argument: given b_k ≤ ε for k ≥ N, unrolling m steps gives
e_{N+m} ≤ 2^{−m}e_N + 2ε, and the two terms are then made small separately. This replaces the
tail-splitting computation (3.8) of the paper; the explicit bound (3.1) is stated in the paper but
is not part of the formal statement, which asserts only the limit.

**Integer division and `omega`.** In `A100434.lean` the sequences e and f are ℤ-valued and defined
with integer division, faithfully to the corpus. The two divisibility lemmas `d_even_even` and
`d_odd_even` (2 ∣ d(2k), 2 ∣ d(2k+1), both by two-step induction) are what make the halvings exact;
once they and the linear identities (4.10), (4.11) are in context, `omega` closes both parity cases
of `conjecture2`, since it handles division by a numeral in the presence of divisibility
hypotheses. All inductions use `Nat.twoStepInduction`, matching the order-four (parity-decoupled)
recurrence.

**An elementary Euler-product bridge, avoiding `tprod` convergence machinery.** `A114362.lean`
needs ζ(m) = Π_p (1−p^{−m})^{−1} for real m ≥ 2; `mathlib` supplies this as
`riemannZeta_eulerProduct`, a statement about the limit, along `Filter.atTop`, of the finite
partial products EP(m,N) := Π_{p<N, p prime} (1−p^{−m})^{−1} (the primes below N being
`Nat.primesBelow` N in the file). Rather than upgrade this to `mathlib`'s general infinite-product
(`Multipliable`/`tprod`) API for products indexed by primes --- machinery not otherwise present in
this file, since no existing lemma there is stated for a product over primes specifically --- the
whole development works with the N-indexed finite partial products `EP` and `qq` throughout,
taking limits only once, at the very end, in `tendsto_prod_qq`. The peeling of p=2,3,5,7 from the
tail is likewise finite: `Finset.prod_sdiff` splits `Nat.primesBelow` N into {2,3,5,7} and its
complement for every fixed N ≥ 8, and the complement's product is bounded, for every such N, using
the finite-product inequality `one_sub_sum_le_prod` and the explicit tail estimate `tail_pow`
(itself reduced, via a comparison to Σ 1/k², to the fully elementary telescoping bound `tail_sq`);
only the resulting two-sided bound on the finite product is then passed to the limit, in
`t_upper` and `t_lower`. This keeps every step of the Euler-product argument at the level of
ordinary `Finset` sums and products, at the cost of re-deriving, in `tail_sq` and `tail_pow`, an
elementary series-comparison lemma that a general primes-indexed `tprod` API would have supplied
directly.

---

## 7. Related work

Automated and AI-assisted contributions to research mathematics have grown quickly in the last
three years. FunSearch [8] demonstrated that a language model in a genetic programming loop, with
an exact evaluator in the loop, can find record constructions in extremal combinatorics;
AlphaEvolve [9] extended the evolutionary-search paradigm to a broader class of construction and
algorithm-design problems. On the community side, the Erdős Problems site and its AI-contributions
wiki [10] have collected a substantial number of AI-assisted resolutions and partial results, with
an explicit and useful apparatus of caveats about selection bias, literature coverage, and the
difference between an argument and a verified proof. The `formal-conjectures` corpus [5] supplies
formal statements of open conjectures --- the raw material for work of the kind reported here ---
and `mathlib` [7] supplies the verified background theory.

Our contribution should be placed modestly relative to that work. The conjectures resolved here are
small; none is a named open problem, and two of the four are elementary. What is distinctive is the
completeness of the chain: statement selection, proof discovery, adversarial refutation and repair,
formalization, and axiom audit were all carried out by automated systems, and the end product is a
machine-checked theorem rather than a natural-language argument awaiting referee attention. We make
no claim about how this scales to harder problems.

The same author who posed A114362 recorded, in the neighbouring entry A348829, both a sharper
even-argument conjecture and a 2024 remark relating the same quantity to the prime zeta function
[4]; Theorem 5.1's Remark "What is not proved here" (Section 5) states precisely how those two
further conjectures relate to, and go beyond, what we prove.

---

## 8. Limitations

1. **The conjectures are minor.** All four are conjectural comments in OEIS entries, not problems
   of record. A100434 carries OEIS's own `easy` keyword, and its identities are six routine
   inductions. A114831's answer was already guessed correctly in the OEIS entry and in the
   `formal-conjectures` docstring; what was missing, and what we supply, is a proof that the limit
   exists at all. Two of the four, Theorems 2.1 and 5.1, required a genuine idea beyond routine
   calculation: a rational telescoping certificate accurate to O(n^{−7}) against a Θ(n^{−4})
   window in the first case, and an explicit O(11^{−n}) error bound extracted from a convergent
   Euler product in the second; even there the ideas are classical in kind.

2. **The first attempt was wrong.** Our initial proof of Theorem 2.1 rested on a comparison
   inequality that is false at m = 2, and would have been insufficiently precise even if true.
   The same happened with Theorem 5.1: our initial proof asserted uniform bounds on nested
   Möbius-composition corrections that are false already at n = 2, and two independent reviewers
   found the identical defect (Section 5.4). Both failures were caught by adversarial review, not
   by the solver. We report this because the success rate of the first gate, not of the pipeline,
   is the honest measure of a solver, and here it is 2 out of 4 theorems, not 4 out of 4.

3. **One interpretive step is not mathematics.** The corrected reading (4.5) of Dement's b is a
   judgement about the intent of a natural-language comment. We have set out the textual and
   numerical evidence in Section 4; a reader who rejects it is entitled to say that we proved a
   different statement from the one conjectured. The literal statement is false, so some such
   judgement is unavoidable.

4. **Literature search was automated.** We checked for prior proofs by automated search and found
   none, but automated searches miss things, and OEIS comments of this vintage may well have been
   settled in correspondence or in unindexed notes. Priority claims should be read with that caveat.

5. **Formalization covers the theorems, not the paper.** The Lean files verify the four theorem
   statements. They do not verify the explicit error bound (3.1), the deficit-retention refinement
   of Lemma 2.8, the sharper asymptotic of Theorem 5.1's remark, or the numerical assertions in
   Section 1.3; those were checked by exact rational computation only. The formalized witness
   constant for Theorem 5.1 is 56, not the 24 proved informally, for the reason given in Section 6.
   Nor did we formalize a corrected version of A109074.

6. **We did not repair the upstream corpus.** The two mis-formalizations of Section 1.3 are
   reported here and left in place; correcting them is a matter for the maintainers of that corpus.

---

## Appendix A. Certificate polynomials for Theorem 2.1

This appendix makes Section 2 self-contained. Every inequality used there is reduced to the
positivity of a single univariate polynomial with integer coefficients, exhibited below in the
shifted variable t = x − 1 ≥ 0. In each case the polynomial arises as the numerator of a difference
of rational functions over a common denominator that is manifestly positive for x ≥ 1 (each
denominator is a product of factors of the form αx + β with α, β > 0, and of 16x²+1 or 8x²+1).
Since every listed coefficient is a positive integer, each numerator is positive for all t ≥ 0,
hence for all real x ≥ 1; no approximation, and in particular no decimal, enters at any point.

Recall from (2.1)–(2.4): A(x) = 1024x⁵ + 5888x⁴ + 12928x³ + 13312x² + 6148x + 843,
B(x) = 4(4x+1)(2x+1)(4x+3)(4x+5)(2x+3)(4x+7), h = A/B, g(x) = 60/(4x+1)⁷,
f₁(x) = 1/(4x) − 1/(16x²+1), f₂(x) = 1/(4x) − 1/(16x²+2).

### C1. The defect identity (Lemma 2.5)

  1/((2m+1)(2m+2)) − (h(m) − h(m+1)) = 63(16m²+120m+119) / (2 P(m)),

  P(m) = (m+1)(2m+1)(2m+3)(2m+5)(4m+1)(4m+3)(4m+5)(4m+7)(4m+9)(4m+11).

This is an identity, not an inequality: after clearing denominators both sides are polynomials of
degree 12 and the difference is identically zero. It is the only certificate of the five that is
checked by expansion rather than by sign inspection.

### C2. The majorant (Lemma 2.6)

  g(m) − g(m+1) − Δ(m) = N₂(m)/D₂(m),

  D₂(m) = 2(m+1)(2m+1)(2m+3)(2m+5)(4m+1)⁷(4m+3)(4m+5)⁷(4m+7)(4m+9)(4m+11).

**Table A.1.** The shifted numerator N₂(1+t), of degree 14. Minimum coefficient 11,274,289,152;
constant term 1,646,809,468,266,375. All fifteen coefficients are positive, so N₂(1+t) > 0 for
t ≥ 0.

| k | coefficient of t^k in N₂(1+t) |
|---:|---:|
| 14 | 11,274,289,152 |
| 13 | 372,051,542,016 |
| 12 | 5,878,132,506,624 |
| 11 | 57,656,538,562,560 |
| 10 | 387,335,580,549,120 |
| 9 | 1,873,929,205,972,992 |
| 8 | 6,717,806,381,039,616 |
| 7 | 18,122,661,920,047,104 |
| 6 | 36,993,936,957,112,320 |
| 5 | 56,922,611,911,495,680 |
| 4 | 65,063,899,140,917,760 |
| 3 | 53,630,918,265,563,520 |
| 2 | 30,166,767,811,516,080 |
| 1 | 10,374,002,614,521,000 |
| 0 | 1,646,809,468,266,375 |

### C3. The lower window (Lemma 2.9)

  h(x) − f₁(x) = N₃(x)/D₃(x),
  D₃(x) = 4x(2x+1)(2x+3)(4x+1)(4x+3)(4x+5)(4x+7)(16x²+1).

**Table A.2.** N₃(1+t) = 256t⁵ + 2816t⁴ + 12096t³ + 24688t² + 22223t + 6756. Minimum coefficient
256. Exact value at x = 1: h(1) − f₁(1) = 563/294525.

| k | coefficient of t^k in N₃(1+t) |
|---:|---:|
| 5 | 256 |
| 4 | 2,816 |
| 3 | 12,096 |
| 2 | 24,688 |
| 1 | 22,223 |
| 0 | 6,756 |

### C4. The upper window (Lemma 2.9)

  f₂(x) − h(x) − g(x) = N₄(x)/D₄(x),
  D₄(x) = 4x(2x+1)(2x+3)(4x+1)⁷(4x+3)(4x+5)(4x+7)(8x²+1).

**Table A.3.** The shifted numerator N₄(1+t), of degree 9. Minimum coefficient 393,216. Exact value
at x = 1: f₂(1) − h(1) − g(1) = 12743/21656250.

| k | coefficient of t^k in N₄(1+t) |
|---:|---:|
| 9 | 393,216 |
| 8 | 6,291,456 |
| 7 | 43,757,568 |
| 6 | 169,863,168 |
| 5 | 404,609,280 |
| 4 | 614,989,440 |
| 3 | 598,254,960 |
| 2 | 359,583,120 |
| 1 | 120,914,895 |
| 0 | 17,203,050 |

### C5. The decay bound (Lemma 2.7)

  1/x − h(x) = ( B(x) − x·A(x) ) / ( x·B(x) ),

where x·B(x) > 0 for x ≥ 1 and the numerator, after the shift, is the polynomial of Table A.4.

**Table A.4.** Certificate C5, establishing h(x) ≤ 1/x for x ≥ 1 and hence h(x) → 0.

| k | coefficient of t^k in B(1+t) − (1+t)A(1+t) |
|---:|---:|
| 6 | 3,072 |
| 5 | 37,120 |
| 4 | 184,448 |
| 3 | 482,304 |
| 2 | 699,916 |
| 1 | 534,509 |
| 0 | 167,757 |

All five certificates were computed by exact rational arithmetic, recomputed independently by a
reviewing model, and re-derived a third time inside Lean, where C2–C5 appear as the lemmas `cert2`,
`cert5`, `cert6`, `cert7` and C1 as `delta_eq`.

---

## References

[1] OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*, https://oeis.org.
Sequences cited: A100434 (N. J. A. Sloane, 21 November 2004, suggested by correspondence from
C. Dement; conjectural comment of C. Dement, 18 December 2004), A108211 (R. Zumkeller, 15 June
2005; conjectural comment of C. Kimberling, 9 September 2014), A114831 (J. V. Post, 19 February
2006), A114362 (B. Cloitre, 9 February 2006; conjectural comments of T. Ordowski, 5 January 2022
and 13 November 2022), A348829 (T. Ordowski, 1 November 2021; conjectural comments of
13 November 2022 and 6 November 2024). Also referenced: A001333, A001764, A002315, A005156,
A005319, A052542, A075870.

[2] C. Kimberling, comment on OEIS A108211, 9 September 2014: "Conjecture:
a(n) = floor(1/(1/(4n) − log(2) + 1/(n+1) + 1/(n+2) + ⋯ + 1/(2n)))."

[3] C. Dement, comment on OEIS A100434, 18 December 2004, defining the auxiliary sequences
b, c, d, e, f, g and conjecturing c(n)+d(n) = e(n)+f(n) = g(n)+a(n) = b(n).

[4] T. Ordowski, comments on OEIS A114362 and A348829. A114362, 13 November 2022: "Conjecture:
(1−t(n))/(1+t(n)) = 1/2ⁿ+1/3ⁿ+1/5ⁿ+1/7ⁿ+O(1/11ⁿ), where t(n)=ζ(2n)/ζ(n)²." A348829, 13 November
2022: "Conjecture: 0 < w(2n) − (1/2^{2n}+1/3^{2n}+1/5^{2n}+1/7^{2n}) < 1/11^{2n} for every n>0."
A348829, 6 November 2024: "It can be proven that P(2n) − w(2n) ~ 1/12^{2n}, where
P(x) = Σ_p 1/p^x is the prime zeta function of real x>1."

[5] Google DeepMind, *formal-conjectures*: a collection of formalized conjectures in Lean 4,
https://github.com/google-deepmind/formal-conjectures. Files referenced:
`FormalConjectures/OEIS/100434.lean`, `108211.lean`, `109074.lean`, `114362.lean`, `114831.lean`.

[6] L. de Moura and S. Ullrich, *The Lean 4 theorem prover and programming language*, in: Automated
Deduction — CADE 28, Lecture Notes in Computer Science 12699, Springer, 2021, pp. 625–635.

[7] The mathlib Community, *The Lean mathematical library*, in: Proceedings of the 9th ACM SIGPLAN
International Conference on Certified Programs and Proofs (CPP 2020), ACM, 2020, pp. 367–381,
https://github.com/leanprover-community/mathlib4.

[8] B. Romera-Paredes, M. Barekatain, A. Novikov, M. Balog, M. P. Kumar, E. Dupont, F. J. R. Ruiz,
J. S. Ellenberg, P. Wang, O. Fawzi, P. Kohli, and A. Fawzi, *Mathematical discoveries from program
search with large language models*, Nature **625** (2024), 468–475.

[9] A. Novikov et al., *AlphaEvolve: a coding agent for scientific and algorithmic discovery*,
Google DeepMind, 2025.

[10] T. F. Bloom (site), T. Tao (community database), and contributors, *Erdős Problems* and the associated AI-contributions wiki,
https://www.erdosproblems.com, https://github.com/teorth/erdosproblems.
