# Bala's $D(r)$ Divisibility Conjecture for A211417: a Proof with an Explicit Constant

**AutoMath Collaboration**
*(Claude Fable 5, GPT-5.6, Qwen3.8-Max, operated autonomously)*

17 August 2026

> **Disclosure of the production pipeline.** Every mathematical step reported in this paper was
> produced by automated systems; no human supplied a definition, a lemma, a proof idea, or a
> correction. The proof of Theorem 3.5 — the step function, the three lemmas, and the prime-power
> stratification — was found by Claude (Fable 5). It was then submitted, in separate sessions and
> without the solver's reasoning trace, to two adversarial reviewers from different vendors:
> OpenAI GPT-5.6 through the `codex` command-line interface, and Qwen3.8-Max through its web
> interface. Both returned VALID for the main theorem and located no critical error in
> Lemmas 3.1, 3.2, 3.4 or in Theorem 3.5; both returned VALID-WITH-GAPS for the document as a
> whole, and every gap they reported is either repaired below or recorded, unrepaired, in
> Section 10. The repairs were then put through a second, targeted review round, which returned
> VALID on all five items nominated to it. Two items in this paper originate with the reviewers
> rather than the solver and are attributed in place: the lower bound of Corollary 3.8
> (GPT-5.6/`codex`), which refuted a false asymptotic claim in the first draft, and the demand for
> an explicit impossibility argument that became Proposition 5.1. The Lean 4 development of
> Section 8 was written by Claude (Fable 5); the Lean compiler is the final arbiter of the
> statements listed there. Orchestration — problem selection, freshness auditing, review
> scheduling, and the drafting of this paper — was likewise automated. Responsibility for what
> follows rests with the reader who checks the argument and the Lean file.

*This file is a faithful transcription of `main.tex`. Numbering follows the compiled PDF.*

---

## Abstract

Let $a(n) = (30n)!\,n!/\bigl((15n)!\,(10n)!\,(6n)!\bigr)$, entry A211417 of the OEIS and one of
Vasyunin's $52$ sporadic integral factorial ratio sequences of height $1$. Peter Bala conjectured
on 28 August 2025 that for every $r \ge 1$ there is a constant $D(r)$ such that $D(r)\,a(n)$ is
divisible by $\prod_{i \le r,\ \gcd(i,30)=1}(30n-i)$ for all $n \ge 0$; the case $r=1$, that
$(30n-1) \mid a(n)$, was proved in 2026 by DeepMind's AlphaProof/Nexus system, and the general
case was carried as `research open` in the `formal-conjectures` corpus. We prove the conjecture
for all $r \ge 1$, with the explicit and computable constant

$$D(r) \;=\; \prod_{\substack{p \le r\\ \gcd(p,30)=1}} p^{\,E(p,r)},
\qquad
E(p,r) \;=\; \sum_{k \ge 1,\ p^k \le r}\ \max_{c \bmod p^k}\
\#\{\, i \in L_r : i \equiv c \ (\mathrm{mod}\ p^k)\,\},$$

where $L_r = \{i \le r : \gcd(i,30)=1\}$, so that $D(1) = \cdots = D(6) = 1$, $D(13) = 1001$,
$D(23) = 81800719$. The proof has three steps: a rigidity lemma stating that the Landau step
function of the ratio takes the value $1$ on every residue class coprime to $30$; a local lemma
promoting this to every $i$ with $\gcd(i,30)=1$, which generalises the mechanism used for $r=1$;
and a prime-power stratification lemma showing that all layers $p^k > r$ are paid for, one for one
and without loss, by distinct Legendre summands of $\nu_p(a(n))$, so that only the finitely many
layers $p^k \le r$ need a constant at all. We prove $\log D(r) = \Theta(r \log r)$ for this
constant. The same method proves Bala's companion $C(k,r)$ family for $k \in \{2,3,5\}$ in general
$r$, and we show that the sign in $30n - i$ is not a typographical accident: no nonzero constant
$D$ makes $(30n+i) \mid D\,a(n)$ hold identically. A Lean 4 development, verified against
`mathlib` and depending only on `propext`, `Classical.choice` and `Quot.sound`, proves the
conjecture in the strengthened form $\exists D > 0$; as a by-product it exhibits a three-line proof
that the corpus's literal statement, which quantifies over $D \in \mathbb{Z}$ without excluding
$D=0$, is vacuous. We record that the existence claim was independently announced, without a public
proof text, in `formal-conjectures` issue #4923 one day before this paper was completed; we make no
priority claim, and we show that the constant announced there, $\operatorname{lcm}(1,\dots,r)^{|L_r|}$,
is a multiple of ours.

---

## 1. Introduction

### 1.1 An integral factorial ratio and Bala's conjectures

A *factorial ratio sequence* is a sequence of the shape

$$u(n) \;=\; \frac{\prod_{s=1}^{S} (A_s n)!}{\prod_{t=1}^{T} (B_t n)!},
\qquad A_s, B_t \in \mathbb{Z}_{\ge 1}, \qquad \sum_s A_s = \sum_t B_t ,
\tag{1.1}$$

and it is called *integral* if $u(n) \in \mathbb{Z}$ for every $n \ge 0$. The classification of
integral factorial ratios is a classical problem going back to Chebyshev's use of
$(30n)!\,n!/\bigl((15n)!\,(10n)!\,(6n)!\bigr)$ in his work on $\pi(x)$, and was brought to a sharp
form by Rodriguez-Villegas, Vasyunin, Bober and Soundararajan [4, 5]: in the *height* $T-S = 1$
case the integral ratios consist of a handful of infinite parametric families together with a
sporadic list, catalogued by Vasyunin, of $52$ sequences, recorded in the OEIS as A295431. The
sequence

$$a(n) \;=\; \frac{(30n)!\; n!}{(15n)!\;(10n)!\;(6n)!},
\qquad
a(0),a(1),a(2) \;=\; 1,\ 77636318760,\ 53837289804317953893960,
\tag{1.2}$$

is OEIS A211417 [1], Chebyshev's own ratio, and is the most famous of the $52$.

On 28 August 2025 Peter Bala contributed to A211417 a group of divisibility observations [2].
Five of them are explicit:

$$\frac{a(n)}{30n-1},\qquad
\frac{7\,a(n)}{2n+1},\qquad
\frac{a(n)}{3n+1},\qquad
\frac{a(n)}{5n+1},\qquad
\frac{42\,a(n)}{(2n+1)(3n+1)(5n+1)}$$

are all integers for every $n$ (checked to $n = 1000$). The last one is a genuinely different kind
of statement, because a single constant has to serve a *product* of linear forms which are not
pairwise coprime as $n$ varies — for instance $\gcd(2n+1,5n+1) = 3$ at $n=1$. Bala then stated the
general form, which is the subject of this paper:

> "More generally, for $r \ge 1$, we conjecture that there exists a constant $D(r)$ such that
> $D(r) \cdot a(n) / \prod_{i=1..r,\; i \text{ coprime to } 30}(30n-i)$ is integral for all $n$."
> — Peter Bala, 28 August 2025

Throughout we write

$$L_r \;=\; \{\, i \in \mathbb{Z} : 1 \le i \le r,\ \gcd(i,30) = 1 \,\},
\qquad
P_r(n) \;=\; \prod_{i \in L_r} (30n - i),
\tag{1.3}$$

so that the conjecture asks for a constant $D(r) \ne 0$ with $P_r(n) \mid D(r)\,a(n)$ for all
$n \ge 0$. Bala's comment closes with the remark that "similar results may hold for all the $52$
sporadic integral factorial ratio sequences listed in A295431"; Section 6 extracts from our proof a
finitely checkable sufficient criterion for exactly that.

### 1.2 What was known

The case $r = 1$ is $L_r = \{1\}$, $P_1(n) = 30n-1$, and the assertion is $(30n-1) \mid a(n)$ with
$D(1) = 1$. This was proved in 2026 by DeepMind's AlphaProof/Nexus system [6] and is recorded as
solved both in the OEIS entry (comment of R. Stephan, 30 June 2026) and in the `formal-conjectures`
corpus [7], whose file `FormalConjectures/OEIS/211417.lean` carries the machine statement. The four
$r=1$ statements for $2n+1$, $3n+1$, $5n+1$ and the $42$-product were formalised in Lean by the
GitHub user KitaKen1 and marked solved in that corpus on 16 August 2026.

The general statement was not known. In the same corpus file it is carried as

```lean
@[category research open, AMS 11]
theorem general_divisibility (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) := by
  sorry
```

and a freshness audit carried out on 17 August 2026 — reading the corpus source directly, the
`alphaproof-nexus-results` repository file list, the live OEIS page, and an arXiv abstract search —
found no public proof. The one competing announcement that audit did find, made one day before this
paper was completed, is discussed in full in Section 7; we do not claim to be first.

### 1.3 Results

Our main theorem proves the conjecture and, beyond mere existence, exhibits a constant in closed
form.

> **Theorem A (= Theorem 3.5).** For $r \ge 1$ put
> $$E(p,r) \;=\; \sum_{k \ge 1,\ p^k \le r}\ \max_{c \bmod p^k}\
>   \#\{\, i \in L_r : i \equiv c \ (\mathrm{mod}\ p^k) \,\},
> \qquad
> D(r) \;=\; \prod_{\substack{p \le r \\ \gcd(p,30)=1}} p^{\,E(p,r)} .$$
> Then $P_r(n) \mid D(r)\, a(n)$ in $\mathbb{Z}$ for every $n \ge 0$.

The constant is small: $D(r) = 1$ for $1 \le r \le 6$, $D(7) = 7$, $D(13) = 1001$,
$D(23) = 81800719$, and $\log D(r) = \Theta(r \log r)$ (Corollary 3.8). For $r \le 19$ it is
exactly the empirically minimal constant; the first slack appears at $r = 23$ (Section 3.6).

The same three lemmas prove Bala's companion family in general $r$, of which his statements for
$2n+1$, $3n+1$ and $5n+1$ are the cases $r=1$.

> **Theorem B (= Theorem 4.3).** Let $k \in \{2,3,5\}$, $m = 30/k$ and
> $L^{(k)}_r = \{ i \le r : \gcd(i,k) = 1\}$. Then
> $$\prod_{i \in L^{(k)}_r} (kn + i) \ \Big|\ C(k,r)\cdot a(n)
> \qquad (n \ge 0),
> \qquad
> C(k,r) = \prod_{\substack{p \le mr\\ p \nmid k}} p^{\,E_k(p,r)},$$
> where $E_k(p,r) = \sum_{j \ge 1,\ p^j \le mr} \max_c \#\{ i \in L^{(k)}_r : i \equiv c \
> (\mathrm{mod}\ p^j)\}$.

Bala writes $30n - i$ with a minus sign but $kn + i$ with a plus sign. That asymmetry is forced:

> **Theorem C (= Proposition 5.1).** Let $\gcd(i,30) = 1$. There is no constant $D \ne 0$ with
> $(30n + i) \mid D\,a(n)$ for all $n \ge 0$.

Finally, Section 8 reports a Lean 4 development which proves the conjecture in the strengthened,
non-vacuous form $\exists D > 0$, recovers the AlphaProof/Nexus $r=1$ theorem as a corollary of the
general machinery, and exhibits a three-line proof that the corpus's literal existential statement
is vacuous as written.

### 1.4 The method in one paragraph

Write $\Delta(x) = \lfloor 30x\rfloor + \lfloor x\rfloor - \lfloor 15x\rfloor - \lfloor 10x\rfloor
- \lfloor 6x\rfloor$, the Landau step function of (1.2). Legendre's formula gives
$\nu_p(a(n)) = \sum_{k \ge 1} \Delta(n/p^k)$, and $\Delta$ takes only the values $0$ and $1$; so
$\nu_p(a(n))$ *counts the layers $k$ at which $\Delta(n/p^k) = 1$*. Lemma 3.1 says $\Delta$ equals
$1$ on every residue class $c$ with $\gcd(c,30)=1$; Lemma 3.2 converts this into the statement that
a single divisibility $p^k \mid 30n - i$ with $p^k > i$ *buys* the layer $k$, i.e. forces
$\Delta(n/p^k) = 1$. The difficulty of the conjecture is entirely in the product: two indices
$i \ne i'$ can share a prime, and a shared prime would be counted twice on the left of the desired
inequality while the corresponding layer can only be counted once on the right. Lemma 3.4 resolves
this by *stratifying by the power rather than by the index*: at every layer $k$ with $p^k > r$ the
witness is unique, because two witnesses would force $p^k \mid i - i'$ with $0 < |i-i'| < r < p^k$.
Hence all high layers are paid for exactly, one for one, and the constant is needed only for the
finitely many low layers $p^k \le r$, where the crude but $n$-independent bound "size of the largest
residue class of $L_r$ modulo $p^k$" applies. Summing that bound over $k$ is the definition of
$E(p,r)$.

### 1.5 Verification protocol, and how to read this paper

Every numbered statement below carries a **verification status** line recording exactly how it was
checked. Three kinds of evidence appear, and they are not interchangeable.

*Adversarial review.* The complete argument was submitted, in separate sessions and without the
solver's reasoning trace, to two reviewers from vendors other than the solver's: GPT-5.6 through
`codex`, and Qwen3.8-Max. Both were instructed to classify each objection as CRITICAL ERROR or
JUSTIFICATION GAP and to return a verdict. Both returned VALID for Theorem 3.5 and for the three
lemmas, and VALID-WITH-GAPS for the document as a whole. This gate did real work: it destroyed a
false asymptotic corollary of the first draft (see Corollary 3.8, whose lower bound is the
reviewer's own construction), and it correctly refused an impossibility claim that had been asserted
on the strength of a local computation, which is why Proposition 5.1 exists. The two reviews are
consistent with each other in verdict and largely disjoint in the gaps they report; Section 10 lists
every gap and its disposition, including the ones we did not close.

The material written *in response* to that first pass was then put through a second, targeted round
with the Qwen reviewer, covering exactly the five items that the first pass could not have seen:
Proposition 5.1; Lemma 4.2 together with the expanded proof of Theorem 4.3; the upper bound of
Corollary 3.8; the judgement that Bala's mixed product is *not* covered by Theorem 4.3
(Remark 4.5); and the attribution of the exponent jumps in Table 2. All five came back OK, with no
critical error and no justification gap; the verdict for that round is VALID. Status lines below
cite it as "round 2". Its one editorial request — that the scope of Theorem 4.3 at $r=1$ be stated
so that it cannot be misread as covering the mixed product — is implemented in Section 4.

*Formal verification.* A Lean 4 file, checked against `mathlib` with an axiom audit, proves the
conjecture in the form $\exists D > 0$. What it does *not* do is formalise the sharp constant $D(r)$
of Theorem 3.5: the Lean witness is the deliberately crude $(r!)^{r^2}$. Statements whose status
line says "Lean" are machine-checked; statements whose status line does not say "Lean" are not, and
Section 8 says precisely which is which.

*Computation.* A short Python script, `a211417_verify.py`, checks every finite assertion in this
paper and every theorem end-to-end in a bounded range. A second, independently written script by the
`codex` reviewer re-checks the main divisibility through a disjoint code path (no SymPy, no
factorial construction, trial division and Legendre valuations only). Computation is evidence
against blunders, not a proof, and no status line below rests on computation alone unless it says
so.

---

## 2. The Landau step function

### 2.1 Definition, periodicity, and the table of cell values

**Definition 2.1.** For $x \in \mathbb{R}$ put

$$\Delta(x) \;=\; \lfloor 30x \rfloor + \lfloor x \rfloor - \lfloor 15x \rfloor
  - \lfloor 10x \rfloor - \lfloor 6x \rfloor .$$

Because the coefficients balance, $30 + 1 - 15 - 10 - 6 = 0$, we have $\Delta(x+1) = \Delta(x)$, so
$\Delta$ depends only on the fractional part $\{x\}$. On $[0,1)$ it is constant on each of the
thirty cells $[j/30,(j+1)/30)$. Indeed let $t$ lie in the $j$-th cell, so $\lfloor 30t\rfloor = j$.
For $d \in \{2,3,5\}$ we have $(30/d)\,t \in [\,j/d,\ (j+1)/d\,)$, and this interval lies inside
$[\,\lfloor j/d\rfloor,\ \lfloor j/d\rfloor + 1)$ because $\lfloor j/d\rfloor \le j/d$ and
$(j+1)/d \le \lfloor j/d\rfloor + 1$, the latter being $(j \bmod d) \le d-1$. Hence

$$\lfloor 15t \rfloor = \lfloor j/2 \rfloor,\qquad
\lfloor 10t \rfloor = \lfloor j/3 \rfloor,\qquad
\lfloor 6t \rfloor = \lfloor j/5 \rfloor ,$$

and $\Delta(t) = \Delta_j$ with

$$\Delta_j \;=\; j - \lfloor j/2 \rfloor - \lfloor j/3 \rfloor - \lfloor j/5 \rfloor,
\qquad j = 0,1,\dots,29 .
\tag{2.1}$$

**Table 1.** The thirty cell values (2.1). The eight residues coprime to $30$, namely
$1,7,11,13,17,19,23,29$, all carry the value $1$ (Lemma 3.1); the second row read backwards is the
complement of the first, i.e. $\Delta_{29-j} = 1 - \Delta_j$ (Lemma 2.3).

| $j$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\Delta_j$ | 0 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 | 0 | 1 | 0 | 1 | 1 |

| $j$ | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\Delta_j$ | 0 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |

Two properties of this table are used throughout.

**Lemma 2.2 (Chebyshev nonnegativity).** $\Delta_j \in \{0,1\}$ for all $j$; in particular
$\Delta(x) \ge 0$ for all real $x$.

*Proof.* Writing $\lfloor j/d\rfloor = j/d - \{j/d\}$ and using
$\tfrac12 + \tfrac13 + \tfrac15 = \tfrac{31}{30}$,

$$\Delta_j \;=\; j - \frac{31j}{30} + \{j/2\} + \{j/3\} + \{j/5\}
\;=\; \{j/2\} + \{j/3\} + \{j/5\} - \frac{j}{30} .$$

For $0 \le j \le 29$ the right-hand side is $> 0 - \tfrac{29}{30} > -1$ and
$\le \tfrac12 + \tfrac23 + \tfrac45 = \tfrac{59}{30} < 2$. Being an integer,
$\Delta_j \in \{0,1\}$; the individual values are those of Table 1. The nonnegativity is Chebyshev's
classical reason for the integrality of $a(n)$; a formal proof that does not consult the table is
`f_nonneg` in Section 8, which reduces $\Delta(n/d) \ge 0$ to a linear-arithmetic fact about
$\lfloor 30(n \bmod d)/d\rfloor \le 29$. $\blacksquare$

**Verification status.** Dual review (both reviewers recomputed the table independently and obtained
only the values $0$ and $1$); Lean (`f_nonneg`, for the nonnegativity in the form actually used);
computational.

**Lemma 2.3 (Reflection identity).** $\Delta_j + \Delta_{29-j} = 1$ for $0 \le j \le 29$.

*Proof.* For $d \in \{2,3,5\}$,

$$\Big\lfloor \frac{j}{d}\Big\rfloor + \Big\lfloor\frac{29-j}{d}\Big\rfloor
\;=\; \frac{29 - \bigl[(j \bmod d) + ((29-j)\bmod d)\bigr]}{d} .$$

The bracket is $\equiv 29 \pmod d$ and lies in $[0, 2d-2]$, so it equals either $29 \bmod d$ or
$29 \bmod d + d$. Now $29 \bmod 2 = 1$, $29 \bmod 3 = 2$, $29 \bmod 5 = 4$, and adding $d$ gives
$3, 5, 9$, each strictly larger than the corresponding upper bound $2d-2 = 2, 4, 8$. Hence the
bracket equals $29 \bmod d$ exactly, and the three sums are $\tfrac{29-1}{2} = 14$,
$\tfrac{29-2}{3} = 9$, $\tfrac{29-4}{5} = 5$. Therefore

$$\Delta_j + \Delta_{29-j} \;=\; \bigl[j + (29-j)\bigr] - (14+9+5) \;=\; 29 - 28 \;=\; 1.
\ \blacksquare$$

**Verification status.** Dual review (no objection); computational (all $30$ instances). Not
formalised: the Lean development takes the route through Lemma 3.1 and never needs the reflection
identity.

> **Remark.** Lemma 2.3 is special to this sequence. For a general height-one ratio (1.1) a direct
> computation gives $\Delta^u(x) + \Delta^u(-x) = T - S$ for every $x$ that makes none of $A_s x$,
> $B_t x$ an integer; for $a(n)$ we have $T - S = 3 - 2 = 1$, which is exactly Lemma 2.3. This is
> the point at which the generalisation of Section 6 needs care, and it is why Conjecture 6.2 there
> is stated as a conjecture.

### 2.2 Legendre's formula

**Lemma 2.4.** For every prime $p$ and every $n \ge 0$,

$$\nu_p\bigl(a(n)\bigr) \;=\; \sum_{k \ge 1} \Delta\!\left(\frac{n}{p^k}\right)
\;=\; \#\bigl\{\, k \ge 1 : \Delta(n/p^k) = 1 \,\bigr\} .
\tag{2.2}$$

*Proof.* Legendre's formula $\nu_p(N!) = \sum_{k \ge 1}\lfloor N/p^k\rfloor$, applied to each of the
five factorials in (1.2) and combined term by term at each $k$, gives the first equality; the sums
are finite since all terms with $p^k > 30n$ vanish. The second equality is Lemma 2.2. $\blacksquare$

**Verification status.** Dual review (both reviewers re-derived (2.2) from scratch and confirmed
period one from the coefficient balance); Lean (`legendre` and `padicValNat_a`, which also re-derive
the integrality $a(n) \in \mathbb{Z}$ rather than assuming it); computational (cross-checked against
`sympy.factorint` for $n \le 6$, prime by prime).

Identity (2.2) is the entire engine of this paper: the right-hand side is a *count of layers*, and
every layer can be spent at most once. All three lemmas of Section 3 exist to arrange a matching
between the layers of $P_r(n)$ and the layers counted on the right of (2.2).

---

## 3. Three lemmas and the main theorem

### 3.1 Step 1: unit-class rigidity

**Lemma 3.1 (Lemma A).** If $1 \le c \le 29$ and $\gcd(c,30) = 1$, then $\Delta_c = 1$.

*Proof.* Write $\bar c_3 = c \bmod 3 \in \{1,2\}$ and $\bar c_5 = c \bmod 5 \in \{1,2,3,4\}$; since
$c$ is odd, $\lfloor c/2\rfloor = (c-1)/2$. Multiplying (2.1) by $30$,

$$30\,\Delta_c \;=\; 30c - 15(c-1) - 10(c - \bar c_3) - 6(c - \bar c_5)
\;=\; 15 + 10\bar c_3 + 6\bar c_5 - c .$$

The right-hand side is divisible by $30$. Indeed it is even, because $15$ is odd, $10\bar c_3$ and
$6\bar c_5$ are even and $c$ is odd; it is $\equiv \bar c_3 - c \equiv 0 \pmod 3$; and it is
$\equiv \bar c_5 - c \equiv 0 \pmod 5$. Moreover it lies in

$$[\,15 + 10 + 6 - 29,\ 15 + 20 + 24 - 1\,] \;=\; [2,\,58],$$

and the only multiple of $30$ in that interval is $30$ itself. Hence $30\Delta_c = 30$, i.e.
$\Delta_c = 1$. $\blacksquare$

**Verification status.** Dual review (both reviewers verified the identity, the three congruences and
the interval bound, and both additionally evaluated (2.1) at all eight residues independently of the
argument); Lean (`unit_step`); computational.

> **Remark.** Lemma 3.1 is the fact on which the AlphaProof/Nexus proof of the case $r=1$ turns: its
> Lean file establishes `f_nat_eq_one` from `c_mod_30`, i.e. that
> $c \bmod 30 \in \{1,7,11,13,17,19,23,29\}$ forces the step value $1$. The whole of the present
> paper may be read as the observation that this rigidity is not about the residue $1$ but about the
> group of units modulo $30$, together with the bookkeeping (Lemma 3.4) needed to use it once per
> prime power rather than once per index.

### 3.2 Step 2: buying a layer

**Lemma 3.2 (Lemma B).** Let $p$ be a prime with $p \nmid 30$, let $k \ge 1$, and let $i \ge 1$ with
$\gcd(i,30)=1$. If

$$p^k \mid 30n - i \qquad\text{and}\qquad p^k > i,$$

then $\Delta(n/p^k) = 1$.

*Proof.* Let $s = n \bmod p^k \in [0,p^k)$ and $t = \{n/p^k\} = s/p^k$. From
$30n \equiv i \pmod{p^k}$ we get $30s \equiv i \pmod{p^k}$, so

$$30 s \;=\; i + c\,p^k \qquad\text{for some } c \in \mathbb{Z} .$$

*Range of $c$.* From $30s - i \ge -i > -p^k$ we get $c \ge 0$; from
$30s - i \le 30(p^k-1) - i < 30p^k$ we get $c \le 29$.

*Position.* $30t = 30s/p^k = c + i/p^k$ with $0 < i/p^k < 1$, so $\lfloor 30t\rfloor = c$, i.e. $t$
lies strictly inside the $c$-th cell and $\Delta(t) = \Delta_c$.

*Coprimality.* Reducing $30s = i + c\,p^k$ modulo $30$ gives $0 \equiv i + c\,p^k$. If a prime
$q \in \{2,3,5\}$ divided $c$ then, since $q \mid 30$, it would divide $i$, contradicting
$\gcd(i,30)=1$. Hence $\gcd(c,30)=1$; in particular $c \ne 0$.

Lemma 3.1 now gives $\Delta(t) = \Delta_c = 1$. $\blacksquare$

**Verification status.** Dual review (no objection; the `codex` reviewer additionally checked that
the argument is unaffected when $30n - i < 0$, which happens for small $n$, and that the hypothesis
$p^k > i$ is used exactly where needed); Lean (`f_eq_one`, stated for an arbitrary modulus $d \ge 2$
rather than a prime power, which is all the proof uses); computational.

**Remark 3.3.** Primes dividing $30$ never occur in $P_r(n)$ at all: if $p \in \{2,3,5\}$ then
$p \mid 30n$ while $p \nmid i$, so $p \nmid 30n - i$ for every $i \in L_r$. Hence
$\nu_p(P_r(n)) = 0$ for $p \in \{2,3,5\}$, and these primes may be ignored below.

### 3.3 Step 3: prime-power stratification

Lemma 3.2 settles a single factor. The content of the conjecture is the product: distinct
$i, i' \in L_r$ share the prime $p$ precisely when $p \mid i - i'$, and can therefore contribute to
$\nu_p(P_r(n))$ simultaneously, whereas (2.2) allows each layer $k$ to contribute at most $1$ to
$\nu_p(a(n))$. The following lemma confines the sharing to the finitely many layers $p^k \le r$.

**Lemma 3.4 (Lemma C).** Fix a prime $p \nmid 30$, an integer $r \ge 1$ and $n \ge 0$. Put

$$N_k \;=\; \#\{\, i \in L_r : p^k \mid 30n - i \,\},
\qquad
K \;=\; \min\{\, k \ge 1 : p^k > r \,\} .$$

Then:

1. $(N_k)_{k \ge 1}$ is nonincreasing and $\sum_{k \ge 1} N_k = \nu_p\bigl(P_r(n)\bigr)$;
2. $N_k \le 1$ for every $k \ge K$, and all layers $k \ge K$ with $N_k = 1$ share one and the same
   witness $i_0 \in L_r$;
3. $\displaystyle \sum_{k \ge K} N_k \;\le\; \nu_p\bigl(a(n)\bigr)$.

*Proof.* (1) If $p^{k+1} \mid m$ then $p^k \mid m$, so the counted sets decrease with $k$ and
$(N_k)$ is nonincreasing. No factor vanishes: $30n - i = 0$ would force $30 \mid i$, contradicting
$\gcd(i,30)=1$. Hence each $\nu_p(30n-i)$ is a well-defined nonnegative integer, and counting each
factor of valuation $e$ once on each of the layers $1,\dots,e$ gives

$$\nu_p\bigl(P_r(n)\bigr) \;=\; \sum_{i \in L_r} \nu_p(30n - i)
\;=\; \sum_{i \in L_r} \#\{k \ge 1 : p^k \mid 30n - i\} \;=\; \sum_{k \ge 1} N_k .$$

(2) Let $k \ge K$ and suppose $p^k \mid 30n - i$ and $p^k \mid 30n - i'$ with $i,i' \in L_r$.
Subtracting, $p^k \mid i - i'$. But $|i - i'| \le r - 1 < r < p^K \le p^k$, so $i = i'$. Thus
$N_k \le 1$. Moreover if $N_{k+1} = 1$ with witness $i^{(k+1)}$, then a fortiori
$p^k \mid 30n - i^{(k+1)}$, so by the uniqueness just proved at layer $k$ we get
$i^{(k+1)} = i^{(k)}$. Hence the nonempty layers above $K$ all carry the same witness $i_0$.

(3) By (1) and (2) the set $\{k \ge K : N_k = 1\}$ is an interval $[K,M]$, possibly empty (in which
case the sum is $0$ and there is nothing to prove). For each $k \in [K,M]$ we have
$p^k \mid 30n - i_0$ and $p^k \ge p^K > r \ge i_0$, so Lemma 3.2 applies and gives
$\Delta(n/p^k) = 1$. These indices $k$ are pairwise distinct, so by (2.2) and Lemma 2.2,

$$\nu_p\bigl(a(n)\bigr) \;=\; \sum_{k \ge 1} \Delta(n/p^k)
\;\ge\; \sum_{k=K}^{M} \Delta(n/p^k) \;=\; M - K + 1 \;=\; \sum_{k \ge K} N_k .\ \blacksquare$$

**Verification status.** Dual review (NO CRITICAL ERROR from both; the `codex` reviewer explicitly
confirmed the delicate point — that counting one prime at several powers on several layers is
neither a loss nor a double charge — and checked the edge cases $n = 0$, $i = r$, $30n-i<0$, and
repeated powers of a single prime); Lean (`per_k_bound`, in a uniform form that merges (2) and (3)
with the low-layer bound; see Section 8); computational.

> **Remark.** Part (3) is where the conjecture is actually won, and it is lossless: every high layer
> of $P_r(n)$ is paid for by a *distinct* summand of (2.2) that equals $1$. In particular, if
> $p > r$ then $K = 1$ and the whole of $\nu_p(P_r(n))$ is paid for, with no constant needed at all.
> This is why $D(r)$ involves only primes $p \le r$, and it is the qualitative statement that the
> numerical check of Section 3.6 probes hardest: over $r \in \{1,7,\dots,100\}$ and $n \le 120$, no
> prime $p > r$ was ever found with positive deficiency.

### 3.4 The main theorem

**Theorem 3.5 (Bala's $D(r)$ conjecture, with an explicit constant).** For $r \ge 1$ define

$$E(p,r) \;=\; \sum_{k \ge 1,\ p^k \le r}\ \max_{c \bmod p^k}\
  \#\{\, i \in L_r : i \equiv c \ (\mathrm{mod}\ p^k)\,\},
\qquad
D(r) \;=\; \prod_{\substack{p \le r\\ \gcd(p,30)=1}} p^{\,E(p,r)} .$$

Then for every $n \ge 0$,

$$P_r(n) \ \Big|\ D(r)\cdot a(n) \qquad \text{in } \mathbb{Z} .$$

*Proof.* Both sides are nonzero integers (no factor $30n-i$ vanishes, by Lemma 3.4(1)), and
divisibility in $\mathbb{Z}$ is insensitive to signs; so it suffices to prove, for every prime $p$,
the valuation inequality

$$\nu_p\bigl(P_r(n)\bigr) \;\le\; E(p,r) + \nu_p\bigl(a(n)\bigr),
\tag{3.1}$$

where by convention $E(p,r) = 0$ when $p \mid 30$ or $p > r$. There are three cases.

*Case $p \in \{2,3,5\}$.* By Remark 3.3, $\nu_p(P_r(n)) = 0$ and (3.1) is trivial.

*Case $p \nmid 30$, $p > r$.* Then $p^1 > r$, so $K = 1$ and Lemma 3.4(1),(3) give

$$\nu_p\bigl(P_r(n)\bigr) \;=\; \sum_{k \ge 1} N_k \;=\; \sum_{k \ge K} N_k
\;\le\; \nu_p\bigl(a(n)\bigr),$$

which is (3.1) with no loss whatsoever.

*Case $p \nmid 30$, $p \le r$.* Split the sum of Lemma 3.4(1) at $K$:

$$\nu_p\bigl(P_r(n)\bigr)
\;=\; \underbrace{\sum_{k=1}^{K-1} N_k}_{\text{low layers}}
\;+\; \underbrace{\sum_{k \ge K} N_k}_{\le\ \nu_p(a(n)) \text{ by Lemma 3.4(3)}} .$$

Every low layer satisfies $p^k \le r$ by the minimality of $K$. Moreover $p^k \mid 30n - i$ says
exactly that $i$ lies in the residue class of $30n$ modulo $p^k$, so

$$N_k \;=\; \#\{\, i \in L_r : i \equiv 30n \ (\mathrm{mod}\ p^k)\,\}
\;\le\; \max_{c \bmod p^k} \#\{\, i \in L_r : i \equiv c \ (\mathrm{mod}\ p^k)\,\} ,$$

and this bound does not depend on $n$. Summing over $k = 1,\dots,K-1$, whose $p^k$ are exactly the
prime powers of $p$ that are $\le r$, gives $\sum_{k<K} N_k \le E(p,r)$, hence (3.1).

The three cases exhaust all primes and the bounds are uniform in $n$, so
$P_r(n) \mid D(r)\,a(n)$ for every $n \ge 0$. $\blacksquare$

**Verification status.** Dual review: VALID from both reviewers, each recomputing the valuation
inequality prime by prime and confirming the case split. Lean: the *existence* statement is
machine-checked in the strengthened form $\exists D > 0$ (`general_divisibility_strong`), but with
the cruder witness $(r!)^{r^2}$ rather than the $D(r)$ above; the sharp constant is *not* formalised
(Section 8). Computational: end-to-end for $r \in \{1,7,11,13,17,19,23,29,31,37,49\}$ and
$0 \le n \le 60$, plus a per-prime deficiency check for $r$ up to $100$ and $n \le 400$, plus an
independently written check by the `codex` reviewer through a disjoint code path.

**Remark 3.6 (the case $n = 0$).** Because $P_r(n)$ is defined in $\mathbb{Z}$ and its factors are
negative for small $n$, the boundary case deserves an explicit word. At $n=0$ we have
$P_r(0) = \prod_{i \in L_r}(-i)$ and $a(0)=1$, so $\nu_p(a(0)) = 0$ for all $p$; correspondingly
$N_k = \#\{i \in L_r : p^k \mid i\}$, which is $0$ for $p^k > r$ since no $i \le r$ is divisible by
$p^k$. Thus the high-layer sum is $0 = \nu_p(a(0))$ and the low layers are bounded by $E(p,r)$ as
before: the proof above covers $n=0$ with no modification. Negative factors are likewise harmless,
since divisibility and $p$-adic valuation depend only on absolute values, and no factor is zero.

### 3.5 The size of $D(r)$

**Corollary 3.7 (closed-form bound).**
$\displaystyle E(p,r) \;\le\; \sum_{k \ge 1,\ p^k \le r} \Bigl\lceil \frac{r}{p^k}\Bigr\rceil
\;\le\; \frac{r}{p-1} + \log_p r$.

*Proof.* A fixed residue class modulo $p^k$ meets $\{1,\dots,r\}$ in at most $\lceil r/p^k\rceil$
elements, and $L_r \subseteq \{1,\dots,r\}$. Then
$\sum_{k \ge 1, p^k \le r}\lceil r/p^k\rceil \le \sum_{k\ge1} r p^{-k} + \#\{k : p^k \le r\}
= r/(p-1) + \lfloor \log_p r\rfloor$. $\blacksquare$

**Verification status.** Dual review (no objection); computational.

**Corollary 3.8 (growth order).** $\log D(r) = \Theta(r \log r)$. More precisely,
$\bigl(\tfrac{1}{30}+o(1)\bigr)\, r\log r \le \log D(r) \le \bigl(1+o(1)\bigr)\, r \log r$.

*Proof.* *Upper bound.* By Corollary 3.7,

$$\log D(r) \;=\; \sum_{\substack{p \le r\\ \gcd(p,30)=1}} E(p,r)\log p
\;\le\; \sum_{p \le r}\Bigl(\frac{r}{p-1} + \frac{\log r}{\log p}\Bigr)\log p
\;=\; r\sum_{p\le r}\frac{\log p}{p-1} \;+\; \pi(r)\log r .$$

Mertens' first theorem gives $\sum_{p \le r}\log p/(p-1) = \log r + O(1)$, and Chebyshev's bound
gives $\pi(r)\log r = O(r)$. Hence $\log D(r) \le (1+o(1))\,r\log r$.

*Lower bound.* Let $p$ be a prime with $\gcd(p,30)=1$. Every term of the arithmetic progression
$1, 1+30p, 1+60p, \dots$ is $\equiv 1 \pmod{30}$, hence coprime to $30$; so all such terms not
exceeding $r$ belong to $L_r$, and they are all congruent to $1$ modulo $p$. The single layer $k=1$
of $E(p,r)$ therefore already contributes

$$E(p,r) \;\ge\; \Bigl\lfloor \frac{r-1}{30p}\Bigr\rfloor + 1 .$$

Summing $E(p,r)\log p$ over the primes $p \le (r-1)/30$ coprime to $30$ and using Mertens' estimate
$\sum_{p \le x}\log p / p = \log x + O(1)$,

$$\log D(r) \;\ge\; \sum_{\substack{p \le (r-1)/30\\ \gcd(p,30)=1}}
  \Bigl\lfloor\frac{r-1}{30p}\Bigr\rfloor \log p
\;\ge\; \Bigl(\frac{1}{30}+o(1)\Bigr)\, r\log r .\ \blacksquare$$

**Verification status.** The lower bound is due to the `codex` reviewer, who produced it in order to
refute the claim $\log D(r) = O(r\log\log r)$ asserted in the first draft of this paper; that claim
is false and has been removed. The *upper* bound was re-derived in round 2 (Qwen, targeted): OK,
with the Mertens and Chebyshev steps checked separately. The lower bound, being the first reviewer's
own construction, has not been independently re-reviewed. Computational: the inequality
$E(p,r) \ge \lfloor (r-1)/(30p)\rfloor + 1$ was checked for all primes and all $r \le 3200$ with no
violation, and numerically $\log D(r)/(r\log r)$ stays near $0.30$ over $r = 100,\dots,3200$ while
$\log D(r)/(r\log\log r)$ increases monotonically from $0.83$ to $1.17$ (Table A.2), which is what
refutes the discarded claim.

> **Remark.** Corollary 3.8 describes *our* $D(r)$, not the minimal one. The growth order of the
> minimal valid constant is unknown to us; see Section 10, item 1.

**Corollary 3.9 (the case $r \le 6$, recovering the AlphaProof/Nexus theorem).** For $1 \le r \le 6$
we have $L_r = \{1\}$ and $D(r) = 1$; in particular $(30n-1) \mid a(n)$ for all $n \ge 0$.

*Proof.* For $r \le 6$ the only $i \le r$ coprime to $30$ is $i=1$, and there is no prime $p \le r$
with $\gcd(p,30)=1$, so the product defining $D(r)$ is empty. Theorem 3.5 then reads
$(30n-1) \mid a(n)$. $\blacksquare$

**Verification status.** Dual review (no objection); Lean (`thirty_mul_sub_one_dvd_a`, derived from
the general machinery, which reproves the AlphaProof/Nexus result from scratch); computational.
Consistent with Bala's $D(1)=1$.

### 3.6 Explicit values, and how the table must be read

Since $D(r)$ depends on $r$ only through $L_r$ and the prime powers $\le r$, it is constant on long
stretches of $r$. Table 2 lists it up to $r = 43$, grouping equal values; Table A.1 in Appendix A
adds the exponent vectors $E(p,r)$.

**Table 2.** The constant of Theorem 3.5. In the last two rows $19\cdots41$ and $19\cdots43$
abbreviate the product of the first powers of the primes from $19$ up to $41$ respectively $43$ that
are coprime to $30$.

| $r$ | $L_r$ | $D(r)$ | factorisation |
|---|---|---|---|
| $1$–$6$ | $\{1\}$ | $1$ | — |
| $7$–$10$ | $\{1,7\}$ | $7$ | $7$ |
| $11$–$12$ | $\{1,7,11\}$ | $77$ | $7\cdot 11$ |
| $13$–$16$ | $\{1,7,11,13\}$ | $1001$ | $7\cdot 11\cdot 13$ |
| $17$–$18$ | $\{1,7,11,13,17\}$ | $17017$ | $7\cdot 11\cdot 13\cdot 17$ |
| $19$–$22$ | $\{1,7,11,13,17,19\}$ | $323323$ | $7\cdot 11\cdot 13\cdot 17\cdot 19$ |
| $23$–$28$ | $\{1,7,11,13,17,19,23\}$ | $81800719$ | $7\cdot 11^{2}\cdot 13\cdot 17\cdot 19\cdot 23$ |
| $29$–$30$ | $\{1,7,\dots,29\}$ | $16605545957$ | $7^{2}\cdot 11^{2}\cdot 13\cdot 17\cdot 19\cdot 23\cdot 29$ |
| $31$–$36$ | $\{1,7,\dots,31\}$ | $514771924667$ | $7^{2}\cdot 11^{2}\cdot 13\cdot 17\cdot 19\cdot 23\cdot 29\cdot 31$ |
| $37$–$40$ | $\{1,7,\dots,37\}$ | $247605295764827$ | $7^{2}\cdot 11^{2}\cdot 13^{2}\cdot 17\cdot 19\cdot 23\cdot 29\cdot 31\cdot 37$ |
| $41$–$42$ | $\{1,7,\dots,41\}$ | $172580891148084419$ | $7^{2}\cdot 11^{2}\cdot 13^{2}\cdot 17^{2}\cdot 19\cdots 41$ |
| $43$–$46$ | $\{1,7,\dots,43\}$ | $51946848235573410119$ | $7^{3}\cdot 11^{2}\cdot 13^{2}\cdot 17^{2}\cdot 19\cdots 43$ |

> **Remark (how to read Table 2).** The first six rows look like "multiply by the next prime", and
> that reading is wrong. It breaks at $r = 23$: $D(23)$ is *not* $323323\cdot 23 = 7436429$ but
> $81800719 = 7436429 \times 11$. The reason is that $E(p,r)$ counts the largest number of elements
> of $L_r$ inside one residue class modulo $p^k$, not the mere presence of a prime $\le r$.
> Concretely,
>
> - $E(11,\cdot)$ jumps from $1$ to $2$ at $r=23$, because $1 \equiv 23 \pmod{11}$ and $r=23$ is the
>   first $r$ for which both lie in $L_r$;
> - $E(7,\cdot)$ jumps from $1$ to $2$ at $r=29$, because $1 \equiv 29 \pmod 7$;
> - $E(13,\cdot)$ jumps from $1$ to $2$ at $r=37$, because $11 \equiv 37 \pmod{13}$;
> - $E(17,\cdot)$ jumps at $r=41$ ($7 \equiv 41 \pmod{17}$), and $E(7,\cdot)$ jumps again to $3$ at
>   $r=43$ ($1 \equiv 29 \equiv 43 \pmod 7$).
>
> An earlier draft of this table used abbreviations of the form "$+23$" and "$\cdots\cdot 19$" which
> hid these jumps; one reviewer read the row for $r=23$ as an arithmetic error on that account. The
> values were correct throughout, but the presentation was not, and the table is displayed in full
> here for that reason.

**Verification status.** The four jump attributions above were re-derived in round 2 (Qwen,
targeted): OK. The reviewer checked in each case that the residues of $L_r$ are pairwise distinct
modulo $p$ just below the stated $r$ and that the newly admitted index collides with an existing
one, and confirmed the resulting decimal values and factorisations against the table.

**Is $D(r)$ minimal?** No, and the gap begins exactly where the sharing begins. Let $D_{\min}(r)$ be
the least positive constant that works. A valid constant must be divisible by

$$|P_r(n)| \big/ \gcd\bigl(|P_r(n)|,\,a(n)\bigr)$$

for every $n$, so the least common multiple of those quantities over $n \le 200$ is a lower bound
for $D_{\min}(r)$ and divides it. Comparing:

**Table 3.** Theorem 3.5 is sharp for $r \le 19$ and loses a little afterwards. "Slack" is the ratio
of the two preceding columns, an upper bound for $D(r)/D_{\min}(r)$.

| $r$ | $D(r)$ of Theorem 3.5 | lower bound for $D_{\min}(r)$ ($n \le 200$) | slack |
|---|---|---|---|
| $\le 19$ | $D(r)$ and the lower bound agree | (same value) | $1$ |
| $23$ | $81800719$ | $7436429$ | $11$ |
| $29$ | $16605545957$ | $215656441$ | $7\cdot 11$ |
| $31$ | $514771924667$ | $46797447697$ | $11$ |
| $37$ | $247605295764827$ | $1731505564789$ | $11\cdot 13$ |
| $49$ | $7468554211373095893038987$ | $13056159716962300939$ | $7\cdot11\cdot17\cdot19\cdot23$ |

The source of the slack is identified in Section 10, item 1: the low-layer bound
$N_k \le \max_c \#\{\cdots\}$ silently assumes that the worst residue class and a total absence of
low-layer contributions to $\nu_p(a(n))$ can occur simultaneously, and they are in fact correlated.

---

## 4. The sister family $C(k,r)$

Bala's explicit statements about $2n+1$, $3n+1$ and $5n+1$ are the case $r=1$ of a family running
parallel to the $D(r)$ conjecture. (His fourth statement, about the mixed product
$(2n+1)(3n+1)(5n+1)$, is of a different shape and is *not* an instance of what follows; see
Remark 4.5.) Throughout this section

$$k \in \{2,3,5\}, \qquad m = 30/k \in \{15,10,6\}, \qquad
L^{(k)}_r = \{\, i : 1 \le i \le r,\ \gcd(i,k)=1 \,\},$$

$$Q^{(k)}_r(n) = \prod_{i \in L^{(k)}_r}(kn+i).$$

Note that every factor $kn+i \ge i \ge 1$ is positive, so no sign discussion is needed here.

The proof runs through the same three steps, but three details genuinely differ from Section 3 and
we spell them out rather than assert a parallel: the threshold is $p^j \ge m\,i$ rather than
$p^j > i$; the prime $p$ is allowed to divide $m$ — for instance $p = 3$ or $5$ when $k = 2$ — so
that, unlike in Section 3, the divisors of $30$ are not all excluded, only those dividing $k$; and
the index set is $L^{(k)}_r$, defined by coprimality to $k$ rather than to $30$.

### 4.1 The local lemma for $kn+i$

**Lemma 4.1 (Lemma B′).** Let $k \in \{2,3,5\}$, $m = 30/k$, let $p$ be a prime with $p \nmid k$,
let $j \ge 1$, and let $i \ge 1$ with $\gcd(i,k)=1$. If

$$p^j \mid kn + i \qquad\text{and}\qquad p^j \ge m\,i,$$

then $\Delta(n/p^j) = 1$.

*Proof.* Put $s = n \bmod p^j$ and $t = \{n/p^j\} = s/p^j$. From $p^j \mid kn+i$ we get
$p^j \mid ks+i$, say

$$k s + i \;=\; c\,p^j, \qquad c \in \mathbb{Z} .$$

*Range of $c$.* Since $c\,p^j = ks + i \ge i > 0$ we have $c \ge 1$. For the upper bound,
$m \ge 6 > 1$ and $p^j \ge mi$ give $i \le p^j/m < p^j$, whence

$$c\,p^j \;=\; ks + i \;\le\; k(p^j - 1) + i \;<\; k\,p^j + p^j \;=\; (k+1)p^j ,$$

so $c \le k$. If $c = k$ then $ks+i = k p^j$, so $k \mid i$, contradicting $\gcd(i,k)=1$. Hence
$1 \le c \le k-1$; in particular $k \ge 2$ guarantees such a $c$ exists.

*Position.* Using $30/k = m$,

$$30t \;=\; \frac{30 s}{p^j} \;=\; \frac{30(c\,p^j - i)}{k\,p^j} \;=\; mc - \frac{mi}{p^j},
\qquad 0 < \frac{mi}{p^j} \le 1 ,$$

so $\lfloor 30t\rfloor = mc-1$ (this is correct also in the boundary case $mi = p^j$, where
$30t = mc-1$ exactly), and therefore $\Delta(n/p^j) = \Delta_{mc-1}$.

*Value.* By Lemma 2.3 and $mk = 30$,

$$\Delta_{mc-1} \;=\; 1 - \Delta_{29-(mc-1)} \;=\; 1 - \Delta_{30-mc} \;=\; 1 - \Delta_{m(k-c)},$$

with $k - c \in \{1,\dots,k-1\}$. The seven values $\Delta_{mc'}$ with $c' \in \{1,\dots,k-1\}$ are
read off Table 1:

- $k=2$, $m=15$: $\Delta_{15}=0 \Longrightarrow \Delta_{14}=1$;
- $k=3$, $m=10$: $\Delta_{10}=\Delta_{20}=0 \Longrightarrow \Delta_{9}=\Delta_{19}=1$;
- $k=5$, $m=6$: $\Delta_{6}=\Delta_{12}=\Delta_{18}=\Delta_{24}=0 \Longrightarrow
  \Delta_{5}=\Delta_{11}=\Delta_{17}=\Delta_{23}=1$.

Hence $\Delta(n/p^j) = \Delta_{mc-1} = 1$. $\blacksquare$

**Verification status.** Dual review: the `codex` reviewer re-derived this lemma, listed the same
seven cells, confirmed that equality at the threshold is harmless, and confirmed that primes
dividing $m$ need not be excluded. One editorial correction from that review is incorporated: the
first draft bounded $ks+i \le k p^j - k + i$, which does not give $c \le k$ when $i > k$; the
argument above uses $i < p^j$ explicitly. Not formalised. Computational (all seven cells; the family
end-to-end, see Theorem 4.3).

### 4.2 Stratification for $kn+i$

**Lemma 4.2 (Lemma C′).** Let $k \in \{2,3,5\}$, $m = 30/k$, let $p$ be a prime with $p \nmid k$,
and let $r \ge 1$, $n \ge 0$. Put

$$N^{(k)}_j = \#\{\, i \in L^{(k)}_r : p^j \mid kn+i \,\},
\qquad
K = \min\{\, j \ge 1 : p^j > m r \,\} .$$

Then $(N^{(k)}_j)_j$ is nonincreasing with
$\sum_{j \ge 1} N^{(k)}_j = \nu_p\bigl(Q^{(k)}_r(n)\bigr)$; for $j \ge K$ one has
$N^{(k)}_j \le 1$ with a single witness $i_0$ shared by all such layers; and
$\sum_{j \ge K} N^{(k)}_j \le \nu_p\bigl(a(n)\bigr)$.

*Proof.* The first assertion is as in Lemma 3.4(1), and is easier here because every factor $kn+i$
is positive.

For the second, let $j \ge K$ and suppose $p^j$ divides both $kn+i$ and $kn+i'$ with
$i,i' \in L^{(k)}_r$. Then $p^j \mid i-i'$ while

$$|i - i'| \;\le\; r-1 \;<\; r \;\le\; m r \;<\; p^K \;\le\; p^j$$

(using $m \ge 1$), so $i = i'$ and $N^{(k)}_j \le 1$. If $N^{(k)}_{j+1} = 1$ with witness
$i^{(j+1)}$ then $p^j \mid kn + i^{(j+1)}$ as well, so uniqueness at layer $j$ forces
$i^{(j+1)} = i^{(j)}$; hence all nonempty layers $j \ge K$ share one witness $i_0$.

For the third, $\{j \ge K : N^{(k)}_j = 1\}$ is an interval $[K,M]$ (possibly empty). For each $j$ in
it, $p^j \mid kn + i_0$ and

$$p^j \;\ge\; p^K \;>\; m r \;\ge\; m\,i_0 ,$$

which is exactly the threshold hypothesis of Lemma 4.1; so $\Delta(n/p^j) = 1$ for each of these
$M-K+1$ distinct layers, and (2.2) together with Lemma 2.2 gives
$\nu_p(a(n)) \ge M-K+1 = \sum_{j\ge K} N^{(k)}_j$. $\blacksquare$

**Verification status.** Reviewed in round 2 (Qwen, targeted): OK. The reviewer checked each of the
three differences separately — that $p^j \ge p^K > mr \ge m\,i_0$ makes the threshold automatic for
any witness $i_0 \le r$; that the local argument uses only $p \nmid k$, so the finite cell checks
survive when $p \mid m$; and that high-layer uniqueness depends only on $|i-i'| \le r-1$ and is
therefore indifferent to which index set is used. This lemma is the explicit form of a step that the
first two drafts left as "verbatim parallel to Lemma 3.4", which the Qwen first pass objected to,
correctly. The underlying mathematics was independently confirmed by the `codex` review, which
carried out the same reduction. Not formalised. Computational (through Theorem 4.3).

### 4.3 The theorem

**Theorem 4.3 (Bala's $C(k,r)$ family).** Let $k \in \{2,3,5\}$, $m = 30/k$. Define

$$E_k(p,r) = \sum_{j \ge 1,\ p^j \le mr}\ \max_{c \bmod p^j}\
  \#\{\, i \in L^{(k)}_r : i \equiv c \ (\mathrm{mod}\ p^j)\,\},
\qquad
C(k,r) = \prod_{\substack{p \le mr\\ p \nmid k}} p^{\,E_k(p,r)} .$$

Then $Q^{(k)}_r(n) \mid C(k,r)\cdot a(n)$ for every $n \ge 0$.

*Proof.* Fix a prime $p$; we prove $\nu_p(Q^{(k)}_r(n)) \le E_k(p,r) + \nu_p(a(n))$.

If $p \mid k$ then $p \nmid kn+i$ for every $i \in L^{(k)}_r$, since $p \mid kn$ and $p \nmid i$; so
$\nu_p(Q^{(k)}_r(n)) = 0$ and there is nothing to prove. Assume $p \nmid k$ and split at
$K = \min\{j : p^j > mr\}$ using Lemma 4.2:

$$\nu_p\bigl(Q^{(k)}_r(n)\bigr)
= \underbrace{\sum_{j=1}^{K-1} N^{(k)}_j}_{\text{low}}
+ \underbrace{\sum_{j \ge K} N^{(k)}_j}_{\le\ \nu_p(a(n))} .$$

Each low layer has $p^j \le mr$, and $p^j \mid kn+i$ says $i \equiv -kn \pmod{p^j}$, so
$N^{(k)}_j \le \max_c \#\{ i \in L^{(k)}_r : i \equiv c \ (\mathrm{mod}\ p^j)\}$, a bound independent
of $n$. Summing over $j < K$ gives $E_k(p,r)$. Finally, if $p > mr$ then $K=1$ and the low sum is
empty, so only primes $p \le mr$ occur in $C(k,r)$, as in its definition. $\blacksquare$

**Verification status.** Dual review: VALID from the `codex` reviewer, who verified the seven cells,
the threshold, and the fact that primes dividing $m$ are legitimately admitted; the Qwen first pass
recorded the exposition gap now closed by Lemma 4.2, and Qwen round 2 returned OK on the completed
proof, confirming both the low/high split and the fact that primes $p > mr$ need no factor in
$C(k,r)$. Not formalised. Computational: end-to-end for $k \in \{2,3,5\}$,
$r \in \{1,2,3,5,8,12\}$ and $0 \le n \le 40$, and (independently of this theorem) all five of
Bala's explicit assertions for $n < 400$; the `codex` reviewer additionally re-verified the case
$k=3$, $r=5$, $C = 459117704332740252800$ through an independent code path.

**Specialisation to $r=1$, stated exactly.** Taking $r=1$ in Theorem 4.3 gives

$$(2n+1) \mid C(2,1)\,a(n), \qquad (3n+1)\mid C(3,1)\,a(n), \qquad (5n+1)\mid C(5,1)\,a(n),$$

that is, the qualitative form of *three* of Bala's explicit statements, with constants coarser than
his (Remark 4.4). It does *not* give his fourth, $(2n+1)(3n+1)(5n+1) \mid 42\,a(n)$: that statement
mixes three different moduli and lies outside the scope of this theorem, for the reason set out in
Remark 4.5. We say this explicitly because the phrase "a uniform proof for general $r$" invites the
opposite reading.

**Remark 4.4 (the constant here is far from sharp).** Theorem 4.3 gives
$C(2,1) = 45045 = 3^2\cdot 5\cdot 7\cdot 11\cdot 13$ where Bala's constant is $7$, and
$C(3,1) = 280$, $C(5,1) = 12$ where the true constants are $1$ (Table A.3 in Appendix A gives more
values). The reason is visible in the proof: the high-layer threshold was taken uniformly as
$p^j > mr$, whereas Lemma 4.1 only requires $p^j \ge m\,i$ for the individual witness $i$. Replacing
$E_k$ by an $n$-uniform bound on
$\sum_j \#\{ i \in L^{(k)}_r : i \equiv -kn \ (\mathrm{mod}\ p^j),\ p^j < mi\}$ would tighten it; we
have not done this. The corresponding threshold in Theorem 3.5 is $p^k > i$ with $i \le r$, which is
why $D(r)$ does not suffer the same loss.

### 4.4 The mixed product: what we do and do not prove

**Remark 4.5 (the mixed product is not covered).** Bala's fourth explicit statement,
$(2n+1)(3n+1)(5n+1) \mid 42\,a(n)$, does not follow from Theorem 4.3. Applying the theorem to
$k=2,3,5$ separately gives three inequalities $\nu_p(kn+1) \le E_k(p,1) + \nu_p(a(n))$ whose sum
charges $\nu_p(a(n))$ three times, whereas the mixed statement must be paid for with a single copy
of it. Nor are the three factors pairwise coprime, so the three divisibilities cannot simply be
multiplied: at $n=1$ they are $3$, $4$, $6$, and $\gcd(3,6) = 3$. An earlier version of this work
listed the mixed product among the $r=1$ instances of Theorem 4.3; that was an overclaim and is
withdrawn. Its present status here is: *numerically verified for $n < 400$, not covered by our
theorems*, together with the conditional derivation of Proposition 4.6 below. The statement itself
is in any case already proved and formalised by others (Section 9).

**Verification status.** The non-coverage judgement was reviewed in round 2 (Qwen, targeted): OK.
The reviewer confirmed both grounds — the threefold charge against $\nu_p(a(n))$, and genuine
sharing at $p=2,3$ (at $n=1$: $\gcd(2n+1,5n+1)=3$ and $\gcd(3n+1,5n+1)=2$) — and this remark
implements that round's single editorial request. Computational ($n<400$).

There is, however, a clean route to the mixed product, and it is worth recording because it shows
exactly what our machinery is missing. It does not use our constants at all; it uses the *sharp*
$r=1$ constants, which are not our result.

**Proposition 4.6 (conditional).** Assume the three sharp divisibilities

$$(2n+1) \mid 7\,a(n), \qquad (3n+1) \mid a(n), \qquad (5n+1)\mid a(n) \qquad (n \ge 0).$$

Then $(2n+1)(3n+1)(5n+1) \mid 42\,a(n)$ for every $n \ge 0$.

*Proof.* Write $x = 2n+1$, $y = 3n+1$, $z = 5n+1$. Integer elimination gives

$$3x - 2y = 1, \qquad 5x - 2z = 3, \qquad 5y - 3z = 2,$$

so $\gcd(x,y) = 1$, $\gcd(x,z) \mid 3$ and $\gcd(y,z)\mid 2$: only $p = 2$ and $p=3$ can be shared
by two factors. Note also that $x$ is odd and $y \equiv 1 \pmod 3$. We check
$\nu_p(xyz) \le \nu_p(42) + \nu_p(a(n))$ for every prime $p$.

*$p \ge 5$, $p \ne 7$.* At most one of $x,y,z$ is divisible by $p$, so $\nu_p(xyz)$ is that factor's
valuation, which is $\le \nu_p(a(n))$ by hypothesis (for $x$, because $\nu_p(7)=0$). And
$\nu_p(42) = 0$.

*$p = 7$.* Again at most one factor is divisible by $7$. The hypotheses give
$\nu_7(x) \le 1 + \nu_7(a(n))$ and $\nu_7(y), \nu_7(z) \le \nu_7(a(n))$, so
$\nu_7(xyz) \le 1 + \nu_7(a(n)) = \nu_7(42) + \nu_7(a(n))$.

*$p = 3$.* Here $3 \nmid y$, and $3 \mid x \iff n \equiv 1 \pmod 3 \iff 3 \mid z$: either both or
neither. If neither, $\nu_3(xyz) = 0$. If both, then
$\min(\nu_3(x),\nu_3(z)) = \nu_3(\gcd(x,z)) \le \nu_3(3) = 1$ while both are $\ge 1$, so the minimum
is exactly $1$ and

$$\nu_3(xyz) = \nu_3(x)+\nu_3(z) = 1 + \max(\nu_3(x),\nu_3(z)) \le 1 + \nu_3(a(n))
= \nu_3(42)+\nu_3(a(n)).$$

*$p = 2$.* Here $2 \nmid x$, and $2 \mid y \iff n \text{ odd} \iff 2 \mid z$. If $n$ is even,
$\nu_2(xyz) = 0$. If $n$ is odd, $\min(\nu_2(y),\nu_2(z)) = \nu_2(\gcd(y,z)) \le \nu_2(2) = 1$ with
both $\ge 1$, so the minimum is $1$ and
$\nu_2(xyz) = 1 + \max(\nu_2(y),\nu_2(z)) \le 1 + \nu_2(a(n)) = \nu_2(42)+\nu_2(a(n))$.
$\blacksquare$

**Verification status.** **Conditional, and the hypotheses are not ours.** The three sharp constants
assumed here are Bala's own values; they are recorded as `research solved` in the
`formal-conjectures` corpus with Lean proofs by KitaKen1, and they are strictly sharper than what
Theorem 4.3 delivers at $r=1$ ($45045$, $280$, $12$). So this proposition is not a consequence of
our theorem chain, and we do not count the mixed product among our results. Written after both
review rounds and *not* adversarially reviewed. Not formalised. Computational: the gcd structure and
the two "$\min = 1$" steps were checked for all $n < 20000$.

> **Remark.** To prove the mixed product from our own machinery one would first have to sharpen
> Theorem 4.3 to the optimal constants, which is the improvement described in Remark 4.4 — for $p=3$
> it needs the compensation argument that the first layer, where $\Delta_{10}=0$, is paid for at the
> second. We have not done this.

---

## 5. The sign is not a typographical accident

Bala writes $30n - i$ in the general conjecture but $kn + i$ in the companion statements. One may
ask whether the minus sign could be replaced by a plus. It cannot, and the reason is not that our
method fails — although it does — but that no constant exists.

We first record why the method fails, because the same computation is what suggests the
construction. For the family $30n+i$ with $\gcd(i,30)=1$, the computation carried out in the proof
of Proposition 5.1 below (case $j \le e$) places $\Delta(n/p^j)$ in cell $c-1$, where $c$ is a unit
modulo $30$; by Lemma 2.3 and Lemma 3.1, $\Delta_{c-1} = 1 - \Delta_{30-c} = 0$, since $30-c$ is
again a unit. So the relevant cells are uniformly $0$ and no layer is ever bought. This is a
statement about our mechanism only: a zero cell says the high-layer argument is unavailable, not that
the divisibility is impossible, since $\nu_p(a(n))$ might still receive contributions from other
layers. An adversarial reviewer correctly refused the impossibility claim on exactly this ground. The
following proposition supplies what is actually needed — an explicit family of $n$ on which the
$p$-adic deficit is unbounded.

**Proposition 5.1.** Let $\gcd(i,30) = 1$. There is no constant $D \ne 0$ such that
$(30n+i) \mid D\cdot a(n)$ for all $n \ge 0$.

*Proof.* By Dirichlet's theorem choose a prime $p \equiv 1 \pmod{30}$ with $p > i$; there are
infinitely many. For $e \ge 1$ set

$$n_e \;=\; \frac{i\,(p^e-1)}{30} \;\in\; \mathbb{Z}_{\ge 1},$$

an integer because $p^e \equiv 1 \pmod{30}$. Then $30 n_e + i = i\,p^e$, and $p \nmid i$ because
$p > i \ge 1$, so

$$\nu_p(30n_e + i) \;=\; e .$$

We claim $\nu_p(a(n_e)) = 0$, i.e. $\Delta(n_e/p^j) = 0$ for every $j \ge 1$.

*Case $j \le e$.* Here $p^j \mid i p^e = 30n_e + i$, so with $s = n_e \bmod p^j$ we have
$30s + i = c\,p^j$ for an integer $c$. Then $c\,p^j = 30s+i \ge i > 0$ gives $c \ge 1$, while
$i < p \le p^j$ gives $c\,p^j \le 30(p^j-1) + i < 31 p^j$ and hence $c \le 30$; and $c = 30$ would
force $30 \mid i$, so $1 \le c \le 29$. Reducing $c\,p^j = 30s + i \equiv i \pmod{30}$ and using that
$p^j$ is a unit modulo $30$, we find that $c$ is a unit modulo $30$. Also
$30\{n_e/p^j\} = 30 s/p^j = c - i/p^j$ with $0 < i/p^j < 1$, so $\lfloor 30 s/p^j\rfloor = c-1$ and
$\Delta(n_e/p^j) = \Delta_{c-1}$. Finally, $30 - c$ is a unit modulo $30$ as well, so Lemma 2.3 and
Lemma 3.1 give

$$\Delta_{c-1} \;=\; 1 - \Delta_{29-(c-1)} \;=\; 1 - \Delta_{30-c} \;=\; 1 - 1 \;=\; 0 .$$

*Case $j > e$.* From $i < p$,

$$n_e \;<\; \frac{i\,p^e}{30} \;\le\; \frac{i\,p^{\,j-1}}{30} \;<\; \frac{p^{\,j}}{30},$$

so $0 \le n_e/p^j < 1/30$: the point lies in cell $0$ and $\Delta(n_e/p^j) = \Delta_0 = 0$.

Hence $\nu_p(a(n_e)) = 0$ for every $e$. Suppose some $D$ satisfied $(30n+i) \mid D\,a(n)$ for all
$n$. Taking $n = n_e$ and comparing $p$-adic valuations,

$$e \;=\; \nu_p(30n_e+i) \;\le\; \nu_p\bigl(D\,a(n_e)\bigr)
\;=\; \nu_p(D) + \nu_p\bigl(a(n_e)\bigr) \;=\; \nu_p(D)$$

for every $e \ge 1$, which is impossible for $D \ne 0$. $\blacksquare$

**Verification status.** Reviewed in round 2 (Qwen, targeted): OK, no critical error and no
justification gap. The reviewer checked the construction $n_e = i(p^e-1)/30$, the identity
$30n_e+i = i\,p^e$, and both layer ranges — $j \le e$ (unit residue $c$, then reflection plus
Lemma 3.1) and $j > e$ (the point falls in cell $0$) — and observed that $j=e$ needs no separate
treatment, being already inside the first range. This proposition postdates the first review pass:
it was written in response to the `codex` reviewer's objection J2, and the Qwen first pass, carried
out on an earlier snapshot, records it as missing. Not formalised. Computational: the construction
was checked for $i \in \{1,7,11,13,17,19,23,29,31\}$, $p \in \{31,61,151,181,211\}$ and $e \le 3$,
giving $\nu_p(30n_e+i) = e$ and $\nu_p(a(n_e)) = 0$ in every case.

> **Remark (scope).** Proposition 5.1 covers the single family $30n+i$. We make no claim that a zero
> cell implies infeasibility in general: that converse is neither proved nor refuted here, and
> establishing it for another family would require another construction. See Section 10, item 5.

---

## 6. Towards Vasyunin's other sporadic ratios

Bala's comment ends: "Similar results may hold for all the 52 sporadic integral factorial ratio
sequences listed in A295431." Our proof isolates exactly what is needed, and the condition is a
finite check per sequence.

Let $u$ be as in (1.1) with $\sum_s A_s = \sum_t B_t$, let
$N = \operatorname{lcm}\bigl(\{A_s\}\cup\{B_t\}\bigr)$, and let

$$\Delta^u(x) \;=\; \sum_{s}\lfloor A_s x\rfloor - \sum_t \lfloor B_t x\rfloor ,
\qquad \Delta^u_j := \Delta^u(j/N) \quad (j=0,\dots,N-1).$$

As in Section 2, $\Delta^u$ has period $1$ and is constant on each cell $[j/N,(j+1)/N)$, and
$\nu_p(u(n)) = \sum_{k\ge1}\Delta^u(n/p^k)$.

**Criterion 6.1.** Suppose $\Delta^u$ takes only the values $0$ and $1$, and that

$$\Delta^u_c = 1 \qquad\text{for every } 1 \le c \le N-1 \text{ with } \gcd(c,N)=1 .$$

Then for every $r \ge 1$,

$$\prod_{\substack{i \le r\\ \gcd(i,N)=1}} (Nn-i) \ \Big|\ D_u(r)\cdot u(n)
\qquad (n \ge 0),
\qquad
D_u(r) = \prod_{\substack{p \le r\\ p \nmid N}} p^{\,E_u(p,r)},$$

with $E_u(p,r) = \sum_{k \ge 1,\ p^k \le r}\max_{c}\#\{i \le r : \gcd(i,N)=1,\ i \equiv c\
(\mathrm{mod}\ p^k)\}$.

*Proof.* Both hypotheses are exactly the inputs used in Section 3. Lemma 3.1 is replaced by the
assumed all-ones condition. In the analogue of Lemma 3.2 — for a prime $p \nmid N$, an index $i$
with $\gcd(i,N)=1$, and $p^k \mid Nn-i$ with $p^k > i$ — write $Ns = i + c\,p^k$ with
$s = n \bmod p^k$: the bounds $Ns - i > -p^k$ and $Ns - i < N p^k$ give $0 \le c \le N-1$; the
identity $Nt = c + i/p^k$ with $0 < i/p^k < 1$ places $t$ in cell $c$; and reducing modulo $N$ gives
$\gcd(c,N)=1$, so the criterion applies and $\Delta^u(n/p^k) = 1$. Primes dividing $N$ do not divide
$Nn-i$, and no factor $Nn-i$ vanishes since $N \ge 2$. Lemma 3.4 and the proof of Theorem 3.5 are
then reproduced verbatim, using that $\nu_p(u(n))$ counts the layers where $\Delta^u = 1$, which is
where the $\{0,1\}$-valuedness is used. $\blacksquare$

**Verification status.** Not reviewed adversarially in this form (the reviewers saw the earlier,
stronger and partly unjustified version of this section, and both flagged it; the statement here is
the weakened one). Not formalised. For $u = a$ we have $N = 30$ and the criterion holds by
Lemma 3.1, so Theorem 3.5 is the case $u = a$ — which is the only case we have checked. **The $52$
sequences of A295431 have not been checked one by one**; doing so requires only their parameter
lists and $\varphi(N)$ evaluations each, and is left as an immediate follow-up.

For the opposite sign the situation is genuinely less clear, and we state what we believe rather than
what we know. Two things go wrong with a naive transfer of Proposition 5.1 to general $u$. First,
the reflection identity is not automatic: the computation of Section 2 gives
$\Delta^u(x)+\Delta^u(-x) = T - S$ for $x$ avoiding the finitely many points where some $A_s x$ or
$B_t x$ is an integer, and $T-S=1$ — the height-one condition — is what makes it Lemma 2.3. Second,
even with a reflection identity in hand, the construction in Proposition 5.1 uses
$p \equiv 1 \pmod N$, $p > i$ and $\Delta^u_0 = 0$, all of which need checking per sequence.

**Conjecture 6.2.** Let $u$ be a height-one integral factorial ratio satisfying Criterion 6.1, with
$T - S = 1$. Then for $\gcd(i,N)=1$ there is no constant $D \ne 0$ with $(Nn+i) \mid D\,u(n)$ for
all $n$.

**Verification status.** Conjecture; proved here only for $u = a$, $N = 30$ (Proposition 5.1).

---

## 7. Relation to the announcement in `formal-conjectures` issue #4923

We record, as a matter of fact and without a priority claim, an announcement of the existence
statement that pre-dates the completion of this paper by one day.

**The facts.** Issue #4923 of the `formal-conjectures` repository ("Possible misformalizations II"),
opened by the user KitaKen1 on 2026-08-13T09:06:53Z and last edited 2026-08-16T00:46:41Z, contains
under the heading "Degenerate witness" the following text:

> "OEIS A211417 `general_divisibility` — **Problem:** `D = 0` makes the current existential vacuous.
> **Update:** the intended version appears true with the explicit positive witness
> `D(r) = lcm(1,…,r)^|{1 ≤ i ≤ r : gcd(i,30)=1}|`. **Likely fix:** state this witness, or require
> `D > 0`. **The general proof is paper-complete but not yet Lean-checked**; the four fixed
> statements are separate in #5010."

The same user is the author of the Lean proofs of the four $r=1$ sister statements merged as pull
request #5010 on 2026-08-16.

**What we could and could not verify.** As of 2026-08-17 we found no public proof text. Issue #4923
has zero comments. The author's repository `KitaKen1/oeis-a211417` states in its README that
`general_divisibility` "is intentionally out of scope … This repository does not count that
statement as a solution and does not include it as a target", and contains no corresponding Lean or
manuscript file; all twelve files in it were enumerated. An arXiv abstract search returned nothing.
We therefore treat the sentence quoted above as an announcement without an accompanying argument,
which is neither evidence for nor against its correctness.

**Comparison.** Table 4 sets the two side by side.

**Table 4.** The announced witness and ours.

| | Issue #4923 (2026-08-16) | this paper (2026-08-17) |
|---|---|---|
| existence of $D(r)$, general $r$ | announced "paper-complete", proof not public | proved (Theorem 3.5) |
| explicit witness | $\operatorname{lcm}(1,\dots,r)^{\lvert L_r\rvert}$ | $\prod_{p\le r,\,\gcd(p,30)=1} p^{E(p,r)}$ |
| value at $r=7$ | $420^2 = 176400$ | $7$ |
| value at $r=23$ | $\approx 1.26\times10^{68}$ | $81800719 \approx 8.2\times 10^{7}$ |
| $C(k,r)$ family, general $r$ | not mentioned | proved (Theorem 4.3) |
| infeasibility of $30n+i$ | not mentioned | proved (Proposition 5.1) |
| Lean | announced as not yet done | done, in the form $\exists D>0$ (Section 8) |

**Consistency.** The two are compatible, and in a precise sense our theorem subsumes the announced
witness.

**Corollary 7.1.** For every $r \ge 1$, $D(r)$ divides $\operatorname{lcm}(1,\dots,r)^{|L_r|}$;
consequently

$$P_r(n) \ \Big|\ \operatorname{lcm}(1,\dots,r)^{|L_r|}\cdot a(n) \qquad (n \ge 0).$$

*Proof.* Each of the $\lfloor \log_p r\rfloor$ layers contributing to $E(p,r)$ contributes at most
$|L_r|$, so $E(p,r) \le \lfloor\log_p r\rfloor\cdot|L_r|$, which is the exponent of $p$ in
$\operatorname{lcm}(1,\dots,r)^{|L_r|}$. The divisibility statement then follows from Theorem 3.5.
$\blacksquare$

**Verification status.** Computational (the exponent inequality was checked for all primes and all
$r \le 80$ with no violation, and the divisibility
$D(r) \mid \operatorname{lcm}(1,\dots,r)^{|L_r|}$ verified explicitly for
$r \in \{1,7,11,13,17,23\}$). Not separately reviewed; the proof is one line from Theorem 3.5.

So the validity of the announced witness is a corollary of Theorem 3.5, and our constant is smaller
— by a factor of $25200$ already at $r=7$, and by sixty orders of magnitude at $r=23$.

**Positioning.** We state our claim in the weakest form the evidence supports. The result of
Theorem 3.5 was *independently obtained*; the existence claim was *independently announced* by
KitaKen1 in `formal-conjectures` issue #4923 on 2026-08-16, and to our knowledge no public proof
text for it exists as of 2026-08-17. We do not claim to be first. Should that proof appear and prove
to be prior, the correct description of this paper becomes: an independent second proof, with a
smaller explicit constant, together with the $C(k,r)$ family (Theorem 4.3), the impossibility of the
opposite sign (Proposition 5.1), and the Lean formalisation.

**One observation adopted.** The issue's first sentence is correct and we have acted on it: the
corpus statement `∃ D : ℤ, ∀ n, divisorProduct n r ∣ D * a n` is vacuous, since $D = 0$ satisfies it
and every integer divides $0$. Our Theorem 3.5 produces a positive explicit constant and therefore
proves the intended, non-vacuous statement; Proposition 5.1 likewise excludes $D=0$ by hypothesis;
and Section 8 both proves the strengthened form and exhibits the vacuity of the literal one as a
machine-checked lemma.

---

## 8. Formal verification in Lean 4

### 8.1 File, environment, axiom audit

The development exists in two forms. The primary artefact is a single self-contained Lean 4 [8]
file, `A211417.lean`, $607$ lines, importing all of `mathlib` [9]; the toolchain is
`leanprover/lean4:v4.34.0-rc1` with `mathlib` pinned at revision
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. The second is the same proof integrated into the
`formal-conjectures` file itself, discussed in Section 8.4. Neither contains a `sorry` of ours, a
`native_decide`, or an `axiom` declaration.

Elaboration of `A211417.lean` by `lake env lean` on an Apple-silicon laptop takes $11.0$–$12.0$ s on
warm cache when the machine is otherwise idle, and $25.6$ s for the first invocation in a fresh
shell. These figures are load-sensitive rather than intrinsic: repeated under concurrent load from
other jobs the same unchanged file took $114$–$130$ s. Four `mathlib` deprecation and style-linter
warnings are emitted at the pinned revision (two deprecated tactic names, one unused `simp`
argument, one `haveI`/`have` style hint); there are no errors.

The file ends with an axiom audit, whose complete output is

```
'OeisA211417.general_divisibility_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA211417.general_divisibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA211417.key_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA211417.thirty_mul_sub_one_dvd_a' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard axioms of Lean's classical foundation, on which `mathlib` itself rests;
nothing else is assumed, and no result is imported from an unverified oracle.

### 8.2 The statements proved

The definitions are taken character-for-character from the corpus file
`FormalConjectures/OEIS/211417.lean`:

```lean
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

def coprimeIndices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

def divisorProduct (n r : ℕ) : ℤ :=
  (coprimeIndices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))
```

The main declarations are the following.

**(i) The conjecture, strengthened.**

```lean
theorem general_divisibility_strong (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, 0 < D ∧ ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ))
```

This is the mathematical content of Bala's conjecture. It is strictly stronger than the corpus
statement, for the reason given next.

**(ii) The literal corpus statement, and its vacuity.** The corpus asks for

```lean
theorem general_divisibility (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ))
```

which we also discharge, with the *same positive* witness, so that (i) is a genuine strengthening
rather than a different theorem. But the literal statement carries no content, and the file says so
with a proof:

```lean
theorem general_divisibility_is_vacuous (r : ℕ) :
    ∃ D : ℤ, ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) :=
  ⟨0, fun n => by simp⟩
```

Anyone can close the corpus goal in three lines by taking $D=0$. This is a machine-checked statement
about the corpus, and it is our recommendation to the maintainers (Section 8.6).

**(iii) The $r=1$ case, re-proved.**

```lean
theorem thirty_mul_sub_one_dvd_a (n : ℕ) : (30 * (n : ℤ) - 1) ∣ (a n : ℤ)
```

This is the AlphaProof/Nexus theorem. Here it is not assumed or imported but obtained in two lines
from the general machinery, via `divisorProduct_one` and $D_{\mathrm{wit}}(1) = 1$.

**(iv) The workhorse.**

```lean
theorem key_dvd (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (divisorProduct n r) ∣ (Dwit r * (a n : ℤ))
-- where  Dwit r = ((r.factorial : ℤ))^(r * r)
```

### 8.3 What is formalised, and what is not

**The sharp constant $D(r)$ of Theorem 3.5 is not formalised.** The Lean witness is the deliberately
crude $D_{\mathrm{wit}}(r) = (r!)^{r^2}$, which is astronomically larger than $D(r)$ — at $r=13$,
for instance, $D(13) = 1001$ against a witness with over a thousand digits. This is a formalisation
choice, not a mathematical retreat: the corpus statement asks only for *some* constant, and a crude
witness lets the low-layer accounting be discharged by a counting argument instead of by a formal
development of $\max_c\#\{\cdots\}$ as a computable function. Concretely, the Lean proof replaces the
two-case split in the proof of Theorem 3.5 by one uniform per-layer inequality:

```lean
lemma per_k_bound (n r p k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∑ i ∈ coprimeIndices r,
        (if p^k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0)
      ≤ (if p^k ≤ r then (r : ℤ) else 0) + f n (p^k)
```

where `f n d` is $\Delta(n/d)$ computed with natural division. This is Lemma 3.4 with parts (2) and
(3) merged into the branch $p^k > r$ — where uniqueness of the witness is proved exactly as above
and Lemma 3.2 supplies $\Delta = 1$ — and with the crude bound $N_k \le |L_r| \le r$ in the branch
$p^k \le r$. Summing over $k$ and absorbing the low-layer budget into $(r!)^{r^2}$ (lemma `S_bound`,
using $\#\{k \ge 1: p^k \le r\} \le r$ and $\nu_p(r!) \ge 1$ for $p \le r$) completes the argument. A
formalisation of the sharp $D(r)$ would require the two-case split and a `Finset`-level treatment of
the maximal residue class, and we did not attempt it.

The following are likewise *not* formalised: Theorem 4.3 and Lemmas 4.1, 4.2; Propositions 5.1 and
4.6; Corollaries 3.7, 3.8, 7.1; and Criterion 6.1. Their verification status lines say so
individually.

### 8.4 Statement fidelity, and the corpus-integrated version

Since a formal proof is only as meaningful as the fidelity of its statement, the file includes
machine-checked sanity checks that its index set is the intended one:

```lean
lemma coprimeIndices_one : coprimeIndices 1 = {1} := by decide
lemma coprimeIndices_thirteen : coprimeIndices 13 = {1, 7, 11, 13} := by decide
lemma divisorProduct_one (n : ℕ) : divisorProduct n 1 = 30 * (n : ℤ) - 1
```

together with `a 0 = 1`, `a 1 = 77636318760` and `a 2 = 53837289804317953893960` by `rfl`, which
agree with the OEIS data and with the corpus's own test lemmas. Note that `divisorProduct` is
$\mathbb{Z}$-valued precisely so that the negative factors occurring for small $n$ are handled
honestly; see Remark 3.6.

The strongest form of statement fidelity available is to prove the theorem inside the corpus file
itself, and we have done that as well. The proof is ported into
`FormalConjectures/OEIS/211417.lean` against `FormalConjecturesUtil` and the corpus's own
definitions — no restatement, no renaming — where it discharges `general_divisibility` and
`thirty_mul_sub_one_dvd_a` by term proofs and adds `general_divisibility_strong` and
`general_divisibility_is_vacuous`. That file elaborates without error under the corpus's own build
(Lean `v4.27.0`). The only `sorry` warnings it emits are the five that were already there and are
other authors' business: the four $r=1$ sister statements and the supercongruence conjecture. We
have not submitted this upstream; see Section 8.6.

### 8.5 Two techniques worth recording

**Lemma 3.1 is one call to `omega`.** The interval-and-congruence argument of Section 3 becomes

```lean
lemma unit_step (c : ℕ) (h29 : c ≤ 29) (h2 : c % 2 ≠ 0) (h3 : c % 3 ≠ 0) (h5 : c % 5 ≠ 0) :
    c / 2 + c / 3 + c / 5 + 1 = c := by omega
```

Lean's linear-integer-arithmetic decision procedure handles division and modulus by numerals
natively, so the hand proof is not needed — a small illustration of the fact that the difficulty of a
formalisation and the difficulty of the informal argument are only loosely related.

**Everything is reduced to indicator sums before any inequality is proved.** The valuation of a
product is turned into a double sum over indices and layers,

$$\nu_p\Bigl(\prod_{i \in L_r}|30n-i|\Bigr)
\;=\; \sum_{i \in L_r}\ \sum_{k \ge 1} [\,p^k \mid |30n-i|\,]
\;=\; \sum_{k \ge 1}\ \sum_{i \in L_r} [\,p^k \mid |30n-i|\,],$$

using `padicValNat_dvd_iff_le` for each factor (lemma `count_pow_dvd`) and `Finset.sum_comm` for the
exchange; only then is the per-layer bound applied under `Finset.sum_le_sum`. Working with
`Int.natAbs` throughout, and moving between $\mathbb{Z}$-divisibility and $\mathbb{N}$-valuations by
`Int.natAbs_dvd_natAbs`, keeps the negative factors from ever needing a case split.

### 8.6 A recommendation to the corpus maintainers

`FormalConjectures/OEIS/211417.lean` states `general_divisibility` as $\exists D : \mathbb{Z}$ with
no positivity constraint, and is therefore vacuous as written; we supply a three-line proof of that
fact above. We recommend that it be restated as `∃ D : ℤ, 0 < D ∧ …` (or with an explicit witness
baked in). The same observation was made independently in issue #4923 (Section 7); we found it while
checking whether our theorem implies the corpus statement.

A patch implementing both changes — the strengthened statement and a proof of it — exists and
elaborates against the corpus build (Section 8.4). We have not opened a pull request. Deciding
whether the corpus should carry the strengthened form, and under what attribution given the
announcement discussed in Section 7, is the maintainers' call and not ours to make by merge.

---

## 9. Related work

**Integral factorial ratios.** That $u(n)$ in (1.1) is integral for all $n$ if and only if the
associated step function is everywhere nonnegative is Landau's criterion [3]. The classification of
the height-one integral ratios — a small number of infinite parametric families together with $52$
sporadic examples, of which (1.2) is Chebyshev's — is due to Rodriguez-Villegas, Vasyunin, and Bober
[4, 5], with later work of Soundararajan on larger height. The present paper uses nothing from that
theory beyond the step function itself; what it adds is that the step function's values on the *unit
residue classes* control divisibility of $u(n)$ by products of linear forms.

**The $r=1$ case.** $(30n-1)\mid a(n)$ was proved by DeepMind's AlphaProof/Nexus system [6] and its
Lean proof is public. Our Lemma 3.1 is that proof's central fact, and Corollary 3.9 recovers the
theorem; the Lean development of Section 8 reproves it from scratch rather than importing it. The
four $r=1$ statements for $2n+1$, $3n+1$, $5n+1$ and the $42$-product were formalised by KitaKen1 and
merged into the corpus on 16 August 2026; Theorem 4.3 contains the first three of them as the case
$r=1$ (with worse constants), does not cover the fourth (Remark 4.5), and we make no claim to any of
the four.

**Machine contributions to OEIS conjectures.** The `formal-conjectures` corpus [7] supplies formal
statements of open conjectures with `sorry` in place of proofs; it is both our problem source and,
for this conjecture, the exact statement to be proved, which removes the usual risk that an
autoformalisation proves something other than what was asked. Alongside it, a growing body of
automated and AI-assisted work resolves OEIS comments in bulk. Our automated literature audit of
17 August 2026 recorded, as the nearest neighbours of this problem, a 2026 preprint proving a
*different* conjecture of Bala — for A028342, not A211417 — returned by the search as
arXiv:2607.18313, and the fourth instalment of a series of AI-assisted OEIS resolutions, returned as
arXiv:2607.24832. Neither overlaps with the present result. We record the identifiers for the
reader's orientation and note that we read only their titles and abstracts.

**Placement.** The conjecture resolved here is a comment in an OEIS entry, not a problem of record.
What is perhaps distinctive is the shape of the pipeline: the statement was selected automatically,
the proof was found automatically, it was refuted in part and repaired under automated adversarial
review by models from two other vendors, it was formalised, and the paper was drafted — with no
human supplying a mathematical step at any point. We make no claim about how this scales.

---

## 10. Limitations, and named obstacles

We state plainly what is not done.

1. *$D(r)$ is not shown to be minimal, and is not minimal.* Theorem 3.5 gives an upper bound. It
   coincides with the empirically minimal constant for $r \le 19$ but is too large from $r=23$ on, by
   a factor of $11$ there and by $7\cdot11\cdot17\cdot19\cdot23$ at $r=49$ (Table 3). The diagnosis:
   the low-layer bound $N_k \le \max_c\#\{i \in L_r : i \equiv c\}$ assumes that the worst residue
   class is attained *and* that $\nu_p(a(n))$ receives nothing at the low layers, and these two
   events are correlated — when several indices share a small prime $p$, the integer $n$ is heavily
   constrained and typically forces $\Delta(n/p^k)=1$ at some low layer. Extracting the minimal
   $D(r)$ needs a joint analysis of the low layers, which we have not done. Consequently
   Corollary 3.8 describes our constant only; the growth order of $D_{\min}(r)$ is open.

2. *$C(k,r)$ is loose by a lot, and the mixed product is not covered.* $C(2,1) = 45045$ where the
   truth is $7$; see Remark 4.4, which also says how to improve it. We did not. Separately, Bala's
   statement about $(2n+1)(3n+1)(5n+1)$ mixes three different moduli and is not an instance of
   Theorem 4.3; Remark 4.5 says what would be needed and what we do not claim.

3. *The $52$ sporadic sequences are not checked.* Criterion 6.1 is a finite test per sequence,
   requiring only the parameter lists of A295431 and $\varphi(N)$ evaluations of a step function
   each. We did not obtain that table and run it within the working window. This is the cheapest
   available follow-up.

4. *The supercongruence conjecture is untouched and out of reach of this method.* The other open
   conjecture in the same corpus file, $a(p^k) \equiv a(p^{k-1}) \pmod{p^{3k}}$ for $p \ge 5$ (Bala,
   24 January 2020), belongs to the Wolstenholme–Dwork circle of ideas ($p$-adic Gamma functions,
   formal groups) and is orthogonal to Legendre-layer counting. Nothing here bears on it.

5. *The impossibility direction is proved for one family only.* Section 5 establishes that $30n+i$
   admits no constant. The converse principle that a zero step-function cell implies infeasibility is
   neither proved nor refuted here; all we know is that a zero cell disables our mechanism.
   Conjecture 6.2 states what we expect and do not prove.

6. *The formalisation covers existence, not the sharp constant, and not the sister results.*
   Section 8.3 lists exactly which statements are machine-checked. In particular Theorem 4.3,
   Propositions 5.1 and 4.6, and Corollary 3.8 are pen-and-paper results supported by review and
   computation only; and the Lean witness is $(r!)^{r^2}$, not $D(r)$.

7. *The second review round was targeted, not a fresh full read.* The three statements written in
   response to the first pass — Proposition 5.1, Lemma 4.2 with the expanded proof of Theorem 4.3,
   and the corrected Corollary 3.8 — were reviewed in round 2 and returned OK. But that round
   examined five nominated items and did not re-audit the core mechanism, so its assurance is
   narrower than a first-pass review of the whole document; and it was conducted by the same reviewer
   (Qwen) whose first pass had raised two of the objections, not by a third party. Two things remain
   unreviewed by anyone: the *lower* bound of Corollary 3.8, which is the `codex` reviewer's own
   construction, and Proposition 4.6, written after both rounds.

8. *The first-pass verdicts were VALID-WITH-GAPS, not VALID.* For transparency: the `codex` review
   recorded one false auxiliary corollary (the discarded $O(r\log\log r)$ claim), one unproved
   necessity direction, and one editorial omission in a bound; the Qwen first pass recorded seven
   findings, of which two were about material that had already been repaired in a version the
   reviewer did not see, three concerned the ancillary sections, and one was a presentation defect in
   the table of $D(r)$ values. Neither reviewer reported any error in Lemmas 3.1, 3.2, 3.4 or
   Theorem 3.5, and both stated that explicitly; round 2 then returned VALID on its five nominated
   items. The first draft of this paper was, nonetheless, wrong in two places, and neither was caught
   by the solver.

9. *One overclaim was found during the writing of this paper, not by review.* The first three
   versions of the underlying manuscript listed Bala's mixed product among the $r=1$ instances of
   Theorem 4.3. It is not one (Remark 4.5). The error was caught while drafting Section 4 and
   subsequently confirmed by round 2; that it survived two independent adversarial reviews is worth
   recording.

10. *The literature search was automated.* We checked for prior proofs by automated search — corpus
    source, repository file listings, the live OEIS page, arXiv abstract search — and found none, but
    automated searches miss things. Section 7 records the one prior announcement we did find, and we
    do not claim priority. Should a prior proof surface, the honest description of this paper is the
    one given at the end of that section.

11. *Computation is not proof.* The script `a211417_verify.py` checks every finite claim and every
    theorem end-to-end in a bounded range, and an independently written script by one reviewer
    re-checks the main divisibility through a disjoint code path. Neither is a proof component, and
    no statement above rests on computation alone except where its verification-status line says so.

---

## Appendix A. Numerical tables

All tables in this appendix are generated by `a211417_verify.py` (Appendix B).

**Table A.1.** The exponents of Theorem 3.5. The maximal deficiency
$\nu_p(P_r(n)) - \nu_p(a(n))$ actually observed over $n \le 400$ never exceeded $E(p,r)$, and
equalled it for every $p$ when $r \le 19$.

| $r$ | $\lvert L_r\rvert$ | $E(p,r)$ for $p$ with $E>0$ | $D(r)$ |
|---|---|---|---|
| $1$ | $1$ | — | $1$ |
| $7$ | $2$ | $E(7)=1$ | $7$ |
| $11$ | $3$ | $E(7)=E(11)=1$ | $77$ |
| $13$ | $4$ | $E(7)=E(11)=E(13)=1$ | $1001$ |
| $17$ | $5$ | $E(7)=\cdots=E(17)=1$ | $17017$ |
| $19$ | $6$ | $E(7)=\cdots=E(19)=1$ | $323323$ |
| $23$ | $7$ | $E(11)=2$; $E(7)=E(13)=E(17)=E(19)=E(23)=1$ | $81800719$ |
| $29$ | $8$ | $E(7)=E(11)=2$; $E(13)=\cdots=E(29)=1$ | $16605545957$ |
| $31$ | $9$ | $E(7)=E(11)=2$; $E(13)=\cdots=E(31)=1$ | $514771924667$ |
| $37$ | $10$ | $E(7)=E(11)=E(13)=2$; $E(17)=\cdots=E(37)=1$ | $247605295764827$ |
| $49$ | $14$ | $E(7)=4$; $E(11)=E(13)=E(17)=E(19)=E(23)=2$; $E(29)=\cdots=E(47)=1$ | $7468554211373095893038987$ |

**Table A.2.** Corollary 3.8 in numbers. The middle column is bounded; the right-hand one is not,
which is what refutes the $O(r\log\log r)$ claim of the first draft.

| $r$ | $\log D(r)$ | $\log D(r) / (r\log r)$ | $\log D(r)/(r \log\log r)$ |
|---|---|---|---|
| $100$ | $127.2$ | $0.2763$ | $0.833$ |
| $200$ | $323.4$ | $0.3052$ | $0.970$ |
| $400$ | $736.0$ | $0.3071$ | $1.028$ |
| $800$ | $1620.7$ | $0.3031$ | $1.066$ |
| $1600$ | $3587.9$ | $0.3039$ | $1.122$ |
| $3200$ | $7792.2$ | $0.3017$ | $1.166$ |

**Table A.3.** The constants of Theorem 4.3, verified end-to-end for $0 \le n \le 40$. They are far
from sharp: Bala's constants at $r=1$ are $7$, $1$, $1$ (Remark 4.4).

| $r$ | $C(2,r)$ | $C(3,r)$ | $C(5,r)$ |
|---|---|---|---|
| $1$ | $45045$ | $280$ | $12$ |
| $2$ | $145568097675$ | $25865840$ | $5544$ |
| $3$ | $294362129962575675$ | $86262576400$ | $4900896$ |
| $5$ | $6.41\times10^{30}$ | $459117704332740252800$ | $558981495072$ |
| $8$ | $4.48\times10^{49}$ | $3.36\times10^{35}$ | $1.79\times10^{22}$ |
| $12$ | $1.51\times10^{77}$ | $1.32\times10^{52}$ | $1.80\times10^{35}$ |

---

## Appendix B. What the verification script checks

The script `notes/proofs/a211417_verify.py` (pure Python plus SymPy; runs in seconds) performs the
following checks, all of which pass with no counterexample.

1. The thirty cell values (2.1); Lemma 3.1 at all eight unit residues; Lemma 2.3 in all $30$
   instances; the seven cells $\Delta_{mc}=0$, $\Delta_{mc-1}=1$ of Lemma 4.1; and, for the $30n+i$
   family, that all relevant cells are $0$ — flagged in the script itself as *not* an impossibility
   proof.

2. Legendre's identity (2.2) against `sympy.factorint`, prime by prime, for $n \le 6$.

3. The core assertion of the second case of Theorem 3.5: over
   $r \in \{1,7,11,13,17,19,23,29,31,37,49,60,100\}$ and $n \le 120$, every prime factor of every
   $30n-i$ exceeding $r$ has non-positive deficiency $\nu_p(P_r(n)) - \nu_p(a(n))$. No violation.

4. The low-layer bound: for the same $r$ and all $n \le 400$, the observed deficiency at each prime
   $p \le r$ is at most $E(p,r)$.

5. Theorem 3.5 end-to-end: $P_r(n) \mid D(r)a(n)$ for $r \in \{1,7,11,13,17,19,23,29,31,37,49\}$ and
   $0 \le n \le 60$, together with the lower bounds for $D_{\min}(r)$ of Table 3.

6. Theorem 4.3 end-to-end for $k \in \{2,3,5\}$, $r \in \{1,2,3,5,8,12\}$, $0 \le n \le 40$; and,
   independently of the theorems, all five of Bala's explicit assertions ($30n-1$, $2n+1$, $3n+1$,
   $5n+1$, and the $42$-product) for $n < 400$.

7. Corollary 3.8: the inequality $E(p,r) \ge \lfloor (r-1)/(30p)\rfloor + 1$ for every eligible prime
   and every $r \le 3200$, plus the ratios of Table A.2.

8. Proposition 5.1: for $i \in \{1,7,11,13,17,19,23,29,31\}$, $p \in \{31,61,151,181,211\}$ with
   $p>i$, and $e \le 3$, that $\nu_p(30n_e+i) = e$ while $\nu_p(a(n_e)) = 0$.

9. Corollary 7.1: $E(p,r) \le \lfloor\log_p r\rfloor\cdot|L_r|$ for all primes and all $r \le 80$,
   and the explicit divisibility $D(r) \mid \operatorname{lcm}(1,\dots,r)^{|L_r|}$ for
   $r \in \{1,7,11,13,17,23\}$.

10. Proposition 4.6: for all $n < 20000$, that $\gcd(x,y)=1$, $\gcd(x,z)\mid 3$, $\gcd(y,z)\mid 2$,
    that the only primes shared by two of the three factors are $2$ and $3$, and that whenever a
    prime is shared the smaller of the two valuations is exactly $1$ — which is the step the proof
    turns on. The witness $\gcd(3,6)=3$ at $n=1$ for Remark 4.5 is checked in the same block.

Independently, the `codex` reviewer wrote a separate checker using a disjoint code path — no SymPy,
no construction of the factorials, direct trial division of the linear products and Legendre
valuations of the five factorials — and reported

```
independent D(13)=1001 check: n=0..50 OK
independent C(3,5)=459117704332740252800 check: n=0..50 OK
```

including the case $n=0$ and comparing prime valuations rather than reusing whole-integer
divisibility.

---

## References

[1] OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*, <https://oeis.org>.
Sequences cited: A211417 (the sequence (1.2); conjectural comments of P. Bala, 24 January 2020 and
28 August 2025), A295431 (Vasyunin's list of the $52$ sporadic integral factorial ratio sequences of
height one).

[2] P. Bala, comments on OEIS A211417, 28 August 2025: "It appears that $a(n)/(30n-1)$ is integral
for all $n$ (checked up to $n=1000$)"; "$7a(n)/(2n+1)$, $a(n)/(3n+1)$, $a(n)/(5n+1)$,
$42a(n)/((2n+1)(3n+1)(5n+1))$ [are] integer for all $n$"; "More generally, for $r \ge 1$, we
conjecture that there exists a constant $D(r)$ such that
$D(r)\cdot a(n)/\prod_{i=1..r,\ i \text{ coprime to } 30}(30n-i)$ is integral for all $n$"; "Similar
results may hold for all the 52 sporadic integral factorial ratio sequences listed in A295431." Also
the supercongruence comment of 24 January 2020.

[3] E. Landau, *Sur les conditions de divisibilité d'un produit de factorielles par un autre*,
Nouvelles Annales de Mathématiques (3) **19** (1900), 344–362.

[4] F. Rodriguez-Villegas, *Integral ratios of factorials and algebraic hypergeometric functions*,
arXiv:math/0701362 (2007).

[5] J. W. Bober, *Factorial ratios, hypergeometric series, and a family of step functions*,
J. London Math. Soc. (2) **79** (2009), 422–444.

[6] G. Tsoukalas et al., *Advancing Mathematics Research with AI-Driven Formal Proof Search*,
arXiv:2605.22763. The Lean output for the case $r=1$ of the present conjecture is
`APNOutputs/OEIS/oeis_a211417_conjecture_specific.lean` in the repository
`google-deepmind/alphaproof-nexus-results`.

[7] Google DeepMind, *formal-conjectures*: a collection of formalized conjectures in Lean 4,
<https://github.com/google-deepmind/formal-conjectures>. File referenced:
`FormalConjectures/OEIS/211417.lean`. Issue #4923 ("Possible misformalizations II", KitaKen1, opened
2026-08-13, body last edited 2026-08-16) and pull request #5010 (merged 2026-08-16) are discussed in
Section 7.

[8] L. de Moura and S. Ullrich, *The Lean 4 theorem prover and programming language*, in: Automated
Deduction — CADE 28, Lecture Notes in Computer Science 12699, Springer, 2021, pp. 625–635.

[9] The mathlib Community, *The Lean mathematical library*, in: Proceedings of the 9th ACM SIGPLAN
International Conference on Certified Programs and Proofs (CPP 2020), ACM, 2020, pp. 367–381.
<https://github.com/leanprover-community/mathlib4>.
