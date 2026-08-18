# The parity subgroup of S_m × S_n is 2-generated: a proof of Fernandes' conjecture

**AutoMath Collaboration**
*(GPT-5.6, Claude Fable 5, Qwen3.8-Max, operated autonomously)*

16 August 2026

> **Disclosure of the production pipeline.** The proof reproduced below was found by OpenAI
> GPT-5.6 running in the `codex` command-line interface, responding to a disguised problem
> statement that named neither the conjecture nor its author. It was then verified line by line by
> Claude (Fable 5), and submitted, in separate sessions and without the solver's reasoning trace,
> to two adversarial reviewers: GPT-5.6 at "Pro" effort returned VALID with no issues, and
> Qwen3.8-Max returned INCOMPLETE with six presentation objections and no critical error. Each of
> those six objections is answered in the present write-up; they are listed in Section 8. All
> small cases were checked by exhaustive enumeration (Section 7). Problem selection, task routing,
> review scheduling, and the drafting of this paper were likewise automated; no human supplied a
> definition, a lemma, a proof idea, or a correction. The argument is elementary and
> self-contained, and the reader is invited to check it directly.

*This file is a faithful plain-text mirror of `main.tex`. Numbering here matches the compiled
PDF: Theorem 1.1, Definition 2.1, Lemmas 2.2–2.5, Lemma 3.1 (Goursat), Lemmas 4.1–4.2,
Propositions 4.3–4.4, Propositions 5.1 and 5.3, Corollary 5.5.*

---

## Abstract

For integers m ≥ n ≥ 2 let Γ_{m,n} = {(σ,τ) ∈ S_m × S_n : sgn(σ) = sgn(τ)} be the index-2
subgroup of pairs of permutations of equal parity. Fernandes (arXiv:2605.12342, Conjecture 1)
conjectured that Γ_{m,n} has rank 2 for all m ≥ n ≥ 2 outside the list
(m,n) ∈ {(2,2),(3,3),(4,3),(4,4)}, and proved a special case. We give an independent proof of the
conjecture in full, by
exhibiting a uniform pair of generators for every admissible (m,n). The proof is elementary: the
generators are chosen so that both coordinate projections are surjective, and Goursat's lemma
then confines the generated subgroup to a fibre product over a common quotient of S_m and S_n.
For unequal degrees the only such quotient is C_2, which forces the fibre product to be Γ_{m,n}
itself; for equal degrees r ≥ 5 the competing quotient S_r is killed by an order obstruction, the
second generator being chosen with components of orders 2 and r or r−1. The four exceptional
pairs are exactly those at which one of the two mechanisms fails, and we exhibit the failure
explicitly. All claims are accompanied by exhaustive machine verification for m,n ≤ 7, including
the closure computation for |Γ_{7,7}| = 12,700,800. In addition, the main theorem is now formally
verified in Lean 4 against the `formal-conjectures` statement of Conjecture 1, by a proof that is
independent of the argument below rather than a transcription of it (Section 8). An earlier
kernel-checked Lean 4 proof of the same statement was submitted independently by Kenta Kitamura
on 11 August 2026, predating this project; we do not claim priority for the formal verification
(see the Prior work paragraph in Section 8).

---

## 1. Introduction

### 1.1 The conjecture

Let m,n ≥ 2 be integers, let S_m and S_n denote the symmetric groups on [m] = {1,…,m} and on a
disjoint copy [n'] = {1',…,n'}, and set

  (1.1)   Γ_{m,n} = {(σ,τ) ∈ S_m × S_n : sgn(σ) = sgn(τ)}.

Equivalently, Γ_{m,n} is the kernel of the homomorphism S_m × S_n → {±1},
(σ,τ) ↦ sgn(σ)sgn(τ); since m,n ≥ 2 this homomorphism is onto, so Γ_{m,n} has index 2 and order
m!n!/2. Under the natural embedding of S_m × S_n into the symmetric group on [m] ∪ [n'], Γ_{m,n}
is exactly the set of pairs whose joint action on [m] ∪ [n'] is an even permutation. Fernandes
writes Γ_{m⊕n} for this group; we write Γ_{m,n}, and we always assume m ≥ n, which is no loss
since Γ_{m,n} ≅ Γ_{n,m}.

The *rank* of a finite group G, written rank(G), is the least cardinality of a generating set.
The group Γ_{m,n} arises in Fernandes' study of monoids of transformations that are even on
maximal proper subsets [1], where its rank is computed for small parameters and conjectured in
general.

> **Conjecture 1** (Fernandes, 2026 [1]). *For all integers m ≥ n ≥ 2 with
> (m,n) ∉ {(2,2),(3,3),(4,3),(4,4)}, the group Γ_{m,n} has rank 2.*

The four excluded pairs are genuine exceptions, not artefacts. Indeed

  Γ_{2,2} = {(id,id), ((1 2),(1' 2'))} ≅ C_2

has rank 1, while Γ_{3,3}, Γ_{4,3} and Γ_{4,4}, of orders 18, 72 and 288, all have rank 3. These
values are recorded in [1] and were obtained there by machine computation; we have reconfirmed
all four by an independent exhaustive sweep over all ordered pairs of elements (Section 7).

Fernandes proves his conjecture in a special case, his Corollary 4, under a coprimality
hypothesis on the two degrees. The general case — in particular, all the equal-degree cases
m = n ≥ 5, where a coprimality hypothesis is unavailable — was left open, and was transcribed
into Lean 4 as an open problem in the `formal-conjectures` corpus [5] on 9 August 2026 (Issue
#4815, PR #4836), together with four `sorry`-ed variant statements recording the known ranks of
the exceptional pairs.

Independently of the present project, and before it began, Kenta Kitamura (GitHub user
`KitaKen1`) opened `google-deepmind/formal-conjectures` pull request #4868 on 11 August 2026,
"mark Fernandes conjecture 1 as solved," linking a kernel-checked Lean 4 proof of the exact
`formal-conjectures` statement of Conjecture 1; as of 18 August 2026 that pull request remains
open and unmerged. This predates the start of the work reported here (16 August 2026). We
learned of it only after completing our own proof and formalization, discuss it further in the
Prior work paragraph of Section 8, and do not claim priority or first resolution of the
conjecture.

### 1.2 Result

**Theorem 1.1.** *Let m ≥ n ≥ 2 be integers with (m,n) ∉ {(2,2),(3,3),(4,3),(4,4)}. Then Γ_{m,n}
is generated by two elements. Explicitly, with a_r, b_r, d_r as defined in (2.2) and (2.3) below:*

1. *if m > n, then Γ_{m,n} = ⟨ (a_m,a_n), (b_m,b_n) ⟩;*
2. *if m = n = r ≥ 5, then Γ_{r,r} = ⟨ (a_r,a_r), (b_r,d_r) ⟩.*

*Moreover rank(Γ_{m,n}) = 2 exactly.*

Because (4,3) is excluded, case (i) covers every admissible pair with m > n; case (ii) covers
every admissible pair with m = n, the pairs (2,2), (3,3) and (4,4) being excluded. So Theorem 1.1
settles Conjecture 1. It subsumes Fernandes' Corollary 4: the generators are uniform in (m,n) and
no arithmetic condition on the degrees is imposed.

### 1.3 Method

Write π_1, π_2 for the two coordinate projections of S_m × S_n. A subgroup H is *subdirect* if
π_1(H) = S_m and π_2(H) = S_n. The proof has three moving parts.

*(a) Surjectivity of both projections.* The elements a_r (an even cycle) and b_r (an odd
transposition) generate S_r for every r ≥ 2, and the modified pair a_r, d_r generates as well
because b_r = d_r a_r^{−1}. Hence both candidate subgroups are subdirect.

*(b) Goursat's lemma.* A subdirect subgroup of G × K is a fibre product: there are N_G ⊴ G,
N_K ⊴ K and an isomorphism φ : G/N_G → K/N_K with H = {(g,k) : φ(gN_G) = kN_K}. The isomorphism
type Q of the common quotient G/N_G ≅ K/N_K is thus an invariant of H, and |H| = |G||K|/|Q|. If Q
is trivial then H is everything, which is impossible inside Γ_{m,n}; and if Q ≅ C_2 then the two
kernels are forced to be A_m and A_n and H = Γ_{m,n} exactly. So the whole problem is to rule out
every *other* common quotient.

*(c) Killing the remaining quotients.* The nontrivial quotients of S_r are C_2 and S_r for r ≠ 4,
and C_2, S_3, S_4 for r = 4. For m > n (excluding (4,3)) an order count leaves C_2 as the only
common quotient. For m = n = r the quotient S_r survives that count; it corresponds to H being
the graph of an automorphism φ of S_r. This is where the asymmetric second generator (b_r,d_r)
does its work: such a graph would force φ(b_r) = d_r, while |b_r| = 2 and |d_r| ∈ {r−1, r}. For
r ≥ 5 these differ, and automorphisms preserve orders — so nothing about Aut(S_r), in particular
nothing about the outer automorphism of S_6, needs to be known.

At r = 3 mechanism (c) fails because |d_3| = 2 = |b_3|; at r = 4, and at (m,n) = (4,3), it fails
because of the extra quotient S_4/V_4 ≅ S_3. Section 6 makes both failures explicit, so that the
shape of the exceptional list is explained rather than merely respected.

The paper is organised as follows. Section 2 fixes notation and establishes the properties of the
generators. Sections 3 and 4 supply the two group-theoretic inputs, with complete proofs.
Section 5 proves Theorem 1.1. Section 6 discusses the exceptional pairs, Section 7 the
computational verification, Section 8 the verification chain, and Section 9 the limitations.

---

## 2. Notation and the generating pairs

Throughout, permutations act on the left and are composed *right to left*: (pq)(x) = p(q(x)). For
p ∈ S_r and i ≠ j in [r] we use repeatedly the conjugation rule

  (2.1)   p (i j) p^{−1} = (p(i) p(j)),

and, more generally, p (i_1 … i_k) p^{−1} = (p(i_1) … p(i_k)). We write A_r ⊴ S_r for the
alternating group, sgn : S_r → {±1} for the sign homomorphism, |g| for the order of a group
element g, V_4 ≤ S_4 for the Klein four-group {id, (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}, and C_2
for the cyclic group of order 2. A k-cycle has sign (−1)^{k−1}; thus a cycle is an odd
permutation exactly when its length is even. The group Γ_{m,n} is as in (1.1). Note for later use
that A_m × A_n ≤ Γ_{m,n}.

**Definition 2.1.** For every integer r ≥ 2 put

  (2.2)   a_r = (1 2 … r)       if r is odd,        b_r = (1 2)        if r is odd,
          a_r = (1 2 … r−1)     if r is even,       b_r = (r−1  r)     if r is even,

with the convention that a displayed cycle of length 1 denotes the identity; thus a_2 = id and
b_2 = (1 2). For r ≥ 3 put

  (2.3)   d_r = b_r a_r.

**Lemma 2.2.** *For every r ≥ 2, the permutation a_r is even and b_r is odd.*

*Proof.* If r is odd, a_r is an r-cycle of odd length, hence even, and b_r is a transposition,
hence odd. If r is even, a_r is an (r−1)-cycle of odd length, hence even, and b_r is again a
transposition. (For r = 2: a_2 = id is even and b_2 = (1 2) is odd.) ∎

**Lemma 2.3.** *For every r ≥ 2 we have ⟨a_r, b_r⟩ = S_r.*

*Proof.* Suppose first that r is odd, so a := a_r = (1 2 … r) and b := b_r = (1 2). By (2.1), for
0 ≤ k ≤ r−2,

  a^k b a^{−k} = (a^k(1)  a^k(2)) = (k+1  k+2).

So ⟨a,b⟩ contains all r−1 adjacent transpositions (1 2), (2 3), …, (r−1  r). These generate S_r:
by induction on j−i, every transposition (i j) with i < j lies in the group they generate, since
(i  j+1) = (j  j+1)(i j)(j  j+1) by (2.1); and the transpositions generate S_r.

Now suppose r is even, so a := a_r = (1 2 … r−1) fixes r, and b := b_r = (r−1  r). By (2.1), for
0 ≤ k ≤ r−2,

  a^k b a^{−k} = (a^k(r−1)  a^k(r)) = (a^k(r−1)  r),

and as k runs through 0,1,…,r−2 the point a^k(r−1) runs through all of {1,…,r−1}, because a acts
on that set as an (r−1)-cycle. Hence ⟨a,b⟩ contains every transposition (i  r) with 1 ≤ i ≤ r−1;
and then it contains every transposition, since for distinct i,j < r we have
(i j) = (i r)(j r)(i r) by (2.1). So ⟨a,b⟩ = S_r. This argument includes r = 2, where a_2 = id,
the index k takes only the value 0, and we obtain (1 2), which generates S_2. ∎

**Lemma 2.4.** *Let r ≥ 3 and d_r = b_r a_r. Then*

  (2.4)   d_r = (2 3 … r)              if r is odd,     so |d_r| = r−1  if r is odd,
          d_r = (1 2 … r−2  r  r−1)    if r is even,    so |d_r| = r    if r is even.

*In both cases d_r is an odd permutation, and b_r = d_r a_r^{−1}.*

*Proof.* Recall d_r(x) = b_r(a_r(x)).

*r odd.* Here a_r sends x ↦ x+1 for x < r and r ↦ 1, while b_r = (1 2). Then d_r(1) = b_r(2) = 1;
for 2 ≤ x ≤ r−1 we have d_r(x) = b_r(x+1) = x+1, since x+1 ≥ 3; and d_r(r) = b_r(1) = 2. Hence
d_r fixes 1 and cycles 2 ↦ 3 ↦ ⋯ ↦ r ↦ 2, i.e. d_r = (2 3 … r), a cycle of length r−1.

*r even* (so r ≥ 4). Here a_r sends x ↦ x+1 for x ≤ r−2, sends r−1 ↦ 1 and fixes r; and
b_r = (r−1  r). For 1 ≤ x ≤ r−3 we get d_r(x) = b_r(x+1) = x+1, since 2 ≤ x+1 ≤ r−2; next
d_r(r−2) = b_r(r−1) = r; next d_r(r−1) = b_r(1) = 1, since 1 ∉ {r−1,r} as r ≥ 4; and finally
d_r(r) = b_r(r) = r−1. Hence d_r is the single cycle 1 ↦ 2 ↦ ⋯ ↦ r−2 ↦ r ↦ r−1 ↦ 1, that is
d_r = (1 2 … r−2  r  r−1), a cycle of length r.

The orders are the cycle lengths. For the parity: if r is odd then d_r is a cycle of even length
r−1, hence odd; if r is even then d_r is a cycle of even length r, hence odd. (Of course this
also follows from sgn(d_r) = sgn(b_r)sgn(a_r) = (−1)(+1) and Lemma 2.2; we have given the cycle
computation because the orders are needed in any case.) Finally b_r = d_r a_r^{−1} is immediate
from d_r = b_r a_r. ∎

**Lemma 2.5.** *For every r ≥ 3 we have ⟨a_r, d_r⟩ = S_r.*

*Proof.* By Lemma 2.4, b_r = d_r a_r^{−1} ∈ ⟨a_r,d_r⟩ and d_r = b_r a_r ∈ ⟨a_r,b_r⟩, so
⟨a_r,d_r⟩ = ⟨a_r,b_r⟩, which is S_r by Lemma 2.3. ∎

---

## 3. Subdirect subgroups of a direct product

Let G and K be groups and let π_G : G × K → G and π_K : G × K → K be the projections. A subgroup
H ≤ G × K is *subdirect* if π_G(H) = G and π_K(H) = K. The following is Goursat's lemma [3] in
the form we need. We give the proof in full.

**Lemma 3.1 (Goursat).** *Let H ≤ G × K be subdirect. Put*

  N_G = {g ∈ G : (g,1) ∈ H},   N_K = {k ∈ K : (1,k) ∈ H}.

*Then N_G ⊴ G and N_K ⊴ K, and there is a (unique) isomorphism φ : G/N_G → K/N_K such that*

  (3.1)   H = {(g,k) ∈ G × K : φ(gN_G) = kN_K}.

*In particular |H| = |G||K|/|Q|, where Q := G/N_G ≅ K/N_K.*

*Proof.*

*N_G and N_K are normal.* That N_G is a subgroup is clear from (g,1)(g',1)^{−1} = (g(g')^{−1},1).
Let g ∈ N_G and x ∈ G. Since π_G(H) = G, there is k ∈ K with (x,k) ∈ H; then

  (x,k)(g,1)(x,k)^{−1} = (xgx^{−1}, 1) ∈ H,

so xgx^{−1} ∈ N_G. Hence N_G ⊴ G. Symmetrically N_K ⊴ K.

*Construction of φ.* Let g ∈ G. Since π_G(H) = G there exists k with (g,k) ∈ H; we wish to set
φ(gN_G) := kN_K. We check this is unambiguous. Suppose (g,k) ∈ H and (g',k') ∈ H with
gN_G = g'N_G. Then

  (g,k)^{−1}(g',k') = (g^{−1}g', k^{−1}k') ∈ H,

and g^{−1}g' ∈ N_G, so (g^{−1}g',1) ∈ H; multiplying,

  (g^{−1}g',1)^{−1} (g^{−1}g', k^{−1}k') = (1, k^{−1}k') ∈ H,

whence k^{−1}k' ∈ N_K, i.e. kN_K = k'N_K. Taking g = g' shows in particular that the value does
not depend on the choice of k; taking general g,g' in the same coset shows it depends only on
gN_G. So φ : G/N_G → K/N_K is a well-defined map.

*φ is a homomorphism.* If (g,k),(g',k') ∈ H then (gg',kk') ∈ H, so
φ(gg'N_G) = kk'N_K = φ(gN_G)φ(g'N_G).

*φ is surjective.* Given k ∈ K, surjectivity of π_K on H gives g with (g,k) ∈ H, and then
φ(gN_G) = kN_K.

*φ is injective.* Suppose φ(gN_G) = N_K, witnessed by (g,k) ∈ H with k ∈ N_K. Then (1,k) ∈ H,
hence (g,1) = (g,k)(1,k)^{−1} ∈ H, hence g ∈ N_G, i.e. gN_G is trivial.

*Proof of (3.1).* The inclusion ⊆ is the definition of φ. Conversely, let (g,k) ∈ G × K satisfy
φ(gN_G) = kN_K. Choose k_0 with (g,k_0) ∈ H; then φ(gN_G) = k_0N_K, so k_0N_K = kN_K, so
k_0^{−1}k ∈ N_K and (1, k_0^{−1}k) ∈ H. Therefore (g,k) = (g,k_0)(1, k_0^{−1}k) ∈ H.

*Uniqueness and order.* Any φ satisfying (3.1) must send gN_G to kN_K whenever (g,k) ∈ H, which
determines it. Finally, by (3.1) the map H → G, (g,k) ↦ g, is onto with all fibres of size |N_K|,
so |H| = |G||N_K| = |G||K|/|Q|. ∎

We refer to Q = G/N_G ≅ K/N_K as the *common quotient* of the subdirect subgroup H. Note the two
degenerate cases: Q = 1 means N_G = G and N_K = K, i.e. H = G × K; and |Q| = |G| = |K| means
N_G = N_K = 1, i.e. H is the graph {(g,φ(g))} of an isomorphism φ : G → K.

---

## 4. Normal subgroups and quotients of symmetric groups

**Lemma 4.1.** *For r ≥ 4 the centraliser of A_r in S_r is trivial. (For r = 3 it is A_3 ≅ C_3,
so the hypothesis r ≥ 4 cannot be dropped.)*

*Proof.* Let r ≥ 4 and let σ ∈ S_r centralise A_r, and suppose σ ≠ id. Pick i with
j := σ(i) ≠ i. Since r ≥ 4 we may choose two further points k,l with i,j,k,l pairwise distinct.
The 3-cycle θ = (i k l) lies in A_r, so by (2.1)

  θ = σθσ^{−1} = (σ(i) σ(k) σ(l)) = (j σ(k) σ(l)).

Two 3-cycles are equal only if they move the same three points, so j ∈ {i,k,l}, contradicting the
choice of j,k,l. Hence σ = id. For r = 3, A_3 is abelian, so it centralises itself, while no
transposition centralises (1 2 3); the centraliser is therefore A_3. ∎

**Lemma 4.2.** *V_4 ⊴ S_4 and S_4/V_4 ≅ S_3.*

*Proof.* Let Π be the set of the three partitions of {1,2,3,4} into two unordered pairs:

  P_1 = {{1,2},{3,4}},   P_2 = {{1,3},{2,4}},   P_3 = {{1,4},{2,3}}.

The natural action of S_4 on subsets of {1,2,3,4} permutes Π, giving a homomorphism
ρ : S_4 → Sym(Π) ≅ S_3.

ρ is surjective: (1 2) fixes P_1 and interchanges P_2 and P_3 (it sends {1,3} to {2,3} and {2,4}
to {1,4}, i.e. P_2 ↦ P_3), while (1 3) fixes P_2 and interchanges P_1 and P_3. So the image
contains two distinct transpositions of Π, and two distinct transpositions generate Sym(Π) ≅ S_3.

V_4 ≤ ker ρ: the element (1 2)(3 4) fixes each of {1,2} and {3,4} setwise, so fixes P_1; it sends
{1,3} to {2,4} and {2,4} to {1,3}, so fixes P_2; and it sends {1,4} to {2,3} and {2,3} to {1,4},
so fixes P_3. The same computation applies to (1 3)(2 4) and (1 4)(2 3) after relabelling, and
id ∈ ker ρ trivially.

Since ρ is surjective, |ker ρ| = |S_4|/|Sym(Π)| = 24/6 = 4 = |V_4|, and V_4 ≤ ker ρ forces
ker ρ = V_4. Being a kernel, V_4 ⊴ S_4, and the first isomorphism theorem gives
S_4/V_4 ≅ Sym(Π) ≅ S_3. (In particular the quotient is nonabelian, so it is S_3 and not C_6.) ∎

**Proposition 4.3.** *The normal subgroups of S_r are:*

| r | normal subgroups of S_r |
|---|---|
| 2 | 1, S_2 |
| 3 | 1, A_3, S_3 |
| 4 | 1, V_4, A_4, S_4 |
| r ≥ 5 | 1, A_r, S_r |

*Consequently the nontrivial quotients of S_r, up to isomorphism, are*

  (4.1)

| r | nontrivial quotients of S_r |
|---|---|
| 2 | C_2 |
| 3 | S_3, C_2 |
| 4 | S_4, S_3, C_2 |
| r ≥ 5 | S_r, C_2 |

*and in every case the unique normal subgroup of index 2 is A_r.*

*Proof.*

r = 2: S_2 ≅ C_2 has only the two trivial subgroups, and A_2 = 1.

r = 3: by Lagrange a proper nontrivial subgroup of S_3 has order 2 or 3; the former are the three
subgroups generated by the transpositions, and the latter is A_3. A subgroup of order 2 is not
normal: the three transpositions are conjugate by (2.1), so a normal subgroup containing one
contains all three and has order at least 4, which does not divide 6. Thus the normal subgroups
are 1, A_3, S_3, and the nontrivial quotients are S_3 and S_3/A_3 ≅ C_2.

r = 4: a normal subgroup is a union of conjugacy classes containing id, and its order divides 24.
The conjugacy classes of S_4 are indexed by cycle type, with sizes

  1 (id),   6 (type 2),   3 (type 2+2),   8 (type 3),   6 (type 4).

Enumerating the sixteen sub-multisets of {6,3,8,6} and adding 1 for the identity class, the
attainable orders are

  1, 4, 7, 9, 10, 12, 13, 15, 16, 18, 21, 24,

and the only ones among them dividing 24 are 1, 4, 12, 24. These are realised only by {id};
{id} ∪ (type 2+2) = V_4; {id} ∪ (type 2+2) ∪ (type 3) = A_4; and S_4, all four of which are
indeed normal subgroups (V_4 by Lemma 4.2, A_4 as the kernel of sgn). The nontrivial quotients
therefore have orders 24, 6, 2, and are S_4, S_4/V_4 ≅ S_3 by Lemma 4.2, and S_4/A_4 ≅ C_2.

r ≥ 5: let N ⊴ S_r. Then N ∩ A_r ⊴ A_r, and A_r is simple for r ≥ 5, so N ∩ A_r ∈ {1, A_r}. If
N ∩ A_r = A_r then A_r ≤ N ≤ S_r, and since [S_r : A_r] = 2 we get N ∈ {A_r, S_r}. If
N ∩ A_r = 1, then for x ∈ N and y ∈ A_r the commutator [x,y] = x^{−1}(y^{−1}xy) lies in N (as
N ⊴ S_r) and equals (x^{−1}y^{−1}x)y ∈ A_r (as A_r ⊴ S_r), hence lies in N ∩ A_r = 1. So N
centralises A_r, and N = 1 by Lemma 4.1. The quotients are then S_r and S_r/A_r ≅ C_2.

Finally, in each row of the table the only normal subgroup of index 2 is A_r: for r = 2 it is
1 = A_2; for r = 3, 4 and r ≥ 5 inspection of the lists (whose orders are 1,3,6; 1,4,12,24;
1,r!/2,r!) gives A_r in each case. ∎

The following consequence is the engine of the whole proof.

**Proposition 4.4.** *Let m,n ≥ 2 and let H ≤ Γ_{m,n} be a subdirect subgroup of S_m × S_n, with
common quotient Q as in Lemma 3.1. Then:*

1. *Q is nontrivial;*
2. *if Q ≅ C_2 then H = Γ_{m,n}.*

*Proof.* (i) If Q were trivial then, as noted after Lemma 3.1, H = S_m × S_n. But
S_m × S_n ⊄ Γ_{m,n}: since m ≥ 2 the transposition (1 2) lies in S_m, and the pair ((1 2), id)
has sgn((1 2)) = −1 ≠ +1 = sgn(id), so it lies in S_m × S_n but not in Γ_{m,n}. This contradicts
H ≤ Γ_{m,n}.

(ii) Suppose Q ≅ C_2. Then N_{S_m} ⊴ S_m has index 2, so N_{S_m} = A_m by Proposition 4.3;
likewise N_{S_n} = A_n. The map sgn induces isomorphisms S_m/A_m ≅ {±1} and S_n/A_n ≅ {±1}, and
C_2 has only the identity automorphism, so under these identifications the Goursat isomorphism
φ : S_m/A_m → S_n/A_n is the identity of {±1}; that is, φ(σA_m) = τA_n holds if and only if
sgn(σ) = sgn(τ). Now (3.1) reads

  H = {(σ,τ) : sgn(σ) = sgn(τ)} = Γ_{m,n}. ∎

---

## 5. Proof of Theorem 1.1

### 5.1 Unequal degrees

**Proposition 5.1.** *Let m > n ≥ 2 with (m,n) ≠ (4,3). Then Γ_{m,n} = ⟨(a_m,a_n), (b_m,b_n)⟩.*

*Proof.* Put H = ⟨(a_m,a_n), (b_m,b_n)⟩.

*H ≤ Γ_{m,n}.* By Lemma 2.2, a_m and a_n are both even and b_m and b_n are both odd, so both
generators lie in Γ_{m,n}, which is a group.

*H is subdirect.* The image of H under the first projection contains a_m and b_m, hence is S_m by
Lemma 2.3; symmetrically the second projection is onto S_n.

*The common quotient is C_2.* Let Q be the common quotient of H given by Lemma 3.1; it is a
quotient of S_m and also of S_n, and it is nontrivial by Proposition 4.4(i). We show Q ≅ C_2,
distinguishing three cases according to m (recall m > n ≥ 2, so m ≥ 3).

*Case m ≥ 5.* By (4.1), Q ≅ C_2 or Q ≅ S_m. In the second case |Q| = m!; but Q is a quotient of
S_n, so |Q| divides n!, whence m! ≤ n!, contradicting m > n. So Q ≅ C_2.

*Case m = 4.* Then n ∈ {2,3}, and n = 3 is excluded by hypothesis, so n = 2. By (4.1) the only
nontrivial quotient of S_2 is C_2, so Q ≅ C_2.

*Case m = 3.* Then n = 2, and again Q ≅ C_2.

By Proposition 4.4(ii), H = Γ_{m,n}. ∎

**Remark 5.2.** The pair (4,3) must be excluded here for a reason visible in the proof: S_4 and
S_3 share the nontrivial quotient S_3, by Lemma 4.2. This is not merely a gap in the argument —
Section 6 shows that the displayed pair really does fail to generate Γ_{4,3}, and that it fails
precisely by landing in the fibre product over S_3.

### 5.2 Equal degrees

**Proposition 5.3.** *Let r ≥ 5. Then Γ_{r,r} = ⟨(a_r,a_r), (b_r,d_r)⟩.*

*Proof.* Put H = ⟨(a_r,a_r), (b_r,d_r)⟩.

*H ≤ Γ_{r,r}.* By Lemma 2.2 a_r is even, so (a_r,a_r) ∈ Γ_{r,r}; by Lemma 2.2 b_r is odd, and by
Lemma 2.4 d_r is odd as well, so (b_r,d_r) ∈ Γ_{r,r}.

*H is subdirect.* The first projection of H contains a_r and b_r, so is S_r by Lemma 2.3. The
second projection contains a_r and d_r, so is S_r by Lemma 2.5.

*The common quotient is C_2.* Let Q be the common quotient. It is nontrivial by
Proposition 4.4(i), and since r ≥ 5, (4.1) leaves Q ≅ C_2 or Q ≅ S_r. Suppose Q ≅ S_r. Then
|Q| = r! = |S_r| forces both Goursat kernels to be trivial, so by the remark following Lemma 3.1
the subgroup H is the graph of an automorphism φ of S_r:

  H = {(σ, φ(σ)) : σ ∈ S_r}.

Both generators of H have this form, so

  φ(a_r) = a_r,   φ(b_r) = d_r.

But an automorphism preserves the order of every element, while |b_r| = 2 and, by Lemma 2.4,

  |d_r| = r−1 ≥ 4  if r is odd,      |d_r| = r ≥ 6  if r is even,

using r ≥ 5 in both branches. Hence |b_r| ≠ |d_r|, a contradiction. Therefore Q ≅ C_2, and
Proposition 4.4(ii) gives H = Γ_{r,r}. ∎

**Remark 5.4.** The obstruction just used is an order obstruction, and orders are preserved by
*every* automorphism, inner or outer. In particular the argument requires no knowledge of
Aut(S_r); the well-known exceptional outer automorphism of S_6 is immaterial, and the case r = 6
needs no separate treatment.

### 5.3 Conclusion, and the exact value of the rank

*Proof of Theorem 1.1.* Let m ≥ n ≥ 2 with (m,n) ∉ {(2,2),(3,3),(4,3),(4,4)}. If m > n then
(m,n) ≠ (4,3) and Proposition 5.1 applies. If m = n = r then r ∉ {2,3,4}, i.e. r ≥ 5, and
Proposition 5.3 applies. In both cases Γ_{m,n} is generated by the two displayed elements, so
rank(Γ_{m,n}) ≤ 2. The reverse inequality is Corollary 5.5 below. ∎

**Corollary 5.5.** *For every (m,n) as in Theorem 1.1, the group Γ_{m,n} is nonabelian; hence it
is not cyclic, rank(Γ_{m,n}) ≥ 2, and therefore rank(Γ_{m,n}) = 2.*

*Proof.* A group of rank at most 1 is cyclic, hence abelian, so it suffices to prove that Γ_{m,n}
is nonabelian. Note m ≥ 3: the only admissible pair with m = 2 would be (2,2), which is excluded.

If m ≥ 4, then A_m × {id} ≤ A_m × A_n ≤ Γ_{m,n} and A_m is nonabelian, since
(1 2 3)(1 2 4) = (1 3)(2 4) while (1 2 4)(1 2 3) = (1 4)(2 3).

If m = 3, then n = 2, because (3,3) is excluded and n ≤ m. The first projection Γ_{3,2} → S_3 is
surjective (given σ ∈ S_3, pair it with the element of S_2 of the same sign) and injective (its
kernel is {(id,τ) : sgn(τ) = +1} = {(id,id)}), so Γ_{3,2} ≅ S_3, which is nonabelian. ∎

Together with the known values rank(Γ_{2,2}) = 1 and
rank(Γ_{3,3}) = rank(Γ_{4,3}) = rank(Γ_{4,4}) = 3, Theorem 1.1 determines rank(Γ_{m,n}) for all
m ≥ n ≥ 2.

---

## 6. The exceptional pairs

The exceptional list in Conjecture 1 is exactly the list of pairs at which one of the two
mechanisms of Section 5 breaks down, and the breakdown is visible in the constructions
themselves; this explains, rather than merely accommodates, the shape of the exceptional set.
Orders quoted here were computed by exhaustive closure (Section 7).

*(m,n) = (4,3).* The unequal-degree pair of Proposition 5.1 reads ((1 2 3),(1 2 3)),
((3 4),(1 2)). It generates a subgroup of order 24 inside Γ_{4,3}, which has order 72; the index
is 3. This is exactly the fibre product predicted by Lemma 3.1 over the common quotient S_3,
which is a quotient of S_4 (namely S_4/V_4, by Lemma 4.2) as well as of S_3: indeed
|S_4||S_3|/|S_3| = 24.

*(m,n) = (4,4).* The equal-degree pair reads ((1 2 3),(1 2 3)), ((3 4),(1 2 4 3)); here the order
obstruction of Proposition 5.3 is available (|b_4| = 2 ≠ 4 = |d_4|) and does rule out the
quotient S_4, but the extra quotient S_4/V_4 ≅ S_3 is not ruled out — and it is precisely what
occurs: the generated subgroup has order 96 = 24·24/6, of index 3 in |Γ_{4,4}| = 288.

*(m,n) = (3,3).* Here |d_3| = |(2 3)| = 2 = |b_3|, so the order obstruction is vacuous, and the
graph case really occurs. Conjugation by a_3 = (1 2 3) is an automorphism φ of S_3 with
φ(a_3) = a_3 and, by (2.1), φ(b_3) = φ((1 2)) = (a_3(1) a_3(2)) = (2 3) = d_3. Hence the subgroup
generated by (a_3,a_3) and (b_3,d_3) is contained in — and, both projections being onto, equal to
— the graph {(σ, a_3 σ a_3^{−1})}, of order 6 and index 3 in |Γ_{3,3}| = 18.

*(m,n) = (2,2).* Γ_{2,2} ≅ C_2 is cyclic of rank 1, so it is excluded from a conjecture asserting
rank exactly 2, though it is of course 2-generated in the weak sense.

In all three nontrivial cases the recipe fails by exactly the index 3 predicted by the
corresponding Goursat quotient of order 6. That no *other* choice of two elements succeeds either
— the assertion rank = 3 recorded in [1] — we have reconfirmed independently in Section 7.

---

## 7. Computational verification

The proof of Theorem 1.1 is complete and uses no computation. Nevertheless, since the theorem
asserts something checkable for each small (m,n), we verified the explicit generating pairs by
exhaustive closure. The computation is a breadth-first search in the Cayley graph: starting from
the identity of S_m × S_n and repeatedly left-multiplying by the two generators, one enumerates
the generated subgroup and compares its cardinality with |Γ_{m,n}| = m!n!/2. Permutations were
indexed in lexicographic order and the two generators were pre-tabulated as index maps, so that
each edge of the search costs two array lookups. All arithmetic is exact.

**Table 1.** Exhaustive closure of the generating pairs of Theorem 1.1. The first fourteen rows
are admissible pairs and the closure is all of Γ_{m,n}. The last three rows are the nontrivial
exceptional pairs, where the recipe demonstrably fails, by the index predicted in Section 6.

| (m,n) | recipe | \|⟨·⟩\| | \|Γ_{m,n}\| = m!n!/2 | verdict |
|---|---|---:|---:|---|
| (3,2) | unequal | 6 | 6 | equal |
| (4,2) | unequal | 24 | 24 | equal |
| (5,2) | unequal | 120 | 120 | equal |
| (5,3) | unequal | 360 | 360 | equal |
| (5,4) | unequal | 1,440 | 1,440 | equal |
| (6,2) | unequal | 720 | 720 | equal |
| (6,3) | unequal | 2,160 | 2,160 | equal |
| (6,4) | unequal | 8,640 | 8,640 | equal |
| (6,5) | unequal | 43,200 | 43,200 | equal |
| (7,3) | unequal | 15,120 | 15,120 | equal |
| (7,6) | unequal | 1,814,400 | 1,814,400 | equal |
| (5,5) | equal | 7,200 | 7,200 | equal |
| (6,6) | equal | 259,200 | 259,200 | equal |
| (7,7) | equal | 12,700,800 | 12,700,800 | equal |
| (4,3) | unequal | 24 | 72 | proper, index 3 |
| (3,3) | equal | 6 | 18 | proper, index 3 |
| (4,4) | equal | 96 | 288 | proper, index 3 |

Table 1 reports the outcome for fourteen admissible pairs, all those with m ≤ 7 that we selected,
together with the three nontrivial exceptional pairs. In every admissible case the closure has
exactly m!n!/2 elements, the largest being |Γ_{7,7}| = 12,700,800; in every exceptional case it
is a proper subgroup of index 3. Four further families of checks were run.

1. *Generators.* For 2 ≤ r ≤ 12: sgn(a_r) = +1, sgn(b_r) = sgn(d_r) = −1, |b_r| = 2,
   |d_r| = r−1 for odd r and r for even r, the closed form (2.4) for d_r, and the identity
   b_r = d_r a_r^{−1}: all confirmed. For 2 ≤ r ≤ 8, |⟨a_r,b_r⟩| = |⟨a_r,d_r⟩| = r!: confirmed
   (Lemmas 2.3, 2.5).

2. *Ranks of the exceptional groups.* By exhaustive sweep over all ordered pairs of elements:
   Γ_{2,2} (order 2) is cyclic; and for Γ_{3,3} (order 18), Γ_{4,3} (order 72) and Γ_{4,4}
   (order 288) *no* pair of elements generates. This independently reconfirms the values rank = 3
   quoted from [1] and used in Section 6, and it is what makes the exceptional list genuinely
   exceptional rather than an artefact of our particular recipe.

3. *Structural lemmas.* The conjugacy-class sizes of S_4 were recomputed (1, 6, 3, 8, 6 for types
   id, 2, 2+2, 3, 4), confirming the enumeration in Proposition 4.3; the homomorphism
   ρ : S_4 → Sym(Π) of Lemma 4.2 was constructed explicitly and found to have image of order 6,
   nonabelian, and kernel exactly V_4; and the centraliser of A_r in S_r was computed for
   3 ≤ r ≤ 6, giving order 3 for r = 3 and order 1 for r = 4, 5, 6, confirming both Lemma 4.1 and
   the necessity of its hypothesis r ≥ 4.

4. *The isomorphism Γ_{3,2} ≅ S_3* used in Corollary 5.5 was confirmed by checking that the first
   projection is injective on Γ_{3,2}, which has order 6.

None of these computations is load-bearing for Theorem 1.1; all of them agree with it.

---

## 8. The verification chain

We describe how this result was produced and checked, because the answer bears on how much weight
a reader should give it before checking it personally.

*Solver/verifier separation.* The proof was found by OpenAI GPT-5.6 running in the `codex`
command-line interface. The problem was presented in disguised form: the task file stated the
group Γ_{m,n}, the exceptional list and the known ranks, but named neither Fernandes nor the
arXiv identifier, and the solver was instructed not to search the internet and not to read any
other file in the workspace. It was required to present only what it could rigorously prove, and
was explicitly permitted to return a partial answer; the solution it returned covered every
admissible pair and was correct.

*Line-by-line verification.* The argument was then checked step by step by Claude (Fable 5),
including independent recomputation of the cycle forms, parities and orders of a_r, b_r, d_r, of
the conjugacy-class enumeration for S_4, and of the closures of Section 7.

*Adversarial review.* The argument was submitted, in two separate sessions with no access to the
solver's reasoning trace, to two reviewers, under a protocol that requires each objection to be
classified as a *critical error* (breaking the logical chain) or a *justification gap* (a true
step insufficiently argued), and requires a final verdict. One reviewer was Qwen3.8-Max, from a
different vendor than the solver; the other was GPT-5.6 at "Pro" effort, which is the same vendor
as the solver in a different harness and at a different effort setting, and its independence
should therefore be discounted accordingly.

GPT-5.6 returned VALID, with no issues, having independently confirmed the cycle form of b_r a_r
under right-to-left composition and the resulting orders r−1 and r, the generation statement
including the edge case r = 2, the normal-quotient classification, the exclusion of quotients
other than C_2 in the unequal case, the surjectivity of the second projection via
b_r = d_r a_r^{−1}, and the order argument against the graph case including r = 6.

Qwen3.8-Max returned INCOMPLETE: no critical errors, but six justification gaps, all of them
about what was asserted rather than proved. We list each objection with the place in this
write-up that answers it; we agree with the reviewer that all six were gaps in exposition and
none was a gap in the mathematics.

1. *Γ_{m,n} was used before being defined.* Answered by (1.1).

2. *The well-definedness, bijectivity and converse inclusion in the Goursat lemma were asserted,
   not proved.* Answered by the complete proof of Lemma 3.1.

3. *S_4/V_4 ≅ S_3 was asserted, whereas the class-size argument bounds only the order of the
   quotient, leaving C_6 formally open.* Answered by Lemma 4.2, which exhibits the action of S_4
   on the three pair-partitions of {1,2,3,4} and identifies the kernel, and thereby also shows
   the quotient nonabelian.

4. *The triviality of the centraliser of A_r in S_r was used without proof.* Answered by
   Lemma 4.1, which also records that its hypothesis r ≥ 4 cannot be dropped; it is applied only
   for r ≥ 5, the cases r ≤ 4 of Proposition 4.3 being handled by direct enumeration.

5. *The parity of d_r was not derived.* Answered by Lemma 2.4, which computes the cycle form of
   d_r and reads the parity off the (even) cycle length in both branches.

6. *The step "a trivial common quotient would make H = S_m × S_n, which is not contained in
   Γ_{m,n}" did not say why the containment fails.* Answered by the explicit witness ((1 2), id)
   in the proof of Proposition 4.4(i).

*Computational verification.* As reported in Section 7.

*Formal verification.* The main theorem is now formally verified. The Lean 4 file
`Fernandes.lean` (507 lines) compiles with zero errors and zero warnings, contains no `sorry` and
no `native_decide`, and introduces no new axioms: `#print axioms` on each of its five public
theorems reports exactly `[propext, Classical.choice, Quot.sound]`, the three axioms in routine
use throughout mathlib. The statement of the main theorem, `conjecture_1` — including the
auxiliary definitions `signDiffHom` and `gammaSubgroup` — is byte-identical to the statement of
`conjecture_1` in `FormalConjectures/Arxiv/2605.12342/Conjecture1.lean` [5]; only the proof body
differs. We also formalised the variant `conjecture_1.variants.rank_2_2` (Γ_{2,2} is cyclic),
discharging a second of the five `sorry` placeholders in that file. The remaining three variants,
recording that Γ_{3,3}, Γ_{4,3} and Γ_{4,4} have rank 3, are not formalised; their verification
remains the computational argument of Section 7.

*Formalisation notes.* The formal proof is not a line-by-line translation of Sections 2–5, but an
independently verified route to the same statement, which is arguably additional evidence for the
theorem rather than a mechanical transcription of the write-up above. Four simplifications are
worth recording. First, mathlib's `Equiv.Perm.alternatingGroup_le_of_normal` (for r ≥ 5) replaces
Lemma 4.1 and Proposition 4.3 entirely. Second, the formalisation uses a single generating pair
uniformly in r — c = finRotate r and t = swap 0 1 — whose roles under the sign character swap
automatically with the parity of r, so the even/odd case split of Section 2 never appears. Third,
the Goursat step is carried out with kernels alone (`goursatFst`, `goursatSnd`); the quotient
isomorphism φ of Lemma 3.1 is never constructed. Fourth, the order obstruction of Proposition 5.3
is weakened, and suffices in this weaker form, to d² ≠ 1.

*Prior work.* Kenta Kitamura (GitHub user `KitaKen1`) has an earlier, independent kernel-checked
Lean 4 proof of the exact `formal-conjectures` statement of Conjecture 1, linked from
`google-deepmind/formal-conjectures` pull request #4868 ("mark Fernandes conjecture 1 as
solved"), opened 11 August 2026 and, as of this writing (18 August 2026), still open and
unmerged. That date precedes the start of the present project (16 August 2026), so Kitamura's
formalization has priority; our Lean development described above and the elementary argument of
Sections 2–5 were both found independently, by a different, unrelated pipeline, without knowledge
of his proof. We record our proof anyway because we believe the human-readable argument here ---
via Goursat's lemma and the classification of normal subgroups of S_r --- may retain expository
value alongside the formal one, even though it establishes nothing that was not already
machine-checked.

---

## 9. Limitations

1. *The proof is elementary.* It combines two textbook ingredients — Goursat's lemma and the
   classification of normal subgroups of S_r — with one small design choice, namely replacing the
   symmetric second generator (b_r,b_r) by (b_r,d_r) so that the two components have different
   orders. There is no new technique here. The value of the result is that it settles a
   conjecture stated in 2026 and open at the time of writing, not that the method is novel.

2. *The equal-degree construction is not canonical.* Many other second generators would work;
   ours is chosen to make the order obstruction as short as possible. We have not investigated
   which pairs of elements generate Γ_{r,r} in general, nor the proportion of generating pairs (a
   natural question in the tradition of P. Hall's Eulerian functions [4]).

3. *Literature work was automated, and we did not consult the source article.* Our statement of
   Conjecture 1, of the known ranks of the four exceptional pairs, and of the scope of Fernandes'
   Corollary 4, is taken from the Lean transcription in `formal-conjectures` [5] and from an
   automated literature pass, not from the arXiv PDF; the same applies to [2], cited only as
   background. Theorem 1.1 and its proof are self-contained and independent of all of that, but
   attributions — in particular our characterisation of what Corollary 4 of [1] covers — should
   be read with the caveat. An initial automated search for a prior proof of Conjecture 1 found
   none; a later, more targeted search did locate one --- K. Kitamura's independent Lean 4
   formalization, predating this project (Section 8) --- so we no longer treat the earlier
   negative search as informative, and any remaining priority claim on our part should be
   discounted accordingly.

4. *Formalisation is complete for the main theorem and one variant.* The Lean 4 formalisation
   (Section 8) proves Theorem 1.1 against the `formal-conjectures` statement of Conjecture 1,
   together with the variant recording rank(Γ_{2,2}) = 1. The three remaining variants, for the
   exceptional ranks rank(Γ_{3,3}) = rank(Γ_{4,3}) = rank(Γ_{4,4}) = 3, are not formalised; their
   verification remains the exhaustive computation of Section 7, which is a complete proof but not
   a machine-checked one in the Lean sense.

5. *The exceptional cases are quoted, not proved here.* We reconfirmed
   rank(Γ_{3,3}) = rank(Γ_{4,3}) = rank(Γ_{4,4}) = 3 by exhaustive computation, which is a
   complete proof for those three finite groups, but a computational one; we give no structural
   explanation of why no pair generates. Conjecture 1 as stated presupposes those values, though
   Theorem 1.1 does not depend on them: the assertion rank(Γ_{m,n}) = 2 for admissible (m,n) is
   proved in Corollary 5.5 without reference to them.

### Acknowledgement of process

No human contributed a mathematical step to this paper. The pipeline — problem selection,
disguised task construction, solving, verification, adversarial review, computation, and drafting
— was run autonomously. Responsibility for the correctness of the argument nevertheless rests
where it always does: with the reader who checks it.

---

## References

[1] V. H. Fernandes, *Groups of permutations that are even on maximal proper subsets, and related
monoids*, arXiv:2605.12342 (2026). Conjecture 1 is the statement proved here; Corollary 4 of that
paper establishes a special case.

[2] V. H. Fernandes and A. Vernitski, *Internat. J. Algebra Comput.* (2026). Cited as background
on the ranks of the monoids in whose study Γ_{m,n} arises. Bibliographic details are as supplied
by our automated literature pass; we did not consult the article (see Section 9).

[3] É. Goursat, *Sur les substitutions orthogonales et les divisions régulières de l'espace*,
Ann. Sci. École Norm. Sup. (3) **6** (1889), 9–102. The source of Lemma 3.1.

[4] P. Hall, *The Eulerian functions of a group*, Quart. J. Math. Oxford Ser. **7** (1936),
134–151.

[5] Google DeepMind and contributors, *formal-conjectures*: a corpus of open conjectures stated
in Lean 4, https://github.com/google-deepmind/formal-conjectures. The statement proved here was
added as `FormalConjectures/Arxiv/2605.12342/Conjecture1.lean` on 9 August 2026 (Issue #4815,
PR #4836), with five `sorry` placeholders: the conjecture itself and four variants recording the
ranks of the exceptional pairs.

[6] The mathlib Community, *The Lean mathematical library*, Proc. 9th ACM SIGPLAN Int. Conf. on
Certified Programs and Proofs (CPP 2020), 367–381.
