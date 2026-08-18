/-
# Fernandes' conjecture on the 2-generation of the parity subgroup of `S_m × S_n`

Formalisation of Conjecture 1 of arXiv:2605.12342 (V. H. Fernandes), following the
proof in `papers/fernandes/main.md`.

The definitions `signDiffHom`, `gammaSubgroup` and the statement of `conjecture_1` are
reproduced verbatim from
`FormalConjectures/Arxiv/2605.12342/Conjecture1.lean`.
-/

import Mathlib

set_option maxHeartbeats 1000000

open Equiv Equiv.Perm Subgroup Function

namespace Fernandes

/-! ## 1. The statement (verbatim from `formal-conjectures`) -/

/--
The group homomorphism `(σ₁, σ₂) ↦ sgn(σ₁) * sgn(σ₂)⁻¹` from `S_m × S_n` to `{±1}`.
Its kernel is exactly `Γ_{m ⊕ n}`.
-/
noncomputable def signDiffHom (m n : ℕ) : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)) * (sign.comp (MonoidHom.snd _ _))⁻¹

/--
The subgroup `Γ_{m ⊕ n} ≤ S_m × S_n` consisting of all pairs of permutations with equal
signature.
-/
noncomputable def gammaSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) :=
  (signDiffHom m n).ker

theorem units_mul_eq_one_iff (a b : ℤˣ) : a * b = 1 ↔ a = b := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
    decide

theorem mem_gammaSubgroup {m n : ℕ} {x : Equiv.Perm (Fin m) × Equiv.Perm (Fin n)} :
    x ∈ gammaSubgroup m n ↔ sign x.1 = sign x.2 := by
  simp [gammaSubgroup, signDiffHom, MonoidHom.mem_ker, units_mul_eq_one_iff]

/-! ## 2. Generic helpers -/

theorem closure_top_of_mem {G : Type*} [Group G] {S T : Set G}
    (h : Subgroup.closure S = ⊤) (hST : ∀ x ∈ S, x ∈ Subgroup.closure T) :
    Subgroup.closure T = ⊤ := by
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  exact fun x hx => hST x hx

/-- Two elements generating a subgroup `Γ` (inside the ambient group) give two elements of
`Γ` generating `Γ` as a group in its own right. -/
theorem exists_pair_of_closure_eq {G : Type*} [Group G] {Γ : Subgroup G} {x y : G}
    (hx : x ∈ Γ) (hy : y ∈ Γ) (h : Subgroup.closure ({x, y} : Set G) = Γ) :
    ∃ g₁ g₂ : Γ, Subgroup.closure ({g₁, g₂} : Set Γ) = ⊤ := by
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  have hxK : (⟨x, hx⟩ : Γ) ∈ Subgroup.closure ({(⟨x, hx⟩ : Γ), ⟨y, hy⟩} : Set Γ) :=
    Subgroup.subset_closure (by simp)
  have hyK : (⟨y, hy⟩ : Γ) ∈ Subgroup.closure ({(⟨x, hx⟩ : Γ), ⟨y, hy⟩} : Set Γ) :=
    Subgroup.subset_closure (by simp)
  have hmap0 : Subgroup.closure ({x, y} : Set G) ≤
      (Subgroup.closure ({(⟨x, hx⟩ : Γ), ⟨y, hy⟩} : Set Γ)).map Γ.subtype := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨_, hxK, rfl⟩
    · exact ⟨_, hyK, rfl⟩
  rw [h] at hmap0
  have hmap : Γ ≤ (Subgroup.closure ({(⟨x, hx⟩ : Γ), ⟨y, hy⟩} : Set Γ)).map Γ.subtype := hmap0
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, hw, hwz⟩ := hmap z.2
  have hwz' : w = z := Subtype.ext hwz
  rwa [hwz'] at hw

/-! ## 3. The generators (Section 2 of the paper)

For a degree `r + 2 ≥ 2` we use the full cycle `c = finRotate (r+2) = (0 1 … r+1)` and the
transposition `t = (0 1)`.  The paper's `a_r` is `c` when the degree is odd and `t * c`
(an `(r+1)`-cycle) when the degree is even; the second generator is the other one of the
two, so that the pair `(b, d)` always consists of a transposition and the remaining
element, whose orders differ. -/

theorem finRotate_mk {r k : ℕ} (hk : k < r + 2) (hk1 : k + 1 < r + 2) :
    finRotate (r + 2) (⟨k, hk⟩ : Fin (r + 2)) = ⟨k + 1, hk1⟩ := by
  rw [finRotate_apply]
  apply Fin.ext
  rw [Fin.val_add]
  simp only [Fin.val_one]
  exact Nat.mod_eq_of_lt hk1

/-- The package of generators used for degree `r + 2`. -/
theorem exists_gens (r : ℕ) :
    ∃ a b d : Equiv.Perm (Fin (r + 2)),
      sign a = 1 ∧ sign b = -1 ∧ sign d = -1 ∧
      Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ ∧
      Subgroup.closure ({a, d} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ ∧
      b * b = 1 ∧ (3 ≤ r → d * d ≠ 1) := by
  classical
  set c : Equiv.Perm (Fin (r + 2)) := finRotate (r + 2) with hcdef
  set t : Equiv.Perm (Fin (r + 2)) := Equiv.swap 0 1 with htdef
  have h01 : (0 : Fin (r + 2)) ≠ 1 := by simp
  have hsigt : sign t = -1 := by rw [htdef]; exact Equiv.Perm.sign_swap h01
  have hsigc : sign c = (-1 : ℤˣ) ^ (r + 1) := by
    rw [hcdef, _root_.sign_finRotate]
    norm_num
  have hcycle : c.IsCycle := by rw [hcdef]; exact isCycle_finRotate
  have hsupp : c.support = Finset.univ := by rw [hcdef]; exact support_finRotate
  have hc0 : c 0 = 1 := by rw [hcdef]; exact finRotate_apply_zero
  have htop : Subgroup.closure ({c, t} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ := by
    have h := Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupp 0
    rw [hc0] at h
    rw [htdef]
    exact h
  have htt : t * t = 1 := by rw [htdef]; exact Equiv.swap_mul_self 0 1
  -- the three two-element sets we need generate everything
  have hct : Subgroup.closure ({c, t * c} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ := by
    refine closure_top_of_mem htop ?_
    intro x hx
    have hc : c ∈ Subgroup.closure ({c, t * c} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    have htc : t * c ∈ Subgroup.closure ({c, t * c} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc
    · have h2 := mul_mem htc (inv_mem hc)
      simpa using h2
  have htct : Subgroup.closure ({t * c, t} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ := by
    refine closure_top_of_mem htop ?_
    intro x hx
    have ht : t ∈ Subgroup.closure ({t * c, t} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    have htc : t * c ∈ Subgroup.closure ({t * c, t} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have h2 := mul_mem ht htc
      rwa [← mul_assoc, htt, one_mul] at h2
    · exact ht
  have htcc : Subgroup.closure ({t * c, c} : Set (Equiv.Perm (Fin (r + 2)))) = ⊤ := by
    refine closure_top_of_mem htop ?_
    intro x hx
    have hc : c ∈ Subgroup.closure ({t * c, c} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    have htc : t * c ∈ Subgroup.closure ({t * c, c} : Set (Equiv.Perm (Fin (r + 2)))) :=
      Subgroup.subset_closure (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc
    · have h2 := mul_mem htc (inv_mem hc)
      simpa using h2
  rcases Nat.even_or_odd r with hr | hr
  · -- degree `r + 2` is even: `a = t * c` (an `(r+1)`-cycle), `b = t`, `d = c`
    refine ⟨t * c, t, c, ?_, hsigt, ?_, htct, htcc, htt, ?_⟩
    · rw [map_mul, hsigt, hsigc, (Even.add_one hr).neg_one_pow]
      norm_num
    · rw [hsigc, (Even.add_one hr).neg_one_pow]
    · intro hr3 hsq
      have hord : orderOf c = r + 2 := by
        rw [hcdef, Equiv.Perm.IsCycle.orderOf (by rw [← hcdef]; exact hcycle)]
        rw [← hcdef, hsupp]
        simp
      have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  · -- degree `r + 2` is odd: `a = c`, `b = t`, `d = t * c`
    refine ⟨c, t, t * c, ?_, hsigt, ?_, htop, hct, htt, ?_⟩
    · rw [hsigc, (Odd.add_one hr).neg_one_pow]
    · rw [map_mul, hsigt, hsigc, (Odd.add_one hr).neg_one_pow]
      norm_num
    · intro hr3 hsq
      have h1 : (1 : ℕ) < r + 2 := by omega
      have h2 : (2 : ℕ) < r + 2 := by omega
      have h3 : (3 : ℕ) < r + 2 := by omega
      have e1 : (t * c) (⟨1, h1⟩ : Fin (r + 2)) = ⟨2, h2⟩ := by
        rw [Equiv.Perm.mul_apply, hcdef, finRotate_mk h1 h2, htdef]
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff]
      have e2 : (t * c) (⟨2, h2⟩ : Fin (r + 2)) = ⟨3, h3⟩ := by
        rw [Equiv.Perm.mul_apply, hcdef, finRotate_mk h2 h3, htdef]
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff]
      have happ : (t * c * (t * c)) (⟨1, h1⟩ : Fin (r + 2)) = ⟨1, h1⟩ := by
        rw [hsq]; rfl
      rw [Equiv.Perm.mul_apply, e1, e2] at happ
      simp [Fin.ext_iff] at happ

/-! ## 4. Structural lemmas (Sections 3–5 of the paper) -/

variable {m n : ℕ}

/-- If `H ≤ Γ`, the second projection of `H` is onto and `A_m × 1 ≤ H`, then `H = Γ`. -/
theorem eq_gamma_left {H : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))}
    (hle : H ≤ gammaSubgroup m n)
    (hsurj : ∀ τ : Equiv.Perm (Fin n), ∃ σ : Equiv.Perm (Fin m), (σ, τ) ∈ H)
    (halt : ∀ σ : Equiv.Perm (Fin m), sign σ = 1 → (σ, (1 : Equiv.Perm (Fin n))) ∈ H) :
    H = gammaSubgroup m n := by
  refine le_antisymm hle ?_
  rintro ⟨σ, τ⟩ hx
  rw [mem_gammaSubgroup] at hx
  simp only at hx
  obtain ⟨σ', hσ'⟩ := hsurj τ
  have h1 : sign σ' = sign τ := mem_gammaSubgroup.1 (hle hσ')
  have h2 : (σ * σ'⁻¹, (1 : Equiv.Perm (Fin n))) ∈ H := by
    refine halt _ ?_
    rw [map_mul, map_inv, hx, ← h1, mul_inv_cancel]
  have h3 := H.mul_mem h2 hσ'
  simpa using h3

/-- If `H ≤ Γ`, the first projection of `H` is onto and `1 × A_n ≤ H`, then `H = Γ`. -/
theorem eq_gamma_right {H : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))}
    (hle : H ≤ gammaSubgroup m n)
    (hsurj : ∀ σ : Equiv.Perm (Fin m), ∃ τ : Equiv.Perm (Fin n), (σ, τ) ∈ H)
    (halt : ∀ τ : Equiv.Perm (Fin n), sign τ = 1 → ((1 : Equiv.Perm (Fin m)), τ) ∈ H) :
    H = gammaSubgroup m n := by
  refine le_antisymm hle ?_
  rintro ⟨σ, τ⟩ hx
  rw [mem_gammaSubgroup] at hx
  simp only at hx
  obtain ⟨τ', hτ'⟩ := hsurj σ
  have h1 : sign σ = sign τ' := mem_gammaSubgroup.1 (hle hτ')
  have h2 : ((1 : Equiv.Perm (Fin m)), τ'⁻¹ * τ) ∈ H := by
    refine halt _ ?_
    rw [map_mul, map_inv, ← hx, ← h1, inv_mul_cancel]
  have h3 := H.mul_mem hτ' h2
  simpa using h3

/-- Both coordinates of the two chosen generators have matching signs, so the generated
subgroup lies inside `Γ`. -/
theorem closure_pair_le_gamma {x₁ y₁ : Equiv.Perm (Fin m)} {x₂ y₂ : Equiv.Perm (Fin n)}
    (h1 : sign x₁ = sign x₂) (h2 : sign y₁ = sign y₂) :
    Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) ≤ gammaSubgroup m n := by
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact mem_gammaSubgroup.2 h1
  · exact mem_gammaSubgroup.2 h2

theorem closure_pair_surj_fst {x₁ y₁ : Equiv.Perm (Fin m)} {x₂ y₂ : Equiv.Perm (Fin n)}
    (h : Subgroup.closure ({x₁, y₁} : Set (Equiv.Perm (Fin m))) = ⊤)
    (σ : Equiv.Perm (Fin m)) :
    ∃ τ, (σ, τ) ∈ Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) := by
  have hmap : (Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))).map
      (MonoidHom.fst (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) = ⊤ := by
    rw [MonoidHom.map_closure]
    rw [show (MonoidHom.fst (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) ''
        ({(x₁, x₂), (y₁, y₂)} : Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))
        = ({x₁, y₁} : Set (Equiv.Perm (Fin m))) by simp [Set.image_pair]]
    exact h
  have hmem : σ ∈ (Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))).map
      (MonoidHom.fst (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) := by
    rw [hmap]; trivial
  obtain ⟨z, hz, hz1⟩ := hmem
  refine ⟨z.2, ?_⟩
  have hz1' : z.1 = σ := hz1
  rw [← hz1']
  simpa using hz

theorem closure_pair_surj_snd {x₁ y₁ : Equiv.Perm (Fin m)} {x₂ y₂ : Equiv.Perm (Fin n)}
    (h : Subgroup.closure ({x₂, y₂} : Set (Equiv.Perm (Fin n))) = ⊤)
    (τ : Equiv.Perm (Fin n)) :
    ∃ σ, (σ, τ) ∈ Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) := by
  have hmap : (Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))).map
      (MonoidHom.snd (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) = ⊤ := by
    rw [MonoidHom.map_closure]
    rw [show (MonoidHom.snd (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) ''
        ({(x₁, x₂), (y₁, y₂)} : Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))
        = ({x₂, y₂} : Set (Equiv.Perm (Fin n))) by simp [Set.image_pair]]
    exact h
  have hmem : τ ∈ (Subgroup.closure ({(x₁, x₂), (y₁, y₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)))).map
      (MonoidHom.snd (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))) := by
    rw [hmap]; trivial
  obtain ⟨z, hz, hz1⟩ := hmem
  refine ⟨z.1, ?_⟩
  have hz1' : z.2 = τ := hz1
  rw [← hz1']
  simpa using hz

/-- Turning a "componentwise surjectivity" statement into the form required by
`Subgroup.normal_goursatFst`. -/
theorem surjective_fst_of {H : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))}
    (h : ∀ σ : Equiv.Perm (Fin m), ∃ τ, (σ, τ) ∈ H) :
    Function.Surjective (Prod.fst ∘ (H.subtype : H →* _)) := by
  intro σ
  obtain ⟨τ, hτ⟩ := h σ
  exact ⟨⟨(σ, τ), hτ⟩, rfl⟩

theorem surjective_snd_of {H : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))}
    (h : ∀ τ : Equiv.Perm (Fin n), ∃ σ, (σ, τ) ∈ H) :
    Function.Surjective (Prod.snd ∘ (H.subtype : H →* _)) := by
  intro τ
  obtain ⟨σ, hσ⟩ := h τ
  exact ⟨⟨(σ, τ), hσ⟩, rfl⟩

/-! ### 4.1 The unequal-degree case (Proposition 5.1) -/

theorem gamma_gen_unequal (hn1 : 1 ≤ n) (hlt : n < m) (hm5 : 5 ≤ m)
    {a₁ b₁ : Equiv.Perm (Fin m)} {a₂ b₂ : Equiv.Perm (Fin n)}
    (hsa₁ : sign a₁ = 1) (hsb₁ : sign b₁ = -1)
    (hab₁ : Subgroup.closure ({a₁, b₁} : Set (Equiv.Perm (Fin m))) = ⊤)
    (hsa₂ : sign a₂ = 1) (hsb₂ : sign b₂ = -1)
    (hab₂ : Subgroup.closure ({a₂, b₂} : Set (Equiv.Perm (Fin n))) = ⊤) :
    Subgroup.closure ({(a₁, a₂), (b₁, b₂)} :
      Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) = gammaSubgroup m n := by
  set H := Subgroup.closure ({(a₁, a₂), (b₁, b₂)} :
    Set (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) with hH
  have hle : H ≤ gammaSubgroup m n :=
    closure_pair_le_gamma (by rw [hsa₁, hsa₂]) (by rw [hsb₁, hsb₂])
  have hs1 : ∀ σ : Equiv.Perm (Fin m), ∃ τ, (σ, τ) ∈ H := closure_pair_surj_fst hab₁
  have hs2 : ∀ τ : Equiv.Perm (Fin n), ∃ σ, (σ, τ) ∈ H := closure_pair_surj_snd hab₂
  have hS1 := surjective_fst_of hs1
  have hS2 := surjective_snd_of hs2
  have : (H.goursatFst).Normal := Subgroup.normal_goursatFst hS1
  -- the first Goursat kernel is nontrivial, else `S_m` would be a quotient of `S_n`
  have hbot : H.goursatFst ≠ ⊥ := by
    intro hb
    have hker : ((MonoidHom.snd (Equiv.Perm (Fin m)) (Equiv.Perm (Fin n))).comp
        H.subtype).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : (x : Equiv.Perm (Fin m) × Equiv.Perm (Fin n)).2 = 1 := hx
      have h1 : (x : Equiv.Perm (Fin m) × Equiv.Perm (Fin n)).1 ∈ H.goursatFst := by
        rw [Subgroup.mem_goursatFst, ← hx']
        exact x.2
      rw [hb, Subgroup.mem_bot] at h1
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨by simpa using h1, by simpa using hx'⟩
    have hinj : Function.Injective ((MonoidHom.snd (Equiv.Perm (Fin m))
        (Equiv.Perm (Fin n))).comp H.subtype) := (MonoidHom.ker_eq_bot_iff _).1 hker
    have hbij : Function.Bijective ((MonoidHom.snd (Equiv.Perm (Fin m))
        (Equiv.Perm (Fin n))).comp H.subtype) := ⟨hinj, hS2⟩
    have hcard1 : Nat.card (Equiv.Perm (Fin n)) = Nat.card H :=
      (Nat.card_eq_of_bijective _ hbij).symm
    have hcard2 : Nat.card (Equiv.Perm (Fin m)) ≤ Nat.card H :=
      Nat.card_le_card_of_surjective _ hS1
    rw [← hcard1] at hcard2
    rw [Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin] at hcard2
    have hfac : Nat.factorial n < Nat.factorial m := (Nat.factorial_lt (by omega)).2 hlt
    omega
  have halt : alternatingGroup (Fin m) ≤ H.goursatFst := by
    refine Equiv.Perm.alternatingGroup_le_of_normal ?_ ((Subgroup.nontrivial_iff_ne_bot _).2 hbot)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hm5
  refine eq_gamma_left hle hs2 ?_
  intro σ hσ
  exact Subgroup.mem_goursatFst.1 (halt (Equiv.Perm.mem_alternatingGroup.2 hσ))

/-! ### 4.2 The equal-degree case (Proposition 5.3) -/

theorem gamma_gen_equal {r : ℕ} (hr5 : 5 ≤ r) {a b d : Equiv.Perm (Fin r)}
    (_hsa : sign a = 1) (hsb : sign b = -1) (hsd : sign d = -1)
    (hab : Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin r))) = ⊤)
    (had : Subgroup.closure ({a, d} : Set (Equiv.Perm (Fin r))) = ⊤)
    (hbb : b * b = 1) (hdd : d * d ≠ 1) :
    Subgroup.closure ({(a, a), (b, d)} :
      Set (Equiv.Perm (Fin r) × Equiv.Perm (Fin r))) = gammaSubgroup r r := by
  set H := Subgroup.closure ({(a, a), (b, d)} :
    Set (Equiv.Perm (Fin r) × Equiv.Perm (Fin r))) with hH
  have hle : H ≤ gammaSubgroup r r :=
    closure_pair_le_gamma rfl (by rw [hsb, hsd])
  have hs1 : ∀ σ : Equiv.Perm (Fin r), ∃ τ, (σ, τ) ∈ H := closure_pair_surj_fst hab
  have hs2 : ∀ τ : Equiv.Perm (Fin r), ∃ σ, (σ, τ) ∈ H := closure_pair_surj_snd had
  have hS2 := surjective_snd_of hs2
  have : (H.goursatSnd).Normal := Subgroup.normal_goursatSnd hS2
  -- `(b, d)² = (1, d²)` shows the second Goursat kernel is nontrivial
  have hbot : H.goursatSnd ≠ ⊥ := by
    intro hb
    have hgen : ((b, d) : Equiv.Perm (Fin r) × Equiv.Perm (Fin r)) ∈ H :=
      Subgroup.subset_closure (by simp)
    have h2 := H.mul_mem hgen hgen
    rw [show ((b, d) * (b, d) : Equiv.Perm (Fin r) × Equiv.Perm (Fin r)) = (b * b, d * d) from rfl,
      hbb] at h2
    have h3 : d * d ∈ H.goursatSnd := Subgroup.mem_goursatSnd.2 h2
    rw [hb, Subgroup.mem_bot] at h3
    exact hdd h3
  have halt : alternatingGroup (Fin r) ≤ H.goursatSnd := by
    refine Equiv.Perm.alternatingGroup_le_of_normal ?_ ((Subgroup.nontrivial_iff_ne_bot _).2 hbot)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hr5
  refine eq_gamma_right hle hs1 ?_
  intro τ hτ
  exact Subgroup.mem_goursatSnd.1 (halt (Equiv.Perm.mem_alternatingGroup.2 hτ))

/-! ### 4.3 Degree 2 on the right: `A_2` is trivial -/

theorem alt_fin_two (τ : Equiv.Perm (Fin 2)) (hτ : sign τ = 1) : τ = 1 := by
  revert hτ
  revert τ
  decide

/-! ## 5. Main theorem -/

/--
**Conjecture 1 (Fernandes, 2026).**
Let `m ≥ n ≥ 2` with `(m, n) ∉ {(2,2), (3,3), (4,3), (4,4)}`.  Then `Γ_{m ⊕ n}` is
generated by two elements.
-/
theorem conjecture_1 {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m)
    (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤ := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or] at h_except
  obtain ⟨aM, bM, dM, hsaM, hsbM, hsdM, habM, hadM, hbbM, hddM⟩ := exists_gens M
  obtain ⟨aN, bN, dN, hsaN, hsbN, hsdN, habN, hadN, hbbN, hddN⟩ := exists_gens N
  rcases eq_or_lt_of_le hmn with heq | hlt
  · -- equal degrees: `M = N ≥ 3`, i.e. degree `≥ 5`
    have hMN : M = N := by omega
    subst hMN
    have hM3 : 3 ≤ M := by omega
    have hgen := gamma_gen_equal (r := M + 2) (by omega) hsaM hsbM hsdM habM hadM hbbM
      (hddM hM3)
    exact exists_pair_of_closure_eq (mem_gammaSubgroup.2 rfl)
      (mem_gammaSubgroup.2 (by rw [hsbM, hsdM])) hgen
  · -- unequal degrees
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · -- `n = 2`: the second component is determined by its sign
      subst hN0
      have hle : Subgroup.closure ({(aM, aN), (bM, bN)} :
          Set (Equiv.Perm (Fin (M + 2)) × Equiv.Perm (Fin (0 + 2)))) ≤
          gammaSubgroup (M + 2) (0 + 2) :=
        closure_pair_le_gamma (by rw [hsaM, hsaN]) (by rw [hsbM, hsbN])
      have hgen : Subgroup.closure ({(aM, aN), (bM, bN)} :
          Set (Equiv.Perm (Fin (M + 2)) × Equiv.Perm (Fin (0 + 2)))) =
          gammaSubgroup (M + 2) (0 + 2) := by
        refine eq_gamma_right hle (closure_pair_surj_fst habM) ?_
        intro τ hτ
        have : τ = 1 := alt_fin_two τ hτ
        subst this
        exact one_mem _
      exact exists_pair_of_closure_eq (mem_gammaSubgroup.2 (by rw [hsaM, hsaN]))
        (mem_gammaSubgroup.2 (by rw [hsbM, hsbN])) hgen
    · -- `n ≥ 3`, hence `m ≥ 5` since `(4,3)` is excluded
      have hM3 : 3 ≤ M := by omega
      have hgen := gamma_gen_unequal (m := M + 2) (n := N + 2) (by omega) (by omega) (by omega)
        hsaM hsbM habM hsaN hsbN habN
      exact exists_pair_of_closure_eq (mem_gammaSubgroup.2 (by rw [hsaM, hsaN]))
        (mem_gammaSubgroup.2 (by rw [hsbM, hsbN])) hgen

/-! ## 6. The first exceptional variant: `Γ_{2 ⊕ 2} ≅ C₂` is cyclic -/

/--
It is known that `Γ_{2 ⊕ 2} ≅ C₂` has rank `1`: it is cyclic, generated by a single element.
-/
theorem conjecture_1.variants.rank_2_2 :
    ∃ g : gammaSubgroup 2 2, Subgroup.closure {g} = ⊤ := by
  have hmem : ((Equiv.swap (0 : Fin 2) 1, Equiv.swap (0 : Fin 2) 1) :
      Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) ∈ gammaSubgroup 2 2 := mem_gammaSubgroup.2 rfl
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨⟨σ, τ⟩, hz⟩ -
  rw [mem_gammaSubgroup] at hz
  have hz' : sign σ = sign τ := hz
  rcases (by decide : ∀ s : Equiv.Perm (Fin 2), s = 1 ∨ s = Equiv.swap 0 1) σ with rfl | rfl
  · have hτ : τ = 1 := alt_fin_two τ (by rw [← hz', map_one])
    subst hτ
    exact Subgroup.one_mem _
  · have hτ : τ = Equiv.swap 0 1 :=
      (by decide : ∀ s : Equiv.Perm (Fin 2), sign s = -1 → s = Equiv.swap 0 1) τ
        (by rw [← hz']; decide)
    subst hτ
    exact Subgroup.subset_closure rfl

/-! ## 7. Sanity checks: the hypotheses are satisfiable and the statement has content -/

-- an unequal-degree instance
example : ∃ g₁ g₂ : gammaSubgroup 5 3, Subgroup.closure {g₁, g₂} = ⊤ :=
  conjecture_1 (by norm_num) (by norm_num) (by norm_num) (by simp)

-- an equal-degree instance
example : ∃ g₁ g₂ : gammaSubgroup 7 7, Subgroup.closure {g₁, g₂} = ⊤ :=
  conjecture_1 (by norm_num) (by norm_num) (by norm_num) (by simp)

-- a degree-2 instance
example : ∃ g₁ g₂ : gammaSubgroup 6 2, Subgroup.closure {g₁, g₂} = ⊤ :=
  conjecture_1 (by norm_num) (by norm_num) (by norm_num) (by simp)

-- `Γ_{5 ⊕ 3}` really is a proper subgroup of `S₅ × S₃`, so the statement is not vacuous
example : gammaSubgroup 5 3 ≠ ⊤ := by
  intro h
  have hmem : ((Equiv.swap 0 1, 1) : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) ∈
      gammaSubgroup 5 3 := by rw [h]; trivial
  rw [mem_gammaSubgroup] at hmem
  have h2 : sign (Equiv.swap (0 : Fin 5) 1) = sign (1 : Equiv.Perm (Fin 3)) := hmem
  rw [Equiv.Perm.sign_swap (by decide), map_one] at h2
  exact absurd h2 (by decide)

end Fernandes

#print axioms Fernandes.conjecture_1
#print axioms Fernandes.gamma_gen_unequal
#print axioms Fernandes.gamma_gen_equal
#print axioms Fernandes.exists_gens
#print axioms Fernandes.conjecture_1.variants.rank_2_2
