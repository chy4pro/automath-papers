/-
OEIS A108211 : for every n ≥ 1,

    ⌊ 1 / ( 1/(4n) - log 2 + ∑_{k=n+1}^{2n} 1/k ) ⌋ = 16 n² + 1.

Formalization of the informal proof `notes/proofs/A108211_proof_v2.md`.

Structure.
* `ffun m = 1/((2m+1)(2m+2))` is the paired alternating harmonic term.  Its
  partial sums are `H_{2n} - H_n = ∑_{k=n+1}^{2n} 1/k`, and they converge to
  `log 2` (squeezed between `log(2n+1) - log(n+1)` and `log 2`).
* `T n = ∑' m, ffun (m+n) = log 2 - ∑_{k=n+1}^{2n} 1/k`.
* A telescoping certificate `hf` with defect `Δ` bounded by
  `gf m - gf (m+1)`, `gf x = 60/(4x+1)^7`, gives `hf n ≤ T n ≤ hf n + gf n`.
* Two polynomial certificates place that window strictly inside
  `(1/(4n) - 1/(16n²+1), 1/(4n) - 1/(16n²+2))`, which pins the floor.

All polynomial inequalities are proved from all-nonnegative shifted
coefficient certificates (substitution `x = 1 + t`, `t ≥ 0`).
-/
import Mathlib

open Finset Filter
open scoped Topology

set_option maxHeartbeats 2000000

namespace A108211

noncomputable section

/-! ### The certificate functions -/

/-- Numerator of the telescoping certificate. -/
def Apoly (x : ℝ) : ℝ :=
  1024 * x ^ 5 + 5888 * x ^ 4 + 12928 * x ^ 3 + 13312 * x ^ 2 + 6148 * x + 843

/-- Telescoping certificate `h`. -/
def hf (x : ℝ) : ℝ :=
  Apoly x / (4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7))

/-- Majorant certificate `g`. -/
def gf (x : ℝ) : ℝ := 60 / (4 * x + 1) ^ 7

/-- The summand, as a function of a real variable. -/
def ff (x : ℝ) : ℝ := 1 / ((2 * x + 1) * (2 * x + 2))

/-- The summand, as a function of a natural number. -/
def ffun (m : ℕ) : ℝ := 1 / ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2))

/-! ### Polynomial certificates -/

/-- Certificate C3 : `h - f₁ > 0`. -/
theorem cert5 (x : ℝ) (hx : 1 ≤ x) :
    (16 * x ^ 2 - 4 * x + 1) *
        (4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7))
      < Apoly x * (4 * x * (16 * x ^ 2 + 1)) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5]

/-- Certificate C4 : `f₂ - h - g > 0`. -/
theorem cert6 (x : ℝ) (hx : 1 ≤ x) :
    (Apoly x * (4 * x + 1) ^ 6 +
        240 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) *
        (4 * x * (8 * x ^ 2 + 1))
      < (8 * x ^ 2 - 2 * x + 1) *
        (4 * (4 * x + 1) ^ 7 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

/-- Certificate C2 : `Δ(x) + g(x+1) ≤ g(x)`, cleared of denominators. -/
theorem cert2 (x : ℝ) (hx : 1 ≤ x) :
    (126 * (16 * x ^ 2 + 120 * x + 119) * (4 * x + 5) ^ 7 +
        4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) * 60) * (4 * x + 1) ^ 7
      ≤ 60 * (4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) * (4 * x + 5) ^ 7) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10,
    pow_nonneg ht 11, pow_nonneg ht 12, pow_nonneg ht 13, pow_nonneg ht 14, pow_nonneg ht 15,
    pow_nonneg ht 16]

/-- Decay certificate : `x * A(x) ≤ denominator`, i.e. `hf x ≤ 1/x`. -/
theorem cert7 (x : ℝ) (hx : 1 ≤ x) :
    x * Apoly x
      ≤ 4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6]

/-! ### The defect identity (Lemma 1) -/

/-- `Δ(x) = ff x - (hf x - hf (x+1))` in closed form. -/
theorem delta_eq (x : ℝ) (hx : 0 ≤ x) :
    ff x - (hf x - hf (x + 1))
      = 126 * (16 * x ^ 2 + 120 * x + 119) /
        (4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11))) := by
  have h1 : (4 * x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h2 : (2 * x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h3 : (4 * x + 3 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h4 : (4 * x + 5 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h5 : (2 * x + 3 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h6 : (4 * x + 7 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h7 : (4 * x + 9 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h8 : (2 * x + 5 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h9 : (4 * x + 11 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h10 : (x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h11 : (2 * x + 2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  simp only [ff, hf, Apoly]
  field_simp
  ring

theorem delta_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ ff x - (hf x - hf (x + 1)) := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have h7 : (0:ℝ) < 4 * x + 9 := by linarith
  have h8 : (0:ℝ) < 2 * x + 5 := by linarith
  have h9 : (0:ℝ) < 4 * x + 11 := by linarith
  have h10 : (0:ℝ) < x + 1 := by linarith
  rw [delta_eq x hx]
  positivity

theorem delta_le (x : ℝ) (hx : 1 ≤ x) :
    ff x - (hf x - hf (x + 1)) ≤ gf x - gf (x + 1) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have h7 : (0:ℝ) < 4 * x + 9 := by linarith
  have h8 : (0:ℝ) < 2 * x + 5 := by linarith
  have h9 : (0:ℝ) < 4 * x + 11 := by linarith
  have h10 : (0:ℝ) < x + 1 := by linarith
  have hDd : (0:ℝ) < 4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
      ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
      ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) := by positivity
  have he : (4:ℝ) * (x + 1) + 1 = 4 * x + 5 := by ring
  rw [delta_eq x hx0]
  simp only [gf, he]
  rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt hDd) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [cert2 x hx]

/-! ### Elementary bounds on `hf` and `gf` -/

theorem hf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ hf x := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  simp only [hf, Apoly]
  positivity

theorem gf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ gf x := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  simp only [gf]
  positivity

theorem hf_le_inv (x : ℝ) (hx : 1 ≤ x) : hf x ≤ 1 / x := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  simp only [hf]
  rw [div_le_div_iff₀ (by positivity) hx0]
  linarith [cert7 x hx]

/-! ### The window inequalities (Lemmas 4 and 5) -/

theorem window_low (x : ℝ) (hx : 1 ≤ x) : (4 * x)⁻¹ - (16 * x ^ 2 + 1)⁻¹ < hf x := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have hq : (0:ℝ) < 16 * x ^ 2 + 1 := by positivity
  have e : (4 * x)⁻¹ - (16 * x ^ 2 + 1)⁻¹
      = (16 * x ^ 2 - 4 * x + 1) / (4 * x * (16 * x ^ 2 + 1)) := by
    field_simp
    ring
  rw [e]
  simp only [hf]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith [cert5 x hx]

theorem window_high (x : ℝ) (hx : 1 ≤ x) :
    hf x + gf x < (4 * x)⁻¹ - (16 * x ^ 2 + 2)⁻¹ := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have e2 : (4 * x)⁻¹ - (16 * x ^ 2 + 2)⁻¹
      = (8 * x ^ 2 - 2 * x + 1) / (4 * x * (8 * x ^ 2 + 1)) := by
    field_simp
    ring
  have e3 : hf x + gf x
      = (Apoly x * (4 * x + 1) ^ 6 +
          240 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) /
        (4 * (4 * x + 1) ^ 7 *
          ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) := by
    simp only [hf, gf]
    field_simp
    ring
  rw [e2, e3, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith [cert6 x hx]

/-! ### The harmonic partial sums and `log 2` -/

/-- `Hh N = H_N`, the `N`-th harmonic number. -/
def Hh (N : ℕ) : ℝ := ∑ i ∈ range N, ((i : ℝ) + 1)⁻¹

theorem Hh_succ (N : ℕ) : Hh (N + 1) = Hh N + ((N : ℝ) + 1)⁻¹ := by
  simp only [Hh, Finset.sum_range_succ]

theorem Hh_diff (n : ℕ) : Hh (2 * n) - Hh n = ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
  have h : n ≤ 2 * n := by omega
  simp only [Hh]
  rw [← Finset.sum_Ico_eq_sub _ h, Finset.sum_Ico_eq_sum_range]
  rw [show 2 * n - n = n by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

theorem ffun_nonneg (m : ℕ) : 0 ≤ ffun m := by
  simp only [ffun]
  positivity

theorem sum_ffun (n : ℕ) : ∑ m ∈ range n, ffun m = Hh (2 * n) - Hh n := by
  induction n with
  | zero => simp [Hh]
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [Finset.sum_range_succ, ih, e]
    simp only [Hh, Finset.sum_range_succ, ffun]
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem harm_upper (n : ℕ) (hn : 1 ≤ n) : Hh (2 * n) - Hh n ≤ Real.log 2 := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : ((n : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  rw [Hh_diff]
  set g : ℕ → ℝ := fun j => Real.log ((n : ℝ) + (j : ℝ)) with hg
  have key : ∀ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ ≤ g (i + 1) - g i := by
    intro i _
    have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have ha : (1:ℝ) ≤ (n : ℝ) + (i : ℝ) := by linarith
    have hb : (0:ℝ) < (n : ℝ) + (i : ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < ((n : ℝ) + (i : ℝ)) / ((n : ℝ) + (i : ℝ) + 1) :=
      div_pos (by linarith) hb
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have e : ((n : ℝ) + (i : ℝ)) / ((n : ℝ) + (i : ℝ) + 1) - 1 = -(((n : ℝ) + (i : ℝ) + 1)⁻¹) := by
      field_simp
      ring
    rw [e] at hlog
    have hgi : g (i + 1) = Real.log ((n : ℝ) + (i : ℝ) + 1) := by
      simp only [hg]
      congr 1
      push_cast
      ring
    rw [hgi]
    simp only [hg]
    linarith
  calc ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹
      ≤ ∑ i ∈ range n, (g (i + 1) - g i) := Finset.sum_le_sum key
    _ = g n - g 0 := Finset.sum_range_sub g n
    _ = Real.log 2 := by
        simp only [hg, Nat.cast_zero, add_zero]
        rw [show (n : ℝ) + (n : ℝ) = 2 * (n : ℝ) by ring, Real.log_mul two_ne_zero hn0]
        ring

theorem harm_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1) ≤ Hh (2 * n) - Hh n := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Hh_diff]
  set g : ℕ → ℝ := fun j => Real.log ((n : ℝ) + (j : ℝ) + 1) with hg
  have key : ∀ i ∈ range n, g (i + 1) - g i ≤ ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
    intro i _
    have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hb : (0:ℝ) < (n : ℝ) + (i : ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < ((n : ℝ) + (i : ℝ) + 2) / ((n : ℝ) + (i : ℝ) + 1) :=
      div_pos (by linarith) hb
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have e : ((n : ℝ) + (i : ℝ) + 2) / ((n : ℝ) + (i : ℝ) + 1) - 1 = ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
      field_simp
      ring
    rw [e] at hlog
    have hgi : g (i + 1) = Real.log ((n : ℝ) + (i : ℝ) + 2) := by
      simp only [hg]
      congr 1
      push_cast
      ring
    rw [hgi]
    simp only [hg]
    linarith
  calc Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)
      = g n - g 0 := by
        simp only [hg, Nat.cast_zero, add_zero]
        rw [show (n : ℝ) + (n : ℝ) + 1 = 2 * (n : ℝ) + 1 by ring]
    _ = ∑ i ∈ range n, (g (i + 1) - g i) := (Finset.sum_range_sub g n).symm
    _ ≤ ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ := Finset.sum_le_sum key

theorem tendsto_lower :
    Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 (Real.log 2)) := by
  have h1 : ∀ n : ℕ, Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)
      = Real.log ((2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.log_div (by positivity) (by positivity)]
  have h2 : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 2) := by
    have he : ∀ n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) = 2 - 1 / ((n : ℝ) + 1) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [tendsto_congr he]
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.sub this
  simp_rw [h1]
  exact h2.log two_ne_zero

theorem tendsto_partial :
    Tendsto (fun n : ℕ => Hh (2 * n) - Hh n) atTop (𝓝 (Real.log 2)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_lower tendsto_const_nhds
    (eventually_atTop.2 ⟨1, fun n hn => harm_lower n hn⟩)
    (eventually_atTop.2 ⟨1, fun n hn => harm_upper n hn⟩)

theorem summable_ffun : Summable ffun := by
  refine summable_of_sum_range_le (c := Real.log 2) ffun_nonneg fun n => ?_
  rw [sum_ffun]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Hh, Nat.mul_zero, sub_self]
    exact Real.log_nonneg (by norm_num)
  · exact harm_upper n hn

theorem hasSum_ffun : HasSum ffun (Real.log 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg ffun_nonneg]
  simpa only [sum_ffun] using tendsto_partial

/-! ### The tail `T` -/

/-- The tail of the paired alternating harmonic series. -/
def T (n : ℕ) : ℝ := ∑' m : ℕ, ffun (m + n)

theorem T_eq (n : ℕ) : Real.log 2 - (Hh (2 * n) - Hh n) = T n := by
  have h := summable_ffun.sum_add_tsum_nat_add n
  rw [hasSum_ffun.tsum_eq, sum_ffun] at h
  simp only [T]
  linarith

theorem Icc_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹ = Hh (2 * n) - Hh n := by
  have e : Finset.Icc (n + 1) (2 * n) = Finset.Ico (n + 1) (2 * n + 1) := by
    ext k
    simp
  rw [e, Finset.sum_Ico_eq_sum_range, Hh_diff, show 2 * n + 1 - (n + 1) = n by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/-! ### The sandwich (Lemma 3) -/

theorem T_bounds (n : ℕ) (hn : 1 ≤ n) :
    hf (n : ℝ) ≤ T n ∧ T n ≤ hf (n : ℝ) + gf (n : ℝ) := by
  have hx1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxm : ∀ m : ℕ, (1:ℝ) ≤ (n : ℝ) + (m : ℝ) := by
    intro m
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  set F : ℕ → ℝ := fun m => hf ((n : ℝ) + (m : ℝ)) with hF
  set G : ℕ → ℝ := fun m => gf ((n : ℝ) + (m : ℝ)) with hG
  have hFs : ∀ m : ℕ, F (m + 1) = hf ((n : ℝ) + (m : ℝ) + 1) := by
    intro m
    simp only [hF]
    congr 1
    push_cast
    ring
  have hGs : ∀ m : ℕ, G (m + 1) = gf ((n : ℝ) + (m : ℝ) + 1) := by
    intro m
    simp only [hG]
    congr 1
    push_cast
    ring
  have hffe : ∀ m : ℕ, ffun (m + n) = ff ((n : ℝ) + (m : ℝ)) := by
    intro m
    simp only [ffun, ff]
    push_cast
    ring_nf
  have hsum : Summable (fun m : ℕ => ffun (m + n)) := (summable_nat_add_iff n).2 summable_ffun
  have hP : Tendsto (fun N : ℕ => ∑ m ∈ range N, ffun (m + n)) atTop (𝓝 (T n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hF0 : F 0 = hf (n : ℝ) := by simp [hF]
  have hG0 : G 0 = gf (n : ℝ) := by simp [hG]
  -- lower estimate on partial sums
  have hlow : ∀ N : ℕ, F 0 - F N ≤ ∑ m ∈ range N, ffun (m + n) := by
    intro N
    rw [← Finset.sum_range_sub' F N]
    refine Finset.sum_le_sum fun m _ => ?_
    have := delta_nonneg ((n : ℝ) + (m : ℝ)) (by linarith [hxm m])
    rw [hFs m, hffe m]
    linarith
  -- upper estimate on partial sums
  have hup : ∀ N : ℕ, ∑ m ∈ range N, ffun (m + n) ≤ (F 0 - F N) + (G 0 - G N) := by
    intro N
    rw [← Finset.sum_range_sub' F N, ← Finset.sum_range_sub' G N, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    have := delta_le ((n : ℝ) + (m : ℝ)) (hxm m)
    rw [hFs m, hGs m, hffe m]
    linarith
  -- `F N → 0`
  have hFtend : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero (f := F) (g := fun N : ℕ => 1 / ((N : ℝ) + 1))
      (fun N => hf_nonneg _ (by linarith [hxm N])) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : hf ((n : ℝ) + (N : ℝ)) ≤ 1 / ((n : ℝ) + (N : ℝ)) := hf_le_inv _ (hxm N)
    have h2 : (1:ℝ) / ((n : ℝ) + (N : ℝ)) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    simp only [hF]
    linarith
  constructor
  · have hA : Tendsto (fun N : ℕ => F 0 - F N) atTop (𝓝 (F 0 - 0)) :=
      tendsto_const_nhds.sub hFtend
    rw [sub_zero] at hA
    rw [← hF0]
    exact le_of_tendsto_of_tendsto' hA hP hlow
  · rw [← hF0, ← hG0]
    refine le_of_tendsto' hP fun N => ?_
    have h1 : 0 ≤ F N := hf_nonneg _ (by linarith [hxm N])
    have h2 : 0 ≤ G N := gf_nonneg _ (by linarith [hxm N])
    linarith [hup N]

end

end A108211

/-! ### Main theorem -/

open A108211 in
theorem a108211 (n : ℕ) (hn : 0 < n) :
    (16 * (n : ℤ) ^ 2 + 1 : ℤ) =
      ⌊ 1 / ((4 * (n : ℝ))⁻¹ - Real.log 2 +
        ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹) ⌋ := by
  have hn1 : 1 ≤ n := hn
  have hx1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : (0:ℝ) < (n : ℝ) := by linarith
  have hDeq : (4 * (n : ℝ))⁻¹ - Real.log 2 + ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹
      = (4 * (n : ℝ))⁻¹ - T n := by
    rw [Icc_sum n]
    have := T_eq n
    linarith
  rw [hDeq]
  obtain ⟨hTl, hTu⟩ := T_bounds n hn1
  have hw1 := window_low (n : ℝ) hx1
  have hw2 := window_high (n : ℝ) hx1
  have hp1 : (0:ℝ) < 16 * (n : ℝ) ^ 2 + 1 := by positivity
  have hp2 : (0:ℝ) < 16 * (n : ℝ) ^ 2 + 2 := by positivity
  set D : ℝ := (4 * (n : ℝ))⁻¹ - T n with hD
  have hlow : (16 * (n : ℝ) ^ 2 + 2)⁻¹ < D := by rw [hD]; linarith
  have hhigh : D < (16 * (n : ℝ) ^ 2 + 1)⁻¹ := by rw [hD]; linarith
  have hDpos : 0 < D := lt_trans (by positivity) hlow
  have hA : (16 * (n : ℝ) ^ 2 + 1) * D < 1 := by
    have h := mul_lt_mul_of_pos_left hhigh hp1
    rwa [mul_inv_cancel₀ (ne_of_gt hp1)] at h
  have hB : 1 < (16 * (n : ℝ) ^ 2 + 2) * D := by
    have h := mul_lt_mul_of_pos_left hlow hp2
    rwa [mul_inv_cancel₀ (ne_of_gt hp2)] at h
  symm
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    rw [le_div_iff₀ hDpos]
    linarith
  · push_cast
    rw [div_lt_iff₀ hDpos]
    linarith

#print axioms a108211
