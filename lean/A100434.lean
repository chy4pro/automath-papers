import Mathlib.Tactic

/-!
# OEIS A100434 — Corrected Dement identities

This file proves three identities relating auxiliary integer sequences built from the
linear recurrence `x(n+4) = -6 * x(n+2) - x(n)`, following OEIS A100434.

The auxiliary sequence `b` used here uses the *corrected* definition
`b n = if n % 2 = 0 then -c (n + 1) else c (n - 1)` (note the minus sign on the even
branch). The `formal-conjectures` repository version of this file omits that minus sign,
which makes the resulting `conjecture1` false at `n = 0` (there, `c 0 + d 0 = 3` but
`c 1 = -3`, so `c 0 + d 0 ≠ c 1`). With the corrected sign, all three identities hold.
-/

namespace OeisA100434Corrected

/-- The primary defining sequence `a`, which is the expansion of the generating function
$(1+x)(3+x)/(1+6x^2+x^4)$. It satisfies the recurrence $a(n) = -6 a(n-2) - a(n-4)$
for $n \ge 4$. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

/-- $c(n)$ starts with $(1, -3, -7, 17)$ and satisfies the same recurrence as `a` -/
def c : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => -7
  | 3 => 17
  | n + 4 => -6 * c (n + 2) - c n

/-- $d(n)$ starts with $(2, 4, -10, -24)$ and satisfies the same recurrence as `a` -/
def d : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => -10
  | 3 => -24
  | n + 4 => -6 * d (n + 2) - d n

/-- $b(2n) = -c(2n+1)$, $b(2n+1) = c(2n)$. This is the corrected definition, with a minus
sign on the even branch. -/
def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then -c (n + 1) else c (n - 1)

/-- $e(2n) = d(2n)/2$, $e(2n+1) = -d(2n)/2$ -/
def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then d n / 2
  else -(d (n - 1) / 2)

/-- $f(2n) = f(2n+1) = d(2n+1)/2$ -/
def f (n : ℕ) : ℤ :=
  d (2 * (n / 2) + 1) / 2

/-- $g(2n) = 0, g(2n+1) = c(2n+1)$ -/
def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0 else c n

/-! ## Basic value sanity checks -/

example : a 0 = 3 := rfl
example : a 4 = 99 := rfl
example : c 4 = 41 := rfl
example : d 4 = 58 := rfl

/-! ## Auxiliary induction lemmas -/

/-- For all $k$, $a(2k) = -c(2k+1)$. (Same statement/proof pattern as the `formal-conjectures`
repo's `a_even`.) -/
theorem a_even (k : ℕ) : a (2 * k) = -c (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) = 2 * k + 4 := by omega
    have h2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h2, h1]
    have h_lhs : a (2 * k + 4) = -6 * a (2 * k + 2) - a (2 * k) := rfl
    have h_rhs : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 2) = -c (2 * k + 3) := by
      have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
      have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e2, e1] at ih2
      exact ih2
    rw [ih1, ih2']
    ring

/-- For all $k$, $a(2k+1) = d(2k+1)$. -/
theorem a_odd (k : ℕ) : a (2 * k + 1) = d (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h1]
    have h_lhs : a (2 * k + 5) = -6 * a (2 * k + 3) - a (2 * k + 1) := rfl
    have h_rhs : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 3) = d (2 * k + 3) := by
      have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e1] at ih2
      exact ih2
    rw [ih1, ih2']

/-- For all $k$, $c(2k) + d(2k) = -c(2k+1)$. -/
theorem c_d_even (k : ℕ) : c (2 * k) + d (2 * k) = -c (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) = 2 * k + 4 := by omega
    have h2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h2, h1]
    have hc : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    have hd : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    rw [hc, hd, hc5]
    have ih2' : c (2 * k + 2) + d (2 * k + 2) = -c (2 * k + 3) := by
      have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
      have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e2, e1] at ih2
      exact ih2
    linarith [ih1, ih2']

/-- For all $k$, $c(2k+1) + d(2k+1) = c(2k)$. -/
theorem c_d_odd (k : ℕ) : c (2 * k + 1) + d (2 * k + 1) = c (2 * k) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h2 : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h1, h2]
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    have hd5 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    rw [hc5, hd5, hc4]
    have ih2' : c (2 * k + 3) + d (2 * k + 3) = c (2 * k + 2) := by
      have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have e2 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [e1, e2] at ih2
      exact ih2
    linarith [ih1, ih2']

/-- For all $k$, `2 ∣ d (2 * k)`. -/
theorem d_even_even (k : ℕ) : (2 : ℤ) ∣ d (2 * k) := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨1, rfl⟩
  | one => exact ⟨-5, rfl⟩
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h1]
    have hd : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    rw [hd]
    obtain ⟨m1, hm1⟩ := ih1
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2] at ih2
    obtain ⟨m2, hm2⟩ := ih2
    exact ⟨-6 * m2 - m1, by rw [hm1, hm2]; ring⟩

/-- For all $k$, `2 ∣ d (2 * k + 1)`. -/
theorem d_odd_even (k : ℕ) : (2 : ℤ) ∣ d (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨2, rfl⟩
  | one => exact ⟨-12, rfl⟩
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h1]
    have hd : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    rw [hd]
    obtain ⟨m1, hm1⟩ := ih1
    have h2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [h2] at ih2
    obtain ⟨m2, hm2⟩ := ih2
    exact ⟨-6 * m2 - m1, by rw [hm1, hm2]; ring⟩

/-- For all $k$, $d(2k) + d(2k+1) = -2 c(2k+1)$. -/
theorem d_sum_even (k : ℕ) : d (2 * k) + d (2 * k + 1) = -2 * c (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) = 2 * k + 4 := by omega
    have h2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h2, h1]
    have hd4 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    have hd5 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    rw [hd4, hd5, hc5]
    have ih2' : d (2 * k + 2) + d (2 * k + 3) = -2 * c (2 * k + 3) := by
      have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
      have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e2, e1] at ih2
      exact ih2
    linarith [ih1, ih2']

/-- For all $k$, $d(2k+1) - d(2k) = 2 c(2k)$. -/
theorem d_diff (k : ℕ) : d (2 * k + 1) - d (2 * k) = 2 * c (2 * k) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h2 : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h1, h2]
    have hd5 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hd4 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    rw [hd5, hd4, hc4]
    have ih2' : d (2 * k + 3) - d (2 * k + 2) = 2 * c (2 * k + 2) := by
      have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have e2 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [e1, e2] at ih2
      exact ih2
    linarith [ih1, ih2']

/-! ## Main theorems -/

/-- **Conjecture from Creighton Dement (A100434)**, corrected version:
For all $n \ge 0$, $c(n) + d(n) = b(n)$. -/
theorem conjecture1 (n : ℕ) : c n + d n = b n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul k]
    have hmod : (2 * k) % 2 = 0 := by omega
    unfold b
    rw [ite_eq_left hmod]
    exact c_d_even k
  · have hmod : ¬ (2 * k + 1) % 2 = 0 := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    unfold b
    rw [ite_eq_right hmod, hsub]
    exact c_d_odd k

/-- **Conjecture from Creighton Dement (A100434)**, corrected version:
For all $n \ge 0$, $e(n) + f(n) = b(n)$. -/
theorem conjecture2 (n : ℕ) : e n + f n = b n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul k]
    have hmod : (2 * k) % 2 = 0 := by omega
    have hdiv : (2 * k) / 2 = k := by omega
    have hd1 : (2 : ℤ) ∣ d (2 * k) := d_even_even k
    have hd2 : (2 : ℤ) ∣ d (2 * k + 1) := d_odd_even k
    have hsum : d (2 * k) + d (2 * k + 1) = -2 * c (2 * k + 1) := d_sum_even k
    unfold e f b
    rw [ite_eq_left hmod, ite_eq_left hmod, hdiv]
    omega
  · have hmod : ¬ (2 * k + 1) % 2 = 0 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    have hd1 : (2 : ℤ) ∣ d (2 * k) := d_even_even k
    have hd2 : (2 : ℤ) ∣ d (2 * k + 1) := d_odd_even k
    have hdiff : d (2 * k + 1) - d (2 * k) = 2 * c (2 * k) := d_diff k
    unfold e f b
    rw [ite_eq_right hmod, ite_eq_right hmod, hdiv, hsub]
    omega

/-- **Conjecture from Creighton Dement (A100434)**, corrected version:
For all $n \ge 0$, $g(n) + a(n) = b(n)$. -/
theorem conjecture3 (n : ℕ) : g n + a n = b n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul k]
    have hmod : (2 * k) % 2 = 0 := by omega
    unfold g b
    rw [ite_eq_left hmod, ite_eq_left hmod]
    rw [a_even k]
    ring
  · have hmod : ¬ (2 * k + 1) % 2 = 0 := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    unfold g b
    rw [ite_eq_right hmod, ite_eq_right hmod, hsub]
    rw [a_odd k]
    exact c_d_odd k

end OeisA100434Corrected

#print axioms OeisA100434Corrected.conjecture1
#print axioms OeisA100434Corrected.conjecture2
#print axioms OeisA100434Corrected.conjecture3
