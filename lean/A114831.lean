import Mathlib

/-!
# OEIS A114831

We formalize the following limit theorem. Define `a : ℕ → ℕ` by `a 1 = 1`, `a 2 = 2`, and for
`n ≥ 3`,
```
a (n+1) = a n + ⌊ 2 * a n * a (n-1) / (a n + a (n-1)) ⌋
```
i.e. each new term is the previous term plus the floor of the harmonic mean of the two
preceding terms (`a 0` is an unused dummy value; natural number division `/` on `ℕ` already
*is* this floor). We prove that the ratio of consecutive terms converges to `√3`:
```
a (n+1) / a n → √3.
```

## Proof outline

* `a_pos_pair` / `a_pos1`: `a` is positive from index 1 onward.
* `harmonic_ge_one`, `step_ge_one`, `D`: the recursive increment `a (n+1) - a n` is always
  `≥ 1` (this uses `2xy ≥ x + y` for naturals `x, y ≥ 1`), hence `a` is (weakly) increasing
  from index 1 on and `a (n+1) ≥ n + 1` (`a_ge_index`), which we later use to make the
  `1 / a n` error terms tend to `0`.
* `R n := a (n+1) / a n` (as a real number) and `F x := 1 + 2 / (x + 1)`.
* `ratio_rec`: the *exact* two-sided bound coming directly from how natural number division
  truncates: for `k ≥ 0`, `F (R (k+1)) - 1/a(k+2) < R (k+2) ≤ F (R (k+1))`, obtained by
  casting the Euclidean division identity `p = m * (p / m) + p % m` (with `m = a(k+2)+a(k+1)`,
  `p = 2 * a(k+2) * a(k+1)`) defining `a (k+3)` to `ℝ`.
* `F_fixed`: `√3` is a fixed point of `F`, since `(√3 - 1)(√3 + 1) = 2`.
* `F_lipschitz`: `F` is `1/2`-Lipschitz on `[1, ∞)`.
* `e_rec`: writing `e n := |R n - √3|`, the above facts combine (triangle inequality) into
  the contraction-with-forcing-term recursion `e (k+2) ≤ e (k+1) / 2 + 1 / a (k+2)`.
* `aux_geom` / `tendsto_e_zero`: a general elementary lemma — if `e (k+1) ≤ e k / 2 + b k` for
  `k ≥ 1` and `b → 0`, then `e → 0` — proved by an explicit `ε`/`N` argument (unrolling the
  recursion `m` steps from a well-chosen starting index `N` gives
  `e (N + m) ≤ 2⁻ᵐ * e N + 2 * ε` whenever `b` is eventually `≤ ε`).
* `b_to_zero`: the forcing term `1 / a (n+1) → 0` since `a (n+1) ≥ n + 1`.
* Combining `tendsto_e_zero` with `e_rec` and `b_to_zero` gives `e → 0`, i.e. `R → √3`, and
  reindexing (`R n = a (n+1) / a n`) yields the theorem `a114831` exactly as stated.
-/

/-- The defining sequence: `a (n+3)` is `a (n+2)` plus the floor of the harmonic mean of
`a (n+2)` and `a (n+1)`, where the floor comes for free from natural number division. -/
def a : ℕ → ℕ
  | 0 => 0        -- dummy
  | 1 => 1
  | 2 => 2
  | (n+3) => a (n+2) + (2 * a (n+2) * a (n+1)) / (a (n+2) + a (n+1))

example : a 3 = 3 := by decide
example : a 4 = 5 := by decide
example : a 5 = 8 := by decide
example : a 6 = 14 := by decide

theorem a_rec (n : ℕ) :
    a (n+3) = a (n+2) + (2 * a (n+2) * a (n+1)) / (a (n+2) + a (n+1)) := rfl

/-! ## Positivity and growth of `a` -/

/-- `a` is positive from index `1` on. Stated as a pair so that the induction step is
immediate (the recursive term only adds a nonnegative quantity). -/
theorem a_pos_pair (n : ℕ) : 1 ≤ a (n+1) ∧ 1 ≤ a (n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [a_rec]
    exact le_trans ih.2 (Nat.le_add_right _ _)

theorem a_pos1 (n : ℕ) : 1 ≤ a (n+1) := (a_pos_pair n).1

/-- For naturals `x, y ≥ 1`, the harmonic mean `2xy / (x+y)` (Nat division) is `≥ 1`, since
`2xy - x - y = x(y-1) + y(x-1) ≥ 0`. -/
theorem harmonic_ge_one (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ (2*x*y)/(x+y) := by
  rw [Nat.one_le_div_iff (by omega)]
  nlinarith

/-- The recurrence always increments by at least `1`. -/
theorem step_ge_one (n : ℕ) : a (n+2) + 1 ≤ a (n+3) := by
  rw [a_rec]
  have hx := (a_pos_pair n).2
  have hy := (a_pos_pair n).1
  have := harmonic_ge_one (a (n+2)) (a (n+1)) hx hy
  omega

/-- `a` increases by at least `1` at every step from index `1` on (the `n = 0` case is the
base values `a 1 = 1`, `a 2 = 2`, and `n ≥ 1` follows from `step_ge_one`). -/
theorem D (n : ℕ) : a (n+1) + 1 ≤ a (n+2) := by
  match n with
  | 0 => decide
  | (m+1) => exact step_ge_one m

theorem a_mono (n : ℕ) : a (n+1) ≤ a (n+2) := by have := D n; omega

/-- `a (n+1) ≥ n + 1`, i.e. `a m ≥ m` for `m ≥ 1`. -/
theorem a_ge_index (n : ℕ) : n + 1 ≤ a (n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hD := D n
    show n + 2 ≤ a (n + 2)
    omega

/-! ## The ratio recursion -/

/-- The ratio of consecutive terms, as a real number. -/
noncomputable def R (n : ℕ) : ℝ := (a (n+1) : ℝ) / (a n : ℝ)

/-- The averaging map whose fixed point is `√3`. -/
noncomputable def F (x : ℝ) : ℝ := 1 + 2 / (x + 1)

theorem R_ge_one (n : ℕ) : 1 ≤ R (n+1) := by
  show 1 ≤ (a (n+2) : ℝ) / (a (n+1) : ℝ)
  have h1 : (0:ℝ) < (a (n+1) : ℝ) := by exact_mod_cast a_pos1 n
  rw [le_div_iff₀ h1]
  have hmono : a (n+1) ≤ a (n+2) := a_mono n
  have : (a (n+1):ℝ) ≤ (a (n+2):ℝ) := by exact_mod_cast hmono
  linarith

theorem F_eval (x y : ℝ) (hy : y ≠ 0) (hxy : x + y ≠ 0) : F (x/y) = 1 + 2*y/(x+y) := by
  unfold F
  field_simp

/-- The core real-number algebra behind the ratio recursion: given the Euclidean division
data `(x+y)*q + r = 2*x*y` with `0 ≤ r < x+y`, the quotient `q` produces a value `(x+q)/x`
that is sandwiched between `F(x/y) := 1 + 2y/(x+y)` and `F(x/y) - 1/x`. -/
theorem ratio_bound_core (x y q p r : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : p = 2*x*y) (hqr : (x+y)*q + r = p) (hr0 : 0 ≤ r) (hrlt : r < x + y) :
    (x+q)/x ≤ 1 + 2*y/(x+y) ∧ 1 + 2*y/(x+y) - 1/x < (x+q)/x := by
  have hxy : 0 < x + y := by linarith
  have expand : (1 + 2*y/(x+y)) - (x+q)/x
      = (x*(x+y) + 2*y*x - (x+q)*(x+y)) / (x*(x+y)) := by
    field_simp
  have expand2 : (1 + 2*y/(x+y) - 1/x) - (x+q)/x
      = ((x+y)*x + 2*y*x - (x+y) - (x+q)*(x+y)) / (x*(x+y)) := by
    field_simp
  constructor
  · have hnum : 0 ≤ x*(x+y) + 2*y*x - (x+q)*(x+y) := by nlinarith
    have := div_nonneg hnum (le_of_lt (mul_pos hx hxy))
    linarith [expand ▸ this]
  · have hnum : ((x+y)*x + 2*y*x - (x+y) - (x+q)*(x+y)) < 0 := by nlinarith
    have hneg : ((x+y)*x + 2*y*x - (x+y) - (x+q)*(x+y)) / (x*(x+y)) < 0 :=
      div_neg_of_neg_of_pos hnum (mul_pos hx hxy)
    linarith [expand2 ▸ hneg]

/-- The exact ratio recursion with the floor defect controlled: for `k ≥ 0` (i.e. `n = k+2
≥ 2`), `F (R (k+1)) - 1/a(k+2) < R (k+2) ≤ F (R (k+1))`. This is obtained by casting the
Euclidean division identity defining `a (k+3)` to `ℝ` and applying `ratio_bound_core`. -/
theorem ratio_rec (k : ℕ) :
    R (k+2) ≤ F (R (k+1)) ∧ F (R (k+1)) - 1/(a (k+2):ℝ) < R (k+2) := by
  have hx1 : 1 ≤ a (k+2) := (a_pos_pair k).2
  have hy1 : 1 ≤ a (k+1) := (a_pos_pair k).1
  have hm0 : 0 < a (k+2) + a (k+1) := by omega
  have hqrnat : (a (k+2)+a (k+1)) * ((2*a (k+2)*a (k+1)) / (a (k+2)+a (k+1)))
      + (2*a (k+2)*a (k+1)) % (a (k+2)+a (k+1)) = 2*a (k+2)*a (k+1) :=
    Nat.div_add_mod _ _
  have hrltnat : (2*a (k+2)*a (k+1)) % (a (k+2)+a (k+1)) < a (k+2)+a (k+1) :=
    Nat.mod_lt _ hm0
  have ha3 : a (k+2+1) = a (k+2) + (2*a (k+2)*a (k+1)) / (a (k+2)+a (k+1)) := a_rec k
  set xR : ℝ := (a (k+2) : ℝ) with hxRdef
  set yR : ℝ := (a (k+1) : ℝ) with hyRdef
  set qR : ℝ := (((2*a (k+2)*a (k+1)) / (a (k+2)+a (k+1)) : ℕ) : ℝ) with hqRdef
  set rR : ℝ := (((2*a (k+2)*a (k+1)) % (a (k+2)+a (k+1)) : ℕ) : ℝ) with hrRdef
  have hxpos : 0 < xR := by rw [hxRdef]; exact_mod_cast hx1
  have hypos : 0 < yR := by rw [hyRdef]; exact_mod_cast hy1
  have hqrR : (xR+yR)*qR + rR = 2*xR*yR := by
    rw [hxRdef, hyRdef, hqRdef, hrRdef]
    exact_mod_cast hqrnat
  have hr0R : 0 ≤ rR := by rw [hrRdef]; positivity
  have hrltR : rR < xR + yR := by
    rw [hrRdef, hxRdef, hyRdef]
    exact_mod_cast hrltnat
  have hcore := ratio_bound_core xR yR qR (2*xR*yR) rR hxpos hypos rfl hqrR hr0R hrltR
  have hReq : R (k+2) = (xR + qR)/xR := by
    show (a (k+2+1):ℝ)/(a (k+2):ℝ) = (xR+qR)/xR
    rw [ha3, hxRdef, hqRdef]
    push_cast
    ring
  have hFeq : F (R (k+1)) = 1 + 2*yR/(xR+yR) := by
    show F ((a (k+2):ℝ)/(a (k+1):ℝ)) = 1 + 2*yR/(xR+yR)
    rw [hxRdef, hyRdef] at *
    exact F_eval (a (k+2):ℝ) (a (k+1):ℝ)
      (by exact_mod_cast (by omega : a (k+1) ≠ 0)) (by positivity)
  rw [hReq, hFeq]
  exact ⟨hcore.1, hcore.2⟩

/-! ## Fixed point and contraction of `F` -/

theorem F_fixed : F (Real.sqrt 3) = Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold F
  field_simp
  nlinarith [h3]

theorem F_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : |F x - F y| ≤ |x - y| / 2 := by
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have hy1 : (0:ℝ) < y + 1 := by linarith
  have key : F x - F y = 2*(y - x)/((x+1)*(y+1)) := by
    unfold F; field_simp; ring
  rw [key, abs_div]
  rw [abs_of_pos (mul_pos hx1 hy1)]
  have h4 : (4:ℝ) ≤ (x+1)*(y+1) := by nlinarith
  have hle : 2*|y-x| / ((x+1)*(y+1)) ≤ 2*|y-x|/4 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h4
  have heq : (2:ℝ)*|y-x|/4 = |x-y|/2 := by rw [abs_sub_comm]; ring
  calc |2*(y-x)| / ((x+1)*(y+1)) = 2*|y-x|/((x+1)*(y+1)) := by rw [abs_mul]; norm_num
    _ ≤ 2*|y-x|/4 := hle
    _ = |x-y|/2 := heq

/-! ## The error recursion -/

/-- `e n := |R n - √3|` satisfies the contraction-with-forcing-term recursion
`e (k+2) ≤ e (k+1) / 2 + 1 / a (k+2)`. -/
theorem e_rec (k : ℕ) :
    |R (k+2) - Real.sqrt 3| ≤ |R (k+1) - Real.sqrt 3| / 2 + 1/(a (k+2):ℝ) := by
  have hrr := ratio_rec k
  have hsqrt1 : 1 ≤ Real.sqrt 3 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, h3]
  have hR1 : 1 ≤ R (k+1) := R_ge_one k
  have hlip := F_lipschitz hR1 hsqrt1
  have htri : |R (k+2) - Real.sqrt 3| ≤ |R (k+2) - F (R (k+1))| + |F (R (k+1)) - Real.sqrt 3| :=
    abs_sub_le _ _ _
  have hapos : (0:ℝ) < (a (k+2):ℝ) := by exact_mod_cast (a_pos_pair k).2
  have hbound1 : |R (k+2) - F (R (k+1))| ≤ 1/(a (k+2):ℝ) := by
    rw [abs_le]
    constructor <;> [linarith [hrr.2]; linarith [hrr.1, (one_div_pos.mpr hapos)]]
  have hbound2 : |F (R (k+1)) - Real.sqrt 3| ≤ |R (k+1) - Real.sqrt 3| / 2 := by
    rwa [F_fixed] at hlip
  linarith [htri, hbound1, hbound2]

/-! ## General convergence lemma for contraction-with-forcing-term recursions -/

/-- Unrolling `e (k+1) ≤ e k / 2 + b k` (for `k ≥ 1`) for `m` steps from a starting index `N`,
given a uniform bound `b k ≤ ε` for `k ≥ N`. -/
theorem aux_geom (e b : ℕ → ℝ) (N : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hrec : ∀ k, 1 ≤ k → e (k+1) ≤ e k / 2 + b k)
    (hb : ∀ k, N ≤ k → b k ≤ ε) (hN : 1 ≤ N) :
    ∀ m, e (N + m) ≤ (1/2:ℝ)^m * e N + 2 * ε := by
  intro m
  induction m with
  | zero => simp; linarith
  | succ m ih =>
    have h1 : e (N + m + 1) ≤ e (N + m) / 2 + b (N + m) := hrec (N + m) (by omega)
    have h2 : b (N + m) ≤ ε := hb (N + m) (by omega)
    have heq : N + (m + 1) = N + m + 1 := by omega
    rw [heq]
    have hpow : (1/2:ℝ)^(m+1) = (1/2:ℝ)^m / 2 := by ring
    rw [hpow]
    nlinarith [ih, h1, h2]

/-- If `e (k+1) ≤ e k / 2 + b k` for `k ≥ 1`, `e ≥ 0`, and `b → 0`, then `e → 0`. Proved by
an explicit `ε`/`N` argument using `aux_geom`. -/
theorem tendsto_e_zero (e b : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (hrec : ∀ k, 1 ≤ k → e (k+1) ≤ e k / 2 + b k)
    (hbtend : Filter.Tendsto b Filter.atTop (nhds 0)) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hbtend
  obtain ⟨N1, hN1⟩ := hbtend (ε/4) (by linarith)
  set N := max N1 1 with hNdef
  have hN1' : N1 ≤ N := le_max_left _ _
  have hN1ge : 1 ≤ N := le_max_right _ _
  have hb : ∀ k, N ≤ k → b k ≤ ε/4 := by
    intro k hk
    have hh := hN1 k (le_trans hN1' hk)
    rw [Real.dist_eq] at hh
    have hh2 := abs_lt.mp hh
    linarith [hh2.2]
  have hgeom := aux_geom e b N (ε/4) (by linarith) hrec hb hN1ge
  have htendpow : Filter.Tendsto (fun m : ℕ => (1/2:ℝ)^m * e N) Filter.atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    simpa using hp.mul_const (e N)
  rw [Metric.tendsto_atTop] at htendpow
  obtain ⟨M, hM⟩ := htendpow (ε/2) (by linarith)
  refine ⟨N + M, ?_⟩
  intro n hn
  have hm : M ≤ n - N := by omega
  have heqn : N + (n - N) = n := by omega
  have hb1 := hgeom (n - N)
  rw [heqn] at hb1
  have hb2 := hM (n - N) hm
  rw [Real.dist_eq] at hb2
  have habs2 : |(1/2:ℝ)^(n-N) * e N| = (1/2:ℝ)^(n-N) * e N := by
    apply abs_of_nonneg
    apply mul_nonneg (by positivity) (he0 N)
  rw [sub_zero, habs2] at hb2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)]
  linarith [hb1, hb2]

/-- The forcing term `1 / a (n+1) → 0`, since `a (n+1) ≥ n + 1`. -/
theorem b_to_zero : Filter.Tendsto (fun j : ℕ => 1/(a (j+1):ℝ)) Filter.atTop (nhds 0) := by
  have hsqueeze : Filter.Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun j => by positivity) ?_ hsqueeze
  intro j
  have hge := a_ge_index j
  have hpos : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have hcast : (j:ℝ) + 1 ≤ (a (j+1):ℝ) := by exact_mod_cast hge
  exact one_div_le_one_div_of_le hpos hcast

/-- The error `|R n - √3|` tends to `0`. -/
theorem e_tendsto_zero :
    Filter.Tendsto (fun n => |R n - Real.sqrt 3|) Filter.atTop (nhds 0) := by
  apply tendsto_e_zero (fun n => |R n - Real.sqrt 3|) (fun j => 1/(a (j+1):ℝ))
  · intro n; exact abs_nonneg _
  · intro j hj
    match j, hj with
    | (k+1), _ =>
      show |R (k+1+1) - Real.sqrt 3| ≤ |R (k+1) - Real.sqrt 3|/2 + 1/(a (k+1+1):ℝ)
      exact e_rec k
  · exact b_to_zero

/-- **OEIS A114831**: the ratio of consecutive terms of `a` converges to `√3`. -/
theorem a114831 : Filter.Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)) Filter.atTop (nhds (Real.sqrt 3)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have heq : (fun n => dist ((a (n+1):ℝ)/(a n:ℝ)) (Real.sqrt 3)) = (fun n => |R n - Real.sqrt 3|) := by
    funext n
    rw [Real.dist_eq]
    rfl
  rw [heq]
  exact e_tendsto_zero

#print axioms a114831
