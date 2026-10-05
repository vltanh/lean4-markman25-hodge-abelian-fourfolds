module

public import WeilClasses.External.Igusa.Sec10

/-!
# [Igusa, Prop. 3], last paragraph of the proof: the normal form `1 + 2s [pt_X]`

J.-I. Igusa, *A classification of spinors up to dimension twelve*, Amer. J. Math. **92** (1970),
no. 4, 997–1028 ([I] in the paper). For an abelian threefold (`n = 3`), `S⁺_F = H^ev(X, F)` is the
`32`-dimensional half-spin representation of `Spin(V_F)`, `dim V_F = 12`, and `J` is the invariant
quartic (10.1.1) (`WeilClasses.J`). This file proves, over every field `F` of characteristic zero:

* `igusa_prop3_normalForm_general`: if `w ∈ S⁺_F`, `s ∈ F`, `s ≠ 0` and `s² = -J(w)`, then some
  `g ∈ Spin(V_F)` maps `w` to `1 + 2s [pt_X]` (note `J(1 + 2s [pt_X]) = -s²`);
* `igusa_prop3_orbit_complex`: for `c ≠ 0`, `J⁻¹(c) ⊆ S⁺_ℂ` is one `Spin(V_ℂ)`-orbit (proof of
  Lemma 10.1.1, l. 9702);
* `igusa_prop3_normalForm`: the normal form `1 + 2√-d [pt_X]` over `K = ℚ(√-d)` for `w ∈ S⁺_ℚ` with
  `J(w) = d > 0` (proof of Lemma 10.2.1, l. 9792).

The results of §10 that use the normal form (Lemma 10.1.1, Remark 10.1.2, Lemma 10.2.1) cite these
theorems.

## The proof

Write `x = (α, X, Y, β)` for the components of `x ∈ S⁺_F` in degrees `0, 2, 4, 6`: `α = x_∅`,
`X = (x_ij)`, `Y = (y_ij)` (the coefficients of the `e_ij^*`), `β` the coefficient of `[pt_X]`.

1. A product of Weyl elements makes `α ≠ 0` (`sc_exists_weyl_ne`), and root elements
   `1 + t e_i e_j` kill `X` (`sc_bigcell_aux`). For `X = 0`, `J(w) = α N(Y) - ¼ α² β²`, where
   `N(Y) = Pf(y_ij)` (`ig_J_red`).
2. Let `μ = -2α / (αβ + 2s)` (after replacing `s` by `-s` if `αβ + 2s = 0`). It is a root of
   `N μ² + αβ μ + α = 0`, whose discriminant is `α² β² - 4αN = -4J(w) = 4s²`. The fifteen
   contraction root elements `1 + d_ij f_i f_j`, `d = ±μ y` (their product `ig_psiY` acts by
   `exp(μ Ŷ ⌋)`), map `(α, 0, Y, β)` to `(α', μ(2 + βμ) Y^#, (1 + βμ) Y, β)`, where `Y^#` is the
   Pfaffian adjoint of `Y` (`ig_T`) and `α' = α - N(3μ² + βμ³) = α(2 + βμ)² ≠ 0` (`ig_psi_cm0`,
   `ig_psi_cm2`, `ig_psi_cm4`).
3. The fifteen root elements `φ(-X'/α')` (`ig_phi`, `ig_killX`) kill the new degree-`2` part `X'`,
   and the degree-`4` part becomes `Y' - X'^#/α' = (1 + βμ + μ²(2 + βμ)² N/α') Y = 0`, by the
   adjoint identity `(Y^#)^# = -N Y` (`ig_adj_*`, `ig_vanish_*`). So `w ~ a + b [pt_X]`
   (`ig_core`), and `J(a + b [pt_X]) = -¼ (ab)² = J(w) = -s²` gives `ab = ±2s`.
4. Igusa's element `s(a⁻¹)` (`sc_hd`) maps `a + b [pt_X]` to `1 + ab [pt_X]` (`ig_m_hd_line`). If
   `ab = -2s`, the Weyl element `v₁ ⋯ v₆` (`1 ↦ [pt_X]`, `[pt_X] ↦ -1`, `ig_wfl`) followed by an
   Igusa element maps `1 + c [pt_X]` to `1 - c [pt_X]` (`ig_flip`).

The computations are done in the bit-mask coordinates `sc_cm` of `Sec10.lean` (the coordinate
`k < 64` of `x` is the coefficient of `e_K`, `K` the set of bits of `k`), through the coordinate
formulas `sc_cm_ι_e`, `sc_cm_D_f` of the generators; each identity between coordinates is closed by
`ring` or `linear_combination`. The formulas were found and checked first with an exact rational
model of these conventions.

Igusa obtains the normal form in the course of his classification of the orbits of `Spin(12)` on
`S⁺`, over a universal domain (generic elements lie on a secant through two pure spinors with
transversal maximal isotropic subspaces). The argument here is a direct elimination over `F` in the
Fock model, in the style of the reduction theory of Freudenthal triple systems; `μ` is where the
square root `s` of `-J(w)` enters.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-- Evaluates bit-mask coordinates through the coordinate formulas of generators: the given
lemmas, the signs `sc_sgn` and the bit tests (by `decide`). -/
local macro "ig_cm_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) only [$ls,*, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.reduceMul, mul_zero, add_zero, zero_add, sc_sgn, Nat.reducePow,
    Nat.reduceXor, ↓reduceIte])

/-! ## Helpers (prefix `ig_`): the contraction root elements `1 + t f_i f_j` -/

section IGGen

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem ig_Q_F (θ : Module.Dual F (H1 F n)) : Q F n ((θ, 0) : V F n) = 0 := by simp

omit [CharZero F] in
theorem ig_polar_F_F (θ θ' : Module.Dual F (H1 F n)) :
    QuadraticMap.polar (Q F n) ((θ, 0) : V F n) (θ', 0) = 0 := by
  rw [TauCeti.polar_dualProd]; simp

/-- The contraction root element `x⁻_{ij}(t) = 1 + t f_i f_j`, the Spin lift of an Eichler
transvection (Tau Ceti's `spinTransvection`), like the root elements `sc_xp`. -/
noncomputable def ig_xm (i j : Fin (2 * n)) (t : F) : Spin F n :=
  spinTransvection sc_Q_nondegenerate (ig_Q_F (f F n j)) (ig_polar_F_F (f F n j) (t • f F n i))

/-- `1 + t f_i f_j` acts on `S` by `w ↦ w + t f_i ⌋ f_j ⌋ w`. -/
theorem ig_m_xm (i j : Fin (2 * n)) (t : F) (w : S F n) :
    m F n ((ig_xm i j t : Spin F n) : C F n) w = w + t • D F n (f F n i) (D F n (f F n j) w) := by
  rw [ig_xm, coe_spinTransvection, map_add, map_one, map_mul, LinearMap.add_apply,
    Module.End.one_apply, Module.End.mul_apply, sc_m_ι, sc_m_ι]
  simp only [map_zero, zero_mul, zero_add, map_smul, LinearMap.smul_apply]

end IGGen

/-! ## Helpers: bit masks and coordinates (`n = 3`) -/

section IGMask

variable {F : Type*} [Field F] [CharZero F]

/-- The bit masks of the pairs `{i, j}` (the coordinates `x_ij` of degree `2`). -/
def ig_D2 : List ℕ := [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48]

/-- The bit masks of the complements of the pairs (the coordinates of degree `4`). -/
def ig_D4 : List ℕ := [15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58, 60]

theorem ig_card_D2 : ∀ k ∈ ig_D2, (sc_ofMask k).card = 2 := by decide

/-- Every subset of `Fin 6` is `sc_ofMask k` for some `k < 64`. -/
theorem ig_ofMask_surj (K : Finset (Fin (2 * 3))) : ∃ k < 64, sc_ofMask k = K := by
  induction K using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by decide⟩
  | insert a K _ ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    refine ⟨k ||| 2 ^ (a : ℕ), ?_, ?_⟩
    · have h1 : k < 2 ^ 6 := hk
      have h2 : 2 ^ (a : ℕ) < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) a.isLt
      exact Nat.or_lt_two_pow h1 h2
    · ext i
      simp only [sc_mem_ofMask, Finset.mem_insert, Nat.testBit_or, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff]
      tauto

theorem ig_ofMask_eq_empty : ∀ k < 64, sc_ofMask k = ∅ → k = 0 := by decide

theorem ig_ofMask_eq_univ : ∀ k < 64, sc_ofMask k = Finset.univ → k = 63 := by decide

/-- The masks `k < 64` are the odd ones, `0`, `63`, and those of `ig_D2` and `ig_D4`. -/
theorem ig_ofMask_parity : ∀ k < 64,
    (sc_ofMask k).card % 2 = 1 ∨ k ∈ 0 :: 63 :: (ig_D2 ++ ig_D4) := by decide

omit [CharZero F] in
theorem ig_cm_one (k : ℕ) : sc_cm (1 : S F 3) k = if sc_ofMask k = ∅ then 1 else 0 :=
  sc_repr_one _

omit [CharZero F] in
theorem ig_cm_pt (k : ℕ) : sc_cm (pt F 3) k = if sc_ofMask k = Finset.univ then 1 else 0 := by
  unfold sc_cm pt
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

omit [CharZero F] in
theorem ig_cm_one_zero : sc_cm (1 : S F 3) 0 = 1 := by
  rw [ig_cm_one, ite_eq_left (by decide)]

omit [CharZero F] in
theorem ig_cm_one_ne (k : ℕ) (hk : k < 64) (h0 : k ≠ 0) : sc_cm (1 : S F 3) k = 0 := by
  rw [ig_cm_one, ite_eq_right (fun h => h0 (ig_ofMask_eq_empty k hk h))]

omit [CharZero F] in
theorem ig_cm_pt_top : sc_cm (pt F 3) 63 = 1 := by
  rw [ig_cm_pt, ite_eq_left (by decide)]

omit [CharZero F] in
theorem ig_cm_pt_ne (k : ℕ) (hk : k < 64) (h63 : k ≠ 63) : sc_cm (pt F 3) k = 0 := by
  rw [ig_cm_pt, ite_eq_right (fun h => h63 (ig_ofMask_eq_univ k hk h))]

/-- An element of `S⁺` whose coordinates of degree `2` and `4` vanish is
`x_∅ · 1 + x_top [pt_X]`. -/
theorem ig_eq_of_cm (z : S F 3) (hz : z ∈ Splus F 3) (h2 : ∀ k ∈ ig_D2, sc_cm z k = 0)
    (h4 : ∀ k ∈ ig_D4, sc_cm z k = 0) : z = sc_cm z 0 • 1 + sc_cm z 63 • pt F 3 := by
  apply (basisS F 3).repr.injective
  ext K
  obtain ⟨k, hk, rfl⟩ := ig_ofMask_surj K
  change sc_cm z k = sc_cm (sc_cm z 0 • 1 + sc_cm z 63 • pt F 3) k
  rw [sc_cm_add, sc_cm_smul, sc_cm_smul, ig_cm_one, ig_cm_pt]
  by_cases h0 : k = 0
  · subst h0
    rw [ite_eq_left (by decide), ite_eq_right (by decide), mul_one, mul_zero, add_zero]
  by_cases h63 : k = 63
  · subst h63
    rw [ite_eq_right (by decide), ite_eq_left (by decide), mul_one, mul_zero, zero_add]
  rw [ite_eq_right (fun h => h0 (ig_ofMask_eq_empty k hk h)),
    ite_eq_right (fun h => h63 (ig_ofMask_eq_univ k hk h)), mul_zero, mul_zero, add_zero]
  rcases ig_ofMask_parity k hk with hodd | hmem
  · exact sc_repr_eq_zero_of_mem_Splus hz _ (Nat.odd_iff.mpr hodd)
  · simp only [List.mem_cons, List.mem_append] at hmem
    rcases hmem with rfl | rfl | hmem | hmem
    · exact absurd rfl h0
    · exact absurd rfl h63
    · exact h2 k hmem
    · exact h4 k hmem

/-- The coordinates of `x⁺_{ij}(t) v = v + t e_i ∧ e_j ∧ v`. -/
theorem ig_cm_xp (i j : Fin (2 * 3)) (t : F) (v : S F 3) (k : ℕ) :
    sc_cm (m F 3 ((sc_xp i j t : Spin F 3) : C F 3) v) k =
      sc_cm v k + t * (if k.testBit i then (if (k ^^^ 2 ^ (i : ℕ)).testBit j then
        sc_sgn (k ^^^ 2 ^ (i : ℕ)) i * sc_sgn ((k ^^^ 2 ^ (i : ℕ)) ^^^ 2 ^ (j : ℕ)) j *
          sc_cm v ((k ^^^ 2 ^ (i : ℕ)) ^^^ 2 ^ (j : ℕ)) else 0) else 0) := by
  rw [sc_m_xp, sc_cm_add, sc_cm_smul, sc_cm_ι_e', sc_cm_ι_e']
  split_ifs <;> ring

/-- The coordinates of `x⁻_{ij}(t) v = v + t f_i ⌋ f_j ⌋ v`. -/
theorem ig_cm_xm (i j : Fin (2 * 3)) (t : F) (v : S F 3) (k : ℕ) :
    sc_cm (m F 3 ((ig_xm i j t : Spin F 3) : C F 3) v) k =
      sc_cm v k + t * (if k.testBit i then 0 else sc_sgn k i *
        (if (k ^^^ 2 ^ (i : ℕ)).testBit j then 0 else
          sc_sgn (k ^^^ 2 ^ (i : ℕ)) j * sc_cm v ((k ^^^ 2 ^ (i : ℕ)) ^^^ 2 ^ (j : ℕ)))) := by
  rw [ig_m_xm, sc_cm_add, sc_cm_smul, sc_cm_D_f', sc_cm_D_f']

/-- The coordinates of `m(v_a) u = e_a ∧ u + f_a ⌋ u`, `v_a = f_a + e_a`. -/
theorem ig_cm_vW (a : Fin (2 * 3)) (u : S F 3) (k : ℕ) :
    sc_cm (m F 3 (ι (Q F 3) (sc_vW a)) u) k =
      (if k.testBit a then sc_sgn (k ^^^ 2 ^ (a : ℕ)) a * sc_cm u (k ^^^ 2 ^ (a : ℕ)) else 0) +
        (if k.testBit a then 0 else sc_sgn k a * sc_cm u (k ^^^ 2 ^ (a : ℕ))) := by
  rw [sc_m_vW3, sc_cm_add, sc_cm_ι_e', sc_cm_D_f']

end IGMask

/-! ## Helpers: the Pfaffian `N(Y)`, its adjoint `Y^#`, and the identity `(Y^#)^# = -N(Y) Y` -/

section IGPfaffian

variable {F : Type*} [Field F]

/-- The Pfaffian `N(Y) = Pf(y_ij)` of the degree-`4` coordinates, as it enters `J` (the coefficient
of `x₀` in `sc_JcM`). -/
def ig_N (c : ℕ → F) : F :=
  c 60 * ((-c 43) * (-c 23) - c 51 * c 15 - c 27 * c 39) - (-c 58) * (c 45 * (-c 23) -
    (-c 53) * c 15 - (-c 29) * c 39) + c 54 * (c 45 * c 27 - c 57 * c 15 - (-c 29) * (-c 43)) -
    (-c 46) * ((-c 53) * c 27 - c 57 * (-c 23) - (-c 29) * c 51) + c 30 * ((-c 53) * (-c 43) -
    c 57 * c 39 - c 45 * c 51)

/-- The Pfaffian adjoint `Y^#` of the degree-`4` part, at the bit mask `k` of a pair:
`T_k(y) = Σ ± y_{k ∪ p} y_{k ∪ q}` over the matchings `{p, q}` of the complement of `k`. -/
def ig_T (y : ℕ → F) : ℕ → F
  | 3 => y 15 * y 51 - y 23 * y 43 + y 27 * y 39
  | 5 => y 15 * y 53 - y 23 * y 45 + y 29 * y 39
  | 6 => y 15 * y 54 - y 23 * y 46 + y 30 * y 39
  | 9 => y 15 * y 57 - y 27 * y 45 + y 29 * y 43
  | 10 => y 15 * y 58 - y 27 * y 46 + y 30 * y 43
  | 12 => y 15 * y 60 - y 29 * y 46 + y 30 * y 45
  | 17 => y 23 * y 57 - y 27 * y 53 + y 29 * y 51
  | 18 => y 23 * y 58 - y 27 * y 54 + y 30 * y 51
  | 20 => y 23 * y 60 - y 29 * y 54 + y 30 * y 53
  | 24 => y 27 * y 60 - y 29 * y 58 + y 30 * y 57
  | 33 => y 39 * y 57 - y 43 * y 53 + y 45 * y 51
  | 34 => y 39 * y 58 - y 43 * y 54 + y 46 * y 51
  | 36 => y 39 * y 60 - y 45 * y 54 + y 46 * y 53
  | 40 => y 43 * y 60 - y 45 * y 58 + y 46 * y 57
  | 48 => y 51 * y 60 - y 53 * y 58 + y 54 * y 57
  | _ => 0

/-- The adjoint identity `(Y^#)^# = -N(Y) Y` at the degree-`4` mask `15` (and below at the
other fourteen masks): the sum of `± T_p T_q` over the three matchings `{p, q}` of the
mask. -/
theorem ig_adj_15 (y : ℕ → F) :
    ig_T y 3 * ig_T y 12 - ig_T y 5 * ig_T y 10 + ig_T y 6 * ig_T y 9 = -(ig_N y * y 15) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_23 (y : ℕ → F) :
    ig_T y 3 * ig_T y 20 - ig_T y 5 * ig_T y 18 + ig_T y 6 * ig_T y 17 = -(ig_N y * y 23) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_27 (y : ℕ → F) :
    ig_T y 3 * ig_T y 24 - ig_T y 9 * ig_T y 18 + ig_T y 10 * ig_T y 17 = -(ig_N y * y 27) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_29 (y : ℕ → F) :
    ig_T y 5 * ig_T y 24 - ig_T y 9 * ig_T y 20 + ig_T y 12 * ig_T y 17 = -(ig_N y * y 29) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_30 (y : ℕ → F) :
    ig_T y 6 * ig_T y 24 - ig_T y 10 * ig_T y 20 + ig_T y 12 * ig_T y 18 = -(ig_N y * y 30) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_39 (y : ℕ → F) :
    ig_T y 3 * ig_T y 36 - ig_T y 5 * ig_T y 34 + ig_T y 6 * ig_T y 33 = -(ig_N y * y 39) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_43 (y : ℕ → F) :
    ig_T y 3 * ig_T y 40 - ig_T y 9 * ig_T y 34 + ig_T y 10 * ig_T y 33 = -(ig_N y * y 43) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_45 (y : ℕ → F) :
    ig_T y 5 * ig_T y 40 - ig_T y 9 * ig_T y 36 + ig_T y 12 * ig_T y 33 = -(ig_N y * y 45) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_46 (y : ℕ → F) :
    ig_T y 6 * ig_T y 40 - ig_T y 10 * ig_T y 36 + ig_T y 12 * ig_T y 34 = -(ig_N y * y 46) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_51 (y : ℕ → F) :
    ig_T y 3 * ig_T y 48 - ig_T y 17 * ig_T y 34 + ig_T y 18 * ig_T y 33 = -(ig_N y * y 51) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_53 (y : ℕ → F) :
    ig_T y 5 * ig_T y 48 - ig_T y 17 * ig_T y 36 + ig_T y 20 * ig_T y 33 = -(ig_N y * y 53) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_54 (y : ℕ → F) :
    ig_T y 6 * ig_T y 48 - ig_T y 18 * ig_T y 36 + ig_T y 20 * ig_T y 34 = -(ig_N y * y 54) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_57 (y : ℕ → F) :
    ig_T y 9 * ig_T y 48 - ig_T y 17 * ig_T y 40 + ig_T y 24 * ig_T y 33 = -(ig_N y * y 57) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_58 (y : ℕ → F) :
    ig_T y 10 * ig_T y 48 - ig_T y 18 * ig_T y 40 + ig_T y 24 * ig_T y 34 = -(ig_N y * y 58) := by
  simp only [ig_T, ig_N]
  ring

theorem ig_adj_60 (y : ℕ → F) :
    ig_T y 12 * ig_T y 48 - ig_T y 20 * ig_T y 40 + ig_T y 24 * ig_T y 36 = -(ig_N y * y 60) := by
  simp only [ig_T, ig_N]
  ring

end IGPfaffian

/-! ## Helpers: the products `φ(c)` of root elements and `ψ_Y(μ)` of contraction root elements -/

section IGProducts

variable {F : Type*} [Field F] [CharZero F]

/-- The product `φ(c) = ∏_{i<j} (1 + c_ij e_i e_j)` of the fifteen root elements, `c_ij` being the
value of `c` at the bit mask `2^i + 2^j`; it acts on `S` by `v ↦ exp(Σ c_ij e_i ∧ e_j) ∧ v`. -/
noncomputable def ig_phi (c : ℕ → F) : Spin F 3 :=
  sc_xp 0 1 (c 3) *
    (sc_xp 0 2 (c 5) *
    (sc_xp 0 3 (c 9) *
    (sc_xp 0 4 (c 17) *
    (sc_xp 0 5 (c 33) *
    (sc_xp 1 2 (c 6) *
    (sc_xp 1 3 (c 10) *
    (sc_xp 1 4 (c 18) *
    (sc_xp 1 5 (c 34) *
    (sc_xp 2 3 (c 12) *
    (sc_xp 2 4 (c 20) *
    (sc_xp 2 5 (c 36) *
    (sc_xp 3 4 (c 24) *
    (sc_xp 3 5 (c 40) *
    (sc_xp 4 5 (c 48)))))))))))))))

/-- The product `ψ_Y(μ) = ∏_{i<j} (1 + d_ij f_i f_j)` of the fifteen contraction root elements,
`d_ij = ±μ y_{\{i,j\}ᶜ}`: it acts on `S` by `exp(μ Ŷ ⌋)`, where `Ŷ ∈ ⋀² H¹(X)^*` is the form
with `Ŷ ⌋ [pt_X] = Y`, the degree-`4` part with coordinates `y`. -/
noncomputable def ig_psiY (μ : F) (y : ℕ → F) : Spin F 3 :=
  ig_xm 0 1 (-(μ * y 60)) *
    (ig_xm 0 2 (μ * y 58) *
    (ig_xm 0 3 (-(μ * y 54)) *
    (ig_xm 0 4 (μ * y 46) *
    (ig_xm 0 5 (-(μ * y 30)) *
    (ig_xm 1 2 (-(μ * y 57)) *
    (ig_xm 1 3 (μ * y 53) *
    (ig_xm 1 4 (-(μ * y 45)) *
    (ig_xm 1 5 (μ * y 29) *
    (ig_xm 2 3 (-(μ * y 51)) *
    (ig_xm 2 4 (μ * y 43) *
    (ig_xm 2 5 (-(μ * y 27)) *
    (ig_xm 3 4 (-(μ * y 39)) *
    (ig_xm 3 5 (μ * y 23) *
    (ig_xm 4 5 (-(μ * y 15))))))))))))))))

/-- The coefficients `-x_k / x_∅` of `φ` that kill the degree-`2` part of `v` (`ig_vanish2`). -/
noncomputable def ig_killX (v : S F 3) (k : ℕ) : F := -((sc_cm v 0)⁻¹ * sc_cm v k)

/-- `φ(c)` in degree `2`: `(exp(C) ∧ v)_k = v_k + c_k v_∅`. -/
theorem ig_phi_cm2 (c : ℕ → F) (v : S F 3) : ∀ k ∈ ig_D2,
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) k = sc_cm v k + c k * sc_cm v 0 := by
  intro k hk
  simp only [ig_D2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  all_goals
    ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
    ring

/-- `φ(c)` at the degree-`4` mask `15` (and below at the other fourteen masks):
`(exp(C) ∧ v)_K = v_K + Σ ± (c_p v_q + c_q v_p + c_p c_q v_∅)` over the three matchings
`{p, q}` of `K`. -/
theorem ig_phi_cm_15 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 15 =
      sc_cm v 15 +
        (c 3 * sc_cm v 12 + c 12 * sc_cm v 3 + c 3 * c 12 * sc_cm v 0) -
        (c 5 * sc_cm v 10 + c 10 * sc_cm v 5 + c 5 * c 10 * sc_cm v 0) +
        (c 6 * sc_cm v 9 + c 9 * sc_cm v 6 + c 6 * c 9 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_23 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 23 =
      sc_cm v 23 +
        (c 3 * sc_cm v 20 + c 20 * sc_cm v 3 + c 3 * c 20 * sc_cm v 0) -
        (c 5 * sc_cm v 18 + c 18 * sc_cm v 5 + c 5 * c 18 * sc_cm v 0) +
        (c 6 * sc_cm v 17 + c 17 * sc_cm v 6 + c 6 * c 17 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_27 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 27 =
      sc_cm v 27 +
        (c 3 * sc_cm v 24 + c 24 * sc_cm v 3 + c 3 * c 24 * sc_cm v 0) -
        (c 9 * sc_cm v 18 + c 18 * sc_cm v 9 + c 9 * c 18 * sc_cm v 0) +
        (c 10 * sc_cm v 17 + c 17 * sc_cm v 10 + c 10 * c 17 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_29 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 29 =
      sc_cm v 29 +
        (c 5 * sc_cm v 24 + c 24 * sc_cm v 5 + c 5 * c 24 * sc_cm v 0) -
        (c 9 * sc_cm v 20 + c 20 * sc_cm v 9 + c 9 * c 20 * sc_cm v 0) +
        (c 12 * sc_cm v 17 + c 17 * sc_cm v 12 + c 12 * c 17 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_30 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 30 =
      sc_cm v 30 +
        (c 6 * sc_cm v 24 + c 24 * sc_cm v 6 + c 6 * c 24 * sc_cm v 0) -
        (c 10 * sc_cm v 20 + c 20 * sc_cm v 10 + c 10 * c 20 * sc_cm v 0) +
        (c 12 * sc_cm v 18 + c 18 * sc_cm v 12 + c 12 * c 18 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_39 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 39 =
      sc_cm v 39 +
        (c 3 * sc_cm v 36 + c 36 * sc_cm v 3 + c 3 * c 36 * sc_cm v 0) -
        (c 5 * sc_cm v 34 + c 34 * sc_cm v 5 + c 5 * c 34 * sc_cm v 0) +
        (c 6 * sc_cm v 33 + c 33 * sc_cm v 6 + c 6 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_43 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 43 =
      sc_cm v 43 +
        (c 3 * sc_cm v 40 + c 40 * sc_cm v 3 + c 3 * c 40 * sc_cm v 0) -
        (c 9 * sc_cm v 34 + c 34 * sc_cm v 9 + c 9 * c 34 * sc_cm v 0) +
        (c 10 * sc_cm v 33 + c 33 * sc_cm v 10 + c 10 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_45 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 45 =
      sc_cm v 45 +
        (c 5 * sc_cm v 40 + c 40 * sc_cm v 5 + c 5 * c 40 * sc_cm v 0) -
        (c 9 * sc_cm v 36 + c 36 * sc_cm v 9 + c 9 * c 36 * sc_cm v 0) +
        (c 12 * sc_cm v 33 + c 33 * sc_cm v 12 + c 12 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_46 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 46 =
      sc_cm v 46 +
        (c 6 * sc_cm v 40 + c 40 * sc_cm v 6 + c 6 * c 40 * sc_cm v 0) -
        (c 10 * sc_cm v 36 + c 36 * sc_cm v 10 + c 10 * c 36 * sc_cm v 0) +
        (c 12 * sc_cm v 34 + c 34 * sc_cm v 12 + c 12 * c 34 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_51 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 51 =
      sc_cm v 51 +
        (c 3 * sc_cm v 48 + c 48 * sc_cm v 3 + c 3 * c 48 * sc_cm v 0) -
        (c 17 * sc_cm v 34 + c 34 * sc_cm v 17 + c 17 * c 34 * sc_cm v 0) +
        (c 18 * sc_cm v 33 + c 33 * sc_cm v 18 + c 18 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_53 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 53 =
      sc_cm v 53 +
        (c 5 * sc_cm v 48 + c 48 * sc_cm v 5 + c 5 * c 48 * sc_cm v 0) -
        (c 17 * sc_cm v 36 + c 36 * sc_cm v 17 + c 17 * c 36 * sc_cm v 0) +
        (c 20 * sc_cm v 33 + c 33 * sc_cm v 20 + c 20 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_54 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 54 =
      sc_cm v 54 +
        (c 6 * sc_cm v 48 + c 48 * sc_cm v 6 + c 6 * c 48 * sc_cm v 0) -
        (c 18 * sc_cm v 36 + c 36 * sc_cm v 18 + c 18 * c 36 * sc_cm v 0) +
        (c 20 * sc_cm v 34 + c 34 * sc_cm v 20 + c 20 * c 34 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_57 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 57 =
      sc_cm v 57 +
        (c 9 * sc_cm v 48 + c 48 * sc_cm v 9 + c 9 * c 48 * sc_cm v 0) -
        (c 17 * sc_cm v 40 + c 40 * sc_cm v 17 + c 17 * c 40 * sc_cm v 0) +
        (c 24 * sc_cm v 33 + c 33 * sc_cm v 24 + c 24 * c 33 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_58 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 58 =
      sc_cm v 58 +
        (c 10 * sc_cm v 48 + c 48 * sc_cm v 10 + c 10 * c 48 * sc_cm v 0) -
        (c 18 * sc_cm v 40 + c 40 * sc_cm v 18 + c 18 * c 40 * sc_cm v 0) +
        (c 24 * sc_cm v 34 + c 34 * sc_cm v 24 + c 24 * c 34 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

theorem ig_phi_cm_60 (c : ℕ → F) (v : S F 3) :
    sc_cm (m F 3 ((ig_phi c : Spin F 3) : C F 3) v) 60 =
      sc_cm v 60 +
        (c 12 * sc_cm v 48 + c 48 * sc_cm v 12 + c 12 * c 48 * sc_cm v 0) -
        (c 20 * sc_cm v 40 + c 40 * sc_cm v 20 + c 20 * c 40 * sc_cm v 0) +
        (c 24 * sc_cm v 36 + c 36 * sc_cm v 24 + c 24 * c 36 * sc_cm v 0) := by
  ig_cm_simp [ig_phi, sc_m_mul, ig_cm_xp]
  ring

/-- `ψ_Y(μ)` in degree `0`, on a spinor without degree-`2` part: `α' = α - N(Y) (3μ² + βμ³)`. -/
theorem ig_psi_cm0 (μ : F) (v : S F 3) (hX : ∀ k ∈ ig_D2, sc_cm v k = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 0 =
      sc_cm v 0 - ig_N (sc_cm v) * (3 * μ ^ 2 + sc_cm v 63 * μ ^ 3) := by
  have h3 := hX 3 (by decide)
  have h5 := hX 5 (by decide)
  have h6 := hX 6 (by decide)
  have h9 := hX 9 (by decide)
  have h10 := hX 10 (by decide)
  have h12 := hX 12 (by decide)
  have h17 := hX 17 (by decide)
  have h18 := hX 18 (by decide)
  have h20 := hX 20 (by decide)
  have h24 := hX 24 (by decide)
  have h33 := hX 33 (by decide)
  have h34 := hX 34 (by decide)
  have h36 := hX 36 (by decide)
  have h40 := hX 40 (by decide)
  have h48 := hX 48 (by decide)
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h3, h5, h6, h9, h10, h12, h17, h18, h20, h24, h33, h34,
    h36, h40, h48]
  unfold ig_N
  ring

/-- `ψ_Y(μ)` at the degree-`2` mask `3` (and below at the other fourteen masks), on a spinor
whose coordinate at the mask vanishes. -/
theorem ig_psi_cm_3 (μ : F) (v : S F 3) (h : sc_cm v 3 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 3 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 3 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_5 (μ : F) (v : S F 3) (h : sc_cm v 5 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 5 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 5 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_6 (μ : F) (v : S F 3) (h : sc_cm v 6 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 6 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 6 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_9 (μ : F) (v : S F 3) (h : sc_cm v 9 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 9 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 9 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_10 (μ : F) (v : S F 3) (h : sc_cm v 10 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 10 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 10 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_12 (μ : F) (v : S F 3) (h : sc_cm v 12 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 12 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 12 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_17 (μ : F) (v : S F 3) (h : sc_cm v 17 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 17 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 17 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_18 (μ : F) (v : S F 3) (h : sc_cm v 18 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 18 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 18 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_20 (μ : F) (v : S F 3) (h : sc_cm v 20 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 20 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 20 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_24 (μ : F) (v : S F 3) (h : sc_cm v 24 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 24 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 24 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_33 (μ : F) (v : S F 3) (h : sc_cm v 33 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 33 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 33 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_34 (μ : F) (v : S F 3) (h : sc_cm v 34 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 34 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 34 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_36 (μ : F) (v : S F 3) (h : sc_cm v 36 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 36 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 36 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_40 (μ : F) (v : S F 3) (h : sc_cm v 40 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 40 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 40 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

theorem ig_psi_cm_48 (μ : F) (v : S F 3) (h : sc_cm v 48 = 0) :
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) 48 =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) 48 := by
  ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm, h]
  simp only [ig_T]
  ring

/-- `ψ_Y(μ)` in degree `2`, on a spinor without degree-`2` part: `X' = μ(2 + βμ) Y^#`. -/
theorem ig_psi_cm2 (μ : F) (v : S F 3) (hX : ∀ k ∈ ig_D2, sc_cm v k = 0) : ∀ k ∈ ig_D2,
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) k =
      μ * (2 + sc_cm v 63 * μ) * ig_T (sc_cm v) k := by
  intro k hk
  simp only [ig_D2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  exacts [ig_psi_cm_3 μ v (hX 3 (by decide)), ig_psi_cm_5 μ v (hX 5 (by decide)),
    ig_psi_cm_6 μ v (hX 6 (by decide)), ig_psi_cm_9 μ v (hX 9 (by decide)),
    ig_psi_cm_10 μ v (hX 10 (by decide)), ig_psi_cm_12 μ v (hX 12 (by decide)),
    ig_psi_cm_17 μ v (hX 17 (by decide)), ig_psi_cm_18 μ v (hX 18 (by decide)),
    ig_psi_cm_20 μ v (hX 20 (by decide)), ig_psi_cm_24 μ v (hX 24 (by decide)),
    ig_psi_cm_33 μ v (hX 33 (by decide)), ig_psi_cm_34 μ v (hX 34 (by decide)),
    ig_psi_cm_36 μ v (hX 36 (by decide)), ig_psi_cm_40 μ v (hX 40 (by decide)),
    ig_psi_cm_48 μ v (hX 48 (by decide))]

/-- `ψ_Y(μ)` in degree `4`: `Y' = (1 + βμ) Y`. -/
theorem ig_psi_cm4 (μ : F) (v : S F 3) : ∀ k ∈ ig_D4,
    sc_cm (m F 3 ((ig_psiY μ (sc_cm v) : Spin F 3) : C F 3) v) k =
      (1 + sc_cm v 63 * μ) * sc_cm v k := by
  intro k hk
  simp only [ig_D4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  all_goals
    ig_cm_simp [ig_psiY, sc_m_mul, ig_cm_xm]
    ring

end IGProducts

/-! ## Helpers: `φ(-X'/α')` kills the degrees `2` and `4` after `ψ_Y(μ)` -/

section IGVanish

variable {F : Type*} [Field F] [CharZero F]

/-- `φ(-X/x_∅)` kills the degree-`2` part. -/
theorem ig_vanish2 (v : S F 3) (h0 : sc_cm v 0 ≠ 0) : ∀ k ∈ ig_D2,
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) k = 0 := by
  intro k hk
  rw [ig_phi_cm2 _ _ k hk, ig_killX]
  linear_combination (-sc_cm v k) * mul_inv_cancel₀ h0

/-- After `ψ_Y(μ)` (degree `2` part `μ(2 + βμ) Y^#`, degree `4` part `(1 + βμ) Y`), the
elements `φ(-X'/α')` kill the coordinate at the degree-`4` mask `15` (and below at the
other fourteen masks) when `1 + βμ + μ²(2 + βμ)² N/α' = 0`. -/
theorem ig_vanish_15 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 15 = (1 + y 63 * μ) * y 15) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 15 = 0 := by
  rw [ig_phi_cm_15]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 5 (by decide), h2 6 (by decide), h2 9 (by decide), h2 10 (by decide),
    h2 12 (by decide)]
  linear_combination y 15 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_15 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 15 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_23 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 23 = (1 + y 63 * μ) * y 23) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 23 = 0 := by
  rw [ig_phi_cm_23]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 5 (by decide), h2 6 (by decide), h2 17 (by decide),
    h2 18 (by decide), h2 20 (by decide)]
  linear_combination y 23 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_23 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 23 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_27 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 27 = (1 + y 63 * μ) * y 27) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 27 = 0 := by
  rw [ig_phi_cm_27]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 9 (by decide), h2 10 (by decide), h2 17 (by decide),
    h2 18 (by decide), h2 24 (by decide)]
  linear_combination y 27 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_27 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 27 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_29 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 29 = (1 + y 63 * μ) * y 29) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 29 = 0 := by
  rw [ig_phi_cm_29]
  simp only [ig_killX]
  rw [h4, h2 5 (by decide), h2 9 (by decide), h2 12 (by decide), h2 17 (by decide),
    h2 20 (by decide), h2 24 (by decide)]
  linear_combination y 29 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_29 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 29 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_30 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 30 = (1 + y 63 * μ) * y 30) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 30 = 0 := by
  rw [ig_phi_cm_30]
  simp only [ig_killX]
  rw [h4, h2 6 (by decide), h2 10 (by decide), h2 12 (by decide), h2 18 (by decide),
    h2 20 (by decide), h2 24 (by decide)]
  linear_combination y 30 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_30 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 30 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_39 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 39 = (1 + y 63 * μ) * y 39) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 39 = 0 := by
  rw [ig_phi_cm_39]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 5 (by decide), h2 6 (by decide), h2 33 (by decide),
    h2 34 (by decide), h2 36 (by decide)]
  linear_combination y 39 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_39 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 39 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_43 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 43 = (1 + y 63 * μ) * y 43) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 43 = 0 := by
  rw [ig_phi_cm_43]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 9 (by decide), h2 10 (by decide), h2 33 (by decide),
    h2 34 (by decide), h2 40 (by decide)]
  linear_combination y 43 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_43 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 43 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_45 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 45 = (1 + y 63 * μ) * y 45) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 45 = 0 := by
  rw [ig_phi_cm_45]
  simp only [ig_killX]
  rw [h4, h2 5 (by decide), h2 9 (by decide), h2 12 (by decide), h2 33 (by decide),
    h2 36 (by decide), h2 40 (by decide)]
  linear_combination y 45 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_45 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 45 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_46 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 46 = (1 + y 63 * μ) * y 46) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 46 = 0 := by
  rw [ig_phi_cm_46]
  simp only [ig_killX]
  rw [h4, h2 6 (by decide), h2 10 (by decide), h2 12 (by decide), h2 34 (by decide),
    h2 36 (by decide), h2 40 (by decide)]
  linear_combination y 46 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_46 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 46 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_51 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 51 = (1 + y 63 * μ) * y 51) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 51 = 0 := by
  rw [ig_phi_cm_51]
  simp only [ig_killX]
  rw [h4, h2 3 (by decide), h2 17 (by decide), h2 18 (by decide), h2 33 (by decide),
    h2 34 (by decide), h2 48 (by decide)]
  linear_combination y 51 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_51 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 51 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_53 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 53 = (1 + y 63 * μ) * y 53) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 53 = 0 := by
  rw [ig_phi_cm_53]
  simp only [ig_killX]
  rw [h4, h2 5 (by decide), h2 17 (by decide), h2 20 (by decide), h2 33 (by decide),
    h2 36 (by decide), h2 48 (by decide)]
  linear_combination y 53 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_53 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 53 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_54 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 54 = (1 + y 63 * μ) * y 54) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 54 = 0 := by
  rw [ig_phi_cm_54]
  simp only [ig_killX]
  rw [h4, h2 6 (by decide), h2 18 (by decide), h2 20 (by decide), h2 34 (by decide),
    h2 36 (by decide), h2 48 (by decide)]
  linear_combination y 54 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_54 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 54 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_57 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 57 = (1 + y 63 * μ) * y 57) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 57 = 0 := by
  rw [ig_phi_cm_57]
  simp only [ig_killX]
  rw [h4, h2 9 (by decide), h2 17 (by decide), h2 24 (by decide), h2 33 (by decide),
    h2 40 (by decide), h2 48 (by decide)]
  linear_combination y 57 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_57 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 57 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_58 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 58 = (1 + y 63 * μ) * y 58) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 58 = 0 := by
  rw [ig_phi_cm_58]
  simp only [ig_killX]
  rw [h4, h2 10 (by decide), h2 18 (by decide), h2 24 (by decide), h2 34 (by decide),
    h2 40 (by decide), h2 48 (by decide)]
  linear_combination y 58 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_58 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 58 * (sc_cm v 0)⁻¹ * hinv

theorem ig_vanish_60 (v : S F 3) (y : ℕ → F) (μ : F) (hinv : sc_cm v 0 * (sc_cm v 0)⁻¹ = 1)
    (hsc : 1 + y 63 * μ + (sc_cm v 0)⁻¹ * (μ * (2 + y 63 * μ)) ^ 2 * ig_N y = 0)
    (h2 : ∀ k ∈ ig_D2, sc_cm v k = μ * (2 + y 63 * μ) * ig_T y k)
    (h4 : sc_cm v 60 = (1 + y 63 * μ) * y 60) :
    sc_cm (m F 3 ((ig_phi (ig_killX v) : Spin F 3) : C F 3) v) 60 = 0 := by
  rw [ig_phi_cm_60]
  simp only [ig_killX]
  rw [h4, h2 12 (by decide), h2 20 (by decide), h2 24 (by decide), h2 36 (by decide),
    h2 40 (by decide), h2 48 (by decide)]
  linear_combination y 60 * hsc +
    ((sc_cm v 0)⁻¹ ^ 2 * sc_cm v 0 - 2 * (sc_cm v 0)⁻¹) * (μ * (2 + y 63 * μ)) ^ 2 * ig_adj_60 y -
    (μ * (2 + y 63 * μ)) ^ 2 * ig_N y * y 60 * (sc_cm v 0)⁻¹ * hinv

end IGVanish

/-! ## Helpers: `J` on the reduced forms, Igusa's scaling, and the change of sign -/

section IGEnd

variable {F : Type*} [Field F] [CharZero F]

/-- `J` of a spinor without degree-`2` part: `J = α N(Y) - ¼ (αβ)²`. -/
theorem ig_J_red (w : S F 3) (hX : ∀ k ∈ ig_D2, sc_cm w k = 0) :
    J F w = sc_cm w 0 * ig_N (sc_cm w) - 1 / 4 * (sc_cm w 0 * sc_cm w 63) ^ 2 := by
  have h3 := hX 3 (by decide)
  have h5 := hX 5 (by decide)
  have h6 := hX 6 (by decide)
  have h9 := hX 9 (by decide)
  have h10 := hX 10 (by decide)
  have h12 := hX 12 (by decide)
  have h17 := hX 17 (by decide)
  have h18 := hX 18 (by decide)
  have h20 := hX 20 (by decide)
  have h24 := hX 24 (by decide)
  have h33 := hX 33 (by decide)
  have h34 := hX 34 (by decide)
  have h36 := hX 36 (by decide)
  have h40 := hX 40 (by decide)
  have h48 := hX 48 (by decide)
  rw [sc_J_eqM]
  unfold sc_JcM ig_N
  simp only [h3, h5, h6, h9, h10, h12, h17, h18, h20, h24, h33, h34, h36, h40, h48]
  ring

/-- `J(a + b [pt_X]) = -¼ (ab)²`. -/
theorem ig_J_line (a b : F) : J F (a • 1 + b • pt F 3) = -(1 / 4) * (a * b) ^ 2 := by
  rw [sc_J_eqM]
  unfold sc_JcM
  simp (disch := decide) only [sc_cm_add, sc_cm_smul, ig_cm_one_zero, ig_cm_pt_top, ig_cm_one_ne,
    ig_cm_pt_ne]
  ring

/-- Igusa's element `s(r)` for `f₁, e₁` maps `a + b [pt_X]` to `ra + r⁻¹ b [pt_X]`. -/
theorem ig_m_hd_line (r : F) (hr : r ≠ 0) (a b : F) :
    m F 3 ((sc_hd (by norm_num) r hr : Spin F 3) : C F 3) (a • 1 + b • pt F 3) =
      (r * a) • 1 + (r⁻¹ * b) • pt F 3 := by
  rw [sc_m_hd]
  have h1 : ExteriorAlgebra.ι F (e F 3 0) * (a • 1 + b • pt F 3) =
      a • ExteriorAlgebra.ι F (e F 3 0) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, sc_ι_mul_pt, smul_zero, add_zero]
  have h2 : D F 3 (f F 3 0) (ExteriorAlgebra.ι F (e F 3 0)) = 1 := by
    change contractLeft (f F 3 0) (ι (0 : QuadraticForm F (H1 F 3)) (e F 3 0)) = 1
    rw [contractLeft_ι]
    simp [f, e]
  rw [h1, map_smul, h2]
  module

/-- The Weyl element `v₁ v₂ v₃ v₄ v₅ v₆`, `v_a = f_a + e_a` (a product of three Weyl generators). -/
noncomputable def ig_wfl : Spin F 3 := sc_wp 0 1 * (sc_wp 2 3 * sc_wp 4 5)

/-- `v₁ ⋯ v₆ · 1 = [pt_X]`. -/
theorem ig_wfl_one : m F 3 ((ig_wfl : Spin F 3) : C F 3) 1 = pt F 3 := by
  have hz := sc_m_mem_Splus (ig_wfl : Spin F 3) (sc_one_mem_Splus (F := F) (n := 3))
  rw [ig_eq_of_cm _ hz]
  · have h0 : sc_cm (m F 3 ((ig_wfl : Spin F 3) : C F 3) 1) 0 = 0 := by
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_one]
    have h63 : sc_cm (m F 3 ((ig_wfl : Spin F 3) : C F 3) 1) 63 = 1 := by
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_one]
    rw [h0, h63, zero_smul, zero_add, one_smul]
  all_goals
    intro k hk
    simp only [ig_D2, ig_D4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_one]

/-- `v₁ ⋯ v₆ · [pt_X] = -1`. -/
theorem ig_wfl_pt : m F 3 ((ig_wfl : Spin F 3) : C F 3) (pt F 3) = -1 := by
  have hz := sc_m_mem_Splus (ig_wfl : Spin F 3) (sc_pt_mem_Splus (F := F) (n := 3))
  rw [ig_eq_of_cm _ hz]
  · have h0 : sc_cm (m F 3 ((ig_wfl : Spin F 3) : C F 3) (pt F 3)) 0 = -1 := by
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_pt]
    have h63 : sc_cm (m F 3 ((ig_wfl : Spin F 3) : C F 3) (pt F 3)) 63 = 0 := by
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_pt]
    rw [h0, h63, zero_smul, add_zero, neg_one_smul]
  all_goals
    intro k hk
    simp only [ig_D2, ig_D4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      ig_cm_simp [ig_wfl, sc_m_mul, sc_m_wp, ig_cm_vW, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
        neg_zero, ig_cm_pt]

/-- The change of sign `1 + c [pt_X] ↦ 1 - c [pt_X]` (`c ≠ 0`): the Weyl element `v₁ ⋯ v₆`, then
Igusa's element `s(-c⁻¹)`. -/
theorem ig_flip (c : F) (hc : c ≠ 0) :
    ∃ g : Spin F 3, m F 3 (g : C F 3) (1 + c • pt F 3) = 1 + (-c) • pt F 3 := by
  have hr : -c⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
  refine ⟨sc_hd (by norm_num) (-c⁻¹) hr * ig_wfl, ?_⟩
  rw [sc_m_mul, map_add, map_smul, ig_wfl_one, ig_wfl_pt]
  have h : pt F 3 + c • (-1 : S F 3) = (-c) • 1 + (1 : F) • pt F 3 := by module
  rw [h, ig_m_hd_line, show -c⁻¹ * -c = 1 by field_simp, one_smul, inv_neg, inv_inv, mul_one]

end IGEnd

/-! ## The reduction to the plane of `1` and `[pt_X]` -/

section IGCore

variable {F : Type*} [Field F] [CharZero F]

/-- **The core reduction.** Let `w ∈ S⁺` have `w_∅ ≠ 0` and no degree-`2` part, and let `σ ≠ 0`
with `σ² = -J(w)` and `w_∅ w_top + 2σ ≠ 0`. For `μ = -2 w_∅ / (w_∅ w_top + 2σ)`, the element
`φ(-X'/α') ψ_Y(μ)` maps `w` into the plane of `1` and `[pt_X]`. -/
theorem ig_core (w : S F 3) (hw : w ∈ Splus F 3) (hα : sc_cm w 0 ≠ 0)
    (hX : ∀ k ∈ ig_D2, sc_cm w k = 0) (σ : F) (hσ : σ ≠ 0) (hσJ : σ ^ 2 = -J F w)
    (hden : sc_cm w 0 * sc_cm w 63 + 2 * σ ≠ 0) :
    ∃ (g : Spin F 3) (a b : F), m F 3 (g : C F 3) w = a • 1 + b • pt F 3 := by
  have hJ := ig_J_red w hX
  -- `μ` is a root of `N μ² + αβ μ + α = 0`, and `2 + βμ ≠ 0`
  obtain ⟨μ, hμdef⟩ : ∃ μ : F, μ = -2 * sc_cm w 0 / (sc_cm w 0 * sc_cm w 63 + 2 * σ) :=
    ⟨_, rfl⟩
  have hμD : μ * (sc_cm w 0 * sc_cm w 63 + 2 * σ) = -2 * sc_cm w 0 := by
    rw [hμdef]
    exact div_mul_cancel₀ _ hden
  have hμ : ig_N (sc_cm w) * μ ^ 2 + sc_cm w 0 * sc_cm w 63 * μ + sc_cm w 0 = 0 := by
    have key : (ig_N (sc_cm w) * μ ^ 2 + sc_cm w 0 * sc_cm w 63 * μ + sc_cm w 0) *
        (sc_cm w 0 * sc_cm w 63 + 2 * σ) ^ 2 = 0 := by
      linear_combination (ig_N (sc_cm w) * (μ * (sc_cm w 0 * sc_cm w 63 + 2 * σ) -
        2 * sc_cm w 0) + sc_cm w 0 * sc_cm w 63 * (sc_cm w 0 * sc_cm w 63 + 2 * σ)) * hμD +
        4 * sc_cm w 0 * hσJ - 4 * sc_cm w 0 * hJ
    exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 hden)
  have h2 : 2 + sc_cm w 63 * μ ≠ 0 := by
    intro h
    have h4 : (2 + sc_cm w 63 * μ) * (sc_cm w 0 * sc_cm w 63 + 2 * σ) = 4 * σ := by
      linear_combination sc_cm w 63 * hμD
    rw [h, zero_mul] at h4
    exact hσ (by linear_combination -h4 / 4)
  -- the step `ψ_Y(μ)`: `α' = α (2 + βμ)²`
  obtain ⟨w₂, hw₂⟩ : ∃ x : S F 3, x = m F 3 ((ig_psiY μ (sc_cm w) : Spin F 3) : C F 3) w :=
    ⟨_, rfl⟩
  have e0 := ig_psi_cm0 μ w hX
  have e2 := ig_psi_cm2 μ w hX
  have e4 := ig_psi_cm4 μ w
  rw [← hw₂] at e0 e2 e4
  have hv0 : sc_cm w₂ 0 = sc_cm w 0 * (2 + sc_cm w 63 * μ) ^ 2 := by
    linear_combination e0 - (3 + sc_cm w 63 * μ) * hμ
  have hv0' : sc_cm w₂ 0 ≠ 0 := by
    rw [hv0]
    exact mul_ne_zero hα (pow_ne_zero 2 h2)
  have hinv : sc_cm w₂ 0 * (sc_cm w₂ 0)⁻¹ = 1 := mul_inv_cancel₀ hv0'
  have hsc : 1 + sc_cm w 63 * μ + (sc_cm w₂ 0)⁻¹ * (μ * (2 + sc_cm w 63 * μ)) ^ 2 *
      ig_N (sc_cm w) = 0 := by
    have hαi : sc_cm w 0 * (sc_cm w 0)⁻¹ = 1 := mul_inv_cancel₀ hα
    have h2i : (2 + sc_cm w 63 * μ) ^ 2 * ((2 + sc_cm w 63 * μ) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero 2 h2)
    rw [hv0, mul_inv]
    linear_combination (sc_cm w 0)⁻¹ * hμ - (1 + sc_cm w 63 * μ) * hαi +
      (sc_cm w 0)⁻¹ * μ ^ 2 * ig_N (sc_cm w) * h2i
  -- the step `φ(-X'/α')`
  obtain ⟨w₃, hw₃⟩ : ∃ x : S F 3, x = m F 3 ((ig_phi (ig_killX w₂) : Spin F 3) : C F 3) w₂ :=
    ⟨_, rfl⟩
  have hw₃S : w₃ ∈ Splus F 3 := by
    rw [hw₃, hw₂]
    exact sc_m_mem_Splus _ (sc_m_mem_Splus _ hw)
  have v2 : ∀ k ∈ ig_D2, sc_cm w₃ k = 0 := by
    rw [hw₃]
    exact ig_vanish2 w₂ hv0'
  have v4 : ∀ k ∈ ig_D4, sc_cm w₃ k = 0 := by
    rw [hw₃]
    intro k hk
    simp only [ig_D4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [ig_vanish_15 w₂ (sc_cm w) μ hinv hsc e2 (e4 15 (by decide)),
      ig_vanish_23 w₂ (sc_cm w) μ hinv hsc e2 (e4 23 (by decide)),
      ig_vanish_27 w₂ (sc_cm w) μ hinv hsc e2 (e4 27 (by decide)),
      ig_vanish_29 w₂ (sc_cm w) μ hinv hsc e2 (e4 29 (by decide)),
      ig_vanish_30 w₂ (sc_cm w) μ hinv hsc e2 (e4 30 (by decide)),
      ig_vanish_39 w₂ (sc_cm w) μ hinv hsc e2 (e4 39 (by decide)),
      ig_vanish_43 w₂ (sc_cm w) μ hinv hsc e2 (e4 43 (by decide)),
      ig_vanish_45 w₂ (sc_cm w) μ hinv hsc e2 (e4 45 (by decide)),
      ig_vanish_46 w₂ (sc_cm w) μ hinv hsc e2 (e4 46 (by decide)),
      ig_vanish_51 w₂ (sc_cm w) μ hinv hsc e2 (e4 51 (by decide)),
      ig_vanish_53 w₂ (sc_cm w) μ hinv hsc e2 (e4 53 (by decide)),
      ig_vanish_54 w₂ (sc_cm w) μ hinv hsc e2 (e4 54 (by decide)),
      ig_vanish_57 w₂ (sc_cm w) μ hinv hsc e2 (e4 57 (by decide)),
      ig_vanish_58 w₂ (sc_cm w) μ hinv hsc e2 (e4 58 (by decide)),
      ig_vanish_60 w₂ (sc_cm w) μ hinv hsc e2 (e4 60 (by decide))]
  refine ⟨ig_phi (ig_killX w₂) * ig_psiY μ (sc_cm w), sc_cm w₃ 0, sc_cm w₃ 63, ?_⟩
  rw [sc_m_mul, ← hw₂, ← hw₃]
  exact ig_eq_of_cm w₃ hw₃S v2 v4

end IGCore

/-! ## The normal form -/

/-- **[Igusa, Prop. 3], last paragraph of the proof** (the normal form), over every field of
characteristic `0`: if `w ∈ S⁺_F`, `s ∈ F`, `s ≠ 0` and `s² = -J(w)`, then some `g ∈ Spin(V_F)`
maps `w` to `1 + 2s [pt_X]`. (`J(1 + 2s [pt_X]) = -s²`, so the hypothesis says that `w` and the
normal form have the same `J`.) -/
theorem igusa_prop3_normalForm_general (F : Type*) [Field F] [CharZero F] (w : S F 3)
    (hw : w ∈ Splus F 3) (s : F) (hs : s ≠ 0) (hsJ : s ^ 2 = -J F w) :
    ∃ g : Spin F 3, m F 3 (g : C F 3) w = 1 + (2 * s) • pt F 3 := by
  -- `w ≠ 0`, as `J(0) = 0`
  have hw0 : w ≠ 0 := by
    rintro rfl
    have hJ0 : J F (0 : S F 3) = 0 := by
      have h := J_smul F 0 (0 : S F 3)
      rwa [zero_smul, zero_pow (by norm_num), zero_mul] at h
    rw [hJ0, neg_zero] at hsJ
    exact hs (pow_eq_zero_iff two_ne_zero |>.mp hsJ)
  -- move `w` into the big cell (Weyl elements), then kill its degree-`2` part (root elements)
  obtain ⟨s₁, -, hs₁⟩ := sc_exists_weyl_ne w hw hw0
  obtain ⟨u, -, hu0, hP, -⟩ := sc_bigcell_aux (m F 3 (s₁ : C F 3) w) hs₁
    (Finset.univ.powersetCard 2) (fun K hK => (Finset.mem_powersetCard.mp hK).2)
  obtain ⟨w₁, hw₁⟩ : ∃ x : S F 3, x = m F 3 ((u * s₁ : Spin F 3) : C F 3) w := ⟨_, rfl⟩
  have hw₁m : w₁ = m F 3 (u : C F 3) (m F 3 (s₁ : C F 3) w) := by rw [hw₁, sc_m_mul]
  have hw₁S : w₁ ∈ Splus F 3 := by
    rw [hw₁]
    exact sc_m_mem_Splus _ hw
  have hJ₁ : J F w₁ = J F w := by rw [hw₁, igusa_prop3_invariant]
  have hα : sc_cm w₁ 0 ≠ 0 := by
    have h0 : sc_ofMask 0 = (∅ : Finset (Fin (2 * 3))) := by decide
    unfold sc_cm
    rw [h0, hw₁m, hu0]
    exact hs₁
  have hX : ∀ k ∈ ig_D2, sc_cm w₁ k = 0 := by
    intro k hk
    unfold sc_cm
    rw [hw₁m]
    exact hP _ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ig_card_D2 k hk⟩)
  -- the square root `σ = ±s` of `-J(w)` with `αβ + 2σ ≠ 0`
  obtain ⟨σ, hσ, hσs, hden⟩ : ∃ σ : F, σ ≠ 0 ∧ σ ^ 2 = s ^ 2 ∧
      sc_cm w₁ 0 * sc_cm w₁ 63 + 2 * σ ≠ 0 := by
    by_cases h : sc_cm w₁ 0 * sc_cm w₁ 63 + 2 * s = 0
    · refine ⟨-s, neg_ne_zero.mpr hs, by ring, fun h' => hs ?_⟩
      linear_combination (h - h') / 4
    · exact ⟨s, hs, rfl, h⟩
  obtain ⟨g, a, b, hg⟩ := ig_core w₁ hw₁S hα hX σ hσ (by rw [hσs, hsJ, hJ₁]) hden
  -- `J(a + b [pt_X]) = -¼ (ab)²` determines `ab` up to sign
  have hab : (a * b) ^ 2 = (2 * s) ^ 2 := by
    have h := ig_J_line (F := F) a b
    rw [← hg, igusa_prop3_invariant, hJ₁] at h
    linear_combination 4 * h - 4 * hsJ
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_pow two_ne_zero, eq_comm, pow_eq_zero_iff two_ne_zero,
      mul_eq_zero] at hab
    rcases hab with h | h
    · exact two_ne_zero h
    · exact hs h
  -- scale to `1 + ab [pt_X]` (Igusa's element `s(a⁻¹)`), and change the sign if `ab = -2s`
  have hsc := ig_m_hd_line a⁻¹ (inv_ne_zero ha) a b
  rw [inv_mul_cancel₀ ha, inv_inv, one_smul] at hsc
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hab with hpos | hneg
  · refine ⟨sc_hd (by norm_num) a⁻¹ (inv_ne_zero ha) * (g * (u * s₁)), ?_⟩
    rw [sc_m_mul, sc_m_mul, ← hw₁, hg, hsc, hpos]
  · have hc : a * b ≠ 0 := by
      rw [hneg]
      exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero hs)
    obtain ⟨g', hg'⟩ := ig_flip (a * b) hc
    refine ⟨g' * (sc_hd (by norm_num) a⁻¹ (inv_ne_zero ha) * (g * (u * s₁))), ?_⟩
    rw [sc_m_mul, sc_m_mul, sc_m_mul, ← hw₁, hg, hsc, hg', hneg, neg_neg]

/-- **[Igusa, Prop. 3]** (orbits over `ℂ`): for `c ≠ 0` the fiber `J⁻¹(c) ⊆ S⁺_ℂ` is a single
`Spin(V_ℂ)`-orbit. Used in the proof of Lemma 10.1.1 (l. 9702: "the complement
`S⁺_ℂ ∖ Ṽ(J)` intersects each fiber of `J : S⁺_ℂ → ℂ` in a single `Spin(V_ℂ)`-orbit"). -/
theorem igusa_prop3_orbit_complex (x y : S ℂ 3)
    (hx : x ∈ Splus ℂ 3) (hy : y ∈ Splus ℂ 3) (hxy : J ℂ x = J ℂ y) (hx0 : J ℂ x ≠ 0) :
    ∃ g : Spin ℂ 3, m ℂ 3 (g : C ℂ 3) x = y := by
  -- both are in the orbit of the normal form `1 + 2s [pt_X]`, `s² = -J(x)`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (-J ℂ x)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, neg_eq_zero] at hs
    exact hx0 hs
  obtain ⟨gx, hgx⟩ := igusa_prop3_normalForm_general ℂ x hx s hs0 (by rw [hs, sq])
  obtain ⟨gy, hgy⟩ := igusa_prop3_normalForm_general ℂ y hy s hs0 (by rw [← hxy, hs, sq])
  refine ⟨gy⁻¹ * gx, ?_⟩
  rw [sc_m_mul, hgx, ← hgy, fnd_m_inv_m]

/-- **[Igusa, Prop. 3], last paragraph of the proof**, in the case used in the proof of
Lemma 10.2.1 (l. 9792): for `w ∈ S⁺_ℚ` with `d := J(w) > 0` and `K = ℚ(√-d)` there is
`g ∈ Spin(V_K)` with `g(w) = 1 + 2√-d [pt_X]` (with the paper's `√-d = i√d`,
`WeilClasses.Kd.sqrtNeg`). -/
theorem igusa_prop3_normalForm (w : S ℚ 3) (hw : w ∈ Splus ℚ 3)
    (hd : 0 < J ℚ w) :
    ∃ g : Spin (Kd (J ℚ w)) 3,
      m (Kd (J ℚ w)) 3 (g : C (Kd (J ℚ w)) 3) (bcS ℚ (Kd (J ℚ w)) 3 w) =
        1 + (2 * Kd.sqrtNeg (J ℚ w)) • pt (Kd (J ℚ w)) 3 := by
  -- `(√-d)² = -d = -J(w)` in `K`, and `w ∈ S⁺_K`; apply the normal form over `K`
  have hsq : Kd.sqrtNeg (J ℚ w) ^ 2 = -J (Kd (J ℚ w)) (bcS ℚ (Kd (J ℚ w)) 3 w) := by
    rw [J_bcS]
    apply Subtype.ext
    have hq : ((algebraMap ℚ (Kd (J ℚ w)) (J ℚ w) : Kd (J ℚ w)) : ℂ) = ((J ℚ w : ℚ) : ℂ) := by
      rw [eq_ratCast (algebraMap ℚ (Kd (J ℚ w))) (J ℚ w), SubfieldClass.coe_ratCast]
    rw [Subfield.coe_neg, hq, SubmonoidClass.coe_pow]
    exact sqrtNeg_sq hd.le
  have hs0 : Kd.sqrtNeg (J ℚ w) ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, J_bcS, eq_comm, neg_eq_zero, map_eq_zero] at hsq
    exact hd.ne' hsq
  exact igusa_prop3_normalForm_general (Kd (J ℚ w)) (bcS ℚ (Kd (J ℚ w)) 3 w)
    (sc_bcS_Splus ℚ (Kd (J ℚ w)) w hw) _ hs0 hsq

end WeilClasses
