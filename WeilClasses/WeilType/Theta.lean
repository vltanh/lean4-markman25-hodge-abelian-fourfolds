module

public import WeilClasses.WeilType.Basic
public import WeilClasses.External.Chevalley.Sec2_4
public import WeilClasses.Hodge.Ample
public import WeilClasses.PureSpinor.Lemma2_2_1

/-!
# The oriented `K`-secant `P_Θ` of an ample class; Proposition 2.4.4 (paper §2.4)

The second half of §2.4 of the paper (TeX lines 1310–1432). Let `Θ ∈ H²(X, ℚ) = ⋀² H¹(X, ℚ)` be an
ample class (`WeilClasses.IsAmple`) and `d > 0`, `K = ℚ(√-d)`:

* `θ : H¹(X, ℚ)* → H¹(X, ℚ)`, contraction with `Θ` (2.4.3) (`WeilClasses.thetaMap`; its extensions
  `WeilClasses.thetaExt`); it is an isomorphism of Hodge structures;
* `u = √-d Θ ∈ S_K` and the element `exp(u) ∈ Spin(V_K)` (`WeilClasses.expUSpin`, by
  [Chevalley, III.1.7]), which acts on `S_K` by cup product with `exp(u)` and on `V_K` by (2.4.4);
* the oriented rational `K`-secant `P_Θ` with `ℓ̃₁ = K exp(u)` (`WeilClasses.PTheta`), its plane
  (2.4.5) `P = span{Re exp(u), Im exp(u)/√d}`, and its maximal isotropic subspaces (2.4.6);
  `W₁ ∩ W₂ = 0`; `P_Θ` satisfies Assumption 2.4.1;
* Proposition 2.4.4 (`g_P` negative definite), for the complex structure `I_{V_ℝ}` of `X × X̂` in
  the paper's convention (`productStructure`).

## The contraction `θ`

`θ(y) = y ⌋ Θ` is contraction from the left (`WeilClasses.contractOne`), and
`Θ(y, y') := ⟪Θ, y ∧ y'⟫ = y'(θ(y))` (`WeilClasses.eval2`). This is the reading for which (2.4.4)
and (2.4.6) hold (`W₁ = ker m_{exp u} = {(-√-d θ(y), y)}`), and for which the proof of Lemma 3.1.3
gives `H((0, yᵢ), (0, yⱼ)) = d √-d Θ(yᵢ, yⱼ)`; we checked these three formulas numerically.

## Coefficients

The paper takes `d` a positive integer and `Θ ∈ H^{1,1}(X, ℤ)`; all statements here only use
`d ∈ ℚ`, `d > 0`, and `Θ` rational. The geometric identification of `-θ` with the differential of
the isogeny `φ_L : X → X̂` (footnote, [BL, Lemma 2.4.5, 3.6.4, Cor. 2.4.6]) is not formalized.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers: coordinates, base change, contraction, conjugation (prefix `s24b_`) -/

section S24bBC
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] in
theorem s24b_e_eq (i : Fin (2 * n)) : e F n i = Pi.basisFun F (Fin (2 * n)) i := by
  simp [e]

omit [CharZero F] in
theorem s24b_dual_ext {y y' : Module.Dual F (H1 F n)} (h : ∀ i, y (e F n i) = y' (e F n i)) :
    y = y' :=
  (Pi.basisFun F (Fin (2 * n))).ext fun i => by simpa [s24b_e_eq] using h i

omit [CharZero F] in
theorem s24b_dual_apply (y : Module.Dual F (H1 F n)) (w : H1 F n) :
    y w = ∑ i, w i * y (e F n i) := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ y w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  ext j
  simp [e, Pi.single_apply, eq_comm]

theorem s24b_bcDual_apply (y : Module.Dual F (H1 F n)) (w : H1 F' n) :
    bcDual F F' n y w = ∑ i, algebraMap F F' (y (e F n i)) * w i := by
  simp [bcDual, f, Finset.sum_apply, Algebra.smul_def]

theorem s24b_bcDual_bcH1 (y : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n y (bcH1 F F' n w) = algebraMap F F' (y w) := by
  rw [s24b_bcDual_apply, s24b_dual_apply F n y w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [bcH1, mul_comm]

omit [CharZero F] [CharZero F'] in
theorem s24b_bcH1_e (i : Fin (2 * n)) : bcH1 F F' n (e F n i) = e F' n i := by
  ext j
  simp only [bcH1, e, LinearMap.compLeft_apply, Function.comp_apply, Pi.single_apply]
  split_ifs <;> simp

theorem s24b_bcDual_e (y : Module.Dual F (H1 F n)) (i : Fin (2 * n)) :
    bcDual F F' n y (e F' n i) = algebraMap F F' (y (e F n i)) := by
  rw [← s24b_bcH1_e F F' n i, s24b_bcDual_bcH1]

omit [CharZero F] in
theorem s24b_f_e (i j : Fin (2 * n)) : f F n i (e F n j) = if i = j then 1 else 0 := by
  simp [f, e, Pi.single_apply]

theorem s24b_bcDual_f (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  apply s24b_dual_ext
  intro j
  rw [s24b_bcDual_e, s24b_f_e, s24b_f_e]
  split_ifs <;> simp

omit [CharZero F] [CharZero F'] in
theorem s24b_bcH1_injective : Function.Injective (bcH1 F F' n) := by
  intro w w' h
  ext i
  have := congrFun h i
  simpa [bcH1] using this

theorem s24b_bcDual_injective : Function.Injective (bcDual F F' n) := by
  intro y y' h
  apply s24b_dual_ext
  intro i
  have := congrArg (fun z => z (e F' n i)) h
  simpa [s24b_bcDual_e] using this

omit [CharZero F] [CharZero F'] in
theorem s24b_bcS_ι (w : H1 F n) : bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) := by
  exact ExteriorAlgebra.lift_ι_apply (R := F) _ _ w

omit [CharZero F] [CharZero F'] in
theorem s24b_bcS_ιMulti (k : ℕ) (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simp [List.map_ofFn, Function.comp_def, s24b_bcS_ι]

omit [CharZero F] in
theorem s24b_basisS_apply' (J : Finset (Fin (2 * n))) (k : ℕ) (h : J.card = k) :
    basisS F n J = ExteriorAlgebra.ιMulti F k (fun i => e F n (J.orderEmbOfFin h i)) := by
  rw [basisS, ExteriorAlgebra.basis_apply_ofCard _ h]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.basisFun_apply, e]
  rfl

omit [CharZero F] in
theorem s24b_basisS_apply (J : Finset (Fin (2 * n))) :
    basisS F n J = ExteriorAlgebra.ιMulti F J.card
      (fun i => e F n (J.orderEmbOfFin rfl i)) :=
  s24b_basisS_apply' F n J _ rfl

omit [CharZero F] [CharZero F'] in
theorem s24b_bcS_basisS (J : Finset (Fin (2 * n))) : bcS F F' n (basisS F n J) = basisS F' n J := by
  rw [s24b_basisS_apply, s24b_basisS_apply, s24b_bcS_ιMulti]
  congr 1
  ext1 i
  simp [s24b_bcH1_e]

omit [CharZero F] in
theorem s24b_basisS_empty : basisS F n ∅ = 1 := by
  rw [s24b_basisS_apply' F n ∅ 0 Finset.card_empty]
  exact ExteriorAlgebra.ιMulti_zero_apply _

omit [CharZero F] in
theorem s24b_basisS_singleton (i : Fin (2 * n)) : basisS F n {i} = ExteriorAlgebra.ι F (e F n i) := by
  rw [s24b_basisS_apply' F n {i} 1 (Finset.card_singleton i)]
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
    Finset.orderEmbOfFin_singleton]

omit [CharZero F] [CharZero F'] in
theorem s24b_repr_bcS (s : S F n) (J : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n s) J = algebraMap F F' ((basisS F n).repr s J) := by
  conv_lhs => rw [← (basisS F n).sum_repr s]
  rw [map_sum]
  simp only [map_smul, s24b_bcS_basisS]
  rw [map_sum]
  simp only [← algebraMap_smul (A := F') (R := F), map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Algebra.smul_def]

omit [CharZero F] [CharZero F'] in
theorem s24b_bcS_injective : Function.Injective (bcS F F' n) := by
  intro s t h
  apply (basisS F n).repr.injective
  ext J
  have := congrArg (fun x => (basisS F' n).repr x J) h
  simp only [s24b_repr_bcS] at this
  exact (algebraMap F F').injective this

omit [CharZero F] in
theorem s24b_coord_ι (w : H1 F n) (i : Fin (2 * n)) :
    (basisS F n).coord {i} (ExteriorAlgebra.ι F w) = w i := by
  have hw : w = ∑ j, w j • e F n j := by
    ext k
    simp [e, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum, map_sum]
  simp only [map_smul, ← s24b_basisS_singleton, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Finset.singleton_inj]

omit [CharZero F] in
theorem s24b_coord_algebraMap (c : F) :
    (basisS F n).coord ∅ (algebraMap F (S F n) c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ← s24b_basisS_empty, Module.Basis.coord_apply,
    Module.Basis.repr_self]
  simp

end S24bBC

section S24bContr
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] in
theorem s24b_D_ι (y : Module.Dual F (H1 F n)) (w : H1 F n) :
    D F n y (ExteriorAlgebra.ι F w) = algebraMap F (S F n) (y w) :=
  contractLeft_ι _ _ w

theorem s24b_D_bcS (y : Module.Dual F (H1 F n)) (ξ : S F n) :
    D F' n (bcDual F F' n y) (bcS F F' n ξ) = bcS F F' n (D F n y ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, contractLeft_algebraMap, AlgHom.commutes, map_zero]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    have h1 : bcS F F' n (CliffordAlgebra.ι 0 m * x) =
        ExteriorAlgebra.ι F' (bcH1 F F' n m) * bcS F F' n x := by
      rw [map_mul]
      congr 1
      exact s24b_bcS_ι F F' n m
    rw [h1]
    simp only [D] at hx ⊢
    rw [contractLeft_ι_mul, contractLeft_ι_mul, hx, map_sub, map_smul, map_mul,
      s24b_bcDual_bcH1, algebraMap_smul]
    congr 2
    exact (s24b_bcS_ι F F' n m).symm

omit [CharZero F] in
theorem s24b_contractOne_apply (ξ : S F n) (y : Module.Dual F (H1 F n)) (i : Fin (2 * n)) :
    contractOne F n ξ y i = (basisS F n).coord {i} (D F n y ξ) := rfl

theorem s24b_contractOne_bcS (ξ : S F n) (y : Module.Dual F (H1 F n)) :
    contractOne F' n (bcS F F' n ξ) (bcDual F F' n y) = bcH1 F F' n (contractOne F n ξ y) := by
  ext i
  rw [s24b_contractOne_apply, s24b_D_bcS, Module.Basis.coord_apply, s24b_repr_bcS]
  rfl

theorem s24b_eval2_bcS (ξ : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F' n (bcS F F' n ξ) (bcDual F F' n a) (bcDual F F' n b) =
      algebraMap F F' (eval2 F n ξ a b) := by
  simp only [eval2]
  rw [s24b_D_bcS, s24b_D_bcS, Module.Basis.coord_apply, s24b_repr_bcS]
  rfl

theorem s24b_eval2_eq (ξ : S F n) (hξ : ξ ∈ ⋀[F]^2 (H1 F n)) (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ a b = b (contractOne F n ξ a) := by
  rw [eval2, ← ι_contractOne F n ξ hξ a, s24b_D_ι, s24b_coord_algebraMap]

theorem s24b_eval2_swap (ξ : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ a b = -eval2 F n ξ b a := by
  simp only [eval2, D]
  rw [contractLeft_comm, map_neg]

end S24bContr

section S24bKd
variable (d : ℚ)

theorem s24b_coe_algebraMap (q : ℚ) : ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := by
  simp

theorem s24b_coe_sqrtNeg : ((Kd.sqrtNeg d : Kd d) : ℂ) = Complex.I * (Real.sqrt d : ℂ) := rfl

theorem s24b_ratPart_spec (z : Kd d) : ((Kd.ratPart d z : ℚ) : ℝ) = (z : ℂ).re :=
  Classical.choose_spec (Kd.exists_ratPart d z)

theorem s24b_ratPart_eq (z : Kd d) (a : ℚ) (h : (z : ℂ).re = a) : Kd.ratPart d z = a := by
  have := s24b_ratPart_spec d z
  exact_mod_cast this.trans h

theorem s24b_ratPart_algebraMap (q : ℚ) : Kd.ratPart d (algebraMap ℚ (Kd d) q) = q :=
  s24b_ratPart_eq d _ q (by simp)

theorem s24b_ratPart_sqrtNeg : Kd.ratPart d (Kd.sqrtNeg d) = 0 :=
  s24b_ratPart_eq d _ 0 (by simp [s24b_coe_sqrtNeg])

theorem s24b_sqrtNegCoeff_apply (z : Kd d) :
    Kd.sqrtNegCoeff d z = -(d⁻¹) * Kd.ratPart d (z * Kd.sqrtNeg d) := by
  simp [Kd.sqrtNegCoeff]

theorem s24b_re_mul_sqrtNeg (z : Kd d) :
    ((z * Kd.sqrtNeg d : Kd d) : ℂ).re = -((z : ℂ).im * Real.sqrt d) := by
  simp [Subfield.coe_mul, s24b_coe_sqrtNeg, Complex.mul_re]

theorem s24b_sqrtNegCoeff_spec {d : ℚ} (hd : 0 < d) (z : Kd d) :
    ((Kd.sqrtNegCoeff d z : ℚ) : ℝ) * Real.sqrt d = (z : ℂ).im := by
  rw [s24b_sqrtNegCoeff_apply]
  push_cast
  rw [s24b_ratPart_spec, s24b_re_mul_sqrtNeg]
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  linear_combination (z : ℂ).im * hs

theorem s24b_sqrtNegCoeff_eq {d : ℚ} (hd : 0 < d) (z : Kd d) (b : ℚ)
    (h : (z : ℂ).im = b * Real.sqrt d) : Kd.sqrtNegCoeff d z = b := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have := s24b_sqrtNegCoeff_spec hd z
  rw [h] at this
  exact_mod_cast mul_right_cancel₀ hs.ne' this

theorem s24b_sqrtNegCoeff_algebraMap {d : ℚ} (hd : 0 < d) (q : ℚ) :
    Kd.sqrtNegCoeff d (algebraMap ℚ (Kd d) q) = 0 :=
  s24b_sqrtNegCoeff_eq hd _ 0 (by simp)

theorem s24b_sqrtNegCoeff_sqrtNeg {d : ℚ} (hd : 0 < d) : Kd.sqrtNegCoeff d (Kd.sqrtNeg d) = 1 :=
  s24b_sqrtNegCoeff_eq hd _ 1 (by simp [s24b_coe_sqrtNeg])

theorem s24b_ratPart_mul {d : ℚ} (hd : 0 < d) (z w : Kd d) :
    Kd.ratPart d (z * w) =
      Kd.ratPart d z * Kd.ratPart d w - d * Kd.sqrtNegCoeff d z * Kd.sqrtNegCoeff d w := by
  apply s24b_ratPart_eq
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have h1 := s24b_ratPart_spec d z
  have h2 := s24b_ratPart_spec d w
  have h3 := s24b_sqrtNegCoeff_spec hd z
  have h4 := s24b_sqrtNegCoeff_spec hd w
  rw [Subfield.coe_mul, Complex.mul_re, ← h1, ← h2, ← h3, ← h4]
  push_cast
  linear_combination (-(Kd.sqrtNegCoeff d z : ℝ) * (Kd.sqrtNegCoeff d w)) * hs

theorem s24b_sqrtNegCoeff_mul {d : ℚ} (hd : 0 < d) (z w : Kd d) :
    Kd.sqrtNegCoeff d (z * w) =
      Kd.ratPart d z * Kd.sqrtNegCoeff d w + Kd.sqrtNegCoeff d z * Kd.ratPart d w := by
  apply s24b_sqrtNegCoeff_eq hd
  have h1 := s24b_ratPart_spec d z
  have h2 := s24b_ratPart_spec d w
  have h3 := s24b_sqrtNegCoeff_spec hd z
  have h4 := s24b_sqrtNegCoeff_spec hd w
  rw [Subfield.coe_mul, Complex.mul_im, ← h1, ← h2, ← h3, ← h4]
  push_cast
  ring

theorem s24b_sqrtNeg_mul_self {d : ℚ} (hd : 0 ≤ d) :
    Kd.sqrtNeg d * Kd.sqrtNeg d = algebraMap ℚ (Kd d) (-d) := by
  apply Subtype.ext
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd)
  simp only [Subfield.coe_mul, s24b_coe_sqrtNeg, s24b_coe_algebraMap]
  have : (Complex.I * (Real.sqrt d : ℂ)) * (Complex.I * (Real.sqrt d : ℂ)) =
      Complex.I * Complex.I * ((Real.sqrt d * Real.sqrt d : ℝ) : ℂ) := by push_cast; ring
  rw [this, hs, Complex.I_mul_I]
  push_cast
  ring

theorem s24b_sqrtNeg_ne_zero {d : ℚ} (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := congrArg (fun z : Kd d => (z : ℂ).im) h
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  simp [s24b_coe_sqrtNeg] at this
  exact hs.ne' this

theorem s24b_σ_sqrtNeg : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp [s24b_coe_sqrtNeg]

theorem s24b_σ_algebraMap (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp

theorem s24b_σ_σ (x : Kd d) : Kd.σ d (Kd.σ d x) = x := by
  apply Subtype.ext
  simp

end S24bKd

section S24bGrade
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] [CharZero F'] in
theorem s24b_bcS_mem_exteriorPower {k : ℕ} {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    bcS F F' n s ∈ ⋀[F']^k (H1 F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [s24b_bcS_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' k ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, ← algebraMap_smul (A := F')]
    exact Submodule.smul_mem _ _ hx

omit [CharZero F] in
theorem s24b_exteriorPower_eq_bot {k : ℕ} (hk : 2 * n < k) : ⋀[F]^k (H1 F n) = ⊥ := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_eq_bot]
  rintro _ ⟨v, rfl⟩
  apply AlternatingMap.map_linearDependent
  intro hv
  have := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
  omega

omit [CharZero F] in
theorem s24b_pow_eq_zero {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) : u ^ (2 * n + 1) = 0 := by
  have h : u ^ (2 * n + 1) ∈ ⋀[F]^((2 * n + 1) • 2) (H1 F n) :=
    SetLike.pow_mem_graded (2 * n + 1) hu
  rw [s24b_exteriorPower_eq_bot F n (by simp; omega)] at h
  exact (Submodule.mem_bot F).mp h

omit [CharZero F] in
theorem s24b_isNilpotent {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) : IsNilpotent u :=
  ⟨_, s24b_pow_eq_zero F n hu⟩

omit [CharZero F] in
theorem s24b_mul_eq_zero_of_mem {k l : ℕ} {s t : S F n} (hs : s ∈ ⋀[F]^k (H1 F n))
    (ht : t ∈ ⋀[F]^l (H1 F n)) (hkl : 2 * n < k + l) : s * t = 0 := by
  have h : s * t ∈ ⋀[F]^(k + l) (H1 F n) := SetLike.mul_mem_graded hs ht
  rw [s24b_exteriorPower_eq_bot F n hkl] at h
  exact (Submodule.mem_bot F).mp h

omit [CharZero F] in
theorem s24b_algebraMapInv_eq_zero {k : ℕ} (hk : 0 < k) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    ExteriorAlgebra.algebraMapInv s = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

omit [CharZero F] in
theorem s24b_pt_mem : pt F n ∈ ⋀[F]^(2 * n) (H1 F n) := by
  rw [pt, s24b_basisS_apply' F n Finset.univ (2 * n) (by simp)]
  exact ExteriorAlgebra.ιMulti_range F (2 * n) ⟨_, rfl⟩

theorem s24b_exp_mul_pt {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    IsNilpotent.exp u * pt F n = pt F n := by
  rw [IsNilpotent.exp_eq_sum (s24b_pow_eq_zero F n hu), Finset.sum_mul,
    Finset.sum_range_succ']
  have h0 : u * pt F n = 0 := s24b_mul_eq_zero_of_mem F n hu (s24b_pt_mem F n) (by omega)
  have : ∀ i ∈ Finset.range (2 * n), ((i + 1).factorial : ℚ)⁻¹ • u ^ (i + 1) * pt F n = 0 := by
    intro i _
    rw [smul_mul_assoc, pow_succ, mul_assoc, h0, mul_zero, smul_zero]
  rw [Finset.sum_eq_zero this]
  simp

end S24bGrade

section S24bConj
variable {F : Type*} [Field F] [CharZero F] (c : F ≃+* F) (n : ℕ)

theorem s24b_repr_conjS (s : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F n).repr (conjS c n s) K = c ((basisS F n).repr s K) := by
  show (basisS F n).repr (∑ K, c ((basisS F n).repr s K) • basisS F n K) K = _
  rw [Module.Basis.repr_sum_self]

theorem s24b_conjS_smul (k : F) (s : S F n) : conjS c n (k • s) = c k • conjS c n s := by
  apply (basisS F n).repr.injective
  ext K
  simp [s24b_repr_conjS]

theorem s24b_ringEquiv_algebraMap (q : ℚ) : c (algebraMap ℚ F q) = algebraMap ℚ F q := by
  rw [eq_ratCast, map_ratCast]

theorem s24b_conjS_bcS (x : S ℚ n) : conjS c n (bcS ℚ F n x) = bcS ℚ F n x := by
  apply (basisS F n).repr.injective
  ext K
  rw [s24b_repr_conjS, s24b_repr_bcS, s24b_ringEquiv_algebraMap]

end S24bConj

section S24bContrSmul
variable (n : ℕ)

theorem s24b_contractOne_smul {F : Type*} [Field F] [CharZero F] (c : F) (ξ : S F n) :
    contractOne F n (c • ξ) = c • contractOne F n ξ := by
  ext y i
  simp [s24b_contractOne_apply, map_smul]

theorem s24b_contractOne_add {F : Type*} [Field F] [CharZero F] (ξ η : S F n) :
    contractOne F n (ξ + η) = contractOne F n ξ + contractOne F n η := by
  ext y i
  simp [s24b_contractOne_apply, map_add]

theorem s24b_contractOne_zero {F : Type*} [Field F] [CharZero F] :
    contractOne F n (0 : S F n) = 0 := by
  ext y i
  simp [s24b_contractOne_apply]

theorem s24b_contractOne_ι_mul_ι {F : Type*} [Field F] [CharZero F] (u v : H1 F n)
    (z : Module.Dual F (H1 F n)) :
    contractOne F n (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v) z = z u • v - z v • u := by
  ext i
  rw [s24b_contractOne_apply, D, contractLeft_ι_mul]
  change (basisS F n).coord {i} (z u • ExteriorAlgebra.ι F v -
    ExteriorAlgebra.ι F u * (D F n z (ExteriorAlgebra.ι F v))) = _
  rw [s24b_D_ι, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul, map_smul, s24b_coord_ι,
    s24b_coord_ι]
  simp [mul_comm]

end S24bContrSmul

section S24bAnn
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s24b_m_ι (v : V F n) : m F n (CliffordAlgebra.ι (Q F n) v) = cliffordOp F n v :=
  CliffordAlgebra.lift_ι_apply _ _ _

theorem s24b_mOf_one (v : V F n) : mOf F n 1 v = ExteriorAlgebra.ι F v.2 := by
  simp [mOf, s24b_m_ι, cliffordOp, L, D]

theorem s24b_ann_one : ann F n 1 = LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) := by
  ext v
  simp only [ann, LinearMap.mem_ker, s24b_mOf_one, LinearMap.mem_range, LinearMap.inl_apply]
  constructor
  · intro h
    refine ⟨v.1, ?_⟩
    have : v.2 = 0 := ExteriorAlgebra.ι_inj F v.2 0 |>.mp (by simpa using h)
    ext <;> simp [this]
  · rintro ⟨y, rfl⟩
    simp

/-- The element `exp(j(u)) ∈ Spin(V_F)` of [Chevalley, III.1.7], for `u ∈ ⋀² H¹(X, F)`. -/
noncomputable def s24b_expSpin (u : S F n) (hu : u ∈ ⋀[F]^2 (H1 F n)) : Spin F n :=
  ⟨IsNilpotent.exp (iotaX F n u), chevalley_III_1_7_mem F n u hu⟩

theorem s24b_ann_exp (u : S F n) (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    ann F n (IsNilpotent.exp u) =
      (LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n))).map
        (rho F n (s24b_expSpin F n u hu)).toLinearMap ∧
    ann F n (IsNilpotent.exp u) =
      LinearMap.range (LinearMap.prod LinearMap.id (-contractOne F n u)) := by
  have h1 : IsNilpotent.exp u = m F n (s24b_expSpin F n u hu : C F n) 1 := by
    rw [s24b_expSpin, m_exp_jH F n u hu, LinearMap.mulLeft_apply, mul_one]
  refine ⟨?_, ?_⟩
  · rw [h1, ann_m_spin, s24b_ann_one]
  · rw [h1, ann_m_spin, s24b_ann_one, ← LinearMap.range_comp]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, s24b_expSpin,
      LinearEquiv.coe_coe]
    rw [chevalley_III_1_7_rho F n u hu]
    simp

end S24bAnn

section S24bEven
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s24b_mem_Splus_of_mem_two {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    u ∈ Splus F n := by
  have h : ⋀[F]^2 (H1 F n) ≤ Splus F n := by
    rw [Splus, CliffordAlgebra.evenOdd]
    exact le_iSup (fun j : {k : ℕ // (k : ZMod 2) = 0} =>
      LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n))) ^ (j : ℕ)) ⟨2, rfl⟩
  exact h hu

theorem s24b_exp_mem_Splus {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    IsNilpotent.exp u ∈ Splus F n := by
  rw [IsNilpotent.exp_eq_sum (s24b_pow_eq_zero F n hu)]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ ?_
  have h : u ^ i ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)) (i • (0 : ZMod 2)) :=
    SetLike.pow_mem_graded i (s24b_mem_Splus_of_mem_two F n hu)
  rwa [smul_zero] at h

omit [CharZero F] in
theorem s24b_Q_inl (y : Module.Dual F (H1 F n)) : Q F n (y, 0) = 0 := by
  simp [Q, QuadraticForm.dualProd]

theorem s24b_isMaxIsotropic_exp {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    IsMaxIsotropic F n (ann F n (IsNilpotent.exp u)) := by
  rw [(s24b_ann_exp F n u hu).1]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearMap.inl_apply, rho]
    rw [spinVectorAction_map_app]
    exact s24b_Q_inl F n y
  · rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
      Subspace.dual_finrank_eq]
    simp

theorem s24b_proj_two_exp {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) 2 (IsNilpotent.exp u) = u := by
  have hk : u ^ (2 * n + 2) = 0 := pow_eq_zero_of_le (by omega) (s24b_pow_eq_zero F n hu)
  rw [IsNilpotent.exp_eq_sum hk, map_sum]
  rw [Finset.sum_eq_single 1]
  · rw [map_rat_smul, GradedAlgebra.proj_apply, pow_one,
      DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (H1 F n)) hu]
    simp
  · intro i _ hi
    have hi' : u ^ i ∈ ⋀[F]^(i • 2) (H1 F n) := SetLike.pow_mem_graded i hu
    rw [map_rat_smul, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (H1 F n)) hi' (by simp; omega),
      smul_zero]
  · intro h
    simp at h

theorem s24b_algebraMapInv_exp {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    ExteriorAlgebra.algebraMapInv (IsNilpotent.exp u) = 1 := by
  rw [IsNilpotent.map_exp (s24b_isNilpotent F n hu), s24b_algebraMapInv_eq_zero F n two_pos hu,
    IsNilpotent.exp_zero]

theorem s24b_linIndep_exp_neg {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) (hu0 : u ≠ 0) :
    LinearIndependent F ![IsNilpotent.exp u, IsNilpotent.exp (-u)] := by
  have hu' : -u ∈ ⋀[F]^2 (H1 F n) := neg_mem hu
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 : s + t = 0 := by
    have := congrArg ExteriorAlgebra.algebraMapInv hst
    rw [map_add, map_smul, map_smul, s24b_algebraMapInv_exp F n hu,
      s24b_algebraMapInv_exp F n hu', map_zero, smul_eq_mul, smul_eq_mul, mul_one,
      mul_one] at this
    exact this
  have h2 : (s - t) • u = 0 := by
    have := congrArg (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) 2) hst
    rw [map_add, map_smul, map_smul, s24b_proj_two_exp F n hu, s24b_proj_two_exp F n hu',
      map_zero] at this
    rw [sub_smul, ← this, smul_neg, sub_eq_add_neg]
  have hst' : s - t = 0 := by
    by_contra h
    exact hu0 ((smul_eq_zero.mp h2).resolve_left h)
  have hs : s = 0 := by
    have h3 : (2 : F) * s = 0 := by rw [two_mul]; nth_rewrite 2 [sub_eq_zero.mp hst']; exact h0
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
  refine ⟨hs, ?_⟩
  rw [hs, zero_add] at h0
  exact h0

end S24bEven

section S24bGraphs
variable {F : Type*} [Field F] [CharZero F] {M N : Type*} [AddCommGroup M] [Module F M]
  [AddCommGroup N] [Module F N]

theorem s24b_isCompl_graphs (T : M →ₗ[F] N) (hT : Function.Bijective T) (s : F) (hs : s ≠ 0) :
    IsCompl (LinearMap.range (LinearMap.prod LinearMap.id ((-s) • T)))
      (LinearMap.range (LinearMap.prod LinearMap.id (s • T))) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨y, rfl⟩ ⟨y', hy'⟩
    have h1 := (Prod.ext_iff.mp hy').1
    have h2 := (Prod.ext_iff.mp hy').2
    simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply,
      LinearMap.smul_apply] at h1 h2
    subst h1
    have h3 : (2 * s) • T y' = 0 := by
      rw [mul_smul, two_smul]
      nth_rewrite 1 [h2]
      rw [neg_smul, neg_add_cancel]
    have hTy : T y' = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    have hy : y' = 0 := hT.1 (by rw [hTy, map_zero])
    simp [hy]
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨y, w⟩ -
    obtain ⟨z, rfl⟩ := hT.2 w
    obtain ⟨z', rfl⟩ : ∃ z', z = s • z' := ⟨s⁻¹ • z, by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]⟩
    have h₁ : (((2 : F)⁻¹ • (y - z'), (-s) • T ((2 : F)⁻¹ • (y - z'))) : M × N) ∈
        LinearMap.range (LinearMap.prod LinearMap.id ((-s) • T)) := ⟨(2 : F)⁻¹ • (y - z'), rfl⟩
    have h₂ : (((2 : F)⁻¹ • (y + z'), s • T ((2 : F)⁻¹ • (y + z'))) : M × N) ∈
        LinearMap.range (LinearMap.prod LinearMap.id (s • T)) := ⟨(2 : F)⁻¹ • (y + z'), rfl⟩
    have key : ((y, T (s • z')) : M × N) =
        ((2 : F)⁻¹ • (y - z'), (-s) • T ((2 : F)⁻¹ • (y - z'))) +
          ((2 : F)⁻¹ • (y + z'), s • T ((2 : F)⁻¹ • (y + z'))) := by
      simp only [map_smul, map_sub, map_add, Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · module
      · module
    rw [key]
    exact Submodule.add_mem_sup h₁ h₂

theorem s24b_split_inl (s : F) (T : M →ₗ[F] N) (y : M) :
    ((y, 0) : M × N) = ((2 : F)⁻¹ • y, (-s) • T ((2 : F)⁻¹ • y)) +
      ((2 : F)⁻¹ • y, s • T ((2 : F)⁻¹ • y)) := by
  simp only [map_smul, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> module

theorem s24b_eta_inl (s c : F) (hs : s * s = -c) (T : M →ₗ[F] N) (y : M) :
    s • (((2 : F)⁻¹ • y, (-s) • T ((2 : F)⁻¹ • y)) : M × N) +
      (-s) • ((2 : F)⁻¹ • y, s • T ((2 : F)⁻¹ • y)) = (0, c • T y) := by
  simp only [map_smul, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_smul]
  constructor
  · module
  · rw [← add_smul]
    congr 1
    linear_combination -hs

theorem s24b_split_inr (s : F) (hs : s ≠ 0) (T : M →ₗ[F] N) (y : M) :
    (((0 : M), T y) : M × N) = ((-(2 * s)⁻¹) • y, (-s) • T ((-(2 * s)⁻¹) • y)) +
      ((2 * s)⁻¹ • y, s • T ((2 * s)⁻¹ • y)) := by
  simp only [map_smul, Prod.mk_add_mk, Prod.mk.injEq, smul_smul]
  constructor
  · module
  · rw [← add_smul]
    have : -s * -(2 * s)⁻¹ + s * (2 * s)⁻¹ = 1 := by field_simp; ring
    rw [this, one_smul]

theorem s24b_eta_inr (s : F) (hs : s ≠ 0) (T : M →ₗ[F] N) (y : M) :
    s • ((((-(2 * s)⁻¹) • y, (-s) • T ((-(2 * s)⁻¹) • y))) : M × N) +
      (-s) • ((2 * s)⁻¹ • y, s • T ((2 * s)⁻¹ • y)) = (-y, 0) := by
  simp only [map_smul, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_smul]
  constructor
  · rw [← add_smul]
    have : s * -(2 * s)⁻¹ + -s * (2 * s)⁻¹ = -1 := by field_simp; ring
    rw [this, neg_one_smul]
  · module

end S24bGraphs

section S24bPair
variable {F : Type*} [Field F] [CharZero F] {M : Type*} [AddCommGroup M] [Module F M]

theorem s24b_pair_re (s : F) (X Y : M) : (2 : F)⁻¹ • (X + s • Y) + (2 : F)⁻¹ • (X - s • Y) = X := by
  module

theorem s24b_pair_im (s : F) (hs : s ≠ 0) (X Y : M) :
    (2 * s)⁻¹ • (X + s • Y) + (-(2 * s)⁻¹) • (X - s • Y) = Y := by
  rw [smul_add, smul_sub, smul_smul, smul_smul, neg_mul]
  have : (2 * s)⁻¹ * s = (2 : F)⁻¹ := by field_simp
  rw [this]
  module

omit [CharZero F] in
theorem s24b_pair_comb (s a b : F) (X Y : M) :
    a • (X + s • Y) + b • (X - s • Y) = (a + b) • X + ((a - b) * s) • Y := by
  module

end S24bPair

section S24bThetaBij
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s24b_dual_eq_sum (y : Module.Dual F (H1 F n)) : y = ∑ j, y (e F n j) • f F n j := by
  apply s24b_dual_ext
  intro i
  simp [s24b_f_e]

omit [CharZero F] in
theorem s24b_H1_eq_sum (w : H1 F n) : w = ∑ j, w j • e F n j := by
  ext k
  simp [e, Pi.single_apply]

theorem s24b_contractOne_bcS_eq_sum (Θ : S ℚ n) (y : Module.Dual F (H1 F n)) :
    contractOne F n (bcS ℚ F n Θ) y =
      ∑ j, y (e F n j) • bcH1 ℚ F n (contractOne ℚ n Θ (f ℚ n j)) := by
  conv_lhs => rw [s24b_dual_eq_sum F n y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← s24b_bcDual_f ℚ F n j, s24b_contractOne_bcS]

/-- The `F`-linear extension of a bijective `θ` is bijective (its inverse is the extension of
`θ⁻¹`). -/
theorem s24b_thetaExt_bijective (Θ : S ℚ n) (hθ : Function.Bijective (contractOne ℚ n Θ)) :
    Function.Bijective (contractOne F n (bcS ℚ F n Θ)) := by
  set ψ := (LinearEquiv.ofBijective (contractOne ℚ n Θ) hθ).symm with hψ
  have hψθ : ∀ y, ψ (contractOne ℚ n Θ y) = y := fun y =>
    (LinearEquiv.ofBijective (contractOne ℚ n Θ) hθ).symm_apply_apply y
  have hθψ : ∀ w, contractOne ℚ n Θ (ψ w) = w := fun w =>
    (LinearEquiv.ofBijective (contractOne ℚ n Θ) hθ).apply_symm_apply w
  let ψF : H1 F n → Module.Dual F (H1 F n) := fun w => ∑ i, w i • bcDual ℚ F n (ψ (e ℚ n i))
  have hψF : ∀ v : H1 ℚ n, ψF (bcH1 ℚ F n v) = bcDual ℚ F n (ψ v) := by
    intro v
    simp only [ψF]
    conv_rhs => rw [s24b_H1_eq_sum ℚ n v]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← algebraMap_smul (A := F) (v i)]
    rfl
  have hlin : ∀ (c : Fin (2 * n) → F) (v : Fin (2 * n) → H1 ℚ n),
      ψF (∑ j, c j • bcH1 ℚ F n (v j)) = ∑ j, c j • ψF (bcH1 ℚ F n (v j)) := by
    intro c v
    simp only [ψF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  constructor
  · intro y y' h
    have key : ∀ y, ψF (contractOne F n (bcS ℚ F n Θ) y) = y := by
      intro y
      rw [s24b_contractOne_bcS_eq_sum, hlin]
      simp only [hψF, hψθ, s24b_bcDual_f]
      exact (s24b_dual_eq_sum F n y).symm
    rw [← key y, ← key y', h]
  · intro w
    refine ⟨ψF w, ?_⟩
    simp only [ψF, map_sum, map_smul]
    conv_rhs => rw [s24b_H1_eq_sum F n w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s24b_contractOne_bcS, hθψ, s24b_bcH1_e]

end S24bThetaBij

section S24bConjV
variable {F : Type*} [Field F] [CharZero F] (c : F ≃+* F) (n : ℕ)

omit [CharZero F] in
theorem s24b_sum_smul_f_apply (a : Fin (2 * n) → F) (j : Fin (2 * n)) :
    (∑ i, a i • f F n i) (e F n j) = a j := by
  simp [s24b_f_e]

theorem s24b_conjV_apply (v : V F n) :
    conjV c n v = (∑ i, c (v.1 (e F n i)) • f F n i, c ∘ v.2) := rfl

theorem s24b_conj_contractOne (Θ : S ℚ n) (y : Module.Dual F (H1 F n)) :
    c ∘ (contractOne F n (bcS ℚ F n Θ) y) =
      contractOne F n (bcS ℚ F n Θ) (∑ i, c (y (e F n i)) • f F n i) := by
  rw [s24b_contractOne_bcS_eq_sum, s24b_contractOne_bcS_eq_sum]
  funext k
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
    map_mul, s24b_sum_smul_f_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact s24b_ringEquiv_algebraMap c _

omit [CharZero F] in
theorem s24b_conjDual_conjDual (hc : ∀ x, c (c x) = x) (y : Module.Dual F (H1 F n)) :
    (∑ i, c ((∑ j, c (y (e F n j)) • f F n j) (e F n i)) • f F n i) = y := by
  simp only [s24b_sum_smul_f_apply, hc]
  exact (s24b_dual_eq_sum F n y).symm

theorem s24b_conjV_image_graph (hc : ∀ x, c (c x) = x) (s : F) (hs : c s = -s) (Θ : S ℚ n) :
    conjV c n '' (LinearMap.range (LinearMap.prod LinearMap.id
        ((-s) • contractOne F n (bcS ℚ F n Θ))) : Set (V F n)) =
      LinearMap.range (LinearMap.prod LinearMap.id (s • contractOne F n (bcS ℚ F n Θ))) := by
  have key : ∀ y : Module.Dual F (H1 F n),
      conjV c n (y, ((-s) • contractOne F n (bcS ℚ F n Θ)) y) =
        (∑ i, c (y (e F n i)) • f F n i,
          (s • contractOne F n (bcS ℚ F n Θ)) (∑ i, c (y (e F n i)) • f F n i)) := by
    intro y
    rw [s24b_conjV_apply]
    congr 1
    simp only [LinearMap.smul_apply]
    rw [← s24b_conj_contractOne]
    funext k
    simp [hs]
  ext v
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply]
    rw [key]
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(LinearMap.prod LinearMap.id ((-s) • contractOne F n (bcS ℚ F n Θ)))
      (∑ i, c (y (e F n i)) • f F n i), ⟨_, rfl⟩, ?_⟩
    simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply]
    rw [key, s24b_conjDual_conjDual c n hc]

end S24bConjV

section S24bDescend
variable (n : ℕ) (d : ℚ)

theorem s24b_ratPartV_bcV (w : V ℚ n) : ratPartV n d (bcV ℚ (Kd d) n w) = w := by
  show (∑ i, Kd.ratPart d ((bcV ℚ (Kd d) n w).1 (e (Kd d) n i)) • f ℚ n i,
      fun i => Kd.ratPart d ((bcV ℚ (Kd d) n w).2 i)) = w
  refine Prod.ext ?_ ?_
  · simp only [bcV, LinearMap.prodMap_apply, s24b_bcDual_e, s24b_ratPart_algebraMap]
    exact (s24b_dual_eq_sum ℚ n w.1).symm
  · funext i
    simp only [bcV, LinearMap.prodMap_apply]
    exact s24b_ratPart_algebraMap d _

theorem s24b_descend_of_eq (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n) (v w : V ℚ n)
    (h : A (bcV ℚ (Kd d) n v) = bcV ℚ (Kd d) n w) : descend n d A v = w := by
  show ratPartV n d (A (bcV ℚ (Kd d) n v)) = w
  rw [h, s24b_ratPartV_bcV]

theorem s24b_ηK_add (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {w₁ w₂ : V (Kd d) n}
    (h₁ : w₁ ∈ P.W₁) (h₂ : w₂ ∈ P.W₂) : P.ηK hW l (w₁ + w₂) = l • w₁ + Kd.σ d l • w₂ := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.coe_subtype, map_add,
    Submodule.projectionOnto_apply_of_mem_left hW h₁,
    Submodule.projectionOnto_apply_of_mem_right hW h₂,
    Submodule.projectionOnto_apply_of_mem_left hW.symm h₂,
    Submodule.projectionOnto_apply_of_mem_right hW.symm h₁]
  simp

end S24bDescend

section S24bComplexify

theorem s24b_toLin_map_bc {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {M M' : Type*} [AddCommGroup M] [Module F M] [AddCommGroup M']
    [Module F' M'] [Module F M'] [IsScalarTower F F' M'] (b : Module.Basis ι F M)
    (b' : Module.Basis ι F' M') (β : M →ₗ[F] M') (hβ : ∀ i, β (b i) = b' i) (A : M →ₗ[F] M)
    (v : M) :
    Matrix.toLin b' b' ((LinearMap.toMatrix b b A).map (algebraMap F F')) (β v) = β (A v) := by
  let L1 : M →ₗ[F] M' :=
    ((Matrix.toLin b' b' ((LinearMap.toMatrix b b A).map (algebraMap F F'))).restrictScalars F) ∘ₗ β
  let L2 : M →ₗ[F] M' := β ∘ₗ A
  have h : L1 = L2 := by
    refine b.ext fun j => ?_
    simp only [L1, L2, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      hβ, Matrix.toLin_self, Matrix.map_apply]
    conv_rhs => rw [← b.sum_repr (A (b j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hβ, algebraMap_smul, LinearMap.toMatrix_apply]
  exact LinearMap.congr_fun h v

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s24b_bcV_basisV (k : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n k) = basisV F' n k := by
  obtain ⟨k', rfl⟩ := finSumFinEquiv.surjective k
  have hd : ∀ i, (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
    intro i
    apply s24b_dual_ext
    intro j
    rw [s24b_e_eq, Module.Basis.dualBasis_apply_self, ← s24b_e_eq, s24b_f_e]
    simp [eq_comm]
  have hd' : ∀ i, (Pi.basisFun F' (Fin (2 * n))).dualBasis i = f F' n i := by
    intro i
    apply s24b_dual_ext
    intro j
    rw [s24b_e_eq, Module.Basis.dualBasis_apply_self, ← s24b_e_eq, s24b_f_e]
    simp [eq_comm]
  rcases k' with i | i
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · simp only [bcV, LinearMap.prodMap_apply, Module.Basis.prod_apply_inl_fst, hd, hd',
        s24b_bcDual_f]
    · simp only [bcV, LinearMap.prodMap_apply, Module.Basis.prod_apply_inl_snd, map_zero]
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · simp only [bcV, LinearMap.prodMap_apply, Module.Basis.prod_apply_inr_fst, map_zero]
    · simp only [bcV, LinearMap.prodMap_apply, Module.Basis.prod_apply_inr_snd,
        ← s24b_e_eq, s24b_bcH1_e]

end S24bComplexify

section S24bComplexifyR
variable (n : ℕ)

theorem s24b_complexifyV_bcV (A : Module.End ℝ (V ℝ n)) (v : V ℝ n) :
    complexifyV n A (bcV ℝ ℂ n v) = bcV ℝ ℂ n (A v) :=
  s24b_toLin_map_bc (basisV ℝ n) (basisV ℂ n) (bcV ℝ ℂ n) (s24b_bcV_basisV ℝ ℂ n) A v

theorem s24b_complexifyH1_bcH1 (A : Module.End ℝ (H1 ℝ n)) (w : H1 ℝ n) :
    complexifyH1 n A (bcH1 ℝ ℂ n w) = bcH1 ℝ ℂ n (A w) :=
  s24b_toLin_map_bc (Pi.basisFun ℝ (Fin (2 * n))) (Pi.basisFun ℂ (Fin (2 * n))) (bcH1 ℝ ℂ n)
    (fun i => by rw [← s24b_e_eq, ← s24b_e_eq, s24b_bcH1_e]) A w

theorem s24b_H1C_ext {L L' : H1 ℂ n →ₗ[ℂ] H1 ℂ n}
    (h : ∀ i, L (bcH1 ℝ ℂ n (e ℝ n i)) = L' (bcH1 ℝ ℂ n (e ℝ n i))) : L = L' :=
  (Pi.basisFun ℂ (Fin (2 * n))).ext fun i => by
    rw [← s24b_e_eq, ← s24b_bcH1_e ℝ ℂ n i]
    exact h i

theorem s24b_complexifyH1_sq (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (w : H1 ℂ n) : complexifyH1 n J (complexifyH1 n J w) = -w := by
  have h : complexifyH1 n J ∘ₗ complexifyH1 n J = -LinearMap.id := by
    apply s24b_H1C_ext
    intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, s24b_complexifyH1_bcH1,
      LinearMap.neg_apply, LinearMap.id_apply]
    rw [← Module.End.mul_apply, hJ]
    simp
  have := LinearMap.congr_fun h w
  simpa using this

theorem s24b_bcDual_comp (A : Module.End ℝ (H1 ℝ n)) (y : Module.Dual ℝ (H1 ℝ n)) :
    bcDual ℝ ℂ n (y ∘ₗ A) = bcDual ℝ ℂ n y ∘ₗ complexifyH1 n A := by
  apply s24b_dual_ext
  intro i
  rw [LinearMap.comp_apply, ← s24b_bcH1_e ℝ ℂ n i, s24b_complexifyH1_bcH1, s24b_bcDual_bcH1,
    s24b_bcDual_bcH1]
  rfl

theorem s24b_complexifyV_productStructure (J : Module.End ℝ (H1 ℝ n)) (v : V ℂ n) :
    complexifyV n (productStructure n J) v =
      (v.1 ∘ₗ complexifyH1 n J, -(complexifyH1 n J v.2)) := by
  have h : complexifyV n (productStructure n J) =
      (LinearMap.dualMap (complexifyH1 n J)).prodMap (-(complexifyH1 n J)) := by
    refine (basisV ℂ n).ext fun k => ?_
    rw [← s24b_bcV_basisV ℝ ℂ n k, s24b_complexifyV_bcV]
    simp only [productStructure, bcV, LinearMap.prodMap_apply, LinearMap.neg_apply, map_neg,
      LinearMap.dualMap_apply', s24b_bcDual_comp, s24b_complexifyH1_bcH1]
  rw [h]
  rfl

end S24bComplexifyR

section S24bHodge
variable (n : ℕ)

theorem s24b_contractOne_hodge (J : Module.End ℝ (H1 ℝ n)) (ξ : S ℂ n)
    (hξ : ξ ∈ pqPiece (H10 n J) (H01 n J) 1 1) (z : Module.Dual ℂ (H1 ℂ n)) :
    contractOne ℂ n ξ (-(z ∘ₗ complexifyH1 n J)) = complexifyH1 n J (contractOne ℂ n ξ z) := by
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hx
    have ha' : complexifyH1 n J (a 0) = Complex.I • a 0 :=
      Module.End.mem_eigenspace_iff.mp (ha 0)
    have hb' : complexifyH1 n J (b 0) = (-Complex.I) • b 0 :=
      Module.End.mem_eigenspace_iff.mp (hb 0)
    simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
      Matrix.vecTail]
    rw [s24b_contractOne_ι_mul_ι, s24b_contractOne_ι_mul_ι]
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, ha', hb', map_sub, map_smul,
      smul_eq_mul]
    module
  | zero => simp [s24b_contractOne_zero]
  | add x y _ _ hx hy => rw [s24b_contractOne_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy,
      map_add]
  | smul c x _ hx => rw [s24b_contractOne_smul, LinearMap.smul_apply, LinearMap.smul_apply, hx,
      map_smul]

theorem s24b_bcS_bcS (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Field F''] [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (x : S F n) :
    bcS F' F'' n (bcS F F' n x) = bcS F F'' n x := by
  apply (basisS F'' n).repr.injective
  ext1 K
  rw [s24b_repr_bcS, s24b_repr_bcS, s24b_repr_bcS, ← IsScalarTower.algebraMap_apply]

theorem s24b_bcDual_bcDual (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Field F''] [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (y : Module.Dual F (H1 F n)) :
    bcDual F' F'' n (bcDual F F' n y) = bcDual F F'' n y := by
  apply s24b_dual_ext
  intro i
  rw [s24b_bcDual_e, s24b_bcDual_e, s24b_bcDual_e, ← IsScalarTower.algebraMap_apply]

theorem s24b_bcH1_bcH1 (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Field F''] [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (w : H1 F n) :
    bcH1 F' F'' n (bcH1 F F' n w) = bcH1 F F'' n w := by
  ext i
  simp only [bcH1, LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
    ← IsScalarTower.algebraMap_apply]

end S24bHodge

section S24bPQ
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem s24b_pqPiece_mul (A B : Submodule R M) (p : ℕ) {x y : ExteriorAlgebra R M}
    (hx : x ∈ pqPiece A B p p) (hy : y ∈ pqPiece A B 1 1) :
    x * y ∈ pqPiece A B (p + 1) (p + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a', b', ha', hb', rfl⟩ := hy
      have key : ExteriorAlgebra.ιMulti R p a * ExteriorAlgebra.ιMulti R p b *
          (ExteriorAlgebra.ιMulti R 1 a' * ExteriorAlgebra.ιMulti R 1 b') =
          ((-1 : ℤˣ) ^ (1 * p)) • (ExteriorAlgebra.ιMulti R (p + 1) (Fin.append a a') *
            ExteriorAlgebra.ιMulti R (p + 1) (Fin.append b b')) := by
        rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
          mul_assoc, ← mul_assoc (ExteriorAlgebra.ιMulti R p b),
          ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R b a']
        simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      rw [key]
      refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, _, ?_, ?_, rfl⟩)
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]; exact ha j
        · rw [Fin.append_right]; exact ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]; exact hb j
        · rw [Fin.append_right]; exact hb' j
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem s24b_one_mem_pqPiece (A B : Submodule R M) : (1 : ExteriorAlgebra R M) ∈ pqPiece A B 0 0 :=
  Submodule.subset_span ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem s24b_pow_mem_pqPiece (A B : Submodule R M) {x : ExteriorAlgebra R M}
    (hx : x ∈ pqPiece A B 1 1) (k : ℕ) : x ^ k ∈ pqPiece A B k k := by
  induction k with
  | zero => rw [pow_zero]; exact s24b_one_mem_pqPiece A B
  | succ k ih => rw [pow_succ]; exact s24b_pqPiece_mul A B k ih hx

end S24bPQ

section S24bHodgePow
variable (n : ℕ)

theorem s24b_pow_mem_hodgeClassesX (J : Module.End ℝ (H1 ℝ n)) {Θ : S ℚ n}
    (hΘ : Θ ∈ hodgeClassesX n J 1) (k : ℕ) : Θ ^ k ∈ hodgeClassesX n J k := by
  rw [mem_hodgeClassesX_iff] at hΘ ⊢
  refine ⟨?_, ?_⟩
  · have h : Θ ^ k ∈ ⋀[ℚ]^(k • (2 * 1)) (H1 ℚ n) := SetLike.pow_mem_graded k hΘ.1
    rwa [smul_eq_mul, mul_one, mul_comm k 2] at h
  · rw [map_pow]
    exact s24b_pow_mem_pqPiece _ _ hΘ.2 k

end S24bHodgePow

section S24bProp244Infra
variable (n : ℕ)

theorem s24b_pairing_apply {F : Type*} [Field F] [CharZero F] (v v' : V F n) :
    pairing F n v v' = v.1 v'.2 + v'.1 v.2 := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q,
    QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
  ring

/-- The complex conjugate `ȳ` of `y ∈ H¹(X, ℂ)*` (coordinatewise). -/
noncomputable def s24b_conjDual (y : Module.Dual ℂ (H1 ℂ n)) : Module.Dual ℂ (H1 ℂ n) :=
  ∑ i, starRingEnd ℂ (y (e ℂ n i)) • f ℂ n i

theorem s24b_conjV_eq (v : V ℂ n) :
    conjV (starRingAut : ℂ ≃+* ℂ) n v = (s24b_conjDual n v.1, starRingEnd ℂ ∘ v.2) := rfl

theorem s24b_conjDual_e (y : Module.Dual ℂ (H1 ℂ n)) (i : Fin (2 * n)) :
    s24b_conjDual n y (e ℂ n i) = starRingEnd ℂ (y (e ℂ n i)) :=
  s24b_sum_smul_f_apply n _ i

theorem s24b_conjDual_add (y y' : Module.Dual ℂ (H1 ℂ n)) :
    s24b_conjDual n (y + y') = s24b_conjDual n y + s24b_conjDual n y' := by
  apply s24b_dual_ext
  intro i
  simp [s24b_conjDual_e]

theorem s24b_conjDual_smul (k : ℂ) (y : Module.Dual ℂ (H1 ℂ n)) :
    s24b_conjDual n (k • y) = starRingEnd ℂ k • s24b_conjDual n y := by
  apply s24b_dual_ext
  intro i
  simp [s24b_conjDual_e]

theorem s24b_conjDual_bcH1 (y : Module.Dual ℂ (H1 ℂ n)) (w : H1 ℝ n) :
    s24b_conjDual n y (bcH1 ℝ ℂ n w) = starRingEnd ℂ (y (bcH1 ℝ ℂ n w)) := by
  rw [s24b_dual_apply ℂ n (s24b_conjDual n y), s24b_dual_apply ℂ n y, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s24b_conjDual_e, map_mul]
  congr 1
  simp [bcH1]

theorem s24b_conjDual_comp (y : Module.Dual ℂ (H1 ℂ n)) (A : Module.End ℝ (H1 ℝ n)) :
    s24b_conjDual n (y ∘ₗ complexifyH1 n A) = s24b_conjDual n y ∘ₗ complexifyH1 n A := by
  apply s24b_dual_ext
  intro i
  rw [s24b_conjDual_e, LinearMap.comp_apply, LinearMap.comp_apply, ← s24b_bcH1_e ℝ ℂ n i,
    s24b_complexifyH1_bcH1, s24b_conjDual_bcH1]

theorem s24b_conj_thetaC (Θ : S ℚ n) (y : Module.Dual ℂ (H1 ℂ n)) :
    starRingEnd ℂ ∘ contractOne ℂ n (bcS ℚ ℂ n Θ) y =
      contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n y) :=
  s24b_conj_contractOne (starRingAut : ℂ ≃+* ℂ) n Θ y

theorem s24b_mem_V10_iff (J : Module.End ℝ (H1 ℝ n)) (v : V ℂ n) :
    v ∈ V10 n (productStructure n J) ↔
      v.1 ∘ₗ complexifyH1 n J = Complex.I • v.1 ∧ -(complexifyH1 n J v.2) = Complex.I • v.2 := by
  rw [V10, Module.End.mem_eigenspace_iff, s24b_complexifyV_productStructure, Prod.ext_iff]
  rfl

theorem s24b_mem_V01_iff (J : Module.End ℝ (H1 ℝ n)) (v : V ℂ n) :
    v ∈ V01 n (productStructure n J) ↔
      v.1 ∘ₗ complexifyH1 n J = (-Complex.I) • v.1 ∧
        -(complexifyH1 n J v.2) = (-Complex.I) • v.2 := by
  rw [V01, Module.End.mem_eigenspace_iff, s24b_complexifyV_productStructure, Prod.ext_iff]
  rfl

/-- `Θ(u, v) := ⟪Θ, u ∧ v⟫ = v(θ(u))` is alternating. -/
theorem s24b_theta_antisymm {F : Type*} [Field F] [CharZero F] (ξ : S F n)
    (hξ : ξ ∈ ⋀[F]^2 (H1 F n)) (u v : Module.Dual F (H1 F n)) :
    v (contractOne F n ξ u) = -u (contractOne F n ξ v) := by
  rw [← s24b_eval2_eq F n ξ hξ, ← s24b_eval2_eq F n ξ hξ, s24b_eval2_swap]

theorem s24b_conjV_graph (Θ : S ℚ n) (s : ℂ) (hs : starRingEnd ℂ s = -s)
    (u : Module.Dual ℂ (H1 ℂ n)) :
    conjV (starRingAut : ℂ ≃+* ℂ) n (u, (-s) • contractOne ℂ n (bcS ℚ ℂ n Θ) u) =
      (s24b_conjDual n u, s • contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n u)) := by
  rw [s24b_conjV_eq, ← s24b_conj_thetaC]
  congr 1
  funext k
  simp [hs]

theorem s24b_pairing_graph (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (s : ℂ)
    (u : Module.Dual ℂ (H1 ℂ n)) :
    pairing ℂ n (u, (-s) • contractOne ℂ n (bcS ℚ ℂ n Θ) u)
        (s24b_conjDual n u, s • contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n u)) =
      2 * s * u (contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n u)) := by
  rw [s24b_pairing_apply]
  simp only [map_smul, smul_eq_mul]
  rw [s24b_theta_antisymm n _ (s24b_bcS_mem_exteriorPower ℚ ℂ n hΘ) u (s24b_conjDual n u)]
  ring

theorem s24b_cross_zero (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : Θ ∈ hodgeClassesX n J 1) (ya yc : Module.Dual ℂ (H1 ℂ n))
    (haJ : ya ∘ₗ complexifyH1 n J = Complex.I • ya)
    (hcJ : yc ∘ₗ complexifyH1 n J = (-Complex.I) • yc) :
    ya (contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n yc)) = 0 ∧
      yc (contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n ya)) = 0 := by
  have hξ : bcS ℚ ℂ n Θ ∈ pqPiece (H10 n J) (H01 n J) 1 1 :=
    ((mem_hodgeClassesX_iff n J 1 Θ).mp hΘ).2
  have hbarc : s24b_conjDual n yc ∘ₗ complexifyH1 n J = Complex.I • s24b_conjDual n yc := by
    rw [← s24b_conjDual_comp, hcJ, s24b_conjDual_smul]
    simp
  have hbara : s24b_conjDual n ya ∘ₗ complexifyH1 n J = (-Complex.I) • s24b_conjDual n ya := by
    rw [← s24b_conjDual_comp, haJ, s24b_conjDual_smul]
    simp
  constructor
  · have h1 : ((ya, 0) : V ℂ n) ∈ V10 n (productStructure n J) :=
      (s24b_mem_V10_iff n J _).mpr ⟨haJ, by simp⟩
    have h2 : ((0, contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n yc)) : V ℂ n) ∈
        V10 n (productStructure n J) := by
      refine (s24b_mem_V10_iff n J _).mpr ⟨by ext; simp, ?_⟩
      simp only
      rw [← s24b_contractOne_hodge n J _ hξ, hbarc, map_neg, map_smul]
      simp
    have := V10_isotropic J hJ _ h1 _ h2
    rw [s24b_pairing_apply] at this
    simpa using this
  · have h1 : ((yc, 0) : V ℂ n) ∈ V01 n (productStructure n J) :=
      (s24b_mem_V01_iff n J _).mpr ⟨hcJ, by simp⟩
    have h2 : ((0, contractOne ℂ n (bcS ℚ ℂ n Θ) (s24b_conjDual n ya)) : V ℂ n) ∈
        V01 n (productStructure n J) := by
      refine (s24b_mem_V01_iff n J _).mpr ⟨by ext; simp, ?_⟩
      simp only
      rw [← s24b_contractOne_hodge n J _ hξ, hbara, map_neg, map_smul]
      simp
    have := V01_isotropic J hJ _ h1 _ h2
    rw [s24b_pairing_apply] at this
    simpa using this

theorem s24b_re_im (y : Module.Dual ℂ (H1 ℂ n)) :
    ∃ p q : Module.Dual ℝ (H1 ℝ n),
      y = bcDual ℝ ℂ n p + Complex.I • bcDual ℝ ℂ n q ∧
        s24b_conjDual n y = bcDual ℝ ℂ n p - Complex.I • bcDual ℝ ℂ n q := by
  refine ⟨∑ i, (y (e ℂ n i)).re • f ℝ n i, ∑ i, (y (e ℂ n i)).im • f ℝ n i, ?_, ?_⟩
  · apply s24b_dual_ext
    intro i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, s24b_bcDual_e, s24b_sum_smul_f_apply,
      smul_eq_mul, Complex.coe_algebraMap]
    apply Complex.ext <;> simp
  · apply s24b_dual_ext
    intro i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, s24b_bcDual_e, s24b_sum_smul_f_apply,
      smul_eq_mul, s24b_conjDual_e, Complex.coe_algebraMap]
    apply Complex.ext <;> simp

theorem s24b_thetaC_bcDual (Θ : S ℚ n) (u v : Module.Dual ℝ (H1 ℝ n)) :
    bcDual ℝ ℂ n v (contractOne ℂ n (bcS ℚ ℂ n Θ) (bcDual ℝ ℂ n u)) =
      ((v (contractOne ℝ n (bcS ℚ ℝ n Θ) u) : ℝ) : ℂ) := by
  rw [← s24b_bcS_bcS n ℚ ℝ ℂ, s24b_contractOne_bcS, s24b_bcDual_bcH1, Complex.coe_algebraMap]

theorem s24b_bcV_injective {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] : Function.Injective (bcV F F' n) := by
  intro v w h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [bcV, LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (s24b_bcDual_injective F F' n h1) (s24b_bcH1_injective F F' n h2)

end S24bProp244Infra

variable (n : ℕ) (d : ℚ)

/-! ## The contraction `θ` (2.4.3) -/

/-- **`θ`** (2.4.3): contraction with `Θ ∈ H²(X, ℚ)`, `θ : H¹(X, ℚ)* → H¹(X, ℚ)`,
`θ(y) = y ⌋ Θ`. -/
noncomputable abbrev thetaMap (Θ : S ℚ n) : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n :=
  contractOne ℚ n Θ

/-- The `F`-linear extension `θ : H¹(X, F)* → H¹(X, F)` of `θ` (§2.4, after (2.4.3); `F = K, ℝ, ℂ`):
contraction with `Θ ∈ H²(X, F)`. -/
noncomputable abbrev thetaExt (F : Type*) [Field F] [CharZero F] (Θ : S ℚ n) :
    Module.Dual F (H1 F n) →ₗ[F] H1 F n :=
  contractOne F n (bcS ℚ F n Θ)

/-- `thetaExt F n Θ` extends `θ`. -/
theorem thetaExt_bcDual (F : Type*) [Field F] [CharZero F] (Θ : S ℚ n)
    (y : Module.Dual ℚ (H1 ℚ n)) :
    thetaExt n F Θ (bcDual ℚ F n y) = bcH1 ℚ F n (thetaMap n Θ y) :=
  s24b_contractOne_bcS ℚ F n Θ y

/-- `Θ(y, y') = y'(θ(y))`: the pairing `⟪Θ, y ∧ y'⟫` of `WeilClasses.eval2` is the bilinear form
`Θ(yᵢ, yⱼ)` of the proof of Lemma 3.1.3. -/
theorem thetaMap_apply_eq_eval2 (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (y y' : Module.Dual ℚ (H1 ℚ n)) : y' (thetaMap n Θ y) = eval2 ℚ n Θ y y' :=
  (s24b_eval2_eq ℚ n Θ hΘ y y').symm

/-- `θ` is a morphism of Hodge structures `H¹(X̂, ℝ) = H¹(X, ℝ)* → H¹(X, ℝ)` when `Θ` is of type
`(1,1)`: it intertwines the standard complex structure `y ↦ -y ∘ J` of `H¹(X̂, ℝ) = H¹(X, ℝ)*` with
`J` (the paper's footnote in §2.4 uses the negatives `y ↦ y ∘ J` and `-J`; the statement is the
same) (§2.4, after (2.4.3): "`θ` is an isomorphism of rational Hodge structures under the
identification of `H¹(X, ℚ)*` with `H¹(X̂, ℚ)`").

Departure from the paper (the representation; reason 3): the paper identifies `-θ` with the
differential of the isogeny `φ_L : X → X̂` of the polarization ([BL, Lemma 2.4.5, 3.6.4]; footnote in
§2.4). The model has no line bundles or isogenies, so the proof checks the Hodge property directly:
`Θ` of type `(1,1)` means `Θ(a ∘ J, b ∘ J) = Θ(a, b)`, which is the intertwining identity. -/
theorem thetaExt_comp_neg_dualMap (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : Θ ∈ hodgeClassesX n J 1) :
    thetaExt n ℝ Θ ∘ₗ (-(J.dualMap)) = J ∘ₗ thetaExt n ℝ Θ := by
  have _ := hJ
  have hξ : bcS ℚ ℂ n Θ ∈ pqPiece (H10 n J) (H01 n J) 1 1 := ((mem_hodgeClassesX_iff n J 1 Θ).mp hΘ).2
  refine LinearMap.ext fun y => ?_
  apply s24b_bcH1_injective ℝ ℂ n
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.dualMap_apply', thetaExt]
  rw [← s24b_complexifyH1_bcH1, ← s24b_contractOne_bcS, ← s24b_contractOne_bcS, map_neg,
    s24b_bcDual_comp, s24b_bcS_bcS]
  exact s24b_contractOne_hodge n J _ hξ _

theorem s24b_thetaR_swap (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : Θ ∈ hodgeClassesX n J 1) (p q : Module.Dual ℝ (H1 ℝ n)) :
    (q ∘ₗ J) (contractOne ℝ n (bcS ℚ ℝ n Θ) p) = (p ∘ₗ J) (contractOne ℝ n (bcS ℚ ℝ n Θ) q) := by
  have h2 : bcS ℚ ℝ n Θ ∈ ⋀[ℝ]^2 (H1 ℝ n) :=
    s24b_bcS_mem_exteriorPower ℚ ℝ n (Submodule.mem_inf.mp hΘ).1
  have h := LinearMap.congr_fun (thetaExt_comp_neg_dualMap n J hJ Θ hΘ) p
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.dualMap_apply', map_neg,
    thetaExt] at h
  rw [LinearMap.comp_apply, ← h, map_neg, s24b_theta_antisymm n _ h2 (p ∘ₗ J) q, neg_neg]

section AmpleAPI

variable {n}

/-- An ample class has degree two. -/
theorem IsAmple.mem_exteriorPower_two {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n}
    (hΘ : IsAmple n J Θ) : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n) :=
  (Submodule.mem_inf.mp hΘ.1).1

/-- An ample class on an abelian variety of positive dimension is nonzero. -/
theorem IsAmple.ne_zero_of_pos {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ)
    (hn : 0 < n) : Θ ≠ 0 := by
  rintro rfl
  have hne : f ℝ n ⟨0, by omega⟩ ≠ 0 := by
    intro h0
    have := congrArg (fun y => y (e ℝ n ⟨0, by omega⟩)) h0
    simp [s24b_f_e] at this
  have h := hΘ.2 _ hne
  simp [eval2] at h

/-- `θ` is an isomorphism when `Θ` is ample (§2.4: "`θ` is an isomorphism of rational Hodge
structures"; used for `W₁ ∩ W₂ = 0`).

Departure from the paper (the representation; reason 3): the paper gets this from the isogeny `φ_L`
of the ample line bundle ([BL, Lemma 2.4.5]). The model has no line bundles; the proof uses
`Θ(a, a ∘ J) > 0` for `a ≠ 0` (ampleness), so `θ` is injective. -/
theorem IsAmple.bijective_thetaMap {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n}
    (hΘ : IsAmple n J Θ) : Function.Bijective (thetaMap n Θ) := by
  have hΘ2 : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n) := hΘ.mem_exteriorPower_two
  have hinj : Function.Injective (thetaMap n Θ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have ha0 : bcDual ℚ ℝ n y ≠ 0 := fun h =>
      hy0 (s24b_bcDual_injective ℚ ℝ n (by rw [h, map_zero]))
    have h := hΘ.2 _ ha0
    rw [s24b_eval2_eq ℝ n _ (s24b_bcS_mem_exteriorPower ℚ ℝ n hΘ2), LinearMap.comp_apply,
      s24b_contractOne_bcS, hy, map_zero, map_zero, map_zero] at h
    exact lt_irrefl (0 : ℝ) h
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mp hinj⟩

end AmpleAPI

/-! ## `u = √-d Θ` and `exp(u) ∈ Spin(V_K)` -/

/-- `u = √-d Θ ∈ H²(X, K) ⊆ S_K` (§2.4, before (2.4.4)). -/
noncomputable def uΘ (Θ : S ℚ n) : S (Kd d) n := Kd.sqrtNeg d • bcS ℚ (Kd d) n Θ

/-- `u = √-d Θ ∈ ⋀² H¹(X, K)` for `Θ ∈ ⋀² H¹(X, ℚ)`. -/
theorem uΘ_mem (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) : uΘ n d Θ ∈ ⋀[Kd d]^2 (H1 (Kd d) n) :=
  Submodule.smul_mem _ _ (s24b_bcS_mem_exteriorPower ℚ (Kd d) n hΘ)

/-- The class `exp(u) ∈ H^{ev}(X, K) = S⁺_K` (§2.4). -/
noncomputable def expUS (Θ : S ℚ n) : S (Kd d) n := IsNilpotent.exp (uΘ n d Θ)

/-- The element `exp(u)` of `Spin(V_K)` (§2.4, before (2.4.4)): `exp(j(u))` in `C(V_K)`, which lies
in `Spin(V_K)` by [Chevalley, III.1.7] (`WeilClasses.chevalley_III_1_7_mem`). -/
noncomputable def expUSpin (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) : Spin (Kd d) n :=
  ⟨IsNilpotent.exp (iotaX (Kd d) n (uΘ n d Θ)),
    chevalley_III_1_7_mem (Kd d) n (uΘ n d Θ) (uΘ_mem n d Θ hΘ)⟩

/-- Cup product with `exp(u)` is the spin representation image `m(exp u)` of `exp(u) ∈ Spin(V_K)`
(§2.4, before (2.4.4)). -/
theorem m_expUSpin (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) = LinearMap.mulLeft (Kd d) (expUS n d Θ) :=
  m_exp_jH (Kd d) n (uΘ n d Θ) (uΘ_mem n d Θ hΘ)

/-- **(2.4.4)** (`eq-action-of-exp-u-on-V`): `exp(u)` acts on `V_K` by
`exp(u)·(w, y) = (w - √-d θ(y), y)`, `w ∈ H¹(X, K)`, `y ∈ H¹(X̂, K) ≅ H¹(X, K)*`. In our order
`(y, w)`: `ρ(exp u)(y, w) = (y, w - √-d θ(y))`. -/
theorem equation2_4_4 (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (v : V (Kd d) n) :
    rho (Kd d) n (expUSpin n d Θ hΘ) v = (v.1, v.2 - Kd.sqrtNeg d • thetaExt n (Kd d) Θ v.1) := by
  rw [show expUSpin n d Θ hΘ = ⟨_, chevalley_III_1_7_mem (Kd d) n _ (uΘ_mem n d Θ hΘ)⟩ from rfl,
    chevalley_III_1_7_rho (Kd d) n _ (uΘ_mem n d Θ hΘ), uΘ, s24b_contractOne_smul]
  rfl

/-- `exp(u)` leaves invariant the pure spinor `[pt] ∈ H^{2n}(X, K)` (§2.4, after (2.4.4)). -/
theorem m_expUSpin_pt (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) (pt (Kd d) n) = pt (Kd d) n := by
  rw [m_expUSpin, LinearMap.mulLeft_apply, expUS]
  exact s24b_exp_mul_pt (Kd d) n (uΘ_mem n d Θ hΘ)

/-- `exp(u)` leaves invariant every element of `H¹(X, K) = 0 × H¹(X, K)` (§2.4, after (2.4.4)). -/
theorem rho_expUSpin_inr (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (w : H1 (Kd d) n) :
    rho (Kd d) n (expUSpin n d Θ hΘ) (0, w) = (0, w) := by
  rw [equation2_4_4]
  simp

/-- `exp(u)` takes the pure spinor `1` (of `H¹(X, K)*`) to the class `exp(u) ∈ H^{ev}(X, K)`
(§2.4, after (2.4.4)). -/
theorem m_expUSpin_one (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) 1 = expUS n d Θ := by
  rw [m_expUSpin, LinearMap.mulLeft_apply, mul_one]

/-! ## The oriented rational `K`-secant `P_Θ` -/

theorem s24b_σS_uΘ (Θ : S ℚ n) : σS n d (uΘ n d Θ) = -uΘ n d Θ := by
  rw [uΘ, s24b_conjS_smul, s24b_conjS_bcS, s24b_σ_sqrtNeg, neg_smul]

theorem s24b_σS_expUS (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    σS n d (expUS n d Θ) = IsNilpotent.exp (-uΘ n d Θ) := by
  rw [expUS, IsNilpotent.map_exp (s24b_isNilpotent _ n (uΘ_mem n d Θ hΘ)), s24b_σS_uΘ]

theorem s24b_uΘ_ne_zero (hd : 0 < d) (Θ : S ℚ n) (hΘ0 : Θ ≠ 0) : uΘ n d Θ ≠ 0 := by
  rw [uΘ]
  refine smul_ne_zero (s24b_sqrtNeg_ne_zero hd) ?_
  intro h
  apply hΘ0
  apply s24b_bcS_injective ℚ (Kd d) n
  rw [h, map_zero]

/-- `exp(u)` is an even pure spinor, with `ker m_{exp u} = exp(u)(H¹(X, K)*)` (§2.4). -/
theorem expUS_isEvenPureSpinor (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    IsEvenPureSpinor (Kd d) n (expUS n d Θ) :=
  ⟨s24b_exp_mem_Splus _ n (uΘ_mem n d Θ hΘ), s24b_isMaxIsotropic_exp _ n (uΘ_mem n d Θ hΘ)⟩

/-- `exp(u)` and `σ(exp u) = exp(ū)` span distinct lines when `d > 0` and `Θ ≠ 0`. -/
theorem expUS_linIndep (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    LinearIndependent (Kd d) ![expUS n d Θ, σS n d (expUS n d Θ)] := by
  rw [s24b_σS_expUS n d Θ hΘ, expUS]
  exact s24b_linIndep_exp_neg _ n (uΘ_mem n d Θ hΘ) (s24b_uΘ_ne_zero n d hd Θ hΘ0)

/-- **The oriented rational `K`-secant `P_Θ`** (§2.4, (2.4.5)): `ℓ̃₁ = span_K{exp(u)}`,
`ℓ̃₂ = span_K{exp(ū)}`, `u = √-d Θ`, oriented by the choice of `ℓ̃₁`. Its plane is (2.4.5)
(`WeilClasses.equation2_4_5`). -/
noncomputable def PTheta (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    KSecant n d where
  u₁ := expUS n d Θ
  isPure := expUS_isEvenPureSpinor n d Θ hΘ
  linIndep := expUS_linIndep n d hd Θ hΘ hΘ0

/-- `ℓ̃₂ = span_K{exp(ū)}`: `u₂ = σ(exp u) = exp(ū) = exp(-u)` (§2.4). -/
theorem PTheta_u₂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).u₂ = IsNilpotent.exp (-uΘ n d Θ) := by
  show σS n d (expUS n d Θ) = _
  exact s24b_σS_expUS n d Θ hΘ

/-- The coordinatewise map `S_K → S_ℚ` obtained by applying a `ℚ`-linear form `φ : K → ℚ` to the
coefficients in the basis `e_K`. -/
noncomputable def coeffMapS (φ : Kd d →ₗ[ℚ] ℚ) : S (Kd d) n →ₗ[ℚ] S ℚ n :=
  (basisS ℚ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun K => φ ∘ₗ ((basisS (Kd d) n).coord K).restrictScalars ℚ)

/-- The real part `Re : S_K → S_ℚ` (coefficientwise `a + b√-d ↦ a`). -/
noncomputable def reS : S (Kd d) n →ₗ[ℚ] S ℚ n := coeffMapS n d (Kd.ratPart d)

/-- `Im/√d : S_K → S_ℚ` (coefficientwise `a + b√-d ↦ b`, i.e. `Im(z)/√d`). -/
noncomputable def imS : S (Kd d) n →ₗ[ℚ] S ℚ n := coeffMapS n d (Kd.sqrtNegCoeff d)

theorem s24b_repr_coeffMapS (φ : Kd d →ₗ[ℚ] ℚ) (s : S (Kd d) n) (K : Finset (Fin (2 * n))) :
    (basisS ℚ n).repr (coeffMapS n d φ s) K = φ ((basisS (Kd d) n).repr s K) := by
  rw [coeffMapS, LinearMap.comp_apply, LinearEquiv.coe_coe, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  rfl

theorem s24b_reS_bcS (x : S ℚ n) : reS n d (bcS ℚ (Kd d) n x) = x := by
  apply (basisS ℚ n).repr.injective
  ext K
  rw [reS, s24b_repr_coeffMapS, s24b_repr_bcS, s24b_ratPart_algebraMap]

theorem s24b_reS_smul_bcS (c : Kd d) (x : S ℚ n) :
    reS n d (c • bcS ℚ (Kd d) n x) = Kd.ratPart d c • x := by
  apply (basisS ℚ n).repr.injective
  ext K
  rw [reS, s24b_repr_coeffMapS, LinearEquiv.map_smul, Finsupp.smul_apply, s24b_repr_bcS,
    LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← Algebra.commutes,
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem s24b_imS_smul_bcS (c : Kd d) (x : S ℚ n) :
    imS n d (c • bcS ℚ (Kd d) n x) = Kd.sqrtNegCoeff d c • x := by
  apply (basisS ℚ n).repr.injective
  ext K
  rw [imS, s24b_repr_coeffMapS, LinearEquiv.map_smul, Finsupp.smul_apply, s24b_repr_bcS,
    LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← Algebra.commutes,
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- `s = Re(s) + √-d · Im(s)/√d` for `s ∈ S_K` (with rational `Re(s)`, `Im(s)/√d`). -/
theorem bcS_reS_add_imS (hd : 0 < d) (s : S (Kd d) n) :
    bcS ℚ (Kd d) n (reS n d s) + Kd.sqrtNeg d • bcS ℚ (Kd d) n (imS n d s) = s := by
  apply (basisS (Kd d) n).repr.injective
  ext1 K
  rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s24b_repr_bcS, s24b_repr_bcS,
    reS, imS, s24b_repr_coeffMapS, s24b_repr_coeffMapS, smul_eq_mul]
  have := Kd.eq_ratPart_add_sqrtNegCoeff hd ((basisS (Kd d) n).repr s K)
  linear_combination -this

/-- **(2.4.5)** (`eq-P`): `P = span{Re(exp(u)), Im(exp(u))/√d}` (oriented via `ℓ̃₁`). -/
theorem equation2_4_5 (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).Pℚ =
      Submodule.span ℚ {reS n d (expUS n d Θ), imS n d (expUS n d Θ)} := by
  set A := reS n d (expUS n d Θ)
  set B := imS n d (expUS n d Θ)
  set s := Kd.sqrtNeg d
  have hu₁ : expUS n d Θ = bcS ℚ (Kd d) n A + s • bcS ℚ (Kd d) n B :=
    (bcS_reS_add_imS n d hd _).symm
  have hu₂ : (PTheta n d hd Θ hΘ hΘ0).u₂ = bcS ℚ (Kd d) n A - s • bcS ℚ (Kd d) n B := by
    show σS n d (expUS n d Θ) = _
    rw [hu₁, map_add, s24b_conjS_smul, s24b_conjS_bcS, s24b_conjS_bcS, s24b_σ_sqrtNeg, neg_smul,
      ← sub_eq_add_neg]
  have hPK : ∀ x : S ℚ n, x ∈ (PTheta n d hd Θ hΘ hΘ0).Pℚ ↔ bcS ℚ (Kd d) n x ∈
      Submodule.span (Kd d) {expUS n d Θ, (PTheta n d hd Θ hΘ hΘ0).u₂} := fun x => Iff.rfl
  apply le_antisymm
  · intro x hx
    rw [hPK] at hx
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
    have h1 : bcS ℚ (Kd d) n x =
        (a + b) • bcS ℚ (Kd d) n A + ((a - b) * s) • bcS ℚ (Kd d) n B := by
      rw [← hab, hu₁, hu₂, s24b_pair_comb]
    have h2 : x = Kd.ratPart d (a + b) • A + Kd.ratPart d ((a - b) * s) • B := by
      rw [← s24b_reS_bcS n d x, h1, map_add, s24b_reS_smul_bcS, s24b_reS_smul_bcS]
    rw [h2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, hPK, Submodule.mem_span_pair]
      exact ⟨2⁻¹, 2⁻¹, by rw [hu₁, hu₂, s24b_pair_re]⟩
    · rw [SetLike.mem_coe, hPK, Submodule.mem_span_pair]
      exact ⟨(2 * s)⁻¹, -(2 * s)⁻¹, by rw [hu₁, hu₂, s24b_pair_im s (s24b_sqrtNeg_ne_zero hd)]⟩

/-- **(2.4.6)** (`eq-W-1-and-2`), first line: `W₁ = exp(u)(H¹(X, K)*) = {(-√-d θ(y), y)}`; in our
order `(y, w)`: `W₁ = ρ(exp u)(H¹(X, K)* × 0) = {(y, -√-d θ(y)) : y ∈ H¹(X, K)*}`. -/
theorem equation2_4_6_W₁ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).W₁ =
        (LinearMap.range (LinearMap.inl (Kd d) (Module.Dual (Kd d) (H1 (Kd d) n))
          (H1 (Kd d) n))).map (rho (Kd d) n (expUSpin n d Θ hΘ) : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∧
      (PTheta n d hd Θ hΘ hΘ0).W₁ =
        LinearMap.range (LinearMap.prod LinearMap.id (-(Kd.sqrtNeg d) • thetaExt n (Kd d) Θ)) := by
  have h := s24b_ann_exp (Kd d) n (uΘ n d Θ) (uΘ_mem n d Θ hΘ)
  refine ⟨h.1, ?_⟩
  rw [show (PTheta n d hd Θ hΘ hΘ0).W₁ = ann (Kd d) n (IsNilpotent.exp (uΘ n d Θ)) from rfl, h.2,
    uΘ, s24b_contractOne_smul, neg_smul]

/-- **(2.4.6)** (`eq-W-1-and-2`), second line: `W₂ = \overline{W₁} = {(+√-d θ(y), y)}`; in our order
`W₂ = σ(W₁) = {(y, √-d θ(y)) : y ∈ H¹(X, K)*}`. -/
theorem equation2_4_6_W₂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (σV n d '' ((PTheta n d hd Θ hΘ hΘ0).W₁ : Set (V (Kd d) n)) =
        ((PTheta n d hd Θ hΘ hΘ0).W₂ : Set (V (Kd d) n))) ∧
      (PTheta n d hd Θ hΘ hΘ0).W₂ =
        LinearMap.range (LinearMap.prod LinearMap.id (Kd.sqrtNeg d • thetaExt n (Kd d) Θ)) := by
  have hW₂ : (PTheta n d hd Θ hΘ hΘ0).W₂ =
      LinearMap.range (LinearMap.prod LinearMap.id (Kd.sqrtNeg d • thetaExt n (Kd d) Θ)) := by
    show ann (Kd d) n (σS n d (expUS n d Θ)) = _
    rw [s24b_σS_expUS n d Θ hΘ, (s24b_ann_exp (Kd d) n _ (neg_mem (uΘ_mem n d Θ hΘ))).2, uΘ,
      ← neg_smul, s24b_contractOne_smul, neg_smul, neg_neg]
  refine ⟨?_, hW₂⟩
  rw [hW₂, (equation2_4_6_W₁ n d hd Θ hΘ hΘ0).2]
  exact s24b_conjV_image_graph (Kd.σ d) n (s24b_σ_σ d) (Kd.sqrtNeg d) (s24b_σ_sqrtNeg d) Θ

/-- `V_K = W₁ ⊕ W₂` for `P_Θ`: `W₁`, `W₂` are the graphs of `∓√-d θ` and `θ` is an isomorphism. -/
theorem s24b_PTheta_isCompl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) :
    IsCompl (PTheta n d hd Θ hΘ hΘ0).W₁ (PTheta n d hd Θ hΘ hΘ0).W₂ := by
  rw [(equation2_4_6_W₁ n d hd Θ hΘ hΘ0).2, (equation2_4_6_W₂ n d hd Θ hΘ hΘ0).2]
  exact s24b_isCompl_graphs _ (s24b_thetaExt_bijective (Kd d) n Θ hθ) _ (s24b_sqrtNeg_ne_zero hd)

/-- `W₁ ∩ W₂ = 0`, since `θ` is an isomorphism (§2.4, after (2.4.6)). -/
theorem PTheta_W₁_inf_W₂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) :
    (PTheta n d hd Θ hΘ hΘ0).W₁ ⊓ (PTheta n d hd Θ hΘ hΘ0).W₂ = ⊥ :=
  (s24b_PTheta_isCompl n d hd Θ hΘ hΘ0 hθ).inf_eq_bot

/-- `V_K = W₁ ⊕ W₂` for `P_Θ` when `θ` is an isomorphism. -/
theorem PTheta_isCompl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) :
    IsCompl (PTheta n d hd Θ hΘ hΘ0).W₁ (PTheta n d hd Θ hΘ hΘ0).W₂ :=
  s24b_PTheta_isCompl n d hd Θ hΘ hΘ0 hθ

theorem s24b_expUS_eq_sum (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    expUS n d Θ = ∑ k ∈ Finset.range (2 * n + 1),
      (((k.factorial : ℚ)⁻¹ • Kd.sqrtNeg d ^ k) • bcS ℚ (Kd d) n (Θ ^ k)) := by
  rw [expUS, IsNilpotent.exp_eq_sum (s24b_pow_eq_zero _ n (uΘ_mem n d Θ hΘ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [uΘ, smul_pow, map_pow, smul_assoc]

/-- `P_Θ` satisfies Assumption 2.4.1 for the complex structure `J` of `X` when `Θ` is ample for `J`
(§1.2 and §2.4: `P ⊆ ⊕_p H^{p,p}(X, ℚ)` is non-isotropic, as `W₁ ∩ W₂ = 0`). -/
theorem PTheta_assumption2_4_1 (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    Assumption2_4_1 (PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)) J where
  isComplex := hJ
  nonIsotropic := by
    rw [lemma2_2_1 _ hd, not_not]
    exact PTheta_W₁_inf_W₂ n d hd Θ _ _ hΘ.bijective_thetaMap
  hodge := by
    have hmem : ∀ k, Θ ^ k ∈ hodgeRingX n J := fun k =>
      Submodule.mem_iSup_of_mem k (s24b_pow_mem_hodgeClassesX n J hΘ.1 k)
    rw [equation2_4_5, Submodule.span_le]
    rintro _ (rfl | rfl)
    · rw [s24b_expUS_eq_sum n d Θ hΘ.mem_exteriorPower_two, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [s24b_reS_smul_bcS]
      exact Submodule.smul_mem _ _ (hmem k)
    · rw [s24b_expUS_eq_sum n d Θ hΘ.mem_exteriorPower_two, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [s24b_imS_smul_bcS]
      exact Submodule.smul_mem _ _ (hmem k)
  pos := hd

/-- The similarity `f = η_{√-d}` of `P_Θ` on `H¹(X, ℚ)* × 0` (proof of Lemma 3.1.3:
`f(0, y) = (d θ(y), 0)` in the paper's order): `f(y, 0) = (0, d θ(y))`. -/
theorem PTheta_fη_inl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).fη (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (y, 0) =
      (0, d • thetaMap n Θ y) := by
  apply s24b_descend_of_eq
  have hW₁ := (equation2_4_6_W₁ n d hd Θ hΘ hΘ0).2
  have hW₂ := (equation2_4_6_W₂ n d hd Θ hΘ hΘ0).2
  set T := thetaExt n (Kd d) Θ
  set s := Kd.sqrtNeg d
  set ŷ := bcDual ℚ (Kd d) n y
  have h₁ : (((2 : Kd d)⁻¹ • ŷ, (-s) • T ((2 : Kd d)⁻¹ • ŷ)) : V (Kd d) n) ∈
      (PTheta n d hd Θ hΘ hΘ0).W₁ := by rw [hW₁]; exact ⟨_, rfl⟩
  have h₂ : (((2 : Kd d)⁻¹ • ŷ, s • T ((2 : Kd d)⁻¹ • ŷ)) : V (Kd d) n) ∈
      (PTheta n d hd Θ hΘ hΘ0).W₂ := by rw [hW₂]; exact ⟨_, rfl⟩
  have hv : bcV ℚ (Kd d) n (y, 0) = (ŷ, 0) := by simp [bcV, ŷ]
  have hw : bcV ℚ (Kd d) n (0, d • thetaMap n Θ y) = (0, algebraMap ℚ (Kd d) d • T ŷ) := by
    simp only [bcV, LinearMap.prodMap_apply, map_zero, map_smul, algebraMap_smul, T, ŷ,
      thetaExt_bcDual]
  rw [hv, hw, s24b_split_inl s T ŷ]
  rw [s24b_ηK_add n d _ _ _ h₁ h₂, s24b_σ_sqrtNeg]
  apply s24b_eta_inl
  rw [s24b_sqrtNeg_mul_self hd.le, map_neg]

/-- The similarity `f` of `P_Θ` on `0 × H¹(X, ℚ)`: `f(0, θ(y)) = (-y, 0)` (with `f(y, 0)`, this
gives `f(y, w) = (-θ⁻¹(w), d θ(y))`). -/
theorem PTheta_fη_inr (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).fη (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (0, thetaMap n Θ y) =
      (-y, 0) := by
  apply s24b_descend_of_eq
  have hW₁ := (equation2_4_6_W₁ n d hd Θ hΘ hΘ0).2
  have hW₂ := (equation2_4_6_W₂ n d hd Θ hΘ hΘ0).2
  set T := thetaExt n (Kd d) Θ
  set s := Kd.sqrtNeg d
  set ŷ := bcDual ℚ (Kd d) n y
  have hs := s24b_sqrtNeg_ne_zero hd
  have h₁ : (((-(2 * s)⁻¹) • ŷ, (-s) • T ((-(2 * s)⁻¹) • ŷ)) : V (Kd d) n) ∈
      (PTheta n d hd Θ hΘ hΘ0).W₁ := by rw [hW₁]; exact ⟨_, rfl⟩
  have h₂ : (((2 * s)⁻¹ • ŷ, s • T ((2 * s)⁻¹ • ŷ)) : V (Kd d) n) ∈
      (PTheta n d hd Θ hΘ hΘ0).W₂ := by rw [hW₂]; exact ⟨_, rfl⟩
  have hv : bcV ℚ (Kd d) n (0, thetaMap n Θ y) = (0, T ŷ) := by
    simp only [bcV, LinearMap.prodMap_apply, map_zero, T, ŷ, thetaExt_bcDual]
  have hw : bcV ℚ (Kd d) n (-y, 0) = (-ŷ, 0) := by simp [bcV, ŷ]
  rw [hv, hw, s24b_split_inr s hs T ŷ]
  rw [s24b_ηK_add n d _ _ _ h₁ h₂, s24b_σ_sqrtNeg]
  exact s24b_eta_inr s hs T ŷ

theorem s24b_PTheta_W₁ℂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).W₁ℂ ≤ LinearMap.range (LinearMap.prod LinearMap.id
      ((-sqrtNeg d) • contractOne ℂ n (bcS ℚ ℂ n Θ))) := by
  rw [KSecant.W₁ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, (equation2_4_6_W₁ n d hd Θ hΘ hΘ0).2] at hw
  obtain ⟨y, rfl⟩ := hw
  refine ⟨bcDual (Kd d) ℂ n y, ?_⟩
  simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply, LinearMap.smul_apply,
    bcV, LinearMap.prodMap_apply]
  congr 1
  rw [map_smul, ← s24b_contractOne_bcS, s24b_bcS_bcS, ← algebraMap_smul ℂ (-Kd.sqrtNeg d)]
  rfl

/-! ## Proposition 2.4.4 -/

/-- **Proposition 2.4.4** (`prop-polarized-abelian-variety-of-Weil-type`). The symmetric bilinear
pairing `g_P` of Lemma 2.4.2 associated with the oriented plane `P` in (2.4.5) is negative
definite.

Here `X = (H¹(X, ℝ), J)`, `Θ` is ample for `J` (`WeilClasses.IsAmple`: Kähler positivity in the
convention of [Huybrechts, Lemma 1.2.15], which the proof cites), `P = P_Θ`, and
`g_P(x, y) = Ξ_P(I x, y)` on `V_ℝ` with `I = I_{V_ℝ} = productStructure n J`, the complex structure
of `X × X̂` in the paper's convention (footnote in §2.4; `productStructure`). With the standard
Hodge structure `-I` instead, `g_P` would be positive definite. The paper takes `d` a
positive integer and `Θ` integral; `0 < n` makes `P_Θ` a secant (the paper's standing assumption is
`n ≥ 2`). -/
theorem proposition2_4_4 (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) (x : V ℝ n) (hx : x ≠ 0) :
    (PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)).gP
      (PTheta_isCompl n d hd Θ _ _ hΘ.bijective_thetaMap) J x x < 0 := by
  -- The paper writes the computation for `x ∈ V_ℚ` (with `y ∈ H¹(X, K)*`); negative definiteness of
  -- the real form `g_P` needs every `x ∈ V_ℝ`, and the same computation applies with `y ∈ H¹(X, ℂ)*`.
  have hP := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  have hΘ2 := hΘ.mem_exteriorPower_two
  have hξ2 : bcS ℚ ℂ n Θ ∈ ⋀[ℂ]^2 (H1 ℂ n) := s24b_bcS_mem_exteriorPower ℚ ℂ n hΘ2
  set P := PTheta n d hd Θ hΘ2 (hΘ.ne_zero_of_pos hn) with hPdef
  -- The decomposition `x = x₁^{1,0} + x₂^{1,0} + x₁^{0,1} + x₂^{0,1}` and the conjugation rules.
  obtain ⟨⟨a, b, c, e⟩, ⟨ha, hb, hc, he, hv⟩, -⟩ := P.existsUnique_decomp_real J hP x
  dsimp only at ha hb hc he hv
  obtain ⟨hea, hcb⟩ := P.conj_decomp_real J hP x a b c e ha hb hc he hv
  -- Lemma 2.4.2.
  have hg := lemma2_4_2 P J hP x a b c e ha hb hc he hv
  -- `x₁^{1,0} = (y^{1,0}, -√-d θ(y^{1,0}))` and `x₁^{0,1} = (y^{0,1}, -√-d θ(y^{0,1}))`.
  obtain ⟨ya, rfl⟩ := s24b_PTheta_W₁ℂ n d hd Θ hΘ2 _ (Submodule.mem_inf.mp ha).1
  obtain ⟨yc, rfl⟩ := s24b_PTheta_W₁ℂ n d hd Θ hΘ2 _ (Submodule.mem_inf.mp hc).1
  have haJ := ((s24b_mem_V10_iff n J _).mp (Submodule.mem_inf.mp ha).2).1
  have hcJ := ((s24b_mem_V01_iff n J _).mp (Submodule.mem_inf.mp hc).2).1
  simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply,
    LinearMap.smul_apply] at haJ hcJ hea hcb hv hg
  set θc := contractOne ℂ n (bcS ℚ ℂ n Θ) with hθc
  have hs : starRingEnd ℂ (sqrtNeg d) = -sqrtNeg d := by simp [sqrtNeg]
  rw [s24b_conjV_graph n Θ _ hs] at hea hcb
  subst hea hcb
  rw [s24b_pairing_graph n Θ hΘ2, s24b_pairing_graph n Θ hΘ2] at hg
  -- The cross terms vanish (`V^{1,0}` and `V^{0,1}` are isotropic).
  obtain ⟨hcross1, hcross2⟩ := s24b_cross_zero n J hJ Θ hΘ.1 ya yc haJ hcJ
  rw [← hθc] at hcross1 hcross2 hg
  -- With `y = y^{1,0} + y^{0,1}` and `I(y) = y ∘ J`:
  -- `Θ(ȳ, I(y)) = i (Θ(ȳ^{1,0}, y^{1,0}) - Θ(ȳ^{0,1}, y^{0,1}))`.
  have hkey : ((ya + yc) ∘ₗ complexifyH1 n J) (θc (s24b_conjDual n (ya + yc))) =
      Complex.I * (ya (θc (s24b_conjDual n ya)) - yc (θc (s24b_conjDual n yc))) := by
    rw [LinearMap.add_comp, haJ, hcJ, s24b_conjDual_add, map_add]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, smul_eq_mul, hcross1,
      hcross2]
    ring
  -- `y = a + i b` with `a, b` real: `Θ(ȳ, I(y)) = Θ(a, I(a)) + Θ(b, I(b))`.
  obtain ⟨p, q, hy, hy'⟩ := s24b_re_im n (ya + yc)
  set θr := contractOne ℝ n (bcS ℚ ℝ n Θ) with hθr
  have hreal : ((ya + yc) ∘ₗ complexifyH1 n J) (θc (s24b_conjDual n (ya + yc))) =
      (((p ∘ₗ J) (θr p) + (q ∘ₗ J) (θr q) : ℝ) : ℂ) := by
    rw [hy', hy, LinearMap.add_comp, LinearMap.smul_comp, ← s24b_bcDual_comp, ← s24b_bcDual_comp]
    simp only [map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hθc, s24b_thetaC_bcDual]
    rw [← hθr, s24b_thetaR_swap n J hJ Θ hΘ.1 p q]
    rw [← hθr]
    push_cast
    simp only [Function.comp_apply]
    linear_combination -((q (J (θr q)) : ℝ) : ℂ) * Complex.I_mul_I
  -- `g_P(x, x) = -4d Θ(ȳ, I(y))`.
  set r : ℝ := (p ∘ₗ J) (θr p) + (q ∘ₗ J) (θr q) with hr_def
  have hgr : P.gP hP.isCompl J x x = -4 * d * r := by
    apply Complex.ofReal_injective
    rw [hg]
    have h1 : Complex.I * (ya (θc (s24b_conjDual n ya)) - yc (θc (s24b_conjDual n yc))) =
        (r : ℂ) := hkey.symm.trans hreal
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = ((d : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp only [sqrtNeg]
    push_cast at h2 ⊢
    linear_combination (-4 * Complex.I * (ya (θc (s24b_conjDual n ya)) -
      yc (θc (s24b_conjDual n yc)))) * h2 + (-4 * (d : ℂ)) * h1
  -- Positivity: `Θ` is ample.
  have hpos : ∀ u : Module.Dual ℝ (H1 ℝ n), u ≠ 0 → 0 < (u ∘ₗ J) (θr u) := by
    intro u hu
    have := hΘ.2 u hu
    rwa [s24b_eval2_eq ℝ n _ (s24b_bcS_mem_exteriorPower ℚ ℝ n hΘ2)] at this
  have hnn : ∀ u : Module.Dual ℝ (H1 ℝ n), 0 ≤ (u ∘ₗ J) (θr u) := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · exact (hpos u hu).le
  have hy0 : ya + yc ≠ 0 := by
    intro h0
    have hyc : yc = -ya := eq_neg_of_add_eq_zero_right h0
    have hya : ya = 0 := by
      rw [hyc, LinearMap.neg_comp, haJ] at hcJ
      have h2 : (2 * Complex.I) • ya = 0 := by
        rw [mul_smul, two_smul]
        nth_rewrite 2 [show Complex.I • ya = -(Complex.I • ya) by rw [hcJ]; simp]
        exact add_neg_cancel _
      exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    have hyc0 : yc = 0 := by rw [hyc, hya, neg_zero]
    apply hx
    apply s24b_bcV_injective n (F := ℝ) (F' := ℂ)
    rw [hv, map_zero, hya, hyc0]
    simp [s24b_conjDual]
  have hr : 0 < r := by
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by
        rintro rfl
        apply hy0
        rw [hy, hp]
        simp
      rw [hr_def, hp]
      simpa using hpos q hq
    · exact add_pos_of_pos_of_nonneg (hpos p hp) (hnn q)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hgr]
  nlinarith

end WeilClasses
