module

public import WeilClasses.Main.Coordinates
public import WeilClasses.PureSpinor.CM

/-!
# The abelian variety `X × X̂` of Weil type of Theorems 1.4.1 and 1.5.1, explicitly

For an abelian `n`-fold `X` with principal polarization `Θ = e₁ ∧ e₂ + ⋯ + e_{2n-1} ∧ e_{2n}`
(`ThetaStd`; for `n = 3`, the Jacobian of a genus-3 curve) and `d > 0`, the paper equips `X × X̂` with
the structure of a polarized abelian `2n`-fold of Weil type for `K = ℚ(√-d)` (§2.4, Lemma 3.1.3,
Corollary 3.2.3), from the `K`-secant spanned by the pure spinors `exp(±√-d Θ)`. In coordinates
(`V = H¹(X̂) ⊕ H¹(X)`, pairs `(y, w)`), with `θ : H¹(X)* → H¹(X)` the contraction with `Θ`
((2.4.3); `θ(f_{2i}) = e_{2i+1}`, `θ(f_{2i+1}) = -e_{2i}`):

* `η(√-d) = f`, `f(y, w) = (-θ⁻¹(w), d θ(y))` (`WeilClasses.fV`), so `η(a + b√-d) = a + b f`
  (`WeilClasses.etaV`); this is the paper's `η` of (2.2.4) for the secant `P_Θ` (compared in
  `WeilClasses.Main.Compare`);
* the polarization `h = d Θ + Θ̂ ∈ H²(X × X̂, ℚ)`, `Θ̂ = f₁ ∧ f₂ + ⋯ + f_{2n-1} ∧ f_{2n}`
  (`WeilClasses.hV`): the class of the paper's `Ξ_P` (2.4.2) under `V ≅ V*`;
* the complex structure of `X × X̂` given by a complex structure `J` of `H¹(X, ℝ)`: in the standard
  convention (`H^{1,0}` the `i`-eigenspace) it is `(y, w) ↦ (-y ∘ J, J w)` (`WeilClasses.stdStructure`),
  the negative of the paper's `I_{V_ℝ}` (`productStructure`).

`fX`, `hX`, `JX` are their transports to the model (`H¹ = ℚ^{4n}`, `coordV`). The data `fV`, `hV`,
`stdStructure`, `fX`, `hX`, `JX` are defined in `WeilClasses.Defs` (they enter the statements of
record); this file defines the action `η` itself (`etaV`, `etaX`), which the statements of record
quantify over (`η` with `η(√-d) = f`; it is unique, `eq_etaX`).
-/

@[expose] public section

namespace WeilClasses

variable (n : ℕ)

/-! ## Helpers (prefix `s24b_`): `θ` and `θ⁻¹` on basis vectors; coordinates in `K` -/

section S24bThetaStd


theorem s24b_e_apply (i j : Fin (2 * n)) : e ℚ n i j = if j = i then 1 else 0 := by
  simp [e, Pi.single_apply]

theorem s24b_f_apply (i : Fin (2 * n)) (w : H1 ℚ n) : f ℚ n i w = w i := rfl

theorem s24b_thetaStd_apply (y : Module.Dual ℚ (H1 ℚ n)) :
    thetaStd n y = ∑ i : Fin n, (y (e ℚ n ⟨2 * i, by omega⟩) • e ℚ n ⟨2 * i + 1, by omega⟩ -
      y (e ℚ n ⟨2 * i + 1, by omega⟩) • e ℚ n ⟨2 * i, by omega⟩) := by
  simp [thetaStd, LinearMap.sum_apply]

theorem s24b_thetaStdInv_apply (w : H1 ℚ n) :
    thetaStdInv n w = ∑ i : Fin n, (w ⟨2 * i + 1, by omega⟩ • f ℚ n ⟨2 * i, by omega⟩ -
      w ⟨2 * i, by omega⟩ • f ℚ n ⟨2 * i + 1, by omega⟩) := by
  simp [thetaStdInv, LinearMap.sum_apply, f]

theorem s24b_thetaStd_f_even (j : Fin n) :
    thetaStd n (f ℚ n ⟨2 * j, by omega⟩) = e ℚ n ⟨2 * j + 1, by omega⟩ := by
  rw [s24b_thetaStd_apply, Finset.sum_eq_single j]
  · simp [s24b_f_apply, s24b_e_apply]
  · intro i _ hij
    have h1 : (⟨2 * (i : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j, by omega⟩ := by
      intro h; apply hij; ext; simp at h; omega
    have h2 : (⟨2 * (j : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by
      intro h; simp at h; omega
    simp [s24b_f_apply, s24b_e_apply, Ne.symm h1, h2]
  · simp

theorem s24b_thetaStd_f_odd (j : Fin n) :
    thetaStd n (f ℚ n ⟨2 * j + 1, by omega⟩) = -e ℚ n ⟨2 * j, by omega⟩ := by
  rw [s24b_thetaStd_apply, Finset.sum_eq_single j]
  · have : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j, by omega⟩ := by
      intro h; simp at h
    simp [s24b_f_apply, s24b_e_apply, this]
  · intro i _ hij
    have h1 : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by
      intro h; apply hij; ext; simp at h; omega
    have h2 : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i, by omega⟩ := by
      intro h; simp at h; omega
    simp [s24b_f_apply, s24b_e_apply, h1, h2]
  · simp

theorem s24b_thetaStdInv_e_odd (j : Fin n) :
    thetaStdInv n (e ℚ n ⟨2 * j + 1, by omega⟩) = f ℚ n ⟨2 * j, by omega⟩ := by
  rw [s24b_thetaStdInv_apply, Finset.sum_eq_single j]
  · have : (⟨2 * (j : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j + 1, by omega⟩ := by
      intro h; simp at h
    simp [s24b_e_apply, this]
  · intro i _ hij
    have h1 : (⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j + 1, by omega⟩ := by
      intro h; apply hij; ext; simp at h; omega
    have h2 : (⟨2 * (i : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j + 1, by omega⟩ := by
      intro h; simp at h; omega
    simp [s24b_e_apply, h1, h2]
  · simp

theorem s24b_thetaStdInv_e_even (j : Fin n) :
    thetaStdInv n (e ℚ n ⟨2 * j, by omega⟩) = -f ℚ n ⟨2 * j + 1, by omega⟩ := by
  rw [s24b_thetaStdInv_apply, Finset.sum_eq_single j]
  · have : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j, by omega⟩ := by
      intro h; simp at h
    simp [s24b_e_apply, this]
  · intro i _ hij
    have h1 : (⟨2 * (i : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j, by omega⟩ := by
      intro h; apply hij; ext; simp at h; omega
    have h2 : (⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j, by omega⟩ := by
      intro h; simp at h; omega
    simp [s24b_e_apply, h1, h2]
  · simp

theorem s24b_fin_parity (k : Fin (2 * n)) :
    (∃ j : Fin n, k = ⟨2 * j, by omega⟩) ∨ (∃ j : Fin n, k = ⟨2 * j + 1, by omega⟩) := by
  obtain ⟨k, hk⟩ := k
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    exact ⟨⟨j, by omega⟩, by ext; simp; omega⟩
  · right
    exact ⟨⟨j, by omega⟩, by ext; simp; omega⟩

theorem s24b_f_eq_dualBasis (k : Fin (2 * n)) : f ℚ n k = (Pi.basisFun ℚ (Fin (2 * n))).dualBasis k := by
  ext w
  simp [f]

theorem s24b_thetaStdInv_comp_thetaStd : thetaStdInv n ∘ₗ thetaStd n = LinearMap.id := by
  refine (Pi.basisFun ℚ (Fin (2 * n))).dualBasis.ext fun k => ?_
  rw [← s24b_f_eq_dualBasis, LinearMap.comp_apply, LinearMap.id_apply]
  rcases s24b_fin_parity n k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [s24b_thetaStd_f_even, s24b_thetaStdInv_e_odd]
  · rw [s24b_thetaStd_f_odd, map_neg, s24b_thetaStdInv_e_even, neg_neg]

theorem s24b_thetaStd_comp_thetaStdInv : thetaStd n ∘ₗ thetaStdInv n = LinearMap.id := by
  refine (Pi.basisFun ℚ (Fin (2 * n))).ext fun k => ?_
  rw [show (Pi.basisFun ℚ (Fin (2 * n))) k = e ℚ n k by simp [e], LinearMap.comp_apply,
    LinearMap.id_apply]
  rcases s24b_fin_parity n k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [s24b_thetaStdInv_e_even, map_neg, s24b_thetaStd_f_odd, neg_neg]
  · rw [s24b_thetaStdInv_e_odd, s24b_thetaStd_f_even]

end S24bThetaStd

section S24bKdJ
variable (d : ℚ)

private theorem kd_ratPart_spec (z : Kd d) : ((Kd.ratPart d z : ℚ) : ℝ) = (z : ℂ).re :=
  Classical.choose_spec (Kd.exists_ratPart d z)

private theorem kd_ratPart_eq (z : Kd d) (a : ℚ) (h : (z : ℂ).re = a) : Kd.ratPart d z = a := by
  have := kd_ratPart_spec d z
  exact_mod_cast this.trans h

private theorem kd_coe_sqrtNeg : ((Kd.sqrtNeg d : Kd d) : ℂ) = Complex.I * (Real.sqrt d : ℂ) := rfl

private theorem kd_sqrtNegCoeff_spec {d : ℚ} (hd : 0 < d) (z : Kd d) :
    ((Kd.sqrtNegCoeff d z : ℚ) : ℝ) * Real.sqrt d = (z : ℂ).im := by
  have hre : ((z * Kd.sqrtNeg d : Kd d) : ℂ).re = -((z : ℂ).im * Real.sqrt d) := by
    simp [Subfield.coe_mul, kd_coe_sqrtNeg, Complex.mul_re]
  have happ : Kd.sqrtNegCoeff d z = -(d⁻¹) * Kd.ratPart d (z * Kd.sqrtNeg d) := by
    simp [Kd.sqrtNegCoeff]
  rw [happ]
  push_cast
  rw [kd_ratPart_spec, hre]
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  linear_combination (z : ℂ).im * hs

private theorem kd_sqrtNegCoeff_eq {d : ℚ} (hd : 0 < d) (z : Kd d) (b : ℚ)
    (h : (z : ℂ).im = b * Real.sqrt d) : Kd.sqrtNegCoeff d z = b := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have := kd_sqrtNegCoeff_spec hd z
  rw [h] at this
  exact_mod_cast mul_right_cancel₀ hs.ne' this

private theorem kd_ratPart_mul {d : ℚ} (hd : 0 < d) (z w : Kd d) :
    Kd.ratPart d (z * w) =
      Kd.ratPart d z * Kd.ratPart d w - d * Kd.sqrtNegCoeff d z * Kd.sqrtNegCoeff d w := by
  apply kd_ratPart_eq
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have h1 := kd_ratPart_spec d z
  have h2 := kd_ratPart_spec d w
  have h3 := kd_sqrtNegCoeff_spec hd z
  have h4 := kd_sqrtNegCoeff_spec hd w
  rw [Subfield.coe_mul, Complex.mul_re, ← h1, ← h2, ← h3, ← h4]
  push_cast
  linear_combination (-(Kd.sqrtNegCoeff d z : ℝ) * (Kd.sqrtNegCoeff d w)) * hs

private theorem kd_sqrtNegCoeff_mul {d : ℚ} (hd : 0 < d) (z w : Kd d) :
    Kd.sqrtNegCoeff d (z * w) =
      Kd.ratPart d z * Kd.sqrtNegCoeff d w + Kd.sqrtNegCoeff d z * Kd.ratPart d w := by
  apply kd_sqrtNegCoeff_eq hd
  have h1 := kd_ratPart_spec d z
  have h2 := kd_ratPart_spec d w
  have h3 := kd_sqrtNegCoeff_spec hd z
  have h4 := kd_sqrtNegCoeff_spec hd w
  rw [Subfield.coe_mul, Complex.mul_im, ← h1, ← h2, ← h3, ← h4]
  push_cast
  ring

private theorem kd_ratPart_one : Kd.ratPart d 1 = 1 :=
  kd_ratPart_eq d 1 1 (by simp)

private theorem kd_sqrtNegCoeff_one {d : ℚ} (hd : 0 < d) : Kd.sqrtNegCoeff d 1 = 0 :=
  kd_sqrtNegCoeff_eq hd 1 0 (by simp)

private theorem kd_ratPart_sqrtNeg : Kd.ratPart d (Kd.sqrtNeg d) = 0 :=
  kd_ratPart_eq d _ 0 (by simp [kd_coe_sqrtNeg])

private theorem kd_sqrtNegCoeff_sqrtNeg {d : ℚ} (hd : 0 < d) : Kd.sqrtNegCoeff d (Kd.sqrtNeg d) = 1 :=
  kd_sqrtNegCoeff_eq hd _ 1 (by simp [kd_coe_sqrtNeg])

end S24bKdJ

/-- `f² = -d`. -/
theorem fV_mul_self (d : ℚ) : fV n d * fV n d = -(d • 1) := by
  apply LinearMap.ext
  intro v
  have h1 := LinearMap.congr_fun (s24b_thetaStdInv_comp_thetaStd n) v.1
  have h2 := LinearMap.congr_fun (s24b_thetaStd_comp_thetaStdInv n) v.2
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
  simp only [fV, Module.End.mul_apply, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, map_smul, map_neg, h1, h2, LinearMap.neg_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  ext <;> simp

/-- The action `η : K → End_ℚ(V_ℚ)` of `K = ℚ(√-d)` on `H¹(X × X̂, ℚ)`: `η(a + b√-d) = a + b f`. -/
noncomputable def etaV (d : ℚ) (hd : 0 < d) : Kd d →+* Module.End ℚ (V ℚ n) where
  toFun k := Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • fV n d
  map_one' := by
    simp only [kd_ratPart_one, kd_sqrtNegCoeff_one hd, one_smul, zero_smul, add_zero]
  map_mul' x y := by
    rw [kd_ratPart_mul hd, kd_sqrtNegCoeff_mul hd]
    have hF := fV_mul_self n d
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hF]
    module
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, add_smul]
    abel

/-! ## Transport to the model `H¹ = ℚ^{4n}` -/

/-- `η` on the model `H¹(X × X̂, ℚ) = ℚ^{4n}`. -/
noncomputable def etaX (d : ℚ) (hd : 0 < d) : Kd d →+* Module.End ℚ (H1 ℚ (2 * n)) :=
  ((coordV ℚ n).conjAlgEquiv ℚ).toRingHom.comp (etaV n d hd)

/-- `η(√-d) = f` in the model. -/
theorem etaX_sqrtNeg (d : ℚ) (hd : 0 < d) : etaX n d hd (Kd.sqrtNeg d) = fX n d := by
  have h : etaV n d hd (Kd.sqrtNeg d) = fV n d := by
    show Kd.ratPart d (Kd.sqrtNeg d) • (1 : Module.End ℚ (V ℚ n)) +
      Kd.sqrtNegCoeff d (Kd.sqrtNeg d) • fV n d = fV n d
    rw [kd_ratPart_sqrtNeg, kd_sqrtNegCoeff_sqrtNeg hd, zero_smul, one_smul, zero_add]
  simp only [etaX, RingHom.coe_comp, Function.comp_apply, h]
  rfl

/-- The action of `K` with `η(√-d) = f` is unique (`K = ℚ(√-d)` is generated by `√-d`). -/
theorem eq_etaX (d : ℚ) (hd : 0 < d) (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n)))
    (hη : η (Kd.sqrtNeg d) = fX n d) : η = etaX n d hd := by
  refine RingHom.ext fun k => ?_
  rw [Kd.eq_ratPart_add_sqrtNegCoeff hd k, map_add, map_add, map_mul, map_mul,
    RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap,
    RingHom.map_rat_algebraMap, hη, etaX_sqrtNeg]

end WeilClasses
