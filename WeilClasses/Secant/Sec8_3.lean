module

public import WeilClasses.Secant.Sec8_2
public import WeilClasses.PureSpinor.Lemma2_2_7

/-!
# §8.3 up to Lemma 8.3.1: the `κ₃`-class of `Φ(F₁ ⊠ F₁)` is independent of `h³`

Statements of the paper's §8.3, TeX lines 3963–4041 (`n = 3`, the notation of Lemma 8.2.1:
`Θ = ThetaStd ℚ 3` ample for the complex structure `J` of `X`, `w = ch(F₁) = chF1 d`,
`P = span{α, β}` the plane of the `K`-secant `P_Θ` (`PJac`), `λ₁ = exp(√-dΘ) = P.u₁`,
`λ₂ = λ̄₁ = P.u₂`).

* `(α, β)_S = ∫_X τ(α) β = ∫_X α β = -4d ≠ 0` (`tau_alphaJac`, `mukai_alphaJac_betaJac`), so
  Assumption 2.4.1 holds (`PJac_not_isIsotropic`, `PJac_assumption2_4_1`).
* `h`: the class `Ξ_P^♯` (`KSecant.hClass`), which spans `H²(X × X̂, ℚ)^{Spin(V)_P}` and is ample
  (`WeilClasses.Main.Intro`; the paper: "an ample class `h` in the rank `1` subgroup
  `H²(X × X̂, ℤ)^{Spin(V)_P}`"; the statements below only depend on the line `ℚh`).
* **Lemma 8.3.1** (`lemma8_3_1_rank`, `lemma8_3_1`), with `ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w) = φ'(w ⊗ τ w)`
  (`lemma8_3_1_ch`; `φ(ch F₁ ⊠ ch F₁)` is the Chern character of `Φ(F₁ ⊠ F₁)` by GRR, not
  formalized), the invariance of the two classes (`lemma8_3_1_invariant`), the value of the rank
  (`lemma8_3_1_rank_eq`: `8d`), and the claims of the proof (`chF1_eq_lambda`, `tau_lambda`,
  `chF1_tmul_tau_decomp`).

Checked numerically (exact arithmetic, `d = 1, 2, 3, 5, 7`): `(α, β)_S = -4d`, the rank of
`φ(w ⊗ w)` is `8d`, `h³` and `κ₃(φ(w ⊗ w))` are linearly independent, and
`κ₃ ∈ ℚh³ ⊕ ĤW_P`.

**Left out (sheaf-theoretic).** After the proof of Lemma 8.3.1 (TeX lines 4027–4041): the
deformations of `F = I_{∪Cᵢ}` and the injective homomorphism (8.3.1) into `Ext¹(F, F)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (d : ℚ)

/-! ## `(α, β)_S = -4d` -/

/-- (§8.3, TeX line 3967) `τ(α) = α` (`α` has degrees `0` and `4`). -/
theorem tau_alphaJac : tau ℚ 3 (alphaJac d) = alphaJac d := by
  sorry

/-- (§8.3, TeX line 3967) `(α, β)_S = ∫_X τ(α) ∪ β = ∫_X α ∪ β = -4d`. -/
theorem mukai_alphaJac_betaJac : mukai ℚ 3 (alphaJac d) (betaJac d) = -4 * d := by
  sorry

/-- (§8.3, TeX lines 3966–3967) "Assumption 2.4.1 is satisfied, since `(α, β)_S = -4d ≠ 0`": the
plane `P = span{α, β}` is not isotropic for the Mukai pairing. -/
theorem PJac_not_isIsotropic {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd : 0 < d) : ¬ (PJac d hΘ hd).IsIsotropic := by
  sorry

/-- (§8.3, TeX lines 3966–3967) `P_Θ` satisfies Assumption 2.4.1 (`PTheta_assumption2_4_1`). -/
theorem PJac_assumption2_4_1 {J : Module.End ℝ (H1 ℝ 3)} (hJ : IsComplexStructure J)
    (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) : Assumption2_4_1 (PJac d hΘ hd) J :=
  PTheta_assumption2_4_1 3 d hd (by norm_num) J hJ (ThetaStd ℚ 3) hΘ

/-! ## Lemma 8.3.1 -/

section Lemma831

variable {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d)

/-- (Proof of Lemma 8.3.1, TeX lines 3980–3983) `ch(Φ(F₁ ⊠ F₁)) = φ(ch F₁ ⊠ ch F₁) =
φ'(ch F₁ ⊠ τ(ch F₁))`, `φ' = φ ∘ (id ⊗ τ)` (the first equality, GRR, is the model's definition of the
Chern character of `Φ(F₁ ⊠ F₁)`). -/
theorem lemma8_3_1_ch :
    phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) = phiPrime ℚ 3 (chF1 d ⊗ₜ[ℚ] tau ℚ 3 (chF1 d)) := by
  sorry

/-- (Proof of Lemma 8.3.1, TeX lines 3984–3988) `ch(F₁) = ½[(λ₁ + λ₂) + (λ₁ - λ₂)/√-d]` in
`H^{ev}(X, K)`, `λ₁ = exp(√-dΘ)`, `λ₂ = λ̄₁`. -/
theorem chF1_eq_lambda :
    bcS ℚ (Kd d) 3 (chF1 d) =
      (2 : Kd d)⁻¹ • ((PJac d hΘ hd).u₁ + (PJac d hΘ hd).u₂ +
        (Kd.sqrtNeg d)⁻¹ • ((PJac d hΘ hd).u₁ - (PJac d hΘ hd).u₂)) := by
  sorry

/-- (Proof of Lemma 8.3.1, TeX line 3989) "`τ` interchanges `λ₁` and `λ₂`". -/
theorem tau_lambda :
    tau (Kd d) 3 (PJac d hΘ hd).u₁ = (PJac d hΘ hd).u₂ ∧
      tau (Kd d) 3 (PJac d hΘ hd).u₂ = (PJac d hΘ hd).u₁ := by
  sorry

/-- (Proof of Lemma 8.3.1, TeX lines 3990–4009) In `H^{ev}(X × X, K) = S_K ⊗ S_K`:
`ch(F₁) ⊠ τ(ch F₁) = ((d+1)/(4d)) [λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂] + ((d-1)/(4d)) [λ₁ ⊠ λ₂ + λ₂ ⊠ λ₁]
+ (√-d/(2d)) [λ₂ ⊠ λ₁ - λ₁ ⊠ λ₂]`. -/
theorem chF1_tmul_tau_decomp :
    bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)) =
      ((d + 1) / (4 * d) : ℚ) • ((PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ +
          (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂) +
        ((d - 1) / (4 * d) : ℚ) • ((PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ +
          (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁) +
        (Kd.sqrtNeg d / (2 * (d : Kd d))) • ((PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ -
          (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂) := by
  sorry

/-- **Lemma 8.3.1** (`lemma-kappa-3-is-linearly-independent-from-h-cube`), first sentence: the rank
of `Φ(F₁ ⊠ F₁)` is non-zero. Model: the rank is the degree-`0` coefficient of
`ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w)`, `w = chF1 d`; `d > 0` (the paper: a positive integer). -/
theorem lemma8_3_1_rank : rankExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) ≠ 0 := by
  sorry

/-- The rank of `Φ(F₁ ⊠ F₁)` is `8d` (the rank of the sheaf `E` of Theorem 1.4.1(2); checked
numerically for `d = 1, 2, 3, 5, 7`). -/
theorem lemma8_3_1_rank_eq : rankExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = 8 * d := by
  sorry

/-- (Lemma 8.3.1, "the `Spin(V)_P`-invariant classes `h³` and `κ₃(Φ(F₁ ⊠ F₁))`") Both classes are
invariant under the integral group `Spin(V)_P` acting by `ρ` (for `κ₃`: Corollary 1.3.2, as
`w ⊗ w = w ⊗ τ(τ w)` with `w, τ w ∈ P`). -/
theorem lemma8_3_1_invariant :
    (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 ∈ invariantsExt ℚ 3 (PJac d hΘ hd).spinPZ ∧
      kappaDeg ℚ 3 3 (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) ∈
        invariantsExt ℚ 3 (PJac d hΘ hd).spinPZ := by
  sorry

/-- **Lemma 8.3.1** (`lemma-kappa-3-is-linearly-independent-from-h-cube`), second sentence: the
`Spin(V)_P`-invariant classes `h³` and `κ₃(Φ(F₁ ⊠ F₁))` are linearly independent.

Model: `ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w)` (`lemma8_3_1_ch`), `κ₃` its `κ`-class in `H⁶(X × X̂, ℚ)`
(`kappaDeg ℚ 3 3`); `h = Ξ_P^♯` (`hClass`; any non-zero class of the invariant line gives the same
statement). (Checked numerically for `d = 1, 2, 3, 5, 7`.) -/
theorem lemma8_3_1 :
    LinearIndependent ℚ
      ![(PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3,
        kappaDeg ℚ 3 3 (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)))] := by
  sorry

end Lemma831

end WeilClasses
