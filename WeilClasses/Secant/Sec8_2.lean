module

public import WeilClasses.Secant.Defs
public import WeilClasses.Secant.Sec8_1
public import WeilClasses.External.Markman.Sec8_2

/-!
# §8.2: Examples of secant sheaves (cohomological parts of Lemma 8.2.1 and Example 8.2.2)

Statements of the paper's §8.2 (TeX lines 3721–3962), cohomological claims only. `X` is the
Jacobian `Pic²(C)` of a non-hyperelliptic curve `C` of genus `3`, with theta divisor `Θ`; in the model
`X` is `H¹(X, ℝ)` with a complex structure `J` for which `Θ = ThetaStd ℚ 3` is ample
(`Θ³/6 = [pt]`, `ThetaStd_pow`; the Jacobian structure itself plays no role in the cohomological
statements). `α = 1 - (d/2)Θ²`, `β = Θ - d[pt]` (`alphaJac`, `betaJac`) and
`ch(F₁) = 1 + Θ - (d/2)Θ² - d[pt]` (`chF1`) are defined in `WeilClasses.Secant.Defs`.

* `exp(√-d Θ) = α + √-d β` (`expUS_ThetaStd_eq`);
* the product computed in the proof of Lemma 8.2.1 (`lemma8_2_1_product`) and its specialization
  `ch(F₁) = ch(I_{∪Cᵢ}) · exp(Θ)` (`chF1_eq_mul_exp`);
* **Lemma 8.2.1** (cohomological part, `lemma8_2_1`): `ch(F₁) = α + β`, and `ch(F₁)` and
  `ch(F₁^∨) = τ(ch F₁)` lie on the secant line `P = span{α, β}` through `exp(±√-d Θ)`
  (`PJac_Pℚ_eq`: the plane (2.4.5) of `P_Θ` is `span{α, β}`);
* **Example 8.2.2** (cohomological part, `example8_2_2`): on an abelian surface, `span_ℚ{w, h}` is
  a `ℚ(√-d)`-secant for `(w, w)_S, (h, h)_S < 0`, `(w, h)_S = 0`, `d = (w, w)_S (h, h)_S / 4`, by
  [M2, Prop. 1.7] (`markmanM2_prop1_7`, `WeilClasses.External.Markman.Sec8_2`).

**Left out (sheaf-theoretic).** The isomorphism `C^{(2)} ≅ Θ` and Riemann's singularity theorem,
Poincaré's formula `[C_t] = Θ²/2` and `ch(𝒪_{C_i}) = Θ²/2 - 2[pt]` (`χ(𝒪_C) = -2`), hence the value
`ch(I_{∪_{i=1}^{d+1} Cᵢ} ⊗ 𝒪_X(Θ)) = chF1 d` itself (the hypothesis "the `Cᵢ` are pairwise
disjoint" belongs to it); the facts that cup product with `exp(√-dΘ)` lies in `m(Spin(V_K))` and that
`exp(√-dΘ)` is a pure spinor are §2.4 (`m_expUSpin`, `expUS_isEvenPureSpinor`). In Example 8.2.2,
that `w = ch(F)` for a coherent sheaf `F` and that `h` is algebraic. Examples 8.2.3–8.2.4 (secant
sheaves on Jacobians of genus-`n` curves via Brill–Noether loci, and of genus-`4` curves with two
`g¹₃`'s) and Lemma 8.2.5 (`ch(𝒪_{W₂})`) are sheaf-theoretic and are not stated.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (d : ℚ)

/-- `exp(c Θ) = α + c β` in `H^{ev}(X, K)` for every `c ∈ K` with `c² = -d` (`c = ±√-d`): the
computation of §8.2, TeX lines 3735–3739. -/
theorem s8_exp_smul_ThetaStd (c : Kd d) (hc : c * c = algebraMap ℚ (Kd d) (-d)) :
    IsNilpotent.exp (c • bcS ℚ (Kd d) 3 (ThetaStd ℚ 3)) =
      bcS ℚ (Kd d) 3 (alphaJac d) + c • bcS ℚ (Kd d) 3 (betaJac d) := by
  -- `exp(u) = 1 + u + u²/2 + u³/6` (`u⁴ = 0`), `c² = -d`, `Θ³ = 6[pt]`
  have hT := s8_ThetaStd_mem (Kd d) 3
  rw [s8_bcS_ThetaStd, s8_exp_three (Kd d) (Submodule.smul_mem _ c hT), alphaJac, betaJac]
  simp only [map_sub, map_one, map_smul, map_pow, s8_bcS_ThetaStd, s8_bcS_pt]
  rw [s8_pt_three]
  simp only [smul_pow, ← algebraMap_smul (Kd d) (d / 2 : ℚ), ← algebraMap_smul (Kd d) d]
  have h2 : c ^ 2 = algebraMap ℚ (Kd d) (-d) := by rw [sq, hc]
  have h3 : c ^ 3 = algebraMap ℚ (Kd d) (-d) * c := by rw [pow_succ, h2]
  rw [h2, h3]
  simp only [map_neg, map_div₀, map_ofNat]
  module

/-- (§8.2, TeX lines 3735–3739) `exp(√-d Θ) = 1 + √-dΘ - (d/2)Θ² - d√-d[pt] = α + √-d β` in
`H^{ev}(X, K)` (`Θ = ThetaStd ℚ 3`, `Θ³ = 6[pt]`), for `d > 0` (the paper: a positive integer). -/
theorem expUS_ThetaStd_eq (hd : 0 < d) :
    expUS 3 d (ThetaStd ℚ 3) =
      bcS ℚ (Kd d) 3 (alphaJac d) + Kd.sqrtNeg d • bcS ℚ (Kd d) 3 (betaJac d) :=
  s8_exp_smul_ThetaStd d _ (s8_sqrtNeg_mul_self hd.le)

/-- (Proof of Lemma 8.2.1, TeX lines 3758–3764) The product
`(1 - (m/2)Θ² + 2m[pt]) · exp(kΘ) = 1 + kΘ + ((k² - m)/2)Θ² + (k³ - 3km + 2m)[pt]`
(`Θ = ThetaStd ℚ 3`; `exp(kΘ) = ch(𝒪_X(kΘ))` and `1 - (m/2)Θ² + 2m[pt] = ch(I_{∪_{i=1}^m Cᵢ})`,
geometric). -/
theorem lemma8_2_1_product (m k : ℚ) :
    (1 - (m / 2) • ThetaStd ℚ 3 ^ 2 + (2 * m) • pt ℚ 3) * IsNilpotent.exp (k • ThetaStd ℚ 3) =
      1 + k • ThetaStd ℚ 3 + ((k ^ 2 - m) / 2) • ThetaStd ℚ 3 ^ 2 +
        (k ^ 3 - 3 * k * m + 2 * m) • pt ℚ 3 := by
  -- `exp(kΘ) = 1 + kΘ + (k²/2)Θ² + (k³/6)Θ³`, `[pt] = Θ³/6`, `Θ⁴ = Θ⁵ = Θ⁶ = 0`
  have hT := s8_ThetaStd_mem ℚ 3
  have h4 : ThetaStd ℚ 3 ^ 4 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have h5 : ThetaStd ℚ 3 ^ 5 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have h6 : ThetaStd ℚ 3 ^ 6 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  rw [s8_exp_three ℚ (Submodule.smul_mem _ k hT), s8_pt_three]
  simp only [smul_pow, add_mul, mul_add, sub_mul, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, ← pow_add, ← pow_succ, Nat.reduceAdd, h4, h5, h6, smul_zero, add_zero,
    sub_zero]
  module

/-- (Proof of Lemma 8.2.1, TeX line 3765: "Taking `k = 1` and `n = d + 1`") `ch(F₁) =
ch(I_{∪_{i=1}^{d+1} Cᵢ}) · ch(𝒪_X(Θ))`: `chF1 d = (1 - ((d+1)/2)Θ² + 2(d+1)[pt]) · exp(Θ)`. -/
theorem chF1_eq_mul_exp :
    chF1 d = (1 - ((d + 1) / 2) • ThetaStd ℚ 3 ^ 2 + (2 * (d + 1)) • pt ℚ 3) *
      IsNilpotent.exp ((1 : ℚ) • ThetaStd ℚ 3) := by
  rw [lemma8_2_1_product, chF1]
  module

/-- The plane `P` of the `K`-secant `P_Θ` ((2.4.5): `span{Re exp(u), Im exp(u)/√d}`) is
`span_ℚ{α, β}` (§8.2–8.3, "Let `P := span{α, β}` be the rational `ℚ(√-d)`-secant plane"). -/
theorem PJac_Pℚ_eq {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    (PJac d hΘ hd).Pℚ = Submodule.span ℚ {alphaJac d, betaJac d} := by
  -- (2.4.5): `P = span{Re exp(u), Im exp(u)/√d}`, and `exp(u) = α + √-d β`
  rw [PJac, equation2_4_5, expUS_ThetaStd_eq d hd, map_add, map_add, s8_reS_bcS,
    s8_reS_smul_bcS, s8_ratPart_sqrtNeg, zero_smul, add_zero, s8_imS_bcS, s8_imS_smul_bcS,
    s8_sqrtNegCoeff_sqrtNeg hd, one_smul, zero_add]

/-- `τ(ch F₁) = α - β` (`τ` acts on `H^{2i}` by `(-1)^i`). -/
theorem s8_tau_chF1 : tau ℚ 3 (chF1 d) = alphaJac d - betaJac d := by
  have hT := s8_ThetaStd_mem ℚ 3
  rw [chF1, alphaJac, betaJac, s8_pt_three]
  simp only [map_sub, map_add, map_smul, s8_tau_one, s8_tau_of_mem_two ℚ 3 hT,
    s8_tau_pow ℚ 3 hT]
  simp only [neg_sq, Odd.neg_pow (by decide : Odd 3)]
  module

/-- `u₁ = exp(√-dΘ) = α + √-d β` for `P_Θ`. -/
theorem s8_PJac_u₁ {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    (PJac d hΘ hd).u₁ =
      bcS ℚ (Kd d) 3 (alphaJac d) + Kd.sqrtNeg d • bcS ℚ (Kd d) 3 (betaJac d) :=
  expUS_ThetaStd_eq d hd

/-- `u₂ = exp(-√-dΘ) = α - √-d β` for `P_Θ`. -/
theorem s8_PJac_u₂ {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    (PJac d hΘ hd).u₂ =
      bcS ℚ (Kd d) 3 (alphaJac d) + (-Kd.sqrtNeg d) • bcS ℚ (Kd d) 3 (betaJac d) := by
  rw [PJac, PTheta_u₂, uΘ, ← neg_smul]
  exact s8_exp_smul_ThetaStd d _ (by rw [neg_mul_neg]; exact s8_sqrtNeg_mul_self hd.le)

/-- **Lemma 8.2.1** (`lemma-ch-F-i-is-on-secant-to-spinor-variety`), cohomological part.
`ch(I_{∪Cᵢ} ⊗ 𝒪_X(Θ)) = 1 + Θ - (d/2)Θ² - d[pt] = α + β`. Consequently `ch(F₁)` and
`ch(R𝓗om(F₁, 𝒪_X)) = τ(ch F₁)` both belong to the secant line to the spinor variety through the pure
spinor `exp(√-dΘ)` and its complex conjugate `exp(-√-dΘ)`.

Model: `ch(F₁) = chF1 d` (the value of the Chern character is geometric, see the module docstring);
`ch(F^∨) = τ(ch F)` (Remark 5.2.3); the secant line is the plane `P` of the oriented `K`-secant
`P_Θ` (`PJac`, `u₁ = exp(√-dΘ)`, `u₂ = exp(-√-dΘ)`). `d > 0` rational (the paper: a positive
integer); `X` given by a complex structure `J` for which `Θ` is ample. -/
theorem lemma8_2_1 {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    chF1 d = alphaJac d + betaJac d ∧ chF1 d ∈ (PJac d hΘ hd).Pℚ ∧
      tau ℚ 3 (chF1 d) ∈ (PJac d hΘ hd).Pℚ := by
  have hT := s8_ThetaStd_mem ℚ 3
  have hab : chF1 d = alphaJac d + betaJac d := by
    rw [chF1, alphaJac, betaJac]
    module
  -- `τ` acts on `H^{2i}` by `(-1)^i`: `τ(ch F₁) = α - β`
  have hτ : tau ℚ 3 (chF1 d) = alphaJac d - betaJac d := s8_tau_chF1 d
  refine ⟨hab, ?_, ?_⟩
  · rw [hab, PJac_Pℚ_eq d hΘ hd]
    exact add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  · rw [hτ, PJac_Pℚ_eq d hΘ hd]
    exact sub_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

/-! ## Example 8.2.2 -/

/-- **Example 8.2.2** (no label; TeX lines 3773–3775), cohomological part: on an abelian surface
(`n = 2`), if `w, h ∈ S⁺_ℚ = H^{ev}(X, ℚ)` satisfy `(w, w)_S < 0`, `(h, h)_S < 0` and
`(w, h)_S = 0`, then `ℙ(span_ℚ{w, h})` is a secant to the spinor variety inducing complex
multiplication by `ℚ(√-d)`, `d = (w, w)_S (h, h)_S / 4`: `span_ℚ{w, h}` is the rational plane of a
`K`-secant. The paper cites [M2, Prop. 1.7] (Markman, *The monodromy of generalized Kummer varieties
and algebraic cycles on their intermediate Jacobians*, JEMS 25 (2023)), stated in this form as
`markmanM2_prop1_7` (`WeilClasses.External.Markman.Sec8_2`). That `w = ch(F)` and that `h` is
algebraic play no role in this statement. -/
theorem example8_2_2 (w h : S ℚ 2) (hw : w ∈ Splus ℚ 2) (hh : h ∈ Splus ℚ 2)
    (hww : mukai ℚ 2 w w < 0) (hhh : mukai ℚ 2 h h < 0) (hwh : mukai ℚ 2 w h = 0) :
    ∃ P : KSecant 2 (mukai ℚ 2 w w * mukai ℚ 2 h h / 4), P.Pℚ = Submodule.span ℚ {w, h} :=
  -- `span_ℚ{w, h}` is a secant to the spinor variety inducing complex multiplication by `ℚ(√-d)`,
  -- by [M2, Prop. 1.7]
  markmanM2_prop1_7 w h hw hh hww hhh hwh

end WeilClasses
