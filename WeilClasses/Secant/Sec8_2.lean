module

public import WeilClasses.Secant.Defs

/-!
# §8.2: Examples of secant sheaves (cohomological part of Lemma 8.2.1)

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
  (`PJac_Pℚ_eq`: the plane (2.4.5) of `P_Θ` is `span{α, β}`).

**Left out (sheaf-theoretic).** The isomorphism `C^{(2)} ≅ Θ` and Riemann's singularity theorem,
Poincaré's formula `[C_t] = Θ²/2` and `ch(𝒪_{C_i}) = Θ²/2 - 2[pt]` (`χ(𝒪_C) = -2`), hence the value
`ch(I_{∪_{i=1}^{d+1} Cᵢ} ⊗ 𝒪_X(Θ)) = chF1 d` itself (the hypothesis "the `Cᵢ` are pairwise
disjoint" belongs to it); the facts that cup product with `exp(√-dΘ)` lies in `m(Spin(V_K))` and that
`exp(√-dΘ)` is a pure spinor are §2.4 (`m_expUSpin`, `expUS_isEvenPureSpinor`). Examples 8.2.2–8.2.4
(secant sheaves on abelian surfaces, on Jacobians of genus-`n` curves via Brill–Noether loci, and of
genus-`4` curves with two `g¹₃`'s) and Lemma 8.2.5 (`ch(𝒪_{W₂})`) are sheaf-theoretic and are not
stated.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (d : ℚ)

/-- (§8.2, TeX lines 3735–3739) `exp(√-d Θ) = 1 + √-dΘ - (d/2)Θ² - d√-d[pt] = α + √-d β` in
`H^{ev}(X, K)` (`Θ = ThetaStd ℚ 3`, `Θ³ = 6[pt]`). -/
theorem expUS_ThetaStd_eq :
    expUS 3 d (ThetaStd ℚ 3) =
      bcS ℚ (Kd d) 3 (alphaJac d) + Kd.sqrtNeg d • bcS ℚ (Kd d) 3 (betaJac d) := by
  sorry

/-- (Proof of Lemma 8.2.1, TeX lines 3758–3764) The product
`(1 - (m/2)Θ² + 2m[pt]) · exp(kΘ) = 1 + kΘ + ((k² - m)/2)Θ² + (k³ - 3km + 2m)[pt]`
(`Θ = ThetaStd ℚ 3`; `exp(kΘ) = ch(𝒪_X(kΘ))` and `1 - (m/2)Θ² + 2m[pt] = ch(I_{∪_{i=1}^m Cᵢ})`,
geometric). -/
theorem lemma8_2_1_product (m k : ℚ) :
    (1 - (m / 2) • ThetaStd ℚ 3 ^ 2 + (2 * m) • pt ℚ 3) * IsNilpotent.exp (k • ThetaStd ℚ 3) =
      1 + k • ThetaStd ℚ 3 + ((k ^ 2 - m) / 2) • ThetaStd ℚ 3 ^ 2 +
        (k ^ 3 - 3 * k * m + 2 * m) • pt ℚ 3 := by
  sorry

/-- (Proof of Lemma 8.2.1, TeX line 3765: "Taking `k = 1` and `n = d + 1`") `ch(F₁) =
ch(I_{∪_{i=1}^{d+1} Cᵢ}) · ch(𝒪_X(Θ))`: `chF1 d = (1 - ((d+1)/2)Θ² + 2(d+1)[pt]) · exp(Θ)`. -/
theorem chF1_eq_mul_exp :
    chF1 d = (1 - ((d + 1) / 2) • ThetaStd ℚ 3 ^ 2 + (2 * (d + 1)) • pt ℚ 3) *
      IsNilpotent.exp ((1 : ℚ) • ThetaStd ℚ 3) := by
  sorry

/-- The plane `P` of the `K`-secant `P_Θ` ((2.4.5): `span{Re exp(u), Im exp(u)/√d}`) is
`span_ℚ{α, β}` (§8.2–8.3, "Let `P := span{α, β}` be the rational `ℚ(√-d)`-secant plane"). -/
theorem PJac_Pℚ_eq {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    (PJac d hΘ hd).Pℚ = Submodule.span ℚ {alphaJac d, betaJac d} := by
  sorry

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
  sorry

end WeilClasses
