module

public import WeilClasses.Main.Jacobian
public import WeilClasses.WeilType.Theta
public import WeilClasses.PureSpinor.Lemma2_2_4
public import WeilClasses.Secant.Defs

/-!
# The explicit `X × X̂` and the secant `P_Θ` of §2.4

The statements of Theorem 1.5.1 use the explicit polarized abelian variety of Weil type
`(X × X̂, η, h)` (`fV`, `hV`, `stdStructure` in `WeilClasses.Defs`, `etaV` in
`WeilClasses.Main.Jacobian`), while the paper
constructs it from the oriented `K`-secant `P_Θ` (§2.4: `η` from (2.2.4), `h` the class of `Ξ_P`
(2.4.2), the complex structure `I_{V_ℝ}`). This file states that the two agree for the standard
principal polarization `Θ = ThetaStd`:

* `θ` (2.4.3) is `thetaStd`, and `f = η(√-d)` is `fV`, so `η = etaV`;
* `h = d Θ + Θ̂` is the class of `Ξ_P` under `V ≅ V*` (`(x, ·)_V ↔ x`):
  `⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`;
* the standard complex structure of `X × X̂` is `-I_{V_ℝ}` (`stdStructure_eq_neg`);
* `P_Θ` of §8 (`PJac`) is `PStd`, and `h` is `Ξ_P^♯` (`hClass_PStd`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (n : ℕ)

/-- `Θ = Σ e_{2i} ∧ e_{2i+1}` has degree `2`. -/
theorem ThetaStd_mem : ThetaStd ℚ n ∈ ⋀[ℚ]^2 (H1 ℚ n) := by
  sorry

/-- `Θ ≠ 0` for `n > 0`. -/
theorem ThetaStd_ne_zero (hn : 0 < n) : ThetaStd ℚ n ≠ 0 := by
  sorry

/-- The contraction `θ` (2.4.3) of `Θ = ThetaStd` is `thetaStd`. -/
theorem thetaMap_ThetaStd : thetaMap n (ThetaStd ℚ n) = thetaStd n := by
  sorry

/-- `θ` of `ThetaStd` is an isomorphism, with inverse `thetaStdInv`. -/
theorem thetaStd_bijective : Function.Bijective (thetaMap n (ThetaStd ℚ n)) := by
  sorry

theorem thetaStdInv_comp_thetaStd : thetaStdInv n ∘ₗ thetaStd n = LinearMap.id := by
  sorry

theorem thetaStd_comp_thetaStdInv : thetaStd n ∘ₗ thetaStdInv n = LinearMap.id := by
  sorry

variable (d : ℚ) (hd : 0 < d) (hn : 0 < n)

/-- The oriented `K`-secant `P_Θ` (§2.4) of the standard principal polarization `Θ = ThetaStd`. -/
noncomputable abbrev PStd : KSecant n d :=
  PTheta n d hd (ThetaStd ℚ n) (ThetaStd_mem n) (ThetaStd_ne_zero n hn)

/-- `V_K = W₁ ⊕ W₂` for `P_Θ`. -/
theorem PStd_isCompl : IsCompl (PStd n d hd hn).W₁ (PStd n d hd hn).W₂ :=
  PTheta_isCompl n d hd _ _ _ (thetaStd_bijective n)

/-- `f = η(√-d)` of `P_Θ` is `fV`: `f(y, w) = (-θ⁻¹(w), d θ(y))`. -/
theorem fη_PStd : (PStd n d hd hn).fη (PStd_isCompl n d hd hn) = fV n d := by
  sorry

/-- The action `η : K → End(V_ℚ)` (2.2.4) of `P_Θ` is `etaV`. -/
theorem ηHom_PStd : (PStd n d hd hn).ηHom hd (PStd_isCompl n d hd hn) = etaV n d hd := by
  sorry

/-- `h = d Θ + Θ̂` is the class of `Ξ_P` (2.4.2) of `P_Θ`: for `x, y ∈ V_ℚ`,
`⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`, where `⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-`0` part) as in
`WeilClasses.eval2`. -/
theorem hV_eq_XiQ (x y : V ℚ n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing ℚ n y) (contractLeft (Q := 0) (pairing ℚ n x) (hV n d))) =
      (PStd n d hd hn).XiQ (PStd_isCompl n d hd hn) x y := by
  sorry

/-- `h = d Θ + Θ̂` is the class `Ξ_P^♯` of `WeilClasses.Secant.Defs` (`KSecant.hClass`). -/
theorem hClass_PStd : (PStd n d hd hn).hClass (PStd_isCompl n d hd hn) = hV n d := by
  sorry

/-- `P_Θ` of §8 (`PJac`, for an ample `Θ = ThetaStd` on a threefold) is `PStd`. -/
theorem PJac_eq_PStd {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    PJac d hΘ hd = PStd 3 d hd (by norm_num) :=
  rfl

/-- The standard complex structure of `X × X̂` (`H^{1,0}` the `i`-eigenspace) is the negative of the
paper's `I_{V_ℝ}` (footnote in §2.4). -/
theorem stdStructure_eq_neg (J : Module.End ℝ (H1 ℝ n)) :
    stdStructure n J = -productStructure n J := by
  sorry

end WeilClasses
