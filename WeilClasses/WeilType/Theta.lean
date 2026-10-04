module

public import WeilClasses.WeilType.Basic
public import WeilClasses.External.Chevalley.Sec2_4
public import WeilClasses.Hodge.Ample

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
    thetaExt n F Θ (bcDual ℚ F n y) = bcH1 ℚ F n (thetaMap n Θ y) := by
  sorry

/-- `Θ(y, y') = y'(θ(y))`: the pairing `⟪Θ, y ∧ y'⟫` of `WeilClasses.eval2` is the bilinear form
`Θ(yᵢ, yⱼ)` of the proof of Lemma 3.1.3. -/
theorem thetaMap_apply_eq_eval2 (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (y y' : Module.Dual ℚ (H1 ℚ n)) : y' (thetaMap n Θ y) = eval2 ℚ n Θ y y' := by
  sorry

/-- `θ` is a morphism of Hodge structures `H¹(X̂, ℝ) = H¹(X, ℝ)* → H¹(X, ℝ)` when `Θ` is of type
`(1,1)`: it intertwines the standard complex structure `y ↦ -y ∘ J` of `H¹(X̂, ℝ) = H¹(X, ℝ)*` with
`J` (the paper's footnote in §2.4 uses the negatives `y ↦ y ∘ J` and `-J`; the statement is the
same) (§2.4, after (2.4.3): "`θ` is an isomorphism of rational Hodge structures under the
identification of `H¹(X, ℚ)*` with `H¹(X̂, ℚ)`"). -/
theorem thetaExt_comp_neg_dualMap (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : Θ ∈ hodgeClassesX n J 1) :
    thetaExt n ℝ Θ ∘ₗ (-(J.dualMap)) = J ∘ₗ thetaExt n ℝ Θ := by
  sorry

section AmpleAPI

variable {n}

/-- An ample class has degree two. -/
theorem IsAmple.mem_exteriorPower_two {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n}
    (hΘ : IsAmple n J Θ) : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n) := by
  sorry

/-- An ample class on an abelian variety of positive dimension is nonzero. -/
theorem IsAmple.ne_zero_of_pos {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ)
    (hn : 0 < n) : Θ ≠ 0 := by
  sorry

/-- `θ` is an isomorphism when `Θ` is ample (§2.4: "`θ` is an isomorphism of rational Hodge
structures"; used for `W₁ ∩ W₂ = 0`). -/
theorem IsAmple.bijective_thetaMap {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n}
    (hΘ : IsAmple n J Θ) : Function.Bijective (thetaMap n Θ) := by
  sorry

end AmpleAPI

/-! ## `u = √-d Θ` and `exp(u) ∈ Spin(V_K)` -/

/-- `u = √-d Θ ∈ H²(X, K) ⊆ S_K` (§2.4, before (2.4.4)). -/
noncomputable def uΘ (Θ : S ℚ n) : S (Kd d) n := Kd.sqrtNeg d • bcS ℚ (Kd d) n Θ

/-- `u = √-d Θ ∈ ⋀² H¹(X, K)` for `Θ ∈ ⋀² H¹(X, ℚ)`. -/
theorem uΘ_mem (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) : uΘ n d Θ ∈ ⋀[Kd d]^2 (H1 (Kd d) n) := by
  sorry

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
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) = LinearMap.mulLeft (Kd d) (expUS n d Θ) := by
  sorry

/-- **(2.4.4)** (`eq-action-of-exp-u-on-V`): `exp(u)` acts on `V_K` by
`exp(u)·(w, y) = (w - √-d θ(y), y)`, `w ∈ H¹(X, K)`, `y ∈ H¹(X̂, K) ≅ H¹(X, K)*`. In our order
`(y, w)`: `ρ(exp u)(y, w) = (y, w - √-d θ(y))`. -/
theorem equation2_4_4 (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (v : V (Kd d) n) :
    rho (Kd d) n (expUSpin n d Θ hΘ) v = (v.1, v.2 - Kd.sqrtNeg d • thetaExt n (Kd d) Θ v.1) := by
  sorry

/-- `exp(u)` leaves invariant the pure spinor `[pt] ∈ H^{2n}(X, K)` (§2.4, after (2.4.4)). -/
theorem m_expUSpin_pt (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) (pt (Kd d) n) = pt (Kd d) n := by
  sorry

/-- `exp(u)` leaves invariant every element of `H¹(X, K) = 0 × H¹(X, K)` (§2.4, after (2.4.4)). -/
theorem rho_expUSpin_inr (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (w : H1 (Kd d) n) :
    rho (Kd d) n (expUSpin n d Θ hΘ) (0, w) = (0, w) := by
  sorry

/-- `exp(u)` takes the pure spinor `1` (of `H¹(X, K)*`) to the class `exp(u) ∈ H^{ev}(X, K)`
(§2.4, after (2.4.4)). -/
theorem m_expUSpin_one (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    m (Kd d) n (expUSpin n d Θ hΘ : C (Kd d) n) 1 = expUS n d Θ := by
  sorry

/-! ## The oriented rational `K`-secant `P_Θ` -/

/-- `exp(u)` is an even pure spinor, with `ker m_{exp u} = exp(u)(H¹(X, K)*)` (§2.4). -/
theorem expUS_isEvenPureSpinor (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) :
    IsEvenPureSpinor (Kd d) n (expUS n d Θ) := by
  sorry

/-- `exp(u)` and `σ(exp u) = exp(ū)` span distinct lines when `d > 0` and `Θ ≠ 0`. -/
theorem expUS_linIndep (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    LinearIndependent (Kd d) ![expUS n d Θ, σS n d (expUS n d Θ)] := by
  sorry

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
  sorry

/-- The coordinatewise map `S_K → S_ℚ` obtained by applying a `ℚ`-linear form `φ : K → ℚ` to the
coefficients in the basis `e_K`. -/
noncomputable def coeffMapS (φ : Kd d →ₗ[ℚ] ℚ) : S (Kd d) n →ₗ[ℚ] S ℚ n :=
  (basisS ℚ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun K => φ ∘ₗ ((basisS (Kd d) n).coord K).restrictScalars ℚ)

/-- The real part `Re : S_K → S_ℚ` (coefficientwise `a + b√-d ↦ a`). -/
noncomputable def reS : S (Kd d) n →ₗ[ℚ] S ℚ n := coeffMapS n d (Kd.ratPart d)

/-- `Im/√d : S_K → S_ℚ` (coefficientwise `a + b√-d ↦ b`, i.e. `Im(z)/√d`). -/
noncomputable def imS : S (Kd d) n →ₗ[ℚ] S ℚ n := coeffMapS n d (Kd.sqrtNegCoeff d)

/-- `s = Re(s) + √-d · Im(s)/√d` for `s ∈ S_K` (with rational `Re(s)`, `Im(s)/√d`). -/
theorem bcS_reS_add_imS (hd : 0 < d) (s : S (Kd d) n) :
    bcS ℚ (Kd d) n (reS n d s) + Kd.sqrtNeg d • bcS ℚ (Kd d) n (imS n d s) = s := by
  sorry

/-- **(2.4.5)** (`eq-P`): `P = span{Re(exp(u)), Im(exp(u))/√d}` (oriented via `ℓ̃₁`). -/
theorem equation2_4_5 (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).Pℚ =
      Submodule.span ℚ {reS n d (expUS n d Θ), imS n d (expUS n d Θ)} := by
  sorry

/-- **(2.4.6)** (`eq-W-1-and-2`), first line: `W₁ = exp(u)(H¹(X, K)*) = {(-√-d θ(y), y)}`; in our
order `(y, w)`: `W₁ = ρ(exp u)(H¹(X, K)* × 0) = {(y, -√-d θ(y)) : y ∈ H¹(X, K)*}`. -/
theorem equation2_4_6_W₁ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (PTheta n d hd Θ hΘ hΘ0).W₁ =
        (LinearMap.range (LinearMap.inl (Kd d) (Module.Dual (Kd d) (H1 (Kd d) n))
          (H1 (Kd d) n))).map (rho (Kd d) n (expUSpin n d Θ hΘ) : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∧
      (PTheta n d hd Θ hΘ hΘ0).W₁ =
        LinearMap.range (LinearMap.prod LinearMap.id (-(Kd.sqrtNeg d) • thetaExt n (Kd d) Θ)) := by
  sorry

/-- **(2.4.6)** (`eq-W-1-and-2`), second line: `W₂ = \overline{W₁} = {(+√-d θ(y), y)}`; in our order
`W₂ = σ(W₁) = {(y, √-d θ(y)) : y ∈ H¹(X, K)*}`. -/
theorem equation2_4_6_W₂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0) :
    (σV n d '' ((PTheta n d hd Θ hΘ hΘ0).W₁ : Set (V (Kd d) n)) =
        ((PTheta n d hd Θ hΘ hΘ0).W₂ : Set (V (Kd d) n))) ∧
      (PTheta n d hd Θ hΘ hΘ0).W₂ =
        LinearMap.range (LinearMap.prod LinearMap.id (Kd.sqrtNeg d • thetaExt n (Kd d) Θ)) := by
  sorry

/-- `W₁ ∩ W₂ = 0`, since `θ` is an isomorphism (§2.4, after (2.4.6)). -/
theorem PTheta_W₁_inf_W₂ (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) :
    (PTheta n d hd Θ hΘ hΘ0).W₁ ⊓ (PTheta n d hd Θ hΘ hΘ0).W₂ = ⊥ := by
  sorry

/-- `V_K = W₁ ⊕ W₂` for `P_Θ` when `θ` is an isomorphism. -/
theorem PTheta_isCompl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) :
    IsCompl (PTheta n d hd Θ hΘ hΘ0).W₁ (PTheta n d hd Θ hΘ hΘ0).W₂ := by
  sorry

/-- `P_Θ` satisfies Assumption 2.4.1 for the complex structure `J` of `X` when `Θ` is ample for `J`
(§1.2 and §2.4: `P ⊆ ⊕_p H^{p,p}(X, ℚ)` is non-isotropic, as `W₁ ∩ W₂ = 0`). -/
theorem PTheta_assumption2_4_1 (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    Assumption2_4_1 (PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)) J := by
  sorry

/-- The similarity `f = η_{√-d}` of `P_Θ` on `H¹(X, ℚ)* × 0` (proof of Lemma 3.1.3:
`f(0, y) = (d θ(y), 0)` in the paper's order): `f(y, 0) = (0, d θ(y))`. -/
theorem PTheta_fη_inl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).fη (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (y, 0) =
      (0, d • thetaMap n Θ y) := by
  sorry

/-- The similarity `f` of `P_Θ` on `0 × H¹(X, ℚ)`: `f(0, θ(y)) = (-y, 0)` (with `f(y, 0)`, this
gives `f(y, w) = (-θ⁻¹(w), d θ(y))`). -/
theorem PTheta_fη_inr (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).fη (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (0, thetaMap n Θ y) =
      (-y, 0) := by
  sorry

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
  sorry

end WeilClasses
