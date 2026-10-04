module

public import WeilClasses.Secant.Sec8_3
public import WeilClasses.Orlov.Sec6_2
public import WeilClasses.Orlov.Sec6_4
public import WeilClasses.PeriodDomain.SemiHodge
public import WeilClasses.Igusa.Defs

/-!
# The introduction (paper §§1.2–1.4): Proposition 1.2.1, Corollary 1.3.2, Theorem 1.4.1

Statements of the introduction's results on secant classes (TeX lines 311–532), in the model of
`WeilClasses.Secant.Defs`.

## §1.2 and §1.3

`P = P_Θ` is the oriented `K`-secant (1.2.4) = (2.4.5) of an ample class `Θ` of `X` (complex structure
`J` of `H¹(X, ℝ)`), `u = √-dΘ`, `ℓ̃₁ = K exp(u)`, `ℓ̃₂ = K exp(ū)` (`WeilClasses.PAmple`).

* **Proposition 1.2.1** (`proposition1_2_1`) and the sentence after it
  (`proposition1_2_1_rational`): `φ ∘ (id ⊗ τ)` (`phiPrime`) maps `ℓ̃ᵢ ⊗ ℓ̃ᵢ` into
  `⊕_{k ≥ 2n} H^k(X × X̂, K)` with projection `⋀^{2n} Wᵢ` to `H^{2n}`, and `HW_P` onto a plane
  projecting onto `ĤW_P`. (= Proposition 6.4.1(1).)
* §1.3, before Corollary 1.3.2: `H²(X × X̂, ℚ)^{Spin(V)_P}` is the line spanned by `h = Ξ_P^♯`
  (`intro_invQ_two`), `h` is ample (`intro_hClass_isAmple`, for the standard complex structure
  `-I_{V_ℝ}` of `X × X̂`, transported to the model `H¹(X × X̂) = ℚ^{4n}` by `coordV`), and
  `η(k) h = Nm(k) h` (`intro_eta_hClass`).
* **Corollary 1.3.2** (`corollary1_3_2`, `corollary1_3_2_hodge`; and `corollary1_3_2_field`,
  `corollary1_3_2_baseChange`: the invariance holds for `Spin(V_F)_P` for every field `F`).

## §1.4, Theorem 1.4.1 (`n = 3`)

`X` is the Jacobian of a non-hyperelliptic genus-`3` curve; in the model `Θ = ThetaStd ℚ 3` is ample
for the complex structure `J`; `d ≥ 3`; `ch(F₁) = ch(F₂) = w = chF1 d` (`F₁ = I_{∪Cᵢ}(Θ)`,
`F₂ = I_{∪Σᵢ}(Θ)`; geometric input, see `WeilClasses.Secant.Defs`); `E` is the sheaf with
`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]`, `ch(E) = τ(φ(w ⊗ w))` (`chE`), `κ₃(E) = kappa3E d`; `P = P_Θ` (`PJac`).

* (1) `theorem1_4_1_1`; (3) `theorem1_4_1_3`; (4) `theorem1_4_1_4`, `theorem1_4_1_4_finrank`;
  the cohomological part of (2): the rank of `E` is `8d` (`theorem1_4_1_2_rank`);
  `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))` (`kappa3E_eq_neg`), relating (4) to Lemma 8.3.1.
* **Left out (sheaf-theoretic):** item (2) (`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]` with `E` a simple reflexive sheaf)
  except the value of the rank, and item (5) (first-order deformations of `E` as a twisted sheaf).

Numerical checks (exact arithmetic in `ℚ(√-d)`, `d = 1, 2, 3, 5, 7`): the rank of `φ(w ⊗ w)` is `8d`;
`κ₃` and `h³` are independent; the `η(K)`-translates of `κ₃` and `h³` span the `3`-dimensional
`ℚh³ ⊕ ĤW_P`; on the line through `τ(w)` and `w` only the points `exp(±√-dΘ)` are pure (kernel of
`m` of dimension `6`); `κ(φ(w₁ ⊗ τ w₂))` is invariant under elements `1 + xy`
(`x ∈ W₁`, `y ∈ W₂`, `(x, y)_V = 0`) of `Spin(V_K)_P` (`n = 2, 3`); `h` is ample for `-I_{V_ℝ}`
(`n = 1, 2, 3`, random `J` for which `Θ` is ample).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable {n : ℕ}

/-- The oriented `K`-secant `P_Θ` of (1.2.4) = (2.4.5) for an ample class `Θ` (`0 < n`, `0 < d`). -/
noncomputable abbrev PAmple {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ)
    (hn : 0 < n) (d : ℚ) (hd : 0 < d) : KSecant n d :=
  PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)

/-- `V_K = W₁ ⊕ W₂` for `P_Θ`. -/
theorem PAmple_isCompl {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ) (hn : 0 < n)
    (d : ℚ) (hd : 0 < d) : IsCompl (PAmple hΘ hn d hd).W₁ (PAmple hΘ hn d hd).W₂ :=
  PTheta_isCompl n d hd _ _ _ hΘ.bijective_thetaMap

/-! ## Proposition 1.2.1 -/

/-- **Proposition 1.2.1** (no label; = Proposition 6.4.1(1)). The image `φ(ℓ̃ᵢ ⊗ τ(ℓ̃ᵢ))` via
`φ ∘ (id ⊗ τ)` of the tensor square `ℓ̃ᵢ ⊗ ℓ̃ᵢ` of each of the two pure spinor lines in `P` is
contained in `⊕_{k=2n}^{4n} H^k(X × X̂, K)`, and its projection to `H^{2n}(X × X̂, K)` is `⋀^{2n} Wᵢ`.

Model: `P = P_Θ` for `Θ` ample for `J`, `d > 0` (the paper: a positive integer), `ℓ̃ᵢ = K uᵢ`;
`φ ∘ (id ⊗ τ) = phiPrime`, where the intro's `φ` of (1.2.5) is Orlov's `φ` (`phiOrlov`) by
Proposition 1.3.1 (`proposition1_3_1_eq`). (The intro's `n ≥ 2` is not needed; `0 < n` makes `P_Θ` a
secant.) -/
theorem proposition1_2_1 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    (phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₁ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₁) ∈
          extFiltGE (Kd d) n (2 * n) ∧
        (Submodule.span (Kd d)
            {phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₁ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₁)}).map
            (projDeg (Kd d) n (2 * n)) = topWedge (PAmple hΘ hn d hd).W₁ (2 * n)) ∧
      (phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₂ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₂) ∈
          extFiltGE (Kd d) n (2 * n) ∧
        (Submodule.span (Kd d)
            {phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₂ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₂)}).map
            (projDeg (Kd d) n (2 * n)) = topWedge (PAmple hΘ hn d hd).W₂ (2 * n)) := by
  sorry

/-- (§1.2, after Proposition 1.2.1, TeX lines 392–393) "In particular, the isomorphism `φ ∘ (id ⊗ τ)`
maps the `2`-dimensional rational subspace `HW_P` of `P ⊗ P` to a `2`-dimensional subspace of
`H^{even}(X × X̂, ℚ)`, and the latter projects onto the `2`-dimensional subspace `ĤW_P` of Hodge–Weil
classes in `H^{2n}(X × X̂, ℚ)`." -/
theorem proposition1_2_1_rational (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    Module.finrank ℚ ((PAmple hΘ hn d hd).HWP.map (phiPrime ℚ n)) = 2 ∧
      ((PAmple hΘ hn d hd).HWP.map (phiPrime ℚ n)).map (projDeg ℚ n (2 * n)) =
        (PAmple hΘ hn d hd).hwPlane := by
  sorry

/-! ## The polarization `h` (§1.3) -/

/-- (§1.3, TeX lines 446–447) "When `P` is given by (1.2.4) the subspace
`H²(X × X̂, ℚ)^{Spin(V)_P}` is one-dimensional spanned by an ample class `h`": the
`Spin(V)_P`-invariants of `⋀² V_ℚ` (integral `Spin(V)_P`) are spanned by `h = Ξ_P^♯` (`hClass`; its
ampleness is `intro_hClass_isAmple`). Needs `n ≥ 2` (the intro's standing assumption): for `n = 1`
the invariants of `⋀² V_ℚ` are three-dimensional. -/
theorem intro_invQ_two (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 2 ≤ n) (d : ℚ) (hd : 0 < d) :
    (PAmple hΘ (by omega) d hd).invQ 2 =
      Submodule.span ℚ {(PAmple hΘ (by omega) d hd).hClass (PAmple_isCompl hΘ (by omega) d hd)} := by
  sorry

/-- (§1.3, TeX line 447, "by Proposition 2.4.4") `h = Ξ_P^♯` is ample on `X × X̂`: in the model
`H¹(X × X̂, ℚ) = V_ℚ ≅ ℚ^{4n}` (`coordV`), with the standard complex structure `-I_{V_ℝ}` of
`X × X̂` (`I_{V_ℝ} = productStructure n J` is the paper's convention, the negative of the standard
one), `h` is ample in the sense of `IsAmple`. (Checked numerically for `n = 1, 2, 3`.) -/
theorem intro_hClass_isAmple (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    IsAmple (2 * n)
      ((coordV ℝ n).toLinearMap ∘ₗ (-productStructure n J) ∘ₗ (coordV ℝ n).symm.toLinearMap)
      (ExteriorAlgebra.map (coordV ℚ n).toLinearMap
        ((PAmple hΘ hn d hd).hClass (PAmple_isCompl hΘ hn d hd))) := by
  sorry

/-- (§1.3, TeX lines 447–448) "Given an element `k ∈ K`, the rational endomorphism `η(k)` maps `h` to
`Nm(k) h`", `η(k)` acting on `H²(X × X̂, ℚ) = ⋀² V_ℚ` by `⋀² η_k`. (Checked numerically, `n = 3`.)
Stated for every `K`-secant `P` with `V_K = W₁ ⊕ W₂` (the paper: `P = P_Θ`). -/
theorem intro_eta_hClass {d : ℚ} (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (k : Kd d) :
    ExteriorAlgebra.map (P.η hW k) (P.hClass hW) = (Kd.Nm d k : ℚ) • P.hClass hW := by
  sorry

/-! ## Corollary 1.3.2 -/

/-- **Corollary 1.3.2** (`cor-kappa-class-is-Spin-V-P-invariant`), first sentence. If the rank `r`
of a `P`-secant`^{⊠2}`-object `E := Φ(F₁ ⊠ F₂^∨)` is non-zero, then its characteristic class `κ(E)` is
`Spin(V)_P`-invariant with respect to the representation `ρ`.

Model: `ch(E) = φ(w₁ ⊗ τ w₂)` (`secantSqClass ℚ n w₁ w₂`) with `wᵢ = ch(Fᵢ) ∈ P`; `Spin(V)_P` the
integral group of (2.2.2) (`P.spinPZ`) acting on `⋀• V_ℚ` by `ρ`. Any `K`-secant `P`. -/
theorem corollary1_3_2 {d : ℚ} (P : KSecant n d) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ)
    (hw₂ : w₂ ∈ P.Pℚ) (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) :
    kappa ℚ n (secantSqClass ℚ n w₁ w₂) ∈ invariantsExt ℚ n P.spinPZ := by
  sorry

/-- **Corollary 1.3.2** (`cor-kappa-class-is-Spin-V-P-invariant`), second sentence: "Consequently,
`κ(E)` remains of Hodge type under every deformation of `(X × X̂, η, h)` as a polarized abelian variety
of Weil type". Model: the deformations are parametrized by the period domain `Ω_P` (Lemma 4.0.2,
Corollary 4.0.4), and "of Hodge type" is membership in the Hodge ring `hodgeRingV n I`. Stated for
every `K`-secant satisfying Assumption 2.4.1 (the paper: `P = P_Θ`). -/
theorem corollary1_3_2_hodge {d : ℚ} (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hP.isCompl) :
    kappa ℚ n (secantSqClass ℚ n w₁ w₂) ∈ hodgeRingV n I := by
  sorry

/-- The invariance of Corollary 1.3.2 over any field `F` of characteristic `0` (the proof of the
corollary): if `g ∈ Spin(V_F)` fixes `w₁` and `w₂` (`m_g wᵢ = wᵢ`) and `φ(w₁ ⊗ τ w₂)` has non-zero
rank, then `ρ_g κ(φ(w₁ ⊗ τ w₂)) = κ(φ(w₁ ⊗ τ w₂))`. -/
theorem corollary1_3_2_field (F : Type*) [Field F] [CharZero F] (g : Spin F n) (w₁ w₂ : S F n)
    (h₁ : m F n (g : C F n) w₁ = w₁) (h₂ : m F n (g : C F n) w₂ = w₂)
    (hr : rankExt F n (secantSqClass F n w₁ w₂) ≠ 0) :
    rhoExt F n g (kappa F n (secantSqClass F n w₁ w₂)) = kappa F n (secantSqClass F n w₁ w₂) := by
  sorry

/-- Corollary 1.3.2 for `Spin(V_F)_P`, `F` any field of characteristic `0`: the base change of
`κ(E)` is invariant under every `g ∈ Spin(V_F)` fixing the `F`-span of `P` pointwise. -/
theorem corollary1_3_2_baseChange {d : ℚ} (P : KSecant n d) (F : Type*) [Field F] [CharZero F]
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) (g : Spin F n)
    (hg : g ∈ fixingSpin F n (Submodule.span F (bcS ℚ F n '' P.Pℚ))) :
    rhoExt F n g (bcExt ℚ F n (kappa ℚ n (secantSqClass ℚ n w₁ w₂))) =
      bcExt ℚ F n (kappa ℚ n (secantSqClass ℚ n w₁ w₂)) := by
  sorry

/-! ## Theorem 1.4.1 -/

section Theorem141

variable {J : Module.End ℝ (H1 ℝ 3)} {d : ℚ}

theorem pos_of_three_le (hd3 : 3 ≤ d) : 0 < d := by linarith

/-- **Theorem 1.4.1(1)** (`main-theorem-introduction`). The line `ℙ` in `ℙ(H^{even}(X, ℚ))` through
`ch(F₁^∨)` and `ch(F₂)` intersects the spinor variety at the two complex conjugate pure spinors
`exp(u)` and `exp(ū)` defined over `K = ℚ(√-d)`.

Model: `ch(F₂) = w`, `ch(F₁^∨) = τ(w)`, `w = chF1 d`. Stated: the plane spanned by `τ(w)` and `w` is
the plane `P` of `P_Θ` (whose `K`-span is `P_K = span_K{exp(u), exp(ū)}`), and over `ℂ` it is a
transversal secant meeting the even spinor variety exactly in the lines of `exp(±√-dΘ)`
(`IsTransversalSecant`, Lemma 10.1.1). -/
theorem theorem1_4_1_1 (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd3 : 3 ≤ d) :
    Submodule.span ℚ {tau ℚ 3 (chF1 d), chF1 d} = (PJac d hΘ (pos_of_three_le hd3)).Pℚ ∧
      Submodule.span (Kd d) {bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)), bcS ℚ (Kd d) 3 (chF1 d)} =
        (PJac d hΘ (pos_of_three_le hd3)).PK ∧
      IsTransversalSecant ℂ 3
        (Submodule.span ℂ {bcS ℚ ℂ 3 (tau ℚ 3 (chF1 d)), bcS ℚ ℂ 3 (chF1 d)})
        (IsNilpotent.exp (sqrtNeg d • bcS ℚ ℂ 3 (ThetaStd ℚ 3)))
        (IsNilpotent.exp (-(sqrtNeg d • bcS ℚ ℂ 3 (ThetaStd ℚ 3)))) := by
  sorry

/-- **Theorem 1.4.1(2)** (`main-theorem-introduction`), cohomological part: the rank of `E` is `8d`
(the rank of `ch(E) = τ(φ(w ⊗ w))`). The rest of (2) (`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]`, `E` simple reflexive) is
sheaf-theoretic. (Checked numerically for `d = 1, 2, 3, 5, 7`.) -/
theorem theorem1_4_1_2_rank (hd3 : 3 ≤ d) : rankExt ℚ 3 (chE d) = 8 * d := by
  sorry

/-- **Theorem 1.4.1(3)** (`main-theorem-introduction`). The characteristic class
`κ(E) = exp(-c₁(E)/rank(E)) ch(E)` remains of Hodge type under every deformation of
`(X × X̂, η, h)` as a polarized abelian sixfold of Weil type: `κ(E)` is a Hodge class for every
complex structure `I` in the period domain `Ω_P` of `P = P_Θ`. -/
theorem theorem1_4_1_3 (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd3 : 3 ≤ d)
    (I : Module.End ℝ (V ℝ 3))
    (hI : I ∈ (PJac d hΘ (pos_of_three_le hd3)).OmegaP (PJac_isCompl d hΘ (pos_of_three_le hd3))) :
    kappa ℚ 3 (chE d) ∈ hodgeRingV 3 I := by
  sorry

/-- **Theorem 1.4.1(4)** (`thm-item-K-translates-of-kappa-3-and-h-cube-span-HW`). The
`η(K)`-translates of the graded summand `κ₃(E)` of `κ(E)` in `H^{3,3}(X × X̂, ℚ)`, together with `h³`,
span the `3`-dimensional subspace `ℚh³ ⊕ ĤW_P`.

Model: `η(k)` acts on `H⁶(X × X̂, ℚ) = ⋀⁶ V_ℚ` by `⋀ η_k` (`ExteriorAlgebra.map`, (2.2.4));
`h = Ξ_P^♯` (`hClass`); `ĤW_P = hwPlane`; `κ₃(E) = kappa3E d`. The dimension is
`theorem1_4_1_4_finrank`. -/
theorem theorem1_4_1_4 (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd3 : 3 ≤ d) :
    Submodule.span ℚ
        (Set.range (fun k : Kd d =>
            ExteriorAlgebra.map ((PJac d hΘ (pos_of_three_le hd3)).η
              (PJac_isCompl d hΘ (pos_of_three_le hd3)) k) (kappa3E d)) ∪
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3}) =
      Submodule.span ℚ
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3} ⊔
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane := by
  sorry

/-- **Theorem 1.4.1(4)**, "the `3`-dimensional subspace `ℚh³ ⊕ ĤW_P`": the sum is direct and
three-dimensional. -/
theorem theorem1_4_1_4_finrank (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd3 : 3 ≤ d) :
    Disjoint (Submodule.span ℚ
        {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3})
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane ∧
      Module.finrank ℚ (Submodule.span ℚ
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3} ⊔
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane : Submodule ℚ (ExtV ℚ 3)) = 3 := by
  sorry

/-- `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))`: `ch(E) = τ(ch Φ(F₂ ⊠ F₁))`, `τ` is a ring automorphism of `H^{ev}`
acting by `(-1)^i` on `H^{2i}`, so `κ(τ x) = τ(κ x)`. Relates Theorem 1.4.1(4) to Lemma 8.3.1 (which
is about `Φ(F₁ ⊠ F₁)`, with the same Chern character as `Φ(F₂ ⊠ F₁)`). -/
theorem kappa3E_eq_neg :
    kappa3E d = -kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) := by
  sorry

end Theorem141

end WeilClasses
