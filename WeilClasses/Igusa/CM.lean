module

public import WeilClasses.Igusa.Secant

/-!
# Complex multiplication from a rational class with positive Igusa invariant (paper §10.2)

Here `X` is an abelian threefold (`n = 3`). For `w ∈ S⁺_ℚ` the Igusa invariant `d := J(w)` is
rational (`J` is defined over `ℚ`, `J_bcS`); when `d > 0` we set `K := ℚ(√-d)` (`Kd (J ℚ w)`, with
the paper's `√-d = i√d`); `-d` is then not a rational square.

* **Lemma 10.2.1**: the two maximal isotropic subspaces of `V_ℂ` invariant under `Spin(V_ℚ)_w` are
  defined over `K`, not over `ℚ`, and exchanged by `σ` (`lemma10_2_1`); the centralizer of
  `ρ(Spin(V_ℚ)_w)` in `Õ(V_ℚ)` (2.2.3) is isomorphic to `K^×` (`lemma10_2_1_centralizer`).
  Claims of its proof: the secant through `w` is a rational `K`-secant with `V_K = W₁ ⊕ W₂`
  (`lemma10_2_1_secant`) and `Spin(V_ℚ)_w = Spin(V_ℚ)_P` (`lemma10_2_1_spinStab_eq`, from
  Remark 2.2.3, `n = 3` odd). The text after the lemma: the image of `η : K^× → GL(V_ℚ)` (2.2.4) is
  the centralizer (`eta_centralizer_spinStab`).
* **Example 10.2.2** (`example-gulbrandsen`): `J(2 - dΘ²) = 16d³`, so `K = ℚ(√-d)`, for
  `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` as printed; this `Θ` has `Θ³ = -6[pt_X]`, so it is not a
  principal polarization in the orientation `∫_X e₁ ∧ ⋯ ∧ e₆ = 1` of §10.1 (slip of the paper); the
  value is the same for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, `Θ'³ = 6[pt_X]`
  (`example10_2_2_principal`), and `2 - dΘ'² = 2α` for the class `α = 1 - (d/2)Θ'²` of
  Lemma 8.2.1.
* **Example 10.2.3**: `J(1 - m[pt_X]) = -m²/4 = -(m/2)²` (`m` the length of a zero-dimensional
  subscheme), so `-J` is a rational square and `K = ℚ`.

The sheaf-theoretic content of the examples (Gulbrandsen's moduli spaces, Chern characters of
vector bundles and ideal sheaves) is not formalized; only the cohomological identities are.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Lemma 10.2.1 -/

/-- **Lemma 10.2.1** (`lemma-imaginary-quadratic-field-is-centralizer-sixfold-case`), first
sentence. Let `w ∈ S⁺_ℚ` with `d := J(w) > 0`, and `K = ℚ(√-d)` (`Kd (J ℚ w)`). Then the two maximal
isotropic subspaces `W₁, W₂` of `V_ℂ` invariant under `Spin(V_ℚ)_w` (acting through
`Spin(V_ℚ) → Spin(V_ℂ)` and `ρ`) are defined over `K` — they are the base changes of subspaces
`W₁, W₂ ⊆ V_K` — but not over `ℚ`, and `σ(W₁) = W₂`.
Reading: "the two maximal isotropic subspaces of `V_ℂ` invariant under `Spin(V_ℚ)_w`" asserts that
there are exactly two such subspaces; this is stated as the equivalence below (it uses that
`Spin(V_ℚ)_w` is Zariski dense in `Spin(V_ℂ)_w ≅ SL(W₁)`, which the paper does not discuss). -/
theorem lemma10_2_1 (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ W₁ W₂ : Submodule (Kd (J ℚ w)) (V (Kd (J ℚ w)) 3),
      W₁ ≠ W₂ ∧
      (∀ W : Submodule ℂ (V ℂ 3),
        IsMaxIsotropic ℂ 3 W ∧ IsInvariantUnder ℚ ℂ 3 (spinStab ℚ 3 w) W ↔
          W = bcSubV (Kd (J ℚ w)) ℂ 3 W₁ ∨ W = bcSubV (Kd (J ℚ w)) ℂ 3 W₂) ∧
      ¬ IsDefinedOverV ℚ ℂ 3 (bcSubV (Kd (J ℚ w)) ℂ 3 W₁) ∧
      ¬ IsDefinedOverV ℚ ℂ 3 (bcSubV (Kd (J ℚ w)) ℂ 3 W₂) ∧
      σV 3 (J ℚ w) '' (W₁ : Set (V (Kd (J ℚ w)) 3)) = (W₂ : Set (V (Kd (J ℚ w)) 3)) := by
  sorry

/-- **Lemma 10.2.1** (`lemma-imaginary-quadratic-field-is-centralizer-sixfold-case`), second
sentence. For `w ∈ S⁺_ℚ` with `d := J(w) > 0` and `K = ℚ(√-d)`, the centralizer of
`ρ(Spin(V_ℚ)_w)` in the group `Õ(V_ℚ)` of rational similarities with multiplier in `Nm(K^×)`
(2.2.3) is isomorphic to `K^×`. -/
theorem lemma10_2_1_centralizer (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    Nonempty (↥(Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓
      Otilde 3 (J ℚ w)) ≃* (Kd (J ℚ w))ˣ) := by
  sorry

/-- (Proof of Lemma 10.2.1, l. 9792–9796, with Lemma 10.1.1.) For `w ∈ S⁺_ℚ` with
`d := J(w) > 0`, the secant `P_w` through `w` is a rational `K`-secant in the sense of §2.2: there
is `P : KSecant 3 d` (an even pure spinor `u₁ ∈ S⁺_K` and `u₂ = σ(u₁)`) with `V_K = W₁ ⊕ W₂`, whose
rational plane `P ⊆ S⁺_ℚ` contains `w`, such that `P_K ⊗ ℂ` is the transversal secant through `w`
of Lemma 10.1.1, spanned by `u₁, u₂`, and is the base change of `P` ("`P_w` is defined over
`ℚ`"). -/
theorem lemma10_2_1_secant (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ P : KSecant 3 (J ℚ w), IsCompl P.W₁ P.W₂ ∧ w ∈ P.Pℚ ∧
      IsTransversalSecant ℂ 3 (bcSubS (Kd (J ℚ w)) ℂ 3 P.PK)
        (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) ∧
      bcSubS (Kd (J ℚ w)) ℂ 3 P.PK = bcSubS ℚ ℂ 3 P.Pℚ := by
  sorry

/-- (Proof of Lemma 10.2.1, l. 9798, by Remark 2.2.3 with `n = 3` odd.) For `w ∈ S⁺_ℚ` with
`J(w) > 0` and a `K`-secant `P` with `V_K = W₁ ⊕ W₂` whose rational plane contains `w`,
`Spin(V_ℚ)_w = Spin(V_ℚ)_P`. -/
theorem lemma10_2_1_spinStab_eq (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    spinStab ℚ 3 w = P.spinPℚ := by
  sorry

/-- (Text after Lemma 10.2.1, l. 9842.) Let `w ∈ S⁺_ℚ` with `d := J(w) > 0`, and orient the
secant `P` through `w` (the choice of `W₁`). The homomorphism `η : K^× → GL(V_ℚ)` of (2.2.4) is
injective, its image is contained in `Õ(V_ℚ)`, and it equals the centralizer of `ρ(Spin(V_ℚ)_w)` in
`Õ(V_ℚ)` (by Lemma 2.2.4). -/
theorem eta_centralizer_spinStab (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    (∀ l l' : (Kd (J ℚ w))ˣ, P.η hW l = P.η hW l' → l = l') ∧
      (∀ l : (Kd (J ℚ w))ˣ, ∃ h ∈ Otilde 3 (J ℚ w), (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l) ∧
      ∀ h : V ℚ 3 ≃ₗ[ℚ] V ℚ 3,
        h ∈ Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓
            Otilde 3 (J ℚ w) ↔
          ∃ l : (Kd (J ℚ w))ˣ, (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l := by
  sorry

/-! ## Example 10.2.2 -/

section Example

variable (F : Type*) [Field F] [CharZero F]

/-- The class `e_i ∧ e_j ∈ H²(X, F)` (0-based indices). -/
noncomputable def wedge2 (i j : Fin 6) : S F 3 :=
  ExteriorAlgebra.ι F (e F 3 i) * ExteriorAlgebra.ι F (e F 3 j)

/-- The class `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` of Example 10.2.2, as printed (0-based indices).
In the coordinates of §10.1 (`∫_X e₁ ∧ ⋯ ∧ e₆ = 1`) it has `Θ³ = -6 [pt_X]` (`thetaEx_cube`). -/
noncomputable def thetaEx : S F 3 := wedge2 F 0 3 + wedge2 F 1 4 + wedge2 F 2 5

/-- The class `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, with `Θ'³ = 6 [pt_X]` (`thetaEx'_cube`), i.e.
`Θ'³/3! = [pt_X]` as for a principal polarization (§8.2). -/
noncomputable def thetaEx' : S F 3 := -wedge2 F 0 3 + wedge2 F 1 4 + wedge2 F 2 5

/-- The slip in Example 10.2.2: with `∫_X e₁ ∧ ⋯ ∧ e₆ = 1`, the printed
`Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` has `Θ³ = -6 [pt_X]`, whereas a principal polarization has
`Θ³/3! = [pt_X]`. -/
theorem thetaEx_cube : thetaEx F ^ 3 = (-6 : F) • pt F 3 := by
  sorry

/-- `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` satisfies `Θ'³ = 6 [pt_X]`. -/
theorem thetaEx'_cube : thetaEx' F ^ 3 = (6 : F) • pt F 3 := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), the computation of `Θ²` (l. 9854–9860):
`Θ² = 2[e₁∧e₄∧e₂∧e₅ + e₁∧e₄∧e₃∧e₆ + e₂∧e₅∧e₃∧e₆] = (-2)(e₃₆^* + e₂₅^* + e₁₄^*)` for the printed
`Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. -/
theorem example10_2_2_theta_sq :
    thetaEx F ^ 2 = 2 * (wedge2 F 0 3 * wedge2 F 1 4 + wedge2 F 0 3 * wedge2 F 2 5 +
        wedge2 F 1 4 * wedge2 F 2 5) ∧
      thetaEx F ^ 2 = (-2 : F) • (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9861: `w := 2 - dΘ²` equals
`2 + 2d(e₃₆^* + e₂₅^* + e₁₄^*)`, for the printed `Θ`. -/
theorem example10_2_2_w (d : F) :
    (2 : S F 3) - d • thetaEx F ^ 2 =
      2 + (2 * d) • (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9861, the intermediate steps:
`J(w) = 2⁴ d³ J(1 + (e₃₆^* + e₂₅^* + e₁₄^*))` and `J(1 + (e₃₆^* + e₂₅^* + e₁₄^*)) = 1`
(Remark 10.1.2(1) with `d = 1`), for `w = 2 - dΘ²` with the printed `Θ`. -/
theorem example10_2_2_steps (d : F) :
    J F (2 - d • thetaEx F ^ 2) =
        2 ^ 4 * d ^ 3 * J F (1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3)) ∧
      J F (1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3)) = 1 := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9854 and l. 9861: the Igusa invariant of
`w = 2 - dΘ²` (the Chern character of a bundle in Gulbrandsen's `M(2, 0, dΘ²)`) is
`J(w) = 16 d³`, for the printed `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. The paper takes `d` a positive
integer; the identity holds for every `d ∈ F`.
Slip of the paper: it says that `H¹(X, ℤ)` has a basis with `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` for
the principal polarization `Θ`; with the normalization `∫_X e₁ ∧ ⋯ ∧ e₆ = 1` of §10.1 this class has
`Θ³ = -6 [pt_X]` (`thetaEx_cube`), while a principal polarization has `Θ³ = 6 [pt_X]`. The value is
the same for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, `Θ'³ = 6 [pt_X]` (`example10_2_2_principal`); in
fact `J(2 - dΘ²) = 16 d³ (∫_X Θ³ / 6)²` for every `Θ ∈ H²(X)` (checked numerically). -/
theorem example10_2_2 (d : F) : J F (2 - d • thetaEx F ^ 2) = 16 * d ^ 3 := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`) with a class `Θ'` satisfying `Θ'³ = 6 [pt_X]` (as a
principal polarization does in the orientation of §10.1), correcting the slip of the printed basis:
`J(2 - dΘ'²) = 16 d³` for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. -/
theorem example10_2_2_principal (d : F) : J F (2 - d • thetaEx' F ^ 2) = 16 * d ^ 3 := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), last sentence (l. 9864): `w = 2α`, where
`α = 1 - (d/2)Θ²` is the class of Lemma 8.2.1 (there `Θ³/6 = [pt_X]`; we take `Θ'`); hence
`J(α) = d³`. -/
theorem example10_2_2_alpha (d : F) :
    (2 : S F 3) - d • thetaEx' F ^ 2 = 2 * (1 - (d / 2) • thetaEx' F ^ 2) ∧
      J F (1 - (d / 2) • thetaEx' F ^ 2) = d ^ 3 := by
  sorry

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9854, "so that `K = ℚ(√-d)`": for `d > 0` the
field `ℚ(√-J(w))`, `w = 2 - dΘ²`, is `ℚ(√-d)`, for the printed `Θ` and for `Θ'`. -/
theorem example10_2_2_field (d : ℚ) (hd : 0 < d) :
    Kd (J ℚ (2 - d • thetaEx ℚ ^ 2)) = Kd d ∧ Kd (J ℚ (2 - d • thetaEx' ℚ ^ 2)) = Kd d := by
  sorry

end Example

/-! ## Example 10.2.3 -/

/-- **Example 10.2.3** (no label). The Igusa invariant of `1 - m[pt_X]` (the Chern character of the
ideal sheaf of a zero-dimensional subscheme of length `m`; the paper's `n`) is
`J(1 - m[pt_X]) = -(1/4) m² = -(m/2)²`. -/
theorem example10_2_3 (F : Type*) [Field F] [CharZero F] (m : ℕ) :
    J F (1 - (m : F) • pt F 3) = -(1 / 4) * (m : F) ^ 2 ∧
      -(1 / 4) * (m : F) ^ 2 = -((m : F) / 2) ^ 2 := by
  sorry

/-- **Example 10.2.3** (no label), "and so `K = ℚ`": `-J(1 - m[pt_X])` is the square of a rational
number, so `ℚ(√-J(1 - m[pt_X])) = ℚ`. -/
theorem example10_2_3_field (m : ℕ) : IsSquare (-J ℚ (1 - (m : ℚ) • pt ℚ 3)) := by
  sorry

end WeilClasses
