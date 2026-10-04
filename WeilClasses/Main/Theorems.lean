module

public import WeilClasses.Main.Compare
public import WeilClasses.Main.Intro

/-!
# The main results in the model of abelian varieties (Theorems 1.4.1 (3), (4), 1.5.1, Corollary 1.6.1)

The statements of record (`Challenge.lean`) in the library: Theorem 1.4.1 (3), (4) for the explicit
polarized abelian sixfold of Weil type `X × X̂` of `WeilClasses.Defs` (`fX`, `hX`, `JX`, `kappaX`),
Theorem 1.5.1 and Corollary 1.6.1 for a system of algebraic classes `Z` satisfying the hypotheses of
`WeilClasses.Defs`, and the compared theorems that check the definitions of the block.

* Theorem 1.4.1 (3), (4) follow from the paper's versions for the secant `P_Θ`
  (`WeilClasses.Main.Intro`) through the bridges of `WeilClasses.Main.Compare` (`f = η(√-d)`,
  `h = Ξ_P^♯`, the standard complex structure `-I_{V_ℝ}`, `coordV`).
* Theorem 1.5.1 follows the proof in §9.3: discriminant `-1` of `X × X̂` (Lemma 3.2.? for `n = 3`),
  `κ₃(E)` algebraic near `X × X̂` (`SecantSheafDeformation`), its `η(K)`-translates algebraic
  (`PullbackClosed`), `h³` algebraic (`LefschetzOneOne`, `SubalgebraClosed`), hence `ĤW` algebraic
  near `X × X̂` (Theorem 1.4.1(4)), on the whole connected component (`VoisinLocus`), and on every
  polarized abelian sixfold of Weil type with discriminant `-1` (`VanGeemenModuli`, `PullbackClosed`).
  For `d ∈ {1, 2}` the proof uses `ℚ(√-4d) = ℚ(√-d)`.
* Corollary 1.6.1 follows its proof (§1.6), with Lefschetz (1,1) and hard Lefschetz in the degrees
  other than `4`.
-/

@[expose] public section

namespace WeilClasses

/-! ### Compared theorems -/

/-- `Nm(a + b√-d) = a² + d b²`. -/
theorem Kd_Nm (d : ℚ) (hd : 0 < d) (a b : ℚ) :
    Kd.Nm d ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d) = a ^ 2 + d * b ^ 2 := by
  sorry

/-- `f² = -d` on `H¹(X × X̂, ℚ)` in the model. -/
theorem fX_mul_self (n : ℕ) (d : ℚ) : fX n d * fX n d = -(d • 1) := by
  sorry

/-- `X × X̂` with `(η, h)` is a polarized abelian `2n`-fold of Weil type (§2.4, Proposition 2.4.4,
Lemma 3.1.3): its complex structure lies in its Weil-type period domain. -/
theorem JX_mem_weilDomain (n : ℕ) (hn : 0 < n) (d : ℚ) (hd : 0 < d)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hΘ : IsAmple n J (ThetaStd ℚ n))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n))) (hη : η (Kd.sqrtNeg d) = fX n d) :
    JX n J ∈ WeilDomain η (hX n d) := by
  sorry

/-- The sheaf `E` of Theorem 1.4.1(2) has rank `8d`. -/
theorem rank_chE (d : ℚ) : ExteriorAlgebra.algebraMapInv (chE d) = 8 * d := by
  sorry

/-! ### Theorem 1.4.1 (3), (4) in the model -/

/-- **Theorem 1.4.1 (3)** (`main-theorem-introduction`), in the model: every graded summand of
`κ(E)` is a Hodge class on every deformation of `(X × X̂, η, h)` as a polarized abelian sixfold of
Weil type (the connected component of its Weil-type period domain). -/
theorem theorem1_4_1_3_model (d : ℕ) (hd : 3 ≤ d) (J : Module.End ℝ (H1 ℝ 3))
    (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3))) (hη : η (Kd.sqrtNeg d) = fX 3 d)
    (M : Matrix (Fin (2 * (2 * 3))) (Fin (2 * (2 * 3))) ℝ)
    (hM : M ∈ connectedComponentIn (WeilDomainMat η (hX 3 d)) (LinearMap.toMatrix' (JX 3 J)))
    (k : ℕ) : kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k := by
  sorry

/-- **Theorem 1.4.1 (4)** (`main-theorem-introduction`), in the model: the `η(K)`-translates of
`κ₃(E)`, together with `h³`, span the `3`-dimensional subspace `ℚ h³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`. -/
theorem theorem1_4_1_4_model (d : ℕ) (hd : 3 ≤ d) (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3)))
    (hη : η (Kd.sqrtNeg d) = fX 3 d) :
    Submodule.span ℚ
        (insert (hX 3 d ^ 3) (Set.range fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d))) =
      (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η ∧
    Module.finrank ℚ ↥((ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η) = 3 := by
  sorry

/-! ### Theorem 1.5.1 and Corollary 1.6.1 -/

/-- **Theorem 1.5.1** (`thm-algebraicity`). Let `d` be a positive integer and `K = ℚ(√-d)`. The
Hodge–Weil classes of polarized abelian sixfolds of Weil type with complex multiplication by `K`
and with discriminant `-1` are algebraic. -/
theorem theorem1_5_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [VanGeemenModuli] [SecantSheafDeformation Z]
    (d : ℕ) (hd : 0 < d) (A : AbVar (2 * 3)) (X : PolarizedWeilType A d) (hX : X.DiscIs (-1)) :
    X.HW ≤ Z.alg (2 * 3) A.J := by
  sorry

/-- **Corollary 1.6.1** (no label). The Hodge conjecture holds for abelian fourfolds: every Hodge
class is algebraic. -/
theorem corollary1_6_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [VanGeemenModuli] [SecantSheafDeformation Z]
    [SchoenDegeneration Z] [MoonenZarhinSimple] [RamonMariProducts Z] [MoonenZarhinLowDim]
    (A : AbVar (2 * 2)) (p : ℕ) : A.hodge p ≤ Z.alg (2 * 2) A.J := by
  sorry

end WeilClasses
