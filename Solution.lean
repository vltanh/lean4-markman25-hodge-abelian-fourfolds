module

public import WeilClasses.Main.Theorems

/-!
# Solution: proofs of the statements of record

Each theorem of `Challenge.lean` is restated here verbatim, under the same name, and proved from the
development. The definitions the statements use come from `WeilClasses/Defs.lean`, of which
`Challenge.lean` holds a verbatim copy, so Comparator sees the same constants in both. This module
is also the entry point of the development.
-/

@[expose] public section

namespace WeilClasses.Challenge

open WeilClasses

/-! ### Compared theorems: the definitions are the intended ones -/

/-- `Nm(a + b√-d) = a² + d b²`. -/
theorem Kd_Nm (d : ℚ) (hd : 0 < d) (a b : ℚ) :
    Kd.Nm d ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d) = a ^ 2 + d * b ^ 2 :=
  WeilClasses.Kd_Nm d hd a b

/-- `f² = -d` on `H¹(X × X̂, ℚ)`, so `√-d ↦ f` defines an action of `K = ℚ(√-d)`. -/
theorem fX_mul_self (n : ℕ) (d : ℚ) : fX n d * fX n d = -(d • 1) :=
  WeilClasses.fX_mul_self n d

/-- `X × X̂` with `(η, h)` is a polarized abelian `2n`-fold of Weil type (§2.4, Proposition 2.4.4,
Corollary 3.2.3): its complex structure lies in its Weil-type period domain. -/
theorem JX_mem_weilDomain (n : ℕ) (d : ℚ) (hd : 0 < d)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hΘ : IsAmple n J (ThetaStd ℚ n))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n))) (hη : η (Kd.sqrtNeg d) = fX n d) :
    JX n J ∈ WeilDomain η (hX n d) :=
  WeilClasses.JX_mem_weilDomain n d hd J hJ hΘ η hη

/-- The discriminant of `X × X̂` is `(-1)ⁿ` (Lemma 3.1.3): every polarized abelian `2n`-fold of Weil
type with the action and the polarization of `X × X̂` has discriminant `(-1)ⁿ`. -/
theorem discIs_XXhat (n : ℕ) (d : ℚ) (hd : 0 < d) (A : AbVar (2 * n)) (X : PolarizedWeilType A d)
    (hη : X.η (Kd.sqrtNeg d) = fX n d) (hh : X.h = hX n d) : X.DiscIs ((-1) ^ n) :=
  WeilClasses.discIs_XXhat n d hd A X hη hh

/-- The sheaf `E` of Theorem 1.4.1(2) has rank `8d`. -/
theorem rank_chE (d : ℚ) : ExteriorAlgebra.algebraMapInv (chE d) = 8 * d :=
  WeilClasses.rank_chE d

/-! ### Theorem 1.4.1 -/

/-- **Theorem 1.4.1(3).** Let `X` be a principally polarized abelian threefold (in the paper the
Jacobian of a non-hyperelliptic curve of genus `3`) and `d ≥ 3`. Every graded summand `κ_k(E)` of
`κ(E)` is of Hodge type on every deformation of `(X × X̂, η, h)` as a polarized abelian sixfold of
Weil type. -/
theorem theorem1_4_1_3 (d : ℕ) (hd : 3 ≤ d) (J : Module.End ℝ (H1 ℝ 3))
    (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3))) (hη : η (Kd.sqrtNeg d) = fX 3 d)
    (M : Matrix (Fin (2 * (2 * 3))) (Fin (2 * (2 * 3))) ℝ)
    (hM : M ∈ connectedComponentIn (WeilDomainMat η (hX 3 d)) (LinearMap.toMatrix' (JX 3 J)))
    (k : ℕ) : kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k :=
  WeilClasses.theorem1_4_1_3_model d hd J hJ hΘ η hη M hM k

/-- **Theorem 1.4.1(4).** The `η(K)`-translates of `κ₃(E) ∈ H⁶(X × X̂, ℚ)`, together with `h³`,
span the `3`-dimensional subspace `ℚ h³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`. -/
theorem theorem1_4_1_4 (d : ℕ) (hd : 3 ≤ d) (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3)))
    (hη : η (Kd.sqrtNeg d) = fX 3 d) :
    Submodule.span ℚ
        (insert (hX 3 d ^ 3) (Set.range fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d))) =
      (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η ∧
    Module.finrank ℚ ↥((ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η) = 3 :=
  WeilClasses.theorem1_4_1_4_model d hd η hη

/-! ### Theorem 1.5.1 and Corollary 1.6.1 -/

/-- **Theorem 1.5.1.** Let `d` be a positive integer and `K = ℚ(√-d)`. The Hodge–Weil classes of
polarized abelian sixfolds of Weil type with complex multiplication by `K` and with discriminant
`-1` are algebraic. -/
theorem theorem1_5_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [SecantSheafDeformation Z]
    (d : ℕ) (hd : 0 < d) (A : AbVar (2 * 3)) (X : PolarizedWeilType A d) (hdisc : X.DiscIs (-1)) :
    X.HW ≤ Z.alg (2 * 3) A.J :=
  WeilClasses.theorem1_5_1 Z d hd A X hdisc

/-- **Corollary 1.6.1.** The Hodge conjecture holds for abelian fourfolds: every Hodge class is
algebraic. -/
theorem corollary1_6_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [SecantSheafDeformation Z]
    [SchoenDegeneration Z] [MoonenZarhinSimple] [RamonMariProducts Z] [MoonenZarhinLowDim]
    (A : AbVar (2 * 2)) (p : ℕ) : A.hodge p ≤ Z.alg (2 * 2) A.J :=
  WeilClasses.corollary1_6_1 Z A p

end WeilClasses.Challenge
