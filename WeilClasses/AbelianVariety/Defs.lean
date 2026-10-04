module

public import WeilClasses.Hodge.Ample
public import WeilClasses.Basic.Field

/-!
# Abelian varieties up to isogeny, in the linear-algebra model

The main theorems of the paper (Theorem 1.5.1 and Corollary 1.6.1) are about algebraic cycles on
abelian varieties. Up to isogeny, a complex abelian variety `A` of dimension `g` is determined by the
rational Hodge structure `H¹(A, ℚ)` of weight one, which is polarizable, and every polarizable
rational Hodge structure of weight one arises this way (Riemann). Its rational cohomology ring is
`H*(A, ℚ) = ⋀• H¹(A, ℚ)`. Hodge classes and the Hodge conjecture are invariant under isogeny. So we
model:

* an abelian `g`-fold up to isogeny (`WeilClasses.AbVar g`): `H¹(A, ℚ) = ℚ^{2g}` (`H1 ℚ g`) with a
  complex structure `J` on `H¹(A, ℝ)`, whose `i`-eigenspace is `H^{1,0}(A)`, admitting an ample class
  (`WeilClasses.IsAmple`);
* its Hodge classes `hodgeClassesX g J p` (rational `(p,p)`-classes in `⋀^{2p} H¹(A, ℚ)`);
* homomorphisms (up to isogeny) through their action on `H¹`: rational maps of Hodge structures
  (`WeilClasses.IsHodgeMap`), so that `End_ℚ(A)` acts on `H¹(A, ℚ)` (§1.1);
* abelian varieties of Weil type (`WeilClasses.WeilType`, §1.1, [Weil], [van Geemen]): an embedding
  `η : K → End_ℚ(A)`, `K = ℚ(√-d)`, such that each eigenspace `W, W̄` of `η(√-d)` (eigenvalues `±√-d`)
  meets `H^{1,0}(A)` in a subspace of dimension `g/2`; polarized: with an ample `h` such that
  `η(k)` maps `h` to `Nm(k) h` (`WeilClasses.PolarizedWeilType`);
* the Hodge–Weil classes `ĤW ⊆ H^{g}(A, ℚ)`: the rational points of `⋀^{g}W ⊕ ⋀^{g}W̄`;
* van Geemen's Hermitian form `H(x, y) = E(x, η(√-d) y) + √-d E(x, y)` on `H₁(A, ℚ)` (where `E` is
  the polarization) and the discriminant `det H ∈ ℚ^×/Nm(K^×)` (§1.1);
* sub-Hodge structures (abelian subvarieties and quotients up to isogeny) and simple abelian
  varieties, for Corollary 1.6.1.

The orientation of `H¹(A, ℚ) = ℚ^{2g}` (the class `e₁ ∧ ⋯ ∧ e_{2g}`) plays no role here.

The definitions are in `WeilClasses.Defs` (the block shared with `Challenge.lean`); this file adds
isogenies, the eigenspaces `W`, `W̄` and basic API.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

namespace AbVar

variable {g : ℕ} (A : AbVar g)

/-- `A` and `B` are isogenous: `H¹(A, ℚ)` and `H¹(B, ℚ)` are isomorphic rational Hodge
structures. -/
def Isogenous {g' : ℕ} (B : AbVar g') : Prop :=
  ∃ φ : H1 ℚ g ≃ₗ[ℚ] H1 ℚ g', IsHodgeMap A.J B.J φ

end AbVar

namespace WeilType

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : WeilType A d)

/-- `W ⊆ H¹(A, K)`: the eigenspace of `η(√-d)` with eigenvalue `√-d`. -/
noncomputable def W : Submodule (Kd d) (H1 (Kd d) (2 * m)) :=
  Module.End.eigenspace (bcMap ℚ (Kd d) (X.η (Kd.sqrtNeg d))) (Kd.sqrtNeg d)

/-- `W̄ ⊆ H¹(A, K)`: the eigenspace of `η(√-d)` with eigenvalue `-√-d`. -/
noncomputable def Wbar : Submodule (Kd d) (H1 (Kd d) (2 * m)) :=
  Module.End.eigenspace (bcMap ℚ (Kd d) (X.η (Kd.sqrtNeg d))) (-Kd.sqrtNeg d)

/-- The Hodge–Weil classes are the rational classes of degree `2m` whose image in `H^{2m}(A, K)` lies
in `⋀^{2m} W ⊕ ⋀^{2m} W̄`. -/
theorem mem_HW_iff (α : S ℚ (2 * m)) :
    α ∈ X.HW ↔ α ∈ ⋀[ℚ]^(2 * m) (H1 ℚ (2 * m)) ∧
      bcS ℚ (Kd d) (2 * m) α ∈ topWedge X.W (2 * m) ⊔ topWedge X.Wbar (2 * m) := by
  exact Iff.rfl

end WeilType

end WeilClasses
