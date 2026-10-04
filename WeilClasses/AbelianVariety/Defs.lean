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
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Change of coefficients for linear maps between the `H¹`'s -/

/-- The extension of scalars `F → F'` of a linear map `F^{2g} → F^{2g'}` (in the standard bases). -/
noncomputable def bcMap (F F' : Type*) [Field F] [Field F'] [Algebra F F'] {g g' : ℕ}
    (φ : H1 F g →ₗ[F] H1 F g') : H1 F' g →ₗ[F'] H1 F' g' :=
  Matrix.toLin' ((LinearMap.toMatrix' φ).map (algebraMap F F'))

/-- A rational linear map `φ : H¹(A, ℚ) → H¹(B, ℚ)` is a morphism of Hodge structures: its real
extension intertwines the complex structures. -/
def IsHodgeMap {g g' : ℕ} (J : Module.End ℝ (H1 ℝ g)) (J' : Module.End ℝ (H1 ℝ g'))
    (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g') : Prop :=
  bcMap ℚ ℝ φ ∘ₗ J = J' ∘ₗ bcMap ℚ ℝ φ

/-! ## Abelian varieties up to isogeny -/

/-- **An abelian `g`-fold up to isogeny**: `H¹(A, ℚ) = ℚ^{2g}` with a complex structure `J` of
`H¹(A, ℝ)` (`J² = -1`, `H^{1,0}` its `i`-eigenspace) that admits an ample class. -/
structure AbVar (g : ℕ) where
  /-- The complex structure of `H¹(A, ℝ)`. -/
  J : Module.End ℝ (H1 ℝ g)
  isComplex : IsComplexStructure J
  polarizable : ∃ Θ : S ℚ g, IsAmple g J Θ

namespace AbVar

variable {g : ℕ} (A : AbVar g)

/-- The Hodge classes `H^{p,p}(A, ℚ)` of degree `2p`. -/
noncomputable def hodge (p : ℕ) : Submodule ℚ (S ℚ g) := hodgeClassesX g A.J p

/-- `A` and `B` are isogenous: `H¹(A, ℚ)` and `H¹(B, ℚ)` are isomorphic rational Hodge
structures. -/
def Isogenous {g' : ℕ} (B : AbVar g') : Prop :=
  ∃ φ : H1 ℚ g ≃ₗ[ℚ] H1 ℚ g', IsHodgeMap A.J B.J φ

/-- A sub-Hodge structure of `H¹(A, ℚ)`: a rational subspace `U` whose real span is stable under
`J`. They correspond to quotients `A → A'` up to isogeny, equivalently (Poincaré) to abelian
subvarieties. -/
def IsHodgeSub (U : Submodule ℚ (H1 ℚ g)) : Prop :=
  ∀ x ∈ Submodule.span ℝ (bcH1 ℚ ℝ g '' U), A.J x ∈ Submodule.span ℝ (bcH1 ℚ ℝ g '' U)

/-- `A` is simple: `g > 0` and `H¹(A, ℚ)` has no sub-Hodge structure other than `0` and itself. -/
def IsSimple : Prop := 0 < g ∧ ∀ U : Submodule ℚ (H1 ℚ g), A.IsHodgeSub U → U = ⊥ ∨ U = ⊤

end AbVar

/-! ## Abelian varieties of Weil type -/

/-- **An abelian `2m`-fold of Weil type** for `K = ℚ(√-d)` (§1.1, [Weil], [van Geemen §5]): an
embedding `η : K → End_ℚ(A)` such that the eigenspaces `W` and `W̄` of `η(√-d)` in `H¹(A, ℂ)` with
eigenvalues `√-d` and `-√-d` each meet `H^{1,0}(A)` in an `m`-dimensional subspace. -/
structure WeilType {m : ℕ} (A : AbVar (2 * m)) (d : ℚ) where
  /-- The action of `K` on `H¹(A, ℚ)` by rational endomorphisms of `A`. -/
  η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))
  isHodge : ∀ k, IsHodgeMap A.J A.J (η k)
  weil₁ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (sqrtNeg d) ⊓
    H10 (2 * m) A.J) = m
  weil₂ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (-sqrtNeg d) ⊓
    H10 (2 * m) A.J) = m

namespace WeilType

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : WeilType A d)

/-- `W ⊆ H¹(A, K)`: the eigenspace of `η(√-d)` with eigenvalue `√-d`. -/
noncomputable def W : Submodule (Kd d) (H1 (Kd d) (2 * m)) :=
  Module.End.eigenspace (bcMap ℚ (Kd d) (X.η (Kd.sqrtNeg d))) (Kd.sqrtNeg d)

/-- `W̄ ⊆ H¹(A, K)`: the eigenspace of `η(√-d)` with eigenvalue `-√-d`. -/
noncomputable def Wbar : Submodule (Kd d) (H1 (Kd d) (2 * m)) :=
  Module.End.eigenspace (bcMap ℚ (Kd d) (X.η (Kd.sqrtNeg d))) (-Kd.sqrtNeg d)

/-- **The Hodge–Weil classes** `ĤW ⊆ H^{2m}(A, ℚ)` (§1.1): the rational classes of degree `2m`
whose image in `H^{2m}(A, K)` lies in `⋀^{2m} W ⊕ ⋀^{2m} W̄`. -/
noncomputable def HW : Submodule ℚ (S ℚ (2 * m)) where
  carrier := {α | α ∈ ⋀[ℚ]^(2 * m) (H1 ℚ (2 * m)) ∧
    bcS ℚ (Kd d) (2 * m) α ∈ topWedge X.W (2 * m) ⊔ topWedge X.Wbar (2 * m)}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

end WeilType

/-- **A polarized abelian `2m`-fold of Weil type** `(A, η, h)` (§1.1, [van Geemen Def. 4.9]): an
ample class `h ∈ H^{1,1}(A, ℚ)` such that `η(k)` maps `h` to `Nm(k) h` for every `k ∈ K`. -/
structure PolarizedWeilType {m : ℕ} (A : AbVar (2 * m)) (d : ℚ) extends WeilType A d where
  /-- The polarization. -/
  h : S ℚ (2 * m)
  ample : IsAmple (2 * m) A.J h
  norm : ∀ k, ExteriorAlgebra.map (η k) h = (Kd.Nm d k : ℚ) • h

namespace PolarizedWeilType

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : PolarizedWeilType A d)

/-- The Riemann form `E(x, y) = ⟪h, x ∧ y⟫` of the polarization on `H₁(A, ℚ) = H¹(A, ℚ)*`. -/
noncomputable def E (x y : Module.Dual ℚ (H1 ℚ (2 * m))) : ℚ := eval2 ℚ (2 * m) X.h x y

/-- The action of `η(√-d)` on `H₁(A, ℚ)` (the transpose of its action on `H¹`). -/
noncomputable def fT : Module.Dual ℚ (H1 ℚ (2 * m)) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ (2 * m)) :=
  (X.η (Kd.sqrtNeg d)).dualMap

/-- Van Geemen's `K`-valued Hermitian form on `H₁(A, ℚ)` (§1.1):
`H(x, y) = E(x, η(√-d) y) + √-d E(x, y)`, as a complex number (it lies in `K`). -/
noncomputable def herm (x y : Module.Dual ℚ (H1 ℚ (2 * m))) : ℂ :=
  (X.E x (X.fT y) : ℂ) + sqrtNeg d * (X.E x y : ℂ)

/-- **The discriminant** (§1.1): `det H`, computed in a `K`-basis `b₁, …, b_{2m}` of `H₁(A, ℚ)`
(i.e. the `bᵢ` and `η(√-d) bᵢ` form a `ℚ`-basis), lies in `c · Nm(K^×)`. The class of `det H` in
`ℚ^×/Nm(K^×)` does not depend on the basis; `X.DiscIs (-1)` is the paper's "discriminant `-1`". -/
def DiscIs (c : ℚ) : Prop :=
  ∃ b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)),
    LinearIndependent ℚ (Sum.elim b (fun i => X.fT (b i))) ∧
    ∃ k : Kd d, k ≠ 0 ∧ (Matrix.of fun i j => X.herm (b i) (b j)).det = (c : ℂ) * (Kd.Nm d k : ℂ)

end PolarizedWeilType

end WeilClasses
