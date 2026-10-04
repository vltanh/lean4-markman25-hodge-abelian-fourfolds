module

public import WeilClasses.AbelianVariety.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Algebraic classes and the results assumed about them

No Lean library can yet define algebraic cycles on a complex abelian variety and their classes in
`H*(A, ℚ)`. The main theorems are therefore stated for an arbitrary *system of algebraic classes*
(`WeilClasses.CycleClasses`): for every abelian variety `A` (up to isogeny, `WeilClasses.AbVar`) a
`ℚ`-subspace `Z.alg A ⊆ H*(A, ℚ)`; for the actual algebraic cycles this is the span of their classes.
The properties of algebraic classes that the paper's arguments use are hypotheses, one class per
source:

* `PullbackClosed`: the pullback of an algebraic class along a homomorphism of abelian varieties is
  algebraic (with Riemann's theorem that rational maps of Hodge structures between the `H¹` are
  induced by homomorphisms up to isogeny);
* `SubalgebraClosed`: `[A]` is algebraic and products of algebraic classes are algebraic
  (intersection product);
* `LefschetzOneOne`: rational classes of type `(1,1)` are algebraic (Lefschetz (1,1) theorem);
* `VoisinLocus`: in a connected family of polarized abelian varieties of Weil type, a flat rational
  class that is algebraic on a nonempty open subset of the base is algebraic everywhere (the
  algebraic locus is a countable union of closed analytic subsets [Voisin, *Hodge theory and
  complex algebraic geometry II*, §4.2 / Ch. 11.3], with Baire's theorem and the identity theorem;
  cited in the proof of Theorem 1.5.1);
* `VanGeemenModuli`: polarized abelian varieties of Weil type with the same `n`, `K` and
  discriminant lie, up to isogeny, in one connected family [van Geemen, Th. 5.2(3)] (cited in
  §1.1, used in the proof of Theorem 1.5.1);
* for Corollary 1.6.1: `SchoenDegeneration` [Schoen, Prop. 10], `MoonenZarhinSimple`
  [Moonen–Zarhin 1995, Th. 2.11], `RamonMariProducts` [Ramón-Marí, Th. 4.11],
  `MoonenZarhinLowDim` [Moonen–Zarhin 1999, Prop. 3.8 and Th. 0.1(i)].

The hypothesis attached to the paper's own sheaf-theoretic Sections 7–9 is in
`WeilClasses.Main.Hypotheses`.

The families are parametrized by the *Weil-type period domain* `WeilDomain η h`: the complex
structures `J` of a fixed `H¹(A, ℝ)` for which `(J, η, h)` is a polarized abelian variety of Weil
type (`WeilDomainMat`: as a set of real matrices, with the usual topology).
-/

@[expose] public section

namespace WeilClasses

/-! ## Systems of algebraic classes -/

/-- **A system of algebraic classes** on abelian varieties up to isogeny: for every `g` and every
complex structure `J` of `H¹(A, ℝ) = ℝ^{2g}`, a `ℚ`-subspace `alg g J ⊆ H*(A, ℚ) = ⋀• ℚ^{2g}`. For
actual algebraic cycles, `alg g J` is the span of the classes of algebraic cycles on an abelian
variety `A` with `H¹(A, ℚ) = ℚ^{2g}` and complex structure `J` (it depends only on the isogeny class);
its values at complex structures that are not those of abelian varieties play no role. -/
structure CycleClasses where
  /-- The algebraic classes of the abelian variety with complex structure `J`. -/
  alg : (g : ℕ) → Module.End ℝ (H1 ℝ g) → Submodule ℚ (S ℚ g)

/-- **Pullback of algebraic cycles.** For abelian varieties `A`, `B` and a rational map of Hodge
structures `φ : H¹(A, ℚ) → H¹(B, ℚ)`, the ring homomorphism `⋀φ : H*(A, ℚ) → H*(B, ℚ)` maps
algebraic classes to algebraic classes. (Every such `φ` is a rational multiple of the pullback by a
homomorphism `B → A` [Birkenhake–Lange, Prop. 1.2.? and §1.2]; pullback of cycles preserves
algebraicity [Fulton, Ch. 6–8].) -/
class PullbackClosed (Z : CycleClasses) : Prop where
  map_mem : ∀ {g g' : ℕ} (A : AbVar g) (B : AbVar g') (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g'),
    IsHodgeMap A.J B.J φ → ∀ α ∈ Z.alg g A.J, ExteriorAlgebra.map φ α ∈ Z.alg g' B.J

/-- **Intersection product.** On an abelian variety, the fundamental class `1 = [A]` is algebraic
and the product of two algebraic classes is algebraic. -/
class SubalgebraClosed (Z : CycleClasses) : Prop where
  one_mem : ∀ {g : ℕ} (A : AbVar g), (1 : S ℚ g) ∈ Z.alg g A.J
  mul_mem : ∀ {g : ℕ} (A : AbVar g) (α β : S ℚ g),
    α ∈ Z.alg g A.J → β ∈ Z.alg g A.J → α * β ∈ Z.alg g A.J

/-- **The Lefschetz (1,1) theorem.** Every rational class of type `(1,1)` on an abelian variety is
algebraic. -/
class LefschetzOneOne (Z : CycleClasses) : Prop where
  le : ∀ {g : ℕ} (A : AbVar g), A.hodge 1 ≤ Z.alg g A.J

/-! ## The Weil-type period domain -/

/-- **The Weil-type period domain** of `(η, h)` on `H¹ = ℚ^{4m}` (`m`-dimensional `η`-eigenspace
condition, `A` of dimension `2m`): the complex structures `J` of `H¹(A, ℝ)` such that `η(K)` acts by
endomorphisms of the Hodge structure, `(J, η)` is of Weil type, `h` is ample for `J`, and
`η(k)` maps `h` to `Nm(k) h`. -/
def WeilDomain {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) (h : S ℚ (2 * m)) :
    Set (Module.End ℝ (H1 ℝ (2 * m))) :=
  {J | IsComplexStructure J ∧ (∀ k, IsHodgeMap J J (η k)) ∧
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (sqrtNeg d) ⊓
      H10 (2 * m) J) = m ∧
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (-sqrtNeg d) ⊓
      H10 (2 * m) J) = m ∧
    IsAmple (2 * m) J h ∧ ∀ k, ExteriorAlgebra.map (η k) h = (Kd.Nm d k : ℚ) • h}

/-- The Weil-type period domain as a set of real matrices (in the standard basis of `H¹(A, ℝ)`),
with the usual topology. -/
noncomputable def WeilDomainMat {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m)))
    (h : S ℚ (2 * m)) : Set (Matrix (Fin (2 * (2 * m))) (Fin (2 * (2 * m))) ℝ) :=
  LinearMap.toMatrix' '' WeilDomain η h

/-- **[Voisin, §4.2]** (with Baire's theorem and the identity theorem). Over a connected component
`C` of a Weil-type period domain, the family of abelian varieties is a connected holomorphic family;
the locus where a fixed rational class `α` is algebraic is a countable union of closed analytic
subsets, so if it contains a nonempty open subset of `C` it is all of `C`. -/
class VoisinLocus (Z : CycleClasses) : Prop where
  spread : ∀ {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) (h : S ℚ (2 * m))
    (α : S ℚ (2 * m)) (J₀ : Module.End ℝ (H1 ℝ (2 * m)))
    (U : Set (Matrix (Fin (2 * (2 * m))) (Fin (2 * (2 * m))) ℝ)),
    U ⊆ connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀) → U.Nonempty →
    IsOpen ((↑) ⁻¹' U : Set (connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀))) →
    (∀ J, LinearMap.toMatrix' J ∈ U → α ∈ Z.alg (2 * m) J) →
    ∀ J, LinearMap.toMatrix' J ∈ connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀) →
      α ∈ Z.alg (2 * m) J

/-- **[van Geemen, Th. 5.2(3)]** (via Landherr's classification of Hermitian forms). Two polarized
abelian `2m`-folds of Weil type for the same `K` and with the same discriminant lie in one connected
family up to isogeny: there is a `K`-linear isomorphism `ψ` of their `H¹(·, ℚ)` mapping the
polarization of the first to a positive multiple of that of the second, and carrying the complex
structure of the first into the connected component of the Weil-type period domain of the second
that contains its complex structure. -/
class VanGeemenModuli : Prop where
  moduli : ∀ {m : ℕ} {d : ℚ}, 0 < d → ∀ (A A' : AbVar (2 * m)) (X : PolarizedWeilType A d)
    (X' : PolarizedWeilType A' d) (c : ℚ), X.DiscIs c → X'.DiscIs c →
    ∃ ψ : H1 ℚ (2 * m) ≃ₗ[ℚ] H1 ℚ (2 * m), (∀ k, ψ.toLinearMap ∘ₗ X.η k = X'.η k ∘ₗ ψ.toLinearMap) ∧
      (∃ c' : ℚ, 0 < c' ∧ ExteriorAlgebra.map ψ.toLinearMap X.h = c' • X'.h) ∧
      LinearMap.toMatrix' (bcMap ℚ ℝ ψ.toLinearMap ∘ₗ A.J ∘ₗ bcMap ℚ ℝ ψ.symm.toLinearMap) ∈
        connectedComponentIn (WeilDomainMat X'.η X'.h) (LinearMap.toMatrix' A'.J)

/-! ## Results assumed in the proof of Corollary 1.6.1 -/

/-- The span of the products `α β` of two rational classes of type `(1,1)` on `A`. -/
noncomputable def AbVar.divisorProducts {g : ℕ} (A : AbVar g) : Submodule ℚ (S ℚ g) :=
  Submodule.span ℚ {x | ∃ α ∈ A.hodge 1, ∃ β ∈ A.hodge 1, x = α * β}

/-- The span of the Hodge–Weil classes of all structures of Weil type on an abelian `2m`-fold
(for all imaginary quadratic fields `K = ℚ(√-d)`, `d` a positive integer). -/
noncomputable def AbVar.allHW {m : ℕ} (A : AbVar (2 * m)) : Submodule ℚ (S ℚ (2 * m)) :=
  ⨆ (d : ℕ) (_ : 0 < d) (X : WeilType A d), X.HW

/-- **[Schoen, Prop. 10]** (the degeneration argument, as used in the proof of Corollary 1.6.1):
for every imaginary quadratic field `K = ℚ(√-d)`, if the Hodge–Weil classes of all polarized abelian
sixfolds of Weil type for `K` with discriminant `-1` are algebraic, then so are the Hodge–Weil classes
of all abelian fourfolds of Weil type for `K` (of any discriminant). -/
class SchoenDegeneration (Z : CycleClasses) : Prop where
  imp : ∀ d : ℕ, 0 < d →
    (∀ (A : AbVar (2 * 3)) (X : PolarizedWeilType A d), X.DiscIs (-1) → X.HW ≤ Z.alg (2 * 3) A.J) →
    ∀ (A : AbVar (2 * 2)) (X : WeilType A d), X.HW ≤ Z.alg (2 * 2) A.J

/-- **[Moonen–Zarhin, *Hodge classes and Tate classes on simple abelian fourfolds*, Th. 2.11].**
For a simple abelian fourfold `A`, `H^{2,2}(A, ℚ)` is spanned by products of divisor classes and by
Hodge–Weil classes (for possibly infinitely many structures of Weil type). -/
class MoonenZarhinSimple : Prop where
  span : ∀ A : AbVar (2 * 2), A.IsSimple → A.hodge 2 ≤ A.divisorProducts ⊔ A.allHW

/-- `H¹(A, ℚ) = U₁ ⊕ U₂` is a decomposition into sub-Hodge structures of dimensions `2g₁` and `2g₂`:
up to isogeny, `A` is the product of abelian varieties of dimensions `g₁` and `g₂` with
`H¹ = U₁`, `U₂` (Poincaré). -/
def AbVar.SplitsAs {g : ℕ} (A : AbVar g) (U₁ U₂ : Submodule ℚ (H1 ℚ g)) (g₁ g₂ : ℕ) : Prop :=
  A.IsHodgeSub U₁ ∧ A.IsHodgeSub U₂ ∧ IsCompl U₁ U₂ ∧ Module.finrank ℚ U₁ = 2 * g₁ ∧
    Module.finrank ℚ U₂ = 2 * g₂

/-- The factor with `H¹ = U` of a decomposition is simple: `U ≠ 0` and no sub-Hodge structure of
`H¹(A, ℚ)` lies strictly between `0` and `U`. -/
def AbVar.SimpleFactor {g : ℕ} (A : AbVar g) (U : Submodule ℚ (H1 ℚ g)) : Prop :=
  U ≠ ⊥ ∧ ∀ U' ≤ U, A.IsHodgeSub U' → U' = ⊥ ∨ U' = U

/-- **[Ramón-Marí, Th. 4.11].** The Hodge conjecture holds for abelian fourfolds isogenous to the
product of two abelian surfaces. -/
class RamonMariProducts (Z : CycleClasses) : Prop where
  hc : ∀ (A : AbVar (2 * 2)) (U₁ U₂ : Submodule ℚ (H1 ℚ (2 * 2))), A.SplitsAs U₁ U₂ 2 2 →
    ∀ p, A.hodge p ≤ Z.alg (2 * 2) A.J

/-- **[Moonen–Zarhin, *Hodge classes on abelian varieties of low dimension*, Prop. 3.8 and
Th. 0.1(i)].** If `A` is isogenous to `B × E` with `B` a simple abelian threefold and `E` an elliptic
curve, then the Hodge ring of `A` is generated by divisor classes, or `B` and `E` both have complex
multiplication by the same imaginary quadratic field and the Hodge ring of `A` is generated by
divisor classes and Hodge–Weil classes; in either case `H^{2,2}(A, ℚ)` is spanned by products of
divisor classes and Hodge–Weil classes. -/
class MoonenZarhinLowDim : Prop where
  span : ∀ (A : AbVar (2 * 2)) (U U' : Submodule ℚ (H1 ℚ (2 * 2))), A.SplitsAs U U' 3 1 →
    A.SimpleFactor U → A.hodge 2 ≤ A.divisorProducts ⊔ A.allHW

end WeilClasses
