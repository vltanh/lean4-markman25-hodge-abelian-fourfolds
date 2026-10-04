module

public import WeilClasses.Spinor.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic

/-!
# Hodge decompositions and Hodge classes (paper §§2.2, 2.4, 3.2, 4)

A complex structure `I` on `V_ℝ` (`I² = -1`) defines the Hodge decomposition
`V_ℂ = V^{1,0} ⊕ V^{0,1}` into the eigenspaces of `I` with eigenvalues `i` and `-i` (Lemma 3.2.1's
convention), and hence the decomposition of `⋀^k V_ℂ` into the pieces
`⋀^{p,q} V = ⋀^p V^{1,0} ∧ ⋀^q V^{0,1}`. A rational class of type `(p, p)` is a *Hodge class*.
The same applies to a complex structure `J` on `H¹(X, ℝ)` and to `S = ⋀• H¹(X)`, whose rational
`(p, p)`-classes form the *Hodge ring* `⊕_p H^{p,p}(X, ℚ)` of `X` (§2.2).

The complex structure of `X × X̂` on `V_ℝ = H¹(X̂, ℝ) ⊕ H¹(X, ℝ)` is, in the paper's convention
(footnote in §2.4: the dual of `(I_X, I_{X̂})`, duals composing with `-I`), `(θ, w) ↦ (θ ∘ J, -J w)`,
the negative of the standard Hodge structure of `H¹(X × X̂)`; it is an isometry of the pairing
(1.2.2).

The complexification of a real endomorphism is computed in the standard bases.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (n : ℕ)

/-! ## Complexification of endomorphisms -/

/-- The `ℂ`-linear extension to `V_ℂ` of an `ℝ`-linear endomorphism of `V_ℝ`. -/
noncomputable def complexifyV (A : Module.End ℝ (V ℝ n)) : Module.End ℂ (V ℂ n) :=
  Matrix.toLin (basisV ℂ n) (basisV ℂ n)
    ((LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) A).map (algebraMap ℝ ℂ))

/-- The `ℂ`-linear extension to `H¹(X, ℂ)` of an `ℝ`-linear endomorphism of `H¹(X, ℝ)`. -/
noncomputable def complexifyH1 (A : Module.End ℝ (H1 ℝ n)) : Module.End ℂ (H1 ℂ n) :=
  Matrix.toLin (Pi.basisFun ℂ (Fin (2 * n))) (Pi.basisFun ℂ (Fin (2 * n)))
    ((LinearMap.toMatrix (Pi.basisFun ℝ (Fin (2 * n))) (Pi.basisFun ℝ (Fin (2 * n))) A).map
      (algebraMap ℝ ℂ))

/-! ## Complex structures and their eigenspaces -/

/-- A complex structure: an endomorphism with `I² = -1`. -/
def IsComplexStructure {M : Type*} [AddCommGroup M] [Module ℝ M] (I : Module.End ℝ M) : Prop :=
  I * I = -1

/-- `V^{1,0}`: the eigenspace of `I` in `V_ℂ` with eigenvalue `i`. -/
noncomputable def V10 (I : Module.End ℝ (V ℝ n)) : Submodule ℂ (V ℂ n) :=
  Module.End.eigenspace (complexifyV n I) Complex.I

/-- `V^{0,1}`: the eigenspace of `I` in `V_ℂ` with eigenvalue `-i`. -/
noncomputable def V01 (I : Module.End ℝ (V ℝ n)) : Submodule ℂ (V ℂ n) :=
  Module.End.eigenspace (complexifyV n I) (-Complex.I)

/-- `H^{1,0}(X)`: the eigenspace of `J` in `H¹(X, ℂ)` with eigenvalue `i`. -/
noncomputable def H10 (J : Module.End ℝ (H1 ℝ n)) : Submodule ℂ (H1 ℂ n) :=
  Module.End.eigenspace (complexifyH1 n J) Complex.I

/-- `H^{0,1}(X)`: the eigenspace of `J` in `H¹(X, ℂ)` with eigenvalue `-i`. -/
noncomputable def H01 (J : Module.End ℝ (H1 ℝ n)) : Submodule ℂ (H1 ℂ n) :=
  Module.End.eigenspace (complexifyH1 n J) (-Complex.I)

/-- **The complex structure `I = I_{V_ℝ}` of `X × X̂`** on `V_ℝ = H¹(X̂, ℝ) ⊕ H¹(X, ℝ)`, in the
convention of the paper (footnote in §2.4): `I_{V_ℝ}` is the complex structure of the Hodge structure
dual to `H₁(X, ℝ) ⊕ H₁(X̂, ℝ)` with the tangent complex structures `(I_X, I_{X̂})`, where the dual of
`(W, j)` is `(W*, -jᵀ)` ("composing with `-I`"). In our coordinates, with `J` the complex structure of
`H¹(X, ℝ)` whose `i`-eigenspace is `H^{1,0}(X)` (so that `I_X = Jᵀ` on `H₁(X, ℝ) = H¹(X, ℝ)*`), this is
`(θ, w) ↦ (θ ∘ J, -J w)`. It is an isometry of the pairing (1.2.2).

Its `i`-eigenspace, which the paper calls `V^{1,0}`, is the space of antiholomorphic forms of
`X × X̂`; the standard Hodge structure of `H¹(X × X̂)` is `-I`. Hodge classes, the Weil condition and
all statements of type `(p, p)` are the same for `I` and `-I`; the sign matters for positivity
(Proposition 2.4.4, Corollary 3.2.3, Lemma 4.0.1), where the paper's convention is the one used. -/
noncomputable def productStructure (J : Module.End ℝ (H1 ℝ n)) : Module.End ℝ (V ℝ n) :=
  (LinearMap.dualMap J : Module.End ℝ (Module.Dual ℝ (H1 ℝ n))).prodMap (-J)

/-! ## `(p, q)`-pieces of exterior algebras and Hodge classes -/

/-- The piece `⋀^p A ∧ ⋀^q B ⊆ ⋀^{p+q} M` spanned by the products of `p` vectors of `A` and `q`
vectors of `B`; for `A = V^{1,0}` and `B = V^{0,1}` this is `⋀^{p,q}`. -/
noncomputable def pqPiece {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (p q : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  Submodule.span R
    {x | ∃ (a : Fin p → M) (b : Fin q → M), (∀ i, a i ∈ A) ∧ (∀ j, b j ∈ B) ∧
      x = ExteriorAlgebra.ιMulti R p a * ExteriorAlgebra.ιMulti R q b}

/-- The subspace `⋀^k W ⊆ ⋀^k M` spanned by the products of `k` vectors of `W`. -/
noncomputable def topWedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (W : Submodule R M) (k : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  Submodule.span R {x | ∃ v : Fin k → M, (∀ i, v i ∈ W) ∧ x = ExteriorAlgebra.ιMulti R k v}

/-- The rational classes of type `(p, p)` in `H^{2p}(X × X̂, ℚ) = ⋀^{2p} V_ℚ` for the complex
structure `I` of `V_ℝ`: the Hodge classes of degree `2p`. -/
noncomputable def hodgeClassesV (I : Module.End ℝ (V ℝ n)) (p : ℕ) :
    Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) where
  carrier := {α | α ∈ ⋀[ℚ]^(2 * p) (V ℚ n) ∧
    bcExt ℚ ℂ n α ∈ pqPiece (V10 n I) (V01 n I) p p}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-- The rational classes of type `(p, p)` in `H^{2p}(X, ℚ) = ⋀^{2p} H¹(X, ℚ)` for the complex
structure `J` of `H¹(X, ℝ)`. -/
noncomputable def hodgeClassesX (J : Module.End ℝ (H1 ℝ n)) (p : ℕ) : Submodule ℚ (S ℚ n) where
  carrier := {α | α ∈ ⋀[ℚ]^(2 * p) (H1 ℚ n) ∧
    bcS ℚ ℂ n α ∈ pqPiece (H10 n J) (H01 n J) p p}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-- The Hodge ring `⊕_{p=0}^{n} H^{p,p}(X, ℚ)` of `X` (§2.2). -/
noncomputable def hodgeRingX (J : Module.End ℝ (H1 ℝ n)) : Submodule ℚ (S ℚ n) :=
  ⨆ p, hodgeClassesX n J p

/-- The Hodge classes of all degrees on `X × X̂`. -/
noncomputable def hodgeRingV (I : Module.End ℝ (V ℝ n)) : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ⨆ p, hodgeClassesV n I p

end WeilClasses
