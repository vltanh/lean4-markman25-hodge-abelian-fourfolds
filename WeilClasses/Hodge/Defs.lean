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

/-! ## Complex structures and their eigenspaces -/

/-- `V^{1,0}`: the eigenspace of `I` in `V_ℂ` with eigenvalue `i`. -/
noncomputable def V10 (I : Module.End ℝ (V ℝ n)) : Submodule ℂ (V ℂ n) :=
  Module.End.eigenspace (complexifyV n I) Complex.I

/-- `V^{0,1}`: the eigenspace of `I` in `V_ℂ` with eigenvalue `-i`. -/
noncomputable def V01 (I : Module.End ℝ (V ℝ n)) : Submodule ℂ (V ℂ n) :=
  Module.End.eigenspace (complexifyV n I) (-Complex.I)

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

/-- The rational classes of type `(p, p)` in `H^{2p}(X × X̂, ℚ) = ⋀^{2p} V_ℚ` for the complex
structure `I` of `V_ℝ`: the Hodge classes of degree `2p`. -/
noncomputable def hodgeClassesV (I : Module.End ℝ (V ℝ n)) (p : ℕ) :
    Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ⋀[ℚ]^(2 * p) (V ℚ n) ⊓
    ((pqPiece (V10 n I) (V01 n I) p p).restrictScalars ℚ).comap (bcExt ℚ ℂ n).toLinearMap

theorem mem_hodgeClassesV_iff (I : Module.End ℝ (V ℝ n)) (p : ℕ) (α : ExteriorAlgebra ℚ (V ℚ n)) :
    α ∈ hodgeClassesV n I p ↔
      α ∈ ⋀[ℚ]^(2 * p) (V ℚ n) ∧ bcExt ℚ ℂ n α ∈ pqPiece (V10 n I) (V01 n I) p p := by
  simp [hodgeClassesV, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]

/-- The Hodge classes of degree `2p` on `X` (`WeilClasses.hodgeClassesX`, in `WeilClasses.Defs`):
rational classes of degree `2p` of type `(p, p)`. -/
theorem mem_hodgeClassesX_iff (J : Module.End ℝ (H1 ℝ n)) (p : ℕ) (α : S ℚ n) :
    α ∈ hodgeClassesX n J p ↔
      α ∈ ⋀[ℚ]^(2 * p) (H1 ℚ n) ∧ bcS ℚ ℂ n α ∈ pqPiece (H10 n J) (H01 n J) p p := by
  simp [hodgeClassesX, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]

/-- The Hodge ring `⊕_{p=0}^{n} H^{p,p}(X, ℚ)` of `X` (§2.2). -/
noncomputable def hodgeRingX (J : Module.End ℝ (H1 ℝ n)) : Submodule ℚ (S ℚ n) :=
  ⨆ p, hodgeClassesX n J p

/-- The Hodge classes of all degrees on `X × X̂`. -/
noncomputable def hodgeRingV (I : Module.End ℝ (V ℝ n)) : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ⨆ p, hodgeClassesV n I p

end WeilClasses
