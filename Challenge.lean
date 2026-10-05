module

public import Mathlib

/-!
# Statements of record: Markman, cycles on abelian 2n-folds of Weil type

This file states, in Mathlib's vocabulary, the main results of E. Markman, *Cycles on abelian
2n-folds of Weil type from secant sheaves on abelian n-folds*, arXiv:2502.03415v2 (2025), as this
project proves them. It imports only Mathlib. The definitions it uses are written out below,
between the markers `BEGIN SHARED DEFINITIONS` and `END SHARED DEFINITIONS`, a verbatim copy of the
block in `WeilClasses/Defs.lean`. Numbering follows the paper.

## The model

No Lean library has algebraic cycles on complex abelian varieties yet, so the statements are about
the linear algebra that the paper's arguments act on.

* **Abelian varieties up to isogeny** (`AbVar g`): `H¹(A, ℚ) = ℚ^{2g}` with a complex structure `J`
  of `H¹(A, ℝ)` admitting an ample class; `H*(A, ℚ) = ⋀• H¹(A, ℚ)`. By Riemann's theorem these are
  exactly the polarizable rational Hodge structures of weight one, i.e. abelian varieties up to
  isogeny, which is all the Hodge conjecture sees. Conventions: `H^{1,0}(A)` is the `i`-eigenspace
  of `J` on `H¹(A, ℂ)` (`H10`); a class `Θ ∈ H²` is ample (`IsAmple`) if it has type `(1,1)` and
  `⟪Θ, a ∧ (a ∘ J)⟫ > 0` for all nonzero `a ∈ H₁(A, ℝ) = H¹(A, ℝ)*` (Kähler positivity, as in
  [Huybrechts, *Complex geometry*, 1.2.15]). Hodge classes `A.hodge p` are the rational classes in
  `⋀^{2p}` of type `(p, p)`.
* **Weil type** (§1.1): `K = ℚ(√-d) ⊆ ℂ` with `√-d = i√d` (`Kd`); an abelian `2m`-fold of Weil type
  is `η : K → End_ℚ(H¹(A, ℚ))` acting by endomorphisms of Hodge structure with both eigenspaces of
  `η(√-d)` meeting `H^{1,0}` in dimension `m` (`WeilType`); polarized if moreover `h` is ample and
  `η(k)^* h = Nm(k) h` (`PolarizedWeilType`). The Hodge–Weil classes `ĤW` are the rational classes
  of `⋀^{2m} W ⊕ ⋀^{2m} W̄` (`HWof`). The discriminant is that of van Geemen's Hermitian form
  `H(x, y) = E(x, η(√-d) y) + √-d E(x, y)` on `H₁(A, ℚ)`, in `ℚ^×/Nm(K^×)` (`DiscIs`).
* **Algebraic classes** (`CycleClasses`): an arbitrary assignment of a subspace
  `Z.alg g J ⊆ H*(A, ℚ)` to each abelian variety; for actual cycles it is the span of the classes of
  algebraic cycles. The properties of algebraic classes that the paper's proofs use are hypotheses
  (below).
* **The family `X × X̂`** (§§1.2–1.4, 2.4): for a principally polarized abelian threefold `X`
  (`Θ = e₁ ∧ e₂ + e₃ ∧ e₄ + e₅ ∧ e₆`, `ThetaStd`) and `d > 0`, `X × X̂` is a polarized abelian
  sixfold of Weil type with `H¹(X × X̂, ℚ) = H¹(X̂) ⊕ H¹(X)` (coordinates `coordV`), `η(√-d) = f`,
  `f(y, w) = (-θ⁻¹w, d θ y)` (`fX`), polarization `h = d Θ + Θ̂` (`hX`), and complex structure
  `(y, w) ↦ (-y ∘ J, J w)` (`JX`). The Weil-type period domain of `(η, h)` is `WeilDomain`.
* **The class `κ₃(E)`** (Theorem 1.4.1): `ch(F₁) = ch(F₂) = 1 + Θ - (d/2)Θ² - d[pt]` (`chF1`,
  Lemma 8.2.1) for the secant sheaves on the Jacobian of a genus-`3` curve; Orlov's equivalence
  `Φ : Dᵇ(X × X) → Dᵇ(X × X̂)` acts on cohomology by `φ = (id ⊗ ψ_{𝒫⁻¹[3]}) ∘ μ^*` (`phiOrlov`,
  (6.1.3); `c₁(𝒫) = Σ eᵢ ∪ fᵢ`); `ch(E) = τ φ(ch F₂ ⊗ ch F₁)` (`chE`) for `Φ(F₂ ⊠ F₁)^∨ = E[-2]`;
  `κ(E) = exp(-c₁(E)/rk E) ch(E)` and `κ₃(E)` its part in `H⁶` (`kappaX 3 d`).

## What is stated

* **Theorem 1.4.1(3)** (`theorem1_4_1_3`): every graded summand of `κ(E)` is a Hodge class on every
  deformation of `(X × X̂, η, h)` as a polarized abelian sixfold of Weil type (the connected
  component of the period domain).
* **Theorem 1.4.1(4)** (`theorem1_4_1_4`): the `η(K)`-translates of `κ₃(E)`, together with `h³`,
  span the `3`-dimensional subspace `ℚ h³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`.
* **Theorem 1.5.1** (`theorem1_5_1`): for every positive integer `d`, the Hodge–Weil classes of
  every polarized abelian sixfold of Weil type for `ℚ(√-d)` with discriminant `-1` are algebraic.
* **Corollary 1.6.1** (`corollary1_6_1`): the Hodge conjecture holds for abelian fourfolds: every
  Hodge class is algebraic.

Items (1), (2), (5) of Theorem 1.4.1 are not here: (2) and (5) are about sheaves, and (1) is
proved in the library (`WeilClasses.theorem1_4_1_1`). Compared theorems (`Kd.Nm`, `fX`, the
rank `8d` of `E`, the fact that `X × X̂` is a point of its own period domain, and its discriminant
`(-1)ⁿ`) check the definitions against the paper.

## The results are conditional

Theorems 1.4.1 (3), (4) are unconditional. Theorem 1.5.1 and Corollary 1.6.1 assume, as classes
in their signatures, the results that their proofs take from algebraic geometry:

* `PullbackClosed Z`: pullback of cycles along homomorphisms of abelian varieties;
* `SubalgebraClosed Z`: `[A]` and intersection products are algebraic;
* `LefschetzOneOne Z`: the Lefschetz (1,1) theorem;
* `VoisinLocus Z`: [Voisin, *The Hodge conjecture*, in *Open Problems in Mathematics* (2016),
  §4.2] the locus where a flat class is algebraic is a countable union of closed algebraic subsets
  (used in the form: closed analytic subsets of a component of the period domain);
* `SecantSheafDeformation Z`: the paper's own sheaf-theoretic Sections 7–9 (semiregular twisted
  sheaves, [Buchweitz–Flenner, Th. 5.1]), in cohomological form: near `X × X̂` in its period
  domain, `κ₃(E)` is algebraic wherever every `κ_k(E)` is of Hodge type (that they are of Hodge
  type there is the paper's Corollary 1.3.2, which is proved, not assumed);
* for Corollary 1.6.1 also `SchoenDegeneration Z` [Schoen, Prop. 10], `MoonenZarhinSimple`
  [Moonen–Zarhin 1995, Th. 2.11], `RamonMariProducts Z` [Ramón-Marí, Th. 4.11] and
  `MoonenZarhinLowDim` [Moonen–Zarhin 1999, Prop. 3.8, Th. 0.1(i)].

For actual algebraic cycles each class is a theorem of the cited source (or of the paper's
Sections 7–9); nothing here constructs a `CycleClasses` from cycles.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS
namespace WeilClasses

open TensorProduct

/-! ### The field `K = ℚ(√-d) ⊆ ℂ` -/

/-- The square root `√-d := i √d` of `-d` with argument `π/2` (the paper's choice, §2.4). -/
noncomputable def sqrtNeg (d : ℚ) : ℂ := Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)

/-- The imaginary quadratic field `K = ℚ(√-d)`, as the subfield of `ℂ` generated by `√-d`. -/
noncomputable def Kd (d : ℚ) : Subfield ℂ := Subfield.closure {sqrtNeg d}

/-- `√-d` as an element of `K`. -/
noncomputable def Kd.sqrtNeg (d : ℚ) : Kd d :=
  ⟨WeilClasses.sqrtNeg d, Subfield.subset_closure (Set.mem_singleton _)⟩

/-- The norm `Nm : K → ℚ`, `Nm(a + b√-d) = a² + d b²` (the field norm of `K/ℚ`). -/
noncomputable def Kd.Nm (d : ℚ) (k : Kd d) : ℚ := Algebra.norm ℚ k

/-! ### Rational cohomology in coordinates -/

section Model

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `H¹(X, F) = F^{2n}` for an abelian `n`-fold `X`, in the coordinates of a basis `e₁, …, e_{2n}`
of `H¹(X, ℤ)` with `∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1`. -/
abbrev H1 : Type _ := Fin (2 * n) → F

/-- `H*(X, F) = ⋀• H¹(X, F)`, with the cup product. -/
abbrev S : Type _ := ExteriorAlgebra F (H1 F n)

/-- `V_F = H¹(X̂, F) ⊕ H¹(X, F) = H¹(X × X̂, F)`, where `H¹(X̂, F) = H¹(X, F)*`. -/
abbrev V : Type _ := Module.Dual F (H1 F n) × H1 F n

/-- `H*(X̂, F) = ⋀• H¹(X̂, F)`. -/
abbrev SHat : Type _ := ExteriorAlgebra F (Module.Dual F (H1 F n))

/-- `H*(X × X̂, F) = ⋀• V_F`. -/
abbrev ExtV : Type _ := ExteriorAlgebra F (V F n)

/-- The basis vector `e_i` of `H¹(X, F)`. -/
noncomputable def e (i : Fin (2 * n)) : H1 F n := Pi.single i 1

/-- The coordinate functional `f_i ∈ H¹(X̂, F) = H¹(X, F)*`, dual to `e_i`. -/
noncomputable def f (i : Fin (2 * n)) : Module.Dual F (H1 F n) := LinearMap.proj i

/-- The basis `e_K = e_{i₁} ∧ ⋯ ∧ e_{i_k}` (`i₁ < ⋯ < i_k`) of `H*(X, F)`. -/
noncomputable def basisS : Module.Basis (Finset (Fin (2 * n))) F (S F n) :=
  (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra

/-- The basis `f₁, …, f_{2n}, e₁, …, e_{2n}` of `V_F`. -/
noncomputable def basisV : Module.Basis (Fin (2 * n + 2 * n)) F (V F n) :=
  ((Pi.basisFun F (Fin (2 * n))).dualBasis.prod (Pi.basisFun F (Fin (2 * n)))).reindex
    finSumFinEquiv

/-- The class `[pt_X] = e₁ ∧ ⋯ ∧ e_{2n} ∈ H^{2n}(X, F)` of a point. -/
noncomputable def pt : S F n := basisS F n Finset.univ

/-- Integration `∫_X : H*(X, F) → F`: the coefficient of `[pt_X] = e₁ ∧ ⋯ ∧ e_{2n}`. -/
noncomputable def integral : S F n →ₗ[F] F := (basisS F n).coord Finset.univ

/-- `D_θ`: contraction with `θ ∈ H¹(X, F)*` on `H*(X, F)`. -/
noncomputable def D : Module.Dual F (H1 F n) →ₗ[F] Module.End F (S F n) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n)))

/-- The principal polarization `Θ = e₁ ∧ e₂ + e₃ ∧ e₄ + ⋯ + e_{2n-1} ∧ e_{2n}` in symplectic
coordinates. (The index bounds are proved by terms: a tactic proof here would create a private
auxiliary lemma named after the module, so the copies of this block in `Challenge.lean` and here
would differ and Comparator would reject them.) -/
noncomputable def ThetaStd : S F n :=
  ∑ i : Fin n, ExteriorAlgebra.ι F (e F n ⟨2 * i, Nat.mul_lt_mul_of_pos_left i.isLt Nat.two_pos⟩) *
    ExteriorAlgebra.ι F (e F n ⟨2 * i + 1,
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.mul_le_mul_left 2 i.isLt)⟩)

end Model

section BaseChange

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

/-- Change of coefficients `H¹(X, F) → H¹(X, F')`. -/
noncomputable def bcH1 : H1 F n →ₗ[F] H1 F' n := (Algebra.linearMap F F').compLeft _

/-- Change of coefficients `H*(X, F) → H*(X, F')`, an `F`-algebra homomorphism. -/
noncomputable def bcS : S F n →ₐ[F] S F' n :=
  ExteriorAlgebra.lift F
    ⟨((ExteriorAlgebra.ι F' : H1 F' n →ₗ[F'] S F' n).restrictScalars F) ∘ₗ bcH1 F F' n,
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

end BaseChange

/-- The extension of scalars `F → F'` of a linear map `F^{2g} → F^{2g'}` (in the standard bases). -/
noncomputable def bcMap (F F' : Type*) [Field F] [Field F'] [Algebra F F'] {g g' : ℕ}
    (φ : H1 F g →ₗ[F] H1 F g') : H1 F' g →ₗ[F'] H1 F' g' :=
  Matrix.toLin' ((LinearMap.toMatrix' φ).map (algebraMap F F'))

/-! ### Hodge classes -/

section Hodge

variable (n : ℕ)

/-- The `ℂ`-linear extension to `H¹(X, ℂ)` of an `ℝ`-linear endomorphism of `H¹(X, ℝ)`. -/
noncomputable def complexifyH1 (A : Module.End ℝ (H1 ℝ n)) : Module.End ℂ (H1 ℂ n) :=
  Matrix.toLin (Pi.basisFun ℂ (Fin (2 * n))) (Pi.basisFun ℂ (Fin (2 * n)))
    ((LinearMap.toMatrix (Pi.basisFun ℝ (Fin (2 * n))) (Pi.basisFun ℝ (Fin (2 * n))) A).map
      (algebraMap ℝ ℂ))

/-- A complex structure: an endomorphism with `I² = -1`. -/
def IsComplexStructure {M : Type*} [AddCommGroup M] [Module ℝ M] (I : Module.End ℝ M) : Prop :=
  I * I = -1

/-- `H^{1,0}(X)`: the eigenspace of `J` in `H¹(X, ℂ)` with eigenvalue `i`. -/
noncomputable def H10 (J : Module.End ℝ (H1 ℝ n)) : Submodule ℂ (H1 ℂ n) :=
  Module.End.eigenspace (complexifyH1 n J) Complex.I

/-- `H^{0,1}(X)`: the eigenspace of `J` in `H¹(X, ℂ)` with eigenvalue `-i`. -/
noncomputable def H01 (J : Module.End ℝ (H1 ℝ n)) : Submodule ℂ (H1 ℂ n) :=
  Module.End.eigenspace (complexifyH1 n J) (-Complex.I)

/-- The piece `⋀^p A ∧ ⋀^q B ⊆ ⋀^{p+q} M` spanned by the products of `p` vectors of `A` and `q`
vectors of `B`; for `A = H^{1,0}` and `B = H^{0,1}` this is `H^{p,q}`. -/
noncomputable def pqPiece {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (p q : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  Submodule.span R
    {x | ∃ (a : Fin p → M) (b : Fin q → M), (∀ i, a i ∈ A) ∧ (∀ j, b j ∈ B) ∧
      x = ExteriorAlgebra.ιMulti R p a * ExteriorAlgebra.ιMulti R q b}

/-- The subspace `⋀^k W ⊆ ⋀^k M` spanned by the products of `k` vectors of `W`. -/
noncomputable def topWedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (W : Submodule R M) (k : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  Submodule.span R {x | ∃ v : Fin k → M, (∀ i, v i ∈ W) ∧ x = ExteriorAlgebra.ιMulti R k v}

/-- The Hodge classes `H^{p,p}(X, ℚ)` of degree `2p` for the complex structure `J` of
`H¹(X, ℝ)`: the rational classes in `⋀^{2p} H¹(X, ℚ)` of type `(p, p)`. -/
noncomputable def hodgeClassesX (J : Module.End ℝ (H1 ℝ n)) (p : ℕ) : Submodule ℚ (S ℚ n) :=
  ⋀[ℚ]^(2 * p) (H1 ℚ n) ⊓
    ((pqPiece (H10 n J) (H01 n J) p p).restrictScalars ℚ).comap (bcS ℚ ℂ n).toLinearMap

end Hodge

/-- `⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-`0` coefficient), for `ξ ∈ H*(X, F)` and
`a, b ∈ H₁(X, F) = H¹(X, F)*`; on `⋀² H¹` it is `⟪x ∧ y, a ∧ b⟫ = a(x) b(y) - a(y) b(x)`. -/
noncomputable def eval2 (F : Type*) [Field F] [CharZero F] (n : ℕ) (ξ : S F n)
    (a b : Module.Dual F (H1 F n)) : F :=
  (basisS F n).coord ∅ (D F n b (D F n a ξ))

/-- `Θ ∈ H²(X, ℚ)` is ample for the complex structure `J` of `H¹(X, ℝ)`: of type `(1,1)` and
`⟪Θ, a ∧ (a ∘ J)⟫ > 0` for every nonzero `a ∈ H₁(X, ℝ)` (Kähler positivity). -/
def IsAmple (n : ℕ) (J : Module.End ℝ (H1 ℝ n)) (Θ : S ℚ n) : Prop :=
  Θ ∈ hodgeClassesX n J 1 ∧
    ∀ a : Module.Dual ℝ (H1 ℝ n), a ≠ 0 → 0 < eval2 ℝ n (bcS ℚ ℝ n Θ) a (a ∘ₗ J)

/-! ### Abelian varieties up to isogeny -/

/-- A rational linear map `φ : H¹(A, ℚ) → H¹(B, ℚ)` is a morphism of Hodge structures. -/
def IsHodgeMap {g g' : ℕ} (J : Module.End ℝ (H1 ℝ g)) (J' : Module.End ℝ (H1 ℝ g'))
    (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g') : Prop :=
  bcMap ℚ ℝ φ ∘ₗ J = J' ∘ₗ bcMap ℚ ℝ φ

/-- **An abelian `g`-fold up to isogeny**: `H¹(A, ℚ) = ℚ^{2g}` with a complex structure `J` of
`H¹(A, ℝ)` (its `i`-eigenspace is `H^{1,0}(A)`) that admits an ample class. -/
structure AbVar (g : ℕ) where
  /-- The complex structure of `H¹(A, ℝ)`. -/
  J : Module.End ℝ (H1 ℝ g)
  isComplex : IsComplexStructure J
  polarizable : ∃ Θ : S ℚ g, IsAmple g J Θ

namespace AbVar

variable {g : ℕ} (A : AbVar g)

/-- The Hodge classes `H^{p,p}(A, ℚ)` of degree `2p`. -/
noncomputable def hodge (p : ℕ) : Submodule ℚ (S ℚ g) := hodgeClassesX g A.J p

/-- A sub-Hodge structure of `H¹(A, ℚ)` (an abelian subvariety up to isogeny): a rational subspace
`U` whose real span is stable under `J`. -/
def IsHodgeSub (U : Submodule ℚ (H1 ℚ g)) : Prop :=
  ∀ x ∈ Submodule.span ℝ (bcH1 ℚ ℝ g '' U), A.J x ∈ Submodule.span ℝ (bcH1 ℚ ℝ g '' U)

/-- `A` is simple: `g > 0` and `H¹(A, ℚ)` has no sub-Hodge structure other than `0` and itself. -/
def IsSimple : Prop := 0 < g ∧ ∀ U : Submodule ℚ (H1 ℚ g), A.IsHodgeSub U → U = ⊥ ∨ U = ⊤

end AbVar

/-! ### Abelian varieties of Weil type -/

/-- **The Hodge–Weil classes** `ĤW ⊆ H^{2m}(A, ℚ)` of an action `η : K → End_ℚ(H¹(A, ℚ))` on a
`2m`-fold: the rational classes of degree `2m` whose image in `H^{2m}(A, K)` lies in
`⋀^{2m} W ⊕ ⋀^{2m} W̄`, where `W`, `W̄` are the eigenspaces of `η(√-d)` with eigenvalues `±√-d`. -/
noncomputable def HWof {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) :
    Submodule ℚ (S ℚ (2 * m)) :=
  ⋀[ℚ]^(2 * m) (H1 ℚ (2 * m)) ⊓
    ((topWedge (Module.End.eigenspace (bcMap ℚ (Kd d) (η (Kd.sqrtNeg d))) (Kd.sqrtNeg d)) (2 * m) ⊔
      topWedge (Module.End.eigenspace (bcMap ℚ (Kd d) (η (Kd.sqrtNeg d))) (-Kd.sqrtNeg d))
        (2 * m)).restrictScalars ℚ).comap (bcS ℚ (Kd d) (2 * m)).toLinearMap

/-- **An abelian `2m`-fold of Weil type** for `K = ℚ(√-d)`: an embedding `η : K → End_ℚ(A)`
(acting on `H¹(A, ℚ)`) such that the eigenspaces of `η(√-d)` in `H¹(A, ℂ)` with eigenvalues `√-d`
and `-√-d` each meet `H^{1,0}(A)` in an `m`-dimensional subspace. -/
structure WeilType {m : ℕ} (A : AbVar (2 * m)) (d : ℚ) where
  /-- The action of `K` on `H¹(A, ℚ)` by rational endomorphisms of `A`. -/
  η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))
  isHodge : ∀ k, IsHodgeMap A.J A.J (η k)
  weil₁ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (sqrtNeg d) ⊓
    H10 (2 * m) A.J) = m
  weil₂ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (-sqrtNeg d) ⊓
    H10 (2 * m) A.J) = m

/-- The Hodge–Weil classes of an abelian variety of Weil type. -/
noncomputable def WeilType.HW {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : WeilType A d) :
    Submodule ℚ (S ℚ (2 * m)) :=
  HWof X.η

/-- **A polarized abelian `2m`-fold of Weil type** `(A, η, h)`: an ample class `h` such that `η(k)`
maps `h` to `Nm(k) h` for every `k ∈ K`. -/
structure PolarizedWeilType {m : ℕ} (A : AbVar (2 * m)) (d : ℚ) extends WeilType A d where
  /-- The polarization. -/
  h : S ℚ (2 * m)
  ample : IsAmple (2 * m) A.J h
  norm : ∀ k, ExteriorAlgebra.map (η k) h = Kd.Nm d k • h

namespace PolarizedWeilType

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : PolarizedWeilType A d)

/-- The Riemann form `E(x, y) = ⟪h, x ∧ y⟫` on `H₁(A, ℚ) = H¹(A, ℚ)*`. -/
noncomputable def E (x y : Module.Dual ℚ (H1 ℚ (2 * m))) : ℚ := eval2 ℚ (2 * m) X.h x y

/-- The action of `η(√-d)` on `H₁(A, ℚ)` (the transpose of its action on `H¹`). -/
noncomputable def fT : Module.Dual ℚ (H1 ℚ (2 * m)) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ (2 * m)) :=
  (X.η (Kd.sqrtNeg d)).dualMap

/-- Van Geemen's `K`-valued Hermitian form `H(x, y) = E(x, η(√-d) y) + √-d E(x, y)` on
`H₁(A, ℚ)`, as a complex number. -/
noncomputable def herm (x y : Module.Dual ℚ (H1 ℚ (2 * m))) : ℂ :=
  (X.E x (X.fT y) : ℂ) + sqrtNeg d * (X.E x y : ℂ)

/-- **The discriminant** is `c`: in some `K`-basis `b₁, …, b_{2m}` of `H₁(A, ℚ)`,
`det H(bᵢ, bⱼ) ∈ c · Nm(K^×)`. -/
def DiscIs (c : ℚ) : Prop :=
  ∃ b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)),
    LinearIndependent ℚ (Sum.elim b (fun i => X.fT (b i))) ∧
    ∃ k : Kd d, k ≠ 0 ∧ (Matrix.of fun i j => X.herm (b i) (b j)).det = (c : ℂ) * (Kd.Nm d k : ℂ)

end PolarizedWeilType

/-! ### Algebraic classes and the results assumed about them -/

/-- **A system of algebraic classes**: for every `g` and every complex structure `J` of
`H¹(A, ℝ) = ℝ^{2g}`, a `ℚ`-subspace `alg g J ⊆ H*(A, ℚ)`. For actual cycles, the span of the
classes of algebraic cycles on the abelian variety `(ℚ^{2g}, J)`. -/
structure CycleClasses where
  /-- The algebraic classes of the abelian variety with complex structure `J`. -/
  alg : (g : ℕ) → Module.End ℝ (H1 ℝ g) → Submodule ℚ (S ℚ g)

/-- **Pullback of algebraic cycles** along homomorphisms of abelian varieties (a rational map of
Hodge structures between the `H¹` is a multiple of the pullback by a homomorphism). -/
class PullbackClosed (Z : CycleClasses) : Prop where
  map_mem : ∀ {g g' : ℕ} (A : AbVar g) (B : AbVar g') (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g'),
    IsHodgeMap A.J B.J φ → ∀ α ∈ Z.alg g A.J, ExteriorAlgebra.map φ α ∈ Z.alg g' B.J

/-- **Intersection product**: `1 = [A]` is algebraic and products of algebraic classes are
algebraic. -/
class SubalgebraClosed (Z : CycleClasses) : Prop where
  one_mem : ∀ {g : ℕ} (A : AbVar g), (1 : S ℚ g) ∈ Z.alg g A.J
  mul_mem : ∀ {g : ℕ} (A : AbVar g) (α β : S ℚ g),
    α ∈ Z.alg g A.J → β ∈ Z.alg g A.J → α * β ∈ Z.alg g A.J

/-- **The Lefschetz (1,1) theorem**: rational classes of type `(1,1)` are algebraic. -/
class LefschetzOneOne (Z : CycleClasses) : Prop where
  le : ∀ {g : ℕ} (A : AbVar g), A.hodge 1 ≤ Z.alg g A.J

/-- **The Weil-type period domain** of `(η, h)` on `H¹ = ℚ^{4m}`: the complex structures `J` of
`H¹(A, ℝ)` for which `(J, η, h)` is a polarized abelian `2m`-fold of Weil type. -/
def WeilDomain {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) (h : S ℚ (2 * m)) :
    Set (Module.End ℝ (H1 ℝ (2 * m))) :=
  {J | IsComplexStructure J ∧ (∀ k, IsHodgeMap J J (η k)) ∧
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (sqrtNeg d) ⊓
      H10 (2 * m) J) = m ∧
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η (Kd.sqrtNeg d))) (-sqrtNeg d) ⊓
      H10 (2 * m) J) = m ∧
    IsAmple (2 * m) J h ∧ ∀ k, ExteriorAlgebra.map (η k) h = Kd.Nm d k • h}

/-- The Weil-type period domain as a set of real matrices (standard basis), with the usual
topology. -/
noncomputable def WeilDomainMat {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m)))
    (h : S ℚ (2 * m)) : Set (Matrix (Fin (2 * (2 * m))) (Fin (2 * (2 * m))) ℝ) :=
  LinearMap.toMatrix' '' WeilDomain η h

/-- **[Voisin, *The Hodge conjecture*, §4.2]**: the locus in moduli where a fixed rational class is
algebraic is a countable union of closed algebraic subsets (TeX line 6847). Assumed here in the form
used in the model: over a connected component `C` of a Weil-type period domain, the locus is a
countable union of closed analytic subsets, so if it contains a nonempty open subset of `C`, it is
all of `C`. -/
class VoisinLocus (Z : CycleClasses) : Prop where
  spread : ∀ {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) (h : S ℚ (2 * m))
    (α : S ℚ (2 * m)) (J₀ : Module.End ℝ (H1 ℝ (2 * m)))
    (U : Set (Matrix (Fin (2 * (2 * m))) (Fin (2 * (2 * m))) ℝ)),
    U ⊆ connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀) → U.Nonempty →
    IsOpen ((↑) ⁻¹' U : Set (connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀))) →
    (∀ J, LinearMap.toMatrix' J ∈ U → α ∈ Z.alg (2 * m) J) →
    ∀ J, LinearMap.toMatrix' J ∈ connectedComponentIn (WeilDomainMat η h) (LinearMap.toMatrix' J₀) →
      α ∈ Z.alg (2 * m) J

/-- The span of the products of two rational classes of type `(1,1)`. -/
noncomputable def AbVar.divisorProducts {g : ℕ} (A : AbVar g) : Submodule ℚ (S ℚ g) :=
  Submodule.span ℚ {x | ∃ α ∈ A.hodge 1, ∃ β ∈ A.hodge 1, x = α * β}

/-- The span of the Hodge–Weil classes of all structures of Weil type on `A` (all `K = ℚ(√-d)`,
`d` a positive integer). -/
noncomputable def AbVar.allHW {m : ℕ} (A : AbVar (2 * m)) : Submodule ℚ (S ℚ (2 * m)) :=
  ⨆ (d : ℕ) (_ : 0 < d) (X : WeilType A d), X.HW

/-- **[Schoen, Prop. 10]**: if the Hodge–Weil classes of all polarized abelian sixfolds of Weil type
for `K` with discriminant `-1` are algebraic, so are those of all abelian fourfolds of Weil type for
`K`. -/
class SchoenDegeneration (Z : CycleClasses) : Prop where
  imp : ∀ d : ℕ, 0 < d →
    (∀ (A : AbVar (2 * 3)) (X : PolarizedWeilType A d), X.DiscIs (-1) → X.HW ≤ Z.alg (2 * 3) A.J) →
    ∀ (A : AbVar (2 * 2)) (X : WeilType A d), X.HW ≤ Z.alg (2 * 2) A.J

/-- **[Moonen–Zarhin 1995, Th. 2.11]**: for a simple abelian fourfold, `H^{2,2}(A, ℚ)` is spanned by
products of divisor classes and Hodge–Weil classes. -/
class MoonenZarhinSimple : Prop where
  span : ∀ A : AbVar (2 * 2), A.IsSimple → A.hodge 2 ≤ A.divisorProducts ⊔ A.allHW

/-- `H¹(A, ℚ) = U₁ ⊕ U₂` with sub-Hodge structures of dimensions `2g₁`, `2g₂`: `A` is isogenous to
a product of abelian varieties of dimensions `g₁`, `g₂`. -/
def AbVar.SplitsAs {g : ℕ} (A : AbVar g) (U₁ U₂ : Submodule ℚ (H1 ℚ g)) (g₁ g₂ : ℕ) : Prop :=
  A.IsHodgeSub U₁ ∧ A.IsHodgeSub U₂ ∧ IsCompl U₁ U₂ ∧ Module.finrank ℚ U₁ = 2 * g₁ ∧
    Module.finrank ℚ U₂ = 2 * g₂

/-- The factor with `H¹ = U` is simple. -/
def AbVar.SimpleFactor {g : ℕ} (A : AbVar g) (U : Submodule ℚ (H1 ℚ g)) : Prop :=
  U ≠ ⊥ ∧ ∀ U' ≤ U, A.IsHodgeSub U' → U' = ⊥ ∨ U' = U

/-- **[Ramón-Marí, Th. 4.11]**: the Hodge conjecture holds for abelian fourfolds isogenous to a
product of two abelian surfaces. -/
class RamonMariProducts (Z : CycleClasses) : Prop where
  hc : ∀ (A : AbVar (2 * 2)) (U₁ U₂ : Submodule ℚ (H1 ℚ (2 * 2))), A.SplitsAs U₁ U₂ 2 2 →
    ∀ p, A.hodge p ≤ Z.alg (2 * 2) A.J

/-- **[Moonen–Zarhin 1999, Prop. 3.8 and Th. 0.1(i)]**: if `A` is isogenous to `B × E` with `B` a
simple abelian threefold and `E` an elliptic curve, `H^{2,2}(A, ℚ)` is spanned by products of
divisor classes and Hodge–Weil classes. -/
class MoonenZarhinLowDim : Prop where
  span : ∀ (A : AbVar (2 * 2)) (U U' : Submodule ℚ (H1 ℚ (2 * 2))), A.SplitsAs U U' 3 1 →
    A.SimpleFactor U → A.hodge 2 ≤ A.divisorProducts ⊔ A.allHW

/-! ### The polarized abelian `2n`-fold of Weil type `X × X̂` -/

section XXhat

variable (n : ℕ)

/-- The coordinate isomorphism `V_F ≃ F^{4n}` (`f₁, …, f_{2n}, e₁, …, e_{2n}` to the standard
basis): `H¹(X × X̂, F)` in the coordinates of the model. -/
noncomputable def coordV (F : Type*) [Field F] [CharZero F] (n : ℕ) : V F n ≃ₗ[F] H1 F (2 * n) :=
  (basisV F n).equivFun.trans (LinearEquiv.funCongrLeft F F (finCongr (by ring)))

/-- An endomorphism of `V_F` as an endomorphism of `F^{4n}`. -/
noncomputable def transportEnd {F : Type*} [Field F] [CharZero F] (A : Module.End F (V F n)) :
    Module.End F (H1 F (2 * n)) :=
  (coordV F n).toLinearMap ∘ₗ A ∘ₗ (coordV F n).symm.toLinearMap

/-- `θ : H¹(X, ℚ)* → H¹(X, ℚ)`, contraction with `Θ`: `θ(f_{2i}) = e_{2i+1}`,
`θ(f_{2i+1}) = -e_{2i}` (indices from `0`). -/
noncomputable def thetaStd : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n :=
  ∑ i : Fin n,
    ((Module.Dual.eval ℚ (H1 ℚ n) (e ℚ n ⟨2 * i, by omega⟩)).smulRight
        (e ℚ n ⟨2 * i + 1, by omega⟩) -
      (Module.Dual.eval ℚ (H1 ℚ n) (e ℚ n ⟨2 * i + 1, by omega⟩)).smulRight
        (e ℚ n ⟨2 * i, by omega⟩))

/-- `θ⁻¹ : H¹(X, ℚ) → H¹(X, ℚ)*`: `θ⁻¹(e_{2i+1}) = f_{2i}`, `θ⁻¹(e_{2i}) = -f_{2i+1}`. -/
noncomputable def thetaStdInv : H1 ℚ n →ₗ[ℚ] Module.Dual ℚ (H1 ℚ n) :=
  ∑ i : Fin n,
    ((f ℚ n ⟨2 * i + 1, by omega⟩).smulRight (f ℚ n ⟨2 * i, by omega⟩) -
      (f ℚ n ⟨2 * i, by omega⟩).smulRight (f ℚ n ⟨2 * i + 1, by omega⟩))

/-- `f = η(√-d)` on `V_ℚ`: `f(y, w) = (-θ⁻¹(w), d θ(y))`. -/
noncomputable def fV (d : ℚ) : Module.End ℚ (V ℚ n) :=
  LinearMap.prod (-(thetaStdInv n) ∘ₗ LinearMap.snd ℚ _ _) ((d • thetaStd n) ∘ₗ LinearMap.fst ℚ _ _)

/-- `Θ = Σ e_{2i} ∧ e_{2i+1} ∈ H²(X, ℚ)`, as a class on `X × X̂`. -/
noncomputable def ThetaV : ExtV ℚ n :=
  ∑ i : Fin n, ExteriorAlgebra.ι ℚ ((0, e ℚ n ⟨2 * i, by omega⟩) : V ℚ n) *
    ExteriorAlgebra.ι ℚ ((0, e ℚ n ⟨2 * i + 1, by omega⟩) : V ℚ n)

/-- `Θ̂ = Σ f_{2i} ∧ f_{2i+1} ∈ H²(X̂, ℚ)`, as a class on `X × X̂`. -/
noncomputable def ThetaHatV : ExtV ℚ n :=
  ∑ i : Fin n, ExteriorAlgebra.ι ℚ ((f ℚ n ⟨2 * i, by omega⟩, 0) : V ℚ n) *
    ExteriorAlgebra.ι ℚ ((f ℚ n ⟨2 * i + 1, by omega⟩, 0) : V ℚ n)

/-- The polarization `h = d Θ + Θ̂` of `X × X̂`. -/
noncomputable def hV (d : ℚ) : ExtV ℚ n := d • ThetaV n + ThetaHatV n

/-- The complex structure of `X × X̂` given by the complex structure `J` of `H¹(X, ℝ)`:
`(y, w) ↦ (-y ∘ J, J w)` (`H^{1,0}` the `i`-eigenspace). -/
noncomputable def stdStructure (J : Module.End ℝ (H1 ℝ n)) : Module.End ℝ (V ℝ n) :=
  (-(LinearMap.dualMap J) : Module.End ℝ (Module.Dual ℝ (H1 ℝ n))).prodMap J

/-- `f = η(√-d)` on the model `H¹(X × X̂, ℚ) = ℚ^{4n}`. -/
noncomputable def fX (d : ℚ) : Module.End ℚ (H1 ℚ (2 * n)) := transportEnd n (fV n d)

/-- The polarization `h` in the model `H*(X × X̂, ℚ) = ⋀• ℚ^{4n}`. -/
noncomputable def hX (d : ℚ) : S ℚ (2 * n) := ExteriorAlgebra.map (coordV ℚ n).toLinearMap (hV n d)

/-- The complex structure of `X × X̂` on the model `H¹(X × X̂, ℝ) = ℝ^{4n}`. -/
noncomputable def JX (J : Module.End ℝ (H1 ℝ n)) : Module.End ℝ (H1 ℝ (2 * n)) :=
  transportEnd n (stdStructure n J)

end XXhat

/-! ### Orlov's equivalence in cohomology -/

section Correspondence

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [AddCommGroup B] [Module F B]

/-- Poincaré duality `PD(u) = ∫(• ∪ u)` for an integration functional `∫ : A → F`. -/
noncomputable def pdOf (intA : A →ₗ[F] F) : A →ₗ[F] Module.Dual F A :=
  (LinearMap.mul F A).flip.compr₂ intA

/-- The correspondence `γ_*(s) = π_{Y*}(π_X^*s ∪ γ)` of `γ ∈ H*(X) ⊗ H*(Y)`: for `γ = Σ uᵢ ⊗ vᵢ`,
`γ_*(s) = Σ (∫_X s ∪ uᵢ) vᵢ`. -/
noncomputable def corr (intA : A →ₗ[F] F) : A ⊗[F] B →ₗ[F] A →ₗ[F] B :=
  TensorProduct.lift ((LinearMap.smulRightₗ (R := F) (M := B) (M₂ := A)) ∘ₗ pdOf intA)

end Correspondence

section Orlov

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `π_X^* : H*(X) → H*(X × X̂) = ⋀• V`. -/
noncomputable def pullX : S F n →ₐ[F] ExtV F n :=
  ExteriorAlgebra.map (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n))

/-- `π_X̂^* : H*(X̂) → H*(X × X̂) = ⋀• V`. -/
noncomputable def pullXHat : SHat F n →ₐ[F] ExtV F n :=
  ExteriorAlgebra.map (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n))

/-- Künneth for `X × X̂`: `H*(X) ⊗ H*(X̂) ≅ ⋀• V`, `u ⊗ v ↦ π_X^*u ∪ π_X̂^*v`. -/
noncomputable def kunnethXHat : S F n ⊗[F] SHat F n ≃ₗ[F] ExtV F n :=
  ((GradedTensorProduct.of F (fun i : ℕ => ⋀[F]^i (H1 F n))
      (fun i : ℕ => ⋀[F]^i (Module.Dual F (H1 F n)))).trans
    (GradedTensorProduct.comm (fun i : ℕ => ⋀[F]^i (H1 F n))
      (fun i : ℕ => ⋀[F]^i (Module.Dual F (H1 F n)))).toLinearEquiv).trans
    (ExteriorAlgebra.prodEquivTensor F (Module.Dual F (H1 F n)) (H1 F n)).symm.toLinearEquiv

/-- `H*(X × X, F) = ⋀•(H¹(X) ⊕ H¹(X))`. -/
abbrev SXX : Type _ := ExteriorAlgebra F (H1 F n × H1 F n)

/-- Künneth for `X × X`: `H*(X) ⊗ H*(X) ≅ H*(X × X)`, `u ⊗ v ↦ π₁^*u ∪ π₂^*v`. -/
noncomputable def kunnethXX : S F n ⊗[F] S F n ≃ₗ[F] SXX F n :=
  (GradedTensorProduct.of F (fun i : ℕ => ⋀[F]^i (H1 F n)) (fun i : ℕ => ⋀[F]^i (H1 F n))).trans
    (ExteriorAlgebra.prodEquivTensor F (H1 F n) (H1 F n)).symm.toLinearEquiv

/-- `μ^*` on `H¹(X × X) = H¹(X) ⊕ H¹(X)` for `μ(x, y) = (x + y, y)`: `(a, b) ↦ (a, a + b)`. -/
noncomputable def mu1 : (H1 F n × H1 F n) →ₗ[F] (H1 F n × H1 F n) :=
  (LinearMap.fst F (H1 F n) (H1 F n)).prod
    (LinearMap.fst F (H1 F n) (H1 F n) + LinearMap.snd F (H1 F n) (H1 F n))

/-- `μ^*` on `H*(X × X) = H*(X) ⊗ H*(X)`. -/
noncomputable def muStar : S F n ⊗[F] S F n →ₗ[F] S F n ⊗[F] S F n :=
  (kunnethXX F n).symm.toLinearMap ∘ₗ (ExteriorAlgebra.map (mu1 F n)).toLinearMap ∘ₗ
    (kunnethXX F n).toLinearMap

/-- `c₁(𝒫) = Σᵢ π_X^*eᵢ ∪ π_X̂^*fᵢ ∈ H²(X × X̂)`, the first Chern class of the Poincaré bundle. Its
sign depends on the identification `H¹(X̂) = H¹(X)*`; this is the sign for which the paper's
Lemma 6.3.1 and Proposition 6.1.2 hold. -/
noncomputable def c1P : ExtV F n :=
  ∑ i : Fin (2 * n), pullX F n (ExteriorAlgebra.ι F (e F n i)) *
    pullXHat F n (ExteriorAlgebra.ι F (f F n i))

/-- `ch(𝒫⁻¹[n]) = (-1)ⁿ exp(-c₁(𝒫))`. -/
noncomputable def chPinvShift : ExtV F n := (-1 : F) ^ n • IsNilpotent.exp (-c1P F n)

/-- `ψ_{𝒫⁻¹[n]} = ch(𝒫⁻¹[n])_* : H*(X) → H*(X̂)`, the cohomological action of the inverse
`Ψ_{𝒫⁻¹[n]}` of the Fourier–Mukai equivalence `Φ_𝒫`. -/
noncomputable def psiPinvShift : S F n →ₗ[F] SHat F n :=
  corr (integral F n) ((kunnethXHat F n).symm (chPinvShift F n))

/-- **(6.1.3)** The cohomological action `φ = (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^* : H*(X × X) → H*(X × X̂)` of
Orlov's equivalence `Φ = (id × Ψ_{𝒫⁻¹[n]}) ∘ μ^*`. -/
noncomputable def phiOrlov : S F n ⊗[F] S F n →ₗ[F] ExtV F n :=
  (kunnethXHat F n).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (psiPinvShift F n) ∘ₗ
    muStar F n

/-- The projection `⋀• V → ⋀^k V ⊆ ⋀• V` to the degree-`k` component. -/
noncomputable def projDeg (k : ℕ) : ExtV F n →ₗ[F] ExtV F n :=
  GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (V F n)) k

end Orlov

/-! ### The secant sheaves of Theorem 1.4.1 and the class `κ₃(E)` -/

section Kappa

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `τ` on `H*(X × X̂, F) = ⋀• V`: reversal of products, `(-1)^i` on `H^{2i}`. On Chern characters
it is `ch(G^∨) = τ(ch G)` (derived dual). -/
noncomputable def tauExt : ExtV F n →ₗ[F] ExtV F n :=
  CliffordAlgebra.reverse (Q := (0 : QuadraticForm F (V F n)))

/-- The rank `r = c₀ ∈ H⁰(X × X̂, F) = F` of a class: its degree-`0` coefficient. -/
noncomputable def rankExt : ExtV F n →ₐ[F] F := ExteriorAlgebra.algebraMapInv

/-- `κ(c) = exp(-c₁/r) c` (§1.3) for `c ∈ H*(X × X̂, F)` with rank `r = c₀` (`rankExt`) and
`c₁ ∈ H²` its degree-`2` component. -/
noncomputable def kappa (c : ExtV F n) : ExtV F n :=
  IsNilpotent.exp (-(rankExt F n c)⁻¹ • projDeg F n 2 c) * c

/-- The graded summand `κ_k(c) ∈ H^{2k}` of `κ(c)`. -/
noncomputable def kappaDeg (k : ℕ) (c : ExtV F n) : ExtV F n := projDeg F n (2 * k) (kappa F n c)

end Kappa

/-- **Lemma 8.2.1**: the Chern character `ch(F₁) = ch(F₂) = 1 + Θ - (d/2) Θ² - d [pt]` of the
secant sheaves `F₁ = I_{∪ Cᵢ}(Θ)` and `F₂ = I_{∪ Σᵢ}(Θ)` on the Jacobian `X` of a genus-`3` curve
(`d + 1` disjoint translates `Cᵢ` of `AJ(C)`, `Σᵢ` of `-AJ(C)`). -/
noncomputable def chF1 (d : ℚ) : S ℚ 3 :=
  1 + ThetaStd ℚ 3 - (d / 2) • ThetaStd ℚ 3 ^ 2 - d • pt ℚ 3

/-- `ch(E) = τ φ(ch F₂ ⊗ ch F₁)` for the sheaf `E` of Theorem 1.4.1(2), `Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]`
(Künneth, `ch(Φ(G)) = φ(ch G)` and `ch(G^∨) = τ ch(G)`). -/
noncomputable def chE (d : ℚ) : ExtV ℚ 3 := tauExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ chF1 d))

/-- `κ_k(E) ∈ H^{2k}(X × X̂, ℚ)` in the model `H*(X × X̂, ℚ) = ⋀• ℚ^{12}`. -/
noncomputable def kappaX (k : ℕ) (d : ℚ) : S ℚ (2 * 3) :=
  ExteriorAlgebra.map (coordV ℚ 3).toLinearMap (kappaDeg ℚ 3 k (chE d))

/-- **The paper's Sections 7–9, in cohomological form: the secant sheaf deforms along the Hodge
locus of `κ`.** For every integer `d ≥ 3` there is a principally polarized abelian threefold `X` (a
complex structure `J` of `H¹(X, ℝ) = ℝ⁶` for which `Θ = ThetaStd` is ample; the paper takes the
Jacobian of a generic non-hyperelliptic curve of genus `3`) such that, for the action `η` of `K` on
`H¹(X × X̂, ℚ)` with `η(√-d) = f`: on every polarized abelian sixfold of Weil type near `X × X̂` in
the connected component of its Weil-type period domain at which every graded summand `κ_k(E)` is
of Hodge type, the class `κ₃(E) ∈ H⁶(X × X̂, ℚ)` is algebraic.

In the paper (the paragraph before Theorem 1.5.1 and §9.3) this combines Lemma 8.2.1 (`ch F_i`),
the Grothendieck–Riemann–Roch theorem for Orlov's kernel (`ch Φ(G) = φ(ch G)`), Theorem 1.4.1(2)
(`E` reflexive of rank `8d`), §9.3 (a twisted sheaf `B` on `Y = (X × X̂)/Ḡ` with
`q^*κ(B) = κ(E)`, semiregular by Lemma 9.3.11) and Conjecture 7.3.9 for families of abelian
varieties (proved in §7.4, from [Buchweitz–Flenner, Th. 5.1]): `(Y, B)`, hence `(X × X̂, q^*B)`,
deforms locally over the locus where `κ(B)` remains of Hodge type, and `κ` of the deformed sheaves
is algebraic. That `κ(E)` remains of Hodge type over the Weil-type deformations of
`(X × X̂, η, h)` is the paper's Corollary 1.3.2 (TeX 570); it is proved in the library
(`corollary1_3_2_hodge`), and is not part of this hypothesis. -/
class SecantSheafDeformation (Z : CycleClasses) : Prop where
  deform : ∀ d : ℕ, 3 ≤ d → ∃ J : Module.End ℝ (H1 ℝ 3), IsComplexStructure J ∧
    IsAmple 3 J (ThetaStd ℚ 3) ∧ ∀ η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3)),
      η (Kd.sqrtNeg d) = fX 3 d →
      ∀ᶠ M in nhdsWithin (LinearMap.toMatrix' (JX 3 J))
          (connectedComponentIn (WeilDomainMat η (hX 3 d)) (LinearMap.toMatrix' (JX 3 J))),
        (∀ k, kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k) →
          kappaX 3 d ∈ Z.alg (2 * 3) (Matrix.toLin' M)

end WeilClasses
-- END SHARED DEFINITIONS

namespace WeilClasses.Challenge

open WeilClasses

/-! ### Compared theorems: the definitions are the intended ones -/

/-- `Nm(a + b√-d) = a² + d b²`. -/
theorem Kd_Nm (d : ℚ) (hd : 0 < d) (a b : ℚ) :
    Kd.Nm d ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d) = a ^ 2 + d * b ^ 2 := by
  sorry

/-- `f² = -d` on `H¹(X × X̂, ℚ)`, so `√-d ↦ f` defines an action of `K = ℚ(√-d)`. -/
theorem fX_mul_self (n : ℕ) (d : ℚ) : fX n d * fX n d = -(d • 1) := by
  sorry

/-- `X × X̂` with `(η, h)` is a polarized abelian `2n`-fold of Weil type (§2.4, Proposition 2.4.4,
Corollary 3.2.3): its complex structure lies in its Weil-type period domain. -/
theorem JX_mem_weilDomain (n : ℕ) (d : ℚ) (hd : 0 < d)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hΘ : IsAmple n J (ThetaStd ℚ n))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n))) (hη : η (Kd.sqrtNeg d) = fX n d) :
    JX n J ∈ WeilDomain η (hX n d) := by
  sorry

/-- The discriminant of `X × X̂` is `(-1)ⁿ` (Lemma 3.1.3): every polarized abelian `2n`-fold of Weil
type with the action and the polarization of `X × X̂` has discriminant `(-1)ⁿ`. -/
theorem discIs_XXhat (n : ℕ) (d : ℚ) (hd : 0 < d) (A : AbVar (2 * n)) (X : PolarizedWeilType A d)
    (hη : X.η (Kd.sqrtNeg d) = fX n d) (hh : X.h = hX n d) : X.DiscIs ((-1) ^ n) := by
  sorry

/-- The sheaf `E` of Theorem 1.4.1(2) has rank `8d`. -/
theorem rank_chE (d : ℚ) : ExteriorAlgebra.algebraMapInv (chE d) = 8 * d := by
  sorry

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
    (k : ℕ) : kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k := by
  sorry

/-- **Theorem 1.4.1(4).** The `η(K)`-translates of `κ₃(E) ∈ H⁶(X × X̂, ℚ)`, together with `h³`,
span the `3`-dimensional subspace `ℚ h³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`. -/
theorem theorem1_4_1_4 (d : ℕ) (hd : 3 ≤ d) (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3)))
    (hη : η (Kd.sqrtNeg d) = fX 3 d) :
    Submodule.span ℚ
        (insert (hX 3 d ^ 3) (Set.range fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d))) =
      (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η ∧
    Module.finrank ℚ ↥((ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η) = 3 := by
  sorry

/-! ### Theorem 1.5.1 and Corollary 1.6.1 -/

/-- **Theorem 1.5.1.** Let `d` be a positive integer and `K = ℚ(√-d)`. The Hodge–Weil classes of
polarized abelian sixfolds of Weil type with complex multiplication by `K` and with discriminant
`-1` are algebraic. -/
theorem theorem1_5_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [SecantSheafDeformation Z]
    (d : ℕ) (hd : 0 < d) (A : AbVar (2 * 3)) (X : PolarizedWeilType A d) (hdisc : X.DiscIs (-1)) :
    X.HW ≤ Z.alg (2 * 3) A.J := by
  sorry

/-- **Corollary 1.6.1.** The Hodge conjecture holds for abelian fourfolds: every Hodge class is
algebraic. -/
theorem corollary1_6_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [SecantSheafDeformation Z]
    [SchoenDegeneration Z] [MoonenZarhinSimple] [RamonMariProducts Z] [MoonenZarhinLowDim]
    (A : AbVar (2 * 2)) (p : ℕ) : A.hodge p ≤ Z.alg (2 * 2) A.J := by
  sorry

end WeilClasses.Challenge
