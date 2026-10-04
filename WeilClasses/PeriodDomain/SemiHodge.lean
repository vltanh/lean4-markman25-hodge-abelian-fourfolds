module

public import WeilClasses.PeriodDomain.Defs
public import WeilClasses.Spinor.Integral

/-!
# Semi-Hodge classes; Hodge–Weil classes stay of Hodge type on `Ω_P` (paper §4, Lemma 4.0.3 and
Corollary 4.0.4)

§4 of the paper from line 1806 to 1851, under Assumption 2.4.1. For `I ∈ Ω_P`:

* `Ĩ`, the unique element of `Spin(V_ℝ)_P` with `ρ(Ĩ) = I` (Lemma 3.1.1);
* the circle `𝕊_I = {cos θ + sin θ I}` of `SO_+(V_ℝ)` (`WeilClasses.circleS`), the identity component
  of its inverse image in `Spin(V_ℝ)` (`WeilClasses.circleLift`), and the real Hodge structure of
  weight `0` on `S⁺_ℝ = H^{ev}(X, ℝ)` it defines: `S⁺_ℂ = ⊕_p S^{-p,p}_ℂ` (`WeilClasses.Spq`);
* semi-Hodge classes: rational classes in `S^{0,0}_ℂ` (`WeilClasses.IsSemiHodge`);
* Lemma 4.0.3 (the Hodge–Weil plane consists of Hodge classes and `P` of semi-Hodge classes, for
  every `I ∈ Ω_P`) and Corollary 4.0.4 (`Spin(V)_P`-invariant classes of `⋀• V_ℚ` stay of Hodge
  type on `Ω_P`; `Spin(V)_P` is the integral group `SpinZ n ⊓ Spin(V_ℚ)_P`, acting by `ρ` on
  `⋀• V_ℚ`).

## Conventions

`Spin(V_ℝ) ⊆ C(V_ℝ)` carries the Euclidean topology of `C(V_ℝ)`, transported from coordinates in the
basis `basisExt` of `⋀• V_ℝ` along Mathlib's linear isomorphism `C(V_ℝ) ≅ ⋀• V_ℝ`
(`CliffordAlgebra.equivExterior`) (`WeilClasses.spinTopology`, not an instance). `S^{-p,p}_ℂ` is the
subspace of `S⁺_ℂ` on which the element of the identity component over `cos θ + sin θ I` acts by
`e^{-2ipθ}` (`z^{-p} z̄^{p}`, `z = e^{iθ}`, the convention for which `I` acts on `V^{1,0}` by `z`);
for `I = I_{V_ℝ}` (the paper's convention, the negative of the standard one),
`H^{p,q}(X) ⊆ S^{(q-p)/2, (p-q)/2}` and `S^{0,0}_ℂ = ⊕_p H^{p,p}(X)`. Only
`S^{0,0}` (the invariants) enters the results.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section Circle

variable (n : ℕ)

/-- `I_θ = cos(θ) id + sin(θ) I`. -/
noncomputable def rotI (I : Module.End ℝ (V ℝ n)) (θ : ℝ) : Module.End ℝ (V ℝ n) :=
  Real.cos θ • (1 : Module.End ℝ (V ℝ n)) + Real.sin θ • I

/-- **`𝕊_I`** (§4): `{cos(θ) id_{V_ℝ} + sin(θ) I : θ ∈ ℝ}`. -/
def circleS (I : Module.End ℝ (V ℝ n)) : Set (Module.End ℝ (V ℝ n)) := Set.range (rotI n I)

/-- The Euclidean topology on `Spin(V_ℝ) ⊆ C(V_ℝ)`, induced by the coordinates of `C(V_ℝ) ≅ ⋀• V_ℝ`
in the basis `basisExt`. -/
@[instance_reducible] noncomputable def spinTopology : TopologicalSpace (Spin ℝ n) :=
  TopologicalSpace.induced
    (fun g : Spin ℝ n => ⇑((basisExt ℝ n).repr (CliffordAlgebra.equivExterior (Q ℝ n) (g : C ℝ n))))
    inferInstance

/-- The inverse image of `𝕊_I` in `Spin(V_ℝ)`. -/
def circlePreimage (I : Module.End ℝ (V ℝ n)) : Set (Spin ℝ n) :=
  {g | (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) ∈ circleS n I}

/-- The identity component of the inverse image of `𝕊_I` in `Spin(V_ℝ)` (§4). -/
noncomputable def circleLift (I : Module.End ℝ (V ℝ n)) : Set (Spin ℝ n) :=
  @connectedComponentIn _ (spinTopology n) (circlePreimage n I) 1

/-- **`S^{-p,p}_ℂ`** (§4): the classes `s ∈ S⁺_ℂ` such that the element `g` of the identity component
of the inverse image of `𝕊_I` with `ρ(g) = cos θ + sin θ I` acts on `s` by `e^{-2ipθ}`. -/
noncomputable def Spq (I : Module.End ℝ (V ℝ n)) (p : ℤ) : Submodule ℂ (S ℂ n) where
  carrier := {s | s ∈ Splus ℂ n ∧ ∀ g ∈ circleLift n I, ∀ θ : ℝ,
    (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = rotI n I θ →
      m ℂ n (bcC ℝ ℂ n (g : C ℝ n)) s = Complex.exp (-(2 * (p : ℂ) * θ) * Complex.I) • s}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-- **Semi-Hodge class** (§4): a rational class `s ∈ S_ℚ` lying in `S^{0,0}_ℂ`. -/
def IsSemiHodge (I : Module.End ℝ (V ℝ n)) (s : S ℚ n) : Prop := bcS ℚ ℂ n s ∈ Spq n I 0

end Circle

variable {n : ℕ} {d : ℚ}

namespace KSecant

variable (P : KSecant n d)

/-- For `I ∈ Ω_P`, `Ĩ` is the unique element of `Spin(V_ℝ)_P` satisfying `ρ(Ĩ) = I` (§4, by
Lemma 3.1.1). -/
theorem existsUnique_lift_OmegaP (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∃! g : Spin ℝ n, g ∈ P.spinPR ∧ (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  sorry

/-- `I_θ = cos θ + sin θ I` belongs to `SO_+(V_ℝ)_f` for every `θ ∈ ℝ` and `I ∈ Ω_P` (proof of
Lemma 4.0.3); in particular `𝕊_I` is a subgroup of `SO_+(V_ℝ)` (§4). -/
theorem rotI_mem_SOplusfR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) (θ : ℝ) :
    ∃ g ∈ P.SOplusfR hP.isCompl, (g : V ℝ n →ₗ[ℝ] V ℝ n) = rotI n I θ := by
  sorry

/-- The identity component of the inverse image of `𝕊_I` lies in `Spin(V_ℝ)_P`, and the inverse
image is disconnected (proof of Lemma 4.0.3). -/
theorem circleLift_subset_spinPR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    circleLift n I ⊆ (P.spinPR : Set (Spin ℝ n)) ∧ circleLift n I ≠ circlePreimage n I := by
  sorry

/-- The identity component of the inverse image of `𝕊_I` defines a real Hodge structure of weight `0`
on `S⁺_ℝ = H^{ev}(X, ℝ)` (§4): `S⁺_ℂ = ⊕_{p ∈ ℤ} S^{-p,p}_ℂ`. -/
theorem Spq_iSupIndep (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    iSupIndep (Spq n I) ∧ ⨆ p, Spq n I p = Splus ℂ n := by
  sorry

/-- `\overline{S^{-p,p}_ℂ} = S^{p,-p}_ℂ` (§4; complex conjugation of the coefficients). -/
theorem conj_Spq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) (p : ℤ) :
    conjS (starRingAut : ℂ ≃+* ℂ) n '' (Spq n I p : Set (S ℂ n)) = (Spq n I (-p) : Set (S ℂ n)) := by
  sorry

end KSecant

/-! ## Lemma 4.0.3 and Corollary 4.0.4 -/

/-- **Lemma 4.0.3** (`lemma-Hodge-Weil-classes-remain-of-Hodge-type-for-all-I-in-Omega-P`), part (1):
the plane `⋀^{2n} W₁ ⊕ ⋀^{2n} W₂` corresponds to a rational plane in `⋀^{2n} V_ℚ` (`KSecant.hwPlane`,
`corollary3_2_2_rational`), which is spanned by Hodge classes, for every complex structure `I` in
`Ω_P`. Standing assumption: Assumption 2.4.1. -/
theorem lemma4_0_3_hodgeWeil (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    P.hwPlane ≤ hodgeClassesV n I n := by
  sorry

/-- **Lemma 4.0.3** (`lemma-Hodge-Weil-classes-remain-of-Hodge-type-for-all-I-in-Omega-P`), part (2):
the plane `P` is spanned by semi-Hodge classes, for every complex structure `I` in `Ω_P`. -/
theorem lemma4_0_3_semiHodge (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∀ s ∈ P.Pℚ, IsSemiHodge n I s := by
  sorry

/-- A class `α ∈ ⋀² V_ℚ` is of type `(1,1)` with respect to a complex structure `I` if and only if
`I(α) = α` (`I` acting on `⋀² V_ℝ` by `⋀² I`) (proof of Corollary 4.0.4). -/
theorem mem_hodgeClassesV_one_iff (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (α : ExteriorAlgebra ℚ (V ℚ n)) (hα : α ∈ ⋀[ℚ]^2 (V ℚ n)) :
    α ∈ hodgeClassesV n I 1 ↔ ExteriorAlgebra.map I (bcExt ℚ ℝ n α) = bcExt ℚ ℝ n α := by
  sorry

/-- **Corollary 4.0.4** (`corollary-Spin-V-P-invariant-classes-are-Hodge`). The classes in
`(⋀* V_ℚ)^{Spin(V)_P}` remain of Hodge type for every complex structure in `Ω_P`.

`Spin(V)_P` is the integral group `SpinZ n ⊓ Spin(V_ℚ)_P` acting on `⋀• V_ℚ = H*(X × X̂, ℚ)` by
`ρ` (`rhoExt`); "of Hodge type" means a sum of rational `(p,p)`-classes (`hodgeRingV`). Standing
assumption: Assumption 2.4.1. -/
theorem corollary4_0_4 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (α : ExteriorAlgebra ℚ (V ℚ n)) (hα : ∀ g ∈ SpinZ n ⊓ P.spinPℚ, rhoExt ℚ n g α = α)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) : α ∈ hodgeRingV n I := by
  sorry

end WeilClasses
