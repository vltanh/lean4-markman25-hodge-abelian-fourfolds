module

public import WeilClasses.Hermitian.Defs

/-!
# Elements of `Spin(V)_P` which are complex structures of abelian varieties of Weil type (§3.2)

§3.2 of the paper (TeX lines 1611–1706), under Assumption 2.4.1. Let `I ∈ ρ(Spin(V_ℝ)_P)` be a
complex structure of `V_ℝ` (`I = ρ(Ĩ)`, `Ĩ ∈ Spin(V_ℝ)_P`, `KSecant.spinPR`):

* `I` commutes with `f`, `(I ∘ f)² = d`, and `ν(I)` is the multiplicity of `√d` as an eigenvalue of
  `I ∘ f` (`KSecant.nu`);
* Lemma 3.2.1: if `ν(I) = 2n`, then `V^{1,0}` and `V^{0,1}` meet `W_{1,ℂ}` and `W_{2,ℂ}` in
  `n`-dimensional subspaces, and (3.2.1) `V^{1,0} ∩ W_{2,ℂ} = (V^{1,0} ∩ W_{1,ℂ})^⊥ ∩ W_{2,ℂ}`;
* Corollary 3.2.2: the plane `⋀^{2n} W₁ + ⋀^{2n} W₂` is defined over `ℚ` (`KSecant.hwPlane`, the
  Hodge–Weil classes) and consists of Hodge classes of type `(n, n)`;
* `g_I(x, y) = Ξ_P(x, I y)` (`KSecant.gI`), symmetric;
* Corollary 3.2.3: if `g_I` is positive definite, `(V_ℝ/V_ℤ, I, Ξ_P)` is a polarized abelian
  variety of Weil type — stated as its explicit conditions (`Ξ_P` rational of type `(1,1)` and
  Kähler, `f` commutes with `I`, `dim (W_{i,ℂ} ∩ V^{1,0}) = n`, `f^*Ξ_P = d Ξ_P`).

## The complex torus of Corollary 3.2.3

The paper's proof sets `A := V_ℝ/V_ℤ` with the complex structure `I`, i.e. `V_ℝ` is the tangent
space `H₁(A, ℝ)` of `A` and `I` its complex structure; `Ξ_P` is a `2`-form on `V_ℝ`, i.e. a class in
`H²(A, ℚ) = ⋀² V_ℚ*`. "Kähler" is then `Ξ_P(x, I x) > 0` for `x ≠ 0` ([Huybrechts, Lemma 1.2.15]
convention `ω(v, I v) > 0`, as for `WeilClasses.IsAmple`), and the Weil condition is on the
eigenspaces of `f` in `V_ℂ = H₁(A, ℂ)` (it is equivalent to the condition on `H¹(A, ℂ)` of §1.1, by
duality). Relating `A` to the model `WeilClasses.PolarizedWeilType` is left to the files that use
it.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable {n : ℕ} {d : ℚ}

namespace KSecant

variable (P : KSecant n d)

/-- **`ν(I)`** (§3.2, before Lemma 3.2.1): the multiplicity of the positive square root `√d` as an
eigenvalue of `I ∘ f` (the dimension of the eigenspace; `I ∘ f` is diagonalizable when `I` commutes
with `f`, as `(I ∘ f)² = d`). -/
noncomputable def nu (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) : ℕ :=
  Module.finrank ℝ (Module.End.eigenspace (I * P.fR hW) (Real.sqrt d))

/-- An element `I = ρ(Ĩ)` of `ρ(Spin(V_ℝ)_P)` commutes with `f` (§3.2, by Lemma 3.1.1). -/
theorem rho_spinPR_comm_fR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (g : Spin ℝ n)
    (hg : g ∈ P.spinPR) :
    (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hP.isCompl =
      P.fR hP.isCompl * (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) := by
  sorry

/-- If moreover `I` is a complex structure, `(I ∘ f)² = d · 1` (§3.2). -/
theorem sq_comp_fR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) :
    (I * P.fR hP.isCompl) * (I * P.fR hP.isCompl) = algebraMap ℝ (Module.End ℝ (V ℝ n)) d := by
  sorry

end KSecant

/-! ## Lemma 3.2.1 -/

/-- **Lemma 3.2.1** (`lemma-3-dimensional-eigenvalues`). Assume that `ν(I) = 2n`. Let `V^{1,0}` and
`V^{0,1}` be the eigenspaces of `I` in `V_ℂ` with eigenvalues `±√-1`. Then each of `V^{1,0}` and
`V^{0,1}` intersects each of `W_{1,ℂ}` and `W_{2,ℂ}` along an `n`-dimensional subspace.

Setting of §3.2: `I = ρ(Ĩ)` for some `Ĩ ∈ Spin(V_ℝ)_P` is a complex structure of `V_ℝ`; standing
assumption: Assumption 2.4.1. -/
theorem lemma3_2_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) (hν : P.nu hP.isCompl I = 2 * n) :
    Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) = n ∧ Module.finrank ℂ ↥(V10 n I ⊓ P.W₂ℂ) = n ∧
      Module.finrank ℂ ↥(V01 n I ⊓ P.W₁ℂ) = n ∧ Module.finrank ℂ ↥(V01 n I ⊓ P.W₂ℂ) = n := by
  sorry

/-- **(3.2.1)** (`eq-complex-structure-is-determined-by`), Lemma 3.2.1 continued:
`V^{1,0} ∩ W_{2,ℂ} = (V^{1,0} ∩ W_{1,ℂ})^⊥ ∩ W_{2,ℂ}`, where `(·)^⊥` is the subspace orthogonal with
respect to the pairing `(·,·)_V` (extended to `V_ℂ`). -/
theorem equation3_2_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) (hν : P.nu hP.isCompl I = 2 * n) :
    V10 n I ⊓ P.W₂ℂ = (pairing ℂ n).orthogonal (V10 n I ⊓ P.W₁ℂ) ⊓ P.W₂ℂ := by
  sorry

/-! ## Corollary 3.2.2: the plane of Hodge–Weil classes -/

/-- **The rational plane of Hodge–Weil classes** `ĤW_P ⊆ ⋀^{2n} V_ℚ` (§1.2, Corollary 3.2.2,
Lemma 4.0.3): the rational classes whose image in `⋀• V_K` lies in `⋀^{2n} W₁ + ⋀^{2n} W₂`. -/
noncomputable def KSecant.hwPlane (P : KSecant n d) : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ((topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n)).restrictScalars ℚ).comap (bcExt ℚ (Kd d) n).toLinearMap

/-- `ĤW_P` is a plane (`⋀^{2n} W₁ ≠ ⋀^{2n} W₂` are conjugate lines). -/
theorem KSecant.finrank_hwPlane (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : Module.finrank ℚ P.hwPlane = 2 := by
  sorry

/-- **Corollary 3.2.2** (`cor-plane-of-Hodge-Weil-classes`), first part: the plane
`⋀^{2n} W₁ + ⋀^{2n} W₂` in `⋀^{2n} V_K` is defined over `ℚ`: it is the `K`-span of the rational
plane `ĤW_P`. -/
theorem corollary3_2_2_rational (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' P.hwPlane) = topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) := by
  sorry

/-- **Corollary 3.2.2** (`cor-plane-of-Hodge-Weil-classes`), second part: the plane consists of
rational classes of Hodge type `(n, n)` (the Hodge–Weil classes) for every complex structure `I` in
`ρ(Spin(V_ℝ)_P)` satisfying `ν(I) = 2n`. -/
theorem corollary3_2_2_hodge (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) : P.hwPlane ≤ hodgeClassesV n I n := by
  sorry

/-! ## The form `g_I` and Corollary 3.2.3 -/

/-- **The form `g_I`** (§3.2, before Corollary 3.2.3): `g_I(x, y) = Ξ_P(x, I(y)) = (f(x), I(y))_V`
on `V_ℝ`. -/
noncomputable def KSecant.gI (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂)
    (I : Module.End ℝ (V ℝ n)) : LinearMap.BilinForm ℝ (V ℝ n) :=
  (P.XiR hW).compRight I

/-- `g_I` is symmetric (§3.2): `I` and `f` commute and both are anti-self-dual. (The paper states it
for `I` as in Corollary 3.2.2; `ν(I) = 2n` is not needed.) -/
theorem KSecant.gI_isSymm (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) : (P.gI hP.isCompl I).IsSymm := by
  sorry

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`). If the bilinear form `g_I` is positive
definite, then the rational `(1,1)` class `Ξ_P(x, y)` is a Kähler class, and so the complex torus
`(V_ℝ/V_ℤ, I, Ξ_P)` is a polarized abelian variety of Weil type.

This part: `Ξ_P` is of type `(1,1)` for `I`, i.e. `Ξ_P(I x, I y) = Ξ_P(x, y)`. (`Ξ_P` is rational:
`KSecant.XiR_bcV`.) Setting: `I = ρ(Ĩ)`, `Ĩ ∈ Spin(V_ℝ)_P`, a complex structure with `ν(I) = 2n` (as
in Corollary 3.2.2), `g_I` positive definite; Assumption 2.4.1. -/
theorem corollary3_2_3_type11 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x)
    (x y : V ℝ n) : P.XiR hP.isCompl (I x) (I y) = P.XiR hP.isCompl x y := by
  sorry

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): `Ξ_P` is a Kähler class for the
complex torus `(V_ℝ/V_ℤ, I)`: `Ξ_P(x, I x) > 0` for every nonzero tangent vector `x ∈ V_ℝ`
(convention of [Huybrechts, Lemma 1.2.15]). -/
theorem corollary3_2_3_kahler (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x)
    (x : V ℝ n) (hx : x ≠ 0) : 0 < P.XiR hP.isCompl x (I x) := by
  sorry

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): the embedding `K → End_ℚ(A)` sending
`√-d` to `f` (2.4.1) is by endomorphisms of the complex torus: `f` commutes with `I`. -/
theorem corollary3_2_3_comm (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x) :
    I * P.fR hP.isCompl = P.fR hP.isCompl * I := by
  sorry

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): Weil type — each eigenspace
`W_{i,ℂ}` of `f` meets `V^{1,0}` in an `n`-dimensional subspace (Lemma 3.2.1). -/
theorem corollary3_2_3_weil (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x) :
    Module.finrank ℂ ↥(P.W₁ℂ ⊓ V10 n I) = n ∧ Module.finrank ℂ ↥(P.W₂ℂ ⊓ V10 n I) = n := by
  sorry

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): the condition on the polarization in
[van Geemen, Def. 4.9]: `f^*Ξ_P = d Ξ_P`, i.e. `Ξ_P(f x, f y) = d Ξ_P(x, y)` (which gives
`η(k)^*Ξ_P = Nm(k) Ξ_P` for all `k ∈ K`, `WeilClasses.vanGeemen_def4_9`). -/
theorem corollary3_2_3_polarization (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x)
    (x y : V ℚ n) :
    P.XiQ hP.isCompl (P.fη hP.isCompl x) (P.fη hP.isCompl y) = d * P.XiQ hP.isCompl x y := by
  sorry

end WeilClasses
