module

public import WeilClasses.Hermitian.ComplexStructures
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# An adjoint orbit in `Spin(V_ℝ)_P` as a period domain (paper §4, Lemmas 4.0.1 and 4.0.2)

§4 of the paper up to Lemma 4.0.2 (TeX lines 1711–1804), under Assumption 2.4.1:

* `Ω_P ⊆ SO_+(V_ℝ)_f` (4.0.1) (`KSecant.OmegaP`): the complex structures `I` in `SO_+(V_ℝ)_f` with
  both eigenspaces of `f ∘ I` of dimension `2n` and `g_I` positive definite;
* the Grassmannian `Gr(n, W_{1,ℂ})` (`KSecant.GrW₁`) with its classical topology, and
  `ι(I) = V^{1,0}_I ∩ W_{1,ℂ}` (`KSecant.iota`);
* Lemma 4.0.1: `ι` is injective, with nonempty open image (and a topological embedding);
* Lemma 4.0.2: the connected components of `Ω_P` are `SO_+(V_ℝ)_f`-adjoint orbits (to be proved by
  the authorized departure: direct transitivity of `SO_+(V_ℝ)_f ≅ SU(n, n)`).

## Topologies

* `End(V_ℝ)` carries its Euclidean topology, transported from matrices in the basis `basisV`
  (`WeilClasses.endTopology`, not an instance); `Ω_P` has the subspace topology.
* `Gr(n, W_{1,ℂ})` carries the topology induced by `U ↦ π_U`, the orthogonal projection onto `U` for
  the standard Hermitian inner product of `V_ℂ ≅ ℂ^{4n}` in the basis `basisV` (an operator on
  `EuclideanSpace ℂ (Fin (4n))`, with its norm topology). This is the classical topology of the
  Grassmannian (equivalently, the quotient topology from injective linear maps `ℂⁿ → W_{1,ℂ}`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-- The Euclidean (classical) topology of `End(V_ℝ)`, induced by the matrix in the basis `basisV`
(any linear isomorphism `End(V_ℝ) ≅ ℝ^N` gives the same topology). -/
@[instance_reducible] noncomputable def endTopology (n : ℕ) :
    TopologicalSpace (Module.End ℝ (V ℝ n)) :=
  TopologicalSpace.induced (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) inferInstance

/-- The coordinates of `V_ℂ` in the basis `basisV`, as an isomorphism onto the Hermitian space
`ℂ^{4n}` (`EuclideanSpace ℂ (Fin (2n + 2n))`). -/
noncomputable def eucV (n : ℕ) : V ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * n + 2 * n)) :=
  (basisV ℂ n).equivFun.trans (WithLp.linearEquiv 2 ℂ (Fin (2 * n + 2 * n) → ℂ)).symm

/-- The orthogonal projection `π_U` of `ℂ^{4n}` onto (the coordinates of) a subspace `U ⊆ V_ℂ`, for
the standard Hermitian inner product in the basis `basisV`. -/
noncomputable def projV {n : ℕ} (U : Submodule ℂ (V ℂ n)) :
    EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * n + 2 * n)) :=
  (U.map (eucV n).toLinearMap).starProjection

variable {n : ℕ} {d : ℚ}

namespace KSecant

variable (P : KSecant n d)

/-! ## The period domain `Ω_P` (4.0.1) -/

/-- **`Ω_P`** (4.0.1) (`eq-Omega`): the subset of `SO_+(V_ℝ)_f` of elements `I` such that `I` is a
complex structure on `V_ℝ`, the eigenspaces of `f ∘ I` are both `2n`-dimensional, and the bilinear
form `g_I(x, y) = Ξ_P(x, I y)` of Corollary 3.2.3 is positive definite. (A subset of `End(V_ℝ)`.)
The eigenvalues of `f ∘ I` are `±√d`, as `(f ∘ I)² = d`. -/
def OmegaP (hW : IsCompl P.W₁ P.W₂) : Set (Module.End ℝ (V ℝ n)) :=
  {I | (∃ g ∈ P.SOplusfR hW, (g : V ℝ n →ₗ[ℝ] V ℝ n) = I) ∧ IsComplexStructure I ∧
    Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (Real.sqrt d)) = 2 * n ∧
    Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (-Real.sqrt d)) = 2 * n ∧
    ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hW I x x}

/-! ## The Grassmannian `Gr(n, W_{1,ℂ})` and the map `ι` -/

/-- **`Gr(n, W_{1,ℂ})`**: the `n`-dimensional complex subspaces of `W_{1,ℂ}` (§4). -/
def GrW₁ : Type := {U : Submodule ℂ (V ℂ n) // U ≤ P.W₁ℂ ∧ Module.finrank ℂ U = n}

/-- The classical topology of `Gr(n, W_{1,ℂ})`: induced by the orthogonal projection `U ↦ π_U`. -/
noncomputable instance instTopologicalSpaceGrW₁ : TopologicalSpace P.GrW₁ :=
  TopologicalSpace.induced (fun U : P.GrW₁ => projV U.1) inferInstance

/-- For `I ∈ Ω_P`, `V^{1,0}_I ∩ W_{1,ℂ}` is `n`-dimensional (Lemma 3.2.1; "The map `ι` is well
defined, by Lemma 3.2.1"). -/
theorem finrank_V10_inf_W₁ℂ (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) = n := by
  sorry

/-- **The map `ι : Ω_P → Gr(n, W_{1,ℂ})`**, `ι(I) = V^{1,0}_I ∩ W_{1,ℂ}` (§4, after (4.0.1)). -/
noncomputable def iota (hW : IsCompl P.W₁ P.W₂) (I : P.OmegaP hW) : P.GrW₁ :=
  ⟨V10 n I.1 ⊓ P.W₁ℂ, inf_le_right, P.finrank_V10_inf_W₁ℂ hW I.1 I.2⟩

/-- For `I = I_{V_ℝ}` the complex structure of `X × X̂`, `g_I = -g_P` (proof of Lemma 4.0.1:
"the … bilinear form `g_P` of Proposition 2.4.4 is `-g_I`"). -/
theorem gI_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.gI hP.isCompl (productStructure n J) = -P.gP hP.isCompl J := by
  sorry

/-! ## The adjoint orbits -/

/-- The `SO_+(V_ℝ)_f`-adjoint orbit `{h I h⁻¹ : h ∈ SO_+(V_ℝ)_f}` of `I ∈ End(V_ℝ)`. -/
def adjointOrbit (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) :
    Set (Module.End ℝ (V ℝ n)) :=
  {I' | ∃ h ∈ P.SOplusfR hW, I' = (h : V ℝ n →ₗ[ℝ] V ℝ n) * I *
    ((h⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : V ℝ n →ₗ[ℝ] V ℝ n)}

/-- `Ω_P` is a union of `SO_+(V_ℝ)_f`-adjoint orbits: `g_{hIh⁻¹}(x, y) = g_I(h⁻¹x, h⁻¹y)` (proof of
Lemma 4.0.2). -/
theorem adjointOrbit_subset_OmegaP (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    P.adjointOrbit hP.isCompl I ⊆ P.OmegaP hP.isCompl := by
  sorry

end KSecant

/-! ## Lemma 4.0.1 -/

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`). The map `ι` is
an embedding of `Ω_P` as a non-empty subset, open in the classical topology, of the Grassmannian
`Gr(n, W_{1,ℂ})`. This part: `ι` is injective. Standing assumption: Assumption 2.4.1. -/
theorem lemma4_0_1_injective (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : Function.Injective (P.iota hP.isCompl) := by
  sorry

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): `Ω_P` is non-empty.

The paper's proof uses `I = I_{V_ℝ}` (the complex structure of `X × X̂`) and Proposition 2.4.4,
which concerns `P = P_Θ` (`productStructure_mem_OmegaP`). The statement holds for every `P`
satisfying Assumption 2.4.1: `H` has signature `(n, n)` (Lemma 3.1.2), so `V_ℝ` has an `f`-stable
maximal negative definite subspace `V₋` (for `(·,·)_V`); with `f̃ = f/√d` and `K = 1` on `V₋`,
`K = -1` on `V₋^⊥`, `I = -f̃ K` lies in `Ω_P` (`g_I(x, x) = -√d (x, K x)_V`; `SO_+` by
Remark 2.4.3). -/
theorem lemma4_0_1_nonempty (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : (P.OmegaP hP.isCompl).Nonempty := by
  sorry

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): the image of `ι` is open in the classical topology of `Gr(n, W_{1,ℂ})`. -/
theorem lemma4_0_1_isOpen (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : IsOpen (Set.range (P.iota hP.isCompl)) := by
  sorry

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): `ι` is an embedding (a homeomorphism onto its image) for the subspace topology
of `Ω_P ⊆ End(V_ℝ)`. Reading: "embedding" in the topological sense; the proof constructs the
inverse `U ↦ I_U`, `V^{1,0}_{I_U} = U ⊕ (U^⊥ ∩ W_{2,ℂ})`. -/
theorem lemma4_0_1_isEmbedding (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    @Topology.IsEmbedding _ _ (@instTopologicalSpaceSubtype _ _ (endTopology n)) _
      (P.iota hP.isCompl) := by
  sorry

/-- In the proof of Lemma 4.0.1 (nonemptiness): for `P = P_Θ` with `Θ` ample for `J`, the complex
structure `I = I_{V_ℝ} = productStructure n J` of `X × X̂` lies in `Ω_{P_Θ}`: `g_I = -g_P` is positive
definite by Proposition 2.4.4, `I` commutes with `f` (Lemma 2.2.6), lies in `SO_+(V_ℝ)` (Remark
2.4.3), has determinant `1` on `W₁` and `W₂`, and `ν(I) = 2n`. -/
theorem productStructure_mem_OmegaP (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    productStructure n J ∈ (PTheta n d hd Θ hΘ.mem_exteriorPower_two
      (hΘ.ne_zero_of_pos hn)).OmegaP (PTheta_isCompl n d hd Θ _ _ hΘ.bijective_thetaMap) := by
  sorry

/-! ## Lemma 4.0.2 -/

/-- **Lemma 4.0.2** (`lemma-period-domain-is-an-adjoint-orbit`). The connected components of `Ω_P`
are `SO_+(V_ℝ)_f`-adjoint orbits: for `I ∈ Ω_P`, the connected component of `I` in `Ω_P` (subspace
topology of `End(V_ℝ)`) is the adjoint orbit of `I`. Standing assumption: Assumption 2.4.1.
(To be proved by the authorized departure: direct transitivity of `SO_+(V_ℝ)_f ≅ SU(n, n)` on
`Ω_P`, instead of the paper's dimension count.) -/
theorem lemma4_0_2 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    @connectedComponentIn _ (endTopology n) (P.OmegaP hP.isCompl) I =
      P.adjointOrbit hP.isCompl I := by
  sorry

end WeilClasses
