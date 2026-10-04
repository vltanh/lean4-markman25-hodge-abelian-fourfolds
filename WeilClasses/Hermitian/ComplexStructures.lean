module

public import WeilClasses.Hermitian.Defs

/-!
# Elements of `Spin(V)_P` which are complex structures of abelian varieties of Weil type (§3.2)

§3.2 of the paper (TeX lines 1611–1706), under Assumption 2.4.1. Let `I ∈ ρ(Spin(V_ℝ)_P)` be a
complex structure of `V_ℝ` (`I = ρ(Ĩ)`, `Ĩ ∈ Spin(V_ℝ)_P`, `KSecant.spinPR`; before (3.2.1), TeX line
1678, the paper writes `Spin(V_ℝ)_w`, a misprint for `Spin(V_ℝ)_P`):

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

theorem s3_pairing_bcV (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']
    (x y : V F n) :
    pairing F' n (bcV F F' n x) (bcV F F' n y) = algebraMap F F' (pairing F n x y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, bcV,
    LinearMap.prodMap_apply, s3_bcDual_bcH1, map_add]

namespace KSecant

variable (P : KSecant n d)

/-- `f` is anti-self-dual on `V_ℝ`. -/
theorem s3_pairing_fR_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℝ n) :
    pairing ℝ n (P.fR hW x) y = -pairing ℝ n x (P.fR hW y) := by
  have key : ∀ a b : V ℚ n, pairing ℝ n (P.fR hW (bcV ℚ ℝ n a)) (bcV ℚ ℝ n b) =
      -pairing ℝ n (bcV ℚ ℝ n a) (P.fR hW (bcV ℚ ℝ n b)) := by
    intro a b
    rw [fR, s3_bcEndV_eq, s3_ext_bcV, s3_ext_bcV, s3_pairing_bcV, s3_pairing_bcV,
      P.pairing_fη_left hW, map_neg]
  have h1 : (pairing ℝ n).compl₁₂ (P.fR hW) LinearMap.id =
      -((pairing ℝ n).compl₁₂ LinearMap.id (P.fR hW)) := by
    refine (basisV ℝ n).ext fun i => (basisV ℝ n).ext fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.neg_apply]
    rw [← s3_bcV_basisV ℚ ℝ, ← s3_bcV_basisV ℚ ℝ]
    exact key _ _
  have := LinearMap.congr_fun₂ h1 x y
  simpa using this

/-- `ρ(Spin(V_ℝ)_P)` commutes with `f` ("by Lemma 3.1.1"). -/
theorem s3_rho_mem_SOplusfR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (g : Spin ℝ n)
    (hg : g ∈ P.spinPR) : rho ℝ n g ∈ P.SOplusfR hP.isCompl := by
  have h := (lemma3_1_1_real P J hP).2
  have : rho ℝ n g ∈ rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) := ⟨g, hg, rfl⟩
  rw [h] at this
  exact this

/-- **`ν(I)`** (§3.2, before Lemma 3.2.1): the multiplicity of the positive square root `√d` as an
eigenvalue of `I ∘ f` (the dimension of the eigenspace; `I ∘ f` is diagonalizable when `I` commutes
with `f`, as `(I ∘ f)² = d`). -/
noncomputable def nu (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) : ℕ :=
  Module.finrank ℝ (Module.End.eigenspace (I * P.fR hW) (Real.sqrt d))

/-- An element `I = ρ(Ĩ)` of `ρ(Spin(V_ℝ)_P)` commutes with `f` (§3.2, by Lemma 3.1.1). -/
theorem rho_spinPR_comm_fR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (g : Spin ℝ n)
    (hg : g ∈ P.spinPR) :
    (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hP.isCompl =
      P.fR hP.isCompl * (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) :=
  -- `ρ(g) ∈ SO_+(V_ℝ)_f` by Lemma 3.1.1
  LinearMap.ext fun x => (P.s3_rho_mem_SOplusfR J hP g hg).2.1 x

/-- `I = ρ(g)` is an isometry of `(·,·)_V`. -/
theorem s3_pairing_I (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (x y : V ℝ n) :
    pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
  obtain ⟨g, -, rfl⟩ := hIP
  exact s3_pairing_rho g x y

/-- A complex structure `I` which is an isometry is anti-self-dual. -/
theorem s3_pairing_I_left (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (x y : V ℝ n) : pairing ℝ n (I x) y = -pairing ℝ n x (I y) := by
  have h := P.s3_pairing_I I hIP (I x) y
  have hII : I (I x) = -x := by
    have := LinearMap.congr_fun hI x
    simpa using this
  rw [hII, map_neg, LinearMap.neg_apply] at h
  rw [← h]

/-- If moreover `I` is a complex structure, `(I ∘ f)² = d · 1` (§3.2). -/
theorem sq_comp_fR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) :
    (I * P.fR hP.isCompl) * (I * P.fR hP.isCompl) = algebraMap ℝ (Module.End ℝ (V ℝ n)) d := by
  obtain ⟨g, hg, rfl⟩ := hIP
  have hcomm := P.rho_spinPR_comm_fR J hP g hg
  have hff : P.fR hP.isCompl * P.fR hP.isCompl = -algebraMap ℝ (Module.End ℝ (V ℝ n)) d := by
    rw [fR, s3_bcEndV_eq, ← s3_ext_mul, show P.fη hP.isCompl * P.fη hP.isCompl =
      P.fη hP.isCompl ∘ₗ P.fη hP.isCompl from rfl, P.fη_comp_fη, s3_ext_neg, s3_ext_smul,
      s3_ext_id, Module.algebraMap_end_eq_smul_id]
    rfl
  calc ((rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hP.isCompl) *
        ((rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hP.isCompl)
      = ((rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) * (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n)) *
          (P.fR hP.isCompl * P.fR hP.isCompl) := by
        rw [mul_assoc, ← mul_assoc (P.fR hP.isCompl), ← hcomm, mul_assoc, mul_assoc]
    _ = algebraMap ℝ (Module.End ℝ (V ℝ n)) d := by
        rw [hI, hff, neg_one_mul, neg_neg]

end KSecant

/-! ## Complexification and conjugation (helpers for Lemma 3.2.1) -/

section S3Complex

/-- Real part of the coordinates of a vector of `V_ℂ`. -/
noncomputable def s3_reV : V ℂ n →ₗ[ℝ] V ℝ n :=
  (basisV ℝ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun i => Complex.reLm ∘ₗ ((basisV ℂ n).coord i).restrictScalars ℝ)

/-- Imaginary part of the coordinates of a vector of `V_ℂ`. -/
noncomputable def s3_imV : V ℂ n →ₗ[ℝ] V ℝ n :=
  (basisV ℝ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun i => Complex.imLm ∘ₗ ((basisV ℂ n).coord i).restrictScalars ℝ)

theorem s3_repr_reV (z : V ℂ n) (i) : (basisV ℝ n).repr (s3_reV z) i = ((basisV ℂ n).repr z i).re := by
  simp only [s3_reV, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self, LinearMap.pi_apply]
  rfl

theorem s3_repr_imV (z : V ℂ n) (i) : (basisV ℝ n).repr (s3_imV z) i = ((basisV ℂ n).repr z i).im := by
  simp only [s3_imV, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self, LinearMap.pi_apply]
  rfl

/-- `z = re z + i im z`. -/
theorem s3_re_add_im (z : V ℂ n) :
    bcV ℝ ℂ n (s3_reV z) + Complex.I • bcV ℝ ℂ n (s3_imV z) = z := by
  apply (basisV ℂ n).repr.injective
  ext i
  rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s3_bcV_repr, s3_bcV_repr,
    s3_repr_reV, s3_repr_imV]
  apply Complex.ext <;> simp

/-- `x + i y = 0` with `x, y` real forces `x = y = 0`. -/
theorem s3_re_im_eq_zero {x y : V ℝ n} (h : bcV ℝ ℂ n x + Complex.I • bcV ℝ ℂ n y = 0) :
    x = 0 ∧ y = 0 := by
  have hc : ∀ i, (basisV ℝ n).repr x i = 0 ∧ (basisV ℝ n).repr y i = 0 := by
    intro i
    have := congrArg (fun z => (basisV ℂ n).repr z i) h
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s3_bcV_repr, map_zero,
      Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at this
    have h1 := congrArg Complex.re this
    have h2 := congrArg Complex.im this
    simp at h1 h2
    exact ⟨h1, h2⟩
  constructor
  · apply (basisV ℝ n).repr.injective; ext i; simp [(hc i).1]
  · apply (basisV ℝ n).repr.injective; ext i; simp [(hc i).2]

/-- Real linearly independent vectors stay independent over `ℂ`. -/
theorem s3_linearIndependent_bcV {ι : Type*} {v : ι → V ℝ n} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (bcV ℝ ℂ n ∘ v) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : bcV ℝ ℂ n (∑ j ∈ s, (g j).re • v j) +
      Complex.I • bcV ℝ ℂ n (∑ j ∈ s, (g j).im • v j) = 0 := by
    rw [← hg]
    simp only [map_sum, map_smul, Function.comp_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul ℂ (g j).re, ← algebraMap_smul ℂ (g j).im, smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp
  obtain ⟨h2, h3⟩ := s3_re_im_eq_zero h1
  have hre := (linearIndependent_iff'.mp hv) s (fun j => (g j).re) h2 i hi
  have him := (linearIndependent_iff'.mp hv) s (fun j => (g j).im) h3 i hi
  exact Complex.ext hre him

/-- The kernel of a complexified endomorphism is the complexification of the kernel. -/
theorem s3_finrank_ker_ext (A : Module.End ℝ (V ℝ n)) :
    Module.finrank ℂ (LinearMap.ker (s3_ext ℝ ℂ n A)) = Module.finrank ℝ (LinearMap.ker A) := by
  set b := Module.finBasis ℝ (LinearMap.ker A)
  set v : Fin (Module.finrank ℝ (LinearMap.ker A)) → V ℝ n := fun i => (b i : V ℝ n) with hv
  have hv' : LinearIndependent ℝ v :=
    b.linearIndependent.map' (LinearMap.ker A).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bcV ℝ ℂ n ∘ v) := s3_linearIndependent_bcV hv'
  have hspan : Submodule.span ℂ (Set.range (bcV ℝ ℂ n ∘ v)) =
      LinearMap.ker (s3_ext ℝ ℂ n A) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [Function.comp_apply, SetLike.mem_coe, LinearMap.mem_ker, s3_ext_bcV]
      rw [(b i).2, map_zero]
    · intro z hz
      rw [← s3_re_add_im z] at hz ⊢
      rw [LinearMap.mem_ker, map_add, map_smul, s3_ext_bcV, s3_ext_bcV] at hz
      obtain ⟨h1, h2⟩ := s3_re_im_eq_zero hz
      have hmem : ∀ x ∈ LinearMap.ker A, bcV ℝ ℂ n x ∈
          Submodule.span ℂ (Set.range (bcV ℝ ℂ n ∘ v)) := by
        intro x hx
        have hx' : (⟨x, hx⟩ : LinearMap.ker A) = ∑ i, b.repr ⟨x, hx⟩ i • b i := (b.sum_repr _).symm
        have : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : V ℝ n) := by
          have := congrArg Subtype.val hx'
          rw [Submodule.coe_sum] at this
          simpa only [Submodule.coe_smul] using this
        rw [this, map_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [map_smul, ← algebraMap_smul ℂ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      exact Submodule.add_mem _ (hmem _ h1) (Submodule.smul_mem _ _ (hmem _ h2))
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]


/-- Complex conjugation on `V_ℂ`. -/
noncomputable abbrev s3_cV : V ℂ n →+ V ℂ n := conjV (starRingAut : ℂ ≃+* ℂ) n

theorem s3_cV_smul (a : ℂ) (z : V ℂ n) : s3_cV (a • z) = (starRingEnd ℂ) a • s3_cV z :=
  s3_conjV_smul _ a z

theorem s3_cV_cV (z : V ℂ n) : s3_cV (s3_cV z) = z := by
  show conjV (starRingAut : ℂ ≃+* ℂ) n (conjV (starRingAut : ℂ ≃+* ℂ) n z) = z
  rw [s3_conjV_eq (n := n) (starRingAut : ℂ ≃+* ℂ) (conjV (starRingAut : ℂ ≃+* ℂ) n z)]
  conv_rhs => rw [← (basisV ℂ n).sum_repr z]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s3_conjV_eq, (basisV ℂ n).repr_sum_self]
  simp

theorem s3_cV_injective : Function.Injective (s3_cV (n := n)) :=
  Function.LeftInverse.injective s3_cV_cV

/-- Conjugation commutes with complexified real endomorphisms. -/
theorem s3_cV_ext (A : Module.End ℝ (V ℝ n)) (z : V ℂ n) :
    s3_ext ℝ ℂ n A (s3_cV z) = s3_cV (s3_ext ℝ ℂ n A z) := by
  show s3_ext ℝ ℂ n A (conjV (starRingAut : ℂ ≃+* ℂ) n z) =
    conjV (starRingAut : ℂ ≃+* ℂ) n (s3_ext ℝ ℂ n A z)
  rw [s3_conjV_eq, s3_conjV_eq]
  apply s3_conj_comm
  intro i j
  rw [← s3_bcV_basisV ℝ ℂ, s3_ext_bcV, s3_bcV_repr]
  simp

/-- Conjugation preserves the eigenspace of a complexified real endomorphism for a real
eigenvalue. -/
theorem s3_cV_mem_eigenspace (A : Module.End ℝ (V ℝ n)) (c : ℝ) {z : V ℂ n}
    (hz : z ∈ Module.End.eigenspace (s3_ext ℝ ℂ n A) (c : ℂ)) :
    s3_cV z ∈ Module.End.eigenspace (s3_ext ℝ ℂ n A) (c : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  rw [s3_cV_ext, hz, s3_cV_smul, Complex.conj_ofReal]

/-- `conj(bcV w) = bcV(σ w)`. -/
theorem s3_cV_bcV {d : ℚ} (w : V (Kd d) n) :
    s3_cV (bcV (Kd d) ℂ n w) = bcV (Kd d) ℂ n (σV n d w) := by
  apply (basisV ℂ n).repr.injective
  ext i
  show (basisV ℂ n).repr (conjV (starRingAut : ℂ ≃+* ℂ) n (bcV (Kd d) ℂ n w)) i = _
  rw [s3_conjV_eq, (basisV ℂ n).repr_sum_self, s3_bcV_repr, s3_bcV_repr]
  show (starRingEnd ℂ) ((basisV (Kd d) n).repr w i : ℂ) =
    (((basisV (Kd d) n).repr (conjV (Kd.σ d) n w) i : Kd d) : ℂ)
  rw [s3_conjV_eq, (basisV (Kd d) n).repr_sum_self, Kd.coe_σ]

/-- A conjugation-equivariant inclusion does not decrease dimension. -/
theorem s3_finrank_le_of_cV {U U' : Submodule ℂ (V ℂ n)} (h : ∀ x ∈ U, s3_cV x ∈ U') :
    Module.finrank ℂ U ≤ Module.finrank ℂ U' := by
  set b := Module.finBasis ℂ U
  let w : Fin (Module.finrank ℂ U) → U' := fun i => ⟨s3_cV (b i : V ℂ n), h _ (b i).2⟩
  have hw : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 : s3_cV (∑ j ∈ s, (starRingEnd ℂ) (g j) • (b j : V ℂ n)) = 0 := by
      rw [map_sum]
      simp only [s3_cV_smul, Complex.conj_conj]
      have := congrArg Subtype.val hg
      simpa [w] using this
    have h2 : ∑ j ∈ s, (starRingEnd ℂ) (g j) • (b j : V ℂ n) = 0 :=
      s3_cV_injective (h1.trans (map_zero _).symm)
    have h3 : ∑ j ∈ s, (starRingEnd ℂ) (g j) • b j = 0 := by
      apply Subtype.ext
      simpa using h2
    have := (linearIndependent_iff'.mp b.linearIndependent) s _ h3 i hi
    simpa using this
  have := hw.fintype_card_le_finrank
  simpa using this


theorem s3_finrank_eigenspace_ext (A : Module.End ℝ (V ℝ n)) (c : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (s3_ext ℝ ℂ n A) (c : ℂ)) =
      Module.finrank ℝ (Module.End.eigenspace A c) := by
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def]
  have : s3_ext ℝ ℂ n (A - c • 1) = s3_ext ℝ ℂ n A - (c : ℂ) • 1 := by
    rw [sub_eq_add_neg, s3_ext_add, s3_ext_neg, s3_ext_smul, s3_ext_one, sub_eq_add_neg]
    rfl
  rw [← this, s3_finrank_ker_ext]

/-- Eigenspaces of an endomorphism commuting with `B` are `B`-stable. -/
theorem s3_mem_eigenspace_of_comm {A B : Module.End ℂ (V ℂ n)} (hAB : A * B = B * A) {μ : ℂ}
    {x : V ℂ n} (hx : x ∈ Module.End.eigenspace A μ) : B x ∈ Module.End.eigenspace A μ := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← Module.End.mul_apply, hAB, Module.End.mul_apply, hx, map_smul]

end S3Complex

namespace KSecant

variable (P : KSecant n d)

theorem s3_cV_mem_W₂ℂ {x : V ℂ n} (hx : x ∈ P.W₁ℂ) : s3_cV x ∈ P.W₂ℂ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [s3_cV_bcV]
    exact Submodule.subset_span ⟨_, P.s3_σV_mem_W₂ hw, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [s3_cV_smul]; exact Submodule.smul_mem _ _ hy

theorem s3_cV_mem_W₁ℂ {x : V ℂ n} (hx : x ∈ P.W₂ℂ) : s3_cV x ∈ P.W₁ℂ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [s3_cV_bcV]
    exact Submodule.subset_span ⟨_, P.s3_σV_mem_W₁ hw, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [s3_cV_smul]; exact Submodule.smul_mem _ _ hy

/-- A `f_ℂ`-stable subspace splits along `V_ℂ = W_{1,ℂ} ⊕ W_{2,ℂ}`. -/
theorem s3_split_sup (hW : IsCompl P.W₁ P.W₂) (L : Submodule ℂ (V ℂ n))
    (hL : ∀ x ∈ L, complexifyV n (P.fR hW) x ∈ L) : L ⊓ P.W₁ℂ ⊔ L ⊓ P.W₂ℂ = L := by
  have hs : ((Kd.sqrtNeg d : Kd d) : ℂ) ≠ 0 := by exact_mod_cast s3_sqrtNeg_ne_zero (s3_d_pos P)
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
    Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
  have hf := hL _ hx
  rw [map_add, P.s3_fℂ_W₁ hW hx₁, P.s3_fℂ_W₂ hW hx₂] at hf
  have e0 : ((Kd.sqrtNeg d : Kd d) : ℂ)⁻¹ •
      (((Kd.sqrtNeg d : Kd d) : ℂ) • x₁ + -((Kd.sqrtNeg d : Kd d) : ℂ) • x₂) = x₁ - x₂ := by
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, mul_neg, inv_mul_cancel₀ hs,
      one_smul, neg_smul, one_smul, sub_eq_add_neg]
  have e1 : x₁ = (2 : ℂ)⁻¹ • ((x₁ + x₂) + ((Kd.sqrtNeg d : Kd d) : ℂ)⁻¹ •
      (((Kd.sqrtNeg d : Kd d) : ℂ) • x₁ + -((Kd.sqrtNeg d : Kd d) : ℂ) • x₂)) := by
    rw [e0, add_add_sub_cancel, ← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hx₁L : x₁ ∈ L := by
    rw [e1]; exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx (Submodule.smul_mem _ _ hf))
  have hx₂L : x₂ ∈ L := by
    have := Submodule.sub_mem _ hx hx₁L
    rwa [add_sub_cancel_left] at this
  exact Submodule.add_mem_sup ⟨hx₁L, hx₁⟩ ⟨hx₂L, hx₂⟩

/-- A `f_ℂ`-stable subspace splits along `V_ℂ = W_{1,ℂ} ⊕ W_{2,ℂ}` (dimensions). -/
theorem s3_finrank_split (hW : IsCompl P.W₁ P.W₂) (L : Submodule ℂ (V ℂ n))
    (hL : ∀ x ∈ L, complexifyV n (P.fR hW) x ∈ L) :
    Module.finrank ℂ ↥(L ⊓ P.W₁ℂ) + Module.finrank ℂ ↥(L ⊓ P.W₂ℂ) = Module.finrank ℂ L := by
  have hsup := P.s3_split_sup hW L hL
  have hinf : L ⊓ P.W₁ℂ ⊓ (L ⊓ P.W₂ℂ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.disjoint_def.mp (P.s3_isCompl_ℂ hW).disjoint) x hx.1.2 hx.2.2
  have := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ P.W₁ℂ) (L ⊓ P.W₂ℂ)
  rw [hsup, hinf, finrank_bot, add_zero] at this
  exact this.symm


/-- `a • y = b • x ↔ y = (b / a) • x` for `a ≠ 0`. -/
theorem _root_.WeilClasses.s3_smul_eq_smul_iff {a b : ℂ} (ha : a ≠ 0) (x y : V ℂ n) :
    a • y = b • x ↔ y = (b / a) • x := by
  constructor
  · intro h
    rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rintro rfl
    rw [smul_smul, mul_div_cancel₀ _ ha]

/-- The core of the proof of Lemma 3.2.1: `I` a complex structure commuting with `f` with
`ν(I) = 2n`. `L₁`, `L₂` are the `-√d`, `√d`-eigenspaces of `I ∘ f` in `V_ℂ`. -/
theorem s3_core (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hcomm : I * P.fR hW = P.fR hW * I) (hI : IsComplexStructure I) (hν : P.nu hW I = 2 * n) :
    Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) = n ∧ Module.finrank ℂ ↥(V10 n I ⊓ P.W₂ℂ) = n ∧
      Module.finrank ℂ ↥(V01 n I ⊓ P.W₁ℂ) = n ∧ Module.finrank ℂ ↥(V01 n I ⊓ P.W₂ℂ) = n := by
  have hd := s3_d_pos P
  set Ic := complexifyV n I with hIc
  set fc := complexifyV n (P.fR hW) with hfc
  set Tc := s3_ext ℝ ℂ n (I * P.fR hW) with hTc
  have hTc' : Tc = Ic * fc := s3_ext_mul ℝ ℂ n _ _
  have hIfc : Ic * fc = fc * Ic := by
    rw [hIc, hfc, s3_complexifyV_eq, s3_complexifyV_eq, ← s3_ext_mul, hcomm, s3_ext_mul]
  have hII : Ic * Ic = -1 := by
    rw [hIc, s3_complexifyV_eq, ← s3_ext_mul, hI, s3_ext_neg, s3_ext_one]
  have hff : fc * fc = -((d : ℂ) • 1) := by
    rw [hfc, s3_complexifyV_eq, ← s3_ext_mul, fR, s3_bcEndV_eq, ← s3_ext_mul,
      show P.fη hW * P.fη hW = P.fη hW ∘ₗ P.fη hW from rfl, P.fη_comp_fη, s3_ext_neg,
      s3_ext_smul, s3_ext_id, s3_ext_neg, s3_ext_smul, s3_ext_id]
    congr 2
  set c : ℂ := ((Real.sqrt (d : ℝ) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hcc : c * c = (d : ℂ) := by
    rw [hc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hd.le)]
    simp
  have hs : ((Kd.sqrtNeg d : Kd d) : ℂ) = Complex.I * c := rfl
  have hTT : ∀ x, Tc (Tc x) = (d : ℂ) • x := by
    intro x
    rw [← Module.End.mul_apply, hTc', mul_assoc, ← mul_assoc fc, ← hIfc, mul_assoc, ← mul_assoc,
      hII, hff]
    simp
  set L₁ := Module.End.eigenspace Tc (-c) with hL₁
  set L₂ := Module.End.eigenspace Tc c with hL₂
  -- `dim L₂ = ν(I) = 2n`
  have hL₂dim : Module.finrank ℂ L₂ = 2 * n := by
    rw [hL₂, hTc, hc, s3_finrank_eigenspace_ext]
    exact hν
  -- `V_ℂ = L₁ ⊕ L₂`
  have hL₁₂ : IsCompl L₁ L₂ := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h₁ h₂
      rw [hL₁, Module.End.mem_eigenspace_iff] at h₁
      rw [hL₂, Module.End.mem_eigenspace_iff] at h₂
      have : (2 * c) • x = 0 := by
        have e : (2 * c) • x = c • x - (-c) • x := by module
        rw [e, ← h₁, ← h₂, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hc0)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have e : x = (2 * c)⁻¹ • (c • x - Tc x) + (2 * c)⁻¹ • (c • x + Tc x) := by
        rw [← smul_add, sub_add_add_cancel, ← two_smul ℂ (c • x), smul_smul, smul_smul,
          mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hc0), one_smul]
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [hL₁, Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hTT, smul_smul,
          smul_sub, smul_sub, smul_smul, ← hcc]
        module
      · rw [hL₂, Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hTT, ← hcc]
        module
  have hL₁dim : Module.finrank ℂ L₁ = 2 * n := by
    have := Submodule.finrank_add_eq_of_isCompl hL₁₂
    rw [hL₂dim, s3_finrank_V] at this
    omega
  -- on `W_{i,ℂ}`, `I ∘ f = ±√-d I`; identification of `Lⱼ ∩ W_{i,ℂ}`
  have hs0 : Complex.I * c ≠ 0 := mul_ne_zero Complex.I_ne_zero hc0
  have hmem : ∀ (a μ : ℂ) (x : V ℂ n), a ≠ 0 → Tc x = a • Ic x →
      (x ∈ Module.End.eigenspace Tc μ ↔ x ∈ Module.End.eigenspace Ic (μ / a)) := by
    intro a μ x ha hx
    rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, hx,
      s3_smul_eq_smul_iff ha]
  have hT₁ : ∀ x ∈ P.W₁ℂ, Tc x = (Complex.I * c) • Ic x := by
    intro x hx
    rw [hTc', Module.End.mul_apply, P.s3_fℂ_W₁ hW hx, map_smul, hs]
  have hT₂ : ∀ x ∈ P.W₂ℂ, Tc x = (-(Complex.I * c)) • Ic x := by
    intro x hx
    rw [hTc', Module.End.mul_apply, P.s3_fℂ_W₂ hW hx, map_smul, hs]
  have e1 : -c / (Complex.I * c) = Complex.I := by
    rw [div_eq_iff hs0]; linear_combination (-c) * Complex.I_mul_I
  have e2 : -c / (-(Complex.I * c)) = -Complex.I := by
    rw [div_eq_iff (neg_ne_zero.mpr hs0)]; linear_combination (-c) * Complex.I_mul_I
  have e3 : c / (Complex.I * c) = -Complex.I := by
    rw [div_eq_iff hs0]; linear_combination (c) * Complex.I_mul_I
  have e4 : c / (-(Complex.I * c)) = Complex.I := by
    rw [div_eq_iff (neg_ne_zero.mpr hs0)]; linear_combination (c) * Complex.I_mul_I
  have h11 : L₁ ⊓ P.W₁ℂ = V10 n I ⊓ P.W₁ℂ := by
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := (hmem _ (-c) x hs0 (hT₁ x h2)).mp h1
      rwa [e1] at this
    · rintro ⟨h1, h2⟩
      refine ⟨(hmem _ (-c) x hs0 (hT₁ x h2)).mpr ?_, h2⟩
      rw [e1]; exact h1
  have h12 : L₁ ⊓ P.W₂ℂ = V01 n I ⊓ P.W₂ℂ := by
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := (hmem _ (-c) x (neg_ne_zero.mpr hs0) (hT₂ x h2)).mp h1
      rwa [e2] at this
    · rintro ⟨h1, h2⟩
      refine ⟨(hmem _ (-c) x (neg_ne_zero.mpr hs0) (hT₂ x h2)).mpr ?_, h2⟩
      rw [e2]; exact h1
  have h21 : L₂ ⊓ P.W₁ℂ = V01 n I ⊓ P.W₁ℂ := by
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := (hmem _ c x hs0 (hT₁ x h2)).mp h1
      rwa [e3] at this
    · rintro ⟨h1, h2⟩
      refine ⟨(hmem _ c x hs0 (hT₁ x h2)).mpr ?_, h2⟩
      rw [e3]; exact h1
  have h22 : L₂ ⊓ P.W₂ℂ = V10 n I ⊓ P.W₂ℂ := by
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := (hmem _ c x (neg_ne_zero.mpr hs0) (hT₂ x h2)).mp h1
      rwa [e4] at this
    · rintro ⟨h1, h2⟩
      refine ⟨(hmem _ c x (neg_ne_zero.mpr hs0) (hT₂ x h2)).mpr ?_, h2⟩
      rw [e4]; exact h1
  -- `Lⱼ` is `f`-stable, so splits along `W_{1,ℂ} ⊕ W_{2,ℂ}`
  have hTf : Tc * fc = fc * Tc := by
    rw [hTc', mul_assoc, ← mul_assoc fc, ← hIfc, mul_assoc]
  have hsplit₁ := P.s3_finrank_split hW L₁ fun x hx => s3_mem_eigenspace_of_comm hTf hx
  have hsplit₂ := P.s3_finrank_split hW L₂ fun x hx => s3_mem_eigenspace_of_comm hTf hx
  -- complex conjugation exchanges `Lⱼ ∩ W_{1,ℂ}` and `Lⱼ ∩ W_{2,ℂ}`
  have hcL₁ : ∀ x ∈ L₁, s3_cV x ∈ L₁ := by
    intro x hx
    have := s3_cV_mem_eigenspace (I * P.fR hW) (-Real.sqrt (d : ℝ)) (z := x)
      (by rw [Complex.ofReal_neg]; exact hx)
    rwa [Complex.ofReal_neg] at this
  have hcL₂ : ∀ x ∈ L₂, s3_cV x ∈ L₂ := fun x hx =>
    s3_cV_mem_eigenspace (I * P.fR hW) (Real.sqrt (d : ℝ)) hx
  have hconj : ∀ L : Submodule ℂ (V ℂ n), (∀ x ∈ L, s3_cV x ∈ L) →
      Module.finrank ℂ ↥(L ⊓ P.W₁ℂ) = Module.finrank ℂ ↥(L ⊓ P.W₂ℂ) := by
    intro L hL
    apply le_antisymm
    · exact s3_finrank_le_of_cV fun x hx => ⟨hL x hx.1, P.s3_cV_mem_W₂ℂ hx.2⟩
    · exact s3_finrank_le_of_cV fun x hx => ⟨hL x hx.1, P.s3_cV_mem_W₁ℂ hx.2⟩
  have hc₁ := hconj L₁ hcL₁
  have hc₂ := hconj L₂ hcL₂
  rw [h11, h12] at hsplit₁ hc₁
  rw [h21, h22] at hsplit₂ hc₂
  omega


/-- (3.2.1): `V^{1,0} ∩ W_{2,ℂ} = (V^{1,0} ∩ W_{1,ℂ})^⊥ ∩ W_{2,ℂ}`, by the proof of
Lemma 3.2.1. -/
theorem s3_eq3_2_1 (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hcomm : I * P.fR hW = P.fR hW * I) (hI : IsComplexStructure I) (hν : P.nu hW I = 2 * n)
    (hiso : ∀ a b, pairing ℂ n (complexifyV n I a) (complexifyV n I b) = pairing ℂ n a b) :
    V10 n I ⊓ P.W₂ℂ = (pairing ℂ n).orthogonal (V10 n I ⊓ P.W₁ℂ) ⊓ P.W₂ℂ := by
  obtain ⟨hA, hB, hC, -⟩ := P.s3_core hW I hcomm hI hν
  set Ic := complexifyV n I with hIc
  set fc := complexifyV n (P.fR hW) with hfc
  have hIfc : Ic * fc = fc * Ic := by
    rw [hIc, hfc, s3_complexifyV_eq, s3_complexifyV_eq, ← s3_ext_mul, hcomm, s3_ext_mul]
  -- `V^{1,0}`, `V^{0,1}` and `W_{1,ℂ}` are isotropic
  have hiso' : ∀ (μ : ℂ), μ * μ ≠ 1 → ∀ a ∈ Module.End.eigenspace Ic μ,
      ∀ b ∈ Module.End.eigenspace Ic μ, pairing ℂ n a b = 0 := by
    intro μ hμ a ha b hb
    rw [Module.End.mem_eigenspace_iff] at ha hb
    have h := hiso a b
    rw [ha, hb, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc]
      at h
    have : (μ * μ - 1) * pairing ℂ n a b = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ)
  have hV10iso := hiso' Complex.I (by rw [Complex.I_mul_I]; norm_num)
  have hW₁iso : ∀ a ∈ P.W₁ℂ, ∀ b ∈ P.W₁ℂ, pairing ℂ n a b = 0 := fun a ha b hb =>
    s3_pairing_of_mem_ann P.s3_bcS_u₁_ne_zero (P.s3_W₁ℂ_le_ann ha) (P.s3_W₁ℂ_le_ann hb)
  -- `V^{1,0} = (V^{1,0} ∩ W_{1,ℂ}) ⊕ (V^{1,0} ∩ W_{2,ℂ})`
  have hV10split : V10 n I ⊓ P.W₁ℂ ⊔ V10 n I ⊓ P.W₂ℂ = V10 n I :=
    P.s3_split_sup hW _ fun x hx => s3_mem_eigenspace_of_comm hIfc hx
  have hV10dim : Module.finrank ℂ (V10 n I) = 2 * n := by
    have h := P.s3_finrank_split hW (V10 n I) fun x hx => s3_mem_eigenspace_of_comm hIfc hx
    rw [hA, hB] at h
    omega
  have hdisj : V10 n I ⊓ (V01 n I ⊓ P.W₁ℂ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : Ic x = Complex.I • x := Module.End.mem_eigenspace_iff.mp hx.1
    have h2 : Ic x = -Complex.I • x := Module.End.mem_eigenspace_iff.mp hx.2.1
    have : (2 * Complex.I) • x = 0 := by
      have e : (2 * Complex.I) • x = Complex.I • x - (-Complex.I) • x := by module
      rw [e, ← h1, ← h2, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  -- `(V^{1,0} ∩ W_{1,ℂ})^⊥ = V^{1,0} ⊕ (V^{0,1} ∩ W_{1,ℂ})`: inclusion and dimension `3n`
  set R := V10 n I ⊔ V01 n I ⊓ P.W₁ℂ with hRdef
  have hR : R = (pairing ℂ n).orthogonal (V10 n I ⊓ P.W₁ℂ) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine sup_le (fun x hx y hy => hV10iso y hy.1 x hx) (fun x hx y hy => hW₁iso y hy.2 x hx.2)
    · rw [LinearMap.BilinForm.finrank_orthogonal s3_pairing_nondegenerate, hA, s3_finrank_V]
      have := Submodule.finrank_sup_add_finrank_inf_eq (V10 n I) (V01 n I ⊓ P.W₁ℂ)
      rw [hdisj, finrank_bot, add_zero, hV10dim, hC] at this
      rw [hRdef, this]
      omega
  rw [← hR]
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Submodule.mem_sup_left h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp h1
    rw [← hV10split] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
    have h0 : a₁ + c = 0 := by
      apply (Submodule.disjoint_def.mp (P.s3_isCompl_ℂ hW).disjoint)
      · exact Submodule.add_mem _ ha₁.2 hc.2
      · have := Submodule.sub_mem _ h2 ha₂.2
        rwa [show a₁ + a₂ + c - a₂ = a₁ + c by abel] at this
    rw [show a₁ + a₂ + c = (a₁ + c) + a₂ by abel, h0, zero_add]
    exact ha₂

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
  obtain ⟨g, hg, rfl⟩ := hIP
  exact P.s3_core hP.isCompl _ (P.rho_spinPR_comm_fR J hP g hg) hI hν

/-- **(3.2.1)** (`eq-complex-structure-is-determined-by`), Lemma 3.2.1 continued:
`V^{1,0} ∩ W_{2,ℂ} = (V^{1,0} ∩ W_{1,ℂ})^⊥ ∩ W_{2,ℂ}`, where `(·)^⊥` is the subspace orthogonal with
respect to the pairing `(·,·)_V` (extended to `V_ℂ`). -/
theorem equation3_2_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I)
    (hI : IsComplexStructure I) (hν : P.nu hP.isCompl I = 2 * n) :
    V10 n I ⊓ P.W₂ℂ = (pairing ℂ n).orthogonal (V10 n I ⊓ P.W₁ℂ) ⊓ P.W₂ℂ := by
  obtain ⟨g, hg, rfl⟩ := hIP
  refine P.s3_eq3_2_1 hP.isCompl _ (P.rho_spinPR_comm_fR J hP g hg) hI hν fun a b => ?_
  -- `I_ℂ = ρ(g_ℂ)` is an isometry
  rw [s3_complexifyV_eq, s3_ext_rho ℝ ℂ g]
  exact s3_pairing_rho _ a b

/-! ## Corollary 3.2.2: the plane of Hodge–Weil classes -/

/-- **The rational plane of Hodge–Weil classes** `ĤW_P ⊆ ⋀^{2n} V_ℚ` (§1.2, Corollary 3.2.2,
Lemma 4.0.3): the rational classes whose image in `⋀• V_K` lies in `⋀^{2n} W₁ + ⋀^{2n} W₂`. -/
noncomputable def KSecant.hwPlane (P : KSecant n d) : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ((topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n)).restrictScalars ℚ).comap (bcExt ℚ (Kd d) n).toLinearMap

/-! ### Helpers for Corollary 3.2.2 -/

section S3Ext

/-- An alternating map on a free module of rank `k` is determined by its value on a basis. -/
theorem s3_alternating_eq_det_smul {R N₁ N₂ : Type*} [CommRing R] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] {k : ℕ} (f : N₁ [⋀^Fin k]→ₗ[R] N₂)
    (e : Module.Basis (Fin k) R N₁) (v : Fin k → N₁) : f v = e.det v • f e := by
  have : f = e.det.smulRight (f e) := by
    refine e.ext_alternating fun w hw => ?_
    let σ : Equiv.Perm (Fin k) := Equiv.ofBijective w (Finite.injective_iff_bijective.1 hw)
    change f (e ∘ σ) = (e.det.smulRight (f e)) (e ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self, AlternatingMap.smulRight_apply]
  conv_lhs => rw [this]
  rfl

/-- The wedge product of linearly independent vectors is nonzero. -/
theorem s3_ιMulti_ne_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {k : ℕ}
    {v : Fin k → M} (hv : LinearIndependent K v) : ExteriorAlgebra.ιMulti K k v ≠ 0 := by
  have hinj : LinearMap.ker (Fintype.linearCombination K v) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have h := (Fintype.linearIndependent_iff.mp hv) (a - b) (by
      simp only [Fintype.linearCombination_apply] at hab
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hab, sub_self])
    funext i
    exact sub_eq_zero.mp (h i)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let f : Fin k → Module.Dual K M := fun j => (LinearMap.proj j) ∘ₗ ψ
  have hf : ∀ i j, f j (v i) = if i = j then 1 else 0 := by
    intro i j
    have : ψ (v i) = Pi.single i 1 := by
      have h := LinearMap.congr_fun hψ (Pi.single i 1)
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Fintype.linearCombination_apply_single,
        one_smul] at h
      exact h
    simp only [f, LinearMap.coe_comp, Function.comp_apply, this, LinearMap.coe_proj,
      Function.eval, Pi.single_apply, eq_comm]
  intro h0
  have h1 := exteriorPower.pairingDual_ιMulti_ιMulti f v
  have h2 : exteriorPower.ιMulti K k v = 0 := Subtype.ext (by
    rw [exteriorPower.ιMulti_apply_coe]; exact h0)
  rw [h2, map_zero] at h1
  have h3 : (Matrix.of fun i j => f j (v i)) = 1 := by
    ext i j; simp [hf, Matrix.one_apply]
  rw [h3, Matrix.det_one] at h1
  exact zero_ne_one h1

/-- The wedge of `k` vectors in the span of `k` independent vectors `c` is a multiple of the
wedge of `c`. -/
theorem s3_ιMulti_mem_span {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {k : ℕ}
    {c : Fin k → M} (hc : LinearIndependent K c) {v : Fin k → M}
    (hv : ∀ i, v i ∈ Submodule.span K (Set.range c)) :
    ExteriorAlgebra.ιMulti K k v ∈ K ∙ ExteriorAlgebra.ιMulti K k c := by
  let e := Module.Basis.span hc
  let g := (ExteriorAlgebra.ιMulti K k (M := M)).compLinearMap
    (Submodule.span K (Set.range c)).subtype
  have h := s3_alternating_eq_det_smul g e (fun i => ⟨v i, hv i⟩)
  have h1 : g (fun i => ⟨v i, hv i⟩) = ExteriorAlgebra.ιMulti K k v := rfl
  have h2 : g e = ExteriorAlgebra.ιMulti K k c := by
    show ExteriorAlgebra.ιMulti K k (fun i => (e i : M)) = _
    congr 1
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hc i)
  rw [h1, h2] at h
  rw [Submodule.mem_span_singleton]
  exact ⟨_, h.symm⟩

/-- `⋀^k W` is the line spanned by the wedge of a basis `c` of `W`. -/
theorem s3_topWedge_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {k : ℕ}
    {c : Fin k → M} (hc : LinearIndependent K c) :
    topWedge (Submodule.span K (Set.range c)) k = K ∙ ExteriorAlgebra.ιMulti K k c := by
  apply le_antisymm
  · rw [topWedge, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact s3_ιMulti_mem_span hc hv
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨c, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩

/-- If `W = A ⊕ B` with `dim A = p`, `dim B = q`, the wedge of `p + q` vectors of `W` lies in
`⋀^p A' ∧ ⋀^q B'` for `A ≤ A'`, `B ≤ B'`. -/
theorem s3_ιMulti_mem_pqPiece {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {A B A' B' : Submodule K M} (hAB : A ⊓ B = ⊥) {p q : ℕ}
    (hA : Module.finrank K A = p) (hB : Module.finrank K B = q) (hA' : A ≤ A') (hB' : B ≤ B')
    {k : ℕ} (hk : k = p + q) (v : Fin k → M) (hv : ∀ i, v i ∈ A ⊔ B) :
    ExteriorAlgebra.ιMulti K k v ∈ pqPiece A' B' p q := by
  subst hk
  set a : Fin p → M := fun i => (Module.finBasisOfFinrankEq K A hA i : M)
  set b : Fin q → M := fun i => (Module.finBasisOfFinrankEq K B hB i : M)
  have ha : LinearIndependent K a :=
    (Module.finBasisOfFinrankEq K A hA).linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hb : LinearIndependent K b :=
    (Module.finBasisOfFinrankEq K B hB).linearIndependent.map' B.subtype (Submodule.ker_subtype _)
  have hspa : Submodule.span K (Set.range a) = A := by
    have : Set.range a = A.subtype '' Set.range (Module.finBasisOfFinrankEq K A hA) := by
      ext x; simp [a]
    rw [this, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspb : Submodule.span K (Set.range b) = B := by
    have : Set.range b = B.subtype '' Set.range (Module.finBasisOfFinrankEq K B hB) := by
      ext x; simp [b]
    rw [this, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  have happ : Fin.append a b = Sum.elim a b ∘ finSumFinEquiv.symm := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hc : LinearIndependent K (Fin.append a b) := by
    have h := ha.sum_type hb (by rw [hspa, hspb, disjoint_iff]; exact hAB)
    rw [happ]
    exact h.comp _ finSumFinEquiv.symm.injective
  have hspc : Submodule.span K (Set.range (Fin.append a b)) = A ⊔ B := by
    rw [happ, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Set.Sum.elim_range,
      Submodule.span_union, hspa, hspb]
  have h := s3_ιMulti_mem_span hc (v := v) (fun i => hspc ▸ hv i)
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp h
  rw [← hc', ← ExteriorAlgebra.ιMulti_mul_ιMulti]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, b, fun i => hA' ?_, fun j => hB' ?_, rfl⟩)
  · rw [← hspa]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [← hspb]; exact Submodule.subset_span ⟨j, rfl⟩

end S3Ext

section S3BcExt

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

theorem s3_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) :=
  ExteriorAlgebra.lift_ι_apply F _ _ v

theorem s3_bcExt_ιMulti {k : ℕ} (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcV F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact s3_bcExt_ι F F' (v i)

theorem s3_bcExt_basisExt (K : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n K) = basisExt F' n K := by
  simp only [basisExt, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [s3_bcExt_ιMulti]
  congr 1
  funext i
  simp [s3_bcV_basisV]

theorem s3_bcExt_repr (s : ExteriorAlgebra F (V F n)) (K) :
    (basisExt F' n).repr (bcExt F F' n s) K = algebraMap F F' ((basisExt F n).repr s K) :=
  s3_repr_map_basis (basisExt F n) (basisExt F' n) (bcExt F F' n).toLinearMap
    (s3_bcExt_basisExt F F') s K

theorem s3_bcExt_injective : Function.Injective (bcExt F F' n) :=
  s3_injective_map_basis (basisExt F n) (basisExt F' n) (bcExt F F' n).toLinearMap
    (s3_bcExt_basisExt F F')

variable {F'}

theorem s3_conjExt_eq (c : F' ≃+* F') (s : ExteriorAlgebra F' (V F' n)) :
    conjExt c n s = ∑ K, c ((basisExt F' n).repr s K) • basisExt F' n K := rfl

theorem s3_conjExt_smul (c : F' ≃+* F') (a : F') (s : ExteriorAlgebra F' (V F' n)) :
    conjExt c n (a • s) = c a • conjExt c n s := by
  simp only [s3_conjExt_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    smul_smul]

theorem s3_conjExt_repr (c : F' ≃+* F') (s : ExteriorAlgebra F' (V F' n)) (K) :
    (basisExt F' n).repr (conjExt c n s) K = c ((basisExt F' n).repr s K) := by
  rw [s3_conjExt_eq, (basisExt F' n).repr_sum_self]

theorem s3_conjExt_bcExt (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (t : ExteriorAlgebra F (V F n)) : conjExt c n (bcExt F F' n t) = bcExt F F' n t := by
  rw [s3_conjExt_eq]
  simp only [s3_bcExt_repr, hc]
  conv_rhs => rw [← (basisExt F' n).sum_repr (bcExt F F' n t)]
  simp only [s3_bcExt_repr]

theorem s3_conjExt_ι (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (v : V F' n) : conjExt c n (ExteriorAlgebra.ι F' v) = ExteriorAlgebra.ι F' (conjV c n v) := by
  have h1 : ExteriorAlgebra.ι F' v = ∑ j, (basisV F' n).repr v j •
      bcExt F F' n (ExteriorAlgebra.ι F (basisV F n j)) := by
    conv_lhs => rw [← (basisV F' n).sum_repr v]
    simp only [map_sum, map_smul, s3_bcExt_ι, s3_bcV_basisV]
  rw [h1, s3_conjV_eq c, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s3_conjExt_smul, s3_conjExt_bcExt F c hc, s3_bcExt_ι, s3_bcV_basisV, map_smul]

theorem s3_conjExt_ιMulti (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    {k : ℕ} (v : Fin k → V F' n) :
    conjExt c n (ExteriorAlgebra.ιMulti F' k v) = ExteriorAlgebra.ιMulti F' k (conjV c n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact s3_conjExt_ι F c hc (v i)

variable (F')

/-- Change of coefficients preserves the degree. -/
theorem s3_bcExt_mem_exteriorPower {j : ℕ} {x : ExteriorAlgebra F (V F n)}
    (hx : x ∈ ⋀[F]^j (V F n)) : bcExt F F' n x ∈ ⋀[F']^j (V F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [s3_bcExt_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' j ⟨_, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a y _ hy =>
    rw [map_smul, ← algebraMap_smul F']
    exact Submodule.smul_mem _ _ hy

/-- A rational class whose image is homogeneous of degree `k` has degree `k`. -/
theorem s3_mem_exteriorPower_of_bcExt {k : ℕ} {α : ExteriorAlgebra F (V F n)}
    (h : bcExt F F' n α ∈ ⋀[F']^k (V F' n)) : α ∈ ⋀[F]^k (V F n) := by
  classical
  have hcomm : ∀ (x : ExteriorAlgebra F (V F n)) (j : ℕ),
      bcExt F F' n (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x j) =
        (DirectSum.decompose (fun i : ℕ => ⋀[F']^i (V F' n)) (bcExt F F' n x) j : _) := by
    intro x
    induction x using DirectSum.Decomposition.inductionOn (ℳ := fun i : ℕ => ⋀[F]^i (V F n)) with
    | zero => intro j; simp
    | @homogeneous i m =>
      intro j
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) m.2,
          DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F']^i (V F' n))
            (s3_bcExt_mem_exteriorPower F F' m.2)]
      · rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) m.2 hij,
          DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F']^i (V F' n))
            (s3_bcExt_mem_exteriorPower F F' m.2) hij, map_zero]
    | add a b ha hb =>
      intro j
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, map_add, ha, hb,
        map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  have hz : ∀ j, j ≠ k →
      (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) α j : ExteriorAlgebra F (V F n)) = 0 := by
    intro j hj
    apply s3_bcExt_injective F F'
    rw [hcomm, DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F']^i (V F' n)) h (Ne.symm hj),
      map_zero]
  have hα : α = DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) α k := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) α]
    by_cases hk : k ∈ (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) α).support
    · rw [Finset.sum_eq_single k (fun j _ hj => hz j hj) (fun h' => absurd hk h')]
    · rw [Finset.sum_eq_zero (fun j hj => hz j (fun h' => hk (h' ▸ hj)))]
      rw [DFinsupp.notMem_support_iff] at hk
      rw [hk]; rfl
  rw [hα]
  exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) α k).2

end S3BcExt


section S3HW

variable {n : ℕ} {d : ℚ}

theorem s3_conjExt_conjExt (t : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    conjExt (Kd.σ d) n (conjExt (Kd.σ d) n t) = t := by
  rw [s3_conjExt_eq (n := n) (Kd.σ d) (conjExt (Kd.σ d) n t)]
  conv_rhs => rw [← (basisExt (Kd d) n).sum_repr t]
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [s3_conjExt_repr, s3_σ_σ]

/-- `σ`-fixed classes of `⋀• V_K` are rational. -/
theorem s3_exists_bcExt_of_conjExt_eq (hd : 0 < d) (t : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (ht : conjExt (Kd.σ d) n t = t) : ∃ α, bcExt ℚ (Kd d) n α = t := by
  refine ⟨∑ K, Kd.ratPart d ((basisExt (Kd d) n).repr t K) • basisExt ℚ n K, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (basisExt (Kd d) n).sum_repr t]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s3_bcExt_basisExt ℚ (Kd d), ← algebraMap_smul (Kd d)]
  congr 1
  have hK : Kd.σ d ((basisExt (Kd d) n).repr t K) = (basisExt (Kd d) n).repr t K := by
    rw [← s3_conjExt_repr, ht]
  exact (s3_eq_algebraMap_of_σ_eq hd _ hK).symm

end S3HW

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- A basis of `W₁`. -/
noncomputable def s3_e₁ (P : KSecant n d) : Module.Basis (Fin (2 * n)) (Kd d) P.W₁ :=
  Module.finBasisOfFinrankEq (Kd d) P.W₁ P.isPure.2.2

/-- A basis `b₁` of `W₁`, as vectors of `V_K`. -/
noncomputable def s3_b₁ (P : KSecant n d) : Fin (2 * n) → V (Kd d) n :=
  fun i => (P.s3_e₁ i : V (Kd d) n)

theorem s3_b₁_li : LinearIndependent (Kd d) P.s3_b₁ :=
  P.s3_e₁.linearIndependent.map' P.W₁.subtype (Submodule.ker_subtype _)

theorem s3_span_b₁ : Submodule.span (Kd d) (Set.range P.s3_b₁) = P.W₁ := by
  have : Set.range P.s3_b₁ = P.W₁.subtype '' Set.range P.s3_e₁ := by
    ext x; simp [s3_b₁]
  rw [this, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem s3_b₁_mem (i : Fin (2 * n)) : P.s3_b₁ i ∈ P.W₁ := by
  rw [← P.s3_span_b₁]; exact Submodule.subset_span ⟨i, rfl⟩

theorem s3_span_b₂ (hW : IsCompl P.W₁ P.W₂) :
    Submodule.span (Kd d) (Set.range (σV n d ∘ P.s3_b₁)) = P.W₂ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact P.s3_σV_mem_W₂ (P.s3_b₁_mem i)
  · rw [finrank_span_eq_card (s3_linearIndependent_σV P.s3_b₁_li), Fintype.card_fin]
    exact (P.s3_isPure₂ hW).2.2.symm

/-- `ω₁ = ⋀^{2n} b₁`, spanning `⋀^{2n} W₁`. -/
noncomputable def s3_ω₁ : ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  ExteriorAlgebra.ιMulti (Kd d) (2 * n) P.s3_b₁

/-- `ω₂ = σ(ω₁)`, spanning `⋀^{2n} W₂`. -/
noncomputable def s3_ω₂ : ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  ExteriorAlgebra.ιMulti (Kd d) (2 * n) (σV n d ∘ P.s3_b₁)

theorem s3_topWedge₁ : topWedge P.W₁ (2 * n) = (Kd d) ∙ P.s3_ω₁ := by
  conv_lhs => rw [← P.s3_span_b₁]
  exact s3_topWedge_eq P.s3_b₁_li

theorem s3_topWedge₂ (hW : IsCompl P.W₁ P.W₂) : topWedge P.W₂ (2 * n) = (Kd d) ∙ P.s3_ω₂ := by
  conv_lhs => rw [← P.s3_span_b₂ hW]
  exact s3_topWedge_eq (s3_linearIndependent_σV P.s3_b₁_li)

theorem s3_conjExt_ω₁ : conjExt (Kd.σ d) n P.s3_ω₁ = P.s3_ω₂ :=
  s3_conjExt_ιMulti ℚ (Kd.σ d) s3_σhc _

theorem s3_conjExt_ω₂ : conjExt (Kd.σ d) n P.s3_ω₂ = P.s3_ω₁ := by
  rw [← P.s3_conjExt_ω₁, s3_conjExt_conjExt]

/-- `⋀^{2n} W₁ ≠ ⋀^{2n} W₂`. -/
theorem s3_ω_li (hW : IsCompl P.W₁ P.W₂) :
    LinearIndependent (Kd d) ![P.s3_ω₁, P.s3_ω₂] := by
  have hn := s3_n_pos P
  rw [LinearIndependent.pair_iff]
  intro s t hst
  set w := P.s3_b₁ ⟨0, by omega⟩ with hw
  have hcons : ∀ v : Fin (2 * n) → V (Kd d) n, ExteriorAlgebra.ι (Kd d) w *
      ExteriorAlgebra.ιMulti (Kd d) (2 * n) v =
        ExteriorAlgebra.ιMulti (Kd d) (2 * n + 1) (Fin.cons w v) := by
    intro v
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  have h1 : ExteriorAlgebra.ι (Kd d) w * P.s3_ω₁ = 0 := by
    rw [s3_ω₁, hcons]
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hinj
    have h0 : (Fin.cons w P.s3_b₁ : Fin (2 * n + 1) → V (Kd d) n) 0 =
        (Fin.cons w P.s3_b₁ : Fin (2 * n + 1) → V (Kd d) n) (Fin.succ ⟨0, by omega⟩) := by
      rw [Fin.cons_zero, Fin.cons_succ]
    exact Fin.succ_ne_zero _ (hinj h0).symm
  have h2 : ExteriorAlgebra.ι (Kd d) w * P.s3_ω₂ ≠ 0 := by
    rw [s3_ω₂, hcons]
    apply s3_ιMulti_ne_zero
    rw [linearIndependent_finCons]
    refine ⟨s3_linearIndependent_σV P.s3_b₁_li, ?_⟩
    rw [P.s3_span_b₂ hW]
    intro hw2
    have h0 : w = 0 := (Submodule.disjoint_def.mp hW.disjoint) w (P.s3_b₁_mem _) hw2
    exact P.s3_b₁_li.ne_zero _ h0
  have h3 := congrArg (fun z => ExteriorAlgebra.ι (Kd d) w * z) hst
  simp only [mul_add, mul_smul_comm, h1, smul_zero, zero_add, mul_zero] at h3
  have ht : t = 0 := (smul_eq_zero.mp h3).resolve_right h2
  rw [ht, zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right (s3_ιMulti_ne_zero P.s3_b₁_li), ht⟩


theorem s3_X_eq (hW : IsCompl P.W₁ P.W₂) :
    topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) =
      Submodule.span (Kd d) {P.s3_ω₁, P.s3_ω₂} := by
  rw [P.s3_topWedge₁, P.s3_topWedge₂ hW, Submodule.span_insert]

theorem s3_mem_hwPlane_iff (α : ExteriorAlgebra ℚ (V ℚ n)) :
    α ∈ P.hwPlane ↔ bcExt ℚ (Kd d) n α ∈ topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) :=
  Iff.rfl

/-- The rational points `ω₁ + ω₂` and `√-d (ω₁ - ω₂)` of the plane. -/
theorem s3_exists_α : ∃ α₁ α₂ : ExteriorAlgebra ℚ (V ℚ n),
    bcExt ℚ (Kd d) n α₁ = P.s3_ω₁ + P.s3_ω₂ ∧
      bcExt ℚ (Kd d) n α₂ = Kd.sqrtNeg d • (P.s3_ω₁ - P.s3_ω₂) := by
  have hd := s3_d_pos P
  obtain ⟨α₁, h₁⟩ := s3_exists_bcExt_of_conjExt_eq hd (P.s3_ω₁ + P.s3_ω₂) (by
    rw [map_add, P.s3_conjExt_ω₁, P.s3_conjExt_ω₂, add_comm])
  obtain ⟨α₂, h₂⟩ := s3_exists_bcExt_of_conjExt_eq hd (Kd.sqrtNeg d • (P.s3_ω₁ - P.s3_ω₂)) (by
    rw [s3_conjExt_smul, map_sub, P.s3_conjExt_ω₁, P.s3_conjExt_ω₂, s3_σ_sqrtNeg, neg_smul,
      ← smul_neg, neg_sub])
  exact ⟨α₁, α₂, h₁, h₂⟩

/-- `ĤW_P` is spanned by `α₁`, `α₂`. -/
theorem s3_hwPlane_eq (hW : IsCompl P.W₁ P.W₂) {α₁ α₂ : ExteriorAlgebra ℚ (V ℚ n)}
    (h₁ : bcExt ℚ (Kd d) n α₁ = P.s3_ω₁ + P.s3_ω₂)
    (h₂ : bcExt ℚ (Kd d) n α₂ = Kd.sqrtNeg d • (P.s3_ω₁ - P.s3_ω₂)) :
    P.hwPlane = Submodule.span ℚ (Set.range ![α₁, α₂]) := by
  have hd := s3_d_pos P
  have hmem₁ : P.s3_ω₁ ∈ Submodule.span (Kd d) {P.s3_ω₁, P.s3_ω₂} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hmem₂ : P.s3_ω₂ ∈ Submodule.span (Kd d) {P.s3_ω₁, P.s3_ω₂} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · intro α hα
    rw [P.s3_mem_hwPlane_iff, P.s3_X_eq hW, Submodule.mem_span_pair] at hα
    obtain ⟨a, b, hab⟩ := hα
    -- `bcExt α` is `σ`-fixed
    have hfix := s3_conjExt_bcExt ℚ (Kd.σ d) s3_σhc α
    rw [← hab, map_add, s3_conjExt_smul, s3_conjExt_smul, P.s3_conjExt_ω₁, P.s3_conjExt_ω₂]
      at hfix
    have hb : b = Kd.σ d a := by
      have h := (LinearIndependent.pair_iff.mp (P.s3_ω_li hW)) (Kd.σ d b - a) (Kd.σ d a - b) (by
        have e : (Kd.σ d b - a) • P.s3_ω₁ + (Kd.σ d a - b) • P.s3_ω₂ =
            (Kd.σ d a • P.s3_ω₂ + Kd.σ d b • P.s3_ω₁) - (a • P.s3_ω₁ + b • P.s3_ω₂) := by
          module
        rw [e, hfix, sub_self])
      rw [← sub_eq_zero.mp h.2]
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℚ, a = algebraMap ℚ (Kd d) p + algebraMap ℚ (Kd d) q * Kd.sqrtNeg d :=
      ⟨_, _, Kd.eq_ratPart_add_sqrtNegCoeff hd a⟩
    have hα' : α = p • α₁ + q • α₂ := by
      apply s3_bcExt_injective ℚ (Kd d)
      rw [map_add, map_smul, map_smul, h₁, h₂, ← hab, hb, hpq]
      simp only [map_add, map_mul, s3_σ_algebraMap, s3_σ_sqrtNeg, ← algebraMap_smul (Kd d) p,
        ← algebraMap_smul (Kd d) q, smul_add, smul_sub, smul_smul, add_smul, mul_neg, neg_smul]
      abel
    rw [hα']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, P.s3_mem_hwPlane_iff, P.s3_X_eq hW]
    fin_cases i
    · show bcExt ℚ (Kd d) n α₁ ∈ _
      rw [h₁]; exact Submodule.add_mem _ hmem₁ hmem₂
    · show bcExt ℚ (Kd d) n α₂ ∈ _
      rw [h₂]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem₁ hmem₂)

theorem s3_α_li (hW : IsCompl P.W₁ P.W₂) {α₁ α₂ : ExteriorAlgebra ℚ (V ℚ n)}
    (h₁ : bcExt ℚ (Kd d) n α₁ = P.s3_ω₁ + P.s3_ω₂)
    (h₂ : bcExt ℚ (Kd d) n α₂ = Kd.sqrtNeg d • (P.s3_ω₁ - P.s3_ω₂)) :
    LinearIndependent ℚ ![α₁, α₂] := by
  have hd := s3_d_pos P
  rw [LinearIndependent.pair_iff]
  intro p q hpq
  have h := congrArg (bcExt ℚ (Kd d) n) hpq
  rw [map_add, map_smul, map_smul, h₁, h₂, map_zero] at h
  have h' := (LinearIndependent.pair_iff.mp (P.s3_ω_li hW))
    (algebraMap ℚ (Kd d) p + algebraMap ℚ (Kd d) q * Kd.sqrtNeg d)
    (algebraMap ℚ (Kd d) p - algebraMap ℚ (Kd d) q * Kd.sqrtNeg d) (by
      rw [← h]
      simp only [← algebraMap_smul (Kd d) p, ← algebraMap_smul (Kd d) q, smul_add, smul_sub,
        smul_smul, add_smul, sub_smul]
      abel)
  have hp : algebraMap ℚ (Kd d) (2 * p) = 0 := by
    rw [map_mul, map_ofNat]; linear_combination h'.1 + h'.2
  have hq : algebraMap ℚ (Kd d) (2 * q) * Kd.sqrtNeg d = 0 := by
    rw [map_mul, map_ofNat]; linear_combination h'.1 - h'.2
  rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at hp
  rcases mul_eq_zero.mp hq with hq | hq
  · rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at hq
    constructor <;> linarith
  · exact absurd hq (s3_sqrtNeg_ne_zero hd)


end KSecant

theorem s3_bcExt_trans (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
    [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F'']
    {n : ℕ} (s : ExteriorAlgebra F (V F n)) :
    bcExt F' F'' n (bcExt F F' n s) = bcExt F F'' n s := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F'
      (ExteriorAlgebra F' (V F' n)), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι w =>
    rw [show (ι (0 : QuadraticForm F (V F n)) w : ExteriorAlgebra F (V F n)) =
      ExteriorAlgebra.ι F w from rfl, s3_bcExt_ι, s3_bcExt_ι, s3_bcExt_ι, s3_bcV_trans]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- An `I`-stable subspace splits into its `(1,0)` and `(0,1)` parts. -/
theorem s3_I_split {n : ℕ} (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (W : Submodule ℂ (V ℂ n)) (hW : ∀ x ∈ W, complexifyV n I x ∈ W) :
    V10 n I ⊓ W ⊔ V01 n I ⊓ W = W := by
  have hII : complexifyV n I * complexifyV n I = -1 := by
    rw [s3_complexifyV_eq, ← s3_ext_mul, hI, s3_ext_neg, s3_ext_one]
  have hII' : ∀ x, complexifyV n I (complexifyV n I x) = -x := fun x => by
    rw [← Module.End.mul_apply, hII]; rfl
  refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
  have e : x = (2 : ℂ)⁻¹ • (x - Complex.I • complexifyV n I x) +
      (2 : ℂ)⁻¹ • (x + Complex.I • complexifyV n I x) := by
    rw [← smul_add, sub_add_add_cancel, ← two_smul ℂ x, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  rw [e]
  refine Submodule.add_mem_sup ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, V10, Module.End.mem_eigenspace_iff]
    have h1 : complexifyV n I ((2 : ℂ)⁻¹ • (x - Complex.I • complexifyV n I x)) =
        (2 : ℂ)⁻¹ • (complexifyV n I x + Complex.I • x) := by
      rw [map_smul, map_sub, map_smul, hII', smul_neg, sub_neg_eq_add]
    have h2 : Complex.I • ((2 : ℂ)⁻¹ • (x - Complex.I • complexifyV n I x)) =
        (2 : ℂ)⁻¹ • (complexifyV n I x + Complex.I • x) := by
      rw [smul_comm, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
    rw [h1, h2]
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hW x hx)))
  · rw [SetLike.mem_coe, V01, Module.End.mem_eigenspace_iff]
    have h1 : complexifyV n I ((2 : ℂ)⁻¹ • (x + Complex.I • complexifyV n I x)) =
        (2 : ℂ)⁻¹ • (complexifyV n I x - Complex.I • x) := by
      rw [map_smul, map_add, map_smul, hII', smul_neg, ← sub_eq_add_neg]
    have h2 : (-Complex.I) • ((2 : ℂ)⁻¹ • (x + Complex.I • complexifyV n I x)) =
        (2 : ℂ)⁻¹ • (complexifyV n I x - Complex.I • x) := by
      rw [smul_comm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [h1, h2]
  · exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx (Submodule.smul_mem _ _ (hW x hx)))

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- `W_{1,ℂ}` is the `√-d`-eigenspace of `f_ℂ`. -/
theorem s3_mem_W₁ℂ_of_eigen (hW : IsCompl P.W₁ P.W₂) {x : V ℂ n}
    (hx : complexifyV n (P.fR hW) x = ((Kd.sqrtNeg d : Kd d) : ℂ) • x) : x ∈ P.W₁ℂ := by
  have hs : ((Kd.sqrtNeg d : Kd d) : ℂ) ≠ 0 := by exact_mod_cast s3_sqrtNeg_ne_zero (s3_d_pos P)
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
    Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
  rw [map_add, P.s3_fℂ_W₁ hW hx₁, P.s3_fℂ_W₂ hW hx₂] at hx
  have : (2 * ((Kd.sqrtNeg d : Kd d) : ℂ)) • x₂ = 0 := by
    have e : (2 * ((Kd.sqrtNeg d : Kd d) : ℂ)) • x₂ =
        ((Kd.sqrtNeg d : Kd d) : ℂ) • (x₁ + x₂) -
          (((Kd.sqrtNeg d : Kd d) : ℂ) • x₁ + -((Kd.sqrtNeg d : Kd d) : ℂ) • x₂) := by
      module
    rw [e, ← hx, sub_self]
  have h0 := (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs)
  rw [h0, add_zero]; exact hx₁

theorem s3_mem_W₂ℂ_of_eigen (hW : IsCompl P.W₁ P.W₂) {x : V ℂ n}
    (hx : complexifyV n (P.fR hW) x = -((Kd.sqrtNeg d : Kd d) : ℂ) • x) : x ∈ P.W₂ℂ := by
  have hs : ((Kd.sqrtNeg d : Kd d) : ℂ) ≠ 0 := by exact_mod_cast s3_sqrtNeg_ne_zero (s3_d_pos P)
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
    Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
  rw [map_add, P.s3_fℂ_W₁ hW hx₁, P.s3_fℂ_W₂ hW hx₂] at hx
  have : (2 * ((Kd.sqrtNeg d : Kd d) : ℂ)) • x₁ = 0 := by
    have e : (2 * ((Kd.sqrtNeg d : Kd d) : ℂ)) • x₁ =
        (((Kd.sqrtNeg d : Kd d) : ℂ) • x₁ + -((Kd.sqrtNeg d : Kd d) : ℂ) • x₂) -
          (-((Kd.sqrtNeg d : Kd d) : ℂ)) • (x₁ + x₂) := by
      module
    rw [e, hx, sub_self]
  have h0 := (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs)
  rw [h0, zero_add]; exact hx₂

/-- `W_{i,ℂ}` is `I`-stable when `I` commutes with `f`. -/
theorem s3_W₁ℂ_I_stable (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hcomm : I * P.fR hW = P.fR hW * I) {x : V ℂ n} (hx : x ∈ P.W₁ℂ) :
    complexifyV n I x ∈ P.W₁ℂ := by
  apply P.s3_mem_W₁ℂ_of_eigen hW
  rw [← Module.End.mul_apply, s3_complexifyV_eq, s3_complexifyV_eq, ← s3_ext_mul, ← hcomm,
    s3_ext_mul, Module.End.mul_apply, ← s3_complexifyV_eq, ← s3_complexifyV_eq,
    P.s3_fℂ_W₁ hW hx, map_smul]

theorem s3_W₂ℂ_I_stable (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hcomm : I * P.fR hW = P.fR hW * I) {x : V ℂ n} (hx : x ∈ P.W₂ℂ) :
    complexifyV n I x ∈ P.W₂ℂ := by
  apply P.s3_mem_W₂ℂ_of_eigen hW
  rw [← Module.End.mul_apply, s3_complexifyV_eq, s3_complexifyV_eq, ← s3_ext_mul, ← hcomm,
    s3_ext_mul, Module.End.mul_apply, ← s3_complexifyV_eq, ← s3_complexifyV_eq,
    P.s3_fℂ_W₂ hW hx, map_smul]


end KSecant

/-- `ĤW_P` is a plane (`⋀^{2n} W₁ ≠ ⋀^{2n} W₂` are conjugate lines). -/
theorem KSecant.finrank_hwPlane (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : Module.finrank ℚ P.hwPlane = 2 := by
  obtain ⟨α₁, α₂, h₁, h₂⟩ := P.s3_exists_α
  rw [P.s3_hwPlane_eq hP.isCompl h₁ h₂, finrank_span_eq_card (P.s3_α_li hP.isCompl h₁ h₂)]
  simp


/-- **Corollary 3.2.2** (`cor-plane-of-Hodge-Weil-classes`), first part: the plane
`⋀^{2n} W₁ + ⋀^{2n} W₂` in `⋀^{2n} V_K` is defined over `ℚ`: it is the `K`-span of the rational
plane `ĤW_P`. -/
theorem corollary3_2_2_rational (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' P.hwPlane) = topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) := by
  have hW := hP.isCompl
  have hd := s3_d_pos P
  obtain ⟨α₁, α₂, h₁, h₂⟩ := P.s3_exists_α
  have hplane := P.s3_hwPlane_eq hW h₁ h₂
  have hα₁ : α₁ ∈ P.hwPlane := hplane ▸ Submodule.subset_span ⟨0, rfl⟩
  have hα₂ : α₂ ∈ P.hwPlane := hplane ▸ Submodule.subset_span ⟨1, rfl⟩
  have hs : Kd.sqrtNeg d ≠ 0 := s3_sqrtNeg_ne_zero hd
  have hm₁ : bcExt ℚ (Kd d) n α₁ ∈ Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' P.hwPlane) :=
    Submodule.subset_span ⟨α₁, hα₁, rfl⟩
  have hm₂ : bcExt ℚ (Kd d) n α₂ ∈ Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' P.hwPlane) :=
    Submodule.subset_span ⟨α₂, hα₂, rfl⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact (P.s3_mem_hwPlane_iff α).mp hα
  · rw [P.s3_X_eq hW, Submodule.span_le]
    rintro _ (rfl | rfl)
    · have e : P.s3_ω₁ = (2 : Kd d)⁻¹ • (bcExt ℚ (Kd d) n α₁ +
          (Kd.sqrtNeg d)⁻¹ • bcExt ℚ (Kd d) n α₂) := by
        rw [h₁, h₂, smul_smul, inv_mul_cancel₀ hs, one_smul, add_add_sub_cancel,
          ← two_smul (Kd d), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hm₁ (Submodule.smul_mem _ _ hm₂))
    · have e : P.s3_ω₂ = (2 : Kd d)⁻¹ • (bcExt ℚ (Kd d) n α₁ -
          (Kd.sqrtNeg d)⁻¹ • bcExt ℚ (Kd d) n α₂) := by
        rw [h₁, h₂, smul_smul, inv_mul_cancel₀ hs, one_smul, add_sub_sub_cancel,
          ← two_smul (Kd d), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hm₁ (Submodule.smul_mem _ _ hm₂))


/-- **Corollary 3.2.2** (`cor-plane-of-Hodge-Weil-classes`), second part: the plane consists of
rational classes of Hodge type `(n, n)` (the Hodge–Weil classes) for every complex structure `I` in
`ρ(Spin(V_ℝ)_P)` satisfying `ν(I) = 2n`. -/
theorem corollary3_2_2_hodge (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) : P.hwPlane ≤ hodgeClassesV n I n := by
  have hW := hP.isCompl
  obtain ⟨g, hg, hgI⟩ := hIP
  have hcomm : I * P.fR hW = P.fR hW * I := hgI ▸ P.rho_spinPR_comm_fR J hP g hg
  obtain ⟨hA₁, hA₂, hB₁, hB₂⟩ := P.s3_core hW I hcomm hI hν
  have hdisj : ∀ W : Submodule ℂ (V ℂ n), V10 n I ⊓ W ⊓ (V01 n I ⊓ W) = ⊥ := by
    intro W
    rw [eq_bot_iff]
    intro x hx
    have h1 : complexifyV n I x = Complex.I • x := Module.End.mem_eigenspace_iff.mp hx.1.1
    have h2 : complexifyV n I x = -Complex.I • x := Module.End.mem_eigenspace_iff.mp hx.2.1
    have : (2 * Complex.I) • x = 0 := by
      have e : (2 * Complex.I) • x = Complex.I • x - (-Complex.I) • x := by module
      rw [e, ← h1, ← h2, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hsplit₁ := s3_I_split I hI P.W₁ℂ fun x hx => P.s3_W₁ℂ_I_stable hW I hcomm hx
  have hsplit₂ := s3_I_split I hI P.W₂ℂ fun x hx => P.s3_W₂ℂ_I_stable hW I hcomm hx
  have hω₁ : bcExt (Kd d) ℂ n P.s3_ω₁ ∈ pqPiece (V10 n I) (V01 n I) n n := by
    rw [KSecant.s3_ω₁, s3_bcExt_ιMulti]
    refine s3_ιMulti_mem_pqPiece (hdisj P.W₁ℂ) hA₁ hB₁ inf_le_left inf_le_left (by ring) _
      fun i => ?_
    rw [hsplit₁]
    exact Submodule.subset_span ⟨_, P.s3_b₁_mem i, rfl⟩
  have hω₂ : bcExt (Kd d) ℂ n P.s3_ω₂ ∈ pqPiece (V10 n I) (V01 n I) n n := by
    rw [KSecant.s3_ω₂, s3_bcExt_ιMulti]
    refine s3_ιMulti_mem_pqPiece (hdisj P.W₂ℂ) hA₂ hB₂ inf_le_left inf_le_left (by ring) _
      fun i => ?_
    rw [hsplit₂]
    exact Submodule.subset_span ⟨_, P.s3_σV_mem_W₂ (P.s3_b₁_mem i), rfl⟩
  intro α hα
  rw [mem_hodgeClassesV_iff]
  have hα' := (P.s3_mem_hwPlane_iff α).mp hα
  rw [P.s3_X_eq hW, Submodule.mem_span_pair] at hα'
  obtain ⟨a, b, hab⟩ := hα'
  constructor
  · apply s3_mem_exteriorPower_of_bcExt ℚ (Kd d)
    rw [← hab]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range _ _ ⟨_, rfl⟩))
      (Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range _ _ ⟨_, rfl⟩))
  · rw [← s3_bcExt_trans ℚ (Kd d) ℂ, ← hab, map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ hω₁)
      (Submodule.smul_of_tower_mem _ _ hω₂)


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
  obtain ⟨g, hg, hgI⟩ := hIP
  have hcomm := P.rho_spinPR_comm_fR J hP g hg
  rw [hgI] at hcomm
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y => ?_
  -- `g_I(y, x) = (f y, I x) = -(y, f I x) = -(y, I f x) = (I y, f x) = g_I(x, y)`
  show pairing ℝ n (P.fR hP.isCompl x) (I y) = pairing ℝ n (P.fR hP.isCompl y) (I x)
  rw [P.s3_pairing_fR_left hP.isCompl y, ← Module.End.mul_apply, ← hcomm, Module.End.mul_apply,
    ← neg_neg (pairing ℝ n y _), ← P.s3_pairing_I_left I ⟨g, hg, hgI⟩ hI, neg_neg,
    s3_pairing_comm]

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
  obtain ⟨g, hg, hgI⟩ := hIP
  have hcomm := P.rho_spinPR_comm_fR J hP g hg
  rw [hgI] at hcomm
  -- `Ξ_P(I x, I y) = (f I x, I y)_V = (I f x, I y)_V = (f x, y)_V`
  show pairing ℝ n (P.fR hP.isCompl (I x)) (I y) = pairing ℝ n (P.fR hP.isCompl x) y
  rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply,
    P.s3_pairing_I I ⟨g, hg, hgI⟩]

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): `Ξ_P` is a Kähler class for the
complex torus `(V_ℝ/V_ℤ, I)`: `Ξ_P(x, I x) > 0` for every nonzero tangent vector `x ∈ V_ℝ`
(convention of [Huybrechts, Lemma 1.2.15]). -/
theorem corollary3_2_3_kahler (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x)
    (x : V ℝ n) (hx : x ≠ 0) : 0 < P.XiR hP.isCompl x (I x) :=
  -- `Ξ_P(x, I x) = g_I(x, x)`
  hpos x hx

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): the embedding `K → End_ℚ(A)` sending
`√-d` to `f` (2.4.1) is by endomorphisms of the complex torus: `f` commutes with `I`. -/
theorem corollary3_2_3_comm (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x) :
    I * P.fR hP.isCompl = P.fR hP.isCompl * I := by
  obtain ⟨g, hg, rfl⟩ := hIP
  exact P.rho_spinPR_comm_fR J hP g hg

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): Weil type — each eigenspace
`W_{i,ℂ}` of `f` meets `V^{1,0}` in an `n`-dimensional subspace (Lemma 3.2.1). -/
theorem corollary3_2_3_weil (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x) :
    Module.finrank ℂ ↥(P.W₁ℂ ⊓ V10 n I) = n ∧ Module.finrank ℂ ↥(P.W₂ℂ ⊓ V10 n I) = n := by
  obtain ⟨h1, h2, -, -⟩ := lemma3_2_1 P J hP I hIP hI hν
  rw [inf_comm] at h1 h2
  exact ⟨h1, h2⟩

/-- **Corollary 3.2.3** (`cor-abelian-variety-of-weil-type`): the condition on the polarization in
[van Geemen, Def. 4.9]: `f^*Ξ_P = d Ξ_P`, i.e. `Ξ_P(f x, f y) = d Ξ_P(x, y)` (which gives
`η(k)^*Ξ_P = Nm(k) Ξ_P` for all `k ∈ K`, `WeilClasses.vanGeemen_def4_9`). -/
theorem corollary3_2_3_polarization (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n))
    (hIP : ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) (hI : IsComplexStructure I)
    (hν : P.nu hP.isCompl I = 2 * n) (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl I x x)
    (x y : V ℚ n) :
    P.XiQ hP.isCompl (P.fη hP.isCompl x) (P.fη hP.isCompl y) = d * P.XiQ hP.isCompl x y :=
  -- `Ξ_P(f x, f y) = (f²x, f y)_V = d (f x, y)_V = d Ξ_P(x, y)`
  P.pairing_fη_fη hP.isCompl (P.fη hP.isCompl x) y

end WeilClasses
