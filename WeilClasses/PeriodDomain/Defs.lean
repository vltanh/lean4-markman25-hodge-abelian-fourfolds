module

public import WeilClasses.Hermitian.ComplexStructures
public import WeilClasses.PureSpinor.Lemma2_2_7
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinorNorm

/-!
# An adjoint orbit in `Spin(V_ℝ)_P` as a period domain (paper §4, Lemmas 4.0.1 and 4.0.2)

§4 of the paper up to Lemma 4.0.2 (TeX lines 1711–1804), under Assumption 2.4.1:

* `Ω_P ⊆ SO_+(V_ℝ)_f` (4.0.1) (`KSecant.OmegaP`): the complex structures `I` in `SO_+(V_ℝ)_f` with
  both eigenspaces of `f ∘ I` of dimension `2n` and `g_I` positive definite;
* the Grassmannian `Gr(n, W_{1,ℂ})` (`KSecant.GrW₁`) with its classical topology, and
  `ι(I) = V^{1,0}_I ∩ W_{1,ℂ}` (`KSecant.iota`);
* Lemma 4.0.1: `ι` is injective, with nonempty open image (and a topological embedding);
* Lemma 4.0.2: the connected components of `Ω_P` are `SO_+(V_ℝ)_f`-adjoint orbits (proved by the
  authorized departure: direct transitivity of `SO_+(V_ℝ)_f ≅ SU(n, n)` on `Ω_P`, through Cartan
  involutions, instead of the paper's dimension count).

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

/-! ## Helpers (prefix `s4_`): base change, complexification, conjugation, the eigenspaces of `f` -/

section Repr
variable (F : Type*) [Field F] (n : ℕ)

theorem s4_repr_basisV_inl (v : V F n) (k : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inl k)) = v.1 (e F n k) := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inl]
  simp [e]

theorem s4_repr_basisV_inr (v : V F n) (k : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inr k)) = v.2 k := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inr]
  simp

end Repr

section Conj
variable {F : Type*} [Field F] [CharZero F] (c : F ≃+* F) (n : ℕ)

theorem s4_repr_conjV (v : V F n) (i : Fin (2 * n + 2 * n)) :
    (basisV F n).repr (conjV c n v) i = c ((basisV F n).repr v i) := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  rcases k with k | k
  · rw [s4_repr_basisV_inl, s4_repr_basisV_inl]
    show (∑ i, c (v.1 (e F n i)) • f F n i) (e F n k) = _
    rw [LinearMap.sum_apply, Finset.sum_eq_single k]
    · simp [f, e]
    · intro b _ hb; simp [f, e, hb]
    · simp
  · rw [s4_repr_basisV_inr, s4_repr_basisV_inr]
    rfl

theorem s4_conjV_smul (z : F) (v : V F n) : conjV c n (z • v) = c z • conjV c n v := by
  apply (basisV F n).repr.injective
  ext i
  simp [s4_repr_conjV]

end Conj
section BC
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] in
theorem s4_basisV_inl (k : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inl k)) = (f F n k, 0) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, Function.comp_apply]
  refine Prod.ext ?_ rfl
  ext x
  simp [f]

omit [CharZero F] in
theorem s4_basisV_inr (k : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inr k)) = (0, e F n k) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply]
  simp [e]

theorem s4_bcDual_f (k : Fin (2 * n)) : bcDual F F' n (f F n k) = f F' n k := by
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single k]
  · simp [f, e]
  · intro b _ hb
    simp [f, e, hb]
  · simp

omit [CharZero F] [CharZero F'] in
theorem s4_bcH1_e (k : Fin (2 * n)) : bcH1 F F' n (e F n k) = e F' n k := by
  ext j
  simp [bcH1, e, Pi.single_apply]

theorem s4_bcV_basisV (i : Fin (2 * n + 2 * n)) :
    bcV F F' n (basisV F n i) = basisV F' n i := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  rcases k with k | k
  · rw [s4_basisV_inl, s4_basisV_inl]
    simp [bcV, s4_bcDual_f]
  · rw [s4_basisV_inr, s4_basisV_inr]
    simp [bcV, s4_bcH1_e]

theorem s4_bcV_eq_sum (v : V F n) :
    bcV F F' n v = ∑ i, algebraMap F F' ((basisV F n).repr v i) • basisV F' n i := by
  conv_lhs => rw [← (basisV F n).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower, s4_bcV_basisV, algebraMap_smul]

theorem s4_repr_bcV (v : V F n) (i : Fin (2 * n + 2 * n)) :
    (basisV F' n).repr (bcV F F' n v) i = algebraMap F F' ((basisV F n).repr v i) := by
  rw [s4_bcV_eq_sum, Module.Basis.repr_sum_self]

theorem s4_bcV_injective : Function.Injective (bcV F F' n) := by
  intro v w h
  apply (basisV F n).repr.injective
  ext i
  have := congrArg (fun x => (basisV F' n).repr x i) h
  simp only [s4_repr_bcV] at this
  exact (algebraMap F F').injective this

/-- The extension of scalars `F → F'` of an endomorphism of `V_F` (same matrix in `basisV`). -/
noncomputable def s4_extEnd (A : Module.End F (V F n)) : Module.End F' (V F' n) :=
  Matrix.toLin (basisV F' n) (basisV F' n)
    ((LinearMap.toMatrix (basisV F n) (basisV F n) A).map (algebraMap F F'))

theorem s4_extEnd_basisV (A : Module.End F (V F n)) (j : Fin (2 * n + 2 * n)) :
    s4_extEnd F F' n A (basisV F' n j) = bcV F F' n (A (basisV F n j)) := by
  rw [s4_extEnd, Matrix.toLin_self, s4_bcV_eq_sum]
  simp [LinearMap.toMatrix_apply]

theorem s4_extEnd_bcV (A : Module.End F (V F n)) (v : V F n) :
    s4_extEnd F F' n A (bcV F F' n v) = bcV F F' n (A v) := by
  have h : ((s4_extEnd F F' n A).restrictScalars F ∘ₗ bcV F F' n) = bcV F F' n ∘ₗ A := by
    refine (basisV F n).ext fun j => ?_
    simp [s4_bcV_basisV, s4_extEnd_basisV]
  exact congrArg (fun g => g v) h

omit [CharZero F] [CharZero F'] in
theorem s4_extEnd_mul (A B : Module.End F (V F n)) :
    s4_extEnd F F' n (A * B) = s4_extEnd F F' n A * s4_extEnd F F' n B := by
  simp only [s4_extEnd, LinearMap.toMatrix_mul, Matrix.map_mul,
    Matrix.toLin_mul (basisV F' n) (basisV F' n)]
  rfl

omit [CharZero F] [CharZero F'] in
theorem s4_extEnd_one : s4_extEnd F F' n 1 = 1 := by
  simp [s4_extEnd, Module.End.one_eq_id]

omit [CharZero F] [CharZero F'] in
theorem s4_extEnd_add (A B : Module.End F (V F n)) :
    s4_extEnd F F' n (A + B) = s4_extEnd F F' n A + s4_extEnd F F' n B := by
  simp [s4_extEnd, Matrix.map_add]

theorem s4_extEnd_smul (c : F) (A : Module.End F (V F n)) :
    s4_extEnd F F' n (c • A) = algebraMap F F' c • s4_extEnd F F' n A := by
  refine (basisV F' n).ext fun j => ?_
  rw [LinearMap.smul_apply, s4_extEnd_basisV, s4_extEnd_basisV, LinearMap.smul_apply,
    LinearMap.map_smul_of_tower, algebraMap_smul]

omit [CharZero F] [CharZero F'] in
theorem s4_extEnd_neg (A : Module.End F (V F n)) :
    s4_extEnd F F' n (-A) = -s4_extEnd F F' n A := by
  simp [s4_extEnd, Matrix.map_neg]

omit [CharZero F] [CharZero F'] in
theorem s4_extEnd_sub (A B : Module.End F (V F n)) :
    s4_extEnd F F' n (A - B) = s4_extEnd F F' n A - s4_extEnd F F' n B := by
  simp [s4_extEnd, Matrix.map_sub]

theorem s4_extEnd_injective : Function.Injective (s4_extEnd F F' n) := by
  intro A B h
  refine (basisV F n).ext fun j => ?_
  apply s4_bcV_injective F F' n
  rw [← s4_extEnd_bcV, ← s4_extEnd_bcV, h]

end BC

variable (n : ℕ)

theorem s4_complexifyV_eq (A : Module.End ℝ (V ℝ n)) : complexifyV n A = s4_extEnd ℝ ℂ n A := rfl

theorem s4_bcEndV_eq (F' : Type*) [Field F'] [CharZero F'] (A : Module.End ℚ (V ℚ n)) :
    bcEndV F' n A = s4_extEnd ℚ F' n A := rfl


section Tower
variable (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
  [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F''] (n : ℕ)

theorem s4_bcV_bcV (v : V F n) : bcV F' F'' n (bcV F F' n v) = bcV F F'' n v := by
  apply (basisV F'' n).repr.injective
  ext i
  simp only [s4_repr_bcV, ← IsScalarTower.algebraMap_apply]

theorem s4_extEnd_extEnd (A : Module.End F (V F n)) :
    s4_extEnd F' F'' n (s4_extEnd F F' n A) = s4_extEnd F F'' n A := by
  refine (basisV F'' n).ext fun j => ?_
  rw [s4_extEnd_basisV, ← s4_bcV_basisV F F' n, s4_extEnd_bcV, s4_bcV_bcV, s4_extEnd_basisV]

end Tower

section ReIm
variable (n : ℕ)

/-- The real part of a vector of `V_ℂ` (coordinatewise in `basisV`). -/
noncomputable def s4_reV : V ℂ n →ₗ[ℝ] V ℝ n :=
  (basisV ℝ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi fun j => Complex.reLm ∘ₗ ((basisV ℂ n).coord j).restrictScalars ℝ

/-- The imaginary part of a vector of `V_ℂ` (coordinatewise in `basisV`). -/
noncomputable def s4_imV : V ℂ n →ₗ[ℝ] V ℝ n :=
  (basisV ℝ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi fun j => Complex.imLm ∘ₗ ((basisV ℂ n).coord j).restrictScalars ℝ

theorem s4_repr_reV (x : V ℂ n) (j : Fin (2 * n + 2 * n)) :
    (basisV ℝ n).repr (s4_reV n x) j = ((basisV ℂ n).repr x j).re := by
  rw [s4_reV, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Module.Basis.repr_sum_self]
  simp

theorem s4_repr_imV (x : V ℂ n) (j : Fin (2 * n + 2 * n)) :
    (basisV ℝ n).repr (s4_imV n x) j = ((basisV ℂ n).repr x j).im := by
  rw [s4_imV, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Module.Basis.repr_sum_self]
  simp

theorem s4_bcV_re_add_im (x : V ℂ n) :
    bcV ℝ ℂ n (s4_reV n x) + Complex.I • bcV ℝ ℂ n (s4_imV n x) = x := by
  apply (basisV ℂ n).repr.injective
  ext j
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s4_repr_bcV, s4_repr_reV,
    s4_repr_imV, smul_eq_mul, Complex.coe_algebraMap]
  apply Complex.ext <;> simp

theorem s4_reV_bcV (v : V ℝ n) : s4_reV n (bcV ℝ ℂ n v) = v := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_reV, s4_repr_bcV]

theorem s4_imV_bcV (v : V ℝ n) : s4_imV n (bcV ℝ ℂ n v) = 0 := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_imV, s4_repr_bcV]

theorem s4_reV_I_smul (x : V ℂ n) : s4_reV n (Complex.I • x) = -s4_imV n x := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_reV, s4_repr_imV]

theorem s4_imV_I_smul (x : V ℂ n) : s4_imV n (Complex.I • x) = s4_reV n x := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_reV, s4_repr_imV]

theorem s4_repr_extEnd (A : Module.End ℝ (V ℝ n)) (x : V ℂ n) (i : Fin (2 * n + 2 * n)) :
    (basisV ℂ n).repr (s4_extEnd ℝ ℂ n A x) i =
      ∑ j, (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) A i j : ℂ) * (basisV ℂ n).repr x j := by
  rw [s4_extEnd, Matrix.toLin_apply, Module.Basis.repr_sum_self]
  simp [Matrix.mulVec, dotProduct]

theorem s4_repr_apply (A : Module.End ℝ (V ℝ n)) (v : V ℝ n) (i : Fin (2 * n + 2 * n)) :
    (basisV ℝ n).repr (A v) i =
      ∑ j, LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) A i j * (basisV ℝ n).repr v j := by
  rw [← Matrix.toLin_toMatrix (basisV ℝ n) (basisV ℝ n) A, Matrix.toLin_apply,
    Module.Basis.repr_sum_self, LinearMap.toMatrix_toLin]
  simp [Matrix.mulVec, dotProduct]

theorem s4_reV_extEnd (A : Module.End ℝ (V ℝ n)) (x : V ℂ n) :
    s4_reV n (s4_extEnd ℝ ℂ n A x) = A (s4_reV n x) := by
  apply (basisV ℝ n).repr.injective
  ext i
  rw [s4_repr_reV, s4_repr_extEnd, s4_repr_apply]
  simp [Complex.re_sum, s4_repr_reV]

theorem s4_imV_extEnd (A : Module.End ℝ (V ℝ n)) (x : V ℂ n) :
    s4_imV n (s4_extEnd ℝ ℂ n A x) = A (s4_imV n x) := by
  apply (basisV ℝ n).repr.injective
  ext i
  rw [s4_repr_imV, s4_repr_extEnd, s4_repr_apply]
  simp [Complex.im_sum, s4_repr_imV]

end ReIm

section EigenC
variable (n : ℕ)

theorem s4_reV_smul (z : ℂ) (v : V ℝ n) : s4_reV n (z • bcV ℝ ℂ n v) = z.re • v := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_reV, s4_repr_bcV]

theorem s4_imV_smul (z : ℂ) (v : V ℝ n) : s4_imV n (z • bcV ℝ ℂ n v) = z.im • v := by
  apply (basisV ℝ n).repr.injective
  ext j
  simp [s4_repr_imV, s4_repr_bcV]

/-- The complexification of a real eigenspace: `dim_ℂ E(A_ℂ, μ) = dim_ℝ E(A, μ)` for real `μ`. -/
theorem s4_finrank_eigenspace_extEnd (A : Module.End ℝ (V ℝ n)) (μ : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (s4_extEnd ℝ ℂ n A) (μ : ℂ)) =
      Module.finrank ℝ (Module.End.eigenspace A μ) := by
  set E := Module.End.eigenspace A μ
  set Ec := Module.End.eigenspace (s4_extEnd ℝ ℂ n A) (μ : ℂ)
  have hre : ∀ x ∈ Ec, s4_reV n x ∈ E := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← s4_reV_extEnd, hx]
    apply (basisV ℝ n).repr.injective
    ext j
    simp [s4_repr_reV]
  have him : ∀ x ∈ Ec, s4_imV n x ∈ E := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← s4_imV_extEnd, hx]
    apply (basisV ℝ n).repr.injective
    ext j
    simp [s4_repr_imV]
  have hbc : ∀ v ∈ E, bcV ℝ ℂ n v ∈ Ec := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [s4_extEnd_bcV, hv, LinearMap.map_smul_of_tower]
    rfl
  -- the `ℝ`-linear isomorphism `Ec ≅ E × E`
  let φ : Ec ≃ₗ[ℝ] E × E :=
    { toFun := fun x => (⟨s4_reV n x, hre x x.2⟩, ⟨s4_imV n x, him x x.2⟩)
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun r x => by ext <;> simp
      invFun := fun p => ⟨bcV ℝ ℂ n p.1 + Complex.I • bcV ℝ ℂ n p.2,
        Ec.add_mem (hbc _ p.1.2) (Ec.smul_mem _ (hbc _ p.2.2))⟩
      left_inv := fun x => Subtype.ext (s4_bcV_re_add_im n x)
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [map_add, s4_reV_bcV, s4_reV_I_smul, s4_imV_bcV, neg_zero, add_zero]
        · simp only [map_add, s4_imV_bcV, s4_imV_I_smul, s4_reV_bcV, zero_add] }
  have h1 := φ.finrank_eq
  rw [Module.finrank_prod] at h1
  have h2 := Module.finrank_mul_finrank ℝ ℂ Ec
  rw [Complex.finrank_real_complex] at h2
  omega

end EigenC

section ConjC
variable (n : ℕ)

theorem s4_conjV_conjV (x : V ℂ n) :
    conjV (starRingAut : ℂ ≃+* ℂ) n (conjV (starRingAut : ℂ ≃+* ℂ) n x) = x := by
  apply (basisV ℂ n).repr.injective
  ext j
  simp [s4_repr_conjV]

/-- Complex conjugation of `V_ℂ`, as a semilinear equivalence. -/
noncomputable def s4_conjL : V ℂ n ≃ₛₗ[starRingEnd ℂ] V ℂ n where
  toFun := conjV (starRingAut : ℂ ≃+* ℂ) n
  map_add' := map_add _
  map_smul' z x := s4_conjV_smul _ n z x
  invFun := conjV (starRingAut : ℂ ≃+* ℂ) n
  left_inv := s4_conjV_conjV n
  right_inv := s4_conjV_conjV n

theorem s4_conjL_apply (x : V ℂ n) : s4_conjL n x = conjV (starRingAut : ℂ ≃+* ℂ) n x := rfl

theorem s4_repr_conjL (x : V ℂ n) (j : Fin (2 * n + 2 * n)) :
    (basisV ℂ n).repr (s4_conjL n x) j = (starRingEnd ℂ) ((basisV ℂ n).repr x j) :=
  s4_repr_conjV _ n x j

theorem s4_conjL_conjL (x : V ℂ n) : s4_conjL n (s4_conjL n x) = x := s4_conjV_conjV n x

theorem s4_conjL_bcV (v : V ℝ n) : s4_conjL n (bcV ℝ ℂ n v) = bcV ℝ ℂ n v := by
  apply (basisV ℂ n).repr.injective
  ext j
  simp [s4_repr_conjL, s4_repr_bcV]

theorem s4_conjL_extEnd (A : Module.End ℝ (V ℝ n)) (x : V ℂ n) :
    s4_conjL n (s4_extEnd ℝ ℂ n A x) = s4_extEnd ℝ ℂ n A (s4_conjL n x) := by
  apply (basisV ℂ n).repr.injective
  ext j
  simp [s4_repr_conjL, s4_repr_extEnd]

theorem s4_finrank_map_conjL (U : Submodule ℂ (V ℂ n)) :
    Module.finrank ℂ (U.map (s4_conjL n).toLinearMap) = Module.finrank ℂ U := by
  let j : U ≃+ U.map (s4_conjL n).toLinearMap :=
    (Submodule.equivMapOfInjective (s4_conjL n).toLinearMap (s4_conjL n).injective U).toAddEquiv
  have h := rank_eq_of_equiv_equiv (starRingEnd ℂ) j
    (Function.Involutive.bijective (fun z => Complex.conj_conj z))
    (fun r m => Subtype.ext (s4_conjV_smul _ n r (m : V ℂ n)))
  simp only [Module.finrank, h]

theorem s4_conjL_mem_eigenspace (A : Module.End ℝ (V ℝ n)) (μ : ℂ) (x : V ℂ n)
    (hx : x ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n A) μ) :
    s4_conjL n x ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n A) ((starRingEnd ℂ) μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← s4_conjL_extEnd, hx]
  exact s4_conjV_smul _ n μ x

theorem s4_map_conjL_eigenspace (A : Module.End ℝ (V ℝ n)) (μ : ℂ) :
    (Module.End.eigenspace (s4_extEnd ℝ ℂ n A) μ).map (s4_conjL n).toLinearMap =
      Module.End.eigenspace (s4_extEnd ℝ ℂ n A) ((starRingEnd ℂ) μ) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact s4_conjL_mem_eigenspace n A μ x hx
  · intro y hy
    refine ⟨s4_conjL n y, ?_, s4_conjL_conjL n y⟩
    have := s4_conjL_mem_eigenspace n A _ y hy
    rwa [Complex.conj_conj] at this

end ConjC

section Split

/-- If `S` and `T` commute and `(S - a)(S - b) = 0` with `a ≠ b`, every eigenspace of `T` splits
along the eigenspaces of `S`. -/
theorem s4_eigenspace_split {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S T : Module.End K M) (hST : S * T = T * S) (a b c : K) (hab : a ≠ b)
    (hS : (S - algebraMap K _ a) * (S - algebraMap K _ b) = 0) :
    T.eigenspace c = T.eigenspace c ⊓ S.eigenspace a ⊔ T.eigenspace c ⊓ S.eigenspace b := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hba' : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hS' : ∀ v, S (S v) = (a + b) • S v - (a * b) • v := by
      intro v
      have := congrArg (fun F => F v) hS
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
        map_sub, map_smul, LinearMap.zero_apply] at this
      rw [← sub_eq_zero, ← this]
      module
    have hTS : T (S x) = c • S x := by
      have := congrArg (fun F => F x) hST
      simp only [Module.End.mul_apply] at this
      rw [← this, hx, map_smul]
    set y := (a - b)⁻¹ • (S x - b • x) with hy
    set z := (b - a)⁻¹ • (S x - a • x) with hz
    have hyz : x = y + z := by
      rw [hy, hz]
      have : (b - a)⁻¹ = -(a - b)⁻¹ := by rw [← inv_neg, neg_sub]
      rw [this, neg_smul, ← sub_eq_add_neg, ← smul_sub,
        show S x - b • x - (S x - a • x) = (a - b) • x by module, smul_smul,
        inv_mul_cancel₀ hab', one_smul]
    have hTy : T y = c • y := by
      rw [hy, map_smul, map_sub, map_smul, hTS, hx]
      module
    have hTz : T z = c • z := by
      rw [hz, map_smul, map_sub, map_smul, hTS, hx]
      module
    have hSy : S y = a • y := by
      rw [hy, map_smul, map_sub, map_smul, hS']
      module
    have hSz : S z = b • z := by
      rw [hz, map_smul, map_sub, map_smul, hS']
      module
    rw [hyz]
    exact Submodule.add_mem_sup
      ⟨Module.End.mem_eigenspace_iff.mpr hTy, Module.End.mem_eigenspace_iff.mpr hSy⟩
      ⟨Module.End.mem_eigenspace_iff.mpr hTz, Module.End.mem_eigenspace_iff.mpr hSz⟩
  · exact sup_le inf_le_left inf_le_left

theorem s4_disjoint_eigenspace {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S : Module.End K M) {a b : K} (hab : a ≠ b) : Disjoint (S.eigenspace a) (S.eigenspace b) :=
  (Module.End.eigenspaces_iSupIndep S).pairwiseDisjoint hab

theorem s4_isCompl_eigenspace {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S : Module.End K M) (a b : K) (hab : a ≠ b)
    (hS : (S - algebraMap K _ a) * (S - algebraMap K _ b) = 0) :
    IsCompl (S.eigenspace a) (S.eigenspace b) := by
  refine ⟨s4_disjoint_eigenspace S hab, ?_⟩
  rw [codisjoint_iff]
  have h := s4_eigenspace_split S 1 (by simp) a b 1 hab hS
  have htop : (1 : Module.End K M).eigenspace 1 = ⊤ := by
    ext x
    simp
  rw [htop] at h
  simpa using h.symm

theorem s4_quad_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S : Module.End K M) (a b : K) :
    (S - algebraMap K _ a) * (S - algebraMap K _ b) =
      S * S - (a + b) • S + algebraMap K _ (a * b) := by
  rw [sub_mul, mul_sub, mul_sub, ← Algebra.commutes, ← map_mul, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul]
  simp only [smul_mul_assoc, one_mul]
  abel

/-- The determinant of an operator which is `a` on `U₁` and `b` on `U₂`, `M = U₁ ⊕ U₂`. -/
theorem s4_det_of_isCompl {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (T : Module.End K M) (U₁ U₂ : Submodule K M) (h : IsCompl U₁ U₂)
    (a b : K) (h1 : ∀ x ∈ U₁, T x = a • x) (h2 : ∀ x ∈ U₂, T x = b • x) :
    LinearMap.det T = a ^ Module.finrank K U₁ * b ^ Module.finrank K U₂ := by
  set e := Submodule.prodEquivOfIsCompl _ _ h
  have hT : T = e.toLinearMap ∘ₗ
      (LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id)) ∘ₗ e.symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    simp only [Submodule.coe_smul]
    rw [h1 _ y.1.2, h2 _ y.2.2]
  rw [congrArg LinearMap.det hT, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

/-- The determinant of the restriction of `T` to a `T`-stable `W = U₁ ⊕ U₂` on which `T` is `a` on
`U₁` and `b` on `U₂`. -/
theorem s4_det_restrict {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (T : Module.End K M) (W U₁ U₂ : Submodule K M)
    (hT : ∀ x ∈ W, T x ∈ W) (hU₁ : U₁ ≤ W) (hU₂ : U₂ ≤ W) (hdisj : U₁ ⊓ U₂ = ⊥)
    (hsup : U₁ ⊔ U₂ = W) (a b : K) (h1 : ∀ x ∈ U₁, T x = a • x) (h2 : ∀ x ∈ U₂, T x = b • x) :
    LinearMap.det (T.restrict hT) = a ^ Module.finrank K U₁ * b ^ Module.finrank K U₂ := by
  set T' : Module.End K W := T.restrict hT
  have hfr : ∀ U : Submodule K M, U ≤ W →
      Module.finrank K (U.comap W.subtype) = Module.finrank K U := by
    intro U hU
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr hU]
  have hc : IsCompl (U₁.comap W.subtype) (U₂.comap W.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, hdisj, Submodule.comap_bot]
      exact Submodule.ker_subtype W
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      have hx : (x : M) ∈ U₁ ⊔ U₂ := hsup ▸ x.2
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      have : x = ⟨y, hU₁ hy⟩ + ⟨z, hU₂ hz⟩ := Subtype.ext (by simp [hyz])
      rw [this]
      exact Submodule.add_mem_sup hy hz
  rw [s4_det_of_isCompl T' _ _ hc a b, hfr _ hU₁, hfr _ hU₂]
  · intro x hx
    exact Subtype.ext (by rw [LinearMap.coe_restrict_apply, Submodule.coe_smul]; exact h1 _ hx)
  · intro x hx
    exact Subtype.ext (by rw [LinearMap.coe_restrict_apply, Submodule.coe_smul]; exact h2 _ hx)

end Split

section CS
variable (n : ℕ)

theorem s4_extEnd_sq_of_cs (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    s4_extEnd ℝ ℂ n I * s4_extEnd ℝ ℂ n I = -1 := by
  rw [← s4_extEnd_mul, hI, s4_extEnd_neg, s4_extEnd_one]

theorem s4_V10_V01_split (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    (s4_extEnd ℝ ℂ n I - algebraMap ℂ _ Complex.I) *
      (s4_extEnd ℝ ℂ n I - algebraMap ℂ _ (-Complex.I)) = 0 := by
  rw [s4_quad_eq, s4_extEnd_sq_of_cs n I hI]
  simp

theorem s4_isCompl_V10_V01 (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    IsCompl (V10 n I) (V01 n I) :=
  s4_isCompl_eigenspace _ _ _ (by norm_num [Complex.ext_iff]) (s4_V10_V01_split n I hI)

theorem s4_map_conjL_V10 (I : Module.End ℝ (V ℝ n)) :
    (V10 n I).map (s4_conjL n).toLinearMap = V01 n I := by
  have := s4_map_conjL_eigenspace n I Complex.I
  rwa [Complex.conj_I] at this

/-- A complex structure is determined by its `i`-eigenspace `V^{1,0}`. -/
theorem s4_eq_of_V10_eq (I I' : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (h : V10 n I = V10 n I') : I = I' := by
  have h' : V01 n I = V01 n I' := by
    rw [← s4_map_conjL_V10, h, s4_map_conjL_V10]
  apply s4_extEnd_injective ℝ ℂ n
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ V10 n I ⊔ V01 n I := by rw [(s4_isCompl_V10_V01 n I hI).sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  have ha' : a ∈ V10 n I' := by rw [← h]; exact ha
  have hb' : b ∈ V01 n I' := by rw [← h']; exact hb
  have e1 : s4_extEnd ℝ ℂ n I a = Complex.I • a := Module.End.mem_eigenspace_iff.mp ha
  have e2 : s4_extEnd ℝ ℂ n I b = (-Complex.I) • b := Module.End.mem_eigenspace_iff.mp hb
  have e3 : s4_extEnd ℝ ℂ n I' a = Complex.I • a := Module.End.mem_eigenspace_iff.mp ha'
  have e4 : s4_extEnd ℝ ℂ n I' b = (-Complex.I) • b := Module.End.mem_eigenspace_iff.mp hb'
  rw [map_add, map_add, e1, e2, e3, e4]

end CS

theorem s4_det_extEnd (n : ℕ) (A : Module.End ℝ (V ℝ n)) :
    LinearMap.det (s4_extEnd ℝ ℂ n A) = ((LinearMap.det A : ℝ) : ℂ) := by
  rw [s4_extEnd, LinearMap.det_toLin, ← LinearMap.det_toMatrix (basisV ℝ n) A]
  exact ((algebraMap ℝ ℂ).map_det _).symm

/-- A complex structure `I` of `V_ℝ` has determinant `1`: `I_ℂ` is `i` on `V^{1,0}` and `-i` on
`V^{0,1} = conj(V^{1,0})`, two subspaces of the same dimension. -/
theorem s4_det_of_cs (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    LinearMap.det I = 1 := by
  have h := s4_det_of_isCompl (s4_extEnd ℝ ℂ n I) (V10 n I) (V01 n I) (s4_isCompl_V10_V01 n I hI)
    Complex.I (-Complex.I) (fun x hx => Module.End.mem_eigenspace_iff.mp hx)
    (fun x hx => Module.End.mem_eigenspace_iff.mp hx)
  have hdim : Module.finrank ℂ (V01 n I) = Module.finrank ℂ (V10 n I) := by
    rw [← s4_map_conjL_V10 n I, s4_finrank_map_conjL]
  rw [hdim, ← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow, s4_det_extEnd] at h
  exact_mod_cast h

/-- The squares are open in `ℝ^×` (the positive reals). -/
theorem s4_isOpen_square_real : IsOpen (Subgroup.square ℝˣ : Set ℝˣ) := by
  have h : (Subgroup.square ℝˣ : Set ℝˣ) = Units.val ⁻¹' Set.Ioi 0 := by
    ext u
    simp only [SetLike.mem_coe, Subgroup.mem_square, Set.mem_preimage, Set.mem_Ioi]
    constructor
    · rintro ⟨v, rfl⟩
      simp only [Units.val_mul]
      exact mul_self_pos.mpr v.ne_zero
    · intro hu
      have hs : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hu
      refine ⟨Units.mk0 _ hs.ne', Units.ext ?_⟩
      simp [Real.mul_self_sqrt hu.le]
  rw [h]
  exact isOpen_Ioi.preimage Units.continuous_val

theorem s4_sqrtNeg_ne_zero {d : ℚ} (hd : 0 < d) : sqrtNeg d ≠ 0 := by
  have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  simp [sqrtNeg, this.ne']

theorem s4_sqrtNeg_ne_neg {d : ℚ} (hd : 0 < d) : sqrtNeg d ≠ -sqrtNeg d := by
  intro h
  have : (2 : ℂ) * sqrtNeg d = 0 := by linear_combination h
  exact s4_sqrtNeg_ne_zero hd ((mul_eq_zero.mp this).resolve_left two_ne_zero)

theorem s4_conj_sqrtNeg (d : ℚ) : (starRingEnd ℂ) (sqrtNeg d) = -sqrtNeg d := by
  simp [sqrtNeg]

theorem s4_pairing_bcV (n : ℕ) (v w : V ℚ n) :
    pairing ℝ n (bcV ℚ ℝ n v) (bcV ℚ ℝ n w) = (pairing ℚ n v w : ℝ) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    ← map_sub, Q_bcV]
  simp

theorem s4_map_conjL_V01 (n : ℕ) (I : Module.End ℝ (V ℝ n)) :
    (V01 n I).map (s4_conjL n).toLinearMap = V10 n I := by
  have := s4_map_conjL_eigenspace n I (-Complex.I)
  rwa [map_neg, Complex.conj_I, neg_neg] at this

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

theorem s4_extEnd_fR (hW : IsCompl P.W₁ P.W₂) :
    s4_extEnd ℝ ℂ n (P.fR hW) = s4_extEnd ℚ ℂ n (P.fη hW) :=
  s4_extEnd_extEnd ℚ ℝ ℂ n (P.fη hW)

theorem s4_ηK_W₁ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (w : V (Kd d) n) (hw : w ∈ P.W₁) :
    P.ηK hW l w = l • w := by
  simp [ηK, Submodule.projectionOnto_apply_left hW ⟨w, hw⟩,
    Submodule.projectionOnto_apply_right hW.symm ⟨w, hw⟩]

theorem s4_ηK_W₂ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (w : V (Kd d) n) (hw : w ∈ P.W₂) :
    P.ηK hW l w = Kd.σ d l • w := by
  simp [ηK, Submodule.projectionOnto_apply_right hW ⟨w, hw⟩,
    Submodule.projectionOnto_apply_left hW.symm ⟨w, hw⟩]

theorem s4_extEnd_fη_K (hW : IsCompl P.W₁ P.W₂) :
    s4_extEnd ℚ (Kd d) n (P.fη hW) = P.ηK hW (Kd.sqrtNeg d) := by
  refine (basisV (Kd d) n).ext fun j => ?_
  rw [← s4_bcV_basisV ℚ (Kd d) n, s4_extEnd_bcV, ηK_bcV P P.d_pos hW]
  rfl

theorem s4_fC_bcV_W₁ (hW : IsCompl P.W₁ P.W₂) (w : V (Kd d) n) (hw : w ∈ P.W₁) :
    s4_extEnd ℝ ℂ n (P.fR hW) (bcV (Kd d) ℂ n w) = sqrtNeg d • bcV (Kd d) ℂ n w := by
  rw [s4_extEnd_fR, ← s4_extEnd_extEnd ℚ (Kd d) ℂ n, s4_extEnd_bcV, s4_extEnd_fη_K,
    s4_ηK_W₁ P hW _ w hw, LinearMap.map_smul_of_tower, ← algebraMap_smul ℂ]
  rfl

theorem s4_fC_bcV_W₂ (hW : IsCompl P.W₁ P.W₂) (w : V (Kd d) n) (hw : w ∈ P.W₂) :
    s4_extEnd ℝ ℂ n (P.fR hW) (bcV (Kd d) ℂ n w) = (-sqrtNeg d) • bcV (Kd d) ℂ n w := by
  rw [s4_extEnd_fR, ← s4_extEnd_extEnd ℚ (Kd d) ℂ n, s4_extEnd_bcV, s4_extEnd_fη_K,
    s4_ηK_W₂ P hW _ w hw, LinearMap.map_smul_of_tower, ← algebraMap_smul ℂ]
  congr 1
  show (starRingEnd ℂ) (sqrtNeg d) = _
  exact s4_conj_sqrtNeg d

theorem s4_W₁ℂ_le (hW : IsCompl P.W₁ P.W₂) :
    P.W₁ℂ ≤ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (sqrtNeg d) := by
  rw [W₁ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (s4_fC_bcV_W₁ P hW w hw)

theorem s4_W₂ℂ_le (hW : IsCompl P.W₁ P.W₂) :
    P.W₂ℂ ≤ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (-sqrtNeg d) := by
  rw [W₂ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (s4_fC_bcV_W₂ P hW w hw)

theorem s4_W₁ℂ_sup_W₂ℂ (hW : IsCompl P.W₁ P.W₂) : P.W₁ℂ ⊔ P.W₂ℂ = ⊤ := by
  rw [eq_top_iff, ← (basisV ℂ n).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [← s4_bcV_basisV (Kd d) ℂ n]
  have : basisV (Kd d) n j ∈ P.W₁ ⊔ P.W₂ := by rw [hW.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩)
    (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem s4_W₁ℂ_eq (hW : IsCompl P.W₁ P.W₂) :
    P.W₁ℂ = Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (sqrtNeg d) := by
  refine le_antisymm (s4_W₁ℂ_le P hW) fun x hx => ?_
  have : x ∈ P.W₁ℂ ⊔ P.W₂ℂ := by rw [s4_W₁ℂ_sup_W₂ℂ P hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
  have hb' : b ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (sqrtNeg d) := by
    have := Submodule.sub_mem _ hx (s4_W₁ℂ_le P hW ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := by
    have := (s4_disjoint_eigenspace _ (s4_sqrtNeg_ne_neg P.d_pos)).le_bot
      ⟨hb', s4_W₂ℂ_le P hW hb⟩
    simpa using this
  rw [hb0, add_zero]
  exact ha

theorem s4_W₂ℂ_eq (hW : IsCompl P.W₁ P.W₂) :
    P.W₂ℂ = Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (-sqrtNeg d) := by
  refine le_antisymm (s4_W₂ℂ_le P hW) fun x hx => ?_
  have : x ∈ P.W₁ℂ ⊔ P.W₂ℂ := by rw [s4_W₁ℂ_sup_W₂ℂ P hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
  have ha' : a ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) (-sqrtNeg d) := by
    have := Submodule.sub_mem _ hx (s4_W₂ℂ_le P hW hb)
    rwa [add_sub_cancel_right] at this
  have ha0 : a = 0 := by
    have := (s4_disjoint_eigenspace _ (s4_sqrtNeg_ne_neg P.d_pos)).le_bot
      ⟨s4_W₁ℂ_le P hW ha, ha'⟩
    simpa using this
  rw [ha0, zero_add]
  exact hb

theorem s4_isCompl_Wℂ (hW : IsCompl P.W₁ P.W₂) : IsCompl P.W₁ℂ P.W₂ℂ := by
  refine ⟨?_, codisjoint_iff.mpr (s4_W₁ℂ_sup_W₂ℂ P hW)⟩
  rw [s4_W₁ℂ_eq P hW, s4_W₂ℂ_eq P hW]
  exact s4_disjoint_eigenspace _ (s4_sqrtNeg_ne_neg P.d_pos)

theorem s4_map_conjL_W₁ℂ (hW : IsCompl P.W₁ P.W₂) :
    P.W₁ℂ.map (s4_conjL n).toLinearMap = P.W₂ℂ := by
  rw [s4_W₁ℂ_eq P hW, s4_W₂ℂ_eq P hW, s4_map_conjL_eigenspace, s4_conj_sqrtNeg]

theorem s4_map_conjL_W₂ℂ (hW : IsCompl P.W₁ P.W₂) :
    P.W₂ℂ.map (s4_conjL n).toLinearMap = P.W₁ℂ := by
  rw [s4_W₁ℂ_eq P hW, s4_W₂ℂ_eq P hW, s4_map_conjL_eigenspace, map_neg, s4_conj_sqrtNeg, neg_neg]

theorem s4_finrank_Vℂ : Module.finrank ℂ (V ℂ n) = 2 * n + 2 * n := by
  rw [Module.finrank_eq_card_basis (basisV ℂ n), Fintype.card_fin]

theorem s4_finrank_W₁ℂ (hW : IsCompl P.W₁ P.W₂) : Module.finrank ℂ P.W₁ℂ = 2 * n := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (s4_isCompl_Wℂ P hW)
  have h2 := s4_finrank_map_conjL n P.W₁ℂ
  rw [s4_map_conjL_W₁ℂ P hW, s4_finrank_Vℂ] at *
  omega

theorem s4_finrank_W₂ℂ (hW : IsCompl P.W₁ P.W₂) : Module.finrank ℂ P.W₂ℂ = 2 * n := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (s4_isCompl_Wℂ P hW)
  rw [s4_finrank_Vℂ, s4_finrank_W₁ℂ P hW] at h1
  omega

theorem s4_fC_quad (hW : IsCompl P.W₁ P.W₂) :
    (s4_extEnd ℝ ℂ n (P.fR hW) - algebraMap ℂ _ (sqrtNeg d)) *
      (s4_extEnd ℝ ℂ n (P.fR hW) - algebraMap ℂ _ (-sqrtNeg d)) = 0 := by
  refine LinearMap.ext fun x => ?_
  have : x ∈ P.W₁ℂ ⊔ P.W₂ℂ := by rw [s4_W₁ℂ_sup_W₂ℂ P hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
  rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at ha
  rw [s4_W₂ℂ_eq P hW, Module.End.mem_eigenspace_iff] at hb
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_add,
    map_sub, map_smul, ha, hb, LinearMap.zero_apply]
  module

theorem s4_sqrtNeg_mul_I (d : ℚ) : sqrtNeg d * Complex.I = -((Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
  rw [sqrtNeg, mul_comm, ← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- For a complex structure `I` commuting with `f`, the eigenspaces of `f ∘ I` (complexified) for
`∓√d` are `(V^{1,0} ∩ W_{1,ℂ}) ⊕ (V^{0,1} ∩ W_{2,ℂ})` and `(V^{0,1} ∩ W_{1,ℂ}) ⊕ (V^{1,0} ∩ W_{2,ℂ})`. -/
theorem s4_eigenspace_fI (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hc : I * P.fR hW = P.fR hW * I) :
    Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW * I)) ((-Real.sqrt (d : ℝ) : ℝ) : ℂ) =
        V10 n I ⊓ P.W₁ℂ ⊔ V01 n I ⊓ P.W₂ℂ ∧
      Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW * I)) ((Real.sqrt (d : ℝ) : ℝ) : ℂ) =
        V01 n I ⊓ P.W₁ℂ ⊔ V10 n I ⊓ P.W₂ℂ := by
  set Fc := s4_extEnd ℝ ℂ n (P.fR hW)
  set Ic := s4_extEnd ℝ ℂ n I
  have hcC : Ic * Fc = Fc * Ic := by
    simp only [Ic, Fc, ← s4_extEnd_mul, hc]
  have hFI : s4_extEnd ℝ ℂ n (P.fR hW * I) = Fc * Ic := s4_extEnd_mul ℝ ℂ n _ _
  rw [hFI]
  have hs0 : sqrtNeg d ≠ 0 := s4_sqrtNeg_ne_zero P.d_pos
  have hcomm : Fc * (Fc * Ic) = (Fc * Ic) * Fc := by rw [mul_assoc, ← hcC, ← mul_assoc]
  have hsplit := fun c => s4_eigenspace_split Fc (Fc * Ic) hcomm (sqrtNeg d) (-sqrtNeg d) c
    (s4_sqrtNeg_ne_neg P.d_pos) (s4_fC_quad P hW)
  -- `Ic` preserves `W_{1,ℂ}` and `W_{2,ℂ}`
  have hIW : ∀ μ : ℂ, ∀ x ∈ Module.End.eigenspace Fc μ, Ic x ∈ Module.End.eigenspace Fc μ := by
    intro μ x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have := congrArg (fun F => F x) hcC
    simp only [Module.End.mul_apply] at this
    rw [← this, hx, map_smul]
  have key : ∀ (μ c κ : ℂ), μ * κ = c → μ ≠ 0 →
      Module.End.eigenspace (Fc * Ic) c ⊓ Module.End.eigenspace Fc μ =
        Module.End.eigenspace Ic κ ⊓ Module.End.eigenspace Fc μ := by
    intro μ c κ hμκ hμ
    ext x
    simp only [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mul_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have h3 : Fc (Ic x) = μ • Ic x :=
        Module.End.mem_eigenspace_iff.mp (hIW μ x (Module.End.mem_eigenspace_iff.mpr h2))
      rw [h3, ← hμκ, mul_smul] at h1
      exact smul_right_injective _ hμ h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have h3 : Fc (Ic x) = μ • Ic x :=
        Module.End.mem_eigenspace_iff.mp (hIW μ x (Module.End.mem_eigenspace_iff.mpr h2))
      rw [h3, h1, smul_smul, hμκ]
  have hneg : sqrtNeg d * Complex.I = ((-Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
    rw [s4_sqrtNeg_mul_I]; push_cast; ring
  have hneg' : -sqrtNeg d * -Complex.I = ((-Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
    rw [neg_mul_neg, hneg]
  have hpos : sqrtNeg d * -Complex.I = ((Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
    rw [mul_neg, s4_sqrtNeg_mul_I, neg_neg]
  have hpos' : -sqrtNeg d * Complex.I = ((Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
    rw [neg_mul, s4_sqrtNeg_mul_I, neg_neg]
  have hW1 : P.W₁ℂ = Module.End.eigenspace Fc (sqrtNeg d) := s4_W₁ℂ_eq P hW
  have hW2 : P.W₂ℂ = Module.End.eigenspace Fc (-sqrtNeg d) := s4_W₂ℂ_eq P hW
  constructor
  · rw [hsplit, key _ _ _ hneg hs0, key _ _ _ hneg' (neg_ne_zero.mpr hs0), ← hW1, ← hW2]
    rfl
  · rw [hsplit, key _ _ _ hpos hs0, key _ _ _ hpos' (neg_ne_zero.mpr hs0), ← hW1, ← hW2]
    rfl

/-- For a complex structure `I` commuting with `f`,
`W_{i,ℂ} = (W_{i,ℂ} ∩ V^{1,0}_I) ⊕ (W_{i,ℂ} ∩ V^{0,1}_I)`. -/
theorem s4_Wℂ_split (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : IsComplexStructure I) (hc : I * P.fR hW = P.fR hW * I) :
    P.W₁ℂ = P.W₁ℂ ⊓ V10 n I ⊔ P.W₁ℂ ⊓ V01 n I ∧ P.W₂ℂ = P.W₂ℂ ⊓ V10 n I ⊔ P.W₂ℂ ⊓ V01 n I := by
  have hcC : s4_extEnd ℝ ℂ n I * s4_extEnd ℝ ℂ n (P.fR hW) =
      s4_extEnd ℝ ℂ n (P.fR hW) * s4_extEnd ℝ ℂ n I := by
    rw [← s4_extEnd_mul, ← s4_extEnd_mul, hc]
  have hne : Complex.I ≠ -Complex.I := by norm_num [Complex.ext_iff]
  constructor
  · rw [s4_W₁ℂ_eq P hW]
    exact s4_eigenspace_split _ _ hcC _ _ _ hne (s4_V10_V01_split n I hI)
  · rw [s4_W₂ℂ_eq P hW]
    exact s4_eigenspace_split _ _ hcC _ _ _ hne (s4_V10_V01_split n I hI)

/-- For `I` commuting with `f`, `I_ℂ` preserves `W_{1,ℂ}` and `W_{2,ℂ}`. -/
theorem s4_mapsTo_Wℂ (hW : IsCompl P.W₁ P.W₂) (A : Module.End ℝ (V ℝ n))
    (hc : A * P.fR hW = P.fR hW * A) :
    (∀ x ∈ P.W₁ℂ, s4_extEnd ℝ ℂ n A x ∈ P.W₁ℂ) ∧ (∀ x ∈ P.W₂ℂ, s4_extEnd ℝ ℂ n A x ∈ P.W₂ℂ) := by
  have hcC : s4_extEnd ℝ ℂ n A * s4_extEnd ℝ ℂ n (P.fR hW) =
      s4_extEnd ℝ ℂ n (P.fR hW) * s4_extEnd ℝ ℂ n A := by
    rw [← s4_extEnd_mul, ← s4_extEnd_mul, hc]
  have key : ∀ μ : ℂ, ∀ x ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) μ,
      s4_extEnd ℝ ℂ n A x ∈ Module.End.eigenspace (s4_extEnd ℝ ℂ n (P.fR hW)) μ := by
    intro μ x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have := congrArg (fun F => F x) hcC
    simp only [Module.End.mul_apply] at this
    rw [← this, hx, map_smul]
  rw [s4_W₁ℂ_eq P hW, s4_W₂ℂ_eq P hW]
  exact ⟨key _, key _⟩

/-- An orthogonal complex structure in `SO_+(V_ℝ)` commuting with `f`, whose `±i`-eigenspaces meet
each `W_{i,ℂ}` in subspaces of equal dimension, lies in `SO_+(V_ℝ)_f`: on `W_{i,ℂ}` it is `i` on a
`k`-dimensional and `-i` on a `k`-dimensional subspace, so its determinant is `(i · (-i))^k = 1`. -/
theorem s4_mem_SOplusfR_of_cs (hW : IsCompl P.W₁ P.W₂) (g : V ℝ n ≃ₗ[ℝ] V ℝ n)
    (hg : g ∈ SOplus ℝ n) (hcs : IsComplexStructure (g : V ℝ n →ₗ[ℝ] V ℝ n))
    (hc : (g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hW = P.fR hW * (g : V ℝ n →ₗ[ℝ] V ℝ n))
    (h1 : Module.finrank ℂ ↥(P.W₁ℂ ⊓ V10 n g) = Module.finrank ℂ ↥(P.W₁ℂ ⊓ V01 n g))
    (h2 : Module.finrank ℂ ↥(P.W₂ℂ ⊓ V10 n g) = Module.finrank ℂ ↥(P.W₂ℂ ⊓ V01 n g)) :
    g ∈ P.SOplusfR hW := by
  have hsplit := P.s4_Wℂ_split hW _ hcs hc
  have hmaps := P.s4_mapsTo_Wℂ hW _ hc
  have hdisj : ∀ W : Submodule ℂ (V ℂ n), W ⊓ V10 n g ⊓ (W ⊓ V01 n g) = ⊥ := by
    intro W
    rw [eq_bot_iff]
    intro x hx
    exact (s4_isCompl_V10_V01 n _ hcs).1.le_bot ⟨hx.1.2, hx.2.2⟩
  have hI : ∀ x ∈ V10 n g, complexifyV n g x = Complex.I • x := fun x hx =>
    Module.End.mem_eigenspace_iff.mp hx
  have hI' : ∀ x ∈ V01 n g, complexifyV n g x = (-Complex.I) • x := fun x hx =>
    Module.End.mem_eigenspace_iff.mp hx
  refine ⟨hg, fun x => congrArg (fun F => F x) hc, ⟨hmaps.1, ?_⟩, ⟨hmaps.2, ?_⟩⟩
  · show LinearMap.det ((s4_extEnd ℝ ℂ n g).restrict hmaps.1) = 1
    rw [s4_det_restrict _ _ _ _ hmaps.1 inf_le_left inf_le_left (hdisj _) hsplit.1.symm
        Complex.I (-Complex.I) (fun x hx => hI x hx.2) (fun x hx => hI' x hx.2), h1, ← mul_pow]
    simp
  · show LinearMap.det ((s4_extEnd ℝ ℂ n g).restrict hmaps.2) = 1
    rw [s4_det_restrict _ _ _ _ hmaps.2 inf_le_left inf_le_left (hdisj _) hsplit.2.symm
        Complex.I (-Complex.I) (fun x hx => hI x hx.2) (fun x hx => hI' x hx.2), h2, ← mul_pow]
    simp

/-- The real dimensions of the eigenspaces of `f ∘ I` from the dimensions of the four summands
`V^{1,0} ∩ W_{1,ℂ}`, `V^{0,1} ∩ W_{2,ℂ}` (eigenvalue `-√d`) and `V^{0,1} ∩ W_{1,ℂ}`,
`V^{1,0} ∩ W_{2,ℂ}` (eigenvalue `√d`). -/
theorem s4_finrank_eig_fI (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hc : I * P.fR hW = P.fR hW * I) :
    Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (-Real.sqrt d)) =
        Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) + Module.finrank ℂ ↥(V01 n I ⊓ P.W₂ℂ) ∧
      Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (Real.sqrt d)) =
        Module.finrank ℂ ↥(V01 n I ⊓ P.W₁ℂ) + Module.finrank ℂ ↥(V10 n I ⊓ P.W₂ℂ) := by
  have hdisj : ∀ A B : Submodule ℂ (V ℂ n), A ⊓ P.W₁ℂ ⊓ (B ⊓ P.W₂ℂ) = ⊥ := by
    intro A B
    rw [eq_bot_iff]
    intro x hx
    exact (s4_isCompl_Wℂ P hW).1.le_bot ⟨hx.1.2, hx.2.2⟩
  have hsum : ∀ A B : Submodule ℂ (V ℂ n), Module.finrank ℂ ↥(A ⊓ P.W₁ℂ ⊔ B ⊓ P.W₂ℂ) =
      Module.finrank ℂ ↥(A ⊓ P.W₁ℂ) + Module.finrank ℂ ↥(B ⊓ P.W₂ℂ) := by
    intro A B
    have := Submodule.finrank_sup_add_finrank_inf_eq (A ⊓ P.W₁ℂ) (B ⊓ P.W₂ℂ)
    rw [hdisj, finrank_bot, add_zero] at this
    exact this
  have h1 := s4_finrank_eigenspace_extEnd n (P.fR hW * I) (-Real.sqrt d)
  have h2 := s4_finrank_eigenspace_extEnd n (P.fR hW * I) (Real.sqrt d)
  rw [(s4_eigenspace_fI P hW I hc).1, hsum] at h1
  rw [(s4_eigenspace_fI P hW I hc).2, hsum] at h2
  exact ⟨h1.symm, h2.symm⟩

/-- For `I` commuting with `f`, `V^{1,0}_I = (V^{1,0}_I ∩ W_{1,ℂ}) ⊕ (V^{1,0}_I ∩ W_{2,ℂ})`. -/
theorem s4_V10_split (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hc : I * P.fR hW = P.fR hW * I) :
    V10 n I = V10 n I ⊓ P.W₁ℂ ⊔ V10 n I ⊓ P.W₂ℂ := by
  have hcC : s4_extEnd ℝ ℂ n (P.fR hW) * s4_extEnd ℝ ℂ n I =
      s4_extEnd ℝ ℂ n I * s4_extEnd ℝ ℂ n (P.fR hW) := by
    rw [← s4_extEnd_mul, ← s4_extEnd_mul, hc]
  have := s4_eigenspace_split _ _ hcC (sqrtNeg d) (-sqrtNeg d) Complex.I
    (s4_sqrtNeg_ne_neg P.d_pos) (s4_fC_quad P hW)
  rw [← s4_W₁ℂ_eq P hW, ← s4_W₂ℂ_eq P hW] at this
  exact this

theorem s4_fR_bcV (hW : IsCompl P.W₁ P.W₂) (v : V ℚ n) :
    P.fR hW (bcV ℚ ℝ n v) = bcV ℚ ℝ n (P.fη hW v) :=
  s4_extEnd_bcV ℚ ℝ n _ v

theorem s4_fR_fR (hW : IsCompl P.W₁ P.W₂) (x : V ℝ n) :
    P.fR hW (P.fR hW x) = -((d : ℝ) • x) := by
  have h : P.fR hW * P.fR hW = -((d : ℝ) • (1 : Module.End ℝ (V ℝ n))) := by
    show s4_extEnd ℚ ℝ n (P.fη hW) * s4_extEnd ℚ ℝ n (P.fη hW) = _
    rw [← s4_extEnd_mul]
    rw [show P.fη hW * P.fη hW = P.fη hW ∘ₗ P.fη hW from rfl, P.fη_comp_fη hW,
      show (LinearMap.id : V ℚ n →ₗ[ℚ] V ℚ n) = 1 from rfl, s4_extEnd_neg,
      s4_extEnd_smul, s4_extEnd_one]
    rfl
  have := congrArg (fun F => F x) h
  simpa using this

theorem s4_pairing_fR_fR (hW : IsCompl P.W₁ P.W₂) (x y : V ℝ n) :
    pairing ℝ n (P.fR hW x) (P.fR hW y) = d * pairing ℝ n x y := by
  have h : (pairing ℝ n).compl₁₂ (P.fR hW) (P.fR hW) = (d : ℝ) • pairing ℝ n := by
    refine LinearMap.BilinForm.ext_basis (basisV ℝ n) fun i j => ?_
    rw [← s4_bcV_basisV ℚ ℝ n i, ← s4_bcV_basisV ℚ ℝ n j]
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul, s4_fR_bcV,
      s4_pairing_bcV, P.pairing_fη_fη hW]
    push_cast; ring
  have := congrArg (fun B => B x y) h
  simpa using this

theorem s4_pairing_fR_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℝ n) :
    pairing ℝ n (P.fR hW x) y = -pairing ℝ n x (P.fR hW y) := by
  have h : (pairing ℝ n).compl₁₂ (P.fR hW) LinearMap.id =
      -(pairing ℝ n).compl₁₂ LinearMap.id (P.fR hW) := by
    refine LinearMap.BilinForm.ext_basis (basisV ℝ n) fun i j => ?_
    rw [← s4_bcV_basisV ℚ ℝ n i, ← s4_bcV_basisV ℚ ℝ n j]
    simp only [LinearMap.compl₁₂_apply, LinearMap.neg_apply, LinearMap.id_apply, s4_fR_bcV,
      s4_pairing_bcV, P.pairing_fη_left hW]
    push_cast; ring
  have := congrArg (fun B => B x y) h
  simpa using this

/-- `a + √-d b = 0` with `a, b ∈ ℚ` forces `a = b = 0` (`d > 0`). -/
theorem s4_rat_sqrtNeg_eq_zero (hd : 0 < d) {a b : ℚ}
    (h : algebraMap ℚ (Kd d) a + Kd.sqrtNeg d * algebraMap ℚ (Kd d) b = 0) : a = 0 ∧ b = 0 := by
  have hc := congrArg (fun z : Kd d => (z : ℂ)) h
  simp only [Subfield.coe_add, Subfield.coe_mul, Subfield.coe_zero] at hc
  have h1 : ((algebraMap ℚ (Kd d) a : Kd d) : ℂ) = (a : ℂ) := rfl
  have h2 : ((algebraMap ℚ (Kd d) b : Kd d) : ℂ) = (b : ℂ) := rfl
  have h3 : ((Kd.sqrtNeg d : Kd d) : ℂ) = sqrtNeg d := rfl
  rw [h1, h2, h3] at hc
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp [sqrtNeg] at hre him
  refine ⟨by exact_mod_cast hre, ?_⟩
  rcases him with h | h
  · exact absurd h hs.ne'
  · exact_mod_cast h

/-- The rational part of `a + √-d b` is `a`. -/
theorem s4_ratPart_eq {a b : ℚ} :
    Kd.ratPart d (algebraMap ℚ (Kd d) a + Kd.sqrtNeg d * algebraMap ℚ (Kd d) b) = a := by
  set z := algebraMap ℚ (Kd d) a + Kd.sqrtNeg d * algebraMap ℚ (Kd d) b
  have hspec : ((Kd.ratPartFun d z : ℚ) : ℝ) = (z : ℂ).re :=
    Classical.choose_spec (Kd.exists_ratPart d z)
  have hz : (z : ℂ) = (a : ℂ) + sqrtNeg d * (b : ℂ) := rfl
  rw [hz] at hspec
  have : (Kd.ratPartFun d z : ℝ) = a := by
    rw [hspec]
    simp [sqrtNeg]
  exact_mod_cast this

/-- `n > 0` for a `K`-secant: `S_K` is a line when `n = 0`. -/
theorem s4_n_pos {n : ℕ} {d : ℚ} (P : KSecant n d) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exfalso
    subst h
    have := Module.Finite.of_basis (basisS (Kd d) 0)
    have h1 := P.linIndep.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis (basisS (Kd d) 0)] at h1
    simp at h1
  · exact h

/-- Lemma 3.2.1 for `I` a complex structure commuting with `f` with `dim E(f ∘ I, √d) = 2n` (that
is, `ν(I) = 2n`): the four summands `V^{1,0} ∩ W_{i,ℂ}`, `V^{0,1} ∩ W_{i,ℂ}` are `n`-dimensional.
This is `KSecant.s3_core`, the paper's proof of Lemma 3.2.1 for the general case (TeX 1639–1651),
which uses only that `I` commutes with `f` (for `I ∈ ρ(Spin(V_ℝ)_P)`, Lemma 3.1.1). -/
theorem s4_finrank_four (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hc : I * P.fR hW = P.fR hW * I) (hcs : IsComplexStructure I)
    (hE1 : Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (Real.sqrt d)) = 2 * n) :
    Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) = n ∧ Module.finrank ℂ ↥(V01 n I ⊓ P.W₁ℂ) = n ∧
      Module.finrank ℂ ↥(V10 n I ⊓ P.W₂ℂ) = n ∧ Module.finrank ℂ ↥(V01 n I ⊓ P.W₂ℂ) = n := by
  have hν : P.nu hW I = 2 * n := by rw [nu, hc]; exact hE1
  obtain ⟨h1, h2, h3, h4⟩ := P.s3_core hW I hc hcs hν
  exact ⟨h1, h3, h2, h4⟩

end KSecant

/-! ## Helpers for Lemma 4.0.2: spectral theorem, real powers, continuity -/

section Spectral
variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Spectral theorem for an operator self-adjoint with respect to a positive definite symmetric
form `B`: a `B`-orthonormal basis of eigenvectors. -/
theorem s4_exists_orthonormal_eigenbasis [FiniteDimensional ℝ M] (B : LinearMap.BilinForm ℝ M)
    (hBs : ∀ x y, B x y = B y x)
    (hBpos : ∀ x, x ≠ 0 → 0 < B x x) (P : Module.End ℝ M) (hPs : ∀ x y, B (P x) y = B x (P y)) :
    ∃ (N : ℕ) (b : Module.Basis (Fin N) ℝ M) (lam : Fin N → ℝ),
      (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, P (b i) = lam i • b i := by
  let core : InnerProductSpace.Core ℝ M :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by simp [hBs]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hBpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hBpos x h).ne' hx }
  let : NormedAddCommGroup M := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ M := InnerProductSpace.ofCore core.toCore
  have hinner : ∀ x y : M, inner ℝ x y = B x y := fun x y => rfl
  have hsym : (P : M →ₗ[ℝ] M).IsSymmetric := fun x y => by
    rw [hinner, hinner, hPs]
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℝ M = N := ⟨_, rfl⟩
  set ob := hsym.eigenvectorBasis hN
  refine ⟨N, ob.toBasis, hsym.eigenvalues hN, fun i j => ?_, fun i => ?_⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, ob.inner_eq_ite]
  · rw [OrthonormalBasis.coe_toBasis, hsym.apply_eigenvectorBasis]
    rfl


/-- `P^t = Σᵢ λᵢ^t B(bᵢ, ·) bᵢ` for a `B`-orthonormal eigenbasis `b` of `P` with eigenvalues `λ`. -/
noncomputable def s4_rpowOp (B : LinearMap.BilinForm ℝ M) {N : ℕ} (b : Fin N → M) (lam : Fin N → ℝ)
    (t : ℝ) : Module.End ℝ M :=
  ∑ i, (lam i ^ t) • (B (b i)).smulRight (b i)

section Rpow
variable (B : LinearMap.BilinForm ℝ M) {N : ℕ} (b : Module.Basis (Fin N) ℝ M) (lam : Fin N → ℝ)
  (hon : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
include hon

theorem s4_rpowOp_apply_basis (t : ℝ) (j : Fin N) :
    s4_rpowOp B b lam t (b j) = lam j ^ t • b j := by
  simp only [s4_rpowOp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hon,
    ite_smul, one_smul, zero_smul, smul_zero, smul_ite]
  simp

theorem s4_expand (x : M) : x = ∑ i, B (b i) x • b i := by
  conv_lhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  conv_rhs => rw [← b.sum_repr x]
  rw [map_sum]
  simp only [map_smul, hon, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem s4_rpowOp_mul (s t : ℝ) (hl : ∀ i, 0 < lam i) :
    s4_rpowOp B b lam s * s4_rpowOp B b lam t = s4_rpowOp B b lam (s + t) := by
  refine b.ext fun j => ?_
  rw [Module.End.mul_apply, s4_rpowOp_apply_basis B b lam hon, map_smul,
    s4_rpowOp_apply_basis B b lam hon, s4_rpowOp_apply_basis B b lam hon, smul_smul,
    Real.rpow_add (hl j), mul_comm]

theorem s4_rpowOp_zero : s4_rpowOp B b lam 0 = 1 := by
  refine b.ext fun j => ?_
  rw [s4_rpowOp_apply_basis B b lam hon, Real.rpow_zero, one_smul, Module.End.one_apply]

theorem s4_rpowOp_one (P : Module.End ℝ M) (hP : ∀ i, P (b i) = lam i • b i) :
    s4_rpowOp B b lam 1 = P := by
  refine b.ext fun j => ?_
  rw [s4_rpowOp_apply_basis B b lam hon, Real.rpow_one, hP]

omit hon in
theorem s4_rpowOp_symm (hBs : ∀ x y, B x y = B y x) (t : ℝ) (x y : M) :
    B (s4_rpowOp B b lam t x) y = B x (s4_rpowOp B b lam t y) := by
  simp only [s4_rpowOp, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hBs x (b i)]
  ring

theorem s4_rpowOp_pos (t : ℝ) (hl : ∀ i, 0 < lam i) (x : M)
    (hx : x ≠ 0) : 0 < B (s4_rpowOp B b lam t x) x := by
  have hsum : B (s4_rpowOp B b lam t x) x = ∑ i, lam i ^ t * (B (b i) x) ^ 2 := by
    simp only [s4_rpowOp, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  obtain ⟨i₀, hi₀⟩ : ∃ i, B (b i) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by rw [s4_expand B b hon x]; simp [h])
  calc (0 : ℝ) < lam i₀ ^ t * (B (b i₀) x) ^ 2 :=
        mul_pos (Real.rpow_pos_of_pos (hl i₀) t) (by positivity)
    _ ≤ ∑ i, lam i ^ t * (B (b i) x) ^ 2 :=
        Finset.single_le_sum (f := fun i => lam i ^ t * (B (b i) x) ^ 2)
          (fun i _ => mul_nonneg (Real.rpow_nonneg (hl i).le t) (sq_nonneg _))
          (Finset.mem_univ i₀)

/-- On an eigenvector of `P` with eigenvalue `μ`, `P^t` acts by `μ^t`. -/
theorem s4_rpowOp_eigen (P : Module.End ℝ M) (hP : ∀ i, P (b i) = lam i • b i) (t μ : ℝ) (y : M)
    (hy : P y = μ • y) : s4_rpowOp B b lam t y = μ ^ t • y := by
  have hc : ∀ i, B (b i) y * (lam i - μ) = 0 := by
    intro i
    have h1 : B (b i) (P y) = lam i * B (b i) y := by
      conv_lhs => rw [s4_expand B b hon y]
      rw [map_sum, map_sum]
      simp only [map_smul, hP, smul_eq_mul, hon, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]; simp; ring
    rw [hy, map_smul, smul_eq_mul] at h1
    linarith
  conv_lhs => rw [s4_expand B b hon y]
  conv_rhs => rw [s4_expand B b hon y]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, s4_rpowOp_apply_basis B b lam hon, smul_smul, smul_smul]
  rcases mul_eq_zero.mp (hc i) with h | h
  · rw [h]; simp
  · rw [show lam i = μ by linarith, mul_comm]

/-- `P^t` commutes with every operator commuting with `P`. -/
theorem s4_rpowOp_comm (P : Module.End ℝ M) (hP : ∀ i, P (b i) = lam i • b i) (t : ℝ)
    (A : Module.End ℝ M) (hA : A * P = P * A) :
    A * s4_rpowOp B b lam t = s4_rpowOp B b lam t * A := by
  refine b.ext fun j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, s4_rpowOp_apply_basis B b lam hon, map_smul]
  refine (s4_rpowOp_eigen B b lam hon P hP t (lam j) (A (b j)) ?_).symm
  have := congrArg (fun F => F (b j)) hA
  simp only [Module.End.mul_apply, hP, map_smul] at this
  exact this.symm

/-- If `A` maps each eigenvector `bⱼ` of `P` to an eigenvector with the inverse eigenvalue, then
`P^t A = A P^{-t}`. -/
theorem s4_rpowOp_comm_inv (P : Module.End ℝ M) (hP : ∀ i, P (b i) = lam i • b i)
    (hl : ∀ i, 0 < lam i) (t : ℝ) (A : Module.End ℝ M)
    (hA : ∀ j, P (A (b j)) = (lam j)⁻¹ • A (b j)) :
    s4_rpowOp B b lam t * A = A * s4_rpowOp B b lam (-t) := by
  refine b.ext fun j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, s4_rpowOp_apply_basis B b lam hon, map_smul,
    s4_rpowOp_eigen B b lam hon P hP t _ _ (hA j), Real.inv_rpow (hl j).le,
    Real.rpow_neg (hl j).le]

end Rpow

end Spectral


/-- A `(·,·)_V`-definite subspace of `V_ℝ` has dimension `≤ 2n`: it meets the isotropic subspace
`0 × H¹` trivially. -/
theorem s4_finrank_le_of_definite {n : ℕ} (U : Submodule ℝ (V ℝ n))
    (hU : ∀ x ∈ U, x ≠ 0 → pairing ℝ n x x ≠ 0) : Module.finrank ℝ U ≤ 2 * n := by
  set L := LinearMap.range (LinearMap.inr ℝ (Module.Dual ℝ (H1 ℝ n)) (H1 ℝ n)) with hL_def
  have hL : Module.finrank ℝ L = 2 * n := by
    rw [hL_def, LinearMap.finrank_range_of_inj LinearMap.inr_injective]
    simp
  have hdisj : U ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, v, rfl⟩
    rw [Submodule.mem_bot]
    by_contra h
    apply hU _ hxU h
    simp [pairing]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U L
  have h2 := Submodule.finrank_le (U ⊔ L)
  rw [hdisj, finrank_bot, hL] at h1
  have h3 : Module.finrank ℝ (V ℝ n) = 2 * n + 2 * n := by
    rw [Module.finrank_eq_card_basis (basisV ℝ n), Fintype.card_fin]
  omega


/-! ### Continuity for the Euclidean topology of `End(V_ℝ)` -/

theorem s4_continuous_sum_smul {n N : ℕ} (c : Fin N → ℝ → ℝ) (hc : ∀ i, Continuous (c i))
    (A : Fin N → Module.End ℝ (V ℝ n)) :
    @Continuous _ _ _ (endTopology n) (fun t => ∑ i, c i t • A i) := by
  let := endTopology n
  rw [continuous_induced_rng]
  have : (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ (fun t => ∑ i, c i t • A i) =
      fun t => ∑ i, c i t • LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) (A i) := by
    funext t
    simp only [Function.comp_apply, map_sum, map_smul]
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hc i).smul continuous_const

theorem s4_continuous_mul_left {n : ℕ} {α : Type*} [TopologicalSpace α]
    (A : Module.End ℝ (V ℝ n)) {g : α → Module.End ℝ (V ℝ n)}
    (hg : @Continuous _ _ _ (endTopology n) g) :
    @Continuous _ _ _ (endTopology n) (fun t => A * g t) := by
  let := endTopology n
  rw [continuous_induced_rng] at hg ⊢
  have : (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ (fun t => A * g t) =
      fun t => LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) A *
        ((LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ g) t := by
    funext t
    simp only [Function.comp_apply, LinearMap.toMatrix_mul]
  rw [this]
  exact continuous_const.matrix_mul hg

theorem s4_continuous_smul {n : ℕ} {α : Type*} [TopologicalSpace α] (c : ℝ)
    {g : α → Module.End ℝ (V ℝ n)} (hg : @Continuous _ _ _ (endTopology n) g) :
    @Continuous _ _ _ (endTopology n) (fun t => c • g t) := by
  let := endTopology n
  rw [continuous_induced_rng] at hg ⊢
  have : (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ (fun t => c • g t) =
      fun t => c • ((LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ g) t := by
    funext t
    simp only [Function.comp_apply, map_smul]
  rw [this]
  exact hg.const_smul c


/-! ## Helpers for Lemma 4.0.1: the inverse of `ι` and the topology of `Gr(n, W_{1,ℂ})` -/

section ProjAlg
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- `A(P) = P H P + 1 - P`. -/
noncomputable def s4_AOp (P H : E →L[ℂ] E) : E →L[ℂ] E := P * H * P + 1 - P

/-- `Pi'(P) = A(P)⁻¹ P H`; for `P` the orthogonal projection onto `U`, the projection onto `U`
orthogonal for the sesquilinear form `(x, y) ↦ ⟪y, H x⟫`. -/
noncomputable def s4_PiOp (P H : E →L[ℂ] E) : E →L[ℂ] E := Ring.inverse (s4_AOp P H) * P * H

theorem s4_starProjection_mul_self (U : Submodule ℂ E) :
    U.starProjection * U.starProjection = U.starProjection :=
  (Submodule.isIdempotentElem_starProjection U).eq

theorem s4_PiOp_props (U : Submodule ℂ E) (H : E →L[ℂ] E)
    (hA : IsUnit (s4_AOp U.starProjection H)) :
    (∀ x, s4_PiOp U.starProjection H x ∈ U) ∧
    (∀ u ∈ U, s4_PiOp U.starProjection H u = u) ∧
    (∀ x, ∀ u ∈ U, inner ℂ u (H (x - s4_PiOp U.starProjection H x)) = 0) ∧
    (∀ x, (∀ u ∈ U, inner ℂ u (H x) = 0) → s4_PiOp U.starProjection H x = 0) := by
  set P := U.starProjection with hP
  have hPP : P * P = P := s4_starProjection_mul_self U
  obtain ⟨a, ha⟩ := hA
  set A := s4_AOp P H with hA_def
  have hinv : Ring.inverse A = ((a⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) := by
    rw [← ha, Ring.inverse_unit]
  have hAinvA : Ring.inverse A * A = 1 := by rw [hinv, ← ha, Units.inv_mul]
  have hAAinv : A * Ring.inverse A = 1 := by rw [hinv, ← ha, Units.mul_inv]
  have h1 : (1 - P) * A = 1 - P := by
    rw [hA_def, s4_AOp]
    have e1 : (1 - P) * (P * H * P) = 0 := by
      rw [sub_mul, one_mul, ← mul_assoc, ← mul_assoc, hPP, sub_self]
    have e2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
    rw [mul_sub, mul_add, e1, e2, zero_add, mul_one, sub_zero]
  have h2 : (1 - P) * Ring.inverse A = 1 - P := by
    calc (1 - P) * Ring.inverse A = (1 - P) * A * Ring.inverse A := by rw [h1]
      _ = 1 - P := by rw [mul_assoc, hAAinv, mul_one]
  set Pi' := Ring.inverse A * P * H with hPi'
  have hPPi' : P * Pi' = Pi' := by
    have : (1 - P) * Pi' = 0 := by
      rw [hPi', ← mul_assoc, ← mul_assoc, h2, sub_mul, one_mul, hPP, sub_self, zero_mul]
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this.symm
  have hAP : A * P = P * H * P := by
    rw [hA_def, s4_AOp, sub_mul, add_mul, one_mul, mul_assoc (P * H), hPP, add_sub_cancel_right]
  have hPi'P : Pi' * P = P := by
    rw [hPi', mul_assoc, mul_assoc, ← mul_assoc P, ← hAP, ← mul_assoc, hAinvA, one_mul]
  have hAPi' : A * Pi' = P * H := by
    rw [hPi', ← mul_assoc, ← mul_assoc, hAAinv, one_mul]
  have hPHPi' : P * H * Pi' = P * H := by
    have : A * Pi' = P * H * Pi' := by
      rw [hA_def, s4_AOp, sub_mul, add_mul, one_mul, mul_assoc (P * H), hPPi', add_sub_cancel_right]
    rw [← this, hAPi']
  refine ⟨fun x => ?_, fun u hu => ?_, fun x u hu => ?_, fun x hx => ?_⟩
  · have : Pi' x = P (Pi' x) := by
      rw [← mul_apply_eq_comp, hPPi']
    show Pi' x ∈ U
    rw [this]
    exact Submodule.starProjection_apply_mem U _
  · have hPu : P u = u := Submodule.starProjection_eq_self_iff.mpr hu
    show Pi' u = u
    conv_lhs => rw [← hPu]
    rw [← mul_apply_eq_comp, hPi'P, hPu]
  · have hPu : P u = u := Submodule.starProjection_eq_self_iff.mpr hu
    have h0 : P (H (x - Pi' x)) = 0 := by
      have := congrArg (fun F : E →L[ℂ] E => F x) hPHPi'
      simp only [mul_apply_eq_comp] at this
      rw [map_sub, map_sub, this, sub_self]
    have h0' : U.starProjection (H (x - Pi' x)) = 0 := h0
    show inner ℂ u (H (x - Pi' x)) = 0
    rw [← hPu, Submodule.inner_starProjection_left_eq_right, h0', inner_zero_right]
  · have h0 : P (H x) = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      intro u hu
      exact hx u hu
    show Pi' x = 0
    rw [hPi', mul_apply_eq_comp, mul_apply_eq_comp, h0, map_zero]

/-- `A(P_U)` is invertible when `⟪u, H u⟫ ≠ 0` for `0 ≠ u ∈ U`. -/
theorem s4_isUnit_AOp (U : Submodule ℂ E) (H : E →L[ℂ] E)
    (hpos : ∀ u ∈ U, u ≠ 0 → inner ℂ u (H u) ≠ 0) : IsUnit (s4_AOp U.starProjection H) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro x hx
  set P := U.starProjection with hP
  have hAx : P (H (P x)) + (x - P x) = 0 := by
    have : s4_AOp P H x = 0 := hx
    rw [s4_AOp] at this
    simp only [sub_apply, add_apply,
      mul_apply_eq_comp, one_apply_eq_self] at this
    rw [← this]
    abel
  have hv : x - P x = 0 := by
    have hperp : x - P x ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hin : inner ℂ (x - P x) (P (H (P x))) = 0 :=
      (Submodule.mem_orthogonal' U _).mp hperp _ (Submodule.starProjection_apply_mem U _)
    have : inner ℂ (x - P x) (x - P x) = 0 := by
      have h := congrArg (fun z => inner ℂ (x - P x) z) hAx
      simp only [inner_add_right, hin, zero_add, inner_zero_right] at h
      exact h
    exact inner_self_eq_zero.mp this
  have hxU : x = P x := (sub_eq_zero.mp hv)
  have hPH : P (H (P x)) = 0 := by rw [hv, add_zero] at hAx; exact hAx
  by_contra hx0
  have hPx0 : P x ≠ 0 := by rw [← hxU]; exact hx0
  apply hpos (P x) (Submodule.starProjection_apply_mem U x) hPx0
  have hPP : P (P x) = P x := Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem U x)
  rw [← hPP, Submodule.inner_starProjection_left_eq_right, hPP, hPH, inner_zero_right]

/-- `‖y - π_U y‖ ≤ ‖y - u‖` for `u ∈ U`. -/
theorem s4_norm_sub_starProjection_le (U : Submodule ℂ E) (y u : E) (hu : u ∈ U) :
    ‖y - U.starProjection y‖ ≤ ‖y - u‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨u, hu⟩ : U)

/-- Two orthogonal projections are close when the subspaces are the images of close operators
fixing them: `‖π_U - π_{U'}‖ ≤ 2 ‖T - T'‖`. -/
theorem s4_norm_starProjection_sub_le (U U' : Submodule ℂ E) (T T' : E →L[ℂ] E)
    (hT : ∀ x, T x ∈ U) (hT' : ∀ x, T' x ∈ U') (hTU : ∀ u ∈ U, T u = u)
    (hTU' : ∀ u ∈ U', T' u = u) :
    ‖U.starProjection - U'.starProjection‖ ≤ 2 * ‖T - T'‖ := by
  set P := U.starProjection
  set P' := U'.starProjection
  -- distances from `U` to `U'` and back
  have hd1 : ∀ u ∈ U, ‖u - P' u‖ ≤ ‖T - T'‖ * ‖u‖ := by
    intro u hu
    calc ‖u - P' u‖ ≤ ‖u - T' u‖ := s4_norm_sub_starProjection_le U' u _ (hT' u)
      _ = ‖(T - T') u‖ := by rw [sub_apply, hTU u hu]
      _ ≤ ‖T - T'‖ * ‖u‖ := (T - T').le_opNorm u
  have hd2 : ∀ u ∈ U', ‖u - P u‖ ≤ ‖T - T'‖ * ‖u‖ := by
    intro u hu
    calc ‖u - P u‖ ≤ ‖u - T u‖ := s4_norm_sub_starProjection_le U u _ (hT u)
      _ = ‖(T - T') u‖ := by
          rw [sub_apply, hTU' u hu, ← norm_neg, neg_sub]
      _ ≤ ‖T - T'‖ * ‖u‖ := (T - T').le_opNorm u
  have hle : ∀ x, ‖x - P x‖ ≤ ‖x‖ := fun x => by
    simpa using s4_norm_sub_starProjection_le U x 0 (zero_mem U)
  have hPle : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by
    simpa using Submodule.norm_starProjection_apply_le U x
  -- `‖π_{U'} w‖ ≤ ‖T - T'‖ ‖w‖` for `w ⊥ U`
  have hw : ∀ w ∈ Uᗮ, ‖P' w‖ ≤ ‖T - T'‖ * ‖w‖ := by
    intro w hwU
    set v := P' w
    have hvU' : v ∈ U' := Submodule.starProjection_apply_mem U' w
    have hsq : ‖v‖ ^ 2 = RCLike.re (inner ℂ (v - P v) w) := by
      have h1 : inner ℂ (P v) w = 0 :=
        (Submodule.mem_orthogonal' U w).mp hwU _ (Submodule.starProjection_apply_mem U v) |>
          fun h => by rw [inner_eq_zero_symm]; exact h
      have h2 : inner ℂ v w = inner ℂ v v := by
        have hvv : P' v = v := Submodule.starProjection_eq_self_iff.mpr hvU'
        calc inner ℂ v w = inner ℂ (P' v) w := by rw [hvv]
          _ = inner ℂ v (P' w) := by rw [Submodule.inner_starProjection_left_eq_right]
          _ = inner ℂ v v := rfl
      rw [inner_sub_left, h1, sub_zero, h2, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    have hb : ‖v‖ ^ 2 ≤ (‖T - T'‖ * ‖v‖) * ‖w‖ := by
      rw [hsq]
      calc RCLike.re (inner ℂ (v - P v) w) ≤ ‖inner ℂ (v - P v) w‖ := RCLike.re_le_norm _
        _ ≤ ‖v - P v‖ * ‖w‖ := norm_inner_le_norm _ _
        _ ≤ (‖T - T'‖ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (hd2 v hvU') (norm_nonneg _)
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
    · rw [← h0]; positivity
    · have : ‖v‖ * ‖v‖ ≤ ‖v‖ * (‖T - T'‖ * ‖w‖) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hsplit : (P - P') x = (P x - P' (P x)) - P' (x - P x) := by
    rw [sub_apply, map_sub]
    abel
  rw [hsplit]
  have hxw : x - P x ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal x
  calc ‖(P x - P' (P x)) - P' (x - P x)‖ ≤ ‖P x - P' (P x)‖ + ‖P' (x - P x)‖ := norm_sub_le _ _
    _ ≤ ‖T - T'‖ * ‖P x‖ + ‖T - T'‖ * ‖x - P x‖ :=
        add_le_add (hd1 _ (Submodule.starProjection_apply_mem U x)) (hw _ hxw)
    _ ≤ ‖T - T'‖ * ‖x‖ + ‖T - T'‖ * ‖x‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hPle x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg _))
    _ = 2 * ‖T - T'‖ * ‖x‖ := by ring

end ProjAlg

section Herm
variable (n : ℕ)

theorem s4_pairing_bcV_RC (x y : V ℝ n) :
    pairing ℂ n (bcV ℝ ℂ n x) (bcV ℝ ℂ n y) = (pairing ℝ n x y : ℂ) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    ← map_sub, Q_bcV]
  simp

theorem s4_pairing_symm_C (a b : V ℂ n) : pairing ℂ n a b = pairing ℂ n b a :=
  QuadraticMap.polar_comm _ a b

theorem s4_conjL_eq (a : V ℂ n) :
    s4_conjL n a = bcV ℝ ℂ n (s4_reV n a) - Complex.I • bcV ℝ ℂ n (s4_imV n a) := by
  conv_lhs => rw [← s4_bcV_re_add_im n a]
  rw [map_add, map_smulₛₗ, s4_conjL_bcV, s4_conjL_bcV, Complex.conj_I, neg_smul,
    ← sub_eq_add_neg]

theorem s4_pairing_conjL (a b : V ℂ n) :
    pairing ℂ n (s4_conjL n a) (s4_conjL n b) = (starRingEnd ℂ) (pairing ℂ n a b) := by
  rw [s4_conjL_eq, s4_conjL_eq]
  conv_rhs => rw [← s4_bcV_re_add_im n a, ← s4_bcV_re_add_im n b]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, s4_pairing_bcV_RC, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- The Hermitian form `h(x, y) = (x, ȳ)_V` on `V_ℂ`. -/
noncomputable def s4_hV (x y : V ℂ n) : ℂ := pairing ℂ n x (s4_conjL n y)

theorem s4_hV_conj_symm (x y : V ℂ n) : s4_hV n y x = (starRingEnd ℂ) (s4_hV n x y) := by
  rw [s4_hV, s4_hV, ← s4_pairing_conjL, s4_conjL_conjL, s4_pairing_symm_C]

theorem s4_hV_add_left (x x' y : V ℂ n) : s4_hV n (x + x') y = s4_hV n x y + s4_hV n x' y := by
  simp [s4_hV]

theorem s4_hV_sub_left (x x' y : V ℂ n) : s4_hV n (x - x') y = s4_hV n x y - s4_hV n x' y := by
  simp [s4_hV]

theorem s4_hV_smul_left (c : ℂ) (x y : V ℂ n) : s4_hV n (c • x) y = c * s4_hV n x y := by
  simp [s4_hV]

theorem s4_hV_add_right (x y y' : V ℂ n) : s4_hV n x (y + y') = s4_hV n x y + s4_hV n x y' := by
  simp [s4_hV]

theorem s4_hV_sub_right (x y y' : V ℂ n) : s4_hV n x (y - y') = s4_hV n x y - s4_hV n x y' := by
  simp [s4_hV]

theorem s4_hV_smul_right (c : ℂ) (x y : V ℂ n) :
    s4_hV n x (c • y) = (starRingEnd ℂ) c * s4_hV n x y := by
  simp [s4_hV, map_smulₛₗ]

theorem s4_hV_zero_left (y : V ℂ n) : s4_hV n 0 y = 0 := by simp [s4_hV]

theorem s4_hV_zero_right (x : V ℂ n) : s4_hV n x 0 = 0 := by simp [s4_hV]

theorem s4_hV_bcV (x y : V ℝ n) : s4_hV n (bcV ℝ ℂ n x) (bcV ℝ ℂ n y) = (pairing ℝ n x y : ℂ) := by
  rw [s4_hV, s4_conjL_bcV, s4_pairing_bcV_RC]

theorem s4_hV_self (u : V ℂ n) : s4_hV n u u =
    ((pairing ℝ n (s4_reV n u) (s4_reV n u) + pairing ℝ n (s4_imV n u) (s4_imV n u) : ℝ) : ℂ) := by
  have hu := s4_bcV_re_add_im n u
  rw [s4_hV, s4_conjL_eq]
  set a := s4_reV n u
  set b := s4_imV n u
  rw [← hu]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, s4_pairing_bcV_RC]
  rw [show pairing ℝ n b a = pairing ℝ n a b from QuadraticMap.polar_comm _ _ _]
  push_cast
  linear_combination (-((pairing ℝ n b b : ℝ) : ℂ)) * Complex.I_mul_I

/-! ### The Euclidean coordinates `eucV` and the operator `H` representing `h` -/

theorem s4_eucV_apply (x : V ℂ n) (j : Fin (2 * n + 2 * n)) :
    eucV n x j = (basisV ℂ n).repr x j := rfl

theorem s4_inner_eucV (x y : V ℂ n) :
    inner ℂ (eucV n x) (eucV n y) =
      ∑ j, (starRingEnd ℂ) ((basisV ℂ n).repr x j) * (basisV ℂ n).repr y j := by
  simp [PiLp.inner_apply, s4_eucV_apply, mul_comm]

/-- The operator of `V_ℂ` representing `h` in the coordinates `basisV`. -/
noncomputable def s4_HV : V ℂ n →ₗ[ℂ] V ℂ n :=
  ∑ j, ((pairing ℂ n).flip (basisV ℂ n j)).smulRight (basisV ℂ n j)

theorem s4_repr_HV (x : V ℂ n) (j : Fin (2 * n + 2 * n)) :
    (basisV ℂ n).repr (s4_HV n x) j = pairing ℂ n x (basisV ℂ n j) := by
  simp only [s4_HV, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem s4_conjL_sum (y : V ℂ n) :
    s4_conjL n y = ∑ j, (starRingEnd ℂ) ((basisV ℂ n).repr y j) • basisV ℂ n j := by
  conv_lhs => rw [← (basisV ℂ n).sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smulₛₗ, ← s4_bcV_basisV ℝ ℂ n, s4_conjL_bcV]

theorem s4_inner_HV (x y : V ℂ n) :
    inner ℂ (eucV n y) (eucV n (s4_HV n x)) = s4_hV n x y := by
  rw [s4_inner_eucV, s4_hV, s4_conjL_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, s4_repr_HV]

/-- `H` on the Euclidean space `ℂ^{4n}`. -/
noncomputable def s4_HE : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n)) :=
  LinearMap.toContinuousLinearMap
    ((eucV n).toLinearMap ∘ₗ s4_HV n ∘ₗ (eucV n).symm.toLinearMap)

theorem s4_HE_eucV (x : V ℂ n) : s4_HE n (eucV n x) = eucV n (s4_HV n x) := by
  simp [s4_HE]

theorem s4_inner_HE (x y : V ℂ n) :
    inner ℂ (eucV n y) (s4_HE n (eucV n x)) = s4_hV n x y := by
  rw [s4_HE_eucV, s4_inner_HV]

/-- The `h`-orthogonal projection onto `U` (when `A(π_U)` is invertible), on `V_ℂ`. -/
noncomputable def s4_PiV (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) : V ℂ n →ₗ[ℂ] V ℂ n :=
  (eucV n).symm.toLinearMap ∘ₗ (s4_PiOp T (s4_HE n)).toLinearMap ∘ₗ (eucV n).toLinearMap

theorem s4_PiV_props (U : Submodule ℂ (V ℂ n)) (hA : IsUnit (s4_AOp (projV U) (s4_HE n))) :
    (∀ y, s4_PiV n (projV U) y ∈ U) ∧ (∀ u ∈ U, s4_PiV n (projV U) u = u) ∧
    (∀ y, ∀ u ∈ U, s4_hV n (y - s4_PiV n (projV U) y) u = 0) ∧
    (∀ y, (∀ u ∈ U, s4_hV n y u = 0) → s4_PiV n (projV U) y = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := s4_PiOp_props (U.map (eucV n).toLinearMap) (s4_HE n) hA
  have hPiV : ∀ y, eucV n (s4_PiV n (projV U) y) = s4_PiOp (projV U) (s4_HE n) (eucV n y) :=
    fun y => by simp [s4_PiV]
  refine ⟨fun y => ?_, fun u hu => ?_, fun y u hu => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp (h1 (eucV n y))
    have : z = s4_PiV n (projV U) y := by
      apply (eucV n).injective
      rw [hPiV]
      exact hzy
    rw [← this]
    exact hz
  · apply (eucV n).injective
    rw [hPiV]
    exact h2 _ (Submodule.mem_map_of_mem hu)
  · rw [← s4_inner_HE, map_sub, hPiV]
    exact h3 _ _ (Submodule.mem_map_of_mem hu)
  · apply (eucV n).injective
    rw [hPiV, map_zero]
    apply h4
    rintro _ ⟨u, hu, rfl⟩
    rw [LinearEquiv.coe_coe, s4_inner_HE]
    exact hy u hu

theorem s4_isUnit_AOp_V (U : Submodule ℂ (V ℂ n)) (hpos : ∀ u ∈ U, u ≠ 0 → s4_hV n u u ≠ 0) :
    IsUnit (s4_AOp (projV U) (s4_HE n)) := by
  apply s4_isUnit_AOp
  rintro _ ⟨u, hu, rfl⟩ hu0
  rw [LinearEquiv.coe_coe, s4_inner_HE]
  refine hpos u hu fun h => hu0 ?_
  rw [h, map_zero]

end Herm

section KOp
variable (n : ℕ)

theorem s4_extEnd_re_im (A : Module.End ℝ (V ℝ n)) (a : V ℂ n) :
    s4_extEnd ℝ ℂ n A a =
      bcV ℝ ℂ n (A (s4_reV n a)) + Complex.I • bcV ℝ ℂ n (A (s4_imV n a)) := by
  conv_lhs => rw [← s4_bcV_re_add_im n a]
  rw [map_add, map_smul, s4_extEnd_bcV, s4_extEnd_bcV]

/-- A real identity `(A x, B y)_V = c (x, y)_V` complexifies. -/
theorem s4_pairing_extEnd (A B : Module.End ℝ (V ℝ n)) (c : ℝ)
    (h : ∀ x y, pairing ℝ n (A x) (B y) = c * pairing ℝ n x y) (a b : V ℂ n) :
    pairing ℂ n (s4_extEnd ℝ ℂ n A a) (s4_extEnd ℝ ℂ n B b) = c * pairing ℂ n a b := by
  rw [s4_extEnd_re_im, s4_extEnd_re_im]
  conv_rhs => rw [← s4_bcV_re_add_im n a, ← s4_bcV_re_add_im n b]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    s4_pairing_bcV_RC, h]
  push_cast
  ring

theorem s4_two_bcV_reV (w : V ℂ n) :
    (2 : ℂ) • bcV ℝ ℂ n (s4_reV n w) = w + s4_conjL n w := by
  have hw := s4_bcV_re_add_im n w
  rw [s4_conjL_eq]
  set a := s4_reV n w
  set b := s4_imV n w
  rw [← hw, two_smul]
  abel

/-- The complex conjugate `Π̄ = c ∘ Π ∘ c` of a `ℂ`-linear map of `V_ℂ`. -/
noncomputable def s4_conjOp (A : V ℂ n →ₗ[ℂ] V ℂ n) : V ℂ n →ₗ[ℂ] V ℂ n :=
  (s4_conjL n).toLinearMap.comp (A.comp (s4_conjL n).toLinearMap)

theorem s4_conjOp_apply (A : V ℂ n →ₗ[ℂ] V ℂ n) (y : V ℂ n) :
    s4_conjOp n A y = s4_conjL n (A (s4_conjL n y)) := rfl

/-- `K(T) x = x - 4 Re(Π_T x)` on `V_ℝ`: the Cartan involution with `-1`-eigenspace `U ⊕ Ū` when
`T = π_U`. -/
noncomputable def s4_KOp (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) : Module.End ℝ (V ℝ n) :=
  1 - (4 : ℝ) • ((s4_reV n) ∘ₗ ((s4_PiV n T).restrictScalars ℝ) ∘ₗ (bcV ℝ ℂ n))

theorem s4_bcV_KOp (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) (x : V ℝ n) :
    bcV ℝ ℂ n (s4_KOp n T x) = bcV ℝ ℂ n x - (2 : ℂ) • s4_PiV n T (bcV ℝ ℂ n x) -
      (2 : ℂ) • s4_conjL n (s4_PiV n T (bcV ℝ ℂ n x)) := by
  have h2 := s4_two_bcV_reV n (s4_PiV n T (bcV ℝ ℂ n x))
  simp only [s4_KOp, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, LinearMap.map_smul_of_tower]
  rw [show (4 : ℝ) • bcV ℝ ℂ n (s4_reV n (s4_PiV n T (bcV ℝ ℂ n x))) =
      (2 : ℂ) • ((2 : ℂ) • bcV ℝ ℂ n (s4_reV n (s4_PiV n T (bcV ℝ ℂ n x)))) by
    rw [smul_smul, show (4 : ℝ) • bcV ℝ ℂ n (s4_reV n (s4_PiV n T (bcV ℝ ℂ n x))) =
      ((4 : ℝ) : ℂ) • bcV ℝ ℂ n (s4_reV n (s4_PiV n T (bcV ℝ ℂ n x))) from
      (Complex.coe_smul _ _).symm]
    norm_num, h2, smul_add]
  abel

/-- The complexification of `K(T)`: `1 - 2 Π - 2 Π̄`. -/
theorem s4_extEnd_KOp (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) :
    s4_extEnd ℝ ℂ n (s4_KOp n T) =
      1 - (2 : ℂ) • s4_PiV n T - (2 : ℂ) • s4_conjOp n (s4_PiV n T) := by
  refine (basisV ℂ n).ext fun j => ?_
  rw [← s4_bcV_basisV ℝ ℂ n, s4_extEnd_bcV, s4_bcV_KOp]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, s4_conjOp_apply,
    s4_conjL_bcV]

end KOp

section PiGen
variable (n : ℕ) (U : Submodule ℂ (V ℂ n)) (hA : IsUnit (s4_AOp (projV U) (s4_HE n)))
include hA

theorem s4_PiV_idem (y : V ℂ n) :
    s4_PiV n (projV U) (s4_PiV n (projV U) y) = s4_PiV n (projV U) y :=
  (s4_PiV_props n U hA).2.1 _ ((s4_PiV_props n U hA).1 y)

theorem s4_conjOp_idem (y : V ℂ n) :
    s4_conjOp n (s4_PiV n (projV U)) (s4_conjOp n (s4_PiV n (projV U)) y) =
      s4_conjOp n (s4_PiV n (projV U)) y := by
  rw [s4_conjOp_apply, s4_conjOp_apply, s4_conjL_conjL, s4_PiV_idem n U hA]

/-- `Π` is self-adjoint for `h`. -/
theorem s4_hV_PiV (a c : V ℂ n) :
    s4_hV n (s4_PiV n (projV U) a) c = s4_hV n a (s4_PiV n (projV U) c) := by
  obtain ⟨h1, -, h3, -⟩ := s4_PiV_props n U hA
  set Pv := s4_PiV n (projV U)
  have e1 : s4_hV n (Pv a) (c - Pv c) = 0 := by
    rw [s4_hV_conj_symm, h3 c _ (h1 a), map_zero]
  have e2 : s4_hV n (a - Pv a) (Pv c) = 0 := h3 a _ (h1 c)
  rw [s4_hV_sub_right, sub_eq_zero] at e1
  rw [s4_hV_sub_left, sub_eq_zero] at e2
  rw [e1, e2]

/-- `M = Π + Π̄` is self-adjoint for `(·,·)_V`. -/
theorem s4_pairing_M (a b : V ℂ n) :
    pairing ℂ n (s4_PiV n (projV U) a + s4_conjOp n (s4_PiV n (projV U)) a) b =
      pairing ℂ n a (s4_PiV n (projV U) b + s4_conjOp n (s4_PiV n (projV U)) b) := by
  set Pv := s4_PiV n (projV U)
  have e1 : pairing ℂ n (Pv a) b = pairing ℂ n a (s4_conjOp n Pv b) := by
    have := s4_hV_PiV n U hA a (s4_conjL n b)
    simp only [s4_hV, s4_conjL_conjL] at this
    rw [this, s4_conjOp_apply]
  have e2 : pairing ℂ n (s4_conjOp n Pv a) b = pairing ℂ n a (Pv b) := by
    have := s4_hV_PiV n U hA b (s4_conjL n a)
    simp only [s4_hV, s4_conjL_conjL] at this
    rw [s4_conjOp_apply, s4_pairing_symm_C, ← this, s4_pairing_symm_C]
  rw [map_add, LinearMap.add_apply, e1, e2, map_add, add_comm]

end PiGen

section Topo
variable (n : ℕ)
open scoped Matrix Topology

theorem s4_pairing_equivFun (y z : Fin (2 * n + 2 * n) → ℝ) :
    pairing ℝ n ((basisV ℝ n).equivFun.symm y) ((basisV ℝ n).equivFun.symm z) =
      ∑ i, ∑ j, y i * z j * pairing ℝ n (basisV ℝ n i) (basisV ℝ n j) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem s4_apply_equivFun (K : Module.End ℝ (V ℝ n)) (y : Fin (2 * n + 2 * n) → ℝ) :
    K ((basisV ℝ n).equivFun.symm y) =
      (basisV ℝ n).equivFun.symm (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) K *ᵥ y) := by
  apply (basisV ℝ n).equivFun.injective
  rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr (basisV ℝ n) (basisV ℝ n)]
  congr 1
  ext i
  simp [Finsupp.single_apply]

/-- Negative definiteness of `x ↦ (x, K x)_V` is an open condition on `K`. -/
theorem s4_eventually_neg (K₀ : Module.End ℝ (V ℝ n))
    (h₀ : ∀ x, x ≠ 0 → pairing ℝ n x (K₀ x) < 0) :
    ∀ᶠ K in @nhds _ (endTopology n) K₀, ∀ x, x ≠ 0 → pairing ℝ n x (K x) < 0 := by
  let := endTopology n
  set e := (basisV ℝ n).equivFun.symm with he
  set M := LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) with hM
  set G : Fin (2 * n + 2 * n) → Fin (2 * n + 2 * n) → ℝ :=
    fun i j => pairing ℝ n (basisV ℝ n i) (basisV ℝ n j)
  set φ : Module.End ℝ (V ℝ n) × (Fin (2 * n + 2 * n) → ℝ) → ℝ :=
    fun p => ∑ i, ∑ j, p.2 i * (M p.1 *ᵥ p.2) j * G i j with hφ_def
  have hφ : ∀ K y, φ (K, y) = pairing ℝ n (e y) (K (e y)) := by
    intro K y
    rw [s4_apply_equivFun, s4_pairing_equivFun]
  have hMc : Continuous (fun p : Module.End ℝ (V ℝ n) × (Fin (2 * n + 2 * n) → ℝ) => M p.1) :=
    continuous_induced_dom.comp continuous_fst
  have hφc : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply i).comp continuous_snd).mul
      ((continuous_apply j).comp (hMc.matrix_mulVec continuous_snd))).mul continuous_const
  have hS : IsCompact (Metric.sphere (0 : Fin (2 * n + 2 * n) → ℝ) 1) := isCompact_sphere 0 1
  have hev : ∀ᶠ K in 𝓝 K₀, ∀ y ∈ Metric.sphere (0 : Fin (2 * n + 2 * n) → ℝ) 1, φ (K, y) < 0 := by
    refine hS.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy
      exact zero_ne_one hy
    have hey : e y ≠ 0 := fun h => hy0 (by simpa using congrArg (basisV ℝ n).equivFun h)
    have hlt : φ (K₀, y) < 0 := by rw [hφ]; exact h₀ _ hey
    exact hφc.continuousAt.eventually (Iio_mem_nhds hlt)
  refine hev.mono fun K hK x hx => ?_
  set c := (basisV ℝ n).equivFun x with hc
  have hc0 : c ≠ 0 := fun h => hx (by
    have := congrArg e h
    rwa [hc, he, LinearEquiv.symm_apply_apply, map_zero] at this)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  set y := ‖c‖⁻¹ • c
  have hy : y ∈ Metric.sphere (0 : Fin (2 * n + 2 * n) → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn.ne']
  have h1 := hK y hy
  rw [hφ] at h1
  have hex : e y = ‖c‖⁻¹ • x := by
    rw [map_smul, hc, he, LinearEquiv.symm_apply_apply]
  rw [hex, map_smul, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h1
  have hpos : 0 < ‖c‖⁻¹ * ‖c‖⁻¹ := by positivity
  nlinarith

theorem s4_toMatrix_KOp (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) (i j : Fin (2 * n + 2 * n)) :
    LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) (s4_KOp n T) i j =
      Finsupp.single j (1 : ℝ) i - 4 * ((s4_PiOp T (s4_HE n)) (eucV n (basisV ℂ n j)) i).re := by
  rw [LinearMap.toMatrix_apply]
  simp only [s4_KOp, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, map_smul, Finsupp.sub_apply,
    Finsupp.smul_apply, s4_repr_reV, Module.Basis.repr_self, s4_bcV_basisV, smul_eq_mul]
  rw [← s4_eucV_apply]
  simp [s4_PiV]

theorem s4_continuousAt_PiOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (H T₀ : E →L[ℂ] E) (hA : IsUnit (s4_AOp T₀ H)) :
    ContinuousAt (fun T => s4_PiOp T H) T₀ := by
  have hAc : Continuous (fun T : E →L[ℂ] E => s4_AOp T H) := by
    unfold s4_AOp
    exact (((continuous_id.mul continuous_const).mul continuous_id).add continuous_const).sub
      continuous_id
  obtain ⟨u, hu⟩ := hA
  have hinv : ContinuousAt (fun T => Ring.inverse (s4_AOp T H)) T₀ := by
    have := NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_of_eq this hAc.continuousAt hu.symm
  exact (hinv.mul continuousAt_id).mul continuousAt_const

open scoped Topology in
theorem s4_eventually_isUnit_AOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (H T₀ : E →L[ℂ] E) (hA : IsUnit (s4_AOp T₀ H)) :
    ∀ᶠ T in 𝓝 T₀, IsUnit (s4_AOp T H) := by
  have hAc : Continuous (fun T : E →L[ℂ] E => s4_AOp T H) := by
    unfold s4_AOp
    exact (((continuous_id.mul continuous_const).mul continuous_id).add continuous_const).sub
      continuous_id
  exact hAc.continuousAt.eventually (Units.isOpen.mem_nhds hA)

theorem s4_continuousAt_KOp (T₀ : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) (hA : IsUnit (s4_AOp T₀ (s4_HE n))) :
    ContinuousAt (fun T => LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) (s4_KOp n T)) T₀ := by
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  simp only [s4_toMatrix_KOp]
  have hev : Continuous (fun F : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
      EuclideanSpace ℂ (Fin (2 * n + 2 * n)) => ((F (eucV n (basisV ℂ n j))) i).re) :=
    Complex.continuous_re.comp ((EuclideanSpace.proj i).continuous.comp (continuous_eval_const _))
  exact continuousAt_const.sub (continuousAt_const.mul
    (hev.continuousAt.comp (s4_continuousAt_PiOp _ T₀ hA)))

theorem s4_continuous_end_linear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Module.End ℝ (V ℝ n) →ₗ[ℝ] Y) : @Continuous _ _ (endTopology n) _ L := by
  let := endTopology n
  have h : (L : Module.End ℝ (V ℝ n) → Y) =
      (L ∘ₗ (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)).symm.toLinearMap) ∘
        (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) := by
    funext A
    simp
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional _).comp continuous_induced_dom

/-- `X ↦ eucV ∘ X_ℂ F ∘ eucV⁻¹` (`ℝ`-linear in `X`). -/
noncomputable def s4_LE (F : V ℂ n →ₗ[ℂ] V ℂ n) :
    Module.End ℝ (V ℝ n) →ₗ[ℝ] (EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
      EuclideanSpace ℂ (Fin (2 * n + 2 * n))) where
  toFun X := LinearMap.toContinuousLinearMap
    ((eucV n).toLinearMap ∘ₗ (s4_extEnd ℝ ℂ n X * F) ∘ₗ (eucV n).symm.toLinearMap)
  map_add' X Y := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [s4_extEnd_add, add_mul]
  map_smul' r X := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [s4_extEnd_smul, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_smul, RingHom.id_apply, FunLike.coe_smul, Pi.smul_apply,
      Complex.coe_algebraMap]
    rw [Complex.coe_smul]

open scoped Topology in
theorem s4_continuousAt_KOp_end (T₀ : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) (hA : IsUnit (s4_AOp T₀ (s4_HE n))) :
    @ContinuousAt _ _ _ (endTopology n) (fun T => s4_KOp n T) T₀ := by
  let := endTopology n
  exact (Topology.IsInducing.induced
    (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n))).continuousAt_iff.mpr
    (s4_continuousAt_KOp n T₀ hA)

/-- The orientation condition in the proof of Lemma 4.0.1 is open (TeX 1739–1740: "… is open, as is
the condition that `I_U` preserves the orientation of the positive cone in `V_ℝ`"). The subgroup
`SO_+(V_ℝ) = ρ(Spin(V_ℝ))` of `SO(V_ℝ)` (the kernel of the spinor norm) is open in `SO(V_ℝ)` (Tau
Ceti, `CliffordAlgebra.isOpen_range_spinToSpecialOrthogonal`). So if `x ↦ F x ∈ End(V_ℝ)` is
continuous at `x₀` and the complex structure `F x₀` lies in `SO_+(V_ℝ)`, then for `x` near `x₀`,
every `F x` which is an isometric complex structure (hence in `SO(V_ℝ)`: `det F x = 1`,
`s4_det_of_cs`) lies in `SO_+(V_ℝ)`. `SO(V_ℝ)` carries Tau Ceti's topology, induced by
`g ↦ (g, g⁻¹)` from the module topology of `End(V_ℝ)`, which `endTopology` refines. -/
theorem s4_eventually_mem_SOplus {X : Type*} [TopologicalSpace X] (F : X → Module.End ℝ (V ℝ n))
    (x₀ : X) (hF : @ContinuousAt _ _ _ (endTopology n) F x₀) (hcs₀ : IsComplexStructure (F x₀))
    (h₀ : ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = F x₀) :
    ∀ᶠ x in 𝓝 x₀, IsComplexStructure (F x) →
      (∀ a b, pairing ℝ n (F x a) (F x b) = pairing ℝ n a b) →
        ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = F x := by
  -- `F` is also continuous at `x₀` for Tau Ceti's module topology of `End(V_ℝ)` (coarser than
  -- `endTopology`): `F = e⁻¹ ∘ (e ∘ F)` with `e` the matrix in the basis `basisV`
  have hF' : ContinuousAt F x₀ := by
    let e := LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)
    have hEF : ContinuousAt (fun x => e (F x)) x₀ := by
      let := endTopology n
      exact (Topology.IsInducing.induced e).continuousAt_iff.mp hF
    have h2 : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
    have h3 : F = fun x => e.symm (e (F x)) := by
      funext x
      simp
    rw [h3]
    exact h2.continuousAt.comp hEF
  -- the topology of `SO(V_ℝ)` is induced by `ψ : g ↦ (g, (g⁻¹)ᵐᵒᵖ)`; `ρ(Spin(V_ℝ))` is open
  set SO := TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) with hSO_def
  set H := (CliffordAlgebra.spinToSpecialOrthogonal (Q ℝ n)).range with hH_def
  have hopen : IsOpen (H : Set SO) :=
    CliffordAlgebra.isOpen_range_spinToSpecialOrthogonal (Q ℝ n) s3_Q_nondegenerate
      s4_isOpen_square_real
  let ψ : SO → Module.End ℝ (V ℝ n) × (Module.End ℝ (V ℝ n))ᵐᵒᵖ := fun g =>
    (((g : V ℝ n ≃ₗ[ℝ] V ℝ n) : Module.End ℝ (V ℝ n)),
      MulOpposite.op ((((g : V ℝ n ≃ₗ[ℝ] V ℝ n))⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : Module.End ℝ (V ℝ n)))
  have hψ : Topology.IsInducing ψ :=
    (Units.isInducing_embedProduct.comp
      (⟨rfl⟩ : Topology.IsInducing
        (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (V ℝ n)).symm)).comp
      Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOH⟩ := hψ.isOpen_iff.mp hopen
  -- an isometric complex structure `A` is an element `g` of `SO(V_ℝ)` with `ψ g = (A, (-A)ᵐᵒᵖ)`
  have key : ∀ A : Module.End ℝ (V ℝ n), IsComplexStructure A →
      (∀ a b, pairing ℝ n (A a) (A b) = pairing ℝ n a b) →
      ∃ g : SO, ((g : V ℝ n ≃ₗ[ℝ] V ℝ n) : Module.End ℝ (V ℝ n)) = A ∧
        ψ g = (A, MulOpposite.op (-A)) := by
    intro A hA hiso
    have hAA : A * A = -1 := hA
    let e : V ℝ n ≃ₗ[ℝ] V ℝ n := LinearEquiv.ofLinearMap A (-A)
      (by rw [← Module.End.mul_eq_comp, mul_neg, hAA, neg_neg]; rfl)
      (by rw [← Module.End.mul_eq_comp, neg_mul, hAA, neg_neg]; rfl)
    have he : e ∈ SO := by
      refine TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
      · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
          (IsSMulRegular.of_ne_zero two_ne_zero)]
        exact hiso
      · apply Units.ext
        rw [LinearEquiv.coe_det]
        exact s4_det_of_cs n A hA
    exact ⟨⟨e, he⟩, rfl, rfl⟩
  -- `ψ` maps `ρ(Spin(V_ℝ)) ∩ SO(V_ℝ)` into `O`; in particular `(F x₀, (-F x₀)ᵐᵒᵖ) ∈ O`
  have hmemO : ∀ g : SO, g ∈ H → ψ g ∈ O := fun g hg => by
    have : g ∈ ψ ⁻¹' O := by rw [hOH]; exact hg
    exact this
  have hx₀ : (F x₀, MulOpposite.op (-F x₀)) ∈ O := by
    obtain ⟨g₀, hg₀, hg₀F⟩ := h₀
    obtain ⟨s₀, hs₀⟩ := (mem_SOplus_iff ℝ n g₀).mp hg₀
    have hiso₀ : ∀ a b, pairing ℝ n (F x₀ a) (F x₀ b) = pairing ℝ n a b := fun a b => by
      rw [← hg₀F, ← hs₀]
      exact s3_pairing_rho s₀ a b
    obtain ⟨g, hgA, hgψ⟩ := key (F x₀) hcs₀ hiso₀
    have hgH : g ∈ H := by
      refine ⟨s₀, Subtype.ext (LinearEquiv.toLinearMap_injective ?_)⟩
      rw [hgA, ← hg₀F, ← hs₀]
      refine LinearMap.ext fun v => ?_
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, coe_spinToSpecialOrthogonal_apply]
      rfl
    rw [← hgψ]
    exact hmemO g hgH
  -- for `x` near `x₀`, `(F x, (-F x)ᵐᵒᵖ) ∈ O`
  have hG : ContinuousAt (fun x => (F x, MulOpposite.op (-F x))) x₀ :=
    hF'.prodMk ((MulOpposite.continuous_op.comp continuous_neg).continuousAt.comp hF')
  filter_upwards [hG.preimage_mem_nhds (hO.mem_nhds hx₀)] with x hx hcs hiso
  obtain ⟨g, hgA, hgψ⟩ := key (F x) hcs hiso
  have hgH : g ∈ (H : Set SO) := by
    rw [← hOH]
    show ψ g ∈ O
    rw [hgψ]
    exact hx
  obtain ⟨s, hs⟩ := hgH
  refine ⟨rho ℝ n s, (mem_SOplus_iff ℝ n _).mpr ⟨s, rfl⟩, ?_⟩
  rw [← hgA, ← hs]
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, coe_spinToSpecialOrthogonal_apply]
  rfl

end Topo

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

/-- The eigenspaces of a conjugate `h A h⁻¹` are the images under `h` of those of `A`. -/
theorem s4_eigenspace_conj {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (h : M ≃ₗ[F] M) (A : Module.End F M) (μ : F) :
    Module.End.eigenspace ((h : M →ₗ[F] M) * A * ((h⁻¹ : M ≃ₗ[F] M) : M →ₗ[F] M)) μ =
      (Module.End.eigenspace A μ).map (h : M →ₗ[F] M) := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Module.End.mul_apply, LinearEquiv.coe_coe,
    Submodule.mem_map]
  constructor
  · intro hx
    have e : h (h⁻¹ x) = x := h.apply_symm_apply x
    refine ⟨h⁻¹ x, ?_, e⟩
    apply h.injective
    rw [hx, map_smul, e]
  · rintro ⟨y, hy, rfl⟩
    show h (A (h.symm (h y))) = μ • h y
    rw [h.symm_apply_apply, hy, map_smul]

/-- An element of `SO_+(V_ℝ)_f` commutes with `f`. -/
theorem s4_comm_of_mem_SOplusfR (hW : IsCompl P.W₁ P.W₂) (g : V ℝ n ≃ₗ[ℝ] V ℝ n)
    (hg : g ∈ P.SOplusfR hW) :
    (g : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hW = P.fR hW * (g : V ℝ n →ₗ[ℝ] V ℝ n) :=
  LinearMap.ext fun x => hg.2.1 x

/-- `ρ(g) ∈ SO_+(V_F)` for `g ∈ Spin(V_F)`. -/
theorem s4_rho_mem_SOplus {F : Type*} [Field F] [CharZero F] (g : Spin F n) :
    rho F n g ∈ SOplus F n :=
  ⟨g, LinearEquiv.ext fun m => coe_spinToOrthogonal_apply (Q F n) g m⟩

/-- An element of `SO_+(V_F) = ρ(Spin(V_F))` preserves the pairing `(·,·)_V`. -/
theorem s4_pairing_of_mem_SOplus {F : Type*} [Field F] [CharZero F] (g : V F n ≃ₗ[F] V F n)
    (hg : g ∈ SOplus F n) (x y : V F n) : pairing F n (g x) (g y) = pairing F n x y := by
  obtain ⟨s, rfl⟩ := hg
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (spinToOrthogonal (Q F n) s).2 x y

/-- For `I ∈ Ω_P`, `I = ρ(Ĩ)` for some `Ĩ ∈ Spin(V_ℝ)_P` (Lemma 3.1.1 over `ℝ`). -/
theorem s4_exists_lift_OmegaP (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∃ g ∈ P.spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  obtain ⟨⟨g, hg, rfl⟩, -⟩ := hI
  have hg' : g ∈ rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) := by
    rw [(lemma3_1_1_real P J hP).2]; exact hg
  obtain ⟨x, hx, hxg⟩ := hg'
  exact ⟨x, hx, by rw [hxg]⟩

/-- For `I ∈ Ω_P`, `ν(I) = 2n`. -/
theorem s4_nu_OmegaP (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : P.nu hW I = 2 * n := by
  obtain ⟨⟨g, hg, rfl⟩, -, hE, -, -⟩ := hI
  rw [KSecant.nu, P.s4_comm_of_mem_SOplusfR hW g hg]
  exact hE

/-- For `I ∈ Ω_P`, `I` commutes with `f`. -/
theorem s4_comm_OmegaP (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : I * P.fR hW = P.fR hW * I := by
  obtain ⟨⟨g, hg, rfl⟩, -⟩ := hI
  exact P.s4_comm_of_mem_SOplusfR hW g hg

/-- For `I ∈ Ω_P`, `V^{1,0}_I ∩ W_{1,ℂ}` is `n`-dimensional ("The map `ι` is well defined, by
Lemma 3.2.1", TeX 1721): Lemma 3.2.1 in the form `KSecant.s3_core` (its proof for the general case,
which uses only that `I ∈ Ω_P ⊆ SO_+(V_ℝ)_f` commutes with `f`), with `ν(I) = 2n`. -/
theorem finrank_V10_inf_W₁ℂ (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : Module.finrank ℂ ↥(V10 n I ⊓ P.W₁ℂ) = n :=
  (P.s3_core hW I (P.s4_comm_OmegaP hW I hI) hI.2.1 (P.s4_nu_OmegaP hW I hI)).1

/-- **The map `ι : Ω_P → Gr(n, W_{1,ℂ})`**, `ι(I) = V^{1,0}_I ∩ W_{1,ℂ}` (§4, after (4.0.1)). -/
noncomputable def iota (hW : IsCompl P.W₁ P.W₂) (I : P.OmegaP hW) : P.GrW₁ :=
  ⟨V10 n I.1 ⊓ P.W₁ℂ, inf_le_right, P.finrank_V10_inf_W₁ℂ hW I.1 I.2⟩

/-- For `I = I_{V_ℝ}` the complex structure of `X × X̂`, `g_I = -g_P` (proof of Lemma 4.0.1:
"the … bilinear form `g_P` of Proposition 2.4.4 is `-g_I`"). -/
theorem gI_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.gI hP.isCompl (productStructure n J) = -P.gP hP.isCompl J := by
  refine LinearMap.ext₂ fun x y => ?_
  have hc := congrArg (fun F => F x) (P.fR_comm_productStructure J hP)
  simp only [Module.End.mul_apply] at hc
  simp only [gI, gP, XiR, LinearMap.BilinForm.compRight_apply, LinearMap.BilinForm.compLeft_apply,
    LinearMap.neg_apply]
  rw [hc, pairing_productStructure_left J hP.isComplex, neg_neg]

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
  rintro I' ⟨h, hh, rfl⟩
  obtain ⟨⟨g, hg, rfl⟩, hcs, hE1, hE2, hpos⟩ := hI
  have hhc := P.s4_comm_of_mem_SOplusfR hP.isCompl h hh
  have hinv : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hinv' : ∀ x, h⁻¹ (h x) = x := fun x => h.symm_apply_apply x
  have hconj : ∀ A : Module.End ℝ (V ℝ n),
      P.fR hP.isCompl * ((h : V ℝ n →ₗ[ℝ] V ℝ n) * A * ((h⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : V ℝ n →ₗ[ℝ] V ℝ n)) =
        (h : V ℝ n →ₗ[ℝ] V ℝ n) * (P.fR hP.isCompl * A) *
          ((h⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : V ℝ n →ₗ[ℝ] V ℝ n) := by
    intro A
    rw [← mul_assoc, ← mul_assoc, ← hhc, mul_assoc _ _ A]
  refine ⟨⟨h * g * h⁻¹, mul_mem (mul_mem hh hg) (inv_mem hh), rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    have := congrArg (fun F => F (h⁻¹ x)) hcs
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearMap.neg_apply,
      Module.End.one_apply] at this ⊢
    rw [hinv', this, map_neg, hinv]
  · rw [hconj, s4_eigenspace_conj, LinearEquiv.finrank_map_eq, hE1]
  · rw [hconj, s4_eigenspace_conj, LinearEquiv.finrank_map_eq, hE2]
  · intro x hx
    have hy : h⁻¹ x ≠ 0 := fun h0 => hx (by rw [← hinv x, h0, map_zero])
    have := hpos _ hy
    have hfx := congrArg (fun F => F (h⁻¹ x)) hhc
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at hfx
    simp only [gI, XiR, LinearMap.BilinForm.compRight_apply, LinearMap.BilinForm.compLeft_apply,
      Module.End.mul_apply, LinearEquiv.coe_coe] at this ⊢
    rw [← hinv x, hinv', ← hfx, s4_pairing_of_mem_SOplus h hh.1]
    exact this

/-- The construction proving `Ω_P ≠ ∅` for every `P` (departure from the paper, see
`lemma4_0_1_nonempty`): an `H`-orthogonal `K`-basis `b` of `V_ℚ` (Lemma 3.1.2: `H` has signature
`(n, n)`) gives the `(·,·)_V`-orthogonal real basis `bᵢ, f bᵢ`; `K = ±1` on `span(bᵢ, f bᵢ)` according to
the sign of `(bᵢ, bᵢ)_V`, and `I = -f K/√d`. The vectors `bᵢ` form an orthogonal family adapted to
`I`: the planes `span(bᵢ, I bᵢ) = span(bᵢ, f bᵢ)` are pairwise orthogonal and `(bᵢ, bᵢ)_V ≠ 0`. -/
theorem s4_exists_mem_OmegaP_adapted (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    ∃ I ∈ P.OmegaP hP.isCompl, ∃ x : Fin (2 * n) → V ℝ n,
      (∀ j k, j ≠ k → pairing ℝ n (x j) (x k) = 0 ∧ pairing ℝ n (x j) (I (x k)) = 0) ∧
        ∀ j, pairing ℝ n (x j) (x j) ≠ 0 := by
  set hW := hP.isCompl
  have hd : 0 < d := hP.pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set sd := Real.sqrt (d : ℝ) with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.mpr hdR
  have hsd2 : sd * sd = d := Real.mul_self_sqrt hdR.le
  have hn : 0 < n := s4_n_pos P
  obtain ⟨⟨b, hb⟩, hsig⟩ := lemma3_1_2_signature P J hP
  obtain ⟨hpos, hneg⟩ := hsig b hb
  set f := P.fη hW with hf_def
  -- rational facts
  have hsymm : ∀ x y, pairing ℚ n x y = pairing ℚ n y x := fun x y =>
    QuadraticMap.polar_comm _ x y
  have hfx : ∀ x, pairing ℚ n (f x) x = 0 := by
    intro x
    have h := P.pairing_fη_left hW x x
    rw [hsymm x] at h
    linarith
  have hff : ∀ x, f (f x) = -(d • x) := fun x => congrArg (fun F => F x) (P.fη_comp_fη hW)
  have horth : ∀ i j, i ≠ j → pairing ℚ n (b i) (b j) = 0 ∧ pairing ℚ n (f (b i)) (b j) = 0 := by
    intro i j hij
    have h := hb.2 i j hij
    obtain ⟨h1, h2⟩ := s4_rat_sqrtNeg_eq_zero hd h
    exact ⟨(mul_eq_zero.mp h1).resolve_left hd.ne', h2⟩
  have hrat : ∀ i, Kd.ratPart d (P.hermH hW (b i) (b i)) = d * pairing ℚ n (b i) (b i) :=
    fun i => s4_ratPart_eq
  -- signs: `n` positive and `n` negative `(bᵢ, bᵢ)`, none zero
  set Sp := Finset.univ.filter (fun i => 0 < pairing ℚ n (b i) (b i)) with hSp
  set Sm := Finset.univ.filter (fun i => pairing ℚ n (b i) (b i) < 0) with hSm
  have hSp_card : Sp.card = n := by
    have : Sp = Finset.univ.filter (fun i => 0 < Kd.ratPart d (P.hermH hW (b i) (b i))) := by
      ext i
      simp only [hSp, Finset.mem_filter, Finset.mem_univ, true_and, hrat]
      exact (mul_pos_iff_of_pos_left hd).symm
    rw [this]; exact hpos
  have hSm_card : Sm.card = n := by
    have : Sm = Finset.univ.filter (fun i => Kd.ratPart d (P.hermH hW (b i) (b i)) < 0) := by
      ext i
      simp only [hSm, Finset.mem_filter, Finset.mem_univ, true_and, hrat]
      constructor
      · intro h; exact mul_neg_of_pos_of_neg hd h
      · intro h
        by_contra h'
        push Not at h'
        exact absurd h (not_lt.mpr (mul_nonneg hd.le h'))
    rw [this]; exact hneg
  have hne : ∀ i, pairing ℚ n (b i) (b i) ≠ 0 := by
    have hdisj : Disjoint Sp Sm := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; linarith
    have hall : Sp ∪ Sm = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, hSp_card, hSm_card, Fintype.card_fin]; ring
    intro i h0
    have : i ∈ Sp ∪ Sm := by rw [hall]; exact Finset.mem_univ i
    rcases Finset.mem_union.mp this with h | h
    · rw [hSp, Finset.mem_filter, h0] at h; exact lt_irrefl _ h.2
    · rw [hSm, Finset.mem_filter, h0] at h; exact lt_irrefl _ h.2
  -- the real orthogonal basis `u = (bᵢ, f bᵢ)` of `V_ℝ`
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * n) ⊕ Fin (2 * n) → V ℝ n,
      u = Sum.elim (fun i => bcV ℚ ℝ n (b i)) (fun i => bcV ℚ ℝ n (f (b i))) := ⟨_, rfl⟩
  have hul : ∀ i, u (Sum.inl i) = bcV ℚ ℝ n (b i) := fun i => by rw [hu]; rfl
  have hur : ∀ i, u (Sum.inr i) = bcV ℚ ℝ n (f (b i)) := fun i => by rw [hu]; rfl
  set q : Fin (2 * n) → ℝ := fun i => (pairing ℚ n (b i) (b i) : ℝ) with hq
  have hp_ll : ∀ i j, pairing ℝ n (u (Sum.inl i)) (u (Sum.inl j)) = if i = j then q i else 0 := by
    intro i j
    rw [hul, hul, s4_pairing_bcV]
    split_ifs with h
    · rw [h]
    · rw [(horth i j h).1]; simp
  have hp_lr : ∀ i j, pairing ℝ n (u (Sum.inl i)) (u (Sum.inr j)) = 0 := by
    intro i j
    rw [hul, hur, s4_pairing_bcV, ← neg_neg (pairing ℚ n (b i) (f (b j))), ← P.pairing_fη_left hW]
    by_cases h : i = j
    · rw [h, hfx]; simp
    · rw [(horth i j h).2]; simp
  have hp_rl : ∀ i j, pairing ℝ n (u (Sum.inr i)) (u (Sum.inl j)) = 0 := by
    intro i j
    rw [hur, hul, s4_pairing_bcV]
    by_cases h : i = j
    · rw [h, hfx]; simp
    · rw [(horth i j h).2]; simp
  have hp_rr : ∀ i j, pairing ℝ n (u (Sum.inr i)) (u (Sum.inr j)) =
      if i = j then (d : ℝ) * q i else 0 := by
    intro i j
    rw [hur, hur, s4_pairing_bcV, P.pairing_fη_fη hW]
    split_ifs with h
    · rw [h]; push_cast; rfl
    · rw [(horth i j h).1]; simp
  have hqne : ∀ i, q i ≠ 0 := fun i => by
    simp only [hq]; exact_mod_cast hne i
  have horthR : (pairing ℝ n).iIsOrtho u := by
    intro k l hkl
    show pairing ℝ n (u k) (u l) = 0
    rcases k with i | i <;> rcases l with j | j
    · rw [hp_ll, ite_eq_right (fun h => hkl (by rw [h]))]
    · exact hp_lr i j
    · exact hp_rl i j
    · rw [hp_rr, ite_eq_right (fun h => hkl (by rw [h]))]
  have hdiagR : ∀ k, pairing ℝ n (u k) (u k) ≠ 0 := by
    intro k
    rcases k with i | i
    · rw [hp_ll, ite_eq_left rfl]; exact hqne i
    · rw [hp_rr, ite_eq_left rfl]; exact mul_ne_zero hdR.ne' (hqne i)
  have hli : LinearIndependent ℝ u :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho horthR hdiagR
  have : Nonempty (Fin (2 * n) ⊕ Fin (2 * n)) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hcardB : Fintype.card (Fin (2 * n) ⊕ Fin (2 * n)) = Module.finrank ℝ (V ℝ n) := by
    rw [Module.finrank_eq_card_basis (basisV ℝ n)]; simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcardB with hB
  have hBu : ∀ k, B k = u k := fun k => by
    rw [hB, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- the involution `K`: `+1` on `span(bᵢ, f bᵢ)` for `(bᵢ, bᵢ) < 0`, `-1` otherwise
  set σ : Fin (2 * n) → ℝ := fun i => if pairing ℚ n (b i) (b i) < 0 then 1 else -1 with hσ
  have hσ2 : ∀ i, σ i * σ i = 1 := fun i => by simp only [hσ]; split_ifs <;> norm_num
  have hσq : ∀ i, σ i * q i < 0 := by
    intro i
    simp only [hσ, hq]
    split_ifs with h
    · rw [one_mul]; exact_mod_cast h
    · have : (0 : ℝ) < (pairing ℚ n (b i) (b i) : ℝ) := by
        have h' := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hne i))
        exact_mod_cast h'
      linarith
  set ε : Fin (2 * n) ⊕ Fin (2 * n) → ℝ := Sum.elim σ σ with hε
  set K : Module.End ℝ (V ℝ n) := B.constr ℝ (fun k => ε k • u k) with hK
  have hKu : ∀ k, K (u k) = ε k • u k := fun k => by
    rw [← hBu k, hK, Module.Basis.constr_basis, hBu]
  have hful : ∀ i, P.fR hW (u (Sum.inl i)) = u (Sum.inr i) := fun i => by
    rw [hul, hur, s4_fR_bcV]
  have hfur : ∀ i, P.fR hW (u (Sum.inr i)) = (-(d : ℝ)) • u (Sum.inl i) := fun i => by
    rw [hur, hul, s4_fR_bcV, hff, map_neg, neg_smul, LinearMap.map_smul_of_tower,
      ← Rat.cast_smul_eq_qsmul ℝ]
  set I : Module.End ℝ (V ℝ n) := (-(sd⁻¹)) • (P.fR hW * K) with hI
  have hIl : ∀ i, I (u (Sum.inl i)) = (-(sd⁻¹) * σ i) • u (Sum.inr i) := fun i => by
    simp only [hI, LinearMap.smul_apply, Module.End.mul_apply, hKu, hε, Sum.elim_inl, map_smul,
      hful, smul_smul]
  have hIr : ∀ i, I (u (Sum.inr i)) = (σ i * sd) • u (Sum.inl i) := fun i => by
    simp only [hI, LinearMap.smul_apply, Module.End.mul_apply, hKu, hε, Sum.elim_inr, map_smul,
      hfur, smul_smul]
    congr 1
    field_simp
    rw [← hsd2]; ring
  have hsdinv : sd⁻¹ * sd = 1 := inv_mul_cancel₀ hsd.ne'
  have hsdinv' : sd * sd⁻¹ = 1 := mul_inv_cancel₀ hsd.ne'
  have hdsd : (d : ℝ) * sd⁻¹ = sd := by
    rw [← hsd2, mul_assoc, mul_inv_cancel₀ hsd.ne', mul_one]
  -- `I` is a complex structure commuting with `f`
  have hcs : IsComplexStructure I := by
    show I * I = -1
    refine B.ext fun k => ?_
    rw [hBu]
    rcases k with i | i
    · rw [Module.End.mul_apply, hIl, map_smul, hIr, smul_smul, LinearMap.neg_apply,
        Module.End.one_apply, show (-(sd⁻¹) * σ i) * (σ i * sd) = -((σ i * σ i) * (sd⁻¹ * sd))
          by ring, hσ2, hsdinv, mul_one, neg_one_smul]
    · rw [Module.End.mul_apply, hIr, map_smul, hIl, smul_smul, LinearMap.neg_apply,
        Module.End.one_apply, show (σ i * sd) * (-(sd⁻¹) * σ i) = -((σ i * σ i) * (sd⁻¹ * sd))
          by ring, hσ2, hsdinv, mul_one, neg_one_smul]
  have hc : I * P.fR hW = P.fR hW * I := by
    refine B.ext fun k => ?_
    rw [hBu]
    rcases k with i | i
    · rw [Module.End.mul_apply, Module.End.mul_apply, hful, hIr, hIl, map_smul, hfur, smul_smul]
      congr 1
      rw [show (-(sd⁻¹) * σ i) * (-(d : ℝ)) = σ i * ((d : ℝ) * sd⁻¹) by ring, hdsd]
    · rw [Module.End.mul_apply, Module.End.mul_apply, hfur, map_smul, hIl, hIr, map_smul, hful,
        smul_smul]
      congr 1
      rw [show (-(d : ℝ)) * (-(sd⁻¹) * σ i) = σ i * ((d : ℝ) * sd⁻¹) by ring, hdsd]
  have hiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
    have h : (pairing ℝ n).compl₁₂ I I = pairing ℝ n := by
      refine LinearMap.BilinForm.ext_basis B fun k l => ?_
      rw [LinearMap.compl₁₂_apply, hBu, hBu]
      rcases k with i | i <;> rcases l with j | j
      · rw [hIl, hIl, map_smul, map_smul, LinearMap.smul_apply, hp_rr, hp_ll, smul_eq_mul,
          smul_eq_mul]
        split_ifs with h
        · subst h
          rw [show -(sd⁻¹) * σ i * (-(sd⁻¹) * σ i * (d * q i)) =
            (σ i * σ i) * ((d : ℝ) * sd⁻¹ * sd⁻¹) * q i by ring, hσ2, hdsd, hsdinv']; ring
        · ring
      · rw [hIl, hIr, map_smul, map_smul, LinearMap.smul_apply, hp_rl, hp_lr]; simp
      · rw [hIr, hIl, map_smul, map_smul, LinearMap.smul_apply, hp_lr, hp_rl]; simp
      · rw [hIr, hIr, map_smul, map_smul, LinearMap.smul_apply, hp_ll, hp_rr, smul_eq_mul,
          smul_eq_mul]
        split_ifs with h
        · subst h
          rw [show σ i * sd * (σ i * sd * q i) = (σ i * σ i) * (sd * sd) * q i by ring, hσ2,
            hsd2]; ring
        · ring
    intro x y
    have := congrArg (fun F => F x y) h
    simpa using this
  -- `f ∘ I = √d K`
  have hfI : P.fR hW * I = sd • K := by
    refine B.ext fun k => ?_
    rw [hBu]
    rcases k with i | i
    · rw [Module.End.mul_apply, hIl, map_smul, hfur, smul_smul, LinearMap.smul_apply, hKu]
      simp only [hε, Sum.elim_inl, smul_smul]
      congr 1
      rw [show (-(sd⁻¹) * σ i) * (-(d : ℝ)) = σ i * ((d : ℝ) * sd⁻¹) by ring, hdsd]; ring
    · rw [Module.End.mul_apply, hIr, map_smul, hful, LinearMap.smul_apply, hKu]
      simp only [hε, Sum.elim_inr, smul_smul]
      congr 1; ring
  -- the eigenspaces of `K`
  have hKK : K * K = 1 := by
    refine B.ext fun k => ?_
    rw [hBu, Module.End.mul_apply, hKu, map_smul, hKu, smul_smul, Module.End.one_apply]
    rcases k with i | i <;> simp [hε, hσ2]
  have hKc : IsCompl (K.eigenspace 1) (K.eigenspace (-1)) := by
    refine s4_isCompl_eigenspace K 1 (-1) (by norm_num) ?_
    rw [s4_quad_eq, hKK]
    simp
  have hlow : ∀ (S : Finset (Fin (2 * n))) (μ : ℝ), (∀ i ∈ S, σ i = μ) →
      S.card + S.card ≤ Module.finrank ℝ (K.eigenspace μ) := by
    intro S μ hS
    have hmem : ∀ k : S ⊕ S, u (Sum.map Subtype.val Subtype.val k) ∈ K.eigenspace μ := by
      intro k
      rw [Module.End.mem_eigenspace_iff, hKu]
      rcases k with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [hε, hS i hi]
    let g : S ⊕ S → K.eigenspace μ := fun k => ⟨_, hmem k⟩
    have hg : LinearIndependent ℝ g := by
      apply LinearIndependent.of_comp (K.eigenspace μ).subtype
      exact hli.comp _ (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
    have := hg.fintype_card_le_finrank
    simpa [Fintype.card_sum] using this
  have hl1 := hlow Sm 1 (fun i hi => by
    simp only [hσ]; rw [ite_eq_left (Finset.mem_filter.mp hi).2])
  have hl2 := hlow Sp (-1) (fun i hi => by
    simp only [hσ]; rw [ite_eq_right (not_lt.mpr (Finset.mem_filter.mp hi).2.le)])
  have hsumK := Submodule.finrank_add_eq_of_isCompl hKc
  rw [Module.finrank_eq_card_basis (basisV ℝ n), Fintype.card_fin] at hsumK
  rw [hSm_card] at hl1
  rw [hSp_card] at hl2
  have hsmul_eig : ∀ μ : ℝ, Module.End.eigenspace (sd • K) (sd * μ) = K.eigenspace μ := by
    intro μ
    ext x
    simp only [Module.End.mem_eigenspace_iff, LinearMap.smul_apply, mul_smul]
    exact (smul_right_injective _ hsd.ne').eq_iff
  have hE1 : Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (Real.sqrt d)) = 2 * n := by
    rw [hfI, ← mul_one (Real.sqrt (d : ℝ)), hsmul_eig]; omega
  have hE2 : Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (-Real.sqrt d)) = 2 * n := by
    rw [hfI, ← mul_neg_one (Real.sqrt (d : ℝ)), hsmul_eig]; omega
  -- `(x, K x)_V < 0` for `x ≠ 0`
  have hw : ∀ k, ε k * pairing ℝ n (u k) (u k) < 0 := by
    intro k
    rcases k with i | i
    · rw [hp_ll, ite_eq_left rfl]; exact hσq i
    · rw [hp_rr, ite_eq_left rfl]
      simp only [hε, Sum.elim_inr]
      nlinarith [hσq i, hdR]
  have hKneg : ∀ x : V ℝ n, x ≠ 0 → pairing ℝ n x (K x) < 0 := by
    intro x hx
    set c := B.repr x
    have hx' : x = ∑ k, c k • u k := by
      conv_lhs => rw [← B.sum_repr x]
      simp [hBu, c]
    have hsum : pairing ℝ n x (K x) = ∑ k, c k * c k * (ε k * pairing ℝ n (u k) (u k)) := by
      conv_lhs => rw [hx']
      simp only [map_sum, map_smul, hKu, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · ring
      · intro l _ hlk
        rw [show pairing ℝ n (u l) (u k) = 0 from horthR hlk]; ring
      · simp
    obtain ⟨k₀, hk₀⟩ : ∃ k, c k ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by rw [hx']; simp [h])
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
    have h1 : c k₀ * c k₀ * (ε k₀ * pairing ℝ n (u k₀) (u k₀)) < 0 :=
      mul_neg_of_pos_of_neg (mul_self_pos.mpr hk₀) (hw k₀)
    have h2 : ∑ k ∈ Finset.univ.erase k₀, c k * c k * (ε k * pairing ℝ n (u k) (u k)) ≤ 0 :=
      Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (hw k).le
    linarith
  -- assembling: `I ∈ Ω_P`
  obtain ⟨xs, hxs⟩ := remark2_4_3_exists_lift I hcs hiso
  have hfr4 := P.s4_finrank_four hW I hc hcs hE1
  have hmem : I ∈ P.OmegaP hW := by
    refine ⟨⟨rho ℝ n xs, P.s4_mem_SOplusfR_of_cs hW _ (s4_rho_mem_SOplus xs) (hxs ▸ hcs)
      (hxs ▸ hc) ?_ ?_, hxs⟩, hcs, hE1, hE2, ?_⟩
    · rw [hxs, inf_comm, hfr4.1, inf_comm, hfr4.2.1]
    · rw [hxs, inf_comm, hfr4.2.2.1, inf_comm, hfr4.2.2.2]
    · intro x hx
      have h1 := hKneg x hx
      simp only [gI, XiR, LinearMap.BilinForm.compRight_apply, LinearMap.BilinForm.compLeft_apply]
      rw [hI, LinearMap.smul_apply, Module.End.mul_apply, map_smul, s4_pairing_fR_fR, smul_eq_mul,
        show -(sd⁻¹) * ((d : ℝ) * pairing ℝ n x (K x)) = sd⁻¹ * ((d : ℝ) * -pairing ℝ n x (K x))
          by ring]
      exact mul_pos (inv_pos.mpr hsd) (mul_pos hdR (neg_pos.mpr h1))
  -- the adapted orthogonal family `bᵢ`
  refine ⟨I, hmem, fun j => u (Sum.inl j), fun j k hjk => ⟨?_, ?_⟩, fun j => ?_⟩
  · rw [hp_ll, ite_eq_right hjk]
  · rw [hIl, map_smul, hp_lr, smul_zero]
  · rw [hp_ll, ite_eq_left rfl]; exact hqne j

theorem s4_exists_mem_OmegaP (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    ∃ I, I ∈ P.OmegaP hP.isCompl := by
  obtain ⟨I, hI, -⟩ := P.s4_exists_mem_OmegaP_adapted J hP
  exact ⟨I, hI⟩

/-! ### Cartan involutions and transitivity on `Ω_P` (for Lemma 4.0.2) -/


/-- A Cartan involution compatible with `f`: `K² = 1`, `K f = f K`, `K` preserves `(·,·)_V`, and
`(x, K x)_V < 0` for `x ≠ 0`. -/
def s4_IsCartan (hW : IsCompl P.W₁ P.W₂) (K : Module.End ℝ (V ℝ n)) : Prop :=
  K * K = 1 ∧ K * P.fR hW = P.fR hW * K ∧ (∀ x y, pairing ℝ n (K x) (K y) = pairing ℝ n x y) ∧
    ∀ x, x ≠ 0 → pairing ℝ n x (K x) < 0

/-- From an `f`-linear isometric involution `K`: `I = -f K/√d` is a complex structure of `V_ℝ` which
is an isometry of `(·,·)_V`. -/
theorem s4_cs_of_cartan (hW : IsCompl P.W₁ P.W₂) (K : Module.End ℝ (V ℝ n)) (hKK : K * K = 1)
    (hKf : K * P.fR hW = P.fR hW * K)
    (hKiso : ∀ x y, pairing ℝ n (K x) (K y) = pairing ℝ n x y) :
    IsComplexStructure ((-(Real.sqrt d)⁻¹) • (P.fR hW * K)) ∧
      ∀ x y, pairing ℝ n (((-(Real.sqrt d)⁻¹) • (P.fR hW * K)) x)
        (((-(Real.sqrt d)⁻¹) • (P.fR hW * K)) y) = pairing ℝ n x y := by
  have hd : 0 < d := P.d_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set sd := Real.sqrt (d : ℝ) with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.mpr hdR
  have hsd2 : sd * sd = d := Real.mul_self_sqrt hdR.le
  set f := P.fR hW with hf
  set I : Module.End ℝ (V ℝ n) := (-(sd⁻¹)) • (f * K) with hI
  have hff : ∀ x, f (f x) = -((d : ℝ) • x) := P.s4_fR_fR hW
  have hKKx : ∀ x, K (K x) = x := fun x => by
    have := congrArg (fun F => F x) hKK
    simpa using this
  have hKfx : ∀ x, K (f x) = f (K x) := fun x => by
    have := congrArg (fun F => F x) hKf
    simpa using this
  have hIx : ∀ x, I x = (-(sd⁻¹)) • f (K x) := fun x => rfl
  have hc1 : -(sd⁻¹) * -(sd⁻¹) * (d : ℝ) = 1 := by
    rw [← hsd2]; field_simp
  refine ⟨?_, fun x y => ?_⟩
  · show I * I = -1
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, hIx, hIx, map_smul, map_smul, hKfx, hKKx, hff, smul_smul,
      smul_neg, smul_smul, hc1, one_smul, LinearMap.neg_apply, Module.End.one_apply]
  · rw [hIx, hIx, map_smul, map_smul, LinearMap.smul_apply, P.s4_pairing_fR_fR hW, hKiso,
      smul_eq_mul, smul_eq_mul]
    linear_combination pairing ℝ n x y * hc1

/-- From a Cartan involution `K` to a point `I = -f K/√d` of `Ω_P`, given that `I ∈ SO_+(V_ℝ)`:
`I` is an orthogonal complex structure commuting with `f` (`KSecant.s4_cs_of_cartan`); the
eigenspaces of `K = f I/√d` are definite, hence both `2n`-dimensional, so `ν(I) = 2n`; `I` has
determinant `1` on `W_{1,ℂ}` and `W_{2,ℂ}` by Lemma 3.2.1 (`KSecant.s4_finrank_four`), so
`I ∈ SO_+(V_ℝ)_f`; and `g_I(x, x) = -√d (x, K x)_V > 0` for `x ≠ 0`. -/
theorem s4_mem_OmegaP_of_cartan_of_SOplus (hW : IsCompl P.W₁ P.W₂) (K : Module.End ℝ (V ℝ n))
    (hK : P.s4_IsCartan hW K)
    (hSO : ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = (-(Real.sqrt d)⁻¹) • (P.fR hW * K)) :
    (-(Real.sqrt d)⁻¹) • (P.fR hW * K) ∈ P.OmegaP hW := by
  obtain ⟨hKK, hKf, hKiso, hKneg⟩ := hK
  obtain ⟨hcs, -⟩ := P.s4_cs_of_cartan hW K hKK hKf hKiso
  have hd : 0 < d := P.d_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set sd := Real.sqrt (d : ℝ) with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.mpr hdR
  have hsd2 : sd * sd = d := Real.mul_self_sqrt hdR.le
  set f := P.fR hW with hf
  set I : Module.End ℝ (V ℝ n) := (-(sd⁻¹)) • (f * K) with hI
  have hff : ∀ x, f (f x) = -((d : ℝ) • x) := P.s4_fR_fR hW
  have hKfx : ∀ x, K (f x) = f (K x) := fun x => by
    have := congrArg (fun F => F x) hKf
    simpa using this
  have hIx : ∀ x, I x = (-(sd⁻¹)) • f (K x) := fun x => rfl
  have hc : I * f = f * I := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hIx, hIx, hKfx, map_smul]
  have hfI : f * I = sd • K := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, hIx, map_smul, hff, LinearMap.smul_apply, smul_neg, smul_smul,
      ← neg_smul]
    congr 1
    rw [← hsd2]; field_simp
  -- the eigenspaces of `K` are definite, hence both `2n`-dimensional
  have hKc : IsCompl (K.eigenspace 1) (K.eigenspace (-1)) := by
    refine s4_isCompl_eigenspace K 1 (-1) (by norm_num) ?_
    rw [s4_quad_eq, hKK]
    simp
  have hle1 : Module.finrank ℝ (K.eigenspace 1) ≤ 2 * n := by
    refine s4_finrank_le_of_definite _ fun x hx hx0 => ?_
    have h := hKneg x hx0
    rw [Module.End.mem_eigenspace_iff.mp hx, one_smul] at h
    exact h.ne
  have hle2 : Module.finrank ℝ (K.eigenspace (-1)) ≤ 2 * n := by
    refine s4_finrank_le_of_definite _ fun x hx hx0 => ?_
    have h := hKneg x hx0
    rw [Module.End.mem_eigenspace_iff.mp hx, neg_one_smul, map_neg] at h
    exact (neg_neg_iff_pos.mp h).ne'
  have hsumK := Submodule.finrank_add_eq_of_isCompl hKc
  rw [Module.finrank_eq_card_basis (basisV ℝ n), Fintype.card_fin] at hsumK
  have hsmul_eig : ∀ μ : ℝ, Module.End.eigenspace (sd • K) (sd * μ) = K.eigenspace μ := by
    intro μ
    ext x
    simp only [Module.End.mem_eigenspace_iff, LinearMap.smul_apply, mul_smul]
    exact (smul_right_injective _ hsd.ne').eq_iff
  have hE1 : Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (Real.sqrt d)) = 2 * n := by
    rw [hfI, ← mul_one (Real.sqrt (d : ℝ)), hsmul_eig]; omega
  have hE2 : Module.finrank ℝ (Module.End.eigenspace (P.fR hW * I) (-Real.sqrt d)) = 2 * n := by
    rw [hfI, ← mul_neg_one (Real.sqrt (d : ℝ)), hsmul_eig]; omega
  -- assembling: `I ∈ Ω_P`
  obtain ⟨g, hg, hgI⟩ := hSO
  have hfr4 := P.s4_finrank_four hW I hc hcs hE1
  refine ⟨⟨g, P.s4_mem_SOplusfR_of_cs hW g hg (hgI ▸ hcs) (hgI ▸ hc) ?_ ?_, hgI⟩, hcs, hE1, hE2,
    ?_⟩
  · rw [hgI, inf_comm, hfr4.1, inf_comm, hfr4.2.1]
  · rw [hgI, inf_comm, hfr4.2.2.1, inf_comm, hfr4.2.2.2]
  · intro x hx
    have h1 := hKneg x hx
    simp only [gI, XiR, LinearMap.BilinForm.compRight_apply, LinearMap.BilinForm.compLeft_apply]
    rw [hIx, map_smul, P.s4_pairing_fR_fR hW, smul_eq_mul,
      show -(sd⁻¹) * ((d : ℝ) * pairing ℝ n x (K x)) = sd⁻¹ * ((d : ℝ) * -pairing ℝ n x (K x))
        by ring]
    exact mul_pos (inv_pos.mpr hsd) (mul_pos hdR (neg_pos.mpr h1))

/-- From a Cartan involution `K` to a point `I = -f K/√d` of `Ω_P`, with `I ∈ SO_+(V_ℝ)` by
Remark 2.4.3 (`remark2_4_3_exists_lift`). Used in the departure for Lemma 4.0.2
(`KSecant.s4_OmegaP_join`). -/
theorem s4_mem_OmegaP_of_cartan (hW : IsCompl P.W₁ P.W₂) (K : Module.End ℝ (V ℝ n))
    (hK : P.s4_IsCartan hW K) : (-(Real.sqrt d)⁻¹) • (P.fR hW * K) ∈ P.OmegaP hW := by
  obtain ⟨hcs, hiso⟩ := P.s4_cs_of_cartan hW K hK.1 hK.2.1 hK.2.2.1
  obtain ⟨xs, hxs⟩ := remark2_4_3_exists_lift _ hcs hiso
  exact P.s4_mem_OmegaP_of_cartan_of_SOplus hW K hK ⟨rho ℝ n xs, s4_rho_mem_SOplus xs, hxs⟩

/-- The Cartan involution `K = f I/√d` of `I ∈ Ω_P`; `I = -f K/√d`. -/
theorem s4_cartan_of_mem_OmegaP (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) :
    P.s4_IsCartan hW ((Real.sqrt d)⁻¹ • (P.fR hW * I)) ∧
      I = (-(Real.sqrt d)⁻¹) • (P.fR hW * ((Real.sqrt d)⁻¹ • (P.fR hW * I))) := by
  have hc := P.s4_comm_OmegaP hW I hI
  obtain ⟨⟨g, hg, hgI⟩, hcs, -, -, hpos⟩ := hI
  have hd : 0 < d := P.d_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set sd := Real.sqrt (d : ℝ) with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.mpr hdR
  have hsd2 : sd * sd = d := Real.mul_self_sqrt hdR.le
  set f := P.fR hW with hf
  have hff : ∀ x, f (f x) = -((d : ℝ) • x) := P.s4_fR_fR hW
  have hIIx : ∀ x, I (I x) = -x := fun x => by
    have := congrArg (fun F => F x) hcs
    simpa using this
  have hIfx : ∀ x, I (f x) = f (I x) := fun x => by
    have := congrArg (fun F => F x) hc
    simpa using this
  have hIiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
    intro x y
    rw [← hgI]
    exact s4_pairing_of_mem_SOplus g hg.1 x y
  set K : Module.End ℝ (V ℝ n) := sd⁻¹ • (f * I) with hK
  have hKx : ∀ x, K x = sd⁻¹ • f (I x) := fun x => rfl
  have hc1 : sd⁻¹ * sd⁻¹ * (d : ℝ) = 1 := by
    rw [← hsd2]; field_simp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, hKx, hKx, map_smul, map_smul, hIfx, hIIx, map_neg, map_neg, hff,
      neg_neg, smul_smul, smul_smul, hc1, one_smul, Module.End.one_apply]
  · refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hKx, hKx, hIfx, map_smul]
  · intro x y
    rw [hKx, hKx, map_smul, map_smul, LinearMap.smul_apply, P.s4_pairing_fR_fR hW, hIiso,
      smul_eq_mul, smul_eq_mul]
    linear_combination pairing ℝ n x y * hc1
  · intro x hx
    have h := hpos x hx
    simp only [gI, XiR, LinearMap.BilinForm.compRight_apply,
      LinearMap.BilinForm.compLeft_apply] at h
    rw [hKx, map_smul, smul_eq_mul, ← neg_neg (pairing ℝ n x (f (I x))),
      ← P.s4_pairing_fR_left hW]
    have : 0 < sd⁻¹ := inv_pos.mpr hsd
    nlinarith
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, hKx, map_smul, hff, smul_neg, smul_smul,
      smul_neg, smul_smul, ← neg_smul, show -(-(sd⁻¹) * (sd⁻¹ * (d : ℝ))) = 1 by
        rw [← hsd2]; field_simp, one_smul]


/-- The geodesic between two Cartan involutions: for Cartan involutions `K₀, K₁`, `B₀ = -(·, K₀ ·)_V`
is positive definite, `P = K₀ K₁` is `B₀`-self-adjoint and positive, `K₀ P K₀ = P⁻¹`, and
`K_t = K₀ P^t` is a continuous path of Cartan involutions from `K₀` to `K₁`, with
`K_{1/2} K₀ K_{1/2} = K₁`. -/
theorem s4_cartan_path (hW : IsCompl P.W₁ P.W₂) (K₀ K₁ : Module.End ℝ (V ℝ n))
    (h₀ : P.s4_IsCartan hW K₀) (h₁ : P.s4_IsCartan hW K₁) :
    ∃ Kt : ℝ → Module.End ℝ (V ℝ n), @Continuous _ _ _ (endTopology n) Kt ∧ Kt 0 = K₀ ∧
      Kt 1 = K₁ ∧ (∀ t, P.s4_IsCartan hW (Kt t)) ∧ Kt (1 / 2) * K₀ * Kt (1 / 2) = K₁ := by
  obtain ⟨hKK₀, hKf₀, hKiso₀, hKneg₀⟩ := h₀
  obtain ⟨hKK₁, hKf₁, hKiso₁, hKneg₁⟩ := h₁
  have hK0x : ∀ x, K₀ (K₀ x) = x := fun x => by
    have := congrArg (fun F => F x) hKK₀
    simpa using this
  have hK1x : ∀ x, K₁ (K₁ x) = x := fun x => by
    have := congrArg (fun F => F x) hKK₁
    simpa using this
  have hsymm : ∀ x y, pairing ℝ n x y = pairing ℝ n y x := fun x y =>
    QuadraticMap.polar_comm _ x y
  have hK0adj : ∀ x y, pairing ℝ n (K₀ x) y = pairing ℝ n x (K₀ y) := fun x y => by
    rw [← hKiso₀ x (K₀ y), hK0x]
  have hK1adj : ∀ x y, pairing ℝ n (K₁ x) y = pairing ℝ n x (K₁ y) := fun x y => by
    rw [← hKiso₁ x (K₁ y), hK1x]
  -- `B₀(x, y) = -(x, K₀ y)_V` is symmetric and positive definite
  set B₀ : LinearMap.BilinForm ℝ (V ℝ n) := -((pairing ℝ n).compl₂ K₀) with hB₀
  have hB₀x : ∀ x y, B₀ x y = -pairing ℝ n x (K₀ y) := fun x y => rfl
  have hBs : ∀ x y, B₀ x y = B₀ y x := fun x y => by
    rw [hB₀x, hB₀x, ← hK0adj, hsymm]
  have hBpos : ∀ x, x ≠ 0 → 0 < B₀ x x := fun x hx => by
    rw [hB₀x]
    linarith [hKneg₀ x hx]
  have hpair : ∀ x y, pairing ℝ n x y = -B₀ x (K₀ y) := fun x y => by
    rw [hB₀x, hK0x, neg_neg]
  -- `P = K₀ K₁` is `B₀`-self-adjoint and positive
  set Pm : Module.End ℝ (V ℝ n) := K₀ * K₁ with hPm
  have hPmx : ∀ x, Pm x = K₀ (K₁ x) := fun x => rfl
  have hPs : ∀ x y, B₀ (Pm x) y = B₀ x (Pm y) := fun x y => by
    rw [hB₀x, hB₀x, hPmx, hPmx, hKiso₀, hK0x, hK1adj]
  have hBPpos : ∀ x, x ≠ 0 → 0 < B₀ (Pm x) x := fun x hx => by
    rw [hB₀x, hPmx, hKiso₀, hsymm]
    linarith [hKneg₁ x hx]
  obtain ⟨N, b, lam, hon, hPb⟩ := s4_exists_orthonormal_eigenbasis B₀ hBs hBpos Pm hPs
  have hl : ∀ i, 0 < lam i := fun i => by
    have h := hBPpos (b i) (b.ne_zero i)
    simpa [hPb, hon] using h
  -- `K₀` inverts the eigenvalues of `P`
  have hK0inv : ∀ j, Pm (K₀ (b j)) = (lam j)⁻¹ • K₀ (b j) := fun j => by
    have h2 : K₁ (b j) = lam j • K₀ (b j) := by
      have := congrArg K₀ (hPb j)
      rwa [hPmx, hK0x, map_smul] at this
    have h3 : lam j • K₁ (K₀ (b j)) = b j := by
      have := congrArg K₁ h2
      rw [hK1x, map_smul] at this
      exact this.symm
    have h4 : K₁ (K₀ (b j)) = (lam j)⁻¹ • b j := (eq_inv_smul_iff₀ (hl j).ne').mpr h3
    rw [hPmx, h4, map_smul]
  set Pt : ℝ → Module.End ℝ (V ℝ n) := s4_rpowOp B₀ b lam with hPt
  have hmul : ∀ s t, Pt s * Pt t = Pt (s + t) := fun s t => s4_rpowOp_mul B₀ b lam hon s t hl
  have hzero : Pt 0 = 1 := s4_rpowOp_zero B₀ b lam hon
  have hone : Pt 1 = Pm := s4_rpowOp_one B₀ b lam hon Pm hPb
  have hsymPt : ∀ t x y, B₀ (Pt t x) y = B₀ x (Pt t y) := fun t =>
    s4_rpowOp_symm B₀ b lam hBs t
  have hposPt : ∀ t x, x ≠ 0 → 0 < B₀ (Pt t x) x := fun t x hx =>
    s4_rpowOp_pos B₀ b lam hon t hl x hx
  have hfPm : P.fR hW * Pm = Pm * P.fR hW := by
    rw [hPm, ← mul_assoc, ← hKf₀, mul_assoc, ← hKf₁, ← mul_assoc]
  have hfPt : ∀ t, P.fR hW * Pt t = Pt t * P.fR hW := fun t =>
    s4_rpowOp_comm B₀ b lam hon Pm hPb t (P.fR hW) hfPm
  have hPtK : ∀ t, Pt t * K₀ = K₀ * Pt (-t) := fun t =>
    s4_rpowOp_comm_inv B₀ b lam hon Pm hPb hl t K₀ hK0inv
  have hPtKx : ∀ t x, Pt t (K₀ x) = K₀ (Pt (-t) x) := fun t x => by
    have := congrArg (fun F => F x) (hPtK t)
    simpa using this
  have hKPt : ∀ t x, K₀ (Pt t x) = Pt (-t) (K₀ x) := fun t x => by
    rw [hPtKx, neg_neg]
  have hPtPt : ∀ s t x, Pt s (Pt t x) = Pt (s + t) x := fun s t x => by
    rw [← hmul s t, Module.End.mul_apply]
  have hPt0x : ∀ x, Pt 0 x = x := fun x => by rw [hzero, Module.End.one_apply]
  refine ⟨fun t => K₀ * Pt t, s4_continuous_mul_left K₀ ?_, ?_, ?_, fun t => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact s4_continuous_sum_smul (fun i t => lam i ^ t)
      (fun i => Real.continuous_const_rpow (hl i).ne') _
  · show K₀ * Pt 0 = K₀
    rw [hzero, mul_one]
  · show K₀ * Pt 1 = K₁
    rw [hone, hPm, ← mul_assoc, hKK₀, one_mul]
  · -- `K_t² = 1`
    refine LinearMap.ext fun x => ?_
    show K₀ (Pt t (K₀ (Pt t x))) = x
    rw [hPtKx, hK0x, hPtPt, neg_add_cancel, hPt0x]
  · -- `K_t` commutes with `f`
    refine LinearMap.ext fun x => ?_
    show K₀ (Pt t (P.fR hW x)) = P.fR hW (K₀ (Pt t x))
    have h1 := congrArg (fun F => F x) (hfPt t)
    have h2 := congrArg (fun F => F (Pt t x)) hKf₀
    simp only [Module.End.mul_apply] at h1 h2
    rw [← h1, h2]
  · -- `K_t` is an isometry
    intro x y
    show pairing ℝ n (K₀ (Pt t x)) (K₀ (Pt t y)) = pairing ℝ n x y
    rw [hKiso₀, hpair, hKPt, ← hsymPt, hPtPt, neg_add_cancel, hPt0x, ← hpair]
  · -- `(x, K_t x)_V < 0`
    intro x hx
    show pairing ℝ n x (K₀ (Pt t x)) < 0
    have h := hposPt t x hx
    rw [hBs, hB₀x] at h
    linarith
  · -- the midpoint
    refine LinearMap.ext fun x => ?_
    show K₀ (Pt (1 / 2) (K₀ (K₀ (Pt (1 / 2) x)))) = K₁ x
    rw [hK0x, hPtPt, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, hone, hPmx, hK0x]

/-- Any two points `I₀, I₁` of `Ω_P` are joined by a continuous path in `Ω_P`, and
`I₁ = h I₀ h⁻¹` for some `h ∈ SO_+(V_ℝ)_f` (namely `h = I_{1/2}`, the midpoint of the path). -/
theorem s4_OmegaP_join (hW : IsCompl P.W₁ P.W₂) (I₀ I₁ : Module.End ℝ (V ℝ n))
    (h₀ : I₀ ∈ P.OmegaP hW) (h₁ : I₁ ∈ P.OmegaP hW) :
    (∃ γ : ℝ → Module.End ℝ (V ℝ n), @Continuous _ _ _ (endTopology n) γ ∧ γ 0 = I₀ ∧
      γ 1 = I₁ ∧ ∀ t, γ t ∈ P.OmegaP hW) ∧
    ∃ h ∈ P.SOplusfR hW, I₁ = (h : V ℝ n →ₗ[ℝ] V ℝ n) * I₀ *
      ((h⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : V ℝ n →ₗ[ℝ] V ℝ n) := by
  obtain ⟨hc₀, he₀⟩ := P.s4_cartan_of_mem_OmegaP hW I₀ h₀
  obtain ⟨hc₁, he₁⟩ := P.s4_cartan_of_mem_OmegaP hW I₁ h₁
  set K₀ := (Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I₀) with hK₀
  set K₁ := (Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I₁) with hK₁
  obtain ⟨Kt, hcont, hKt0, hKt1, hcart, hmid⟩ := P.s4_cartan_path hW K₀ K₁ hc₀ hc₁
  set c : ℝ := -(Real.sqrt (d : ℝ))⁻¹ with hc
  refine ⟨⟨fun t => c • (P.fR hW * Kt t), s4_continuous_smul c (s4_continuous_mul_left _ hcont),
    ?_, ?_, fun t => P.s4_mem_OmegaP_of_cartan hW (Kt t) (hcart t)⟩, ?_⟩
  · show c • (P.fR hW * Kt 0) = I₀
    rw [hKt0, he₀]
  · show c • (P.fR hW * Kt 1) = I₁
    rw [hKt1, he₁]
  · -- the midpoint `I_{1/2}` conjugates `I₀` to `I₁`
    obtain ⟨⟨h, hh, hhI⟩, hcsm, -⟩ := P.s4_mem_OmegaP_of_cartan hW (Kt (1 / 2)) (hcart (1 / 2))
    obtain ⟨-, hKmf, -, -⟩ := hcart (1 / 2)
    obtain ⟨-, hK0f, -, -⟩ := hc₀
    have hd : 0 < d := P.d_pos
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hsd2 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = d := Real.mul_self_sqrt hdR.le
    have hcc : c * c * (d : ℝ) = 1 := by
      have : c * c = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ))⁻¹ := by rw [hc, mul_inv]; ring
      rw [this, hsd2, inv_mul_cancel₀ hdR.ne']
    have hff : ∀ x, P.fR hW (P.fR hW x) = -((d : ℝ) • x) := P.s4_fR_fR hW
    have hKmfx : ∀ x, Kt (1 / 2) (P.fR hW x) = P.fR hW (Kt (1 / 2) x) := fun x =>
      LinearMap.congr_fun hKmf x
    have hK0fx : ∀ x, K₀ (P.fR hW x) = P.fR hW (K₀ x) := fun x => LinearMap.congr_fun hK0f x
    have hmidx : ∀ x, Kt (1 / 2) (K₀ (Kt (1 / 2) x)) = K₁ x := fun x =>
      LinearMap.congr_fun hmid x
    have hhx : ∀ x, h x = c • P.fR hW (Kt (1 / 2) x) := fun x => LinearMap.congr_fun hhI x
    have hI0x : ∀ x, I₀ x = c • P.fR hW (K₀ x) := fun x => LinearMap.congr_fun he₀ x
    have hI1x : ∀ x, I₁ x = c • P.fR hW (K₁ x) := fun x => LinearMap.congr_fun he₁ x
    have hhh : ∀ x, h (h x) = -x := fun x => by
      have := LinearMap.congr_fun hcsm x
      rw [← hhI] at this
      exact this
    have hinv : ∀ x, (h⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) x = -h x := fun x => by
      apply h.injective
      rw [map_neg, hhh, neg_neg]
      exact h.apply_symm_apply x
    refine ⟨h, hh, LinearMap.ext fun x => ?_⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      hinv, map_neg, map_neg, hhx, hI0x, hhx, hI1x, map_smul, map_smul, map_smul, map_smul,
      map_smul, hK0fx, hKmfx, hKmfx, hmidx, hff]
    simp only [map_neg, map_smul, smul_neg, neg_neg, smul_smul]
    congr 1
    linear_combination (-c) * hcc


/-- Every `I ∈ Ω_P` has an orthogonal family adapted to it: `x₁, …, x_{2n}` with pairwise orthogonal
planes `span(xⱼ, I xⱼ)` and `(xⱼ, xⱼ)_V ≠ 0` (transport of `s4_exists_mem_OmegaP_adapted` by an
element of `SO_+(V_ℝ)_f`, `s4_OmegaP_join`). -/
theorem s4_exists_adapted (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∃ x : Fin (2 * n) → V ℝ n,
      (∀ j k, j ≠ k → pairing ℝ n (x j) (x k) = 0 ∧ pairing ℝ n (x j) (I (x k)) = 0) ∧
        ∀ j, pairing ℝ n (x j) (x j) ≠ 0 := by
  obtain ⟨I₀, hI₀, x₀, horth, hne⟩ := P.s4_exists_mem_OmegaP_adapted J hP
  obtain ⟨-, h, hh, hhI⟩ := P.s4_OmegaP_join hP.isCompl I₀ I hI₀ hI
  have hiso : ∀ a b, pairing ℝ n (h a) (h b) = pairing ℝ n a b := s4_pairing_of_mem_SOplus h hh.1
  have hIh : ∀ a, I (h a) = h (I₀ a) := fun a => by
    rw [hhI, Module.End.mul_apply, Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
    rw [show h⁻¹ (h a) = a from h.symm_apply_apply a]
  refine ⟨fun j => h (x₀ j), fun j k hjk => ⟨?_, ?_⟩, fun j => ?_⟩
  · rw [hiso]; exact (horth j k hjk).1
  · rw [hIh, hiso]; exact (horth j k hjk).2
  · rw [hiso]; exact hne j

/-! ### The inverse of `ι` (for Lemma 4.0.1) -/


theorem s4_sqrtNeg_mul_self (hd : 0 < d) : sqrtNeg d * sqrtNeg d = -(d : ℂ) := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
  have h : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdR, Complex.ofReal_ratCast]
  rw [sqrtNeg]
  linear_combination (Complex.I * Complex.I) * h + (d : ℂ) * Complex.I_mul_I

theorem s4_pairing_fC_fC (hW : IsCompl P.W₁ P.W₂) (a b : V ℂ n) :
    pairing ℂ n (s4_extEnd ℝ ℂ n (P.fR hW) a) (s4_extEnd ℝ ℂ n (P.fR hW) b) =
      (d : ℂ) * pairing ℂ n a b := by
  have := s4_pairing_extEnd n (P.fR hW) (P.fR hW) d (P.s4_pairing_fR_fR hW) a b
  rw [this, Complex.ofReal_ratCast]

theorem s4_W₁ℂ_isotropic (hW : IsCompl P.W₁ P.W₂) (a b : V ℂ n) (ha : a ∈ P.W₁ℂ)
    (hb : b ∈ P.W₁ℂ) : pairing ℂ n a b = 0 := by
  have hd := P.d_pos
  rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at ha hb
  have h := P.s4_pairing_fC_fC hW a b
  rw [ha, hb] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, s4_sqrtNeg_mul_self hd] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (2 * (d : ℂ)) * pairing ℂ n a b = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hd')

theorem s4_W₂ℂ_isotropic (hW : IsCompl P.W₁ P.W₂) (a b : V ℂ n) (ha : a ∈ P.W₂ℂ)
    (hb : b ∈ P.W₂ℂ) : pairing ℂ n a b = 0 := by
  have hd := P.d_pos
  rw [s4_W₂ℂ_eq P hW, Module.End.mem_eigenspace_iff] at ha hb
  have h := P.s4_pairing_fC_fC hW a b
  rw [ha, hb] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, neg_mul_neg, s4_sqrtNeg_mul_self hd] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (2 * (d : ℂ)) * pairing ℂ n a b = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hd')

theorem s4_conjL_mem_W₂ℂ (hW : IsCompl P.W₁ P.W₂) (u : V ℂ n) (hu : u ∈ P.W₁ℂ) :
    s4_conjL n u ∈ P.W₂ℂ := by
  rw [← s4_map_conjL_W₁ℂ P hW]
  exact Submodule.mem_map_of_mem hu

theorem s4_conjL_mem_W₁ℂ (hW : IsCompl P.W₁ P.W₂) (u : V ℂ n) (hu : u ∈ P.W₂ℂ) :
    s4_conjL n u ∈ P.W₁ℂ := by
  rw [← s4_map_conjL_W₂ℂ P hW]
  exact Submodule.mem_map_of_mem hu

section PiProps
variable (hW : IsCompl P.W₁ P.W₂) (U : Submodule ℂ (V ℂ n)) (hU : U ≤ P.W₁ℂ)
  (hA : IsUnit (s4_AOp (projV U) (s4_HE n)))
include hW hU hA

theorem s4_PiV_W₂ℂ (w : V ℂ n) (hw : w ∈ P.W₂ℂ) : s4_PiV n (projV U) w = 0 := by
  apply (s4_PiV_props n U hA).2.2.2
  intro u hu
  exact P.s4_W₂ℂ_isotropic hW w _ hw (P.s4_conjL_mem_W₂ℂ hW u (hU hu))

theorem s4_PiV_fC (y : V ℂ n) :
    s4_PiV n (projV U) (s4_extEnd ℝ ℂ n (P.fR hW) y) =
      s4_extEnd ℝ ℂ n (P.fR hW) (s4_PiV n (projV U) y) := by
  have hy : y ∈ P.W₁ℂ ⊔ P.W₂ℂ := by rw [s4_W₁ℂ_sup_W₂ℂ P hW]; trivial
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  have hf₁ : s4_extEnd ℝ ℂ n (P.fR hW) y₁ = sqrtNeg d • y₁ := by
    rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at hy₁; exact hy₁
  have hf₂ : s4_extEnd ℝ ℂ n (P.fR hW) y₂ = (-sqrtNeg d) • y₂ := by
    rw [s4_W₂ℂ_eq P hW, Module.End.mem_eigenspace_iff] at hy₂; exact hy₂
  have hPi₁ : s4_PiV n (projV U) y₁ ∈ P.W₁ℂ := hU ((s4_PiV_props n U hA).1 y₁)
  have hfPi₁ : s4_extEnd ℝ ℂ n (P.fR hW) (s4_PiV n (projV U) y₁) =
      sqrtNeg d • s4_PiV n (projV U) y₁ := by
    rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at hPi₁; exact hPi₁
  have h0 := P.s4_PiV_W₂ℂ hW U hU hA y₂ hy₂
  rw [map_add, hf₁, hf₂, map_add, map_smul, map_smul, h0, smul_zero, add_zero, map_add, h0,
    add_zero, hfPi₁]

theorem s4_PiV_conjOp (y : V ℂ n) :
    s4_PiV n (projV U) (s4_conjOp n (s4_PiV n (projV U)) y) = 0 := by
  rw [s4_conjOp_apply]
  exact P.s4_PiV_W₂ℂ hW U hU hA _ (P.s4_conjL_mem_W₂ℂ hW _ (hU ((s4_PiV_props n U hA).1 _)))

theorem s4_conjOp_PiV (y : V ℂ n) :
    s4_conjOp n (s4_PiV n (projV U)) (s4_PiV n (projV U) y) = 0 := by
  rw [s4_conjOp_apply, P.s4_PiV_W₂ℂ hW U hU hA _
    (P.s4_conjL_mem_W₂ℂ hW _ (hU ((s4_PiV_props n U hA).1 _))), map_zero]


end PiProps

/-- `K(π_U)` is an `f`-linear isometric involution, `-1` on `U` (for `U ⊆ W_{1,ℂ}` with `A(π_U)`
invertible). -/
theorem s4_cartan_KOp (hW : IsCompl P.W₁ P.W₂) (U : Submodule ℂ (V ℂ n)) (hU : U ≤ P.W₁ℂ)
    (hA : IsUnit (s4_AOp (projV U) (s4_HE n))) :
    s4_KOp n (projV U) * s4_KOp n (projV U) = 1 ∧
    s4_KOp n (projV U) * P.fR hW = P.fR hW * s4_KOp n (projV U) ∧
    (∀ x y, pairing ℝ n (s4_KOp n (projV U) x) (s4_KOp n (projV U) y) = pairing ℝ n x y) ∧
    ∀ u ∈ U, s4_extEnd ℝ ℂ n (s4_KOp n (projV U)) u = -u := by
  have hKy : ∀ y, s4_extEnd ℝ ℂ n (s4_KOp n (projV U)) y =
      y - (2 : ℂ) • s4_PiV n (projV U) y - (2 : ℂ) • s4_conjOp n (s4_PiV n (projV U)) y :=
    fun y => by
      rw [s4_extEnd_KOp]
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]
  have hPP := s4_PiV_idem n U hA
  have hPcPc := s4_conjOp_idem n U hA
  have hPPc := P.s4_PiV_conjOp hW U hU hA
  have hPcP := P.s4_conjOp_PiV hW U hU hA
  have hPf := P.s4_PiV_fC hW U hU hA
  have hsa := s4_pairing_M n U hA
  have hPu : ∀ u ∈ U, s4_PiV n (projV U) u = u := (s4_PiV_props n U hA).2.1
  have hPcu : ∀ u ∈ U, s4_conjOp n (s4_PiV n (projV U)) u = 0 := fun u hu => by
    rw [s4_conjOp_apply, P.s4_PiV_W₂ℂ hW U hU hA _ (P.s4_conjL_mem_W₂ℂ hW u (hU hu)), map_zero]
  have hPcf : ∀ y, s4_conjOp n (s4_PiV n (projV U)) (s4_extEnd ℝ ℂ n (P.fR hW) y) =
      s4_extEnd ℝ ℂ n (P.fR hW) (s4_conjOp n (s4_PiV n (projV U)) y) := by
    intro y
    rw [s4_conjOp_apply, s4_conjOp_apply, s4_conjL_extEnd n (P.fR hW) y, hPf, s4_conjL_extEnd]
  set Pv := s4_PiV n (projV U) with hPv
  set Pc := s4_conjOp n Pv with hPc
  set K := s4_KOp n (projV U) with hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply s4_extEnd_injective ℝ ℂ n
    rw [s4_extEnd_mul, s4_extEnd_one]
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_apply, hKy, hKy]
    simp only [map_sub, map_smul, hPP, hPPc, hPcP, hPcPc, smul_zero, sub_zero, Module.End.one_apply]
    module
  · apply s4_extEnd_injective ℝ ℂ n
    rw [s4_extEnd_mul, s4_extEnd_mul]
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hKy, hKy, hPf, hPcf, map_sub, map_sub,
      map_smul, map_smul]
  · -- `K_ℂ = 1 - 2M` with `M = Π + Π̄` self-adjoint and idempotent
    have hM : ∀ a b, pairing ℂ n (s4_extEnd ℝ ℂ n K a) (s4_extEnd ℝ ℂ n K b) =
        pairing ℂ n a b := by
      intro a b
      have hKa : s4_extEnd ℝ ℂ n K a = a - (2 : ℂ) • (Pv a + Pc a) := by rw [hKy]; module
      have hKb : s4_extEnd ℝ ℂ n K b = b - (2 : ℂ) • (Pv b + Pc b) := by rw [hKy]; module
      have hMM : Pv (Pv b + Pc b) + Pc (Pv b + Pc b) = Pv b + Pc b := by
        rw [map_add, map_add, hPP, hPPc, hPcP, hPcPc, add_zero, zero_add]
      have h1 : pairing ℂ n (Pv a + Pc a) b = pairing ℂ n a (Pv b + Pc b) := hsa a b
      have h2 : pairing ℂ n (Pv a + Pc a) (Pv b + Pc b) = pairing ℂ n a (Pv b + Pc b) := by
        rw [hsa, hMM]
      rw [hKa, hKb]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [h1, h2]
      ring
    intro x y
    have := hM (bcV ℝ ℂ n x) (bcV ℝ ℂ n y)
    rw [s4_extEnd_bcV, s4_extEnd_bcV, s4_pairing_bcV_RC, s4_pairing_bcV_RC] at this
    exact_mod_cast this
  · intro u hu
    rw [hKy, hPu u hu, hPcu u hu, smul_zero, sub_zero]
    module

/-- `Ψ(T) = -f K(T)/√d`: the inverse of `ι` (for `T = π_{ι(I)}`). -/
noncomputable def s4_PsiOp (hW : IsCompl P.W₁ P.W₂) (T : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 * n + 2 * n))) : Module.End ℝ (V ℝ n) :=
  (-(Real.sqrt (d : ℝ))⁻¹) • (P.fR hW * s4_KOp n T)

/-- For `U ⊆ W_{1,ℂ}` of dimension `n` with `A(π_U)` invertible, `K(π_U)` negative and
`Ψ(π_U) ∈ SO_+(V_ℝ)`: `Ψ(π_U) ∈ Ω_P` and `ι(Ψ(π_U)) = U`. -/
theorem s4_PsiOp_mem (hW : IsCompl P.W₁ P.W₂) (U : Submodule ℂ (V ℂ n)) (hU : U ≤ P.W₁ℂ)
    (hUn : Module.finrank ℂ U = n) (hA : IsUnit (s4_AOp (projV U) (s4_HE n)))
    (hneg : ∀ x, x ≠ 0 → pairing ℝ n x (s4_KOp n (projV U) x) < 0)
    (hSO : ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = P.s4_PsiOp hW (projV U)) :
    P.s4_PsiOp hW (projV U) ∈ P.OmegaP hW ∧ V10 n (P.s4_PsiOp hW (projV U)) ⊓ P.W₁ℂ = U := by
  obtain ⟨hKK, hKf, hKiso, hKu⟩ := P.s4_cartan_KOp hW U hU hA
  have hmem : P.s4_PsiOp hW (projV U) ∈ P.OmegaP hW :=
    P.s4_mem_OmegaP_of_cartan_of_SOplus hW _ ⟨hKK, hKf, hKiso, hneg⟩ hSO
  refine ⟨hmem, ?_⟩
  have hd := P.d_pos
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hle : U ≤ V10 n (P.s4_PsiOp hW (projV U)) ⊓ P.W₁ℂ := by
    intro u hu
    refine Submodule.mem_inf.mpr ⟨?_, hU hu⟩
    rw [V10, Module.End.mem_eigenspace_iff, s4_complexifyV_eq, s4_PsiOp, s4_extEnd_smul,
      s4_extEnd_mul, LinearMap.smul_apply, Module.End.mul_apply, hKu u hu]
    simp only [map_neg]
    have hfu : s4_extEnd ℝ ℂ n (P.fR hW) u = sqrtNeg d • u := by
      have := hU hu
      rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at this
      exact this
    rw [hfu, smul_neg, smul_smul, ← neg_smul]
    congr 1
    have hsdC : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    rw [sqrtNeg, Complex.coe_algebraMap]
    push_cast
    field_simp
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hUn, P.finrank_V10_inf_W₁ℂ hW _ hmem]

/-- For an isometric complex structure, `V^{0,1}` is isotropic for `(·,·)_V`. -/
theorem s4_V01_isotropic (I : Module.End ℝ (V ℝ n))
    (hiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (a b : V ℂ n)
    (ha : a ∈ V01 n I) (hb : b ∈ V01 n I) : pairing ℂ n a b = 0 := by
  have h := s4_pairing_extEnd n I I 1 (fun x y => by rw [hiso, one_mul]) a b
  rw [V01, Module.End.mem_eigenspace_iff, s4_complexifyV_eq] at ha hb
  rw [ha, hb] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul] at h
  have : (2 : ℂ) * pairing ℂ n a b = 0 := by
    linear_combination -h + (pairing ℂ n a b) * Complex.I_mul_I
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- For `I ∈ Ω_P`, the complexified Cartan involution `K = f I/√d` is `-1` on `V^{1,0} ∩ W_{1,ℂ}` and
`1` on `V^{0,1} ∩ W_{1,ℂ}`. -/
theorem s4_extEnd_cartan_W₁ℂ (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) :
    (∀ u ∈ V10 n I ⊓ P.W₁ℂ,
      s4_extEnd ℝ ℂ n ((Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I)) u = -u) ∧
    (∀ u ∈ V01 n I ⊓ P.W₁ℂ,
      s4_extEnd ℝ ℂ n ((Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I)) u = u) := by
  have hd := P.d_pos
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsdC : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hf : ∀ u ∈ P.W₁ℂ, s4_extEnd ℝ ℂ n (P.fR hW) u = sqrtNeg d • u := fun u hu => by
    rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at hu; exact hu
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h10, h1⟩ := Submodule.mem_inf.mp hu
    rw [V10, Module.End.mem_eigenspace_iff, s4_complexifyV_eq] at h10
    rw [s4_extEnd_smul, s4_extEnd_mul, LinearMap.smul_apply, Module.End.mul_apply, h10, map_smul,
      hf u h1, smul_smul, smul_smul, ← neg_one_smul ℂ u]
    congr 1
    rw [sqrtNeg, Complex.coe_algebraMap]
    push_cast
    field_simp
    linear_combination Complex.I_mul_I
  · obtain ⟨h01, h1⟩ := Submodule.mem_inf.mp hu
    rw [V01, Module.End.mem_eigenspace_iff, s4_complexifyV_eq] at h01
    rw [s4_extEnd_smul, s4_extEnd_mul, LinearMap.smul_apply, Module.End.mul_apply, h01, map_smul,
      hf u h1, smul_smul, smul_smul]
    conv_rhs => rw [← one_smul ℂ u]
    congr 1
    rw [sqrtNeg, Complex.coe_algebraMap]
    push_cast
    field_simp
    linear_combination -Complex.I_mul_I

/-- For `I ∈ Ω_P`, `h` is positive definite on `ι(I) = V^{1,0} ∩ W_{1,ℂ}`. -/
theorem s4_hV_ne_zero_iota (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) (u : V ℂ n) (hu : u ∈ V10 n I ⊓ P.W₁ℂ) (hu0 : u ≠ 0) :
    s4_hV n u u ≠ 0 := by
  obtain ⟨⟨-, -, -, hneg⟩, -⟩ := P.s4_cartan_of_mem_OmegaP hW I hI
  set K₁ := (Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I)
  have hKu := (P.s4_extEnd_cartan_W₁ℂ hW I).1 u hu
  have hKa : K₁ (s4_reV n u) = -s4_reV n u := by
    rw [← s4_reV_extEnd, hKu, map_neg]
  have hKb : K₁ (s4_imV n u) = -s4_imV n u := by
    rw [← s4_imV_extEnd, hKu, map_neg]
  have hpos : ∀ a : V ℝ n, K₁ a = -a → a ≠ 0 → 0 < pairing ℝ n a a := fun a ha ha0 => by
    have := hneg a ha0
    rw [ha, map_neg] at this
    linarith
  have hnn : ∀ a : V ℝ n, K₁ a = -a → 0 ≤ pairing ℝ n a a := fun a ha => by
    by_cases ha0 : a = 0
    · rw [ha0]; simp
    · exact (hpos a ha ha0).le
  rw [s4_hV_self]
  intro h0
  have h0' : pairing ℝ n (s4_reV n u) (s4_reV n u) + pairing ℝ n (s4_imV n u) (s4_imV n u) = 0 :=
    by exact_mod_cast h0
  have ha := hnn _ hKa
  have hb := hnn _ hKb
  have ha0 : s4_reV n u = 0 := by
    by_contra h
    linarith [hpos _ hKa h]
  have hb0 : s4_imV n u = 0 := by
    by_contra h
    linarith [hpos _ hKb h]
  apply hu0
  rw [← s4_bcV_re_add_im n u, ha0, hb0, map_zero, smul_zero, add_zero]

theorem s4_isUnit_iota (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : IsUnit (s4_AOp (projV (V10 n I ⊓ P.W₁ℂ)) (s4_HE n)) :=
  s4_isUnit_AOp_V n _ fun u hu hu0 => P.s4_hV_ne_zero_iota hW I hI u hu hu0

/-- For `I ∈ Ω_P`, `K(π_{ι(I)}) = f I/√d`, hence `Ψ(π_{ι(I)}) = I`. -/
theorem s4_KOp_iota (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) :
    s4_KOp n (projV (V10 n I ⊓ P.W₁ℂ)) = (Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I) := by
  set U := V10 n I ⊓ P.W₁ℂ with hU_def
  have hU : U ≤ P.W₁ℂ := inf_le_right
  have hA := P.s4_isUnit_iota hW I hI
  have hcs : IsComplexStructure I := hI.2.1
  have hc := P.s4_comm_OmegaP hW I hI
  have hiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
    obtain ⟨⟨g, hg, hgI⟩, -⟩ := hI
    intro x y
    rw [← hgI]
    exact s4_pairing_of_mem_SOplus g hg.1 x y
  obtain ⟨hK1, hK2⟩ := P.s4_extEnd_cartan_W₁ℂ hW I
  obtain ⟨-, -, -, hKU⟩ := P.s4_cartan_KOp hW U hU hA
  set L₁ := s4_extEnd ℝ ℂ n (s4_KOp n (projV U))
  set L₂ := s4_extEnd ℝ ℂ n ((Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I))
  -- `L₁` and `L₂` agree on `V^{0,1} ∩ W_{1,ℂ}`
  have hU' : ∀ u ∈ V01 n I ⊓ P.W₁ℂ, L₁ u = L₂ u := by
    intro u hu
    rw [hK2 u hu]
    have hPu : s4_PiV n (projV U) u = 0 := by
      apply (s4_PiV_props n U hA).2.2.2
      intro w hw
      have hcw : s4_conjL n w ∈ V01 n I := by
        rw [← s4_map_conjL_V10 n I]
        exact Submodule.mem_map_of_mem (Submodule.mem_inf.mp hw).1
      exact s4_V01_isotropic I hiso u _ (Submodule.mem_inf.mp hu).1 hcw
    have hPcu : s4_conjOp n (s4_PiV n (projV U)) u = 0 := by
      rw [s4_conjOp_apply, P.s4_PiV_W₂ℂ hW U hU hA _
        (P.s4_conjL_mem_W₂ℂ hW u (Submodule.mem_inf.mp hu).2), map_zero]
    show s4_extEnd ℝ ℂ n (s4_KOp n (projV U)) u = u
    rw [s4_extEnd_KOp]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, hPu, hPcu,
      smul_zero, sub_zero]
  have hW₁ : P.W₁ℂ ≤ LinearMap.eqLocus L₁ L₂ := by
    rw [(P.s4_Wℂ_split hW I hcs hc).1]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [inf_comm] at hu
      show L₁ u = L₂ u
      rw [hKU u hu, hK1 u hu]
    · rw [inf_comm] at hu
      exact hU' u hu
  have hconj : ∀ y, L₁ y = L₂ y → L₁ (s4_conjL n y) = L₂ (s4_conjL n y) := by
    intro y hy
    rw [← s4_conjL_extEnd, ← s4_conjL_extEnd, hy]
  have hW₂ : P.W₂ℂ ≤ LinearMap.eqLocus L₁ L₂ := by
    rw [← s4_map_conjL_W₁ℂ P hW]
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y (hW₁ hy)
  have htop : LinearMap.eqLocus L₁ L₂ = ⊤ := by
    rw [eq_top_iff, ← s4_W₁ℂ_sup_W₂ℂ P hW]
    exact sup_le hW₁ hW₂
  apply s4_extEnd_injective ℝ ℂ n
  exact LinearMap.eqLocus_eq_top.mp htop

theorem s4_PsiOp_iota (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) : P.s4_PsiOp hW (projV (V10 n I ⊓ P.W₁ℂ)) = I := by
  rw [s4_PsiOp, P.s4_KOp_iota hW I hI]
  exact ((P.s4_cartan_of_mem_OmegaP hW I hI).2).symm

/-- `F = 1 - (i/√d) f`, `½ F` is the projection onto `W_{1,ℂ}` along `W_{2,ℂ}`. -/
noncomputable def s4_FV (hW : IsCompl P.W₁ P.W₂) : V ℂ n →ₗ[ℂ] V ℂ n :=
  1 - (Complex.I / ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) • s4_extEnd ℝ ℂ n (P.fR hW)

/-- `E(I) = ¼ (1 - i I) F`, transported to `ℂ^{4n}`: an operator onto `ι(I)` fixing it. -/
noncomputable def s4_EE (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) :
    EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * n + 2 * n)) :=
  (1 / 4 : ℂ) • (LinearMap.toContinuousLinearMap
    ((eucV n).toLinearMap ∘ₗ P.s4_FV hW ∘ₗ (eucV n).symm.toLinearMap) -
      Complex.I • s4_LE n (P.s4_FV hW) I)

theorem s4_EE_eucV (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) (y : V ℂ n) :
    P.s4_EE hW I (eucV n y) = eucV n ((1 / 4 : ℂ) • (P.s4_FV hW y -
      Complex.I • s4_extEnd ℝ ℂ n I (P.s4_FV hW y))) := by
  simp [s4_EE, s4_LE]

theorem s4_continuous_EE (hW : IsCompl P.W₁ P.W₂) :
    @Continuous _ _ (endTopology n) _ (P.s4_EE hW) := by
  let := endTopology n
  have h1 := s4_continuous_end_linear n (s4_LE n (P.s4_FV hW))
  unfold s4_EE
  exact (continuous_const.sub (h1.const_smul Complex.I)).const_smul (1 / 4 : ℂ)

theorem s4_fC_fC (hW : IsCompl P.W₁ P.W₂) (y : V ℂ n) :
    s4_extEnd ℝ ℂ n (P.fR hW) (s4_extEnd ℝ ℂ n (P.fR hW) y) = -((d : ℂ) • y) := by
  have h : P.fR hW * P.fR hW = -((d : ℝ) • (1 : Module.End ℝ (V ℝ n))) :=
    LinearMap.ext fun x => by
      rw [Module.End.mul_apply, P.s4_fR_fR hW]
      simp
  have := congrArg (fun A => s4_extEnd ℝ ℂ n A y) h
  simp only [s4_extEnd_mul, Module.End.mul_apply, s4_extEnd_neg, s4_extEnd_smul,
    s4_extEnd_one, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply] at this
  rw [this, Complex.coe_algebraMap, Complex.ofReal_ratCast]

theorem s4_FV_mem (hW : IsCompl P.W₁ P.W₂) (y : V ℂ n) : P.s4_FV hW y ∈ P.W₁ℂ := by
  have hd := P.d_pos
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsdC : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hsd2 : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hd.le), Complex.ofReal_ratCast]
  rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff, s4_FV]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, map_sub, map_smul,
    P.s4_fC_fC hW, smul_neg, sub_neg_eq_add, sqrtNeg, smul_sub, smul_smul]
  rw [show Complex.I / ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * (d : ℂ) =
      Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) by field_simp; rw [← hsd2]; ring,
    show Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * (Complex.I / ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) =
      -1 by field_simp; rw [Complex.I_sq]]
  module

theorem s4_EV_mem (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hcs : IsComplexStructure I) (hc : I * P.fR hW = P.fR hW * I) (y : V ℂ n) :
    (1 / 4 : ℂ) • (P.s4_FV hW y - Complex.I • s4_extEnd ℝ ℂ n I (P.s4_FV hW y)) ∈
      V10 n I ⊓ P.W₁ℂ := by
  refine Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [V10, Module.End.mem_eigenspace_iff, s4_complexifyV_eq, map_sub, map_smul]
    have hII : s4_extEnd ℝ ℂ n I (s4_extEnd ℝ ℂ n I (P.s4_FV hW y)) = -(P.s4_FV hW y) := by
      rw [← Module.End.mul_apply, ← s4_extEnd_mul, show I * I = -1 from hcs, s4_extEnd_neg,
        s4_extEnd_one]
      rfl
    rw [hII]
    simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add]
    abel
  · have hmaps := (P.s4_mapsTo_Wℂ hW I hc).1
    exact Submodule.sub_mem _ (P.s4_FV_mem hW y)
      (Submodule.smul_mem _ _ (hmaps _ (P.s4_FV_mem hW y)))

theorem s4_EV_fix (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) (u : V ℂ n)
    (hu : u ∈ V10 n I ⊓ P.W₁ℂ) :
    (1 / 4 : ℂ) • (P.s4_FV hW u - Complex.I • s4_extEnd ℝ ℂ n I (P.s4_FV hW u)) = u := by
  obtain ⟨h10, h1⟩ := Submodule.mem_inf.mp hu
  rw [V10, Module.End.mem_eigenspace_iff, s4_complexifyV_eq] at h10
  rw [s4_W₁ℂ_eq P hW, Module.End.mem_eigenspace_iff] at h1
  have hd := P.d_pos
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsdC : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hF : P.s4_FV hW u = (2 : ℂ) • u := by
    rw [s4_FV, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, h1, smul_smul,
      sqrtNeg, show Complex.I / ((Real.sqrt (d : ℝ) : ℝ) : ℂ) *
        (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = -1 by field_simp; rw [Complex.I_sq]]
    module
  rw [hF, map_smul, h10]
  simp only [smul_smul]
  rw [← sub_smul, smul_smul]
  conv_rhs => rw [← one_smul ℂ u]
  congr 1
  linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I

/-- `ι` is continuous: `‖π_{ι(I)} - π_{ι(I₀)}‖ ≤ 2 ‖E(I) - E(I₀)‖`. -/
theorem s4_continuous_iota (hW : IsCompl P.W₁ P.W₂) :
    @Continuous _ _ (@instTopologicalSpaceSubtype _ _ (endTopology n)) _ (P.iota hW) := by
  let := endTopology n
  rw [continuous_induced_rng]
  have hT : ∀ I : P.OmegaP hW, ∀ x, P.s4_EE hW I.1 x ∈
      (P.iota hW I).1.map (eucV n).toLinearMap := by
    intro I x
    rw [← (eucV n).apply_symm_apply x, P.s4_EE_eucV hW]
    exact Submodule.mem_map_of_mem (P.s4_EV_mem hW I.1 I.2.2.1 (P.s4_comm_OmegaP hW I.1 I.2) _)
  have hTU : ∀ I : P.OmegaP hW, ∀ u ∈ (P.iota hW I).1.map (eucV n).toLinearMap,
      P.s4_EE hW I.1 u = u := by
    rintro I _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, P.s4_EE_eucV hW, P.s4_EV_fix hW I.1 v hv]
  refine continuous_iff_continuousAt.2 fun I₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ I : P.OmegaP hW, ‖projV (P.iota hW I).1 - projV (P.iota hW I₀).1‖ ≤
      2 * ‖P.s4_EE hW I.1 - P.s4_EE hW I₀.1‖ := fun I =>
    s4_norm_starProjection_sub_le _ _ _ _ (hT I) (hT I₀) (hTU I) (hTU I₀)
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have := ((P.s4_continuous_EE hW).comp continuous_subtype_val).tendsto I₀
  rw [tendsto_iff_norm_sub_tendsto_zero] at this
  simpa using this.const_mul 2

theorem s4_continuousAt_PsiOp (hW : IsCompl P.W₁ P.W₂)
    (T₀ : EuclideanSpace ℂ (Fin (2 * n + 2 * n)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * n + 2 * n)))
    (hA : IsUnit (s4_AOp T₀ (s4_HE n))) :
    @ContinuousAt _ _ _ (endTopology n) (fun T => P.s4_PsiOp hW T) T₀ := by
  let := endTopology n
  rw [(Topology.IsInducing.induced (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n))).continuousAt_iff]
  have h : (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)) ∘ (fun T => P.s4_PsiOp hW T) =
      fun T => (-(Real.sqrt (d : ℝ))⁻¹) • (LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) (P.fR hW) *
        LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) (s4_KOp n T)) := by
    funext T
    simp only [Function.comp_apply, s4_PsiOp, map_smul, LinearMap.toMatrix_mul]
  rw [h]
  exact (continuousAt_const.mul (s4_continuousAt_KOp n T₀ hA)).const_smul
    (-(Real.sqrt (d : ℝ))⁻¹)

theorem s4_PsiOp_iota' (hW : IsCompl P.W₁ P.W₂) (I : P.OmegaP hW) :
    P.s4_PsiOp hW (projV (P.iota hW I).1) = I.1 :=
  P.s4_PsiOp_iota hW I.1 I.2

theorem s4_isUnit_iota' (hW : IsCompl P.W₁ P.W₂) (I : P.OmegaP hW) :
    IsUnit (s4_AOp (projV (P.iota hW I).1) (s4_HE n)) :=
  P.s4_isUnit_iota hW I.1 I.2

theorem s4_continuousAt_g (hW : IsCompl P.W₁ P.W₂) (I : P.OmegaP hW) :
    @ContinuousAt _ _ _ (endTopology n) (fun U : P.GrW₁ => P.s4_PsiOp hW (projV U.1))
      (P.iota hW I) := by
  let := endTopology n
  have h1 : ContinuousAt (fun U : P.GrW₁ => projV U.1) (P.iota hW I) :=
    continuous_induced_dom.continuousAt
  have h2 := P.s4_continuousAt_PsiOp hW (projV (P.iota hW I).1) (P.s4_isUnit_iota' hW I)
  have h3 := ContinuousAt.comp (f := fun U : P.GrW₁ => projV U.1) (x := P.iota hW I) h2 h1
  simpa only [Function.comp_def] using h3


end KSecant

/-! ## Lemma 4.0.1 -/

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`). The map `ι` is
an embedding of `Ω_P` as a non-empty subset, open in the classical topology, of the Grassmannian
`Gr(n, W_{1,ℂ})`. This part: `ι` is injective. Standing assumption: Assumption 2.4.1. -/
theorem lemma4_0_1_injective (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : Function.Injective (P.iota hP.isCompl) := by
  -- `I` is the unique complex structure with `V^{1,0}_I = U ⊕ (U^⊥ ∩ W_{2,ℂ})`, `U = ι(I)`, by (3.2.1)
  have key : ∀ I : P.OmegaP hP.isCompl, V10 n I.1 =
      V10 n I.1 ⊓ P.W₁ℂ ⊔ (pairing ℂ n).orthogonal (V10 n I.1 ⊓ P.W₁ℂ) ⊓ P.W₂ℂ := by
    intro I
    rw [← equation3_2_1 P J hP I.1 (P.s4_exists_lift_OmegaP J hP I.1 I.2) I.2.2.1
      (P.s4_nu_OmegaP hP.isCompl I.1 I.2)]
    exact P.s4_V10_split hP.isCompl I.1 (P.s4_comm_OmegaP hP.isCompl I.1 I.2)
  intro I I' h
  have hU : V10 n I.1 ⊓ P.W₁ℂ = V10 n I'.1 ⊓ P.W₁ℂ := congrArg Subtype.val h
  apply Subtype.ext
  apply s4_eq_of_V10_eq n I.1 I'.1 I.2.2.1
  rw [key I, key I', hU]

/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): `Ω_P` is non-empty.

The paper's proof uses `I = I_{V_ℝ}` (the complex structure of `X × X̂`) and Proposition 2.4.4,
which concerns `P = P_Θ` (`productStructure_mem_OmegaP`). The statement holds for every `P`
satisfying Assumption 2.4.1: `H` has signature `(n, n)` (Lemma 3.1.2), so `V_ℝ` has an `f`-stable
maximal negative definite subspace `V₋` (for `(·,·)_V`); with `f̃ = f/√d` and `K = 1` on `V₋`,
`K = -1` on `V₋^⊥`, `I = -f̃ K` lies in `Ω_P` (`g_I(x, x) = -√d (x, K x)_V`; `SO_+` by
Remark 2.4.3).

Gap in the paper (reason 1): the paper shows `I_{V_ℝ} ∈ Ω_P` using Proposition 2.4.4 (TeX
1743–1747), which is about the plane `P = P_Θ` of (2.4.5) only (TeX 1370; that case is
`productStructure_mem_OmegaP`, which follows the paper: Proposition 2.4.4, Lemma 2.2.6,
Remark 2.4.3); for a general `P` satisfying Assumption 2.4.1 the form `g_{I_{V_ℝ}} = -g_P` need not
be definite. Here we use instead the `H`-orthogonal `K`-basis `b₁, …, b_{2n}` of Lemma 3.1.2
(signature `(n, n)`): `bᵢ, f bᵢ` is a `(·,·)_V`-orthogonal basis of `V_ℝ`, `K = 1` on
`span(bᵢ, f bᵢ)` when `(bᵢ, bᵢ)_V < 0` and `K = -1` otherwise, and `I = -f K/√d`
(`KSecant.s4_exists_mem_OmegaP`; `I ∈ SO_+(V_ℝ)` by Remark 2.4.3, as in the paper). -/
theorem lemma4_0_1_nonempty (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : (P.OmegaP hP.isCompl).Nonempty :=
  P.s4_exists_mem_OmegaP J hP

open scoped Topology in
/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): the image of
`ι` is open in the classical topology of `Gr(n, W_{1,ℂ})`.

As in the paper (TeX 1729–1741), for `U` near `ι(I₀)` we construct `I_U ∈ Ω_P` with `ι(I_U) = U`.
The paper's `V^{1,0}_{I_U} = U ⊕ (U^⊥ ∩ W_{2,ℂ})` is made explicit by the Cartan involution
`K_U = (f I_U)/√d = 1 - 2(Π_U + Π̄_U)` on `V_ℂ`, where `Π_U` is the projection onto `U` orthogonal
for the Hermitian form `h(x, y) = (x, ȳ)_V`, computed from the orthogonal projection `π_U` defining
the topology as `Π_U = A(π_U)⁻¹ π_U H`, `A(π) = π H π + 1 - π`; then `I_U = Ψ(π_U) = -f K_U/√d`
(`KSecant.s4_PsiOp`). The paper's open conditions: `V^{1,0}_U` and `V^{0,1}_U` transversal (here:
`A(π_U)` invertible, an open condition); `g_{I_U}` positive definite (here: `(x, K_U x)_V < 0` for
`x ≠ 0`, open by continuity of `π ↦ K_π`: `s4_eventually_neg`, `s4_continuousAt_KOp_end`); and
`I_U` preserves the orientation of the positive cone, i.e. `I_U ∈ SO_+(V_ℝ) = ρ(Spin(V_ℝ))` (open:
`ρ(Spin(V_ℝ))` is open in `SO(V_ℝ)` and `π ↦ I_π` is continuous; `s4_eventually_mem_SOplus`,
`KSecant.s4_continuousAt_PsiOp`). The conditions `K_U² = 1`, `K_U f = f K_U` and `K_U` orthogonal
hold identically (`KSecant.s4_cartan_KOp`), so `I_U` is an orthogonal complex structure commuting
with `f` (`KSecant.s4_cs_of_cartan`); it lies in `SO_+(V_ℝ)_f` (determinant `1` on `W_{i,ℂ}` by
Lemma 3.2.1) and in `Ω_P` (`KSecant.s4_mem_OmegaP_of_cartan_of_SOplus`). The paper gets
`ν(I_U) = 2n` from `E_{-√d}(I_U ∘ f) = U ⊕ Ū`; here both eigenspaces of `f ∘ I_U = √d K_U` are
`2n`-dimensional because those of `K_U` are definite (mechanics). -/
theorem lemma4_0_1_isOpen (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : IsOpen (Set.range (P.iota hP.isCompl)) := by
  set hW := hP.isCompl
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨I₀, rfl⟩
  set T₀ := projV (P.iota hW I₀).1 with hT₀
  have hA₀ : IsUnit (s4_AOp T₀ (s4_HE n)) := P.s4_isUnit_iota hW I₀.1 I₀.2
  have hΨ₀ : P.s4_PsiOp hW T₀ = I₀.1 := P.s4_PsiOp_iota hW I₀.1 I₀.2
  have hneg₀ : ∀ x, x ≠ 0 → pairing ℝ n x (s4_KOp n T₀ x) < 0 := by
    have hK₀ : s4_KOp n T₀ = (Real.sqrt (d : ℝ))⁻¹ • (P.fR hW * I₀.1) := P.s4_KOp_iota hW I₀.1 I₀.2
    rw [hK₀]
    exact (P.s4_cartan_of_mem_OmegaP hW I₀.1 I₀.2).1.2.2.2
  -- the open conditions: `A(π)` invertible (transversality), `(x, K_π x)_V < 0` (`g_{I_π}`
  -- positive definite), and `I_π ∈ SO_+(V_ℝ)` (`I_π` preserves the orientation of the positive cone)
  have hN : ∀ᶠ T in 𝓝 T₀, IsUnit (s4_AOp T (s4_HE n)) ∧
      (∀ x, x ≠ 0 → pairing ℝ n x (s4_KOp n T x) < 0) ∧
      (IsComplexStructure (P.s4_PsiOp hW T) →
        (∀ a b, pairing ℝ n (P.s4_PsiOp hW T a) (P.s4_PsiOp hW T b) = pairing ℝ n a b) →
          ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = P.s4_PsiOp hW T) := by
    refine Filter.Eventually.and (s4_eventually_isUnit_AOp _ _ hA₀) (Filter.Eventually.and ?_ ?_)
    · let := endTopology n
      exact (s4_continuousAt_KOp_end n T₀ hA₀).eventually (s4_eventually_neg n _ hneg₀)
    · refine s4_eventually_mem_SOplus n (fun T => P.s4_PsiOp hW T) T₀
        (P.s4_continuousAt_PsiOp hW T₀ hA₀) ?_ ?_
      · show IsComplexStructure (P.s4_PsiOp hW T₀)
        rw [hΨ₀]
        exact I₀.2.2.1
      · obtain ⟨⟨g, hg, hgI⟩, -⟩ := I₀.2
        exact ⟨g, hg.1, hgI.trans hΨ₀.symm⟩
  have hpre : (fun U : P.GrW₁ => projV U.1) ⁻¹' {T | IsUnit (s4_AOp T (s4_HE n)) ∧
      (∀ x, x ≠ 0 → pairing ℝ n x (s4_KOp n T x) < 0) ∧
      (IsComplexStructure (P.s4_PsiOp hW T) →
        (∀ a b, pairing ℝ n (P.s4_PsiOp hW T a) (P.s4_PsiOp hW T b) = pairing ℝ n a b) →
          ∃ g ∈ SOplus ℝ n, (g : Module.End ℝ (V ℝ n)) = P.s4_PsiOp hW T)} ∈
        𝓝 (P.iota hW I₀) :=
    continuous_induced_dom.continuousAt.preimage_mem_nhds hN
  refine Filter.mem_of_superset hpre ?_
  rintro U ⟨hUA, hUneg, hUSO⟩
  -- `I_U = -f K_U/√d` is an orthogonal complex structure (`K_U² = 1`, `K_U f = f K_U`, `K_U`
  -- orthogonal), so it lies in `SO_+(V_ℝ)` by the orientation condition
  obtain ⟨hKK, hKf, hKiso, -⟩ := P.s4_cartan_KOp hW U.1 U.2.1 hUA
  obtain ⟨hcs, hiso⟩ := P.s4_cs_of_cartan hW _ hKK hKf hKiso
  have hΨ : (-(Real.sqrt d)⁻¹) • (P.fR hW * s4_KOp n (projV U.1)) = P.s4_PsiOp hW (projV U.1) :=
    rfl
  rw [hΨ] at hcs hiso
  beta_reduce at hUSO
  obtain ⟨hmem, heq⟩ := P.s4_PsiOp_mem hW U.1 U.2.1 U.2.2 hUA hUneg (hUSO hcs hiso)
  exact ⟨⟨_, hmem⟩, Subtype.ext heq⟩

open scoped Topology in
/-- **Lemma 4.0.1** (`lemma-coadjoint-orbit-embedds-as-open-subset-of-Grassmannian`): `ι` is an embedding (a homeomorphism onto its image) for the subspace topology
of `Ω_P ⊆ End(V_ℝ)`. Reading: "embedding" in the topological sense; the proof constructs the
inverse `U ↦ I_U`, `V^{1,0}_{I_U} = U ⊕ (U^⊥ ∩ W_{2,ℂ})`.

Injectivity is `lemma4_0_1_injective`. Continuity of `ι`: `π_{ι(I)}` is the orthogonal projection onto
the image of the operator `E(I) = ¼ (1 - i I)(1 - i f/√d)`, which fixes `ι(I)`, and
`‖π_U - π_{U'}‖ ≤ 2 ‖E - E'‖` (`KSecant.s4_continuous_iota`). Continuity of the inverse: `I` is
recovered from `π = π_{ι(I)}` by the continuous formula `I = Ψ(π) = -f K_π/√d` of
`lemma4_0_1_isOpen` (`KSecant.s4_PsiOp_iota`, `KSecant.s4_continuousAt_PsiOp`). -/
theorem lemma4_0_1_isEmbedding (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    @Topology.IsEmbedding _ _ (@instTopologicalSpaceSubtype _ _ (endTopology n)) _
      (P.iota hP.isCompl) := by
  set hW := hP.isCompl
  let := endTopology n
  have hcont := P.s4_continuous_iota hW
  have hind : Topology.IsInducing (P.iota hW) := by
    rw [Topology.isInducing_iff_nhds]
    intro I₀
    refine le_antisymm (hcont.tendsto I₀).le_comap ?_
    obtain ⟨g, hg_def⟩ : ∃ g : P.GrW₁ → Module.End ℝ (V ℝ n),
        g = fun U => P.s4_PsiOp hW (projV U.1) := ⟨_, rfl⟩
    have hg : ContinuousAt g (P.iota hW I₀) := by
      rw [hg_def]
      exact P.s4_continuousAt_g hW I₀
    have hgι : g ∘ P.iota hW = Subtype.val := by
      rw [hg_def]
      funext I
      simp only [Function.comp_apply]
      exact P.s4_PsiOp_iota' hW I
    have hgI₀ : g (P.iota hW I₀) = I₀.1 := congrFun hgι I₀
    calc Filter.comap (P.iota hW) (𝓝 (P.iota hW I₀))
        ≤ Filter.comap (P.iota hW) (Filter.comap g (𝓝 (g (P.iota hW I₀)))) :=
          Filter.comap_mono hg.tendsto.le_comap
      _ = Filter.comap (g ∘ P.iota hW) (𝓝 (g (P.iota hW I₀))) := Filter.comap_comap
      _ = Filter.comap Subtype.val (𝓝 I₀.1) := by rw [hgι, hgI₀]
      _ = 𝓝 I₀ := (nhds_subtype _ I₀).symm
  exact ⟨hind, lemma4_0_1_injective P J hP⟩

/-- In the proof of Lemma 4.0.1 (nonemptiness): for `P = P_Θ` with `Θ` ample for `J`, the complex
structure `I = I_{V_ℝ} = productStructure n J` of `X × X̂` lies in `Ω_{P_Θ}`: `g_I = -g_P` is positive
definite by Proposition 2.4.4, `I` commutes with `f` (Lemma 2.2.6), lies in `SO_+(V_ℝ)` (Remark
2.4.3), has determinant `1` on `W₁` and `W₂`, and `ν(I) = 2n`. -/
theorem productStructure_mem_OmegaP (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    productStructure n J ∈ (PTheta n d hd Θ hΘ.mem_exteriorPower_two
      (hΘ.ne_zero_of_pos hn)).OmegaP (PTheta_isCompl n d hd Θ _ _ hΘ.bijective_thetaMap) := by
  set P := PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)
  have hP : Assumption2_4_1 P J := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  show productStructure n J ∈ P.OmegaP hP.isCompl
  have hcs := isComplexStructure_productStructure J hJ
  have hc : productStructure n J * P.fR hP.isCompl = P.fR hP.isCompl * productStructure n J :=
    (P.fR_comm_productStructure J hP).symm
  -- Lemma 2.2.6: the four summands `W_{i,ℂ} ∩ V^{1,0}`, `W_{i,ℂ} ∩ V^{0,1}` are `n`-dimensional
  obtain ⟨d1, d2⟩ := lemma2_2_6 P hd hP.nonIsotropic J hJ hP.hodge
  obtain ⟨d3, d4⟩ := lemma2_2_6_V01 P hd hP.nonIsotropic J hJ hP.hodge
  -- Remark 2.4.3: `I` lies in `SO_+(V_ℝ)`
  obtain ⟨x, hx⟩ := remark2_4_3 J hJ
  have heig := P.s4_finrank_eig_fI hP.isCompl _ hc
  rw [inf_comm (V10 n _), inf_comm (V01 n _), inf_comm (V01 n _), inf_comm (V10 n _ ) P.W₂ℂ,
    d1, d2, d3, d4] at heig
  refine ⟨⟨rho ℝ n x, ?_, hx⟩, hcs, by rw [heig.2]; ring, by rw [heig.1]; ring, ?_⟩
  · refine P.s4_mem_SOplusfR_of_cs hP.isCompl _ (KSecant.s4_rho_mem_SOplus x) (hx ▸ hcs) (hx ▸ hc) ?_ ?_
    · rw [hx, d1, d3]
    · rw [hx, d2, d4]
  · -- `g_I = -g_P` is positive definite by Proposition 2.4.4
    intro v hv
    rw [P.gI_productStructure J hP, LinearMap.neg_apply, LinearMap.neg_apply, neg_pos]
    exact proposition2_4_4 n d hd hn J hJ Θ hΘ v hv

/-! ## Lemma 4.0.2 -/

/-- **Lemma 4.0.2** (`lemma-period-domain-is-an-adjoint-orbit`). The connected components of `Ω_P`
are `SO_+(V_ℝ)_f`-adjoint orbits: for `I ∈ Ω_P`, the connected component of `I` in `Ω_P` (subspace
topology of `End(V_ℝ)`) is the adjoint orbit of `I`. Standing assumption: Assumption 2.4.1.
(Proved by the authorized departure: direct transitivity of `SO_+(V_ℝ)_f ≅ SU(n, n)` on `Ω_P`,
instead of the paper's dimension count; in fact `Ω_P` is a single adjoint orbit.)

The first step of the paper's proof (`Ω_P` is a union of adjoint orbits, `g_{hIh⁻¹}(x, y) =
g_I(h⁻¹x, h⁻¹y)`) is `KSecant.adjointOrbit_subset_OmegaP`.

Departure from the paper (authorized; reason 2: the paper's count needs dimensions of orbits of
real Lie group actions, which Lean lacks): the paper (TeX 1772–1803) compares the dimension
`4n² - 1` of `SO_+(V_ℝ)_f` with that of the stabilizer of `I` and of `Ω_P`; here we show directly
that `Ω_P` is a single `SO_+(V_ℝ)_f`-adjoint orbit and is (path) connected, so that it is its own
connected component. For `I ∈ Ω_P`, `K = f I/√d` is a "Cartan involution": `K² = 1`, `K f = f K`, `K`
preserves `(·,·)_V` and `(x, K x)_V < 0` for `x ≠ 0`; conversely every such `K` gives
`I = -f K/√d ∈ Ω_P` (`KSecant.s4_cartan_of_mem_OmegaP`, `KSecant.s4_mem_OmegaP_of_cartan`; the
eigenspaces of `K` are definite, hence of dimension `≤ 2n`, hence `= 2n`; `I ∈ SO_+(V_ℝ)` by
Remark 2.4.3). For two such `K₀, K₁`,
`P = K₀ K₁` is self-adjoint and positive definite for the inner product `-(·, K₀ ·)_V`, and
`K_t = K₀ P^t` (`t ∈ ℝ`, spectral calculus) is a continuous path of such involutions from `K₀` to
`K₁` (`KSecant.s4_cartan_path`); the corresponding `I_t` is a path in `Ω_P`, and the midpoint
`h = I_{1/2} ∈ Ω_P ⊆ SO_+(V_ℝ)_f` satisfies `h I₀ h⁻¹ = I₁` since `K_{1/2} K₀ K_{1/2} = K₁`
(`KSecant.s4_OmegaP_join`). -/
theorem lemma4_0_2 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    @connectedComponentIn _ (endTopology n) (P.OmegaP hP.isCompl) I =
      P.adjointOrbit hP.isCompl I := by
  let := endTopology n
  have hpre : IsPreconnected (P.OmegaP hP.isCompl) := by
    refine isPreconnected_of_forall_pair fun x hx y hy => ?_
    obtain ⟨⟨γ, hγ, h0, h1, hmem⟩, -⟩ := P.s4_OmegaP_join hP.isCompl x y hx hy
    refine ⟨γ '' Set.Icc 0 1, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩,
      isPreconnected_Icc.image γ hγ.continuousOn⟩
    rintro _ ⟨t, -, rfl⟩
    exact hmem t
  rw [hpre.connectedComponentIn hI]
  refine Set.Subset.antisymm (fun I' hI' => ?_) (P.adjointOrbit_subset_OmegaP J hP I hI)
  obtain ⟨-, h, hh, hhI⟩ := P.s4_OmegaP_join hP.isCompl I I' hI hI'
  exact ⟨h, hh, hhI⟩

end WeilClasses
