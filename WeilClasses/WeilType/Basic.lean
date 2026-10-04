module

public import WeilClasses.PureSpinor.CM
public import WeilClasses.Hodge.Defs
public import Mathlib.Algebra.Algebra.Rat
import WeilClasses.PureSpinor.Lemma2_2_4
import WeilClasses.PureSpinor.Lemma2_2_6
import WeilClasses.External.Igusa.Sec2_4
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# Polarized abelian varieties of Weil type from oriented `K`-secants: the setup (paper §2.4)

The first half of §2.4 of the paper (TeX lines 1223–1308):

* Assumption 2.4.1 (`WeilClasses.Assumption2_4_1`) and its consequence `V_K = W₁ ⊕ W₂`;
* the similarity `f = η_{√-d}` of (2.4.1) (`WeilClasses.KSecant.fη`, defined in
  `WeilClasses.PureSpinor.CM`): `f ∈ Õ(V_ℚ)`, `(f x, f y)_V = d (x, y)_V`, `f² = -d`, `f`
  anti-self-dual;
* the `2`-form `Ξ_P(x, y) = (f x, y)_V` of (2.4.2) (`KSecant.XiQ`; on `V_ℝ`, `KSecant.XiR`):
  nondegenerate, equal to `√-d ((x₁, y₂)_V - (x₂, y₁)_V)`;
* the subspaces `W_{i,ℂ} ⊆ V_ℂ` (`KSecant.W₁ℂ`, `KSecant.W₂ℂ`) and the decomposition
  `v = v₁^{1,0} + v₂^{1,0} + v₁^{0,1} + v₂^{0,1}` with its conjugation rules;
* the complex structure `I = I_{V_ℝ}` of `X × X̂` (`productStructure n J`): an isometry,
  anti-self-dual, with isotropic `V^{1,0}` and `V^{0,1}`, commuting with `f`; `Ξ_P` of type `(1,1)`;
  the symmetric form `g_P(x, y) = Ξ_P(I x, y)` (`KSecant.gP`) and Lemma 2.4.2;
* Remark 2.4.3: the lift `ϖ̃(λ) ∈ Spin(V_F)` of `ϖ(λ)` (`WeilClasses.varpiTilde`), and the lift of
  an orthogonal complex structure of `V_ℝ` to `Spin(V_ℝ)`.

The second half of §2.4 (the class `Θ`, `exp(√-d Θ)`, the plane `P_Θ` and Proposition 2.4.4) is in
`WeilClasses.WeilType.Theta`.

## Conventions

* `V_F = H¹(X, F)* × H¹(X, F)`, pairs `(y, w)` (Mathlib's order; the paper writes `(w, y)`); the
  pairing (1.2.2) is `pairing F n`.
* `K = Kd d ⊆ ℂ` with `√-d = i √d` (`Kd.sqrtNeg d`); `σ` is complex conjugation.
* `W₁, W₂ ⊆ V_K` are the maximal isotropic subspaces `ker m_{u₁}`, `ker m_{u₂}` of the `K`-secant
  `P`; `W_{i,ℂ}` is the `ℂ`-span of `Wᵢ` in `V_ℂ` (`bcV (Kd d) ℂ n`).
* The `F'`-linear extension of a rational endomorphism of `V_ℚ` (`F' = K, ℝ, ℂ`) is computed in the
  bases `basisV` (`WeilClasses.bcEndV`); `f` on `V_ℝ` is `KSecant.fR`.
* The complex structure of `V_ℝ = H¹(X × X̂, ℝ)` induced by the complex structure `J` of
  `H¹(X, ℝ)` (with `H^{1,0}(X)` its `i`-eigenspace) is, in the paper's convention (footnote in §2.4:
  the dual of the tangent complex structures, a dual composing with `-I`),
  `productStructure n J : (y, w) ↦ (y ∘ J, -J w)`, the negative of the standard Hodge structure;
  the paper's `V^{1,0} = V10 n I` is its `i`-eigenspace in `V_ℂ`.

## Proofs

The proofs use, as the paper does, Lemma 2.2.1 (`V_K = W₁ ⊕ W₂`), the proof of Lemma 2.2.4 (`η_λ`
is a similarity with multiplier `Nm(λ)`, `η` is multiplicative), Lemma 2.2.6 (the decomposition
`W_{i,ℂ} = W_i^{1,0} ⊕ W_i^{0,1}`) and [Igusa, §2] (`WeilClasses.igusa_sec2_mem`,
`WeilClasses.igusa_sec2_rho`). The step "`ϖ̃(e^{iπ/4})` must be already in `Spin(V_ℝ)`" of
Remark 2.4.3 is completed with the spinor norm and the kernel `{±1}` of `ρ` (Tau Ceti); see
`remark2_4_3_complexStructure`. `KSecant.d_pos` takes the secant `P` as a hypothesis (as stated at
the baseline it did not mention `P` and was false). Helper lemmas carry the prefix `s24a_`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (`s24a_`): coordinates, change of coefficients, conjugation, complexification -/

section S24aCoords

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- The coordinate of `v ∈ V_F` at the index of `fᵢ` in `basisV` is `v.1 (eᵢ)`. -/
theorem s24a_repr_inl (v : V F n) (i : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inl i)) = v.1 (e F n i) := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inl, Module.Basis.dualBasis_repr, Pi.basisFun_apply]
  rfl

omit [CharZero F] in
/-- The coordinate of `v ∈ V_F` at the index of `eᵢ` in `basisV` is `v.2 i`. -/
theorem s24a_repr_inr (v : V F n) (i : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inr i)) = v.2 i := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inr, Pi.basisFun_repr]

variable (F' : Type*) [Field F'] [CharZero F'] [Algebra F F']

/-- `bcDual` keeps the coordinates of a functional. -/
theorem s24a_bcDual_apply_e (θ : Module.Dual F (H1 F n)) (i : Fin (2 * n)) :
    bcDual F F' n θ (e F' n i) = algebraMap F F' (θ (e F n i)) := by
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, f, e, LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Change of coefficients is coordinatewise in the bases `basisV`. -/
theorem s24a_repr_bcV (v : V F n) (k : Fin (2 * n + 2 * n)) :
    (basisV F' n).repr (bcV F F' n v) k = algebraMap F F' ((basisV F n).repr v k) := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with i | i
  · rw [s24a_repr_inl, s24a_repr_inl]
    exact s24a_bcDual_apply_e F n F' v.1 i
  · rw [s24a_repr_inr, s24a_repr_inr]
    rfl

/-- Change of coefficients maps the basis `basisV` to `basisV`. -/
theorem s24a_bcV_basisV (k : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n k) = basisV F' n k := by
  refine (basisV F' n).ext_elem fun j => ?_
  rw [s24a_repr_bcV, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- `F'`-linear maps out of `V_{F'}` are determined by their values on `V_F`. -/
theorem s24a_linearMap_ext_bcV {W : Type*} [AddCommGroup W] [Module F' W]
    {A B : V F' n →ₗ[F'] W} (h : ∀ x, A (bcV F F' n x) = B (bcV F F' n x)) : A = B :=
  (basisV F' n).ext fun k => by rw [← s24a_bcV_basisV F n F' k]; exact h _

/-- `F'`-bilinear forms on `V_{F'}` are determined by their values on `V_F`. -/
theorem s24a_bilin_ext_bcV {B₁ B₂ : LinearMap.BilinForm F' (V F' n)}
    (h : ∀ x y, B₁ (bcV F F' n x) (bcV F F' n y) = B₂ (bcV F F' n x) (bcV F F' n y)) :
    B₁ = B₂ :=
  LinearMap.BilinForm.ext_basis (basisV F' n) fun i j => by
    rw [← s24a_bcV_basisV F n F' i, ← s24a_bcV_basisV F n F' j]; exact h _ _

/-- Change of coefficients along a tower `F ⊆ F' ⊆ F''`. -/
theorem s24a_bcV_bcV (F'' : Type*) [Field F''] [CharZero F''] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (v : V F n) :
    bcV F' F'' n (bcV F F' n v) = bcV F F'' n v := by
  refine (basisV F'' n).ext_elem fun k => ?_
  rw [s24a_repr_bcV, s24a_repr_bcV, s24a_repr_bcV, ← IsScalarTower.algebraMap_apply]

/-- Change of coefficients is injective. -/
theorem s24a_bcV_injective : Function.Injective (bcV F F' n) := by
  intro v w h
  refine (basisV F n).ext_elem fun k => ?_
  have := congrArg (fun x => (basisV F' n).repr x k) h
  simp only [s24a_repr_bcV] at this
  exact (algebraMap F F').injective this

omit [CharZero F] in
/-- The pairing (1.2.2) in coordinates: `((θ, w), (θ', w'))_V = θ(w') + θ'(w)`. -/
theorem s24a_pairing_apply (x y : V F n) : pairing F n x y = x.1 y.2 + y.1 x.2 := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd]

omit [CharZero F] in
/-- The pairing (1.2.2) is symmetric. -/
theorem s24a_pairing_comm (x y : V F n) : pairing F n x y = pairing F n y x :=
  QuadraticMap.polar_comm _ _ _

/-- Change of coefficients preserves the pairing. -/
theorem s24a_pairing_bcV (x y : V F n) :
    pairing F' n (bcV F F' n x) (bcV F F' n y) = algebraMap F F' (pairing F n x y) := by
  rw [pairing, pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add, Q_bcV, Q_bcV, Q_bcV, map_sub, map_sub]

omit [CharZero F] in
/-- If `Q` vanishes on a subspace, so does the pairing. -/
theorem s24a_pairing_eq_zero_of_Q {W : Submodule F (V F n)} (hW : ∀ v ∈ W, Q F n v = 0)
    {a b : V F n} (ha : a ∈ W) (hb : b ∈ W) : pairing F n a b = 0 := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hW _ (W.add_mem ha hb),
    hW _ ha, hW _ hb, sub_zero, sub_zero]

omit [CharZero F] in
/-- The pairing (1.2.2) on `V_F` is nondegenerate. -/
theorem s24a_pairing_nondeg (x : V F n) (h : ∀ y, pairing F n x y = 0) : x = 0 := by
  obtain ⟨θ, w⟩ := x
  have h1 : ∀ i, θ (e F n i) = 0 := fun i => by
    have := h (0, e F n i)
    rwa [s24a_pairing_apply, LinearMap.zero_apply, add_zero] at this
  have h2 : ∀ i, w i = 0 := fun i => by
    have := h (f F n i, 0)
    rwa [s24a_pairing_apply, map_zero, zero_add] at this
  refine Prod.ext ?_ (funext h2)
  refine (Pi.basisFun F (Fin (2 * n))).ext fun i => ?_
  rw [Pi.basisFun_apply]
  exact h1 i

end S24aCoords

section S24aConj

variable {F : Type*} [Field F] [CharZero F] (c : F ≃+* F) (n : ℕ)

/-- The conjugation `conjV c` acts on the coordinates in `basisV`. -/
theorem s24a_repr_conjV (v : V F n) (k : Fin (2 * n + 2 * n)) :
    (basisV F n).repr (conjV c n v) k = c ((basisV F n).repr v k) := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with i | i
  · rw [s24a_repr_inl, s24a_repr_inl]
    simp only [conjV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.sum_apply,
      LinearMap.smul_apply, f, e, LinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · rw [s24a_repr_inr, s24a_repr_inr]
    rfl

/-- `conjV c` is `c`-semilinear. -/
theorem s24a_conjV_smul (a : F) (v : V F n) : conjV c n (a • v) = c a • conjV c n v := by
  refine (basisV F n).ext_elem fun k => ?_
  simp [s24a_repr_conjV]

/-- `conjV c` is an involution when `c` is. -/
theorem s24a_conjV_conjV (hc : ∀ a, c (c a) = a) (v : V F n) : conjV c n (conjV c n v) = v := by
  refine (basisV F n).ext_elem fun k => ?_
  simp [s24a_repr_conjV, hc]

end S24aConj

section S24aComplexify

variable (n : ℕ)

/-- The coordinates of `complexifyV n A z` are the matrix of `A` applied to those of `z`. -/
theorem s24a_repr_complexifyV (A : Module.End ℝ (V ℝ n)) (z : V ℂ n) :
    ⇑((basisV ℂ n).repr (complexifyV n A z)) =
      ((LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n) A).map (algebraMap ℝ ℂ)).mulVec
        ⇑((basisV ℂ n).repr z) := by
  rw [complexifyV, ← LinearMap.toMatrix_mulVec_repr (basisV ℂ n) (basisV ℂ n),
    LinearMap.toMatrix_toLin]

/-- `complexifyV n A` extends `A`. -/
theorem s24a_complexifyV_bcV (A : Module.End ℝ (V ℝ n)) (x : V ℝ n) :
    complexifyV n A (bcV ℝ ℂ n x) = bcV ℝ ℂ n (A x) := by
  refine (basisV ℂ n).ext_elem fun k => ?_
  have h1 := congrFun (s24a_repr_complexifyV n A (bcV ℝ ℂ n x)) k
  rw [h1, s24a_repr_bcV, ← LinearMap.toMatrix_mulVec_repr (basisV ℝ n) (basisV ℝ n) A x,
    RingHom.map_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, s24a_repr_bcV]

/-- Complexification is multiplicative. -/
theorem s24a_complexifyV_mul (A B : Module.End ℝ (V ℝ n)) :
    complexifyV n (A * B) = complexifyV n A * complexifyV n B :=
  s24a_linearMap_ext_bcV ℝ n ℂ fun x => by
    simp only [Module.End.mul_apply, s24a_complexifyV_bcV]

theorem s24a_complexifyV_neg_one : complexifyV n (-1) = -1 :=
  s24a_linearMap_ext_bcV ℝ n ℂ fun x => by
    simp only [s24a_complexifyV_bcV, LinearMap.neg_apply, Module.End.one_apply, map_neg]

/-- Complex conjugation commutes with the complexification of a real endomorphism. -/
theorem s24a_conjV_complexifyV (A : Module.End ℝ (V ℝ n)) (z : V ℂ n) :
    conjV (starRingAut : ℂ ≃+* ℂ) n (complexifyV n A z) =
      complexifyV n A (conjV (starRingAut : ℂ ≃+* ℂ) n z) := by
  refine (basisV ℂ n).ext_elem fun k => ?_
  rw [s24a_repr_conjV, congrFun (s24a_repr_complexifyV n A _) k,
    congrFun (s24a_repr_complexifyV n A _) k]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, s24a_repr_conjV]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp [Complex.conj_ofReal]

/-- Complex conjugation fixes the real vectors. -/
theorem s24a_conjV_bcV_real (x : V ℝ n) :
    conjV (starRingAut : ℂ ≃+* ℂ) n (bcV ℝ ℂ n x) = bcV ℝ ℂ n x := by
  refine (basisV ℂ n).ext_elem fun k => ?_
  rw [s24a_repr_conjV, s24a_repr_bcV]
  simp [Complex.conj_ofReal]

/-- `I_ℂ² = -1` for a complex structure `I`. -/
theorem s24a_complexifyV_sq {I : Module.End ℝ (V ℝ n)} (hI : IsComplexStructure I) :
    complexifyV n I * complexifyV n I = -1 := by
  rw [← s24a_complexifyV_mul, hI, s24a_complexifyV_neg_one]

/-- `V^{1,0} ∩ V^{0,1} = 0` (eigenspaces for the distinct eigenvalues `i`, `-i`). -/
theorem s24a_V10_inf_V01 (I : Module.End ℝ (V ℝ n)) : V10 n I ⊓ V01 n I = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hz
  rw [V10, Module.End.mem_eigenspace_iff] at h1
  rw [V01, Module.End.mem_eigenspace_iff] at h2
  have h3 : (Complex.I - -Complex.I) • z = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  have h4 : Complex.I - -Complex.I ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]
    exact mul_ne_zero two_ne_zero Complex.I_ne_zero
  exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp h3).resolve_left h4)

/-- Complex conjugation maps `V^{1,0}` to `V^{0,1}`. -/
theorem s24a_conjV_mem_V01 (I : Module.End ℝ (V ℝ n)) {z : V ℂ n} (hz : z ∈ V10 n I) :
    conjV (starRingAut : ℂ ≃+* ℂ) n z ∈ V01 n I := by
  rw [V10, Module.End.mem_eigenspace_iff] at hz
  rw [V01, Module.End.mem_eigenspace_iff, ← s24a_conjV_complexifyV, hz, s24a_conjV_smul]
  simp

/-- Complex conjugation maps `V^{0,1}` to `V^{1,0}`. -/
theorem s24a_conjV_mem_V10 (I : Module.End ℝ (V ℝ n)) {z : V ℂ n} (hz : z ∈ V01 n I) :
    conjV (starRingAut : ℂ ≃+* ℂ) n z ∈ V10 n I := by
  rw [V01, Module.End.mem_eigenspace_iff] at hz
  rw [V10, Module.End.mem_eigenspace_iff, ← s24a_conjV_complexifyV, hz, s24a_conjV_smul]
  simp

/-- An isometry `I` of `V_ℝ` stays an isometry on `V_ℂ`. -/
theorem s24a_pairing_complexifyV {I : Module.End ℝ (V ℝ n)}
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (a b : V ℂ n) :
    pairing ℂ n (complexifyV n I a) (complexifyV n I b) = pairing ℂ n a b := by
  have h := s24a_bilin_ext_bcV ℝ n ℂ
    (B₁ := (pairing ℂ n).compl₁₂ (complexifyV n I) (complexifyV n I)) (B₂ := pairing ℂ n)
    (fun x y => by
      simp only [LinearMap.compl₁₂_apply, s24a_complexifyV_bcV, s24a_pairing_bcV, hIso])
  exact congrArg (fun B : LinearMap.BilinForm ℂ (V ℂ n) => B a b) h

/-- For an orthogonal complex structure `I`, `V^{1,0}` is isotropic: `(a, b) = (Ia, Ib) = -(a, b)`
(§2.4). -/
theorem s24a_V10_isotropic_of {I : Module.End ℝ (V ℝ n)}
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    ∀ a ∈ V10 n I, ∀ b ∈ V10 n I, pairing ℂ n a b = 0 := by
  intro a ha b hb
  rw [V10, Module.End.mem_eigenspace_iff] at ha hb
  have h := s24a_pairing_complexifyV n hIso a b
  rw [ha, hb] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  linear_combination (-1 / 2 : ℂ) * h + (pairing ℂ n a b / 2) * Complex.I_mul_I

/-- For an orthogonal complex structure `I`, `V^{0,1}` is isotropic (§2.4). -/
theorem s24a_V01_isotropic_of {I : Module.End ℝ (V ℝ n)}
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    ∀ a ∈ V01 n I, ∀ b ∈ V01 n I, pairing ℂ n a b = 0 := by
  intro a ha b hb
  rw [V01, Module.End.mem_eigenspace_iff] at ha hb
  have h := s24a_pairing_complexifyV n hIso a b
  rw [ha, hb] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  linear_combination (-1 / 2 : ℂ) * h + (pairing ℂ n a b / 2) * Complex.I_mul_I

end S24aComplexify

/-! ## Extension of scalars of rational endomorphisms of `V` -/

section BcEnd

variable (F' : Type*) [Field F'] [CharZero F'] (n : ℕ)

/-- The `F'`-linear extension to `V_{F'}` of a rational endomorphism `A` of `V_ℚ` (for
`F' = K, ℝ, ℂ`): the endomorphism with the same matrix in the bases `basisV`. -/
noncomputable def bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) : V F' n →ₗ[F'] V F' n :=
  Matrix.toLin (basisV F' n) (basisV F' n)
    ((LinearMap.toMatrix (basisV ℚ n) (basisV ℚ n) A).map (algebraMap ℚ F'))

/-- The coordinates of `bcEndV F' n A v` are the matrix of `A` applied to those of `v`. -/
theorem s24a_repr_bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V F' n) :
    ⇑((basisV F' n).repr (bcEndV F' n A v)) =
      ((LinearMap.toMatrix (basisV ℚ n) (basisV ℚ n) A).map (algebraMap ℚ F')).mulVec
        ⇑((basisV F' n).repr v) := by
  rw [bcEndV, ← LinearMap.toMatrix_mulVec_repr (basisV F' n) (basisV F' n),
    LinearMap.toMatrix_toLin]

/-- `bcEndV` commutes with change of coefficients along a tower `ℚ ⊆ F ⊆ F'`. -/
theorem s24a_bcEndV_bcV_tower (F : Type*) [Field F] [CharZero F] [Algebra F F']
    [IsScalarTower ℚ F F'] (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V F n) :
    bcEndV F' n A (bcV F F' n v) = bcV F F' n (bcEndV F n A v) := by
  refine (basisV F' n).ext_elem fun k => ?_
  have h1 := congrFun (s24a_repr_bcEndV F' n A (bcV F F' n v)) k
  have h2 := congrFun (s24a_repr_bcEndV F n A v) k
  rw [h1, s24a_repr_bcV, h2, RingHom.map_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, s24a_repr_bcV,
    ← IsScalarTower.algebraMap_apply]

/-- `bcEndV ℚ n A = A`. -/
theorem s24a_bcEndV_rat (A : V ℚ n →ₗ[ℚ] V ℚ n) : bcEndV ℚ n A = A := by
  have h : (LinearMap.toMatrix (basisV ℚ n) (basisV ℚ n) A).map (algebraMap ℚ ℚ) =
      LinearMap.toMatrix (basisV ℚ n) (basisV ℚ n) A := by
    ext i j
    simp
  rw [bcEndV, h, Matrix.toLin_toMatrix]

/-- `bcEndV F' n A` extends `A`. -/
theorem bcEndV_bcV (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V ℚ n) :
    bcEndV F' n A (bcV ℚ F' n v) = bcV ℚ F' n (A v) := by
  rw [s24a_bcEndV_bcV_tower F' n ℚ A v, s24a_bcEndV_rat]

/-- The complexification of the real extension is the complex extension. -/
theorem complexifyV_bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) :
    complexifyV n (bcEndV ℝ n A) = bcEndV ℂ n A := by
  refine s24a_linearMap_ext_bcV ℝ n ℂ fun x => ?_
  rw [s24a_complexifyV_bcV, s24a_bcEndV_bcV_tower ℂ n ℝ A x]

end BcEnd

/-! ## The field `K`: the coefficient of `√-d` -/

/-! ## Assumption 2.4.1 -/

variable {n : ℕ} {d : ℚ}

/-- **Assumption 2.4.1** (`assumption-on-rational-secant-plane-P`). The rational plane `P` is
non-isotropic with respect to the Mukai pairing (1.2.3) and is contained in the Hodge ring of `X`.
`ℙ(P)` intersects the spinor variety in two complex conjugate points defined over
`K := ℚ[√-d]`, where `d` is a positive rational number.

Representation: `X` is given by the complex structure `J` of `H¹(X, ℝ)` (with `H^{1,0}(X)` its
`i`-eigenspace), and `P` is the rational plane `P.Pℚ` of a rational `K`-secant `P : KSecant n d`,
which records the two conjugate even pure spinor lines `ℓ̃₁ = K u₁`, `ℓ̃₂ = K σ(u₁)` where `ℙ(P)`
meets the spinor variety (the choice of `u₁` is the orientation of `P`). -/
structure Assumption2_4_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) : Prop where
  /-- `J` is a complex structure of `H¹(X, ℝ)` (the complex structure of `X`). -/
  isComplex : IsComplexStructure J
  /-- `P` is non-isotropic for the Mukai pairing (1.2.3). -/
  nonIsotropic : ¬ P.IsIsotropic
  /-- `P` is contained in the Hodge ring `⊕_p H^{p,p}(X, ℚ)` of `X`. -/
  hodge : P.Pℚ ≤ hodgeRingX n J
  /-- `d` is a positive rational number. -/
  pos : 0 < d

/-- Under Assumption 2.4.1, `V_K = W₁ ⊕ W₂`: `W₁ ∩ W₂ = 0` by Lemma 2.2.1 (`P` is non-isotropic;
§2.2, line 846 of the TeX: "The vanishing `W₁ ∩ W₂ = (0)` holds, by Lemma 2.2.1"), and
`dim W₁ + dim W₂ = 4n = dim V_K`. This is what the definition (2.2.4) of `η`, hence of `f`, needs. -/
theorem Assumption2_4_1.isCompl {P : KSecant n d} {J : Module.End ℝ (H1 ℝ n)}
    (hP : Assumption2_4_1 P J) : IsCompl P.W₁ P.W₂ := by
  -- Lemma 2.2.1: `P` is non-isotropic, so `W₁ ∩ W₂ = 0`; then `dim W₁ + dim W₂ = dim V_K`.
  have h : P.W₁ ⊓ P.W₂ = ⊥ := by
    by_contra h
    exact hP.nonIsotropic ((lemma2_2_1 P hP.pos).mpr h)
  exact P.isCompl_of_inf_eq_bot h

/-! ### Helpers (`s24a_`): the field `K` -/

section S24aK

/-- `Nm(√-d) = d`. -/
theorem s24a_Nm_sqrtNeg (hd : 0 < d) : Kd.Nm d (Kd.sqrtNeg d) = d := by
  apply Rat.cast_injective (α := ℂ)
  rw [Kd.coe_Nm hd]
  show WeilClasses.sqrtNeg d * (starRingEnd ℂ) (WeilClasses.sqrtNeg d) = (d : ℂ)
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hd.le)]
    simp
  simp only [WeilClasses.sqrtNeg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  linear_combination h - ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq

/-- `√-d ≠ 0` for `d > 0`. -/
theorem s24a_sqrtNeg_ne_zero (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have h' : WeilClasses.sqrtNeg d = 0 := congrArg Subtype.val h
  rw [WeilClasses.sqrtNeg, mul_eq_zero, Complex.ofReal_eq_zero, Real.sqrt_eq_zero'] at h'
  rcases h' with h' | h'
  · exact Complex.I_ne_zero h'
  · exact absurd h' (not_le.mpr (by exact_mod_cast hd))

/-- `σ(√-d) = -√-d`. -/
theorem s24a_σ_sqrtNeg : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  show (starRingEnd ℂ) (WeilClasses.sqrtNeg d) = -WeilClasses.sqrtNeg d
  simp [WeilClasses.sqrtNeg]

/-- `√-d · √-d = -d` in `K`. -/
theorem s24a_sqrtNeg_mul_self (hd : 0 < d) :
    Kd.sqrtNeg d * Kd.sqrtNeg d = algebraMap ℚ (Kd d) (-d) := by
  apply Subtype.ext
  show WeilClasses.sqrtNeg d * WeilClasses.sqrtNeg d = ((algebraMap ℚ (Kd d) (-d) : Kd d) : ℂ)
  rw [← sq, sqrtNeg_sq hd.le]
  simp

end S24aK

namespace KSecant

variable (P : KSecant n d)

include P in
/-- A rational `K`-secant exists only when `d > 0`: for `d ≤ 0` the chosen square root `√-d` is
`0`, `Kd d = ℚ`, `σ` is the identity and `u₂ = u₁`.

Correction of the statement (helper lemma): as stated at the baseline, the section variable `P`
was not included (it does not occur in `0 < d`), so the statement read `∀ {d : ℚ}, 0 < d`, which is
false for `d = 0`; the secant `P` is now an explicit hypothesis (`include P`). -/
theorem d_pos : 0 < d := by
  by_contra hd
  push Not at hd
  have hs : WeilClasses.sqrtNeg d = 0 := by
    have h0 : Real.sqrt (d : ℝ) = 0 := Real.sqrt_eq_zero'.mpr (by exact_mod_cast hd)
    simp [WeilClasses.sqrtNeg, h0]
  have hσ : ∀ z : Kd d, Kd.σ d z = z := fun z => by
    obtain ⟨a, b, hz⟩ := (Kd.mem_iff d).mp z.2
    apply Subtype.ext
    rw [Kd.coe_σ, hz, hs]
    simp
  have hu : σS n d P.u₁ = P.u₁ := by
    show conjS (Kd.σ d) n P.u₁ = P.u₁
    simp only [conjS, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hσ]
    exact (basisS (Kd d) n).sum_repr P.u₁
  have h01 := P.linIndep.injective (a₁ := 0) (a₂ := 1) (by simp [hu])
  exact absurd h01 (by decide)

/-- `η` sends a rational number `q` to `q · id` (`η : K → End(V_ℚ)` is a ring homomorphism, (2.2.4)
and Lemma 2.2.4's file). -/
theorem s24a_η_algebraMap (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (q : ℚ) :
    P.η hW (algebraMap ℚ (Kd d) q) = q • LinearMap.id := by
  have h := RingHom.ext_rat ((P.ηHom hd hW).comp (algebraMap ℚ (Kd d)))
    (algebraMap ℚ (Module.End ℚ (V ℚ n)))
  have hq := congrArg (fun φ : ℚ →+* Module.End ℚ (V ℚ n) => φ q) h
  simpa [ηHom, Module.algebraMap_end_eq_smul_id] using hq

/-- `f² = -d` pointwise (by Lemma 2.2.4's file: `η` is multiplicative). -/
theorem s24a_fη_fη_apply (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    P.fη hW (P.fη hW x) = -(d • x) := by
  have hd := P.d_pos
  have h := P.η_mul hd hW (Kd.sqrtNeg d) (Kd.sqrtNeg d)
  rw [s24a_sqrtNeg_mul_self hd, s24a_η_algebraMap P hd hW] at h
  have hx := congrArg (fun φ : Module.End ℚ (V ℚ n) => φ x) h
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Module.End.mul_apply] at hx
  rw [fη, ← hx, neg_smul]

/-- `(f x, f y)_V = d (x, y)_V` (by the proof of Lemma 2.2.4: `η_λ` is a similarity with multiplier
`Nm(λ)`, and `Nm(√-d) = d`). -/
theorem s24a_pairing_fη (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) (P.fη hW y) = d * pairing ℚ n x y := by
  have hd := P.d_pos
  rw [fη, P.pairing_η hd hW, s24a_Nm_sqrtNeg hd]

/-! ## The similarity `f` (2.4.1) -/

/-- `f = η_{√-d}` (2.4.1) belongs to the similarity group `Õ(V_ℚ)` of (2.2.3) (§2.4, after
(2.4.1), "by Lemma 2.2.4"). -/
theorem fη_mem_Otilde (hW : IsCompl P.W₁ P.W₂) :
    ∃ g : V ℚ n ≃ₗ[ℚ] V ℚ n, g ∈ Otilde n d ∧ (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.fη hW := by
  -- `f` is invertible (`f² = -d`) and a similarity with multiplier `d = Nm(√-d)`.
  have hd := P.d_pos
  have hd0 : d ≠ 0 := hd.ne'
  refine ⟨LinearEquiv.ofLinearMap (P.fη hW) ((-d⁻¹) • P.fη hW) ?_ ?_,
    ⟨d, ⟨Kd.sqrtNeg d, s24a_sqrtNeg_ne_zero hd, s24a_Nm_sqrtNeg hd⟩,
      fun x y => s24a_pairing_fη P hW x y⟩, rfl⟩
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, s24a_fη_fη_apply,
      LinearMap.id_apply, smul_neg, smul_smul]
    rw [neg_mul, inv_mul_cancel₀ hd0, neg_smul, one_smul, neg_neg]
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, s24a_fη_fη_apply,
      LinearMap.id_apply, smul_neg, smul_smul]
    rw [neg_mul, inv_mul_cancel₀ hd0, neg_smul, one_smul, neg_neg]

/-- `(f x, f y)_V = d (x, y)_V` (§2.4, after (2.4.1), "by Lemma 2.2.4"). -/
theorem pairing_fη_fη (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) (P.fη hW y) = d * pairing ℚ n x y := by
  exact s24a_pairing_fη P hW x y

/-- `f² = -d` (§2.4, after (2.4.1), "by Lemma 2.2.4"). -/
theorem fη_comp_fη (hW : IsCompl P.W₁ P.W₂) : P.fη hW ∘ₗ P.fη hW = -(d • LinearMap.id) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, s24a_fη_fη_apply]
  rfl

/-- `f` is anti-self-dual: `(f x, y)_V = -(x, f y)_V` (§2.4, after (2.4.1)). -/
theorem pairing_fη_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) y = -pairing ℚ n x (P.fη hW y) := by
  -- `(f x, y)_V = (1/d) (f² x, f y)_V = -(x, f y)_V`.
  have hd0 : d ≠ 0 := P.d_pos.ne'
  have h := s24a_pairing_fη P hW (P.fη hW x) y
  rw [s24a_fη_fη_apply, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  have h' : d * (pairing ℚ n (P.fη hW x) y + pairing ℚ n x (P.fη hW y)) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd h1 hd0
  · linear_combination h1

/-- The real extension `f_ℝ` of `f` to `V_ℝ`. -/
noncomputable def fR (hW : IsCompl P.W₁ P.W₂) : Module.End ℝ (V ℝ n) := bcEndV ℝ n (P.fη hW)

/-! ## The `2`-form `Ξ_P` (2.4.2) -/

/-- **The `2`-form `Ξ_P`** (2.4.2): `Ξ_P(x, y) = (f x, y)_V` on `V_ℚ`. -/
noncomputable def XiQ (hW : IsCompl P.W₁ P.W₂) : LinearMap.BilinForm ℚ (V ℚ n) :=
  (pairing ℚ n).compLeft (P.fη hW)

/-- `Ξ_P` on `V_ℝ`: `Ξ_P(x, y) = (f x, y)_V` (§2.4 and §3.2). -/
noncomputable def XiR (hW : IsCompl P.W₁ P.W₂) : LinearMap.BilinForm ℝ (V ℝ n) :=
  (pairing ℝ n).compLeft (P.fR hW)

/-- `XiR` extends `XiQ`. -/
theorem XiR_bcV (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.XiR hW (bcV ℚ ℝ n x) (bcV ℚ ℝ n y) = (P.XiQ hW x y : ℝ) := by
  simp only [XiR, XiQ, LinearMap.BilinForm.compLeft_apply, fR, bcEndV_bcV, s24a_pairing_bcV]
  simp

/-- `Ξ_P` is a `2`-form, `Ξ_P ∈ ⋀² V_ℚ*` (§2.4, (2.4.2)): it is alternating. -/
theorem XiQ_isAlt (hW : IsCompl P.W₁ P.W₂) : (P.XiQ hW).IsAlt := by
  -- `f` is anti-self-dual and the pairing is symmetric.
  intro x
  have h := P.pairing_fη_left hW x x
  rw [s24a_pairing_comm ℚ n x] at h
  simp only [XiQ, LinearMap.BilinForm.compLeft_apply]
  linarith

/-- `Ξ_P` is non-degenerate, since `f` is invertible and the pairing on `V` is non-degenerate
(§2.4, after (2.4.2)). -/
theorem XiQ_nondegenerate (hW : IsCompl P.W₁ P.W₂) : (P.XiQ hW).Nondegenerate := by
  have hd0 : d ≠ 0 := P.d_pos.ne'
  -- `f` is invertible: `f² = -d`.
  have hf : ∀ x, P.fη hW x = 0 → x = 0 := fun x hx => by
    have h := s24a_fη_fη_apply P hW x
    rw [hx, map_zero, eq_comm, neg_eq_zero, smul_eq_zero] at h
    exact h.resolve_left hd0
  refine ⟨fun x hx => hf x (s24a_pairing_nondeg ℚ n _ fun y => hx y),
    fun y hy => hf y (s24a_pairing_nondeg ℚ n _ fun x => ?_)⟩
  have h := hy x
  rw [XiQ, LinearMap.BilinForm.compLeft_apply, P.pairing_fη_left, neg_eq_zero] at h
  rw [s24a_pairing_comm, h]

/-- `η_λ` acts on `W₁` by `λ` ((2.2.4)). -/
theorem s24a_ηK_of_mem_W₁ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {x : V (Kd d) n}
    (hx : x ∈ P.W₁) : P.ηK hW l x = l • x := by
  have h1 : P.W₁.projectionOnto P.W₂ hW x = ⟨x, hx⟩ :=
    Submodule.projectionOnto_apply_left hW ⟨x, hx⟩
  have h2 : P.W₂.projectionOnto P.W₁ hW.symm x = 0 :=
    Submodule.projectionOnto_apply_right hW.symm ⟨x, hx⟩
  simp [ηK, h1, h2]

/-- `η_λ` acts on `W₂` by `σ(λ)` ((2.2.4)). -/
theorem s24a_ηK_of_mem_W₂ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {x : V (Kd d) n}
    (hx : x ∈ P.W₂) : P.ηK hW l x = Kd.σ d l • x := by
  have h1 : P.W₁.projectionOnto P.W₂ hW x = 0 :=
    Submodule.projectionOnto_apply_right hW ⟨x, hx⟩
  have h2 : P.W₂.projectionOnto P.W₁ hW.symm x = ⟨x, hx⟩ :=
    Submodule.projectionOnto_apply_left hW.symm ⟨x, hx⟩
  simp [ηK, h1, h2]

/-- `W₁` is isotropic (it is maximal isotropic, `u₁` being pure). -/
theorem s24a_W₁_isotropic {a b : V (Kd d) n} (ha : a ∈ P.W₁) (hb : b ∈ P.W₁) :
    pairing (Kd d) n a b = 0 :=
  s24a_pairing_eq_zero_of_Q (Kd d) n P.isPure.2.1 ha hb

/-- `W₂` is isotropic (`u₂` is pure, by Lemma 2.2.1's file). -/
theorem s24a_W₂_isotropic {a b : V (Kd d) n} (ha : a ∈ P.W₂) (hb : b ∈ P.W₂) :
    pairing (Kd d) n a b = 0 :=
  s24a_pairing_eq_zero_of_Q (Kd d) n P.isPure₂.2.1 ha hb

/-- `Ξ_P(x, y) = √-d ((x₁, y₂)_V - (x₂, y₁)_V)`, where `x = x₁ + x₂` and `y = y₁ + y₂` with
`xᵢ, yᵢ ∈ Wᵢ` (decompositions in `V_K`) (§2.4, after (2.4.2)). -/
theorem XiQ_eq (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) (x₁ x₂ y₁ y₂ : V (Kd d) n)
    (hx₁ : x₁ ∈ P.W₁) (hx₂ : x₂ ∈ P.W₂) (hy₁ : y₁ ∈ P.W₁) (hy₂ : y₂ ∈ P.W₂)
    (hx : bcV ℚ (Kd d) n x = x₁ + x₂) (hy : bcV ℚ (Kd d) n y = y₁ + y₂) :
    algebraMap ℚ (Kd d) (P.XiQ hW x y) =
      Kd.sqrtNeg d * (pairing (Kd d) n x₁ y₂ - pairing (Kd d) n x₂ y₁) := by
  -- In `V_K`, `f = η_{√-d}` is `√-d` on `W₁` and `σ(√-d) = -√-d` on `W₂`; `W₁`, `W₂` are isotropic.
  have hd := P.d_pos
  rw [XiQ, LinearMap.BilinForm.compLeft_apply, ← s24a_pairing_bcV, fη, ← P.ηK_bcV hd hW, hx, hy,
    map_add (P.ηK hW (Kd.sqrtNeg d)) x₁ x₂, s24a_ηK_of_mem_W₁ P hW _ hx₁,
    s24a_ηK_of_mem_W₂ P hW _ hx₂, s24a_σ_sqrtNeg]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, neg_smul,
    map_neg, LinearMap.neg_apply]
  rw [s24a_W₁_isotropic P hx₁ hy₁, s24a_W₂_isotropic P hx₂ hy₂]
  ring

/-! ## The subspaces `W_{i,ℂ}` and the decomposition into four summands -/

/-- Complex conjugation on `V_K ⊆ V_ℂ` is `σ`. -/
theorem s24a_conjV_bcV_K (w : V (Kd d) n) :
    conjV (starRingAut : ℂ ≃+* ℂ) n (bcV (Kd d) ℂ n w) = bcV (Kd d) ℂ n (σV n d w) := by
  refine (basisV ℂ n).ext_elem fun k => ?_
  rw [s24a_repr_conjV, s24a_repr_bcV, s24a_repr_bcV, σV, s24a_repr_conjV]
  rfl

/-- `σ` is an involution of `V_K`. -/
theorem s24a_σV_σV (w : V (Kd d) n) : σV n d (σV n d w) = w :=
  s24a_conjV_conjV (Kd.σ d) n (fun z => Subtype.ext (by simp)) w

/-- Complex conjugation maps `W_{1,ℂ}` into `W_{2,ℂ}` (`W₂ = σ(W₁)`, Lemma 2.2.1's file). -/
theorem s24a_conjV_mem_W₂ℂ {z : V ℂ n} (hz : z ∈ P.W₁ℂ) :
    conjV (starRingAut : ℂ ≃+* ℂ) n z ∈ P.W₂ℂ := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [s24a_conjV_bcV_K]
      exact Submodule.subset_span ⟨_, (P.σV_mem_W₂_iff w).mpr hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [s24a_conjV_smul]; exact Submodule.smul_mem _ _ hx

/-- Complex conjugation maps `W_{2,ℂ}` into `W_{1,ℂ}`. -/
theorem s24a_conjV_mem_W₁ℂ {z : V ℂ n} (hz : z ∈ P.W₂ℂ) :
    conjV (starRingAut : ℂ ≃+* ℂ) n z ∈ P.W₁ℂ := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [s24a_conjV_bcV_K]
      refine Submodule.subset_span ⟨_, (P.σV_mem_W₂_iff (σV n d w)).mp ?_, rfl⟩
      rwa [s24a_σV_σV]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [s24a_conjV_smul]; exact Submodule.smul_mem _ _ hx

/-- `V_ℂ = W_{1,ℂ} + W_{2,ℂ}` (from `V_K = W₁ ⊕ W₂`). -/
theorem s24a_W₁ℂ_sup_W₂ℂ (hW : IsCompl P.W₁ P.W₂) : P.W₁ℂ ⊔ P.W₂ℂ = ⊤ := by
  rw [eq_top_iff, ← (basisV ℂ n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [← s24a_bcV_basisV (Kd d) n ℂ k]
  have hk : basisV (Kd d) n k ∈ P.W₁ ⊔ P.W₂ := by rw [hW.sup_eq_top]; trivial
  obtain ⟨w₁, hw₁, w₂, hw₂, hsum⟩ := Submodule.mem_sup.mp hk
  rw [← hsum, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨w₁, hw₁, rfl⟩)
    (Submodule.subset_span ⟨w₂, hw₂, rfl⟩)

/-- `dim_ℂ W_ℂ ≤ dim_K W`. -/
theorem s24a_finrank_span_bcV_le (W : Submodule (Kd d) (V (Kd d) n)) :
    Module.finrank ℂ (Submodule.span ℂ (bcV (Kd d) ℂ n '' W)) ≤ Module.finrank (Kd d) W := by
  let b := Module.finBasis (Kd d) W
  have hle : Submodule.span ℂ (bcV (Kd d) ℂ n '' W) ≤
      Submodule.span ℂ (Set.range fun i => bcV (Kd d) ℂ n (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : V (Kd d) n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩).symm
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
    rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank ℂ (Submodule.span ℂ (bcV (Kd d) ℂ n '' W))
      ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => bcV (Kd d) ℂ n (b i))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank (Kd d) W)) := finrank_range_le_card _
    _ = Module.finrank (Kd d) W := Fintype.card_fin _

/-- `W_{1,ℂ} ∩ W_{2,ℂ} = 0` (dimension count). -/
theorem s24a_W₁ℂ_inf_W₂ℂ (hW : IsCompl P.W₁ P.W₂) : P.W₁ℂ ⊓ P.W₂ℂ = ⊥ := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P.W₁ℂ P.W₂ℂ
  rw [s24a_W₁ℂ_sup_W₂ℂ P hW, finrank_top] at h1
  have hV : Module.finrank ℂ (V ℂ n) = 2 * n + 2 * n := by
    rw [Module.finrank_eq_card_basis (basisV ℂ n), Fintype.card_fin]
  have h2 : Module.finrank ℂ P.W₁ℂ ≤ 2 * n :=
    (s24a_finrank_span_bcV_le P.W₁).trans P.isPure.2.2.le
  have h3 : Module.finrank ℂ P.W₂ℂ ≤ 2 * n :=
    (s24a_finrank_span_bcV_le P.W₂).trans P.isPure₂.2.2.le
  have h4 : Module.finrank ℂ (P.W₁ℂ ⊓ P.W₂ℂ : Submodule ℂ (V ℂ n)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h4

/-- The four summands `W_i ∩ V^{p,q}` are independent. -/
theorem s24a_decomp_zero (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) {a b c e : V ℂ n}
    (ha : a ∈ P.W₁ℂ ⊓ V10 n I) (hb : b ∈ P.W₂ℂ ⊓ V10 n I) (hc : c ∈ P.W₁ℂ ⊓ V01 n I)
    (he : e ∈ P.W₂ℂ ⊓ V01 n I) (h : a + b + c + e = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have h' : (a + c) + (b + e) = 0 := by rw [← h]; abel
  have hac : a + c = 0 := by
    have h2 : a + c ∈ P.W₂ℂ := by
      rw [eq_neg_of_add_eq_zero_left h']
      exact neg_mem (add_mem hb.1 he.1)
    have h3 := Submodule.mem_inf.mpr ⟨add_mem ha.1 hc.1, h2⟩
    rwa [s24a_W₁ℂ_inf_W₂ℂ P hW, Submodule.mem_bot] at h3
  have hbe : b + e = 0 := by rwa [hac, zero_add] at h'
  have hV : ∀ {x y : V ℂ n}, x ∈ V10 n I → y ∈ V01 n I → x + y = 0 → x = 0 ∧ y = 0 := by
    intro x y hx hy hxy
    have h2 : x ∈ V01 n I := by
      rw [eq_neg_of_add_eq_zero_left hxy]
      exact neg_mem hy
    have h3 := Submodule.mem_inf.mpr ⟨hx, h2⟩
    rw [s24a_V10_inf_V01, Submodule.mem_bot] at h3
    refine ⟨h3, ?_⟩
    rwa [h3, zero_add] at hxy
  obtain ⟨ha0, hc0⟩ := hV ha.2 hc.2 hac
  obtain ⟨hb0, he0⟩ := hV hb.2 he.2 hbe
  exact ⟨ha0, hb0, hc0, he0⟩

/-- The decomposition `z = z₁^{1,0} + z₂^{1,0} + z₁^{0,1} + z₂^{0,1}` of any `z ∈ V_ℂ`, by
`V_ℂ = W_{1,ℂ} ⊕ W_{2,ℂ}` (Assumption 2.4.1 and Lemma 2.2.1) and Lemma 2.2.6
(`W_{i,ℂ} = (W_{i,ℂ} ∩ V^{1,0}) ⊕ (W_{i,ℂ} ∩ V^{0,1})`). -/
theorem s24a_existsUnique_decomp_C (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (z : V ℂ n) :
    ∃! p : V ℂ n × V ℂ n × V ℂ n × V ℂ n,
      p.1 ∈ P.W₁ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.1 ∈ P.W₂ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.2.1 ∈ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      p.2.2.2 ∈ P.W₂ℂ ⊓ V01 n (productStructure n J) ∧
      z = p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  have hW := hP.isCompl
  obtain ⟨hd1, hd2⟩ := lemma2_2_6_decomp P hP.pos hP.nonIsotropic J hP.isComplex hP.hodge
  have hz : z ∈ P.W₁ℂ ⊔ P.W₂ℂ := by rw [s24a_W₁ℂ_sup_W₂ℂ P hW]; trivial
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hz
  rw [hd1] at hw₁
  rw [hd2] at hw₂
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hw₁
  obtain ⟨b, hb, e, he, rfl⟩ := Submodule.mem_sup.mp hw₂
  refine ⟨(a, b, c, e), ⟨ha, hb, hc, he, by abel⟩, ?_⟩
  rintro ⟨a', b', c', e'⟩ ⟨ha', hb', hc', he', hsum⟩
  have h0 := s24a_decomp_zero P hW _ (sub_mem ha' ha) (sub_mem hb' hb) (sub_mem hc' hc)
    (sub_mem he' he) (by
      have : a' + b' + c' + e' = a + b + c + e := by rw [← hsum]; abel
      rw [← sub_eq_zero] at this
      rw [← this]; abel)
  simp only [sub_eq_zero] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  rw [h1, h2, h3, h4]

/-- The conjugation rules for a real vector `z` of `V_ℂ`: conjugation swaps `W_{1,ℂ}` and
`W_{2,ℂ}` and swaps `V^{1,0}` and `V^{0,1}`; conclude by uniqueness of the decomposition. -/
theorem s24a_conj_decomp_of_conj (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (z : V ℂ n) (hzr : conjV (starRingAut : ℂ ≃+* ℂ) n z = z)
    (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : z = a + b + c + e) :
    conjV (starRingAut : ℂ ≃+* ℂ) n a = e ∧ conjV (starRingAut : ℂ ≃+* ℂ) n c = b := by
  set cj := conjV (starRingAut : ℂ ≃+* ℂ) n
  have hz : z = cj e + cj c + cj b + cj a := by
    rw [← hzr, hv]
    simp only [map_add]
    abel
  obtain ⟨p, _, huniq⟩ := s24a_existsUnique_decomp_C P J hP z
  have h1 := huniq (a, b, c, e) ⟨ha, hb, hc, he, hv⟩
  have h2 := huniq (cj e, cj c, cj b, cj a)
    ⟨⟨s24a_conjV_mem_W₁ℂ P he.1, s24a_conjV_mem_V10 n _ he.2⟩,
      ⟨s24a_conjV_mem_W₂ℂ P hc.1, s24a_conjV_mem_V10 n _ hc.2⟩,
      ⟨s24a_conjV_mem_W₁ℂ P hb.1, s24a_conjV_mem_V01 n _ hb.2⟩,
      ⟨s24a_conjV_mem_W₂ℂ P ha.1, s24a_conjV_mem_V01 n _ ha.2⟩, hz⟩
  have h3 := h1.trans h2.symm
  simp only [Prod.mk.injEq] at h3
  exact ⟨h3.2.2.2.symm, h3.2.1.symm⟩

/-- The decomposition `v = v₁^{1,0} + v₂^{1,0} + v₁^{0,1} + v₂^{0,1}` (§2.4, after (2.4.2), "by
Lemma 2.2.6"): under Assumption 2.4.1, every `v ∈ V_ℚ` is, in a unique way, a sum of vectors
`vᵢ^{1,0} ∈ W_{i,ℂ} ∩ V^{1,0}` and `vᵢ^{0,1} ∈ W_{i,ℂ} ∩ V^{0,1}` of `V_ℂ` (`I = I_{V_ℝ}`). The
components are listed in the order `(v₁^{1,0}, v₂^{1,0}, v₁^{0,1}, v₂^{0,1})`. -/
theorem existsUnique_decomp (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℚ n) :
    ∃! p : V ℂ n × V ℂ n × V ℂ n × V ℂ n,
      p.1 ∈ P.W₁ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.1 ∈ P.W₂ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.2.1 ∈ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      p.2.2.2 ∈ P.W₂ℂ ⊓ V01 n (productStructure n J) ∧
      bcV ℚ ℂ n v = p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  exact s24a_existsUnique_decomp_C P J hP _

/-- The summands of the decomposition of `v ∈ V_ℚ` satisfy `\overline{v₁^{1,0}} = v₂^{0,1}` and
`\overline{v₁^{0,1}} = v₂^{1,0}` (§2.4, after (2.4.2)); here `a = v₁^{1,0}`, `b = v₂^{1,0}`,
`c = v₁^{0,1}`, `e = v₂^{0,1}` and the bar is complex conjugation of `V_ℂ`. -/
theorem conj_decomp (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℚ n)
    (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℚ ℂ n v = a + b + c + e) :
    conjV (starRingAut : ℂ ≃+* ℂ) n a = e ∧ conjV (starRingAut : ℂ ≃+* ℂ) n c = b := by
  refine s24a_conj_decomp_of_conj P J hP _ ?_ a b c e ha hb hc he hv
  rw [← s24a_bcV_bcV ℚ n ℝ ℂ, s24a_conjV_bcV_real]

/-- The decomposition into four summands also holds for `v ∈ V_ℝ` (used in Lemma 2.4.2 and
Proposition 2.4.4, where `g_P` is a form on `V_ℝ`). -/
theorem existsUnique_decomp_real (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (v : V ℝ n) :
    ∃! p : V ℂ n × V ℂ n × V ℂ n × V ℂ n,
      p.1 ∈ P.W₁ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.1 ∈ P.W₂ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.2.1 ∈ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      p.2.2.2 ∈ P.W₂ℂ ⊓ V01 n (productStructure n J) ∧
      bcV ℝ ℂ n v = p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  exact s24a_existsUnique_decomp_C P J hP _

/-- The conjugation rules `\overline{v₁^{1,0}} = v₂^{0,1}`, `\overline{v₁^{0,1}} = v₂^{1,0}` for
`v ∈ V_ℝ`. -/
theorem conj_decomp_real (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℝ n)
    (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℝ ℂ n v = a + b + c + e) :
    conjV (starRingAut : ℂ ≃+* ℂ) n a = e ∧ conjV (starRingAut : ℂ ≃+* ℂ) n c = b := by
  exact s24a_conj_decomp_of_conj P J hP _ (s24a_conjV_bcV_real n v) a b c e ha hb hc he hv

end KSecant

/-! ## The complex structure `I = I_{V_ℝ}` of `X × X̂` -/

section ProductStructure

variable (J : Module.End ℝ (H1 ℝ n))

/-- `J² = -1`, pointwise. -/
theorem s24a_J_J (hJ : IsComplexStructure J) (w : H1 ℝ n) : J (J w) = -w := by
  have := congrArg (fun A : Module.End ℝ (H1 ℝ n) => A w) hJ
  simpa using this

/-- `I = I_{V_ℝ}` is a complex structure: `I² = -1`. -/
theorem isComplexStructure_productStructure (hJ : IsComplexStructure J) :
    IsComplexStructure (productStructure n J) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨θ, w⟩ := x
  refine Prod.ext (LinearMap.ext fun u => ?_) ?_
  · simp [productStructure, s24a_J_J J hJ]
  · simp [productStructure, s24a_J_J J hJ]

/-- The complex structure `I = I_{V_ℝ}` of `X × X̂` is an isometry of `(·,·)_V` (§2.4 and its
footnote). -/
theorem pairing_productStructure (hJ : IsComplexStructure J) (x y : V ℝ n) :
    pairing ℝ n (productStructure n J x) (productStructure n J y) = pairing ℝ n x y := by
  -- `(θ ∘ J)(-J w') + (θ' ∘ J)(-J w) = θ(w') + θ'(w)`, as `J² = -1`.
  simp only [s24a_pairing_apply, productStructure, LinearMap.prodMap_apply,
    LinearMap.dualMap_apply, LinearMap.neg_apply, map_neg, s24a_J_J J hJ, neg_neg]

/-- `I^{-1} = -I`, hence `I` is anti-self-dual: `(I x, y)_V = -(x, I y)_V` (§2.4). -/
theorem pairing_productStructure_left (hJ : IsComplexStructure J) (x y : V ℝ n) :
    pairing ℝ n (productStructure n J x) y = -pairing ℝ n x (productStructure n J y) := by
  -- `I⁻¹ = -I`: `y = I(-I y)`, and `I` is an isometry.
  have hy : y = productStructure n J (-productStructure n J y) := by
    have := congrArg (fun A : Module.End ℝ (V ℝ n) => A y)
      (isComplexStructure_productStructure J hJ)
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] at this
    rw [map_neg, this, neg_neg]
  conv_lhs => rw [hy]
  rw [pairing_productStructure J hJ, map_neg]

/-- The eigenspace `V^{1,0}` of `I` in `V_ℂ` is isotropic (§2.4). -/
theorem V10_isotropic (hJ : IsComplexStructure J) :
    ∀ a ∈ V10 n (productStructure n J), ∀ b ∈ V10 n (productStructure n J), pairing ℂ n a b = 0 := by
  exact s24a_V10_isotropic_of n (pairing_productStructure J hJ)

/-- The eigenspace `V^{0,1}` of `I` in `V_ℂ` is isotropic (§2.4). -/
theorem V01_isotropic (hJ : IsComplexStructure J) :
    ∀ a ∈ V01 n (productStructure n J), ∀ b ∈ V01 n (productStructure n J), pairing ℂ n a b = 0 := by
  exact s24a_V01_isotropic_of n (pairing_productStructure J hJ)

end ProductStructure

namespace KSecant

variable (P : KSecant n d)

/-- The `K`-linear extension of `f` is `η_{√-d}` on `V_K` (Lemma 2.2.4's file: `η_λ` on `V_K`
restricts to `η_λ` on `V_ℚ`). -/
theorem s24a_bcEndV_K (hW : IsCompl P.W₁ P.W₂) :
    bcEndV (Kd d) n (P.fη hW) = P.ηK hW (Kd.sqrtNeg d) :=
  s24a_linearMap_ext_bcV ℚ n (Kd d) fun x => by
    rw [bcEndV_bcV, fη, P.ηK_bcV P.d_pos hW]

/-- `f_ℂ` acts on `W_{1,ℂ}` by `√-d`. -/
theorem s24a_fC_of_mem_W₁ℂ (hW : IsCompl P.W₁ P.W₂) {z : V ℂ n} (hz : z ∈ P.W₁ℂ) :
    bcEndV ℂ n (P.fη hW) z = WeilClasses.sqrtNeg d • z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [s24a_bcEndV_bcV_tower ℂ n (Kd d), s24a_bcEndV_K, s24a_ηK_of_mem_W₁ P hW _ hw, map_smul,
        ← algebraMap_smul ℂ (Kd.sqrtNeg d)]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

/-- `f_ℂ` acts on `W_{2,ℂ}` by `-√-d`. -/
theorem s24a_fC_of_mem_W₂ℂ (hW : IsCompl P.W₁ P.W₂) {z : V ℂ n} (hz : z ∈ P.W₂ℂ) :
    bcEndV ℂ n (P.fη hW) z = (-WeilClasses.sqrtNeg d) • z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [s24a_bcEndV_bcV_tower ℂ n (Kd d), s24a_bcEndV_K, s24a_ηK_of_mem_W₂ P hW _ hw,
        s24a_σ_sqrtNeg, map_smul, ← algebraMap_smul ℂ (-Kd.sqrtNeg d)]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

/-- Two endomorphisms acting by scalars on a vector commute on it. -/
theorem s24a_comm_of_eigen {A B : Module.End ℂ (V ℂ n)} {x : V ℂ n} {α β : ℂ}
    (hA : A x = α • x) (hB : B x = β • x) : A (B x) = B (A x) := by
  rw [hB, map_smul, hA, map_smul, hB, smul_comm]

/-- `I_ℂ` commutes with `f_ℂ`: on each of the four summands of Lemma 2.2.6 both act by scalars. -/
theorem s24a_fC_comm_IC (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (z : V ℂ n) :
    bcEndV ℂ n (P.fη hP.isCompl) (complexifyV n (productStructure n J) z) =
      complexifyV n (productStructure n J) (bcEndV ℂ n (P.fη hP.isCompl) z) := by
  obtain ⟨⟨a, b, c, e⟩, ⟨ha, hb, hc, he, hz⟩, -⟩ := s24a_existsUnique_decomp_C P J hP z
  rw [hz]
  simp only [map_add]
  rw [s24a_comm_of_eigen (s24a_fC_of_mem_W₁ℂ P _ ha.1) (Module.End.mem_eigenspace_iff.mp ha.2),
    s24a_comm_of_eigen (s24a_fC_of_mem_W₂ℂ P _ hb.1) (Module.End.mem_eigenspace_iff.mp hb.2),
    s24a_comm_of_eigen (s24a_fC_of_mem_W₁ℂ P _ hc.1) (Module.End.mem_eigenspace_iff.mp hc.2),
    s24a_comm_of_eigen (s24a_fC_of_mem_W₂ℂ P _ he.1) (Module.End.mem_eigenspace_iff.mp he.2)]

/-- `I = I_{V_ℝ}` commutes with `f` (§2.4, "by Lemma 2.2.6"). -/
theorem fR_comm_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.fR hP.isCompl * productStructure n J = productStructure n J * P.fR hP.isCompl := by
  refine LinearMap.ext fun x => s24a_bcV_injective ℝ n ℂ ?_
  simp only [Module.End.mul_apply]
  rw [← s24a_complexifyV_bcV, fR, complexifyV_bcEndV, ← s24a_complexifyV_bcV,
    s24a_fC_comm_IC P J hP, ← s24a_complexifyV_bcV n (productStructure n J),
    ← s24a_complexifyV_bcV, complexifyV_bcEndV]

/-- `f_ℝ` is anti-self-dual on `V_ℝ` (the real extension of `pairing_fη_left`). -/
theorem s24a_pairing_fR_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℝ n) :
    pairing ℝ n (P.fR hW x) y = -pairing ℝ n x (P.fR hW y) := by
  have h := s24a_bilin_ext_bcV ℚ n ℝ (B₁ := (pairing ℝ n).compl₁₂ (P.fR hW) LinearMap.id)
    (B₂ := -(pairing ℝ n).compl₁₂ LinearMap.id (P.fR hW)) (fun x y => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.neg_apply, fR, bcEndV_bcV,
        s24a_pairing_bcV, P.pairing_fη_left, map_neg])
  exact congrArg (fun B : LinearMap.BilinForm ℝ (V ℝ n) => B x y) h

/-- `Ξ_P` is of Hodge type `(1,1)` for `I = I_{V_ℝ}`: `Ξ_P(I x, I y) = Ξ_P(x, y)` (§2.4). -/
theorem XiR_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (x y : V ℝ n) :
    P.XiR hP.isCompl (productStructure n J x) (productStructure n J y) = P.XiR hP.isCompl x y := by
  -- `(f(I x), I y) = (I(f x), I y) = (f x, y)`: `I` commutes with `f` and is an isometry.
  have hc := congrArg (fun A : Module.End ℝ (V ℝ n) => A x) (P.fR_comm_productStructure J hP)
  simp only [Module.End.mul_apply] at hc
  simp only [XiR, LinearMap.BilinForm.compLeft_apply]
  rw [hc, pairing_productStructure J hP.isComplex]

/-- `f ∘ I` is self-dual: `(f(I x), y)_V = (x, f(I y))_V` (§2.4). -/
theorem pairing_fR_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (x y : V ℝ n) :
    pairing ℝ n (P.fR hP.isCompl (productStructure n J x)) y =
      pairing ℝ n x (P.fR hP.isCompl (productStructure n J y)) := by
  -- `f` and `I` are anti-self-dual and commute.
  have hc := congrArg (fun A : Module.End ℝ (V ℝ n) => A y) (P.fR_comm_productStructure J hP)
  simp only [Module.End.mul_apply] at hc
  rw [s24a_pairing_fR_left, pairing_productStructure_left J hP.isComplex, neg_neg, hc]

/-- **The form `g_P`** (§2.4, before Lemma 2.4.2): `g_P(x, y) = Ξ_P(I x, y) = (f(I x), y)_V` on
`V_ℝ`, for the complex structure `I = I_{V_ℝ} = productStructure n J` of `X × X̂`. -/
noncomputable def gP (hW : IsCompl P.W₁ P.W₂) (J : Module.End ℝ (H1 ℝ n)) :
    LinearMap.BilinForm ℝ (V ℝ n) :=
  (P.XiR hW).compLeft (productStructure n J)

/-- `g_P` is symmetric (§2.4: "We get the symmetric bilinear form on `V_ℝ` …"). -/
theorem gP_isSymm (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    (P.gP hP.isCompl J).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp only [gP, XiR, LinearMap.BilinForm.compLeft_apply]
  rw [P.pairing_fR_productStructure J hP, s24a_pairing_comm]

/-- `W_{1,ℂ}` is isotropic (`W₁` is). -/
theorem s24a_W₁ℂ_isotropic : ∀ a ∈ P.W₁ℂ, ∀ b ∈ P.W₁ℂ, pairing ℂ n a b = 0 := by
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨w', hw', rfl⟩ := hy
          rw [s24a_pairing_bcV, P.s24a_W₁_isotropic hw hw', map_zero]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply, hx, hz, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-- `W_{2,ℂ}` is isotropic (`W₂` is). -/
theorem s24a_W₂ℂ_isotropic : ∀ a ∈ P.W₂ℂ, ∀ b ∈ P.W₂ℂ, pairing ℂ n a b = 0 := by
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨w', hw', rfl⟩ := hy
          rw [s24a_pairing_bcV, P.s24a_W₂_isotropic hw hw', map_zero]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply, hx, hz, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

end KSecant

/-- **Lemma 2.4.2** (`lemma-g-P-in-terms-of-4-summands`).
`g_P(v, v) = 2√d (-(v₁^{1,0}, v₂^{0,1})_V + (v₁^{0,1}, v₂^{1,0})_V)`.

Here `v ∈ V_ℝ` and `a = v₁^{1,0}`, `b = v₂^{1,0}`, `c = v₁^{0,1}`, `e = v₂^{0,1}` are the components
of `v` in `V_ℂ = W₁^{1,0} ⊕ W₂^{1,0} ⊕ W₁^{0,1} ⊕ W₂^{0,1}` (`KSecant.existsUnique_decomp_real`),
for the complex structure `I = I_{V_ℝ}` of `X × X̂`; the right-hand side is computed with the
`ℂ`-bilinear extension of the pairing. Standing assumption: Assumption 2.4.1. -/
theorem lemma2_4_2 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (v : V ℝ n) (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℝ ℂ n v = a + b + c + e) :
    ((P.gP hP.isCompl J v v : ℝ) : ℂ) =
      2 * (Real.sqrt d : ℂ) * (-pairing ℂ n a e + pairing ℂ n c b) := by
  have hW := hP.isCompl
  -- `g_P(v, v) = (f(I v), v)_V`, computed in `V_ℂ`.
  have h1 : ((P.gP hW J v v : ℝ) : ℂ) = pairing ℂ n (bcEndV ℂ n (P.fη hW)
      (complexifyV n (productStructure n J) (bcV ℝ ℂ n v))) (bcV ℝ ℂ n v) := by
    rw [s24a_complexifyV_bcV, ← complexifyV_bcEndV, s24a_complexifyV_bcV, s24a_pairing_bcV]
    rfl
  -- `I` acts by `±i` and `f` by `±√-d` on the four summands, so
  -- `f(I v) = √-1 √-d (v₁^{1,0} - v₂^{1,0} - v₁^{0,1} + v₂^{0,1})`.
  have hIa := Module.End.mem_eigenspace_iff.mp ha.2
  have hIb := Module.End.mem_eigenspace_iff.mp hb.2
  have hIc := Module.End.mem_eigenspace_iff.mp hc.2
  have hIe := Module.End.mem_eigenspace_iff.mp he.2
  have hfa := P.s24a_fC_of_mem_W₁ℂ hW ha.1
  have hfb := P.s24a_fC_of_mem_W₂ℂ hW hb.1
  have hfc := P.s24a_fC_of_mem_W₁ℂ hW hc.1
  have hfe := P.s24a_fC_of_mem_W₂ℂ hW he.1
  rw [h1, hv]
  simp only [map_add, map_smul, hIa, hIb, hIc, hIe, hfa, hfb, hfc, hfe, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  -- `W_{1,ℂ}`, `W_{2,ℂ}`, `V^{1,0}` and `V^{0,1}` are isotropic.
  have hV10 := V10_isotropic J hP.isComplex
  have hV01 := V01_isotropic J hP.isComplex
  rw [hV10 a ha.2 a ha.2, hV10 a ha.2 b hb.2, hV10 b hb.2 a ha.2, hV10 b hb.2 b hb.2,
    hV01 c hc.2 c hc.2, hV01 c hc.2 e he.2, hV01 e he.2 c hc.2, hV01 e he.2 e he.2,
    P.s24a_W₁ℂ_isotropic a ha.1 c hc.1, P.s24a_W₁ℂ_isotropic c hc.1 a ha.1,
    P.s24a_W₂ℂ_isotropic b hb.1 e he.1, P.s24a_W₂ℂ_isotropic e he.1 b hb.1,
    s24a_pairing_comm ℂ n e a, s24a_pairing_comm ℂ n b c]
  -- The sign convention for square roots: `√-1 √-d = -√d`.
  have hs : Complex.I * WeilClasses.sqrtNeg d = -(Real.sqrt d : ℂ) := by
    rw [WeilClasses.sqrtNeg, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination (2 * pairing ℂ n a e - 2 * pairing ℂ n c b) * hs

/-! ## Remark 2.4.3 -/

section Remark243

variable {F : Type*} [Field F] [CharZero F]

/-- The element `ϖ̃(λ) = ∏_{k=1}^{2n} (λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n})` of `C(V_F)` (Remark 2.4.3), for
a basis `e_1, …, e_{4n}` of `V_F` with `e_k = e k` in a maximal isotropic subspace `L`,
`e_{k+2n} = e' k` in a complementary maximal isotropic subspace `M`, and `(e_i, e_j)_V = 1` if
`|i - j| = 2n`, `0` otherwise. The factors commute; they are multiplied in the order
`k = 1, …, 2n`. -/
noncomputable def varpiTilde (e e' : Fin (2 * n) → V F n) (l : Fˣ) : C F n :=
  (List.ofFn fun k : Fin (2 * n) =>
    algebraMap F (C F n) ((l⁻¹ : Fˣ) : F) +
      ((l : F) - ((l⁻¹ : Fˣ) : F)) •
        (CliffordAlgebra.ι (Q F n) (e k) * CliffordAlgebra.ι (Q F n) (e' k))).prod

omit [CharZero F] in
/-- The factors of `ϖ̃(λ)` are Igusa's elements `s_k(λ)` ([Igusa, §2]). -/
private theorem s24a_varpiTilde_eq (e e' : Fin (2 * n) → V F n) (l : Fˣ) :
    varpiTilde e e' l = (List.ofFn fun k => igusaFactor (e k) (e' k) l).prod := rfl

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), general part: for a basis
`e₁, …, e_{4n}` of `V_F` as in `varpiTilde` (`L = span(e)`, `M = span(e')` complementary maximal
isotropic subspaces in duality) and `λ ∈ F^×`, `ϖ̃(λ)` is an element of `Spin(V_F)` (by the second
displayed formula in [Igusa, Sec. 2], `WeilClasses.igusa_sec2_mem`). -/
theorem remark2_4_3_mem (e e' : Fin (2 * n) → V F n) (he : ∀ i j, pairing F n (e i) (e j) = 0)
    (he' : ∀ i j, pairing F n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing F n (e i) (e' j) = if i = j then 1 else 0) (l : Fˣ) :
    varpiTilde e e' l ∈ spinGroup (Q F n) := by
  -- each factor is in `Spin(V_F)` by [Igusa, §2], and `Spin(V_F)` is closed under products
  rw [s24a_varpiTilde_eq]
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  exact igusa_sec2_mem (e k) (e' k) (he k k) (he' k k) (by simpa using hee' k k) l

/-- The action of a product of spin elements on a common eigenvector. -/
theorem s24a_rho_ofFn_prod_apply {m : ℕ} (s : Fin m → Spin F n) (c : Fin m → F) (v : V F n)
    (h : ∀ k, rho F n (s k) v = c k • v) : rho F n (List.ofFn s).prod v = (∏ k, c k) • v := by
  induction m with
  | zero => simp [rho]
  | succ m ih =>
      rw [List.ofFn_succ, List.prod_cons, rho, CliffordAlgebra.spinVectorAction_mul,
        LinearEquiv.mul_apply, ← rho, ← rho, ih (fun k => s k.succ) (fun k => c k.succ)
          (fun k => h k.succ), map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm (c 0)]

/-- `ϖ̃(λ)` as a product of Igusa's elements in `Spin(V_F)`. -/
private theorem s24a_varpiTilde_spin (e e' : Fin (2 * n) → V F n)
    (he : ∀ i j, pairing F n (e i) (e j) = 0) (he' : ∀ i j, pairing F n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing F n (e i) (e' j) = if i = j then 1 else 0) (l : Fˣ) :
    (⟨varpiTilde e e' l, remark2_4_3_mem e e' he he' hee' l⟩ : Spin F n) =
      (List.ofFn fun k => (⟨igusaFactor (e k) (e' k) l, igusa_sec2_mem (e k) (e' k) (he k k)
        (he' k k) (by simpa using hee' k k) l⟩ : Spin F n)).prod := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_ofFn]
  rfl

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), general part, continued: `ϖ̃(λ)` maps to `ϖ(λ) ∈ SO(V_F)`, which acts on `L`
by multiplication by `λ²` and on `M` by multiplication by `λ⁻²`. -/
theorem remark2_4_3_rho (e e' : Fin (2 * n) → V F n) (he : ∀ i j, pairing F n (e i) (e j) = 0)
    (he' : ∀ i j, pairing F n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing F n (e i) (e' j) = if i = j then 1 else 0) (l : Fˣ) (i : Fin (2 * n)) :
    rho F n ⟨varpiTilde e e' l, remark2_4_3_mem e e' he he' hee' l⟩ (e i) = ((l : F) ^ 2) • e i ∧
      rho F n ⟨varpiTilde e e' l, remark2_4_3_mem e e' he he' hee' l⟩ (e' i) =
        (((l⁻¹ : Fˣ) : F) ^ 2) • e' i := by
  rw [s24a_varpiTilde_spin e e' he he' hee' l]
  have hpair : ∀ k, pairing F n (e k) (e' k) = 1 := fun k => by simpa using hee' k k
  constructor
  · -- the factor `k = i` multiplies `e i` by `λ²`, the others fix it ([Igusa, §2])
    rw [s24a_rho_ofFn_prod_apply _ (fun k => if k = i then (l : F) ^ 2 else 1) (e i),
      Finset.prod_ite_eq' Finset.univ i]
    · simp only [Finset.mem_univ, ↓reduceIte]
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [↓reduceIte]
      exact (igusa_sec2_rho (e k) (e' k) (he k k) (he' k k) (hpair k) l).1
    · simp only [hk, ↓reduceIte, one_smul]
      refine (igusa_sec2_rho (e k) (e' k) (he k k) (he' k k) (hpair k) l).2.2 (e i) (he k i) ?_
      rw [s24a_pairing_comm, hee' i k]
      simp [Ne.symm hk]
  · -- the factor `k = i` multiplies `e' i` by `λ⁻²`, the others fix it
    rw [s24a_rho_ofFn_prod_apply _ (fun k => if k = i then ((l⁻¹ : Fˣ) : F) ^ 2 else 1) (e' i),
      Finset.prod_ite_eq' Finset.univ i]
    · simp only [Finset.mem_univ, ↓reduceIte]
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [↓reduceIte]
      exact (igusa_sec2_rho (e k) (e' k) (he k k) (he' k k) (hpair k) l).2.1
    · simp only [hk, ↓reduceIte, one_smul]
      refine (igusa_sec2_rho (e k) (e' k) (he k k) (he' k k) (hpair k) l).2.2 (e' i) ?_ (he' k i)
      rw [hee' k i]
      simp [hk]

end Remark243

/-! ### Helpers (`s24a_`): spin groups and change of coefficients -/

section S24aSpin

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

/-- `bcC` sends `ι v` to `ι (bcV v)`. -/
theorem s24a_bcC_ι (v : V F n) : bcC F F' n (CliffordAlgebra.ι (Q F n) v) =
    CliffordAlgebra.ι (Q F' n) (bcV F F' n v) :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- `bcC` commutes with the conjugation `x ↦ x*` of `C(V)`. -/
theorem s24a_bcC_star (x : C F n) : bcC F F' n (star x) = star (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [star_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n),
        star_algebraMap]
  | ι m => rw [star_ι, map_neg, s24a_bcC_ι, star_ι]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]
  | mul x y hx hy => rw [star_mul, map_mul, hx, hy, map_mul, star_mul]

/-- `ρ` commutes with change of coefficients. -/
theorem s24a_rho_bcC (g : Spin F n) (x : V F n) :
    rho F' n ⟨bcC F F' n g, bcC_mem_spinGroup F F' n g⟩ (bcV F F' n x) =
      bcV F F' n (rho F n g x) := by
  apply CliffordAlgebra.ι_injective (Q F' n)
  rw [ι_rho, ← s24a_bcC_ι, ← s24a_bcC_ι, ι_rho, map_mul, map_mul, s24a_bcC_star]

omit [CharZero F] in
/-- The quadratic form `Q` of `V_F` is nondegenerate. -/
theorem s24a_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

omit [CharZero F] in
/-- `V_F = 0` for `n = 0`. -/
theorem s24a_V_zero (x : V F 0) : x = 0 := by
  have hw : ∀ w : H1 F 0, w = 0 := fun w => funext fun i => absurd i.2 (by simp)
  refine Prod.ext (LinearMap.ext fun w => ?_) (hw _)
  rw [hw w, map_zero]
  rfl

/-- `V_F ≠ 0` for `n > 0`. -/
theorem s24a_nontrivial_V (hn : 0 < n) : Nontrivial (V F n) := by
  refine nontrivial_of_ne ((0, e F n ⟨0, by omega⟩) : V F n) 0 fun h => ?_
  have := congrArg (fun v : V F n => v.2 ⟨0, by omega⟩) h
  simp [e] at this

end S24aSpin

/-- An orthogonal complex structure `I` of `V_ℝ` lies in `ρ(Spin(V_ℝ))`: `I = G²` with
`G = (1 + I)/√2 ∈ O(V_ℝ)`, so `det I = (det G)² > 0`, and the spinor norm of `I` is the square of
that of `G` in the square-class group `ℝ^×/(ℝ^×)²`, which has exponent `2`; by Tau Ceti,
`ρ(Spin(V_ℝ))` is the kernel of the spinor norm on `SO(V_ℝ)`. (This fills the step "must be already
in `Spin(V_ℝ)`" of Remark 2.4.3, see `remark2_4_3_complexStructure`.) -/
private theorem s24a_exists_spin_lift (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  have hII : ∀ x, I (I x) = -x := fun x => by
    have := congrArg (fun A : Module.End ℝ (V ℝ n) => A x) hI
    simpa using this
  have hQI : ∀ x, Q ℝ n (I x) = Q ℝ n x := fun x => by
    have h := hIso x x
    rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, QuadraticMap.polar_self, two_smul, two_smul] at h
    linarith
  have hxIx : ∀ x, pairing ℝ n x (I x) = 0 := fun x => by
    have h := hIso x (I x)
    rw [hII, map_neg, s24a_pairing_comm ℝ n (I x) x] at h
    linarith
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_mul_cancel₀ two_ne_zero]
  set r : ℝ := (Real.sqrt 2)⁻¹ with hr_def
  let Ie : V ℝ n ≃ₗ[ℝ] V ℝ n := LinearEquiv.ofLinearMap I (-I)
    (LinearMap.ext fun x => by simp [hII]) (LinearMap.ext fun x => by simp [hII])
  let Gl : Module.End ℝ (V ℝ n) := r • (1 + I)
  let Hl : Module.End ℝ (V ℝ n) := r • (1 - I)
  have hGx : ∀ x, Gl x = r • (x + I x) := fun x => by simp [Gl]
  have hHx : ∀ x, Hl x = r • (x - I x) := fun x => by simp [Hl]
  have hGH : Gl ∘ₗ Hl = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hHx, hGx, map_smul, map_sub, hII, LinearMap.id_apply]
    have : r • (r • (x - I x) + r • (I x - -x)) = (r * r * 2) • x := by module
    rw [this, hr, one_smul]
  have hHG : Hl ∘ₗ Gl = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hGx, hHx, map_smul, map_add, hII, LinearMap.id_apply]
    have : r • (r • (x + I x) - r • (I x + -x)) = (r * r * 2) • x := by module
    rw [this, hr, one_smul]
  let Ge : V ℝ n ≃ₗ[ℝ] V ℝ n := LinearEquiv.ofLinearMap Gl Hl hGH hHG
  have hGO : Ge ∈ TauCeti.QuadraticMap.orthogonalGroup (Q ℝ n) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    show Q ℝ n (Gl x) = Q ℝ n x
    have h0 : QuadraticMap.polar (Q ℝ n) x (I x) = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply]; exact hxIx x
    rw [hGx, QuadraticMap.map_smul, QuadraticMap.map_add (Q ℝ n) x (I x), hQI, h0, smul_eq_mul]
    linear_combination (Q ℝ n x) * hr
  have hGG : Ge * Ge = Ie := LinearEquiv.ext fun x => by
    show Gl (Gl x) = I x
    rw [hGx, hGx, map_smul, map_add, hII]
    have : r • (r • (x + I x) + r • (I x + -x)) = (r * r * 2) • I x := by module
    rw [this, hr, one_smul]
  have hIO : Ie ∈ TauCeti.QuadraticMap.orthogonalGroup (Q ℝ n) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact hQI
  -- `det I = (det G)² ≥ 0` and `(det I)² = det(-1) = 1`, so `det I = 1`.
  have hdet : LinearEquiv.det Ie = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    show LinearMap.det I = 1
    have h1 : LinearMap.det I = LinearMap.det Gl * LinearMap.det Gl := by
      rw [← LinearMap.det_comp]
      congr 1
      exact LinearMap.ext fun x => (congrArg (fun A : V ℝ n ≃ₗ[ℝ] V ℝ n => A x) hGG).symm
    have h2 : LinearMap.det I * LinearMap.det I = 1 := by
      rw [← LinearMap.det_comp]
      have : I ∘ₗ I = (-1 : ℝ) • LinearMap.id := LinearMap.ext fun x => by simp [hII]
      rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one,
        Module.finrank_eq_card_basis (basisV ℝ n), Fintype.card_fin]
      exact Even.neg_one_pow ⟨2 * n, rfl⟩
    have h3 : 0 ≤ LinearMap.det I := by rw [h1]; exact mul_self_nonneg _
    nlinarith
  have hISO : Ie ∈ TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) :=
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨hIO, hdet⟩
  have hQnd := s24a_Q_nondegenerate ℝ n
  -- The square-class group has exponent two.
  have hsq : ∀ x : Multiplicative (TauCeti.SquareClassGroup ℝ), x * x = 1 := by
    intro x
    have h := two_smul (ZMod 2) (Multiplicative.toAdd x)
    rw [show (2 : ZMod 2) = 0 from rfl, zero_smul] at h
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, ← h, toAdd_one]
  have hnorm : CliffordAlgebra.spinorNorm (Q ℝ n) hQnd ⟨Ie, hISO⟩ = 1 := by
    rw [CliffordAlgebra.spinorNorm_apply]
    have h1 : QuadraticMap.specialOrthogonalToOrthogonal (Q ℝ n) ⟨Ie, hISO⟩ =
        ⟨Ge, hGO⟩ * ⟨Ge, hGO⟩ := Subtype.ext (by
      rw [QuadraticMap.coe_specialOrthogonalToOrthogonal]
      exact hGG.symm)
    rw [h1, map_mul]
    exact hsq _
  obtain ⟨g, hg⟩ : (⟨Ie, hISO⟩ : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n)) ∈
      (CliffordAlgebra.spinToSpecialOrthogonal (Q ℝ n)).range := by
    rw [CliffordAlgebra.range_spinToSpecialOrthogonal_eq_ker_spinorNorm (Q ℝ n) hQnd]
    exact hnorm
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  have := congrArg
    (fun h : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) => (h : V ℝ n ≃ₗ[ℝ] V ℝ n) x) hg
  simp only [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply] at this
  exact this

/-- Dual bases `e`, `e'` of two isotropic subspaces together span `V_ℂ`. -/
theorem s24a_span_sum_elim (hn : 0 < n) (e e' : Fin (2 * n) → V ℂ n)
    (he : ∀ i j, pairing ℂ n (e i) (e j) = 0) (he' : ∀ i j, pairing ℂ n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing ℂ n (e i) (e' j) = if i = j then 1 else 0) :
    Submodule.span ℂ (Set.range (Sum.elim e e')) = ⊤ := by
  have hli : LinearIndependent ℂ (Sum.elim e e') := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have h1 : ∀ j, g (Sum.inl j) = 0 := fun j => by
      have := congrArg (fun x => pairing ℂ n x (e' j)) hg
      simpa [map_sum, LinearMap.sum_apply, hee', he'] using this
    have h2 : ∀ j, g (Sum.inr j) = 0 := fun j => by
      have := congrArg (fun x => pairing ℂ n x (e j)) hg
      simpa [map_sum, LinearMap.sum_apply, he, s24a_pairing_comm ℂ n (e' _) (e j), hee'] using this
    rintro (j | j)
    exacts [h1 j, h2 j]
  have : Nonempty (Fin (2 * n) ⊕ Fin (2 * n)) := ⟨Sum.inl ⟨0, by omega⟩⟩
  refine hli.span_eq_top_of_card_eq_finrank ?_
  rw [Fintype.card_sum, Fintype.card_fin, Module.finrank_eq_card_basis (basisV ℂ n),
    Fintype.card_fin]

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), the special case: if `I` is an (orthogonal) complex structure of `V_ℝ`, take
`L = V^{1,0}`, `M = V^{0,1}` (dual bases `e`, `e'`) and `λ = e^{iπ/4}`: the element `ϖ̃(e^{iπ/4})` of
`Spin(V_ℂ)` is already in `Spin(V_ℝ)` and maps to `I = ϖ(e^{iπ/4})`.

Reading: "complex structure" means a complex structure which is an isometry of `(·,·)_V` (as
`I_{V_ℝ}` is), so that `V^{1,0}` and `V^{0,1}` are complementary maximal isotropic subspaces.

Departure from the paper: the paper concludes that `ϖ̃(e^{iπ/4}) ∈ Spin(V_ℂ)` "must be already in
`Spin(V_ℝ)` as it maps to `I`". An element of `Spin(V_ℂ)` over an element of `SO(V_ℝ)` is real only
if that element lies in `ρ(Spin(V_ℝ))` (an element of `SO(V_ℝ)` of nontrivial spinor norm, e.g. `-1`
on a real hyperbolic plane, has no real lift). We prove `I ∈ ρ(Spin(V_ℝ))`: `I = G²` with
`G = (1 + I)/√2 ∈ O(V_ℝ)`, so the spinor norm of `I` (valued in `ℝ^×/(ℝ^×)²`) is trivial, and
`ρ(Spin(V_ℝ))` is the kernel of the spinor norm (Tau Ceti). Then `ϖ̃(e^{iπ/4})` and the
complexification of a real lift lie over `I_ℂ`, so they agree up to the kernel `{±1}` of `ρ` (Tau
Ceti), and `-1 ∈ Spin(V_ℝ)`. -/
theorem remark2_4_3_complexStructure (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (e e' : Fin (2 * n) → V ℂ n)
    (he : ∀ i, e i ∈ V10 n I) (he' : ∀ i, e' i ∈ V01 n I)
    (hee' : ∀ i j, pairing ℂ n (e i) (e' j) = if i = j then 1 else 0) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I ∧
      bcC ℝ ℂ n (g : C ℝ n) =
        varpiTilde e e' (Units.mk0 (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I))
          (Complex.exp_ne_zero _)) := by
  set l : ℂˣ := Units.mk0 (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)) (Complex.exp_ne_zero _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `V = 0` and `ϖ̃(λ) = 1`.
    refine ⟨1, LinearMap.ext fun x => ?_, ?_⟩
    · rw [s24a_V_zero ℝ x, map_zero, map_zero]
    · rw [OneMemClass.coe_one, map_one]
      rfl
  -- `V^{1,0}` and `V^{0,1}` are isotropic, `I` being an isometry.
  have he0 : ∀ i j, pairing ℂ n (e i) (e j) = 0 := fun i j =>
    s24a_V10_isotropic_of n hIso _ (he i) _ (he j)
  have he0' : ∀ i j, pairing ℂ n (e' i) (e' j) = 0 := fun i j =>
    s24a_V01_isotropic_of n hIso _ (he' i) _ (he' j)
  have hmem := remark2_4_3_mem e e' he0 he0' hee' l
  -- `λ² = i` and `λ⁻² = -i` for `λ = e^{iπ/4}`.
  have hl2 : (l : ℂ) ^ 2 = Complex.I := by
    rw [Units.val_mk0, ← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) / 4 * Complex.I) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  have hl2' : ((l⁻¹ : ℂˣ) : ℂ) ^ 2 = -Complex.I := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hl2, Complex.inv_I]
  -- `ρ(ϖ̃(λ)) = ϖ(λ)`, which is `I` on `V_ℂ = V^{1,0} ⊕ V^{0,1}`.
  have hρϖ : (rho ℂ n ⟨varpiTilde e e' l, hmem⟩ : V ℂ n →ₗ[ℂ] V ℂ n) = complexifyV n I := by
    refine LinearMap.ext_on_range (s24a_span_sum_elim hn e e' he0 he0' hee') ?_
    rintro (i | i)
    · simp only [Sum.elim_inl, LinearEquiv.coe_coe]
      rw [(remark2_4_3_rho e e' he0 he0' hee' l i).1, hl2,
        Module.End.mem_eigenspace_iff.mp (he i)]
    · simp only [Sum.elim_inr, LinearEquiv.coe_coe]
      rw [(remark2_4_3_rho e e' he0 he0' hee' l i).2, hl2',
        Module.End.mem_eigenspace_iff.mp (he' i)]
  -- (Departure, see the docstring.) A lift `g₀ ∈ Spin(V_ℝ)` of `I`.
  obtain ⟨g₀, hg₀⟩ := s24a_exists_spin_lift I hI hIso
  have hρg₀ : (rho ℂ n ⟨bcC ℝ ℂ n g₀, bcC_mem_spinGroup ℝ ℂ n g₀⟩ : V ℂ n →ₗ[ℂ] V ℂ n) =
      complexifyV n I :=
    s24a_linearMap_ext_bcV ℝ n ℂ fun x => by
      rw [LinearEquiv.coe_coe, s24a_rho_bcC, s24a_complexifyV_bcV, ← hg₀]
      rfl
  -- `ϖ̃(λ)` and `g₀` lie over the same element of `SO(V_ℂ)`, so they agree up to sign.
  have := s24a_nontrivial_V ℂ n hn
  have hQC := s24a_Q_nondegenerate ℂ n
  have hSO : CliffordAlgebra.spinToSpecialOrthogonal (Q ℂ n) ⟨varpiTilde e e' l, hmem⟩ =
      CliffordAlgebra.spinToSpecialOrthogonal (Q ℂ n)
        ⟨bcC ℝ ℂ n g₀, bcC_mem_spinGroup ℝ ℂ n g₀⟩ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply,
      CliffordAlgebra.coe_spinToSpecialOrthogonal_apply]
    exact congrArg (fun A : V ℂ n →ₗ[ℂ] V ℂ n => A z) (hρϖ.trans hρg₀.symm)
  rcases CliffordAlgebra.eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq (Q ℂ n) hQC _ _ hSO
    with h | h
  · exact ⟨g₀, hg₀, (congrArg Subtype.val h).symm⟩
  · have := s24a_nontrivial_V ℝ n hn
    have hQR := s24a_Q_nondegenerate ℝ n
    have hneg : ∀ x, rho ℝ n (CliffordAlgebra.spinGroup.negOne (Q ℝ n) hQR.ne_zero) x = x := by
      intro x
      apply CliffordAlgebra.ι_injective (Q ℝ n)
      rw [ι_rho, CliffordAlgebra.spinGroup.coe_negOne, star_neg, star_one]
      simp
    refine ⟨CliffordAlgebra.spinGroup.negOne (Q ℝ n) hQR.ne_zero * g₀, ?_, ?_⟩
    · refine LinearMap.ext fun x => ?_
      rw [← hg₀]
      show rho ℝ n _ x = rho ℝ n g₀ x
      rw [rho, CliffordAlgebra.spinVectorAction_mul, LinearEquiv.mul_apply, ← rho, ← rho, hneg]
    · have h' := congrArg Subtype.val h
      rw [Submonoid.coe_mul, CliffordAlgebra.spinGroup.coe_negOne] at h'
      rw [Submonoid.coe_mul, CliffordAlgebra.spinGroup.coe_negOne, map_mul, map_neg, map_one]
      exact h'.symm

/-- `V_ℂ = V^{1,0} + V^{0,1}`: `z = ½(z - i I z) + ½(z + i I z)`. -/
theorem s24a_V10_sup_V01 {I : Module.End ℝ (V ℝ n)} (hI : IsComplexStructure I) :
    V10 n I ⊔ V01 n I = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hsq : ∀ w, complexifyV n I (complexifyV n I w) = -w := fun w => by
    have := congrArg (fun A : Module.End ℂ (V ℂ n) => A w) (s24a_complexifyV_sq n hI)
    simpa using this
  refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℂ) • (z - Complex.I • complexifyV n I z), ?_,
    (1 / 2 : ℂ) • (z + Complex.I • complexifyV n I z), ?_, ?_⟩
  · rw [V10, Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hsq]
    linear_combination (norm := module) Complex.I_mul_I • ((1 / 2 : ℂ) • complexifyV n I z)
  · rw [V01, Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hsq]
    linear_combination (norm := module) Complex.I_mul_I • ((1 / 2 : ℂ) • complexifyV n I z)
  · module

/-- The pairing `V^{1,0} × V^{0,1} → ℂ` has no left kernel (`V^{1,0}` is isotropic and the pairing
of `V_ℂ` is nondegenerate). -/
theorem s24a_pairing_V10_V01_injective {I : Module.End ℝ (V ℝ n)} (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    Function.Injective ((pairing ℂ n).compl₁₂ (V10 n I).subtype (V01 n I).subtype) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  apply Subtype.ext
  refine s24a_pairing_nondeg ℂ n _ fun z => ?_
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp ((s24a_V10_sup_V01 hI).symm ▸ trivial :
    z ∈ V10 n I ⊔ V01 n I)
  rw [map_add, s24a_V10_isotropic_of n hIso _ x.2 _ ha, zero_add]
  exact congrArg (fun φ : Module.Dual ℂ (V01 n I) => φ ⟨c, hc⟩) hx

/-- The pairing `V^{0,1} × V^{1,0} → ℂ` has no left kernel. -/
theorem s24a_pairing_V01_V10_injective {I : Module.End ℝ (V ℝ n)} (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    Function.Injective ((pairing ℂ n).compl₁₂ (V01 n I).subtype (V10 n I).subtype) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  apply Subtype.ext
  refine s24a_pairing_nondeg ℂ n _ fun z => ?_
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp ((s24a_V10_sup_V01 hI).symm ▸ trivial :
    z ∈ V10 n I ⊔ V01 n I)
  rw [map_add, s24a_V01_isotropic_of n hIso _ x.2 _ hc, add_zero]
  exact congrArg (fun φ : Module.Dual ℂ (V10 n I) => φ ⟨a, ha⟩) hx

/-- `dim V^{1,0} = dim V^{0,1} = 2n` for an orthogonal complex structure. -/
theorem s24a_finrank_V10_V01 {I : Module.End ℝ (V ℝ n)} (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    Module.finrank ℂ (V10 n I) = 2 * n ∧ Module.finrank ℂ (V01 n I) = 2 * n := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (s24a_pairing_V10_V01_injective hI hIso)
  have h2 := LinearMap.finrank_le_finrank_of_injective (s24a_pairing_V01_V10_injective hI hIso)
  rw [Subspace.dual_finrank_eq] at h1 h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (V10 n I) (V01 n I)
  rw [s24a_V10_sup_V01 hI, s24a_V10_inf_V01, finrank_top, finrank_bot,
    Module.finrank_eq_card_basis (basisV ℂ n), Fintype.card_fin] at h3
  omega

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`): every complex structure `I` of `V_ℝ` which is an isometry of `(·,·)_V` lifts to
an element of `Spin(V_ℝ)`, i.e. lies in `ρ(Spin(V_ℝ)) = SO_+(V_ℝ)`. -/
theorem remark2_4_3_exists_lift (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  -- The special case of the general fact: `L = V^{1,0}`, `M = V^{0,1}` with dual bases `e`, `e'`
  -- (`V^{0,1} ≅ (V^{1,0})*` through the pairing), and `λ = e^{iπ/4}`.
  obtain ⟨h10, h01⟩ := s24a_finrank_V10_V01 hI hIso
  let b := Module.finBasisOfFinrankEq ℂ (V10 n I) h10
  let Ψ := (pairing ℂ n).flip.compl₁₂ (V01 n I).subtype (V10 n I).subtype
  have hΨinj : Function.Injective Ψ := by
    have h := s24a_pairing_V01_V10_injective hI hIso
    intro y y' hyy'
    apply h
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun φ : Module.Dual ℂ (V10 n I) => φ x) hyy'
    simpa [Ψ, s24a_pairing_comm ℂ n (x : V ℂ n)] using this
  have hΨsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, h10, h01])).mp hΨinj
  let Ψe := LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  let e : Fin (2 * n) → V ℂ n := fun i => (b i : V ℂ n)
  let e' : Fin (2 * n) → V ℂ n := fun j => (Ψe.symm (b.dualBasis j) : V ℂ n)
  have hee' : ∀ i j, pairing ℂ n (e i) (e' j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrArg (fun φ : Module.Dual ℂ (V10 n I) => φ (b i))
      (Ψe.apply_symm_apply (b.dualBasis j))
    simp only [Module.Basis.dualBasis_apply_self] at h
    rw [← h]
    rfl
  obtain ⟨g, hg, -⟩ := remark2_4_3_complexStructure I hI hIso e e' (fun i => (b i).2)
    (fun j => (Ψe.symm (b.dualBasis j)).2) hee'
  exact ⟨g, hg⟩

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), first sentence: the complex structure `I = I_{V_ℝ}` of `X × X̂` lifts to an
element of `Spin(V_ℝ)`. -/
theorem remark2_4_3 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = productStructure n J := by
  -- `I_{V_ℝ}` is an orthogonal complex structure.
  exact remark2_4_3_exists_lift (productStructure n J) (isComplexStructure_productStructure J hJ)
    (pairing_productStructure J hJ)

end WeilClasses
