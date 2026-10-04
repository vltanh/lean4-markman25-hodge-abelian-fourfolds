module

public import WeilClasses.PeriodDomain.Defs
public import WeilClasses.Spinor.Integral
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinorNorm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import WeilClasses.Secant.Defs

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

/-! ### Helpers (prefix `s4_`) for `I_θ` -/

theorem s4_Q_nondegenerate (n : ℕ) : (Q ℝ n).Nondegenerate := by
  apply TauCeti.nondegenerate_dualProd
  exact Module.eval_apply_injective ℝ

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

theorem s4_det_extEnd (n : ℕ) (A : Module.End ℝ (V ℝ n)) :
    LinearMap.det (s4_extEnd ℝ ℂ n A) = ((LinearMap.det A : ℝ) : ℂ) := by
  rw [s4_extEnd, LinearMap.det_toLin, ← LinearMap.det_toMatrix (basisV ℝ n) A]
  exact ((algebraMap ℝ ℂ).map_det _).symm

theorem s4_rot_mul (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) (a b : ℝ) :
    rotI n I a * rotI n I b = rotI n I (a + b) := by
  have hII : I * I = -1 := hI
  simp only [rotI, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hII,
    Real.cos_add, Real.sin_add, add_smul, sub_smul, smul_neg]
  module

theorem s4_rot_zero (n : ℕ) (I : Module.End ℝ (V ℝ n)) : rotI n I 0 = 1 := by
  simp [rotI]

/-- `I_θ` as a linear automorphism. -/
noncomputable def s4_rotEquiv (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (θ : ℝ) : V ℝ n ≃ₗ[ℝ] V ℝ n :=
  LinearEquiv.ofLinearMap (rotI n I θ) (rotI n I (-θ))
    (by rw [← Module.End.mul_eq_comp, s4_rot_mul n I hI, add_neg_cancel, s4_rot_zero]; rfl)
    (by rw [← Module.End.mul_eq_comp, s4_rot_mul n I hI, neg_add_cancel, s4_rot_zero]; rfl)

theorem s4_coe_rotEquiv (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) (θ : ℝ) :
    (s4_rotEquiv n I hI θ : Module.End ℝ (V ℝ n)) = rotI n I θ := rfl

theorem s4_coe_rotEquiv_inv (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (θ : ℝ) : (((s4_rotEquiv n I hI θ)⁻¹ : V ℝ n ≃ₗ[ℝ] V ℝ n) : Module.End ℝ (V ℝ n)) =
      rotI n I (-θ) := rfl

theorem s4_extEnd_rot_V10 (n : ℕ) (I : Module.End ℝ (V ℝ n)) (θ : ℝ) (x : V ℂ n)
    (hx : x ∈ V10 n I) :
    s4_extEnd ℝ ℂ n (rotI n I θ) x = ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) • x := by
  have hx' : s4_extEnd ℝ ℂ n I x = Complex.I • x := Module.End.mem_eigenspace_iff.mp hx
  rw [rotI, s4_extEnd_add, s4_extEnd_smul, s4_extEnd_smul, s4_extEnd_one, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, hx', smul_smul, ← add_smul]
  rfl

theorem s4_extEnd_rot_V01 (n : ℕ) (I : Module.End ℝ (V ℝ n)) (θ : ℝ) (x : V ℂ n)
    (hx : x ∈ V01 n I) :
    s4_extEnd ℝ ℂ n (rotI n I θ) x = ((Real.cos θ : ℂ) - Real.sin θ * Complex.I) • x := by
  have hx' : s4_extEnd ℝ ℂ n I x = (-Complex.I) • x := Module.End.mem_eigenspace_iff.mp hx
  rw [rotI, s4_extEnd_add, s4_extEnd_smul, s4_extEnd_smul, s4_extEnd_one, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, hx', smul_smul, ← add_smul]
  congr 1
  simp only [Complex.coe_algebraMap]
  ring

theorem s4_cos_sin_mul (θ : ℝ) :
    ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) * ((Real.cos θ : ℂ) - Real.sin θ * Complex.I) = 1 := by
  have h := Real.cos_sq_add_sin_sq θ
  have : ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) * ((Real.cos θ : ℂ) - Real.sin θ * Complex.I) =
      ((Real.cos θ ^ 2 + Real.sin θ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, h]
  simp


section SBC
variable (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (n : ℕ)

theorem s4_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) := by
  unfold bcS
  exact ExteriorAlgebra.lift_ι_apply F _ _ w

theorem s4_bcS_ιMulti (k : ℕ) (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) =
      ExteriorAlgebra.ιMulti F' k (fun i => bcH1 F F' n (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, s4_bcS_ι]

theorem s4_bcH1_basisFun (i : Fin (2 * n)) :
    bcH1 F F' n (Pi.basisFun F (Fin (2 * n)) i) = Pi.basisFun F' (Fin (2 * n)) i := by
  have h := s4_bcH1_e F F' n i
  simpa [e] using h

theorem s4_bcS_basisS (K : Finset (Fin (2 * n))) :
    bcS F F' n (basisS F n K) = basisS F' n K := by
  rw [basisS, basisS, ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family, s4_bcS_ιMulti, Function.comp_apply, s4_bcH1_basisFun]
  rfl

theorem s4_bcS_eq_sum (x : S F n) :
    bcS F F' n x = ∑ K, algebraMap F F' ((basisS F n).repr x K) • basisS F' n K := by
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s4_bcS_basisS, algebraMap_smul]

theorem s4_repr_bcS (x : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n x) K = algebraMap F F' ((basisS F n).repr x K) := by
  rw [s4_bcS_eq_sum, Module.Basis.repr_sum_self]

theorem s4_bcS_injective : Function.Injective (bcS F F' n) := by
  intro x y h
  apply (basisS F n).repr.injective
  ext K
  have := congrArg (fun z => (basisS F' n).repr z K) h
  simp only [s4_repr_bcS] at this
  exact (algebraMap F F').injective this

end SBC

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
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    refine ⟨add_mem hs1 ht1, fun g hg θ hθ => ?_⟩
    rw [map_add, hs2 g hg θ hθ, ht2 g hg θ hθ, smul_add]
  zero_mem' := ⟨zero_mem _, fun g hg θ hθ => by rw [map_zero, smul_zero]⟩
  smul_mem' := by
    rintro c s ⟨hs1, hs2⟩
    refine ⟨Submodule.smul_mem _ c hs1, fun g hg θ hθ => ?_⟩
    rw [map_smul, hs2 g hg θ hθ, smul_comm]

/-- `g ↦ g` is continuous from `Spin(V_ℝ)` (with `spinTopology`) to `C(V_ℝ)` (module topology). -/
theorem s4_continuous_coe_spin (n : ℕ) :
    @Continuous _ _ (spinTopology n) _ (fun g : Spin ℝ n => (g : C ℝ n)) := by
  let := spinTopology n
  set L : (Finset (Fin (2 * n + 2 * n)) → ℝ) →ₗ[ℝ] C ℝ n :=
    (CliffordAlgebra.equivExterior (Q ℝ n)).symm.toLinearMap ∘ₗ
      (basisExt ℝ n).equivFun.symm.toLinearMap
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hc : Continuous (fun g : Spin ℝ n =>
      ⇑((basisExt ℝ n).repr (CliffordAlgebra.equivExterior (Q ℝ n) (g : C ℝ n)))) :=
    continuous_induced_dom
  refine (hL.comp hc).congr fun g => ?_
  simp only [Function.comp_apply, L, LinearMap.coe_comp, LinearEquiv.coe_coe]
  rw [show ⇑((basisExt ℝ n).repr (CliffordAlgebra.equivExterior (Q ℝ n) (g : C ℝ n))) =
    (basisExt ℝ n).equivFun (CliffordAlgebra.equivExterior (Q ℝ n) (g : C ℝ n)) from rfl,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- For `p ∈ S_ℝ`, `{g ∈ Spin(V_ℝ) : m_g p = c p}` is closed. -/
theorem s4_isClosed_fix (n : ℕ) (p : S ℝ n) (c : ℝ) :
    @IsClosed _ (spinTopology n) {g : Spin ℝ n | m ℝ n (g : C ℝ n) p = c • p} := by
  let := spinTopology n
  have hm : Continuous (fun x : C ℝ n => m ℝ n x p) :=
    IsModuleTopology.continuous_of_linearMap
      ((LinearMap.applyₗ p) ∘ₗ (m ℝ n).toLinearMap : C ℝ n →ₗ[ℝ] S ℝ n)
  exact isClosed_singleton.preimage (hm.comp (s4_continuous_coe_spin n))

section SBC2
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s4_bcDual_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  have hw : w = ∑ i, w i • e F n i := by
    ext j; simp [e, Pi.single_apply]
  rw [show bcDual F F' n θ = ∑ i, algebraMap F F' (θ (e F n i)) • f F' n i from rfl,
    LinearMap.sum_apply]
  conv_rhs => rw [hw]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [bcH1, f, map_smul, LinearMap.smul_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, smul_eq_mul, map_mul]
  simp [mul_comm]

theorem s4_bcS_D (θ : Module.Dual F (H1 F n)) (t : S F n) :
    bcS F F' n (D F n θ t) = D F' n (bcDual F F' n θ) (bcS F F' n t) := by
  induction t using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, CliffordAlgebra.contractLeft_algebraMap, map_zero, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x w hx =>
    simp only [D] at hx ⊢
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, map_mul, hx]
    rw [show bcS F F' n (CliffordAlgebra.ι 0 w) = CliffordAlgebra.ι 0 (bcH1 F F' n w) from
      s4_bcS_ι F F' n w, CliffordAlgebra.contractLeft_ι_mul, s4_bcDual_bcH1, algebraMap_smul]

theorem s4_bcC_ι (v : V F n) :
    bcC F F' n (CliffordAlgebra.ι (Q F n) v) = CliffordAlgebra.ι (Q F' n) (bcV F F' n v) := by
  unfold bcC
  exact CliffordAlgebra.lift_ι_apply _ _ v

theorem s4_m_ι (v : V F n) (t : S F n) :
    m F n (CliffordAlgebra.ι (Q F n) v) t = ExteriorAlgebra.ι F v.2 * t + D F n v.1 t := by
  unfold m
  rw [CliffordAlgebra.lift_ι_apply]
  rfl

/-- The spin representation commutes with base change. -/
theorem s4_m_bcC (x : C F n) (t : S F n) :
    m F' n (bcC F F' n x) (bcS F F' n t) = bcS F F' n (m F n x t) := by
  induction x using CliffordAlgebra.induction generalizing t with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n), AlgHom.commutes,
      AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      algebraMap_smul]
  | ι v =>
    rw [s4_bcC_ι, s4_m_ι, s4_m_ι, map_add, map_mul, s4_bcS_D, s4_bcS_ι]
    rfl
  | mul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, hb, ha, map_mul,
      Module.End.mul_apply]
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, map_add,
      LinearMap.add_apply, map_add]

end SBC2

section STower
variable (F F' F'' : Type*) [Field F] [Field F'] [Field F''] [Algebra F F'] [Algebra F' F'']
  [Algebra F F''] [IsScalarTower F F' F''] (n : ℕ)

theorem s4_bcS_bcS (x : S F n) : bcS F' F'' n (bcS F F' n x) = bcS F F'' n x := by
  apply (basisS F'' n).repr.injective
  ext K
  simp only [s4_repr_bcS, ← IsScalarTower.algebraMap_apply]

end STower

theorem s4_bcS_mem_pow (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (n k : ℕ) (x : S F n)
    (hx : x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)))) ^ k) :
    bcS F F' n x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm F' (H1 F' n)))) ^ k := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n), pow_zero]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, show bcS F F' n (CliffordAlgebra.ι 0 v) = CliffordAlgebra.ι 0 (bcH1 F F' n v) from
      s4_bcS_ι F F' n v, pow_succ']
    exact Submodule.mul_mem_mul ⟨_, rfl⟩ hx

theorem s4_bcS_mem_Splus (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (n : ℕ) (x : S F n) (hx : x ∈ Splus F n) : bcS F F' n x ∈ Splus F' n := by
  unfold Splus CliffordAlgebra.evenOdd at hx ⊢
  exact Submodule.iSup_induction _ (motive := fun y => bcS F F' n y ∈ _) hx
    (fun j y hy => Submodule.mem_iSup_of_mem j (s4_bcS_mem_pow F F' n j y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

section ConjS
variable (n : ℕ)

local notation "cc" => (starRingAut : ℂ ≃+* ℂ)

theorem s4_repr_conjS (s : S ℂ n) (K : Finset (Fin (2 * n))) :
    (basisS ℂ n).repr (conjS cc n s) K = (starRingEnd ℂ) ((basisS ℂ n).repr s K) := by
  show (basisS ℂ n).repr (∑ K, cc ((basisS ℂ n).repr s K) • basisS ℂ n K) K = _
  rw [Module.Basis.repr_sum_self]
  rfl

theorem s4_conjS_eq_sum (s : S ℂ n) :
    conjS cc n s = ∑ K, (starRingEnd ℂ) ((basisS ℂ n).repr s K) • basisS ℂ n K := rfl

theorem s4_conjS_smul (z : ℂ) (s : S ℂ n) :
    conjS cc n (z • s) = (starRingEnd ℂ) z • conjS cc n s := by
  apply (basisS ℂ n).repr.injective
  ext K
  simp [s4_repr_conjS]

theorem s4_conjS_conjS (s : S ℂ n) : conjS cc n (conjS cc n s) = s := by
  apply (basisS ℂ n).repr.injective
  ext K
  simp [s4_repr_conjS]

theorem s4_conjS_bcS (t : S ℝ n) : conjS cc n (bcS ℝ ℂ n t) = bcS ℝ ℂ n t := by
  apply (basisS ℂ n).repr.injective
  ext K
  rw [s4_repr_conjS, s4_repr_bcS]
  simp

/-- A `ℂ`-linear map of `S_ℂ` taking real vectors to real vectors commutes with conjugation. -/
theorem s4_conjS_comm (T : S ℂ n →ₗ[ℂ] S ℂ n) (hT : ∀ t : S ℝ n, ∃ t', T (bcS ℝ ℂ n t) = bcS ℝ ℂ n t')
    (s : S ℂ n) : conjS cc n (T s) = T (conjS cc n s) := by
  have hb : ∀ K, conjS cc n (T (basisS ℂ n K)) = T (basisS ℂ n K) := by
    intro K
    obtain ⟨t', ht'⟩ := hT (basisS ℝ n K)
    rw [← s4_bcS_basisS ℝ ℂ n K, ht', s4_conjS_bcS]
  conv_lhs => rw [← (basisS ℂ n).sum_repr s]
  rw [map_sum, map_sum, s4_conjS_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s4_conjS_smul, hb, map_smul]

theorem s4_conjS_ι_mem (w : H1 ℂ n) :
    conjS cc n (ExteriorAlgebra.ι ℂ w) ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 ℂ n →ₗ[ℂ] _) := by
  have hw : w = ∑ i, w i • e ℂ n i := by ext j; simp [e, Pi.single_apply]
  have he : ∀ i, ExteriorAlgebra.ι ℂ (e ℂ n i) = bcS ℝ ℂ n (ExteriorAlgebra.ι ℝ (e ℝ n i)) := by
    intro i
    rw [s4_bcS_ι, s4_bcH1_e]
  rw [hw, map_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, s4_conjS_smul, he, s4_conjS_bcS, ← he]
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩

theorem s4_conjS_mem_pow (k : ℕ) (x : S ℂ n)
    (hx : x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 ℂ n)))) ^ k) :
    conjS cc n x ∈ (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 ℂ n)))) ^ k := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, s4_conjS_smul, map_one, pow_zero,
      ← Algebra.algebraMap_eq_smul_one]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨w, rfl⟩ := hm
    rw [map_mul, pow_succ']
    exact Submodule.mul_mem_mul (s4_conjS_ι_mem n w) hx

theorem s4_conjS_mem_Splus (x : S ℂ n) (hx : x ∈ Splus ℂ n) : conjS cc n x ∈ Splus ℂ n := by
  unfold Splus CliffordAlgebra.evenOdd at hx ⊢
  exact Submodule.iSup_induction _ (motive := fun y => conjS cc n y ∈ _) hx
    (fun j y hy => Submodule.mem_iSup_of_mem j (s4_conjS_mem_pow n j y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

end ConjS
/-- **Semi-Hodge class** (§4): a rational class `s ∈ S_ℚ` lying in `S^{0,0}_ℂ`. -/
def IsSemiHodge (I : Module.End ℝ (V ℝ n)) (s : S ℚ n) : Prop := bcS ℚ ℂ n s ∈ Spq n I 0

end Circle

/-! ## Helpers for the Hodge decomposition of `S⁺_ℂ` defined by the circle `𝕊_I` -/

section Graded

/-- The projection of `⋀• M` onto `⋀^k M`. -/
noncomputable abbrev s4_proj (F M : Type*) [Field F] [AddCommGroup M] [Module F M] (k : ℕ) :
    ExteriorAlgebra F M →ₗ[F] ExteriorAlgebra F M :=
  GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i M) k

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

theorem s4_proj_mem (k : ℕ) (x : ExteriorAlgebra F M) : s4_proj F M k x ∈ ⋀[F]^k M := by
  rw [GradedAlgebra.proj_apply]
  exact SetLike.coe_mem _

theorem s4_proj_of_mem {i : ℕ} (k : ℕ) {x : ExteriorAlgebra F M} (hx : x ∈ ⋀[F]^i M) :
    s4_proj F M k x = if i = k then x else 0 := by
  rw [GradedAlgebra.proj_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx h

theorem s4_proj_self {k : ℕ} {x : ExteriorAlgebra F M} (hx : x ∈ ⋀[F]^k M) :
    s4_proj F M k x = x := by
  rw [s4_proj_of_mem k hx, ite_eq_left rfl]

open Classical in
theorem s4_sum_proj (x : ExteriorAlgebra F M) :
    ∑ k ∈ DFinsupp.support (DirectSum.decompose (fun i : ℕ => ⋀[F]^i M) x), s4_proj F M k x = x := by
  simp only [GradedAlgebra.proj_apply]
  exact DirectSum.sum_support_decompose _ x

/-- An additive map preserving degrees commutes with the projections. -/
theorem s4_proj_comm {F' N : Type*} [Field F'] [AddCommGroup N] [Module F' N]
    (φ : ExteriorAlgebra F M →+ ExteriorAlgebra F' N)
    (hφ : ∀ i x, x ∈ ⋀[F]^i M → φ x ∈ ⋀[F']^i N) (k : ℕ) (x : ExteriorAlgebra F M) :
    s4_proj F' N k (φ x) = φ (s4_proj F M k x) := by
  classical
  conv_lhs => rw [← s4_sum_proj x, map_sum, map_sum]
  rw [Finset.sum_eq_single k]
  · exact s4_proj_self (hφ k _ (s4_proj_mem k x))
  · intro i _ hik
    rw [s4_proj_of_mem k (hφ i _ (s4_proj_mem i x)), ite_eq_right hik]
  · intro hk
    have : s4_proj F M k x = 0 := by
      rw [GradedAlgebra.proj_apply, DFinsupp.notMem_support_iff.mp hk]
      rfl
    rw [this, map_zero, map_zero]

/-- Degree detection: if `φ` preserves degrees and is injective, `φ x ∈ ⋀^k → x ∈ ⋀^k`. -/
theorem s4_mem_of_map_mem {F' N : Type*} [Field F'] [AddCommGroup N] [Module F' N]
    (φ : ExteriorAlgebra F M →+ ExteriorAlgebra F' N)
    (hφ : ∀ i x, x ∈ ⋀[F]^i M → φ x ∈ ⋀[F']^i N) (hinj : Function.Injective φ) (k : ℕ)
    (x : ExteriorAlgebra F M) (hx : φ x ∈ ⋀[F']^k N) : x ∈ ⋀[F]^k M := by
  classical
  have hcomp : ∀ i, i ≠ k → s4_proj F M i x = 0 := by
    intro i hik
    apply hinj
    rw [map_zero, ← s4_proj_comm φ hφ, s4_proj_of_mem i hx, ite_eq_right (Ne.symm hik)]
  rw [← s4_sum_proj x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases h : i = k
  · subst h; exact s4_proj_mem i x
  · rw [hcomp i h]; exact zero_mem _

end Graded

section Vacuum
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s4_L_apply (w : H1 F n) (x : S F n) : L F n w x = ExteriorAlgebra.ι F w * x := rfl

omit [CharZero F] in
theorem s4_D_apply (θ : Module.Dual F (H1 F n)) (x : S F n) :
    D F n θ x = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ x := rfl

/-- The number operator `N = Σᵢ L_{eᵢ} D_{fᵢ}` on `S = ⋀• H¹`. -/
noncomputable def s4_Nop : Module.End F (S F n) := ∑ i, L F n (e F n i) * D F n (f F n i)

omit [CharZero F] in
theorem s4_sum_e (w : H1 F n) : ∑ i, (f F n i) w • e F n i = w := by
  ext j
  simp [e, f, Pi.single_apply]

omit [CharZero F] in
theorem s4_Nop_ι_mul (w : H1 F n) (x : S F n) :
    s4_Nop F n (ExteriorAlgebra.ι F w * x) =
      ExteriorAlgebra.ι F w * x + ExteriorAlgebra.ι F w * s4_Nop F n x := by
  simp only [s4_Nop, LinearMap.sum_apply, Module.End.mul_apply, s4_L_apply, s4_D_apply,
    CliffordAlgebra.contractLeft_ι_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ i, ExteriorAlgebra.ι F (e F n i) * ((f F n i) w • x) =
      ExteriorAlgebra.ι F w * x := by
    simp only [mul_smul_comm, ← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum,
      s4_sum_e]
  have h2 : ∀ i, ExteriorAlgebra.ι F (e F n i) * (ExteriorAlgebra.ι F w *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) (f F n i) x) =
      -(ExteriorAlgebra.ι F w * (ExteriorAlgebra.ι F (e F n i) *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) (f F n i) x)) := by
    intro i
    rw [← mul_assoc, ← mul_assoc, CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (QuadraticMap.IsOrtho.all _ _), neg_mul]
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_neg_distrib, sub_neg_eq_add,
    Finset.mul_sum]

omit [CharZero F] in
theorem s4_Nop_algebraMap (r : F) : s4_Nop F n (algebraMap F (S F n) r) = 0 := by
  simp [s4_Nop, s4_D_apply, CliffordAlgebra.contractLeft_algebraMap]

theorem s4_Nop_mem' (k : ℕ) (x : S F n)
    (hx : x ∈ (LinearMap.range (ExteriorAlgebra.ι F : H1 F n →ₗ[F] S F n)) ^ k) :
    s4_Nop F n x = (k : F) • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [s4_Nop_algebraMap]
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨w, rfl⟩ := hm
    rw [s4_Nop_ι_mul, ih, mul_smul_comm, Nat.cast_succ, add_smul, one_smul, add_comm]

theorem s4_Nop_mem (k : ℕ) (x : S F n) (hx : x ∈ ⋀[F]^k (H1 F n)) :
    s4_Nop F n x = (k : F) • x :=
  s4_Nop_mem' F n k x hx

/-- The common kernel of the contractions is `⋀⁰ = F`. -/
theorem s4_exists_algebraMap_of_contract (s : S F n) (hs : ∀ θ, D F n θ s = 0) :
    ∃ c : F, s = algebraMap F (S F n) c := by
  classical
  have hN : s4_Nop F n s = 0 := by
    simp [s4_Nop, hs]
  set φ : S F n →+ S F n := (s4_Nop F n).toAddMonoidHom
  have hφ : ∀ i x, x ∈ ⋀[F]^i (H1 F n) → φ x ∈ ⋀[F]^i (H1 F n) := fun i x hx => by
    show s4_Nop F n x ∈ _
    rw [s4_Nop_mem F n i x hx]
    exact Submodule.smul_mem _ _ hx
  have hk : ∀ k, k ≠ 0 → s4_proj F (H1 F n) k s = 0 := by
    intro k hk0
    have h1 := s4_proj_comm φ hφ k s
    have h2 : φ (s4_proj F (H1 F n) k s) = (k : F) • s4_proj F (H1 F n) k s :=
      s4_Nop_mem F n k _ (s4_proj_mem k s)
    have h3 : φ s = 0 := hN
    rw [h3, map_zero, h2] at h1
    have hkF : (k : F) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    exact (smul_eq_zero.mp h1.symm).resolve_left hkF
  have hs0 : s ∈ ⋀[F]^0 (H1 F n) := by
    rw [← s4_sum_proj s]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : i = 0
    · subst h; exact s4_proj_mem 0 s
    · rw [hk i h]; exact zero_mem _
  have hs0' : s ∈ (LinearMap.range (ExteriorAlgebra.ι F : H1 F n →ₗ[F] S F n)) ^ 0 := hs0
  rw [pow_zero, Submodule.mem_one] at hs0'
  obtain ⟨c, hc⟩ := hs0'
  exact ⟨c, hc.symm⟩

/-- An operator of `S` commuting with all `L_w` and `D_θ` is a scalar. -/
theorem s4_eq_smul_one_of_comm (A : Module.End F (S F n))
    (hL : ∀ w, A * L F n w = L F n w * A) (hD : ∀ θ, A * D F n θ = D F n θ * A) :
    ∃ c : F, A = c • 1 := by
  obtain ⟨c, hc⟩ := s4_exists_algebraMap_of_contract F n (A 1) fun θ => by
    have := congrArg (fun T => T 1) (hD θ)
    simp only [Module.End.mul_apply] at this
    rw [← this, s4_D_apply, CliffordAlgebra.contractLeft_one, map_zero]
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  rw [LinearMap.smul_apply, Module.End.one_apply]
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hc, Algebra.algebraMap_eq_smul_one, smul_smul,
      smul_smul, mul_comm r c]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | ι_mul x w hx =>
    have := congrArg (fun T => T x) (hL w)
    simp only [Module.End.mul_apply, s4_L_apply] at this
    rw [this, hx, mul_smul_comm]

/-- The grading involution `ε` of `S`. -/
noncomputable abbrev s4_eps : S F n →ₐ[F] S F n :=
  CliffordAlgebra.involute (Q := (0 : QuadraticForm F (H1 F n)))

omit [CharZero F] in
theorem s4_eps_L (w : H1 F n) (x : S F n) :
    s4_eps F n (L F n w x) = -L F n w (s4_eps F n x) := by
  rw [s4_L_apply, s4_L_apply, map_mul, CliffordAlgebra.involute_ι, neg_mul]

omit [CharZero F] in
theorem s4_eps_D (θ : Module.Dual F (H1 F n)) (x : S F n) :
    s4_eps F n (D F n θ x) = -D F n θ (s4_eps F n x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [s4_D_apply, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]
  | ι_mul x w hx =>
    have e1 : ∀ y : S F n, D F n θ (ExteriorAlgebra.ι F w * y) =
        θ w • y - ExteriorAlgebra.ι F w * D F n θ y := fun y =>
      CliffordAlgebra.contractLeft_ι_mul _ _ _
    have e2 : ∀ y : S F n, s4_eps F n (ExteriorAlgebra.ι F w * y) =
        -(ExteriorAlgebra.ι F w * s4_eps F n y) := fun y => by
      rw [map_mul, CliffordAlgebra.involute_ι, neg_mul]
    rw [e1, map_sub, map_smul, e2, hx, e2, map_neg, e1, mul_neg, neg_neg]
    abel

omit [CharZero F] in
theorem s4_eps_eps (x : S F n) : s4_eps F n (s4_eps F n x) = x :=
  CliffordAlgebra.involute_involute x

/-- An operator of `S` anticommuting with all `L_w` and `D_θ` is a multiple of the grading
involution `ε`. -/
theorem s4_eq_smul_eps_of_anticomm (B : Module.End F (S F n))
    (hL : ∀ w x, B (L F n w x) = -L F n w (B x)) (hD : ∀ θ x, B (D F n θ x) = -D F n θ (B x)) :
    ∃ c : F, ∀ x, B x = c • s4_eps F n x := by
  set A : Module.End F (S F n) := (s4_eps F n).toLinearMap * B
  obtain ⟨c, hc⟩ := s4_eq_smul_one_of_comm F n A
    (fun w => LinearMap.ext fun x => by
      simp only [A, Module.End.mul_apply, AlgHom.toLinearMap_apply, hL, map_neg, s4_eps_L,
        neg_neg])
    (fun θ => LinearMap.ext fun x => by
      simp only [A, Module.End.mul_apply, AlgHom.toLinearMap_apply, hD, map_neg, s4_eps_D,
        neg_neg])
  refine ⟨c, fun x => ?_⟩
  have := congrArg (fun T => T x) hc
  simp only [A, Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
    Module.End.one_apply] at this
  rw [← s4_eps_eps F n (B x), this, map_smul]

end Vacuum

section Weights
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- `R_l(φ) = Π_{T ∈ l} (cos φ - sin φ T)`. -/
noncomputable def s4_Rop (l : List (Module.End ℂ M)) (φ : ℝ) : Module.End ℂ M :=
  (l.map fun T => (Real.cos φ : ℂ) • (1 : Module.End ℂ M) - (Real.sin φ : ℂ) • T).prod

/-- The weight space `{s : R_l(φ) s = e^{-ikφ} s for all φ}`. -/
noncomputable def s4_Wt (l : List (Module.End ℂ M)) (k : ℤ) : Submodule ℂ M :=
  ⨅ φ : ℝ, Module.End.eigenspace (s4_Rop l φ) (Complex.exp (-((k : ℂ) * φ) * Complex.I))

theorem s4_mem_Wt (l : List (Module.End ℂ M)) (k : ℤ) (s : M) :
    s ∈ s4_Wt l k ↔ ∀ φ : ℝ, s4_Rop l φ s = Complex.exp (-((k : ℂ) * φ) * Complex.I) • s := by
  simp [s4_Wt, Submodule.mem_iInf]

theorem s4_Rop_cons (T : Module.End ℂ M) (l : List (Module.End ℂ M)) (φ : ℝ) :
    s4_Rop (T :: l) φ =
      ((Real.cos φ : ℂ) • (1 : Module.End ℂ M) - (Real.sin φ : ℂ) • T) * s4_Rop l φ := by
  simp [s4_Rop]

theorem s4_cos_sub_sin_I (φ : ℝ) :
    (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I = Complex.exp (-(φ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

theorem s4_cos_add_sin_I (φ : ℝ) :
    (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I = Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem s4_Rop_commute (T : Module.End ℂ M) (l : List (Module.End ℂ M))
    (hT : ∀ T' ∈ l, Commute T T') (φ : ℝ) : Commute T (s4_Rop l φ) := by
  apply Commute.list_prod_right
  intro a ha
  obtain ⟨T', hT', rfl⟩ := List.mem_map.mp ha
  exact ((Commute.one_right T).smul_right _).sub_right ((hT T' hT').smul_right _)

/-- Weight decomposition for a commuting family of complex structures `T` (`T² = -1`), on an
invariant subspace. -/
theorem s4_weight_decomp (l : List (Module.End ℂ M)) (hsq : ∀ T ∈ l, T * T = -1)
    (hcomm : l.Pairwise Commute) (S' : Submodule ℂ M) (hS' : ∀ T ∈ l, ∀ x ∈ S', T x ∈ S') :
    S' ≤ ⨆ k : ℤ, (s4_Wt l k ⊓ S') := by
  induction l with
  | nil =>
    intro x hx
    refine Submodule.mem_iSup_of_mem 0
      (Submodule.mem_inf.mpr ⟨(s4_mem_Wt _ _ _).mpr fun φ => ?_, hx⟩)
    simp [s4_Rop]
  | cons T l ih =>
    have hsq' : ∀ T' ∈ l, T' * T' = -1 := fun T' h => hsq T' (List.mem_cons_of_mem _ h)
    have hcomm' : l.Pairwise Commute := (List.pairwise_cons.mp hcomm).2
    have hTl : ∀ T' ∈ l, Commute T T' := (List.pairwise_cons.mp hcomm).1
    have hS'l : ∀ T' ∈ l, ∀ x ∈ S', T' x ∈ S' := fun T' h => hS' T' (List.mem_cons_of_mem _ h)
    have hTS : ∀ x ∈ S', T x ∈ S' := hS' T List.mem_cons_self
    have hTT : ∀ y, T (T y) = -y := fun y => by
      have := congrArg (fun A : Module.End ℂ M => A y) (hsq T List.mem_cons_self)
      simpa using this
    intro x hx
    have hx' := ih hsq' hcomm' hS'l hx
    refine Submodule.iSup_induction _
      (motive := fun z => z ∈ ⨆ k : ℤ, (s4_Wt (T :: l) k ⊓ S')) hx' ?_ (zero_mem _)
      (fun a b ha hb => add_mem ha hb)
    intro k y hy
    obtain ⟨hyW, hyS⟩ := Submodule.mem_inf.mp hy
    rw [s4_mem_Wt] at hyW
    set yp := (1 / 2 : ℂ) • (y - Complex.I • T y) with hyp
    set ym := (1 / 2 : ℂ) • (y + Complex.I • T y) with hym
    have hy_eq : y = yp + ym := by rw [hyp, hym]; module
    have hTyp : T yp = Complex.I • yp := by
      rw [hyp, map_smul, map_sub, map_smul, hTT, smul_comm Complex.I (1 / 2 : ℂ)]
      congr 1
      simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add]
      abel
    have hTym : T ym = (-Complex.I) • ym := by
      rw [hym, map_smul, map_add, map_smul, hTT, smul_comm (-Complex.I) (1 / 2 : ℂ)]
      congr 1
      simp only [smul_add, smul_neg, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
        neg_smul]
      abel
    have hRcomm : ∀ φ z, s4_Rop l φ (T z) = T (s4_Rop l φ z) := fun φ z => by
      have := congrArg (fun A : Module.End ℂ M => A z) (s4_Rop_commute T l hTl φ).eq
      simpa using this.symm
    have hRyp : ∀ φ, s4_Rop l φ yp = Complex.exp (-((k : ℂ) * φ) * Complex.I) • yp := by
      intro φ
      rw [hyp, map_smul, map_sub, map_smul, hRcomm, hyW, map_smul]
      module
    have hRym : ∀ φ, s4_Rop l φ ym = Complex.exp (-((k : ℂ) * φ) * Complex.I) • ym := by
      intro φ
      rw [hym, map_smul, map_add, map_smul, hRcomm, hyW, map_smul]
      module
    have hyp' : yp ∈ s4_Wt (T :: l) (k + 1) ⊓ S' := by
      refine Submodule.mem_inf.mpr ⟨(s4_mem_Wt _ _ _).mpr fun φ => ?_, ?_⟩
      · rw [s4_Rop_cons, Module.End.mul_apply, hRyp, map_smul, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, hTyp,
          smul_smul (Real.sin φ : ℂ), ← sub_smul, smul_smul]
        congr 1
        rw [show (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I =
          Complex.exp (-(φ : ℂ) * Complex.I) from s4_cos_sub_sin_I φ, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hyS (Submodule.smul_mem _ _ (hTS y hyS)))
    have hym' : ym ∈ s4_Wt (T :: l) (k - 1) ⊓ S' := by
      refine Submodule.mem_inf.mpr ⟨(s4_mem_Wt _ _ _).mpr fun φ => ?_, ?_⟩
      · rw [s4_Rop_cons, Module.End.mul_apply, hRym, map_smul, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, hTym,
          smul_smul (Real.sin φ : ℂ), ← sub_smul, smul_smul]
        congr 1
        rw [show (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * -Complex.I =
          Complex.exp ((φ : ℂ) * Complex.I) by rw [← s4_cos_add_sin_I]; ring, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      · exact Submodule.smul_mem _ _ (Submodule.add_mem _ hyS (Submodule.smul_mem _ _ (hTS y hyS)))
    rw [hy_eq]
    exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem (k + 1) hyp')
      (Submodule.mem_iSup_of_mem (k - 1) hym')

end Weights

section Plane
variable {n : ℕ} (x y : V ℝ n)

/-- `u = Q(x)⁻¹ x y ∈ C(V_ℝ)` for an orthogonal pair `x, y` with `Q(x) = Q(y) ≠ 0`; `u² = -1`. -/
noncomputable def s4_uop : C ℝ n :=
  (Q ℝ n x)⁻¹ • (CliffordAlgebra.ι (Q ℝ n) x * CliffordAlgebra.ι (Q ℝ n) y)

/-- `g(θ) = cos(θ/2) - sin(θ/2) u`, a lift to `Spin(V_ℝ)` of the rotation by `θ` in the plane
`span(x, y)`. -/
noncomputable def s4_gop (θ : ℝ) : C ℝ n :=
  Real.cos (θ / 2) • (1 : C ℝ n) - Real.sin (θ / 2) • s4_uop x y

variable {x y} (hq : Q ℝ n x ≠ 0) (hQy : Q ℝ n y = Q ℝ n x) (hxy : (Q ℝ n).IsOrtho x y)
include hq hQy hxy

omit hq hxy in
theorem s4_ι_sq_y : CliffordAlgebra.ι (Q ℝ n) y * CliffordAlgebra.ι (Q ℝ n) y =
    Q ℝ n x • (1 : C ℝ n) := by
  rw [CliffordAlgebra.ι_sq_scalar, hQy, Algebra.algebraMap_eq_smul_one]

omit hq hQy hxy in
theorem s4_ι_sq_x : CliffordAlgebra.ι (Q ℝ n) x * CliffordAlgebra.ι (Q ℝ n) x =
    Q ℝ n x • (1 : C ℝ n) := by
  rw [CliffordAlgebra.ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

omit hq hQy in
theorem s4_ι_yx : CliffordAlgebra.ι (Q ℝ n) y * CliffordAlgebra.ι (Q ℝ n) x =
    -(CliffordAlgebra.ι (Q ℝ n) x * CliffordAlgebra.ι (Q ℝ n) y) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hxy.symm

omit hQy hxy in
theorem s4_ι_x_u : CliffordAlgebra.ι (Q ℝ n) x * s4_uop x y = CliffordAlgebra.ι (Q ℝ n) y := by
  rw [s4_uop, mul_smul_comm, ← mul_assoc, s4_ι_sq_x, smul_mul_assoc, one_mul, smul_smul,
    inv_mul_cancel₀ hq, one_smul]

omit hQy in
theorem s4_u_x : s4_uop x y * CliffordAlgebra.ι (Q ℝ n) x = -CliffordAlgebra.ι (Q ℝ n) y := by
  rw [s4_uop, smul_mul_assoc, mul_assoc, s4_ι_yx hxy, mul_neg, ← mul_assoc, s4_ι_sq_x,
    smul_mul_assoc, one_mul, smul_neg, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem s4_ι_y_u : CliffordAlgebra.ι (Q ℝ n) y * s4_uop x y = -CliffordAlgebra.ι (Q ℝ n) x := by
  rw [s4_uop, mul_smul_comm, ← mul_assoc, s4_ι_yx hxy, neg_mul, mul_assoc,
    s4_ι_sq_y hQy, mul_smul_comm, mul_one, smul_neg, smul_smul, inv_mul_cancel₀ hq, one_smul]

omit hxy in
theorem s4_u_y : s4_uop x y * CliffordAlgebra.ι (Q ℝ n) y = CliffordAlgebra.ι (Q ℝ n) x := by
  rw [s4_uop, smul_mul_assoc, mul_assoc, s4_ι_sq_y hQy, mul_smul_comm, mul_one, smul_smul,
    inv_mul_cancel₀ hq, one_smul]

theorem s4_u_u : s4_uop x y * s4_uop x y = -1 := by
  calc s4_uop x y * s4_uop x y = (Q ℝ n x)⁻¹ • (CliffordAlgebra.ι (Q ℝ n) x *
      CliffordAlgebra.ι (Q ℝ n) y) * s4_uop x y := rfl
    _ = -1 := by
      rw [smul_mul_assoc, mul_assoc, s4_ι_y_u hq hQy hxy, mul_neg, s4_ι_sq_x, smul_neg,
        smul_smul, inv_mul_cancel₀ hq, one_smul]

omit hq hQy in
theorem s4_star_u : star (s4_uop x y) = -s4_uop x y := by
  rw [s4_uop, CliffordAlgebra.star_smul, star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι,
    neg_mul_neg, s4_ι_yx hxy, smul_neg]

omit hq hQy hxy in
theorem s4_ι_v_u (v : V ℝ n) (hxv : (Q ℝ n).IsOrtho x v) (hyv : (Q ℝ n).IsOrtho y v) :
    CliffordAlgebra.ι (Q ℝ n) v * s4_uop x y = s4_uop x y * CliffordAlgebra.ι (Q ℝ n) v := by
  rw [s4_uop, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hxv.symm, neg_mul, mul_assoc,
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hyv.symm, mul_neg, neg_neg, mul_assoc]

omit hq hQy in
theorem s4_star_gop (θ : ℝ) :
    star (s4_gop x y θ) = Real.cos (θ / 2) • (1 : C ℝ n) + Real.sin (θ / 2) • s4_uop x y := by
  rw [s4_gop, star_sub, CliffordAlgebra.star_smul, CliffordAlgebra.star_smul, star_one,
    s4_star_u hxy, smul_neg, sub_neg_eq_add]

theorem s4_gop_conj_x (θ : ℝ) :
    s4_gop x y θ * CliffordAlgebra.ι (Q ℝ n) x * star (s4_gop x y θ) =
      Real.cos θ • CliffordAlgebra.ι (Q ℝ n) x + Real.sin θ • CliffordAlgebra.ι (Q ℝ n) y := by
  rw [s4_star_gop hxy, s4_gop]
  have h1 := s4_ι_x_u (y := y) hq
  have h2 := s4_u_x hq hxy
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2]
  rw [neg_mul, s4_ι_y_u hq hQy hxy]
  have hc2 : Real.cos θ = Real.cos (θ / 2) * Real.cos (θ / 2) -
      Real.sin (θ / 2) * Real.sin (θ / 2) := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hs2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [show θ = 2 * (θ / 2) by ring, Real.sin_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
  rw [hc2, hs2]
  module

theorem s4_gop_conj_y (θ : ℝ) :
    s4_gop x y θ * CliffordAlgebra.ι (Q ℝ n) y * star (s4_gop x y θ) =
      Real.cos θ • CliffordAlgebra.ι (Q ℝ n) y - Real.sin θ • CliffordAlgebra.ι (Q ℝ n) x := by
  rw [s4_star_gop hxy, s4_gop]
  have h1 := s4_ι_y_u hq hQy hxy
  have h2 := s4_u_y hq hQy
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2]
  rw [s4_ι_x_u hq]
  have hc2 : Real.cos θ = Real.cos (θ / 2) * Real.cos (θ / 2) -
      Real.sin (θ / 2) * Real.sin (θ / 2) := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hs2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [show θ = 2 * (θ / 2) by ring, Real.sin_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
  rw [hc2, hs2]
  module

theorem s4_gop_conj_v (θ : ℝ) (v : V ℝ n) (hxv : (Q ℝ n).IsOrtho x v)
    (hyv : (Q ℝ n).IsOrtho y v) :
    s4_gop x y θ * CliffordAlgebra.ι (Q ℝ n) v * star (s4_gop x y θ) =
      CliffordAlgebra.ι (Q ℝ n) v := by
  rw [s4_star_gop hxy, s4_gop, mul_assoc]
  have hc : CliffordAlgebra.ι (Q ℝ n) v * (Real.cos (θ / 2) • (1 : C ℝ n) +
      Real.sin (θ / 2) • s4_uop x y) = (Real.cos (θ / 2) • (1 : C ℝ n) +
      Real.sin (θ / 2) • s4_uop x y) * CliffordAlgebra.ι (Q ℝ n) v := by
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one,
      one_mul, s4_ι_v_u v hxv hyv]
  rw [hc, ← mul_assoc]
  have hgg : (Real.cos (θ / 2) • (1 : C ℝ n) - Real.sin (θ / 2) • s4_uop x y) *
      (Real.cos (θ / 2) • (1 : C ℝ n) + Real.sin (θ / 2) • s4_uop x y) = 1 := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      s4_u_u hq hQy hxy]
    have h1 : Real.cos (θ / 2) * Real.cos (θ / 2) + Real.sin (θ / 2) * Real.sin (θ / 2) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    calc _ = (Real.cos (θ / 2) * Real.cos (θ / 2) + Real.sin (θ / 2) * Real.sin (θ / 2)) •
        (1 : C ℝ n) := by module
      _ = 1 := by rw [h1, one_smul]
  rw [hgg, one_mul]

omit hQy hxy in
theorem s4_gop_eq (θ : ℝ) : s4_gop x y θ =
    CliffordAlgebra.ι (Q ℝ n) ((Q ℝ n x)⁻¹ • x) *
      CliffordAlgebra.ι (Q ℝ n) (Real.cos (θ / 2) • x - Real.sin (θ / 2) • y) := by
  rw [s4_gop, s4_uop, map_smul, map_sub, map_smul, map_smul, smul_mul_assoc, mul_sub,
    mul_smul_comm, mul_smul_comm, s4_ι_sq_x]
  match_scalars <;> (field_simp; try ring)

theorem s4_gop_mem (θ : ℝ) : s4_gop x y θ ∈ spinGroup (Q ℝ n) := by
  rw [s4_gop_eq hq]
  apply CliffordAlgebra.ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one
  have h1 : Q ℝ n ((Q ℝ n x)⁻¹ • x) = (Q ℝ n x)⁻¹ := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    field_simp
  have h2 : Q ℝ n (Real.cos (θ / 2) • x - Real.sin (θ / 2) • y) = Q ℝ n x := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add (Q ℝ n), QuadraticMap.map_smul,
      QuadraticMap.map_smul, hQy, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      hxy.polar_eq_zero]
    simp only [smul_eq_mul, mul_zero, add_zero]
    have := Real.sin_sq_add_cos_sq (θ / 2)
    linear_combination (Q ℝ n x) * this
  rw [h1, h2, inv_mul_cancel₀ hq]

end Plane

section Family
variable {n : ℕ} (I : Module.End ℝ (V ℝ n))

/-- An isometric complex structure `I` with an orthogonal family `x` adapted to it: the planes
`span(xⱼ, I xⱼ)` are pairwise orthogonal and `(xⱼ, xⱼ)_V ≠ 0`. -/
structure s4_Adapted {N : ℕ} (x : Fin N → V ℝ n) : Prop where
  iso : ∀ a b, pairing ℝ n (I a) (I b) = pairing ℝ n a b
  sq : ∀ a, I (I a) = -a
  orth : ∀ j k, j ≠ k → pairing ℝ n (x j) (x k) = 0 ∧ pairing ℝ n (x j) (I (x k)) = 0
  ne : ∀ j, pairing ℝ n (x j) (x j) ≠ 0

variable {I}

theorem s4_pairing_eq_two_Q (v : V ℝ n) : pairing ℝ n v v = 2 * Q ℝ n v := by
  rw [show pairing ℝ n v v = QuadraticMap.polar (Q ℝ n) v v from rfl, QuadraticMap.polar_self,
    nsmul_eq_mul, Nat.cast_ofNat]

theorem s4_pairing_symm_R (a b : V ℝ n) : pairing ℝ n a b = pairing ℝ n b a :=
  QuadraticMap.polar_comm _ a b

namespace s4_Adapted
variable {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x)
include h

theorem hq (j : Fin N) : Q ℝ n (x j) ≠ 0 := fun h0 => h.ne j (by
  rw [s4_pairing_eq_two_Q, h0, mul_zero])

theorem hQy (j : Fin N) : Q ℝ n (I (x j)) = Q ℝ n (x j) := by
  have := h.iso (x j) (x j)
  rw [s4_pairing_eq_two_Q, s4_pairing_eq_two_Q] at this
  linarith

theorem pairing_I_self (a : V ℝ n) : pairing ℝ n a (I a) = 0 := by
  have h1 := h.iso (I a) a
  rw [h.sq, map_neg, LinearMap.neg_apply, s4_pairing_symm_R (I a) a] at h1
  linarith

theorem hxy (j : Fin N) : (Q ℝ n).IsOrtho (x j) (I (x j)) :=
  QuadraticMap.isOrtho_polarBilin.mp (h.pairing_I_self (x j))

end s4_Adapted

theorem s4_Adapted.tail {N : ℕ} {x : Fin (N + 1) → V ℝ n} (h : s4_Adapted I x) :
    s4_Adapted I (fun j : Fin N => x j.succ) :=
  ⟨h.iso, h.sq, fun j k hjk => h.orth j.succ k.succ (fun e => hjk (Fin.succ_injective _ e)),
    fun j => h.ne j.succ⟩

/-- The spin lift of the rotation by `θ` in the plane `span(xⱼ, I xⱼ)`. -/
noncomputable def s4_gfam {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (j : Fin N) (θ : ℝ) :
    Spin ℝ n :=
  ⟨s4_gop (x j) (I (x j)) θ, s4_gop_mem (h.hq j) (h.hQy j) (h.hxy j) θ⟩

/-- `G(θ) = Πⱼ gⱼ(θ)`. -/
noncomputable def s4_Gfam {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (θ : ℝ) : Spin ℝ n :=
  (List.ofFn fun j => s4_gfam h j θ).prod

theorem s4_rotI_apply (θ : ℝ) (v : V ℝ n) : rotI n I θ v = Real.cos θ • v + Real.sin θ • I v := by
  simp [rotI]

section Plane
variable {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x)
include h

theorem s4_rho_gfam_x (j : Fin N) (θ : ℝ) : rho ℝ n (s4_gfam h j θ) (x j) = rotI n I θ (x j) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  apply CliffordAlgebra.ι_injective (Q ℝ n)
  rw [ι_rho, s4_rotI_apply, map_add, map_smul, map_smul]
  exact s4_gop_conj_x (h.hq j) (h.hQy j) (h.hxy j) θ

theorem s4_rho_gfam_Ix (j : Fin N) (θ : ℝ) :
    rho ℝ n (s4_gfam h j θ) (I (x j)) = rotI n I θ (I (x j)) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  apply CliffordAlgebra.ι_injective (Q ℝ n)
  rw [ι_rho, s4_rotI_apply, h.sq, map_add, map_smul, map_smul, map_neg, smul_neg,
    ← sub_eq_add_neg]
  exact s4_gop_conj_y (h.hq j) (h.hQy j) (h.hxy j) θ

theorem s4_rho_gfam_perp (j : Fin N) (θ : ℝ) (v : V ℝ n) (h1 : pairing ℝ n (x j) v = 0)
    (h2 : pairing ℝ n (I (x j)) v = 0) : rho ℝ n (s4_gfam h j θ) v = v := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  apply CliffordAlgebra.ι_injective (Q ℝ n)
  rw [ι_rho]
  exact s4_gop_conj_v (h.hq j) (h.hQy j) (h.hxy j) θ v (QuadraticMap.isOrtho_polarBilin.mp h1)
    (QuadraticMap.isOrtho_polarBilin.mp h2)

end Plane

theorem s4_Gfam_succ {N : ℕ} {x : Fin (N + 1) → V ℝ n} (h : s4_Adapted I x) (θ : ℝ) :
    s4_Gfam h θ = s4_gfam h 0 θ * s4_Gfam h.tail θ := by
  rw [s4_Gfam, List.ofFn_succ, List.prod_cons]
  rfl

/-- `ρ(G(θ))` is the rotation `I_θ` on the planes and the identity on their orthogonal. -/
theorem s4_rho_Gfam : ∀ {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (θ : ℝ),
    (∀ v, (∀ j, pairing ℝ n (x j) v = 0 ∧ pairing ℝ n (I (x j)) v = 0) →
      rho ℝ n (s4_Gfam h θ) v = v) ∧
    (∀ j, rho ℝ n (s4_Gfam h θ) (x j) = rotI n I θ (x j) ∧
      rho ℝ n (s4_Gfam h θ) (I (x j)) = rotI n I θ (I (x j)))
  | 0, x, h, θ => by
    refine ⟨fun v _ => ?_, fun j => j.elim0⟩
    have : s4_Gfam h θ = 1 := by simp [s4_Gfam]
    rw [this]
    exact congrArg (fun e : V ℝ n ≃ₗ[ℝ] V ℝ n => e v) (CliffordAlgebra.spinVectorAction_one _)
  | N + 1, x, h, θ => by
    obtain ⟨ih1, ih2⟩ := s4_rho_Gfam h.tail θ
    have hmul : ∀ v, rho ℝ n (s4_Gfam h θ) v =
        rho ℝ n (s4_gfam h 0 θ) (rho ℝ n (s4_Gfam h.tail θ) v) := fun v => by
      rw [s4_Gfam_succ]
      show CliffordAlgebra.spinVectorAction (Q ℝ n) _ v = _
      rw [CliffordAlgebra.spinVectorAction_mul, LinearEquiv.mul_apply]
      rfl
    have horth : ∀ j k, j ≠ k → pairing ℝ n (x j) (x k) = 0 ∧ pairing ℝ n (I (x j)) (x k) = 0 ∧
        pairing ℝ n (x j) (I (x k)) = 0 ∧ pairing ℝ n (I (x j)) (I (x k)) = 0 := by
      intro j k hjk
      refine ⟨(h.orth j k hjk).1, ?_, (h.orth j k hjk).2, ?_⟩
      · rw [s4_pairing_symm_R]; exact (h.orth k j (Ne.symm hjk)).2
      · rw [h.iso]; exact (h.orth j k hjk).1
    have hperp0 : ∀ v, pairing ℝ n (x 0) v = 0 → pairing ℝ n (I (x 0)) v = 0 →
        rho ℝ n (s4_gfam h 0 θ) v = v := fun v h1 h2 => s4_rho_gfam_perp h 0 θ v h1 h2
    refine ⟨fun v hv => ?_, fun j => ?_⟩
    · rw [hmul, ih1 v (fun j => hv j.succ), hperp0 v (hv 0).1 (hv 0).2]
    · refine Fin.cases ?_ (fun k => ?_) j
      · have hx0 : rho ℝ n (s4_Gfam h.tail θ) (x 0) = x 0 := ih1 _ fun k =>
          ⟨(horth k.succ 0 (Fin.succ_ne_zero k)).1, (horth k.succ 0 (Fin.succ_ne_zero k)).2.1⟩
        have hIx0 : rho ℝ n (s4_Gfam h.tail θ) (I (x 0)) = I (x 0) := ih1 _ fun k =>
          ⟨(horth k.succ 0 (Fin.succ_ne_zero k)).2.2.1,
            (horth k.succ 0 (Fin.succ_ne_zero k)).2.2.2⟩
        exact ⟨by rw [hmul, hx0, s4_rho_gfam_x], by rw [hmul, hIx0, s4_rho_gfam_Ix]⟩
      · obtain ⟨e1, e2⟩ := ih2 k
        have hne : (0 : Fin (N + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
        have hfix : ∀ w, (w = x k.succ ∨ w = I (x k.succ)) →
            rho ℝ n (s4_gfam h 0 θ) w = w := by
          rintro w (rfl | rfl)
          · exact hperp0 _ (horth 0 k.succ hne).1 (horth 0 k.succ hne).2.1
          · exact hperp0 _ (horth 0 k.succ hne).2.2.1 (horth 0 k.succ hne).2.2.2
        refine ⟨?_, ?_⟩
        · rw [hmul]
          show rho ℝ n (s4_gfam h 0 θ) (rho ℝ n (s4_Gfam h.tail θ) (x k.succ)) = _
          rw [e1, s4_rotI_apply, map_add, map_smul, map_smul, hfix _ (Or.inl rfl),
            hfix _ (Or.inr rfl)]
        · rw [hmul]
          show rho ℝ n (s4_gfam h 0 θ) (rho ℝ n (s4_Gfam h.tail θ) (I (x k.succ))) = _
          rw [e2, s4_rotI_apply, h.sq, map_add, map_smul, map_smul, map_neg,
            hfix _ (Or.inl rfl), hfix _ (Or.inr rfl)]

end Family

section Family2
variable {n : ℕ} {I : Module.End ℝ (V ℝ n)}

/-- For a full adapted family, `ρ(G(θ)) = I_θ`. -/
theorem s4_rho_Gfam_eq (hn : 0 < n) {x : Fin (2 * n) → V ℝ n} (h : s4_Adapted I x) (θ : ℝ) :
    (rho ℝ n (s4_Gfam h θ) : V ℝ n →ₗ[ℝ] V ℝ n) = rotI n I θ := by
  have : Nonempty (Fin (2 * n) ⊕ Fin (2 * n)) := ⟨Sum.inl ⟨0, by omega⟩⟩
  set u : Fin (2 * n) ⊕ Fin (2 * n) → V ℝ n := Sum.elim x (fun j => I (x j)) with hu
  have horthR : (pairing ℝ n).iIsOrtho u := by
    intro k l hkl
    show pairing ℝ n (u k) (u l) = 0
    rcases k with j | j <;> rcases l with k | k
    · exact (h.orth j k fun e => hkl (by rw [e])).1
    · by_cases hjk : j = k
      · subst hjk; exact h.pairing_I_self (x j)
      · exact (h.orth j k hjk).2
    · show pairing ℝ n (I (x j)) (x k) = 0
      rw [s4_pairing_symm_R]
      by_cases hjk : k = j
      · subst hjk; exact h.pairing_I_self (x k)
      · exact (h.orth k j hjk).2
    · show pairing ℝ n (I (x j)) (I (x k)) = 0
      rw [h.iso]
      exact (h.orth j k fun e => hkl (by rw [e])).1
  have hdiag : ∀ k, pairing ℝ n (u k) (u k) ≠ 0 := by
    rintro (j | j)
    · exact h.ne j
    · show pairing ℝ n (I (x j)) (I (x j)) ≠ 0
      rw [h.iso]; exact h.ne j
  have hli : LinearIndependent ℝ u := LinearMap.BilinForm.linearIndependent_of_iIsOrtho horthR hdiag
  have hcard : Fintype.card (Fin (2 * n) ⊕ Fin (2 * n)) = Module.finrank ℝ (V ℝ n) := by
    rw [Module.finrank_eq_card_basis (basisV ℝ n)]; simp
  refine (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext fun k => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  obtain ⟨-, hr⟩ := s4_rho_Gfam h θ
  rcases k with j | j
  · exact (hr j).1
  · exact (hr j).2

theorem s4_gfam_zero {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (j : Fin N) :
    s4_gfam h j 0 = 1 := by
  apply Subtype.ext
  show s4_gop (x j) (I (x j)) 0 = 1
  simp [s4_gop]

theorem s4_Gfam_zero {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) : s4_Gfam h 0 = 1 := by
  rw [s4_Gfam]
  apply List.prod_eq_one
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact s4_gfam_zero h j

theorem s4_coe_Gfam {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (θ : ℝ) :
    ((s4_Gfam h θ : Spin ℝ n) : C ℝ n) =
      ((List.finRange N).map fun j => s4_gop (x j) (I (x j)) θ).prod := by
  rw [s4_Gfam, SubmonoidClass.coe_list_prod, List.map_ofFn, List.ofFn_eq_map]
  rfl

theorem s4_continuous_Gfam {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) :
    @Continuous _ _ _ (spinTopology n) (s4_Gfam h) := by
  let := spinTopology n
  have : ContinuousSMul ℝ (C ℝ n) := IsModuleTopology.toContinuousSMul ℝ _
  have hcoe : Continuous fun θ => ((s4_Gfam h θ : Spin ℝ n) : C ℝ n) := by
    simp only [s4_coe_Gfam]
    refine continuous_list_prod _ fun j _ => ?_
    show Continuous fun θ : ℝ =>
      Real.cos (θ / 2) • (1 : C ℝ n) - Real.sin (θ / 2) • s4_uop (x j) (I (x j))
    fun_prop
  apply continuous_induced_rng.2
  set L : C ℝ n →ₗ[ℝ] (Finset (Fin (2 * n + 2 * n)) → ℝ) :=
    (basisExt ℝ n).equivFun.toLinearMap ∘ₗ (CliffordAlgebra.equivExterior (Q ℝ n)).toLinearMap
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  exact (hL.comp hcoe).congr fun θ => rfl

theorem s4_Gfam_mem_circleLift (hn : 0 < n) {x : Fin (2 * n) → V ℝ n} (h : s4_Adapted I x)
    (θ : ℝ) : s4_Gfam h θ ∈ circleLift n I := by
  let := spinTopology n
  have hpre : Set.range (s4_Gfam h) ⊆ circlePreimage n I := by
    rintro _ ⟨θ', rfl⟩
    exact ⟨θ', (s4_rho_Gfam_eq hn h θ').symm⟩
  have h1 : (1 : Spin ℝ n) ∈ Set.range (s4_Gfam h) := ⟨0, s4_Gfam_zero h⟩
  exact (isPreconnected_range (f := s4_Gfam h) (s4_continuous_Gfam h)).subset_connectedComponentIn
    h1 hpre ⟨θ, rfl⟩

/-- The operators `T_j = m(uⱼ)` on `S_ℂ`. -/
noncomputable def s4_Top {N : ℕ} (x : Fin N → V ℝ n) (I : Module.End ℝ (V ℝ n)) (j : Fin N) :
    Module.End ℂ (S ℂ n) :=
  m ℂ n (bcC ℝ ℂ n (s4_uop (x j) (I (x j))))

theorem s4_m_Gfam {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (θ : ℝ) :
    m ℂ n (bcC ℝ ℂ n (s4_Gfam h θ : C ℝ n)) = s4_Rop (List.ofFn (s4_Top x I)) (θ / 2) := by
  rw [s4_coe_Gfam, map_list_prod, map_list_prod, s4_Rop, List.map_map, List.map_map,
    List.map_ofFn, List.ofFn_eq_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, s4_gop, s4_Top]
  rw [map_sub, map_sub, map_smul (bcC ℝ ℂ n), map_smul (bcC ℝ ℂ n), map_one, ← Complex.coe_smul,
    ← Complex.coe_smul, map_smul, map_smul, map_one]

theorem s4_Top_sq {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (j : Fin N) :
    s4_Top x I j * s4_Top x I j = -1 := by
  rw [s4_Top, ← map_mul, ← map_mul, s4_u_u (h.hq j) (h.hQy j) (h.hxy j), map_neg, map_one,
    map_neg, map_one]

theorem s4_Top_comm {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) (j k : Fin N)
    (hjk : j ≠ k) : Commute (s4_Top x I j) (s4_Top x I k) := by
  have hiso1 : (Q ℝ n).IsOrtho (x j) (x k) :=
    QuadraticMap.isOrtho_polarBilin.mp (h.orth j k hjk).1
  have hiso2 : (Q ℝ n).IsOrtho (I (x j)) (x k) := QuadraticMap.isOrtho_polarBilin.mp (by
    show pairing ℝ n (I (x j)) (x k) = 0
    rw [s4_pairing_symm_R]; exact (h.orth k j (Ne.symm hjk)).2)
  have hiso3 : (Q ℝ n).IsOrtho (x j) (I (x k)) :=
    QuadraticMap.isOrtho_polarBilin.mp (h.orth j k hjk).2
  have hiso4 : (Q ℝ n).IsOrtho (I (x j)) (I (x k)) := QuadraticMap.isOrtho_polarBilin.mp (by
    show pairing ℝ n (I (x j)) (I (x k)) = 0
    rw [h.iso]; exact (h.orth j k hjk).1)
  have e1 := s4_ι_v_u (x k) hiso1 hiso2
  have e2 := s4_ι_v_u (I (x k)) hiso3 hiso4
  have hc : s4_uop (x j) (I (x j)) * s4_uop (x k) (I (x k)) =
      s4_uop (x k) (I (x k)) * s4_uop (x j) (I (x j)) := by
    show s4_uop (x j) (I (x j)) * ((Q ℝ n (x k))⁻¹ • (CliffordAlgebra.ι (Q ℝ n) (x k) *
        CliffordAlgebra.ι (Q ℝ n) (I (x k)))) = ((Q ℝ n (x k))⁻¹ • (CliffordAlgebra.ι (Q ℝ n) (x k) *
        CliffordAlgebra.ι (Q ℝ n) (I (x k)))) * s4_uop (x j) (I (x j))
    rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, ← e1, mul_assoc, ← e2, mul_assoc]
  show s4_Top x I j * s4_Top x I k = s4_Top x I k * s4_Top x I j
  rw [s4_Top, s4_Top, ← map_mul, ← map_mul, hc, map_mul, map_mul]

theorem s4_Top_Splus {N : ℕ} {x : Fin N → V ℝ n} (j : Fin N) (t : S ℂ n)
    (ht : t ∈ Splus ℂ n) : s4_Top x I j t ∈ Splus ℂ n := by
  have hsm : ∀ (r : ℝ) (Y : C ℂ n), m ℂ n (r • Y) = r • m ℂ n Y := fun r Y =>
    (m ℂ n).toLinearMap.map_smul_of_tower r Y
  rw [s4_Top, s4_uop, map_smul, map_mul, s4_bcC_ι, s4_bcC_ι, hsm,
    map_mul, LinearMap.smul_apply, Module.End.mul_apply]
  refine Submodule.smul_of_tower_mem _ _ (m_mem_Splus_of_odd ℂ n _
    (CliffordAlgebra.ι_mem_evenOdd_one _ _) _
    (m_mem_Sminus_of_odd ℂ n _ (CliffordAlgebra.ι_mem_evenOdd_one _ _) _ ht))

theorem s4_Top_pairwise {N : ℕ} {x : Fin N → V ℝ n} (h : s4_Adapted I x) :
    (List.ofFn (s4_Top x I)).Pairwise Commute :=
  List.pairwise_ofFn.mpr fun j k hjk => s4_Top_comm h j k (ne_of_lt hjk)

/-- `G(π)` anticommutes with the vectors: `ρ(G(π)) = -1`. -/
theorem s4_Gpi_anticomm (hn : 0 < n) {x : Fin (2 * n) → V ℝ n} (h : s4_Adapted I x)
    (v : V ℝ n) :
    (s4_Gfam h Real.pi : C ℝ n) * CliffordAlgebra.ι (Q ℝ n) v =
      -(CliffordAlgebra.ι (Q ℝ n) v * (s4_Gfam h Real.pi : C ℝ n)) := by
  have hrho : rho ℝ n (s4_Gfam h Real.pi) v = -v := by
    have := congrArg (fun A : Module.End ℝ (V ℝ n) => A v) (s4_rho_Gfam_eq hn h Real.pi)
    simp only [LinearEquiv.coe_coe] at this
    rw [this, s4_rotI_apply, Real.cos_pi, Real.sin_pi, neg_one_smul, zero_smul, add_zero]
  have h1 := ι_rho ℝ n (s4_Gfam h Real.pi) v
  rw [hrho, map_neg] at h1
  have hstar := spinGroup.star_mul_self_of_mem (s4_Gfam h Real.pi).2
  calc (s4_Gfam h Real.pi : C ℝ n) * CliffordAlgebra.ι (Q ℝ n) v
      = (s4_Gfam h Real.pi : C ℝ n) * CliffordAlgebra.ι (Q ℝ n) v *
          (star (s4_Gfam h Real.pi : C ℝ n) * (s4_Gfam h Real.pi : C ℝ n)) := by
        rw [hstar, mul_one]
    _ = -(CliffordAlgebra.ι (Q ℝ n) v * (s4_Gfam h Real.pi : C ℝ n)) := by
        rw [← mul_assoc, ← h1, neg_mul]

end Family2

variable {n : ℕ} {d : ℚ}

namespace KSecant

variable (P : KSecant n d)

/-- For `I ∈ Ω_P`, `Ĩ` is the unique element of `Spin(V_ℝ)_P` satisfying `ρ(Ĩ) = I` (§4, by
Lemma 3.1.1). -/
theorem existsUnique_lift_OmegaP (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∃! g : Spin ℝ n, g ∈ P.spinPR ∧ (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  obtain ⟨⟨g, hg, rfl⟩, -⟩ := hI
  have h := lemma3_1_1_real P J hP
  have hg' : g ∈ rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) := by rw [h.2]; exact hg
  obtain ⟨x, hx, hxg⟩ := hg'
  refine ⟨x, ⟨hx, by rw [hxg]⟩, fun y ⟨hy, hyI⟩ => h.1 hy hx ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [hyI, hxg]

/-- `I_θ ∈ SO_+(V_ℝ)_f` (proof of Lemma 4.0.3(2)); see `rotI_mem_SOplusfR`. -/
theorem s4_rot_mem_SOplusfR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) (θ : ℝ) :
    s4_rotEquiv n I hI.2.1 θ ∈ P.SOplusfR hP.isCompl := by
  set hW := hP.isCompl
  have hcs : IsComplexStructure I := hI.2.1
  have hc : I * P.fR hW = P.fR hW * I := P.s4_comm_OmegaP hW I hI
  obtain ⟨⟨g₀, hg₀, hg₀I⟩, -, hE1, hE2, -⟩ := hI
  have hiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
    rw [← hg₀I]; exact s4_pairing_of_mem_SOplus g₀ hg₀.1
  have hII : ∀ x, I (I x) = -x := fun x => by
    have := congrArg (fun F => F x) (show I * I = -1 from hcs)
    simpa using this
  have hanti : ∀ x y, pairing ℝ n (I x) y = -pairing ℝ n x (I y) := by
    intro x y
    have := hiso x (I y)
    rw [hII, map_neg] at this
    linarith
  -- `I_θ` is an isometry
  have hrot_iso : ∀ t x y, pairing ℝ n (rotI n I t x) (rotI n I t y) = pairing ℝ n x y := by
    intro t x y
    simp only [rotI, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hiso, hanti x y]
    linear_combination (pairing ℝ n x y) * Real.cos_sq_add_sin_sq t
  -- the four summands `V^{1,0} ∩ W_{i,ℂ}`, `V^{0,1} ∩ W_{i,ℂ}` are `n`-dimensional
  have hfr4 := P.s4_finrank_four hW I hc hE1 hE2
  have hV10 : Module.finrank ℂ (V10 n I) = 2 * n := by
    have hsplit := P.s4_V10_split hW I hc
    have hdisj : V10 n I ⊓ P.W₁ℂ ⊓ (V10 n I ⊓ P.W₂ℂ) = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      exact (s4_isCompl_Wℂ P hW).1.le_bot ⟨hx.1.2, hx.2.2⟩
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (V10 n I ⊓ P.W₁ℂ) (V10 n I ⊓ P.W₂ℂ)
    rw [hdisj, finrank_bot, ← hsplit, hfr4.1, hfr4.2.2.1] at h3
    omega
  have hV01 : Module.finrank ℂ (V01 n I) = 2 * n := by
    have h := Submodule.finrank_add_eq_of_isCompl (s4_isCompl_V10_V01 n I hcs)
    rw [hV10, s4_finrank_Vℂ] at h
    omega
  -- `det I_θ = 1`
  have hdetC : ∀ t : ℝ, LinearMap.det (rotI n I t) = 1 := by
    intro t
    have h := s4_det_of_isCompl (s4_extEnd ℝ ℂ n (rotI n I t)) (V10 n I) (V01 n I)
      (s4_isCompl_V10_V01 n I hcs) _ _ (s4_extEnd_rot_V10 n I t) (s4_extEnd_rot_V01 n I t)
    rw [hV10, hV01, ← mul_pow, s4_cos_sin_mul, one_pow, s4_det_extEnd] at h
    exact_mod_cast h
  -- `I_t ∈ SO(V_ℝ)` for every `t`
  have hmemSO : ∀ t, s4_rotEquiv n I hcs t ∈ TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) := by
    intro t
    refine TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
        (IsSMulRegular.of_ne_zero two_ne_zero)]
      intro x y
      exact hrot_iso t x y
    · apply Units.ext
      rw [LinearEquiv.coe_det]
      exact hdetC t
  -- the path `t ↦ I_t` in `SO(V_ℝ)` is continuous, starts at `1`, and the image of `Spin(V_ℝ)` is
  -- an open, hence closed, subgroup of `SO(V_ℝ)`: `I_t` stays in it (the paper: `SO_+(V_ℝ)` is the
  -- connected component of `SO(V_ℝ)` containing the path)
  have : ContinuousSMul ℝ (Module.End ℝ (V ℝ n)) := IsModuleTopology.toContinuousSMul ℝ _
  have : ContinuousAdd (Module.End ℝ (V ℝ n)) := IsModuleTopology.toContinuousAdd ℝ _
  have hcont : ∀ c : ℝ, Continuous fun t : ℝ => rotI n I (c * t) := by
    intro c
    unfold rotI
    exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).smul continuous_const).add
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).smul continuous_const)
  set γ : ℝ → TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) :=
    fun t => ⟨s4_rotEquiv n I hcs t, hmemSO t⟩ with hγ_def
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    rw [TauCeti.continuous_linearEquiv_iff]
    constructor
    · simpa [s4_coe_rotEquiv] using hcont 1
    · simpa [s4_coe_rotEquiv_inv] using hcont (-1)
  set H := (CliffordAlgebra.spinToSpecialOrthogonal (Q ℝ n)).range
  have hopen : IsOpen (H : Set (TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n))) :=
    CliffordAlgebra.isOpen_range_spinToSpecialOrthogonal (Q ℝ n) (s4_Q_nondegenerate n)
      s4_isOpen_square_real
  have hclosed := Subgroup.isClosed_of_isOpen H hopen
  have hγ0 : γ 0 ∈ H := by
    have : γ 0 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      show rotI n I 0 = 1
      exact s4_rot_zero n I
    rw [this]; exact H.one_mem
  have huniv := IsClopen.eq_univ ⟨hclosed.preimage hγ, hopen.preimage hγ⟩ ⟨0, hγ0⟩
  have hθ : γ θ ∈ H := by
    have : θ ∈ γ ⁻¹' (H : Set _) := by rw [huniv]; trivial
    exact this
  obtain ⟨x, hx⟩ := hθ
  have hrho : rho ℝ n x = s4_rotEquiv n I hcs θ := by
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun g : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) =>
      (g : V ℝ n ≃ₗ[ℝ] V ℝ n) v) hx
    rw [← this, CliffordAlgebra.coe_spinToSpecialOrthogonal_apply]
    rfl
  have hSO : s4_rotEquiv n I hcs θ ∈ SOplus ℝ n := hrho ▸ s4_rho_mem_SOplus x
  -- `I_θ` commutes with `f` and has determinant `1` on `W_{1,ℂ}` and `W_{2,ℂ}`
  have hrc : rotI n I θ * P.fR hW = P.fR hW * rotI n I θ := by
    simp only [rotI, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hc]
  have hmaps := P.s4_mapsTo_Wℂ hW _ hrc
  have hsplit := P.s4_Wℂ_split hW I hcs hc
  have hdisj : ∀ W : Submodule ℂ (V ℂ n), W ⊓ V10 n I ⊓ (W ⊓ V01 n I) = ⊥ := by
    intro W
    rw [eq_bot_iff]
    intro x hx
    exact (s4_isCompl_V10_V01 n _ hcs).1.le_bot ⟨hx.1.2, hx.2.2⟩
  refine ⟨hSO, fun x => congrArg (fun F => F x) hrc, ⟨hmaps.1, ?_⟩, ⟨hmaps.2, ?_⟩⟩
  · show LinearMap.det ((s4_extEnd ℝ ℂ n (rotI n I θ)).restrict hmaps.1) = 1
    rw [s4_det_restrict _ _ _ _ hmaps.1 inf_le_left inf_le_left (hdisj _) hsplit.1.symm _ _
      (fun x hx => s4_extEnd_rot_V10 n I θ x hx.2) (fun x hx => s4_extEnd_rot_V01 n I θ x hx.2),
      inf_comm P.W₁ℂ, inf_comm P.W₁ℂ, hfr4.1, hfr4.2.1, ← mul_pow, s4_cos_sin_mul, one_pow]
  · show LinearMap.det ((s4_extEnd ℝ ℂ n (rotI n I θ)).restrict hmaps.2) = 1
    rw [s4_det_restrict _ _ _ _ hmaps.2 inf_le_left inf_le_left (hdisj _) hsplit.2.symm _ _
      (fun x hx => s4_extEnd_rot_V10 n I θ x hx.2) (fun x hx => s4_extEnd_rot_V01 n I θ x hx.2),
      inf_comm P.W₂ℂ, inf_comm P.W₂ℂ, hfr4.2.2.1, hfr4.2.2.2, ← mul_pow, s4_cos_sin_mul, one_pow]


/-- `I_θ = cos θ + sin θ I` belongs to `SO_+(V_ℝ)_f` for every `θ ∈ ℝ` and `I ∈ Ω_P` (proof of
Lemma 4.0.3); in particular `𝕊_I` is a subgroup of `SO_+(V_ℝ)` (§4). -/
theorem rotI_mem_SOplusfR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) (θ : ℝ) :
    ∃ g ∈ P.SOplusfR hP.isCompl, (g : V ℝ n →ₗ[ℝ] V ℝ n) = rotI n I θ :=
  ⟨s4_rotEquiv n I hI.2.1 θ, P.s4_rot_mem_SOplusfR J hP I hI θ, rfl⟩

/-- `P_ℝ ≠ 0`. -/
theorem s4_exists_PR_ne_zero : ∃ p ∈ P.PR, p ≠ 0 := by
  have hne : P.Pℚ ≠ ⊥ := by
    intro h
    have := P.finrank_Pℚ
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨bcS ℚ ℝ n s, Submodule.subset_span ⟨s, hs, rfl⟩, fun h => hs0 ?_⟩
  exact s4_bcS_injective ℚ ℝ n (by rw [h, map_zero])

theorem s4_m_negOne [Nontrivial (V ℝ n)] (hQ : (Q ℝ n).Nondegenerate) (p : S ℝ n) :
    m ℝ n ((spinGroup.negOne (Q ℝ n) hQ.ne_zero : Spin ℝ n) : C ℝ n) p = -p := by
  rw [spinGroup.coe_negOne, map_neg, map_one]
  rfl

theorem s4_circleLift_subset_spinPR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    circleLift n I ⊆ (P.spinPR : Set (Spin ℝ n)) ∧ circleLift n I ≠ circlePreimage n I := by
  let := spinTopology n
  have hQ := s4_Q_nondegenerate n
  have hnt : Nontrivial (V ℝ n) := by
    have hn : 0 < n := s4_n_pos P
    exact ⟨⟨(0, Pi.single ⟨0, by omega⟩ 1), 0, by
      intro h; have := congrArg (fun v => v.2 ⟨0, by omega⟩) h; simp at this⟩⟩
  set neg1 : Spin ℝ n := spinGroup.negOne (Q ℝ n) hQ.ne_zero
  obtain ⟨p₀, hp₀, hp₀0⟩ := P.s4_exists_PR_ne_zero
  set u : Set (Spin ℝ n) := {g | ∀ p ∈ P.PR, m ℝ n (g : C ℝ n) p = (1 : ℝ) • p}
  set v : Set (Spin ℝ n) := {g | ∀ p ∈ P.PR, m ℝ n (g : C ℝ n) p = (-1 : ℝ) • p}
  have hu : (P.spinPR : Set (Spin ℝ n)) = u := by
    ext g; simp only [u, one_smul]; rfl
  have hucl : IsClosed u := by
    have : u = ⋂ p ∈ P.PR, {g : Spin ℝ n | m ℝ n (g : C ℝ n) p = (1 : ℝ) • p} := by
      ext g; simp [u]
    rw [this]
    exact isClosed_biInter fun p _ => s4_isClosed_fix n p 1
  have hvcl : IsClosed v := by
    have : v = ⋂ p ∈ P.PR, {g : Spin ℝ n | m ℝ n (g : C ℝ n) p = (-1 : ℝ) • p} := by
      ext g; simp [v]
    rw [this]
    exact isClosed_biInter fun p _ => s4_isClosed_fix n p (-1)
  have huv : ∀ g, g ∈ u → g ∉ v := by
    intro g hgu hgv
    have h1 := hgu p₀ hp₀
    have h2 := hgv p₀ hp₀
    rw [h1, one_smul, neg_one_smul] at h2
    exact hp₀0 (by have : (2 : ℝ) • p₀ = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; simp
                   exact (smul_eq_zero.mp this).resolve_left two_ne_zero)
  -- every `g` over `𝕊_I` is `±g'` with `g' ∈ Spin(V_ℝ)_P`
  have hcover : circlePreimage n I ⊆ u ∪ v := by
    rintro g ⟨θ, hθ⟩
    obtain ⟨g₁, hg₁, hg₁θ⟩ := P.rotI_mem_SOplusfR J hP I hI θ
    have hg₁' : g₁ ∈ rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) := by
      rw [(lemma3_1_1_real P J hP).2]; exact hg₁
    obtain ⟨g', hg', hg'g₁⟩ := hg₁'
    have heq : CliffordAlgebra.spinToSpecialOrthogonal (Q ℝ n) g =
        CliffordAlgebra.spinToSpecialOrthogonal (Q ℝ n) g' := by
      apply Subtype.ext
      refine LinearEquiv.ext fun x => ?_
      rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply,
        CliffordAlgebra.coe_spinToSpecialOrthogonal_apply]
      have h1 := congrArg (fun F : Module.End ℝ (V ℝ n) => F x) hθ
      have h2 := congrArg (fun F : V ℝ n ≃ₗ[ℝ] V ℝ n => F x) hg'g₁
      have h3 := congrArg (fun F : Module.End ℝ (V ℝ n) => F x) hg₁θ
      simp only [LinearEquiv.coe_coe] at h1 h2 h3
      change rho ℝ n g x = rho ℝ n g' x
      rw [h2, h3, h1]
    rcases CliffordAlgebra.eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq (Q ℝ n) hQ g g' heq
      with h | h
    · left
      rw [← hu, h]; exact hg'
    · right
      intro p hp
      rw [h, show ((spinGroup.negOne (Q ℝ n) hQ.ne_zero * g' : Spin ℝ n) : C ℝ n) =
          ((spinGroup.negOne (Q ℝ n) hQ.ne_zero : Spin ℝ n) : C ℝ n) * (g' : C ℝ n) from rfl,
        map_mul, Module.End.mul_apply, hg' p hp, s4_m_negOne hQ, neg_one_smul]
  have h1u : (1 : Spin ℝ n) ∈ u := fun p _ => by simp
  have h1 : (1 : Spin ℝ n) ∈ circlePreimage n I := ⟨0, by
    have : rho ℝ n 1 = 1 := spinVectorAction_one _
    simp [rotI, this, Module.End.one_eq_id]⟩
  have hsub : circleLift n I ⊆ u := by
    have hpre := (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := circlePreimage n I) (x := 1)))
      u v hucl hvcl ((connectedComponentIn_subset _ _).trans hcover)
      (by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hgu hgv; exact huv g hgu hgv)
    rcases hpre with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn h1)) (huv 1 h1u)
  refine ⟨hu ▸ hsub, fun heq => ?_⟩
  -- `-1` lies over `𝕊_I` but not in `Spin(V_ℝ)_P`
  have hneg_pre : neg1 ∈ circlePreimage n I := ⟨0, by
    refine LinearMap.ext fun x => ?_
    simp only [rotI, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero,
      Module.End.one_apply, LinearEquiv.coe_coe]
    have := congrArg (fun F : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℝ n) =>
      (F : V ℝ n ≃ₗ[ℝ] V ℝ n) x) (spinGroup.spinToSpecialOrthogonal_negOne
        (Q ℝ n) hQ.ne_zero)
    simp only [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply] at this
    change x = rho ℝ n neg1 x
    exact this.symm⟩
  have hneg_v : neg1 ∈ v := fun p _ => by rw [s4_m_negOne hQ, neg_one_smul]
  rw [← heq] at hneg_pre
  exact huv neg1 (hsub hneg_pre) hneg_v

/-- The identity component of the inverse image of `𝕊_I` lies in `Spin(V_ℝ)_P`, and the inverse
image is disconnected (proof of Lemma 4.0.3). -/
theorem circleLift_subset_spinPR (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    circleLift n I ⊆ (P.spinPR : Set (Spin ℝ n)) ∧ circleLift n I ≠ circlePreimage n I :=
  P.s4_circleLift_subset_spinPR J hP I hI


/-- An adapted family for `I ∈ Ω_P` (`KSecant.s4_exists_adapted`). -/
theorem s4_adapted_of_mem (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∃ x : Fin (2 * n) → V ℝ n, s4_Adapted I x := by
  obtain ⟨x, horth, hne⟩ := P.s4_exists_adapted J hP I hI
  have hiso : ∀ a b, pairing ℝ n (I a) (I b) = pairing ℝ n a b := by
    obtain ⟨⟨g, hg, hgI⟩, -⟩ := hI
    intro a b
    rw [← hgI]
    exact s4_pairing_of_mem_SOplus g hg.1 a b
  have hsq : ∀ a, I (I a) = -a := fun a => by
    have := congrArg (fun F => F a) (show I * I = -1 from hI.2.1)
    simpa using this
  exact ⟨x, ⟨hiso, hsq, horth, hne⟩⟩

/-- Every element of the identity component over `I_θ` is `G(θ)` (both lie in `Spin(V_ℝ)_P`, on
which `ρ` is injective, Lemma 3.1.1). -/
theorem s4_circleLift_eq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) {x : Fin (2 * n) → V ℝ n}
    (h : s4_Adapted I x) (g : Spin ℝ n) (hg : g ∈ circleLift n I) (θ : ℝ)
    (hθ : (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = rotI n I θ) : g = s4_Gfam h θ := by
  have hn : 0 < n := s4_n_pos P
  have hsub := (P.circleLift_subset_spinPR J hP I hI).1
  apply (lemma3_1_1_real P J hP).1 (hsub hg) (hsub (s4_Gfam_mem_circleLift hn h θ))
  apply LinearEquiv.toLinearMap_injective
  rw [hθ, s4_rho_Gfam_eq hn h θ]

/-- `S^{-p,p}_ℂ` is the weight space of weight `4p` of the family `R(φ) = m(G(2φ))`, in `S⁺_ℂ`. -/
theorem s4_Spq_eq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) {x : Fin (2 * n) → V ℝ n}
    (h : s4_Adapted I x) (p : ℤ) :
    Spq n I p = s4_Wt (List.ofFn (s4_Top x I)) (4 * p) ⊓ Splus ℂ n := by
  have hn : 0 < n := s4_n_pos P
  ext s
  constructor
  · rintro ⟨hs, hg⟩
    refine Submodule.mem_inf.mpr ⟨(s4_mem_Wt _ _ _).mpr fun φ => ?_, hs⟩
    have := hg (s4_Gfam h (2 * φ)) (s4_Gfam_mem_circleLift hn h _) (2 * φ)
      (s4_rho_Gfam_eq hn h _)
    rw [s4_m_Gfam, show 2 * φ / 2 = φ by ring] at this
    rw [this]
    congr 1
    push_cast
    ring_nf
  · intro hs
    obtain ⟨hW, hs⟩ := Submodule.mem_inf.mp hs
    refine ⟨hs, fun g hg θ hθ => ?_⟩
    rw [P.s4_circleLift_eq J hP I hI h g hg θ hθ, s4_m_Gfam]
    rw [s4_mem_Wt] at hW
    rw [hW (θ / 2)]
    congr 1
    push_cast
    ring_nf

theorem s4_m_ι_cliffordOp {F : Type*} [Field F] [CharZero F] (v : V F n) :
    m F n (CliffordAlgebra.ι (Q F n) v) = cliffordOp F n v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- `G(π)` acts as the identity on `S⁺_ℂ`: it anticommutes with `V`, so it is a multiple `c ε` of the
grading involution (`s4_eq_smul_eps_of_anticomm`), and `c = 1` since `G(π) ∈ Spin(V_ℝ)_P` fixes the
nonzero even class of `P` with `p₁ = u₁ + u₂`. -/
theorem s4_m_Gpi_Splus (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) {x : Fin (2 * n) → V ℝ n}
    (h : s4_Adapted I x) (s : S ℂ n) (hs : s ∈ Splus ℂ n) :
    m ℂ n (bcC ℝ ℂ n (s4_Gfam h Real.pi : C ℝ n)) s = s := by
  have hn : 0 < n := s4_n_pos P
  set B := m ℂ n (bcC ℝ ℂ n (s4_Gfam h Real.pi : C ℝ n)) with hB
  have hreal : ∀ v : V ℝ n, ∀ t, B (m ℂ n (CliffordAlgebra.ι (Q ℂ n) (bcV ℝ ℂ n v)) t) =
      -(m ℂ n (CliffordAlgebra.ι (Q ℂ n) (bcV ℝ ℂ n v)) (B t)) := by
    intro v t
    have h1 := congrArg (fun c => m ℂ n (bcC ℝ ℂ n c)) (s4_Gpi_anticomm hn h v)
    simp only [map_mul, map_neg, s4_bcC_ι] at h1
    have h2 := congrArg (fun A : Module.End ℂ (S ℂ n) => A t) h1
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using h2
  have hall : ∀ w : V ℂ n, ∀ t, B (m ℂ n (CliffordAlgebra.ι (Q ℂ n) w) t) =
      -(m ℂ n (CliffordAlgebra.ι (Q ℂ n) w) (B t)) := by
    intro w t
    rw [← (basisV ℂ n).sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← s4_bcV_basisV ℝ ℂ n j, hreal, smul_neg]
  have hmL : ∀ w, m ℂ n (CliffordAlgebra.ι (Q ℂ n) (0, w)) = L ℂ n w := fun w => by
    rw [s4_m_ι_cliffordOp]
    simp [cliffordOp]
  have hmD : ∀ θ, m ℂ n (CliffordAlgebra.ι (Q ℂ n) (θ, 0)) = D ℂ n θ := fun θ => by
    rw [s4_m_ι_cliffordOp]
    simp [cliffordOp]
  obtain ⟨c, hc⟩ := s4_eq_smul_eps_of_anticomm ℂ n B
    (fun w t => by rw [← hmL]; exact hall _ t) (fun θ t => by rw [← hmD]; exact hall _ t)
  -- the scalar is `1`: `B` fixes `P_ℂ ∋ u₁`, which is even and nonzero
  have hG : s4_Gfam h Real.pi ∈ P.spinPR :=
    (P.circleLift_subset_spinPR J hP I hI).1 (s4_Gfam_mem_circleLift hn h _)
  have hfixP : ∀ p ∈ P.Pℚ, B (bcS ℚ ℂ n p) = bcS ℚ ℂ n p := by
    intro p hp
    have hmem : bcS ℚ ℝ n p ∈ P.PR := Submodule.subset_span ⟨p, hp, rfl⟩
    rw [← s4_bcS_bcS ℚ ℝ ℂ n p, hB, s4_m_bcC, hG _ hmem]
  have hfixSpan : ∀ y ∈ Submodule.span ℂ (bcS ℚ ℂ n '' (P.Pℚ : Set (S ℚ n))), B y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, rfl⟩ := hz
      exact hfixP p hp
    | zero => exact map_zero B
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have hspan : ∀ z ∈ Submodule.span (Kd d) (bcS ℚ (Kd d) n '' (P.Pℚ : Set (S ℚ n))),
      bcS (Kd d) ℂ n z ∈ Submodule.span ℂ (bcS ℚ ℂ n '' (P.Pℚ : Set (S ℚ n))) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨p, hp, rfl⟩ := hw
      rw [s4_bcS_bcS]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c ha
  set x₀ := bcS (Kd d) ℂ n P.u₁ with hx₀
  have hx₀_fix : B x₀ = x₀ := by
    refine hfixSpan _ (hspan _ ?_)
    rw [P.span_bcS_Pℚ]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have hx₀_even : x₀ ∈ Splus ℂ n := s4_bcS_mem_Splus (Kd d) ℂ n _ P.isPure.1
  have hx₀_ne : x₀ ≠ 0 := fun h0 =>
    P.u₁_ne_zero (s4_bcS_injective (Kd d) ℂ n (by rw [← hx₀, h0, map_zero]))
  have hε : ∀ y ∈ Splus ℂ n, s4_eps ℂ n y = y := fun y hy =>
    CliffordAlgebra.involute_eq_of_mem_even hy
  have hc1 : c = 1 := by
    have h1 := hc x₀
    rw [hx₀_fix, hε x₀ hx₀_even] at h1
    have h2 : (c - 1) • x₀ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx₀_ne)
  rw [hc s, hc1, one_smul, hε s hs]

/-- `p ↦ e^{-2ip}` is injective on `ℤ` (`π` is irrational). -/
theorem s4_exp_injective :
    Function.Injective (fun p : ℤ => Complex.exp (-(2 * (p : ℂ)) * Complex.I)) := by
  intro p q hpq
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hpq
  have him := congrArg Complex.im hk
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, zero_add, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero,
    sub_zero, Complex.mul_re] at him
  by_contra hne
  by_cases hk0 : k = 0
  · subst hk0
    apply hne
    have : (p : ℝ) = q := by push_cast at him; linarith
    exact_mod_cast this
  · apply irrational_pi.ne_rat ((q - p : ℤ) / k : ℚ)
    push_cast at him ⊢
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
    linarith

theorem s4_Spq_iSupIndep (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    iSupIndep (Spq n I) ∧ ⨆ p, Spq n I p = Splus ℂ n := by
  have hn : 0 < n := s4_n_pos P
  obtain ⟨x, h⟩ := P.s4_adapted_of_mem J hP I hI
  set L := List.ofFn (s4_Top x I) with hL
  have hSpq := P.s4_Spq_eq J hP I hI h
  constructor
  · have hle : (Spq n I) ≤ (fun p : ℤ => Module.End.eigenspace (s4_Rop L (1 / 2))
        (Complex.exp (-(2 * (p : ℂ)) * Complex.I))) := by
      intro p s hs
      rw [hSpq] at hs
      have h1 := (s4_mem_Wt _ _ _).mp (Submodule.mem_inf.mp hs).1 (1 / 2)
      rw [Module.End.mem_eigenspace_iff, h1]
      congr 1
      push_cast
      ring_nf
    exact ((Module.End.eigenspaces_iSupIndep (s4_Rop L (1 / 2))).comp s4_exp_injective).mono hle
  · apply le_antisymm
    · exact iSup_le fun p => by rw [hSpq]; exact inf_le_right
    · have hdec := s4_weight_decomp L (fun T hT => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
          exact s4_Top_sq h j)
        (s4_Top_pairwise h) (Splus ℂ n) (fun T hT t ht => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
          exact s4_Top_Splus j t ht)
      refine hdec.trans (iSup_le fun k => ?_)
      intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]; exact zero_mem _
      obtain ⟨hyW, hyS⟩ := Submodule.mem_inf.mp hy
      have h1 : s4_Rop L (Real.pi / 2) y = y := by
        rw [hL, ← s4_m_Gfam h Real.pi]
        exact P.s4_m_Gpi_Splus J hP I hI h y hyS
      have h2 := (s4_mem_Wt _ _ _).mp hyW (Real.pi / 2)
      rw [h1] at h2
      have hexp : Complex.exp (-((k : ℂ) * ((Real.pi / 2 : ℝ) : ℂ)) * Complex.I) = 1 := by
        have h3 : (Complex.exp (-((k : ℂ) * ((Real.pi / 2 : ℝ) : ℂ)) * Complex.I) - 1) • y = 0 := by
          rw [sub_smul, ← h2, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
      obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp hexp
      have hk : k = 4 * (-j) := by
        have him := congrArg Complex.im hj
        simp at him
        have hkj : ((k : ℝ) + 4 * j) * Real.pi = 0 := by linear_combination -2 * him
        have hkj' : (k : ℝ) + 4 * j = 0 :=
          (mul_eq_zero.mp hkj).resolve_right Real.pi_ne_zero
        have : (k : ℝ) = 4 * (-(j : ℝ)) := by linarith
        exact_mod_cast this
      rw [hk] at hy
      exact Submodule.mem_iSup_of_mem (-j) (by rw [hSpq]; exact hy)


/-- The identity component of the inverse image of `𝕊_I` defines a real Hodge structure of weight `0`
on `S⁺_ℝ = H^{ev}(X, ℝ)` (§4): `S⁺_ℂ = ⊕_{p ∈ ℤ} S^{-p,p}_ℂ`.

The paper states this without proof; we prove it as follows (`KSecant.s4_Spq_iSupIndep`). `I ∈ Ω_P`
has an orthogonal family `x₁, …, x_{2n}` adapted to it (pairwise orthogonal planes `span(xⱼ, I xⱼ)`,
`(xⱼ, xⱼ)_V ≠ 0`; `KSecant.s4_exists_adapted`), and `G(θ) = Πⱼ (cos(θ/2) - sin(θ/2) uⱼ)`,
`uⱼ = xⱼ (I xⱼ)/Q(xⱼ)`, is a continuous lift of `θ ↦ I_θ` to `Spin(V_ℝ)` with `G(0) = 1`; hence it
lies in the identity component, which consists exactly of the `G(θ)` (it lies in `Spin(V_ℝ)_P`, on
which `ρ` is injective). The commuting operators `Tⱼ = m(uⱼ)` satisfy `Tⱼ² = -1`, so `S⁺_ℂ` is the sum
of the weight spaces of `m(G(θ)) = Πⱼ (cos(θ/2) - sin(θ/2) Tⱼ)` (`s4_weight_decomp`); the weights
occurring on `S⁺_ℂ` are multiples of `4` because `G(π)`, which anticommutes with `V`, acts on `S`
as a multiple of the grading involution (`s4_eq_smul_eps_of_anticomm`), hence trivially on `S⁺_ℂ`
since it fixes the even spinor `u₁ ∈ P_ℂ`. Independence: the weight spaces are eigenspaces of
`m(G(1))` for the distinct eigenvalues `e^{-2ip}` (`π` is irrational). -/
theorem Spq_iSupIndep (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    iSupIndep (Spq n I) ∧ ⨆ p, Spq n I p = Splus ℂ n :=
  P.s4_Spq_iSupIndep J hP I hI

/-- `\overline{S^{-p,p}_ℂ} = S^{p,-p}_ℂ` (§4; complex conjugation of the coefficients). -/
theorem conj_Spq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) (p : ℤ) :
    conjS (starRingAut : ℂ ≃+* ℂ) n '' (Spq n I p : Set (S ℂ n)) = (Spq n I (-p) : Set (S ℂ n)) := by
  -- `I ∈ Ω_P` is not needed: the elements of the identity component are real, so their action
  -- commutes with conjugation
  have _ := hI
  have key : ∀ q : ℤ, ∀ s ∈ Spq n I q, conjS (starRingAut : ℂ ≃+* ℂ) n s ∈ Spq n I (-q) := by
    rintro q s ⟨hs1, hs2⟩
    refine ⟨s4_conjS_mem_Splus n s hs1, fun g hg θ hθ => ?_⟩
    have hT : ∀ t, ∃ t', m ℂ n (bcC ℝ ℂ n g) (bcS ℝ ℂ n t) = bcS ℝ ℂ n t' :=
      fun t => ⟨_, s4_m_bcC ℝ ℂ n g t⟩
    rw [← s4_conjS_comm n (m ℂ n (bcC ℝ ℂ n g)) hT, hs2 g hg θ hθ, s4_conjS_smul]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, map_ofNat, map_intCast, Complex.conj_ofReal]
    push_cast
    ring
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact key p t ht
  · intro hs
    refine ⟨conjS (starRingAut : ℂ ≃+* ℂ) n s, ?_, s4_conjS_conjS n s⟩
    have := key (-p) s hs
    rwa [neg_neg] at this

end KSecant

/-! ## Lemma 4.0.3 and Corollary 4.0.4 -/

/-- **Lemma 4.0.3** (`lemma-Hodge-Weil-classes-remain-of-Hodge-type-for-all-I-in-Omega-P`), part (1):
the plane `⋀^{2n} W₁ ⊕ ⋀^{2n} W₂` corresponds to a rational plane in `⋀^{2n} V_ℚ` (`KSecant.hwPlane`,
`corollary3_2_2_rational`), which is spanned by Hodge classes, for every complex structure `I` in
`Ω_P`. Standing assumption: Assumption 2.4.1. -/
theorem lemma4_0_3_hodgeWeil (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    P.hwPlane ≤ hodgeClassesV n I n := by
  obtain ⟨g, ⟨hg, hgI⟩, -⟩ := P.existsUnique_lift_OmegaP J hP I hI
  obtain ⟨⟨h, hh, rfl⟩, hcs, hE, -, -⟩ := hI
  have hc := P.s4_comm_of_mem_SOplusfR hP.isCompl h hh
  refine corollary3_2_2_hodge P J hP _ ⟨g, hg, hgI⟩ hcs ?_
  rw [KSecant.nu, hc]
  exact hE

/-- **Lemma 4.0.3** (`lemma-Hodge-Weil-classes-remain-of-Hodge-type-for-all-I-in-Omega-P`), part (2):
the plane `P` is spanned by semi-Hodge classes, for every complex structure `I` in `Ω_P`. -/
theorem lemma4_0_3_semiHodge (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    ∀ s ∈ P.Pℚ, IsSemiHodge n I s := by
  -- the identity component of the inverse image of `𝕊_I` lies in `Spin(V_ℝ)_P`, which fixes `P`
  intro s hs
  refine ⟨s4_bcS_mem_Splus ℚ ℂ n s (P.Pℚ_le_Splus hs), fun g hg θ _ => ?_⟩
  have hgP := (P.circleLift_subset_spinPR J hP I hI).1 hg
  have hfix : m ℝ n (g : C ℝ n) (bcS ℚ ℝ n s) = bcS ℚ ℝ n s :=
    hgP (bcS ℚ ℝ n s) (Submodule.subset_span ⟨s, hs, rfl⟩)
  rw [← s4_bcS_bcS ℚ ℝ ℂ n s, s4_m_bcC, hfix]
  simp

/-! ### Helpers (prefix `s4_`): base change and the `(1,1)` part of `⋀² V_ℂ` -/

section ExtBC
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s4_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) := by
  unfold bcExt
  exact ExteriorAlgebra.lift_ι_apply F _ _ v

theorem s4_bcExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) =
      ExteriorAlgebra.ιMulti F' k (fun i => bcV F F' n (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, s4_bcExt_ι]

theorem s4_bcExt_basisExt (S : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n S) = basisExt F' n S := by
  rw [basisExt, basisExt, ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family, s4_bcExt_ιMulti, Function.comp_apply, s4_bcV_basisV]
  rfl

theorem s4_bcExt_eq_sum (x : ExteriorAlgebra F (V F n)) :
    bcExt F F' n x = ∑ S, algebraMap F F' ((basisExt F n).repr x S) • basisExt F' n S := by
  conv_lhs => rw [← (basisExt F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, s4_bcExt_basisExt, algebraMap_smul]

theorem s4_repr_bcExt (x : ExteriorAlgebra F (V F n)) (S : Finset (Fin (2 * n + 2 * n))) :
    (basisExt F' n).repr (bcExt F F' n x) S = algebraMap F F' ((basisExt F n).repr x S) := by
  rw [s4_bcExt_eq_sum, Module.Basis.repr_sum_self]

theorem s4_bcExt_injective : Function.Injective (bcExt F F' n) := by
  intro x y h
  apply (basisExt F n).repr.injective
  ext S
  have := congrArg (fun z => (basisExt F' n).repr z S) h
  simp only [s4_repr_bcExt] at this
  exact (algebraMap F F').injective this

end ExtBC

section ExtTower
variable (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
  [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F''] (n : ℕ)

theorem s4_bcExt_bcExt (x : ExteriorAlgebra F (V F n)) :
    bcExt F' F'' n (bcExt F F' n x) = bcExt F F'' n x := by
  apply (basisExt F'' n).repr.injective
  ext S
  simp only [s4_repr_bcExt, ← IsScalarTower.algebraMap_apply]

end ExtTower

/-- Naturality: `⋀ A_ℂ ∘ bc = bc ∘ ⋀ A` for `A ∈ End(V_ℝ)`. -/
theorem s4_map_extEnd_bcExt (n : ℕ) (A : Module.End ℝ (V ℝ n)) (x : ExteriorAlgebra ℝ (V ℝ n)) :
    ExteriorAlgebra.map (s4_extEnd ℝ ℂ n A) (bcExt ℝ ℂ n x) = bcExt ℝ ℂ n (ExteriorAlgebra.map A x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      AlgHom.map_smul_of_tower, map_one]
  | ι v => rw [s4_bcExt_ι, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, s4_bcExt_ι,
      s4_extEnd_bcV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem s4_ιMulti_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : Fin 1 → M) :
    ExteriorAlgebra.ιMulti R 1 a = ExteriorAlgebra.ι R (a 0) := by
  rw [ExteriorAlgebra.ιMulti_apply]
  simp

/-- A class `γ ∈ ⋀² V_ℂ` is of type `(1,1)` iff `⋀² I_ℂ` fixes it. -/
theorem s4_map_cs_iff_pq11 (n : ℕ) (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (γ : ExteriorAlgebra ℂ (V ℂ n)) (hγ : γ ∈ ⋀[ℂ]^2 (V ℂ n)) :
    ExteriorAlgebra.map (s4_extEnd ℝ ℂ n I) γ = γ ↔ γ ∈ pqPiece (V10 n I) (V01 n I) 1 1 := by
  set M := ExteriorAlgebra.map (s4_extEnd ℝ ℂ n I)
  have hMa : ∀ a ∈ V10 n I, M (ExteriorAlgebra.ι ℂ a) = Complex.I • ExteriorAlgebra.ι ℂ a := by
    intro a ha
    rw [ExteriorAlgebra.map_apply_ι, show s4_extEnd ℝ ℂ n I a = Complex.I • a from
      Module.End.mem_eigenspace_iff.mp ha, map_smul]
  have hMb : ∀ b ∈ V01 n I, M (ExteriorAlgebra.ι ℂ b) = (-Complex.I) • ExteriorAlgebra.ι ℂ b := by
    intro b hb
    rw [ExteriorAlgebra.map_apply_ι, show s4_extEnd ℝ ℂ n I b = (-Complex.I) • b from
      Module.End.mem_eigenspace_iff.mp hb, map_smul]
  set P20 := Submodule.span ℂ {x | ∃ a ∈ V10 n I, ∃ a' ∈ V10 n I,
    x = ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ a'}
  set P02 := Submodule.span ℂ {x | ∃ b ∈ V01 n I, ∃ b' ∈ V01 n I,
    x = ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ b'}
  set P11 := pqPiece (V10 n I) (V01 n I) 1 1
  have hgen11 : ∀ a ∈ V10 n I, ∀ b ∈ V01 n I,
      ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b ∈ P11 := by
    intro a ha b hb
    refine Submodule.subset_span ⟨fun _ => a, fun _ => b, fun _ => ha, fun _ => hb, ?_⟩
    rw [s4_ιMulti_one, s4_ιMulti_one]
  have h20 : ∀ x ∈ P20, M x = -x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, a', ha', rfl⟩ := hx
      rw [map_mul, hMa a ha, hMa a' ha', smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
    | smul c x _ hx => rw [map_smul, hx, smul_neg]
  have h02 : ∀ x ∈ P02, M x = -x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, b', hb', rfl⟩ := hx
      rw [map_mul, hMb b hb, hMb b' hb', smul_mul_smul_comm, neg_mul_neg, Complex.I_mul_I,
        neg_one_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
    | smul c x _ hx => rw [map_smul, hx, smul_neg]
  have h11 : ∀ x ∈ P11, M x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hx
      rw [s4_ιMulti_one, s4_ιMulti_one, map_mul, hMa _ (ha 0), hMb _ (hb 0), smul_mul_smul_comm,
        mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hdecomp : ⋀[ℂ]^2 (V ℂ n) ≤ P20 ⊔ P11 ⊔ P02 := by
    show (LinearMap.range (ExteriorAlgebra.ι ℂ)) ^ 2 ≤ _
    rw [pow_two, Submodule.mul_le]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hx : x ∈ V10 n I ⊔ V01 n I := by rw [(s4_isCompl_V10_V01 n I hI).sup_eq_top]; trivial
    have hy : y ∈ V10 n I ⊔ V01 n I := by rw [(s4_isCompl_V10_V01 n I hI).sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    have hswap : ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ a' =
        -(ExteriorAlgebra.ι ℂ a' * ExteriorAlgebra.ι ℂ b) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a')
    have e : ExteriorAlgebra.ι ℂ (a + b) * ExteriorAlgebra.ι ℂ (a' + b') =
        ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ a' +
          (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b' -
            ExteriorAlgebra.ι ℂ a' * ExteriorAlgebra.ι ℂ b) +
          ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ b' := by
      rw [map_add, map_add, add_mul, mul_add, mul_add, hswap]; abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.subset_span ⟨a, ha, a', ha', rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.sub_mem _ (hgen11 a ha b' hb') (hgen11 a' ha' b hb)))
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, b', hb', rfl⟩)
  constructor
  · intro hM
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hdecomp hγ)
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, map_add, h20 _ hy₁, h11 _ hy₂, h02 _ hz] at hM
    have h2 : (2 : ℂ) • (y₁ + z) = 0 := by
      have e : (2 : ℂ) • (y₁ + z) = (y₁ + y₂ + z) - (-y₁ + y₂ + -z) := by module
      rw [e, hM, sub_self]
    have h0 : y₁ + z = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
    rw [show y₁ + y₂ + z = y₂ + (y₁ + z) by abel, h0, add_zero]
    exact hy₂
  · exact h11 γ

/-- Base change preserves the degree. -/
theorem s4_bcExt_mem_pow (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (n k : ℕ) (x : ExteriorAlgebra F (V F n)) (hx : x ∈ ⋀[F]^k (V F n)) :
    bcExt F F' n x ∈ ⋀[F']^k (V F' n) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExteriorAlgebra F' (V F' n))]
    show _ ∈ (LinearMap.range (ExteriorAlgebra.ι F' : V F' n →ₗ[F'] _)) ^ 0
    rw [pow_zero]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, s4_bcExt_ι]
    show _ ∈ (LinearMap.range (ExteriorAlgebra.ι F' : V F' n →ₗ[F'] _)) ^ (i + 1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul ⟨_, rfl⟩ hx

/-- A class `α ∈ ⋀² V_ℚ` is of type `(1,1)` with respect to a complex structure `I` if and only if
`I(α) = α` (`I` acting on `⋀² V_ℝ` by `⋀² I`) (proof of Corollary 4.0.4). -/
theorem mem_hodgeClassesV_one_iff (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (α : ExteriorAlgebra ℚ (V ℚ n)) (hα : α ∈ ⋀[ℚ]^2 (V ℚ n)) :
    α ∈ hodgeClassesV n I 1 ↔ ExteriorAlgebra.map I (bcExt ℚ ℝ n α) = bcExt ℚ ℝ n α := by
  rw [mem_hodgeClassesV_iff]
  have hβ : bcExt ℚ ℂ n α = bcExt ℝ ℂ n (bcExt ℚ ℝ n α) := (s4_bcExt_bcExt ℚ ℝ ℂ n α).symm
  have hβ2 : bcExt ℚ ℂ n α ∈ ⋀[ℂ]^2 (V ℂ n) := s4_bcExt_mem_pow ℚ ℂ n 2 α hα
  have key := s4_map_cs_iff_pq11 n I hI _ hβ2
  rw [hβ, s4_map_extEnd_bcExt] at key
  rw [hβ, ← key, (s4_bcExt_injective ℝ ℂ n).eq_iff]
  simp [hα]

/-! ### Helpers (prefix `s4_`) for Corollary 4.0.4: the class `Ξ_P^♯` and the degrees -/

section Pair2
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

theorem s4_algebraMapInv_ι (x : M) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ι F x) = 0 := by
  simp [ExteriorAlgebra.algebraMapInv]

/-- Naturality of contraction: `d ⌋ (⋀A z) = ⋀A ((d ∘ A) ⌋ z)`. -/
theorem s4_contract_map (A : M →ₗ[F] M) (d : Module.Dual F M) (z : ExteriorAlgebra F M) :
    contractLeft (Q := 0) d (ExteriorAlgebra.map A z) =
      ExteriorAlgebra.map A (contractLeft (Q := 0) (d ∘ₗ A) z) := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    rw [map_mul, show ExteriorAlgebra.map A (CliffordAlgebra.ι 0 m) = CliffordAlgebra.ι 0 (A m) from
      ExteriorAlgebra.map_apply_ι A m, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_sub, map_smul,
      map_mul, show ExteriorAlgebra.map A (CliffordAlgebra.ι 0 m) = CliffordAlgebra.ι 0 (A m) from
      ExteriorAlgebra.map_apply_ι A m]
    rfl

theorem s4_algebraMapInv_map (A : M →ₗ[F] M) (z : ExteriorAlgebra F M) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map A z) = ExteriorAlgebra.algebraMapInv z := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι x => rw [ExteriorAlgebra.map_apply_ι, s4_algebraMapInv_ι, s4_algebraMapInv_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/-- `⟪ι a ∧ ι b, d, d'⟫ = d a d' b - d b d' a`. -/
theorem s4_pair2_ι (d d' : Module.Dual F M) (a b : M) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) d' (contractLeft (Q := 0) d
      (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b))) = d a * d' b - d b * d' a := by
  rw [show (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b : ExteriorAlgebra F M) =
    CliffordAlgebra.ι 0 a * CliffordAlgebra.ι 0 b from rfl, contractLeft_ι_mul, contractLeft_ι,
    ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul, map_smul, contractLeft_ι,
    contractLeft_ι, map_sub, map_smul, map_smul]
  simp only [ExteriorAlgebra.algebraMapInv, AlgHom.commutes, smul_eq_mul]
  simp

end Pair2

section Unique
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s4_pairing_apply (x v : V F n) : pairing F n x v = x.1 v.2 + v.1 x.2 := by
  simp [pairing, TauCeti.polar_dualProd]

omit [CharZero F] in
/-- Every coordinate functional of `basisV` is `(x, ·)_V` for some `x`. -/
theorem s4_exists_pairing_eq_coord (p : Fin (2 * n + 2 * n)) :
    ∃ x : V F n, pairing F n x = (basisV F n).coord p := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective p
  rcases k with i | i
  · refine ⟨(0, e F n i), LinearMap.ext fun v => ?_⟩
    rw [s4_pairing_apply, Module.Basis.coord_apply, s4_repr_basisV_inl]
    simp
  · refine ⟨(f F n i, 0), LinearMap.ext fun v => ?_⟩
    rw [s4_pairing_apply, Module.Basis.coord_apply, s4_repr_basisV_inr]
    simp [f]

/-- An element of `⋀² V_F` is determined by its pairings `⟪ξ, (x,·) ∧ (y,·)⟫`. -/
theorem s4_eq_zero_of_pair2 (ξ : ExteriorAlgebra F (V F n)) (hξ : ξ ∈ ⋀[F]^2 (V F n))
    (h : ∀ x y : V F n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) ξ)) = 0) : ξ = 0 := by
  set w : Fin (2 * n + 2 * n) × Fin (2 * n + 2 * n) → ExteriorAlgebra F (V F n) :=
    fun kl => ExteriorAlgebra.ι F (basisV F n kl.1) * ExteriorAlgebra.ι F (basisV F n kl.2) with hw
  have hspan : ξ ∈ Submodule.span F (Set.range w) := by
    have hle : ⋀[F]^2 (V F n) ≤ Submodule.span F (Set.range w) := by
      show (LinearMap.range (ExteriorAlgebra.ι F : V F n →ₗ[F] _)) ^ 2 ≤ _
      rw [pow_two, Submodule.mul_le]
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← (basisV F n).sum_repr x, ← (basisV F n).sum_repr y, map_sum, map_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [Finset.mul_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul, map_smul, smul_mul_smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, l), rfl⟩)
    exact hle hξ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  -- the pairings give `c (p, q) - c (q, p)`
  have hsym : ∀ p q, c (p, q) = c (q, p) := by
    intro p q
    obtain ⟨x, hx⟩ := s4_exists_pairing_eq_coord F n p
    obtain ⟨y, hy⟩ := s4_exists_pairing_eq_coord F n q
    have h0 := h x y
    rw [hx, hy, ← hc] at h0
    simp only [map_sum, map_smul, hw, s4_pair2_ι, smul_eq_mul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at h0
    rw [Fintype.sum_prod_type] at h0
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero] at h0
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
    have hqp : (∑ x, ∑ x_1, if x = q then if x_1 = p then c (x, x_1) else 0 else 0) = c (q, p) := by
      rw [Fintype.sum_eq_single q (fun x hx => by simp [hx])]
      simp
    rw [hqp] at h0
    linear_combination h0
  -- hence `ξ = -ξ`
  have hneg : ξ = -ξ := by
    have e2 : ∑ kl : _ × _, c kl • w kl = ∑ kl : _ × _, c kl.swap • w kl.swap :=
      (Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl))
    have e3 : ∀ kl : Fin (2 * n + 2 * n) × Fin (2 * n + 2 * n), w kl.swap = -w kl := by
      intro kl
      simp only [hw, Prod.fst_swap, Prod.snd_swap]
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have key : ∑ kl : _ × _, c kl • w kl = -∑ kl : _ × _, c kl • w kl := by
      calc ∑ kl : _ × _, c kl • w kl = ∑ kl : _ × _, c kl.swap • w kl.swap := e2
        _ = ∑ kl : _ × _, -(c kl • w kl) := Finset.sum_congr rfl fun kl _ => by
            rw [e3, show c kl.swap = c kl from (hsym kl.1 kl.2).symm, smul_neg]
        _ = -∑ kl : _ × _, c kl • w kl := Finset.sum_neg_distrib _
    rw [← hc]; exact key
  have h2 : (2 : F) • ξ = 0 := by
    rw [two_smul]; nth_rewrite 2 [hneg]; exact add_neg_cancel ξ
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Unique

section Pair2Nat
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- `⟪⋀A z, d, d'⟫ = ⟪z, d ∘ A, d' ∘ A⟫`. -/
theorem s4_pair2_map (A : M →ₗ[F] M) (d d' : Module.Dual F M) (z : ExteriorAlgebra F M) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) d' (contractLeft (Q := 0) d
      (ExteriorAlgebra.map A z))) =
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (d' ∘ₗ A) (contractLeft (Q := 0) (d ∘ₗ A) z)) := by
  rw [s4_contract_map, s4_contract_map, s4_algebraMapInv_map]

end Pair2Nat

/-- `⋀A` preserves the degree. -/
theorem s4_map_mem_pow {F M : Type*} [Field F] [AddCommGroup M] [Module F M] (A : M →ₗ[F] M)
    (k : ℕ) (z : ExteriorAlgebra F M) (hz : z ∈ ⋀[F]^k M) : ExteriorAlgebra.map A z ∈ ⋀[F]^k M := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    show _ ∈ (LinearMap.range (ExteriorAlgebra.ι F : M →ₗ[F] _)) ^ 0
    rw [pow_zero]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    show _ ∈ (LinearMap.range (ExteriorAlgebra.ι F : M →ₗ[F] _)) ^ (i + 1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul ⟨_, rfl⟩ hx

/-- A form-preserving `A` (for `B` given by pairings): if `⟪z, x, y⟫ = B x y` for all `x, y` and `A` is
an isometry with `B(A⁻¹x, A⁻¹y) = B(x, y)`, then `⋀A z = z` (for `z ∈ ⋀²`). -/
theorem s4_map_eq_of_spec {F : Type*} [Field F] [CharZero F] (n : ℕ) (A : V F n ≃ₗ[F] V F n)
    (hA : ∀ x y, pairing F n (A x) (A y) = pairing F n x y) (B : V F n → V F n → F)
    (hB : ∀ x y, B (A.symm x) (A.symm y) = B x y) (z : ExteriorAlgebra F (V F n))
    (hz : z ∈ ⋀[F]^2 (V F n))
    (hspec : ∀ x y, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) z)) = B x y) :
    ExteriorAlgebra.map (A : V F n →ₗ[F] V F n) z = z := by
  have hpA : ∀ y, pairing F n y ∘ₗ (A : V F n →ₗ[F] V F n) = pairing F n (A.symm y) := by
    intro y
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [← hA (A.symm y) v, LinearEquiv.apply_symm_apply]
  rw [← sub_eq_zero]
  apply s4_eq_zero_of_pair2 F n
  · exact Submodule.sub_mem _ (s4_map_mem_pow _ 2 z hz) hz
  · intro x y
    rw [map_sub, map_sub, map_sub, s4_pair2_map, hpA, hpA, hspec, hspec, hB, sub_self]

section BCcontract
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s4_contract_bcExt (d : Module.Dual F (V F n)) (d' : Module.Dual F' (V F' n))
    (hd : ∀ v, d' (bcV F F' n v) = algebraMap F F' (d v)) (z : ExteriorAlgebra F (V F n)) :
    contractLeft (Q := 0) d' (bcExt F F' n z) = bcExt F F' n (contractLeft (Q := 0) d z) := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExteriorAlgebra F' (V F' n)),
      contractLeft_algebraMap, contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    rw [map_mul, show bcExt F F' n (CliffordAlgebra.ι 0 m) = CliffordAlgebra.ι 0 (bcV F F' n m) from
      s4_bcExt_ι F F' n m, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_sub, map_smul, map_mul,
      show bcExt F F' n (CliffordAlgebra.ι 0 m) = CliffordAlgebra.ι 0 (bcV F F' n m) from
      s4_bcExt_ι F F' n m, hd, algebraMap_smul]

theorem s4_algebraMapInv_bcExt (z : ExteriorAlgebra F (V F n)) :
    ExteriorAlgebra.algebraMapInv (bcExt F F' n z) =
      algebraMap F F' (ExteriorAlgebra.algebraMapInv z) := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExteriorAlgebra F' (V F' n))]
    simp
  | ι x => rw [s4_bcExt_ι, s4_algebraMapInv_ι, s4_algebraMapInv_ι, map_zero]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end BCcontract


section PQ
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem s4_pqPiece_mul (A B : Submodule R M) (p q p' q' : ℕ) (x y : ExteriorAlgebra R M)
    (hx : x ∈ pqPiece A B p q) (hy : y ∈ pqPiece A B p' q') :
    x * y ∈ pqPiece A B (p + p') (q + q') := by
  have hle : pqPiece A B p q * pqPiece A B p' q' ≤ pqPiece A B (p + p') (q + q') := by
    rw [pqPiece, pqPiece, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨s, ⟨a, b, ha, hb, rfl⟩, t, ⟨a', b', ha', hb', rfl⟩, rfl⟩
    have e : ExteriorAlgebra.ιMulti R p a * ExteriorAlgebra.ιMulti R q b *
        (ExteriorAlgebra.ιMulti R p' a' * ExteriorAlgebra.ιMulti R q' b') =
        ((-1 : ℤˣ) ^ (p' * q)) • (ExteriorAlgebra.ιMulti R (p + p') (Fin.append a a') *
          ExteriorAlgebra.ιMulti R (q + q') (Fin.append b b')) := by
      rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ExteriorAlgebra.ιMulti_mul_ιMulti, mul_assoc,
        ← mul_assoc (ExteriorAlgebra.ιMulti R q b), ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm,
        smul_mul_assoc, mul_smul_comm]
      simp only [mul_assoc]
    dsimp only
    rw [e]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨Fin.append a a', Fin.append b b',
      fun i => ?_, fun j => ?_, rfl⟩)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact ha i
      · rw [Fin.append_right]; exact ha' i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact hb i
      · rw [Fin.append_right]; exact hb' i
  exact hle (Submodule.mul_mem_mul hx hy)

theorem s4_one_mem_pqPiece (A B : Submodule R M) : (1 : ExteriorAlgebra R M) ∈ pqPiece A B 0 0 :=
  Submodule.subset_span ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

end PQ

theorem s4_hodge_mul {n : ℕ} (I : Module.End ℝ (V ℝ n)) (p q : ℕ) (a b : ExteriorAlgebra ℚ (V ℚ n))
    (ha : a ∈ hodgeClassesV n I p) (hb : b ∈ hodgeClassesV n I q) :
    a * b ∈ hodgeClassesV n I (p + q) := by
  rw [mem_hodgeClassesV_iff] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · show a * b ∈ (LinearMap.range (ExteriorAlgebra.ι ℚ)) ^ (2 * (p + q))
    rw [show 2 * (p + q) = 2 * p + 2 * q by ring, pow_add]
    exact Submodule.mul_mem_mul ha.1 hb.1
  · rw [map_mul]
    exact s4_pqPiece_mul _ _ p p q q _ _ ha.2 hb.2

theorem s4_hodge_pow {n : ℕ} (I : Module.End ℝ (V ℝ n)) (ω : ExteriorAlgebra ℚ (V ℚ n))
    (hω : ω ∈ hodgeClassesV n I 1) (j : ℕ) : ω ^ j ∈ hodgeClassesV n I j := by
  induction j with
  | zero =>
    rw [pow_zero, mem_hodgeClassesV_iff]
    refine ⟨?_, ?_⟩
    · show (1 : ExteriorAlgebra ℚ (V ℚ n)) ∈ (LinearMap.range (ExteriorAlgebra.ι ℚ)) ^ (2 * 0)
      rw [mul_zero, pow_zero]
      exact Submodule.one_le.mp le_rfl
    · rw [map_one]; exact s4_one_mem_pqPiece _ _
  | succ j ih =>
    rw [pow_succ]
    exact s4_hodge_mul I j 1 _ _ ih hω

/-- Degree-`0` classes are Hodge classes. -/
theorem s4_hodge_zero {n : ℕ} (I : Module.End ℝ (V ℝ n)) (a : ExteriorAlgebra ℚ (V ℚ n))
    (ha : a ∈ ⋀[ℚ]^0 (V ℚ n)) : a ∈ hodgeClassesV n I 0 := by
  rw [mem_hodgeClassesV_iff]
  refine ⟨ha, ?_⟩
  have ha' : a ∈ (1 : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n))) := by
    have : ⋀[ℚ]^0 (V ℚ n) = 1 := pow_zero _
    rwa [this] at ha
  obtain ⟨r, rfl⟩ := (Submodule.mem_one).mp ha'
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_of_tower_mem _ r (s4_one_mem_pqPiece _ _)

/-- Vector-valued version of `AlternatingMap.eq_smul_basis_det`. -/
theorem s4_alternating_eq_det_smul {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Free K N] [DecidableEq ι] [Fintype ι]
    (e : Module.Basis ι K M) (f : M [⋀^ι]→ₗ[K] N) (v : ι → M) : f v = e.det v • f e := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).mp fun φ => ?_
  have h := AlternatingMap.eq_smul_basis_det e (φ.compAlternatingMap f)
  have hv := congrArg (fun g : M [⋀^ι]→ₗ[K] K => g v) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at hv
  rw [map_sub, map_smul, hv, smul_eq_mul, mul_comm, sub_self]

/-- The top degree `⋀^{4n} V_ℂ` is of type `(2n, 2n)` when `dim V^{1,0} = dim V^{0,1} = 2n`. -/
theorem s4_top_le_pqPiece {n : ℕ} (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (h10 : Module.finrank ℂ (V10 n I) = 2 * n) (h01 : Module.finrank ℂ (V01 n I) = 2 * n) :
    ⋀[ℂ]^(2 * n + 2 * n) (V ℂ n) ≤ pqPiece (V10 n I) (V01 n I) (2 * n) (2 * n) := by
  set b10 := Module.finBasisOfFinrankEq ℂ (V10 n I) h10
  set b01 := Module.finBasisOfFinrankEq ℂ (V01 n I) h01
  set B := ((b10.prod b01).map (Submodule.prodEquivOfIsCompl _ _ (s4_isCompl_V10_V01 n I hI))).reindex
    finSumFinEquiv
  have hB : (⇑B : Fin (2 * n + 2 * n) → V ℂ n) =
      Fin.append (fun i => (b10 i : V ℂ n)) (fun i => (b01 i : V ℂ n)) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left, ← finSumFinEquiv_apply_left, Module.Basis.reindex_apply,
        Equiv.symm_apply_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
      simp
    · rw [Fin.append_right, ← finSumFinEquiv_apply_right, Module.Basis.reindex_apply,
        Equiv.symm_apply_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
      simp
  have htop : ExteriorAlgebra.ιMulti ℂ (2 * n + 2 * n) B ∈ pqPiece (V10 n I) (V01 n I) (2 * n) (2 * n) := by
    rw [hB, ← ExteriorAlgebra.ιMulti_mul_ιMulti]
    exact Submodule.subset_span ⟨_, _, fun i => (b10 i).2, fun j => (b01 j).2, rfl⟩
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have : Module.Free ℂ (ExteriorAlgebra ℂ (V ℂ n)) := Module.Free.of_basis (basisExt ℂ n)
  rw [s4_alternating_eq_det_smul B (ExteriorAlgebra.ιMulti ℂ (2 * n + 2 * n)) v]
  exact Submodule.smul_mem _ _ htop

/-- Top-degree classes are Hodge classes (for `I` with `dim V^{1,0} = dim V^{0,1} = 2n`). -/
theorem s4_hodge_top {n : ℕ} (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (h10 : Module.finrank ℂ (V10 n I) = 2 * n) (h01 : Module.finrank ℂ (V01 n I) = 2 * n)
    (a : ExteriorAlgebra ℚ (V ℚ n)) (ha : a ∈ ⋀[ℚ]^(2 * (2 * n)) (V ℚ n)) :
    a ∈ hodgeClassesV n I (2 * n) := by
  rw [mem_hodgeClassesV_iff]
  refine ⟨ha, s4_top_le_pqPiece I hI h10 h01 ?_⟩
  have := s4_bcExt_mem_pow ℚ ℂ n _ a ha
  rwa [show 2 * (2 * n) = 2 * n + 2 * n by ring] at this



/-- `⋀A` acts on `⋀^k W` (`k = dim W`, `A(W) ⊆ W`) by `det(A|_W)`. -/
theorem s4_map_ιMulti_det {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Module.Free K (ExteriorAlgebra K M)] (W : Submodule K M) [FiniteDimensional K W] (k : ℕ)
    (hk : Module.finrank K W = k) (A : M →ₗ[K] M) (hA : ∀ x ∈ W, A x ∈ W) (v : Fin k → M)
    (hv : ∀ i, v i ∈ W) :
    ExteriorAlgebra.map A (ExteriorAlgebra.ιMulti K k v) =
      LinearMap.det (A.restrict hA) • ExteriorAlgebra.ιMulti K k v := by
  set b := Module.finBasisOfFinrankEq K W hk
  set u : Fin k → W := fun i => ⟨v i, hv i⟩
  set f : W [⋀^Fin k]→ₗ[K] ExteriorAlgebra K M :=
    (ExteriorAlgebra.ιMulti K k).compLinearMap W.subtype
  have hfu : ExteriorAlgebra.ιMulti K k v = f u := rfl
  have hAu : ExteriorAlgebra.map A (ExteriorAlgebra.ιMulti K k v) = f (A.restrict hA ∘ u) := by
    rw [ExteriorAlgebra.map_apply_ιMulti]
    rfl
  rw [hAu, hfu, s4_alternating_eq_det_smul b f, s4_alternating_eq_det_smul b f u,
    Module.Basis.det_comp, mul_smul]

/-- Naturality `⋀ A_{F'} ∘ bc = bc ∘ ⋀ A`. -/
theorem s4_map_extEnd_bcExt' (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (n : ℕ) (A : Module.End F (V F n)) (x : ExteriorAlgebra F (V F n)) :
    ExteriorAlgebra.map (s4_extEnd F F' n A) (bcExt F F' n x) =
      bcExt F F' n (ExteriorAlgebra.map A x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      AlgHom.map_smul_of_tower, map_one]
  | ι v => rw [s4_bcExt_ι, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, s4_bcExt_ι,
      s4_extEnd_bcV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

namespace KSecant
variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- `Ξ_P^♯` lies in `⋀² V_ℚ`. -/
theorem s4_hClass_mem (hW : IsCompl P.W₁ P.W₂) : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) :=
  formToExt2_mem ℚ n (P.XiQ hW)

/-- `Ξ_P^♯ ≠ 0` (`Ξ_P` is non-degenerate and `V ≠ 0`). -/
theorem s4_hClass_ne_zero (hW : IsCompl P.W₁ P.W₂) : P.hClass hW ≠ 0 := by
  intro h0
  have hX : ∀ x y, P.XiQ hW x y = 0 := by
    intro x y
    rw [← P.hClass_spec hW x y, h0, map_zero, map_zero, map_zero]
  have hn : 0 < n := s4_n_pos P
  have : Nontrivial (V ℚ n) := ⟨⟨(0, Pi.single ⟨0, by omega⟩ 1), 0, by
    intro h; have := congrArg (fun v : V ℚ n => v.2 ⟨0, by omega⟩) h; simp at this⟩⟩
  exact (P.XiQ_nondegenerate hW).ne_zero (LinearMap.ext₂ hX)

/-- `Ξ_P^♯` is invariant under `Spin(V_ℚ)_P` (`ρ(g)` is an isometry commuting with `f`, Lemma 3.1.1). -/
theorem s4_rhoExt_hClass (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (g : Spin ℚ n)
    (hg : g ∈ P.spinPℚ) : rhoExt ℚ n g (P.hClass hP.isCompl) = P.hClass hP.isCompl := by
  have hiso := s4_pairing_of_mem_SOplus (rho ℚ n g) (s4_rho_mem_SOplus g)
  have hSO : rho ℚ n g ∈ P.SOplusf hP.isCompl := by
    have : rho ℚ n g ∈ (P.SOplusf hP.isCompl : Set (V ℚ n ≃ₗ[ℚ] V ℚ n)) := by
      rw [← (lemma3_1_1 P J hP).2]; exact ⟨g, hg, rfl⟩
    exact this
  have hc : ∀ x, rho ℚ n g (P.fη hP.isCompl x) = P.fη hP.isCompl (rho ℚ n g x) := hSO.2.1
  refine s4_map_eq_of_spec n (rho ℚ n g) hiso (fun x y => P.XiQ hP.isCompl x y)
    (fun x y => ?_) _ (P.s4_hClass_mem _) (P.hClass_spec _)
  have hc' : P.fη hP.isCompl ((rho ℚ n g).symm x) = (rho ℚ n g).symm (P.fη hP.isCompl x) := by
    apply (rho ℚ n g).injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  simp only [XiQ, LinearMap.BilinForm.compLeft_apply]
  rw [hc', ← hiso ((rho ℚ n g).symm _) ((rho ℚ n g).symm y), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- `⟪bc(Ξ_P^♯), (x,·) ∧ (y,·)⟫ = Ξ_P(x, y)` on `V_ℝ`. -/
theorem s4_hClass_spec_real (hW : IsCompl P.W₁ P.W₂) (x y : V ℝ n) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing ℝ n y)
      (contractLeft (Q := 0) (pairing ℝ n x) (bcExt ℚ ℝ n (P.hClass hW)))) = P.XiR hW x y := by
  set z := bcExt ℚ ℝ n (P.hClass hW)
  let Bz : LinearMap.BilinForm ℝ (V ℝ n) := LinearMap.mk₂ ℝ
    (fun x y => ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing ℝ n y)
      (contractLeft (Q := 0) (pairing ℝ n x) z)))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
  have hB : Bz = P.XiR hW := by
    refine LinearMap.BilinForm.ext_basis (basisV ℝ n) fun i j => ?_
    rw [← s4_bcV_basisV ℚ ℝ n i, ← s4_bcV_basisV ℚ ℝ n j]
    simp only [Bz, LinearMap.mk₂_apply, z]
    have hd : ∀ a : V ℚ n, ∀ v, pairing ℝ n (bcV ℚ ℝ n a) (bcV ℚ ℝ n v) =
        algebraMap ℚ ℝ (pairing ℚ n a v) := fun a v => s4_pairing_bcV n a v
    rw [s4_contract_bcExt ℚ ℝ n _ _ (hd _), s4_contract_bcExt ℚ ℝ n _ _ (hd _),
      s4_algebraMapInv_bcExt, P.hClass_spec, P.XiR_bcV]
    rfl
  have := congrArg (fun B : LinearMap.BilinForm ℝ (V ℝ n) => B x y) hB
  simpa [Bz] using this

/-- `Ξ_P^♯` is of type `(1,1)` for every `I ∈ Ω_P` (`I` is an isometry commuting with `f`). -/
theorem s4_hClass_hodge (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) :
    P.hClass hP.isCompl ∈ hodgeClassesV n I 1 := by
  have hcs : IsComplexStructure I := hI.2.1
  have hc : I * P.fR hP.isCompl = P.fR hP.isCompl * I := P.s4_comm_OmegaP hP.isCompl I hI
  obtain ⟨⟨g₀, hg₀, hg₀I⟩, -⟩ := hI
  have hiso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
    rw [← hg₀I]; exact s4_pairing_of_mem_SOplus g₀ hg₀.1
  have hII : I * I = -1 := hcs
  let A : V ℝ n ≃ₗ[ℝ] V ℝ n := LinearEquiv.ofLinearMap I (-I)
    (by rw [← Module.End.mul_eq_comp, mul_neg, hII, neg_neg]; rfl)
    (by rw [← Module.End.mul_eq_comp, neg_mul, hII, neg_neg]; rfl)
  rw [mem_hodgeClassesV_one_iff I hcs _ (P.s4_hClass_mem _)]
  refine s4_map_eq_of_spec n A hiso (fun x y => P.XiR hP.isCompl x y) (fun x y => ?_) _
    (s4_bcExt_mem_pow ℚ ℝ n 2 _ (P.s4_hClass_mem _)) (P.s4_hClass_spec_real _)
  have hfx : ∀ v, P.fR hP.isCompl (I v) = I (P.fR hP.isCompl v) := fun v => by
    have := congrArg (fun F => F v) hc
    simpa using this.symm
  show P.XiR hP.isCompl ((-I) x) ((-I) y) = P.XiR hP.isCompl x y
  simp only [XiR, LinearMap.BilinForm.compLeft_apply, LinearMap.neg_apply, map_neg,
    LinearMap.neg_apply, neg_neg, hfx, hiso]

theorem s4_algebraMap_Nm (z : Kd d) (hd : 0 < d) :
    algebraMap ℚ (Kd d) (Kd.Nm d z) = z * Kd.σ d z := by
  apply Subtype.ext
  show ((Kd.Nm d z : ℚ) : ℂ) = (z : ℂ) * (starRingEnd ℂ) (z : ℂ)
  exact Kd.coe_Nm hd z

theorem s4_Nm_σ (z : Kd d) (hd : 0 < d) : Kd.Nm d (Kd.σ d z) = Kd.Nm d z := by
  apply Rat.cast_injective (α := ℂ)
  rw [Kd.coe_Nm hd, Kd.coe_Nm hd, Kd.coe_σ, Complex.conj_conj, mul_comm]

theorem s4_η_algebraMap (hW : IsCompl P.W₁ P.W₂) (q : ℚ) :
    P.η hW (algebraMap ℚ (Kd d) q) = q • (1 : Module.End ℚ (V ℚ n)) := by
  have h := RingHom.map_rat_algebraMap (P.ηHom (s4_d_pos P) hW) q
  rw [Algebra.algebraMap_eq_smul_one (A := Module.End ℚ (V ℚ n))] at h
  exact h

theorem s4_η_adj (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (x z : V ℚ n) :
    pairing ℚ n (P.η hW (Kd.σ d l) x) z = pairing ℚ n x (P.η hW l z) := by
  have hd := s4_d_pos P
  by_cases hl : l = 0
  · subst hl
    rw [map_zero, P.η_zero hd hW]
    simp
  · have hN : Kd.Nm d l ≠ 0 := by
      intro h0
      have := Kd.coe_Nm hd l
      rw [h0, Rat.cast_zero] at this
      have hl' : (l : ℂ) ≠ 0 := fun h => hl (Subtype.ext h)
      exact (mul_ne_zero hl' ((map_ne_zero _).mpr hl')) this.symm
    have h := P.pairing_η hd hW l (P.η hW (Kd.σ d l) x) z
    rw [← Module.End.mul_apply, ← P.η_mul hd hW, ← s4_algebraMap_Nm l hd, s4_η_algebraMap,
      LinearMap.smul_apply, Module.End.one_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_left_cancel₀ hN h).symm

theorem s4_XiQ_η (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (x y : V ℚ n) :
    P.XiQ hW (P.η hW l x) (P.η hW l y) = Kd.Nm d l * P.XiQ hW x y := by
  have hd := s4_d_pos P
  simp only [XiQ, LinearMap.BilinForm.compLeft_apply]
  have hc : P.fη hW (P.η hW l x) = P.η hW l (P.fη hW x) := by
    simp only [fη]
    rw [← Module.End.mul_apply, ← P.η_mul hd hW, mul_comm (Kd.sqrtNeg d) l, P.η_mul hd hW,
      Module.End.mul_apply]
  rw [hc, P.pairing_η hd hW]

/-- `η_λ(Ξ_P^♯) = Nm(λ) Ξ_P^♯`. -/
theorem s4_map_η_hClass (hW : IsCompl P.W₁ P.W₂) (l : Kd d) :
    ExteriorAlgebra.map (P.η hW l) (P.hClass hW) = (Kd.Nm d l) • P.hClass hW := by
  rw [← sub_eq_zero]
  apply s4_eq_zero_of_pair2 ℚ n
  · exact Submodule.sub_mem _ (s4_map_mem_pow _ 2 _ (P.s4_hClass_mem hW))
      (Submodule.smul_mem _ _ (P.s4_hClass_mem hW))
  · intro x y
    have hpη : ∀ u, pairing ℚ n u ∘ₗ P.η hW l = pairing ℚ n (P.η hW (Kd.σ d l) u) := by
      intro u
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [s4_η_adj]
    rw [map_sub, map_sub, map_sub, s4_pair2_map, hpη, hpη, P.hClass_spec, map_smul, map_smul,
      map_smul, P.hClass_spec, s4_XiQ_η, s4_Nm_σ _ (s4_d_pos P), smul_eq_mul, sub_self]

theorem s4_extEnd_η_K (hW : IsCompl P.W₁ P.W₂) (l : Kd d) :
    s4_extEnd ℚ (Kd d) n (P.η hW l) = P.ηK hW l := by
  refine (basisV (Kd d) n).ext fun j => ?_
  rw [← s4_bcV_basisV ℚ (Kd d) n, s4_extEnd_bcV, ηK_bcV P (s4_d_pos P) hW]

/-- `⋀η_λ` acts on `Ξ_P^♯` (in `⋀² V_K`) by `λ σ(λ)`. -/
theorem s4_map_ηK_hClass (hW : IsCompl P.W₁ P.W₂) (l : Kd d) :
    ExteriorAlgebra.map (P.ηK hW l) (bcExt ℚ (Kd d) n (P.hClass hW)) =
      (l * Kd.σ d l) • bcExt ℚ (Kd d) n (P.hClass hW) := by
  rw [← s4_extEnd_η_K, s4_map_extEnd_bcExt', s4_map_η_hClass, map_smul,
    ← s4_algebraMap_Nm l (s4_d_pos P), algebraMap_smul]

theorem s4_topWedge_le {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (W : Submodule K M)
    (k : ℕ) : topWedge W k ≤ ⋀[K]^k M := by
  rw [topWedge, Submodule.span_le]
  rintro _ ⟨v, -, rfl⟩
  exact ExteriorAlgebra.ιMulti_range K k ⟨v, rfl⟩

/-- `ĤW_P ⊆ (⋀^{2n} V_ℚ)^{Spin(V)_P}`: `ρ(g)` has determinant `1` on `W₁` and `W₂` (Lemma 3.1.1). -/
theorem s4_hwPlane_le_invQ (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.hwPlane ≤ P.invQ (2 * n) := by
  intro x hx
  have hxK : bcExt ℚ (Kd d) n x ∈ topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) := hx
  have : Module.Free (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)) :=
    Module.Free.of_basis (basisExt (Kd d) n)
  refine ⟨?_, ?_⟩
  · refine s4_mem_of_map_mem (bcExt ℚ (Kd d) n).toLinearMap.toAddMonoidHom
      (fun i y hy => s4_bcExt_mem_pow ℚ (Kd d) n i y hy) (s4_bcExt_injective ℚ (Kd d) n) _ x ?_
    exact sup_le (s4_topWedge_le _ _) (s4_topWedge_le _ _) hxK
  · intro g hg
    have hgP : g ∈ P.spinPℚ := hg.2
    have hSO : rho ℚ n g ∈ P.SOplusf hP.isCompl := by
      have : rho ℚ n g ∈ (P.SOplusf hP.isCompl : Set (V ℚ n ≃ₗ[ℚ] V ℚ n)) := by
        rw [← (lemma3_1_1 P J hP).2]; exact ⟨g, hgP, rfl⟩
      exact this
    obtain ⟨-, -, ⟨h1, hdet1⟩, ⟨h2, hdet2⟩⟩ := hSO
    have hfix : ∀ y ∈ topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n),
        ExteriorAlgebra.map (bcEndV (Kd d) n (rho ℚ n g : V ℚ n →ₗ[ℚ] V ℚ n)) y = y := by
      intro y hy
      have hle : topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) ≤ Module.End.eigenspace
          (ExteriorAlgebra.map (bcEndV (Kd d) n (rho ℚ n g : V ℚ n →ₗ[ℚ] V ℚ n))).toLinearMap 1 := by
        refine sup_le ?_ ?_
        · rw [topWedge, Submodule.span_le]
          rintro _ ⟨v, hv, rfl⟩
          rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply,
            s4_map_ιMulti_det P.W₁ (2 * n) P.isPure.2.2 _ h1 v hv, hdet1]
        · rw [topWedge, Submodule.span_le]
          rintro _ ⟨v, hv, rfl⟩
          rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply,
            s4_map_ιMulti_det P.W₂ (2 * n) P.isPure₂.2.2 _ h2 v hv, hdet2]
      have := Module.End.mem_eigenspace_iff.mp (hle hy)
      rwa [one_smul] at this
    apply s4_bcExt_injective ℚ (Kd d) n
    show bcExt ℚ (Kd d) n (ExteriorAlgebra.map (rho ℚ n g : V ℚ n →ₗ[ℚ] V ℚ n) x) = _
    rw [← s4_map_extEnd_bcExt']
    exact hfix _ hxK

theorem s4_pow_mem_exterior {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (x : ExteriorAlgebra K M) (hx : x ∈ ⋀[K]^2 M) (j : ℕ) : x ^ j ∈ ⋀[K]^(2 * j) M := by
  have := Submodule.pow_mem_pow _ hx j
  show _ ∈ (LinearMap.range (ExteriorAlgebra.ι K : M →ₗ[K] _)) ^ (2 * j)
  rwa [pow_mul]

/-- `(Ξ_P^♯)^n` has `K`-weight `(n, n)`: it lies in `⋀^n W₁ ⊗ ⋀^n W₂`. -/
theorem s4_pow_hClass_mem_pq (hW : IsCompl P.W₁ P.W₂) :
    bcExt ℚ (Kd d) n (P.hClass hW ^ n) ∈ pqPiece P.W₁ P.W₂ n n := by
  rw [← P.wedgeAB_eq (s4_d_pos P) hW]
  refine ⟨?_, fun l hl => ?_⟩
  · have := s4_bcExt_mem_pow ℚ (Kd d) n _ _ (s4_pow_mem_exterior _ (P.s4_hClass_mem hW) n)
    rw [show n + n = 2 * n by ring]
    exact this
  · show ExteriorAlgebra.map (P.ηK hW l) (bcExt ℚ (Kd d) n (P.hClass hW ^ n)) =
      (l ^ (n : ℤ) * Kd.σ d l ^ (n : ℤ)) • bcExt ℚ (Kd d) n (P.hClass hW ^ n)
    rw [map_pow, map_pow, s4_map_ηK_hClass, smul_pow, zpow_natCast, zpow_natCast, mul_pow]

theorem s4_topWedge_le_pq₁ (k : ℕ) : topWedge P.W₁ k ≤ pqPiece P.W₁ P.W₂ k 0 := by
  rw [topWedge, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine Submodule.subset_span ⟨v, Fin.elim0, hv, fun i => i.elim0, ?_⟩
  rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem s4_topWedge_le_pq₂ (k : ℕ) : topWedge P.W₂ k ≤ pqPiece P.W₁ P.W₂ 0 k := by
  rw [topWedge, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine Submodule.subset_span ⟨Fin.elim0, v, fun i => i.elim0, hv, ?_⟩
  rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul]

/-- `(Ξ_P^♯)^n ∉ ĤW_P` (they have different `K`-weights). -/
theorem s4_pow_hClass_not_mem (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.hClass hP.isCompl ^ n ∉ P.hwPlane := by
  have hd := hP.pos
  have hn : 0 < n := s4_n_pos P
  set ω := P.hClass hP.isCompl
  have hωQ : ω ∈ P.invQ 2 := ⟨P.s4_hClass_mem _, fun g hg => P.s4_rhoExt_hClass J hP g hg.2⟩
  have hpow0 : ω ^ n ≠ 0 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      rw [pow_one]; exact P.s4_hClass_ne_zero _
    · intro h0
      apply (lemma2_2_7_note P hd h hP.nonIsotropic ω hωQ (P.s4_hClass_ne_zero _)).1
      have e : ω ^ (2 * n) = ω ^ n * ω ^ n := by rw [← pow_add]; congr 1; omega
      rw [e, h0, zero_mul]
  intro hmem
  have h1 : bcExt ℚ (Kd d) n (ω ^ n) ∈ pqPiece P.W₁ P.W₂ n n := P.s4_pow_hClass_mem_pq _
  have h2 : bcExt ℚ (Kd d) n (ω ^ n) ∈ pqPiece P.W₁ P.W₂ (2 * n) 0 ⊔ pqPiece P.W₁ P.W₂ 0 (2 * n) :=
    sup_le_sup (P.s4_topWedge_le_pq₁ _) (P.s4_topWedge_le_pq₂ _) hmem
  obtain ⟨hind, -⟩ := P.wedge_decomp hd hP.isCompl (2 * n)
  have hdisj := hind.disjoint_biSup (x := ⟨n, by omega⟩)
    (y := {⟨2 * n, by omega⟩, ⟨0, by omega⟩}) (by
      intro hy
      rcases hy with hy | hy
      · have := congrArg Fin.val hy; simp at this; omega
      · have := congrArg Fin.val (Set.mem_singleton_iff.mp hy); simp at this; omega)
  rw [iSup_insert, iSup_singleton] at hdisj
  simp only [show 2 * n - n = n by omega, show 2 * n - 2 * n = 0 by omega, Nat.sub_zero] at hdisj
  have h0 : bcExt ℚ (Kd d) n (ω ^ n) = 0 := hdisj.le_bot ⟨h1, h2⟩
  exact hpow0 (s4_bcExt_injective ℚ (Kd d) n (by rw [h0, map_zero]))

/-- The middle degree: `(⋀^{2n} V_ℚ)^{Spin(V)_P} = ĤW_P ⊕ ℚ (Ξ_P^♯)^n` (Lemma 2.2.7). -/
theorem s4_invQ_middle (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.invQ (2 * n) ≤ P.hwPlane ⊔ ℚ ∙ (P.hClass hP.isCompl ^ n) := by
  have hd := hP.pos
  set ω := P.hClass hP.isCompl
  have hωQ : ω ∈ P.invQ 2 := ⟨P.s4_hClass_mem _, fun g hg => P.s4_rhoExt_hClass J hP g hg.2⟩
  have hpowQ : ω ^ n ∈ P.invQ (2 * n) := by
    refine ⟨s4_pow_mem_exterior _ (P.s4_hClass_mem _) n, fun g hg => ?_⟩
    rw [map_pow, hωQ.2 g hg]
  have hle : P.hwPlane ⊔ ℚ ∙ (ω ^ n) ≤ P.invQ (2 * n) :=
    sup_le (P.s4_hwPlane_le_invQ J hP) ((Submodule.span_singleton_le_iff_mem _ _).mpr hpowQ)
  have hnot := P.s4_pow_hClass_not_mem J hP
  have hpow0 : ω ^ n ≠ 0 := fun h => hnot (h ▸ zero_mem _)
  have : Module.Finite ℚ (ExteriorAlgebra ℚ (V ℚ n)) := Module.Finite.of_basis (basisExt ℚ n)
  have hinf : P.hwPlane ⊓ ℚ ∙ (ω ^ n) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx1) hnot
  have hfin : Module.finrank ℚ ↥(P.hwPlane ⊔ ℚ ∙ (ω ^ n)) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P.hwPlane (ℚ ∙ (ω ^ n))
    rw [hinf, finrank_bot, add_zero, P.finrank_hwPlane J hP, finrank_span_singleton hpow0] at h
    omega
  rw [Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hfin, lemma2_2_7_middle P hd hP.nonIsotropic])]

/-- For `I ∈ Ω_P`, `dim V^{1,0} = dim V^{0,1} = 2n`. -/
theorem s4_finrank_V10_V01_OmegaP (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hW) :
    Module.finrank ℂ (V10 n I) = 2 * n ∧ Module.finrank ℂ (V01 n I) = 2 * n := by
  have hcs : IsComplexStructure I := hI.2.1
  have hc : I * P.fR hW = P.fR hW * I := P.s4_comm_OmegaP hW I hI
  obtain ⟨-, -, hE1, hE2, -⟩ := hI
  have hfr4 := P.s4_finrank_four hW I hc hE1 hE2
  have hV10 : Module.finrank ℂ (V10 n I) = 2 * n := by
    have hsplit := P.s4_V10_split hW I hc
    have hdisj : V10 n I ⊓ P.W₁ℂ ⊓ (V10 n I ⊓ P.W₂ℂ) = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      exact (s4_isCompl_Wℂ P hW).1.le_bot ⟨hx.1.2, hx.2.2⟩
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (V10 n I ⊓ P.W₁ℂ) (V10 n I ⊓ P.W₂ℂ)
    rw [hdisj, finrank_bot, ← hsplit, hfr4.1, hfr4.2.2.1] at h3
    omega
  refine ⟨hV10, ?_⟩
  have h := Submodule.finrank_add_eq_of_isCompl (s4_isCompl_V10_V01 n I hcs)
  rw [hV10, s4_finrank_Vℂ] at h
  omega

end KSecant

/-- **Corollary 4.0.4** (`corollary-Spin-V-P-invariant-classes-are-Hodge`). The classes in
`(⋀* V_ℚ)^{Spin(V)_P}` remain of Hodge type for every complex structure in `Ω_P`.

`Spin(V)_P` is the integral group `SpinZ n ⊓ Spin(V_ℚ)_P` acting on `⋀• V_ℚ = H*(X × X̂, ℚ)` by
`ρ` (`rhoExt`); "of Hodge type" means a sum of rational `(p,p)`-classes (`hodgeRingV`). Standing
assumption: Assumption 2.4.1.

Proof as in the paper, degree by degree, via Lemma 2.2.7 (the invariants are `ℚ` in degree `0`, the
powers `(Ξ_P^♯)^j` in degree `2j ≠ 2n`, `ĤW_P ⊕ ℚ (Ξ_P^♯)^n` in degree `2n`, the top degree, and
`0` in odd degrees) and Lemma 4.0.3(1) (`ĤW_P` consists of Hodge classes). The paper's step "Hence the
statement holds for classes in `⋀²(V_ℚ)^{Spin(V)_P}`" (a class is of type `(1,1)` iff `I(α) = α`)
tacitly uses that these classes are fixed by `I`, i.e. by the real group; we justify it instead
directly: the invariant `⋀²` is spanned by `Ξ_P^♯` (Lemma 2.2.7), and `Ξ_P^♯` is of type `(1,1)`
for every `I ∈ Ω_P` since `I` is an isometry commuting with `f` (`KSecant.s4_hClass_hodge`). -/
theorem corollary4_0_4 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (α : ExteriorAlgebra ℚ (V ℚ n)) (hα : ∀ g ∈ SpinZ n ⊓ P.spinPℚ, rhoExt ℚ n g α = α)
    (I : Module.End ℝ (V ℝ n)) (hI : I ∈ P.OmegaP hP.isCompl) : α ∈ hodgeRingV n I := by
  have hd := hP.pos
  have hn : 0 < n := KSecant.s4_n_pos P
  set ω := P.hClass hP.isCompl
  have hωQ : ω ∈ P.invQ 2 :=
    ⟨P.s4_hClass_mem _, fun g hg => P.s4_rhoExt_hClass J hP g hg.2⟩
  have hω0 : ω ≠ 0 := P.s4_hClass_ne_zero _
  have hωH : ω ∈ hodgeClassesV n I 1 := P.s4_hClass_hodge J hP I hI
  have hcs : IsComplexStructure I := hI.2.1
  obtain ⟨h10, h01⟩ := P.s4_finrank_V10_V01_OmegaP hP.isCompl I hI
  have : Module.Finite ℚ (ExteriorAlgebra ℚ (V ℚ n)) := Module.Finite.of_basis (basisExt ℚ n)
  -- the graded components of `α` are invariant
  have hinvk : ∀ k, s4_proj ℚ (V ℚ n) k α ∈ P.invQ k := by
    intro k
    refine ⟨s4_proj_mem k α, fun g hg => ?_⟩
    have h := s4_proj_comm (rhoExt ℚ n g).toLinearMap.toAddMonoidHom
      (fun i x hx => s4_map_mem_pow _ i x hx) k α
    simp only [LinearMap.toAddMonoidHom_coe, AlgHom.toLinearMap_apply] at h
    rw [hα g hg] at h
    exact h.symm
  have hcomp : ∀ k, s4_proj ℚ (V ℚ n) k α ∈ hodgeRingV n I := by
    intro k
    have hx := hinvk k
    rcases Nat.even_or_odd k with hev | hodd
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by obtain ⟨m, hm⟩ := hev; omega⟩
      refine Submodule.mem_iSup_of_mem j ?_
      by_cases hj0 : j = 0
      · subst hj0
        exact s4_hodge_zero I _ hx.1
      by_cases hjbig : 2 * n < j
      · have hbot : ⋀[ℚ]^(2 * j) (V ℚ n) = ⊥ := by
          rw [← Submodule.finrank_eq_zero, exteriorPower.finrank_eq,
            Module.finrank_eq_card_basis (basisV ℚ n), Fintype.card_fin]
          exact Nat.choose_eq_zero_of_lt (by omega)
        have h1 : s4_proj ℚ (V ℚ n) (2 * j) α ∈ ⋀[ℚ]^(2 * j) (V ℚ n) := hx.1
        rw [hbot, Submodule.mem_bot] at h1
        rw [h1]; exact zero_mem _
      by_cases hjtop : j = 2 * n
      · subst hjtop
        exact s4_hodge_top I hcs h10 h01 _ hx.1
      by_cases hjmid : j = n
      · subst hjmid
        have hle : P.hwPlane ⊔ ℚ ∙ (ω ^ j) ≤ hodgeClassesV j I j :=
          sup_le (lemma4_0_3_hodgeWeil P J hP I hI)
            ((Submodule.span_singleton_le_iff_mem _ _).mpr (s4_hodge_pow I ω hωH j))
        exact hle (P.s4_invQ_middle J hP hx)
      · have hn2 : 2 ≤ n := by omega
        rw [lemma2_2_7_note_pow P hd hn2 hP.nonIsotropic ω hωQ hω0 j hjmid (by omega)] at hx
        exact (Submodule.span_singleton_le_iff_mem _ _).mpr (s4_hodge_pow I ω hωH j) hx
    · have h0 := lemma2_2_7_odd P hd hP.nonIsotropic k hodd
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0, Submodule.mem_bot] at hx
      rw [hx]; exact zero_mem _
  rw [← s4_sum_proj α]
  exact Submodule.sum_mem _ fun k _ => hcomp k


end WeilClasses
