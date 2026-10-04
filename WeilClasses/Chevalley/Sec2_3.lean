module

public import WeilClasses.Chevalley.Defs
public import WeilClasses.Correspondence.FourierMukai
public import WeilClasses.Spinor.Integral
public import WeilClasses.External.Chevalley.Sec2_2
public import WeilClasses.PureSpinor.Lemma2_2_6
public import WeilClasses.External.Chevalley.Sec2_3
public import WeilClasses.External.Trautman.Sec2_3
import WeilClasses.Orlov.Basis
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegralLattice

/-!
# §2.3: the isomorphism `φ̃ : S ⊗ S → ⋀•V`

Statements of the paper's §2.3 (TeX lines 1042–1222):

* the unnumbered claims about `ψ` (2.3.1): `(L'_x)² = ½(x, x)_V · 1` (`Lprime_sq`); `ψ(x) = ψ'(x)·1`
  (`psi_apply_eq_psiPrime`); `ψ` is a homomorphism (`psi_mul`) and an isomorphism (`psi_bijective`)
  of left `C(V)`-modules; `ψ(C(V)_k) ⊆ F^k(⋀•V)` (`psi_mem_extFiltLE`); the graded map
  `ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V` is an isomorphism (`psiBar_surjective`, `psiBar_injective`,
  [Chevalley, II.1.6]) and `Spin(V)`-equivariant (`conjSpin_mem_CFilt`, `psiBar_equivariant`,
  [Chevalley, Sec. 3.3]); the integral versions (`psi_image_CZ`);
* `φ̃ = ψ ∘ φ` (2.3.2) is an isomorphism (`varphiTilde_bijective`, integrally
  `varphiTilde_image_SZZ`);
  the `Spin(V)`-action transported by `φ̃` preserves `F^k(⋀•V)` with associated graded action `⋀ρ`,
  independent of `B₀` (`varphiTilde_transport_graded`, [Chevalley, p. 85]);
* Remark 2.3.1 (`remark2_3_1_*`);
* Lemma 2.3.2 (`lemma2_3_2_1`, `lemma2_3_2_2`).

The quotient `C(V)_k / C(V)_{k-1}` is not formed: `ψ̄_k(x mod C(V)_{k-1})` is the degree-`k`
component `projDeg k (ψ x)` of `ψ(x)` for `x ∈ C(V)_k`, and the bijectivity of `ψ̄_k` is stated as
surjectivity onto `⋀^k V` plus "kernel = `C(V)_{k-1}`".
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## Helpers: the grading and the filtrations -/

omit [CharZero F] in
theorem s23_pairing_apply (v w : V F n) : pairing F n v w = v.1 w.2 + w.1 v.2 := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q,
    QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

omit [CharZero F] in
theorem s23_projDeg_of_mem {k : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^k (V F n)) :
    projDeg F n k z = z :=
  DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) hz

omit [CharZero F] in
theorem s23_projDeg_of_mem_ne {i j : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^i (V F n)) (hij : i ≠ j) :
    projDeg F n j z = 0 :=
  DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) hz hij

omit [CharZero F] in
theorem s23_projDeg_mem (k : ℕ) (z : ExtV F n) : projDeg F n k z ∈ ⋀[F]^k (V F n) :=
  (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z k).2

omit [CharZero F] in
theorem s23_eq_zero_of_projDeg {z : ExtV F n} (h : ∀ j, projDeg F n j z = 0) : z = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) z]
  exact Finset.sum_eq_zero fun j _ => h j

omit [CharZero F] in
theorem s23_ext_projDeg {z z' : ExtV F n} (h : ∀ j, projDeg F n j z = projDeg F n j z') :
    z = z' :=
  sub_eq_zero.1 (s23_eq_zero_of_projDeg F n fun j => by rw [map_sub, h j, sub_self])

omit [CharZero F] in
/-- `F^k(⋀•V)` is the set of elements without components of degree `> k`. -/
theorem s23_mem_extFiltLE_iff (k : ℕ) (z : ExtV F n) :
    z ∈ extFiltLE F n k ↔ ∀ j, k < j → projDeg F n j z = 0 := by
  classical
  constructor
  · intro hz
    have hle : extFiltLE F n k ≤ ⨅ (j : ℕ) (_ : k < j), LinearMap.ker (projDeg F n j) :=
      iSup₂_le fun i hi y hy => by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker]
        intro j hj
        exact s23_projDeg_of_mem_ne F n hy (by omega)
    have := hle hz
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this
  · intro h
    rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) z]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hjk : j ≤ k
    · exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hjk
        (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z j).2)
    · have h0 := h j (lt_of_not_ge hjk)
      change projDeg F n j z ∈ _
      rw [h0]
      exact zero_mem _

omit [CharZero F] in
theorem s23_mem_extFiltLE_of_mem {i k : ℕ} (hik : i ≤ k) {z : ExtV F n}
    (hz : z ∈ ⋀[F]^i (V F n)) : z ∈ extFiltLE F n k :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hik hz)

omit [CharZero F] in
theorem s23_extFiltLE_mono {i k : ℕ} (hik : i ≤ k) : extFiltLE F n i ≤ extFiltLE F n k :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ≤ k) => ⋀[F]^j (V F n)) j
    (hj.trans hik) le_rfl

omit [CharZero F] in
theorem s23_projDeg_eq_zero_of_mem_extFiltLE {k j : ℕ} (hkj : k < j) {z : ExtV F n}
    (hz : z ∈ extFiltLE F n k) : projDeg F n j z = 0 :=
  (s23_mem_extFiltLE_iff F n k z).1 hz j hkj

omit [CharZero F] in
theorem s23_mem_extFiltLE_of_succ {k : ℕ} {z : ExtV F n} (hz : z ∈ extFiltLE F n (k + 1))
    (h0 : projDeg F n (k + 1) z = 0) : z ∈ extFiltLE F n k := by
  rw [s23_mem_extFiltLE_iff] at hz ⊢
  intro j hj
  rcases Nat.lt_or_ge (k + 1) j with h | h
  · exact hz j h
  · rw [show j = k + 1 by omega]; exact h0

omit [CharZero F] in
theorem s23_exists_mem_extFiltLE (z : ExtV F n) : ∃ k, z ∈ extFiltLE F n k := by
  classical
  refine ⟨(DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z).support.sup id, ?_⟩
  rw [s23_mem_extFiltLE_iff]
  intro j hj
  by_contra hne
  have hmem : j ∈ (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z).support := by
    rw [DFinsupp.mem_support_iff]
    intro h0
    exact hne (by change ((DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z j : _) :
      ExtV F n) = 0; rw [h0]; rfl)
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

omit [CharZero F] in
theorem s23_CFiltLT_succ (k : ℕ) : CFiltLT F n (k + 1) = CFilt F n k := by
  simp only [CFiltLT, CFilt, Nat.lt_succ_iff]

omit [CharZero F] in
theorem s23_CFiltLT_zero : CFiltLT F n 0 = ⊥ := by
  simp [CFiltLT]

omit [CharZero F] in
theorem s23_CFilt_mono {i k : ℕ} (hik : i ≤ k) : CFilt F n i ≤ CFilt F n k :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ≤ k) =>
    LinearMap.range (CliffordAlgebra.ι (Q F n)) ^ j) j (hj.trans hik) le_rfl

omit [CharZero F] in
theorem s23_exists_mem_CFilt (x : C F n) : ∃ k, x ∈ CFilt F n k := by
  have hx : x ∈ ⨆ i : ℕ, LinearMap.range (CliffordAlgebra.ι (Q F n)) ^ i := by
    rw [CliffordAlgebra.iSup_ι_range_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem i x hx => exact ⟨i, Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem le_rfl hx)⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨k', hk'⟩ := hy
    exact ⟨max k k', add_mem (s23_CFilt_mono F n (le_max_left k k') hk)
      (s23_CFilt_mono F n (le_max_right k k') hk')⟩

omit [CharZero F] in
/-- `F^k(⋀•V)` is Tau Ceti's degree filtration of `CliffordAlgebra 0 = ⋀•V`. -/
theorem s23_filtration_zero_eq (k : ℕ) :
    CliffordAlgebra.filtration (0 : QuadraticForm F (V F n)) k = extFiltLE F n k := by
  rw [CliffordAlgebra.filtration_eq_iSup_pow, extFiltLE, iSup_subtype']

omit [CharZero F] in
/-- The basis vectors `basisV` in coordinates: `f_i` and `e_i`. -/
theorem s23_basisV_inl (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inl i)) = ((f F n i, 0) : V F n) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  ext x
  · simp [f]
  · simp

omit [CharZero F] in
theorem s23_basisV_inr (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inr i)) = ((0, e F n i) : V F n) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  ext x
  · simp
  · simp [e]

omit [CharZero F] in
theorem s23_basisV_repr_inl (v : V F n) (i : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inl i)) = v.1 (e F n i) := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inl, Module.Basis.dualBasis_repr, Pi.basisFun_apply]
  rfl

omit [CharZero F] in
theorem s23_basisV_repr_inr (v : V F n) (i : Fin (2 * n)) :
    (basisV F n).repr v (finSumFinEquiv (Sum.inr i)) = v.2 i := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inr, Pi.basisFun_repr]

omit [CharZero F] in
/-- The basis vector `basisExt K` is the exterior product of the basis vectors indexed by `K`, in
increasing order. -/
theorem s23_basisExt_eq_prod (K : Finset (Fin (2 * n + 2 * n))) :
    ∃ l : List (V F n), l.length = K.card ∧ (∀ v ∈ l, ∃ j, v = basisV F n j) ∧
      basisExt F n K = (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod := by
  refine ⟨List.ofFn fun i => basisV F n ((Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.prodEquiv.symm K).2) i), by simp, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hv
    exact ⟨_, rfl⟩
  · rw [basisExt, ExteriorAlgebra.basis_apply]
    simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl

omit [CharZero F] in
theorem s23_basisExt_mem (K : Finset (Fin (2 * n + 2 * n))) :
    basisExt F n K ∈ ⋀[F]^K.card (V F n) := by
  obtain ⟨l, hl, -, hK⟩ := s23_basisExt_eq_prod F n K
  rw [hK, ← hl]
  exact CliffordAlgebra.prod_map_ι_mem_pow (0 : QuadraticForm F (V F n)) l

omit [CharZero F] in
/-- The coordinates of the degree-`j` component. -/
theorem s23_repr_projDeg (j : ℕ) (z : ExtV F n) (K : Finset (Fin (2 * n + 2 * n))) :
    (basisExt F n).repr (projDeg F n j z) K =
      if K.card = j then (basisExt F n).repr z K else 0 := by
  have h : ((basisExt F n).coord K) ∘ₗ projDeg F n j =
      if K.card = j then (basisExt F n).coord K else 0 := by
    refine (basisExt F n).ext fun K' => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply]
    by_cases hK' : K'.card = j
    · rw [← hK', s23_projDeg_of_mem F n (s23_basisExt_mem F n K')]
      split_ifs with hK
      · simp [Module.Basis.coord_apply]
      · simp only [Module.Basis.repr_self, LinearMap.zero_apply, Finsupp.single_apply]
        rw [ite_eq_right_iff.2]
        rintro rfl
        exact (hK rfl).elim
    · rw [s23_projDeg_of_mem_ne F n (s23_basisExt_mem F n K') hK', map_zero,
        Finsupp.zero_apply]
      split_ifs with hK
      · simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        rw [ite_eq_right_iff.2]
        rintro rfl
        exact (hK' hK).elim
      · rfl
  have := congrArg (fun φ : ExtV F n →ₗ[F] F => φ z) h
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

omit [CharZero F] in
/-- The leading term of `ψ` on a product of vectors (`ψ̄_k(v₁ ⋯ v_k) = v₁ ∧ ⋯ ∧ v_k`; Tau Ceti's
`changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration`). -/
theorem s23_psi_prod (l : List (V F n)) :
    psi F n (l.map (CliffordAlgebra.ι (Q F n))).prod -
        (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod ∈
      extFiltLE F n (l.length - 1) ∧
    (l.length = 0 → psi F n (l.map (CliffordAlgebra.ι (Q F n))).prod =
        (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod) := by
  refine ⟨?_, fun h0 => ?_⟩
  · rcases Nat.eq_zero_or_pos l.length with h | h
    · rw [List.length_eq_zero_iff.1 h]
      simp [psi]
    · rw [← s23_filtration_zero_eq]
      exact CliffordAlgebra.changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration (Q F n)
        (neg_B0_toQuadraticMap F n) l (by omega)
  · rw [List.length_eq_zero_iff.1 h0]
    simp [psi]

omit [CharZero F] in
theorem s23_psi_prod_mem (l : List (V F n)) :
    psi F n (l.map (CliffordAlgebra.ι (Q F n))).prod ∈ extFiltLE F n l.length ∧
      projDeg F n l.length (psi F n (l.map (CliffordAlgebra.ι (Q F n))).prod) =
        (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod := by
  have hwedge : (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod ∈
      ⋀[F]^l.length (V F n) := CliffordAlgebra.prod_map_ι_mem_pow _ l
  obtain ⟨hdiff, h0⟩ := s23_psi_prod F n l
  have hdiff' : psi F n (l.map (CliffordAlgebra.ι (Q F n))).prod -
      (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod ∈
      extFiltLE F n l.length := s23_extFiltLE_mono F n (Nat.sub_le _ _) hdiff
  refine ⟨?_, ?_⟩
  · simpa using add_mem hdiff' (s23_mem_extFiltLE_of_mem F n le_rfl hwedge)
  · rcases Nat.eq_zero_or_pos l.length with h | h
    · rw [h0 h, s23_projDeg_of_mem F n hwedge]
    · have := s23_projDeg_eq_zero_of_mem_extFiltLE F n (by omega : l.length - 1 < l.length) hdiff
      rw [map_sub, sub_eq_zero, s23_projDeg_of_mem F n hwedge] at this
      exact this

/-! ## The map `ψ` (2.3.1) -/

/-- (§2.3, TeX line 1052) `(L'_x)² = ½(x, x)_V · 1`, where `1` is the identity of `End(⋀•V)`. -/
theorem Lprime_sq (x : V F n) :
    Lprime F n x * Lprime F n x =
      ((2 : F)⁻¹ * pairing F n x x) • (1 : Module.End F (ExtV F n)) := by
  rw [Lprime_mul_self, Algebra.algebraMap_eq_smul_one, pairing, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc,
    inv_mul_cancel₀ (two_ne_zero' F), one_mul]

omit [CharZero F] in
/-- `ψ(v x) = L'_v(ψ(x))`: the defining recursion of `changeForm` for the form `-B₀`. -/
theorem s23_psi_ι_mul (v : V F n) (x : C F n) :
    psi F n (CliffordAlgebra.ι (Q F n) v * x) = Lprime F n v (psi F n x) := by
  rw [psi, changeForm_ι_mul, LinearMap.neg_apply, map_neg, LinearMap.neg_apply, sub_neg_eq_add]
  rfl

set_option linter.unusedSectionVars false in
/-- (§2.3, TeX line 1062) `ψ` is a homomorphism of left `C(V)`-modules, `C(V)` acting on `⋀•V`
through `ψ'`: `ψ(x y) = ψ'(x)(ψ(y))`. -/
theorem psi_mul (x y : C F n) : psi F n (x * y) = psiPrime F n x (psi F n y) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [← Algebra.smul_def, map_smul, AlgHom.commutes, Module.algebraMap_end_apply]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, LinearMap.add_apply]
  | ι_mul x v hx =>
    rw [mul_assoc, s23_psi_ι_mul, hx, map_mul, Module.End.mul_apply, psiPrime, lift_ι_apply]

/-- (2.3.1) The paper's definition of `ψ`: `ψ(x) = ψ'(x) · 1`, with `1 ∈ ⋀⁰V` the unit
(our `psi` is defined as `CliffordAlgebra.changeForm`, see `WeilClasses.Chevalley.Defs`). -/
theorem psi_apply_eq_psiPrime (x : C F n) : psi F n x = psiPrime F n x 1 := by
  rw [← mul_one x, psi_mul, mul_one, psi, changeForm_one]

/-- (§2.3, TeX line 1064) `ψ(C(V)_k) ⊆ F^k(⋀•V) = ⊕_{i ≤ k} ⋀^i V`. -/
theorem psi_mem_extFiltLE (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    psi F n x ∈ extFiltLE F n k :=
  chevalley_II_1_6_filtration F n (B0 F n) (neg_B0_toQuadraticMap F n) k hx

/-- (§2.3, TeX lines 1065–1069; [Chevalley, II.1.6]) The induced map
`ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V`, `x ↦ (degree-k component of ψ(x))`, is surjective. -/
theorem psiBar_surjective (k : ℕ) {y : ExtV F n} (hy : y ∈ ⋀[F]^k (V F n)) :
    ∃ x ∈ CFilt F n k, projDeg F n k (psi F n x) = y :=
  chevalley_II_1_6_surjective F n (B0 F n) (neg_B0_toQuadraticMap F n) k hy

/-- (§2.3, TeX lines 1065–1069; [Chevalley, II.1.6]) `ψ̄_k` is injective: for `x ∈ C(V)_k`, the
degree-`k` component of `ψ(x)` vanishes iff `x ∈ C(V)_{k-1}`. -/
theorem psiBar_injective (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (psi F n x) = 0 ↔ x ∈ CFiltLT F n k :=
  chevalley_II_1_6_injective F n (B0 F n) (neg_B0_toQuadraticMap F n) k hx

/-- (§2.3, TeX line 1069) `ψ : C(V) → ⋀•V` is an isomorphism (of left `C(V)`-modules, by
`psi_mul`). -/
theorem psi_bijective : Function.Bijective (psi F n) := by
  constructor
  · -- injectivity: `ψ(x) = 0` with `x ∈ C(V)_k` forces `x ∈ C(V)_{k-1}` (`ψ̄_k` injective), etc.
    have key : ∀ k, ∀ x ∈ CFilt F n k, psi F n x = 0 → x = 0 := by
      intro k
      induction k with
      | zero =>
        intro x hx h0
        have := (psiBar_injective F n 0 hx).1 (by rw [h0, map_zero])
        rwa [s23_CFiltLT_zero, Submodule.mem_bot] at this
      | succ k ih =>
        intro x hx h0
        have := (psiBar_injective F n (k + 1) hx).1 (by rw [h0, map_zero])
        rw [s23_CFiltLT_succ] at this
        exact ih x this h0
    intro x y hxy
    obtain ⟨k, hk⟩ := s23_exists_mem_CFilt F n (x - y)
    exact sub_eq_zero.1 (key k _ hk (by rw [map_sub, hxy, sub_self]))
  · -- surjectivity: lift the top component (`ψ̄_k` surjective) and induct on the filtration
    have key : ∀ k, ∀ y ∈ extFiltLE F n k, ∃ x, psi F n x = y := by
      intro k
      induction k with
      | zero =>
        intro y hy
        obtain ⟨x, hx, hxy⟩ := psiBar_surjective F n 0 (s23_projDeg_mem F n 0 y)
        refine ⟨x, s23_ext_projDeg F n fun j => ?_⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact hxy
        · rw [s23_projDeg_eq_zero_of_mem_extFiltLE F n hj (psi_mem_extFiltLE F n 0 hx),
            s23_projDeg_eq_zero_of_mem_extFiltLE F n hj hy]
      | succ k ih =>
        intro y hy
        obtain ⟨x, hx, hxy⟩ := psiBar_surjective F n (k + 1) (s23_projDeg_mem F n (k + 1) y)
        have hdiff : y - psi F n x ∈ extFiltLE F n k :=
          s23_mem_extFiltLE_of_succ F n (sub_mem hy (psi_mem_extFiltLE F n (k + 1) hx))
            (by rw [map_sub, hxy, sub_self])
        obtain ⟨x', hx'⟩ := ih _ hdiff
        exact ⟨x + x', by rw [map_add, hx', add_sub_cancel]⟩
    intro y
    obtain ⟨k, hk⟩ := s23_exists_mem_extFiltLE F n y
    exact key k y hk

/-- (§2.3, TeX line 1069; [Chevalley, Sec. 3.3]) The conjugation action of `Spin(V)` on `C(V)`
preserves the filtration `C(V)_k`. -/
theorem conjSpin_mem_CFilt (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    conjSpin F n g x ∈ CFilt F n k :=
  chevalley_sec3_3_conj_mem F n g k hx

/-- (§2.3, TeX line 1069; [Chevalley, Sec. 3.3]) `ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V` is
`Spin(V)`-equivariant, for the conjugation action on `C(V)` and the action `⋀^k ρ` on `⋀^k V`
induced from `V`. -/
theorem psiBar_equivariant (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (psi F n (conjSpin F n g x)) = rhoExt F n g (projDeg F n k (psi F n x)) :=
  chevalley_sec3_3_equivariant F n (B0 F n) (neg_B0_toQuadraticMap F n) g k hx

/-! ## The isomorphism `φ̃ = ψ ∘ φ` (2.3.2) -/

/-- (2.3.2) `φ̃ = ψ ∘ φ : S ⊗ S → ⋀•V` is an isomorphism ("the composite isomorphism"). -/
theorem varphiTilde_bijective : Function.Bijective (varphiTilde F n) :=
  (psi_bijective F n).comp (chevalley_III_3_1_bijective F n)

/-- (§2.3, TeX lines 1074–1077; [Chevalley, p. 85]) The `Spin(V)`-action on `⋀•V` obtained by
conjugating `m ⊗ m` with `φ̃` preserves the increasing filtration `F^k(⋀•V)`, and its associated
graded action is the action `⋀ρ` induced from `V`; in particular it does not depend on `B₀`. -/
theorem varphiTilde_transport_graded (g : Spin F n) (k : ℕ) (y : S F n ⊗[F] S F n)
    (hy : varphiTilde F n y ∈ extFiltLE F n k) :
    varphiTilde F n (TensorProduct.map (m F n g) (m F n g) y) ∈ extFiltLE F n k ∧
      projDeg F n k (varphiTilde F n (TensorProduct.map (m F n g) (m F n g) y)) =
        rhoExt F n g (projDeg F n k (varphiTilde F n y)) :=
  chevalley_p85_transport_graded F n (B0 F n) (neg_B0_toQuadraticMap F n) g k y hy

/-! ## Remark 2.3.1 -/

set_option linter.unusedSectionVars false in
/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`), first claim: the projection `B̄₀`
of `B₀` to `∧²V* = V* ⊗ V* / Sym²(V*)` (realized as the alternating part `½(B₀ - B₀ᵀ)`) is
`B̄₀((w₁, θ₁), (w₂, θ₂)) = ½(θ₂(w₁) - θ₁(w₂))` (our order: `vᵢ = (θᵢ, wᵢ)`). -/
theorem remark2_3_1_B0bar_apply (v₁ v₂ : V F n) :
    B0bar F n v₁ v₂ = (2 : F)⁻¹ * (v₂.1 v₁.2 - v₁.1 v₂.2) := by
  rw [B0bar_apply, B0_apply, B0_apply]

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`): the projection of `B₀` to
`∧²V*` equals that of `B₀ + (·,·)_V` (the pairing is symmetric). -/
theorem remark2_3_1_altPart_add_pairing : altPart F n (B0 F n + pairing F n) = B0bar F n := by
  refine LinearMap.ext₂ fun v₁ v₂ => ?_
  simp only [altPart, B0bar, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.BilinForm.flip_apply, s23_pairing_apply, smul_eq_mul]
  ring

/-- The decomposition `B₀ = ½(·,·)_V + B̄₀` into symmetric and alternating parts (Remark 2.3.1). -/
theorem B0_eq_half_pairing_add_B0bar : B0 F n = (2 : F)⁻¹ • pairing F n + B0bar F n := by
  refine LinearMap.ext₂ fun v₁ v₂ => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, B0bar_apply, B0_apply,
    s23_pairing_apply]
  ring

/-- The operator form of the identification of `B̄₀` with a multiple of `c₁(𝒫)` (Remark 2.3.1), the
form in which the proof of Proposition 6.1.2 uses it: under the isomorphism
`φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)` (Poincaré duality up to sign, Lemma 6.3.2), the change of
form by `B̄₀` on `⋀•V` (the exponential of contraction with `B̄₀`; `changeB0bar`) becomes cup product
with `exp(½c₁(𝒫))`. (Checked numerically for `n = 1, 2`.) Not a statement of the paper.
Proof (from the explicit transforms; prover P10, moved here by prover SD): in the basis of `V`,
`E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})` (`s61_changeB0bar_eq_G`),
`Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π` on the basis vectors `f_A ∧ e_B` (`s61_PiMap_D`), and
`exp(½ Σᵢ e_i ∧ f_i) = ∏ᵢ (1 + ½ e_i ∧ f_i)` (`s61_exp_list`); the helpers are in
`WeilClasses.Orlov.Basis`. -/
theorem PiMap_changeB0bar (x : ExtV F n) :
    PiMap F n (changeB0bar F n x) =
      IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) * PiMap F n x := by
  rw [s61_changeB0bar_eq_G, s61_PiMap_G, s61_c1P_eq, Fin.sum_univ_def, s61_exp_list]

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`), corrected: `B̄₀ = -½ c₁(𝒫)`. The
alternating form `B̄₀ ∈ ∧²V*` is identified with a class in `H²(X × X̂) = ∧²V` through the determinant
pairing induced by `(·,·)_V`, `⟨a ∧ b, x ∧ y⟩ = (a, x)_V (b, y)_V - (a, y)_V (b, x)_V`; the class
`c₁(𝒫) = Σ eᵢ ∧ fᵢ` is the alternating form `(v₁, v₂) ↦ θ₁(w₂) - θ₂(w₁) = -2 B̄₀(v₁, v₂)`.

**Correction of the paper** (agreed with the project owner; REPORT.md). The paper states
`B̄₀ = ½c₁(𝒫)` ([BL, Th. 2.5.1 and 2.6(2b)]), which holds only for the opposite sign of `c₁(𝒫)`.
The sign `c₁(𝒫) = +Σ eᵢ ∪ fᵢ` is forced by Lemma 6.3.1, Lemma 6.1.1 and Proposition 6.1.2, which
fail with the other sign (`WeilClasses.Correspondence.FourierMukai`); no sign makes all of the
paper's sign statements hold (compare Lemma 6.3.2). The operator form used in the proof of
Proposition 6.1.2 is `PiMap_changeB0bar`. -/
theorem remark2_3_1_B0bar_eq_neg_half_c1P (v₁ v₂ : V F n) :
    B0bar F n v₁ v₂ = -((2 : F)⁻¹ * extPairing F n (c1P F n)
        (ExteriorAlgebra.ι F v₁ * ExteriorAlgebra.ι F v₂)) := by
  -- `⟨c₁(𝒫), v₁ ∧ v₂⟩ = Σᵢ det((eᵢ, vⱼ)_V, (fᵢ, vⱼ)_V) = θ₁(w₂) - θ₂(w₁)`
  have hmem2 : ∀ a b : V F n, ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b ∈ ⋀[F]^2 (V F n) :=
    fun a b => by
      have := ExteriorAlgebra.ιMulti_range F (M := V F n) 2 ⟨![a, b], rfl⟩
      simpa [ExteriorAlgebra.ιMulti_apply] using this
  have hsub : ∀ a b : V F n, projDegSub F n 2 (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) =
      exteriorPower.ιMulti F 2 ![a, b] := by
    intro a b
    apply Subtype.ext
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    change (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n))
      (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) 2 : ExtV F n) = _
    rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) (hmem2 a b)]
    simp
  have hne : ∀ k ≠ 2, projDegSub F n k (ExteriorAlgebra.ι F v₁ * ExteriorAlgebra.ι F v₂) = 0 := by
    intro k hk
    apply Subtype.ext
    change (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n))
      (ExteriorAlgebra.ι F v₁ * ExteriorAlgebra.ι F v₂) k : ExtV F n) = _
    rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) (hmem2 v₁ v₂) (Ne.symm hk)]
    rfl
  have hc1P : c1P F n = ∑ i : Fin (2 * n), ExteriorAlgebra.ι F ((0, e F n i) : V F n) *
      ExteriorAlgebra.ι F ((f F n i, 0) : V F n) := by
    simp [c1P, pullX, pullXHat, ExteriorAlgebra.map_apply_ι]
  have hterm : ∀ i : Fin (2 * n), (pairing F n).exteriorPower 2
      (exteriorPower.ιMulti F 2 ![((0, e F n i) : V F n), ((f F n i, 0) : V F n)])
      (exteriorPower.ιMulti F 2 ![v₁, v₂]) = v₁.1 (e F n i) * v₂.2 i - v₂.1 (e F n i) * v₁.2 i := by
    intro i
    rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, Matrix.det_fin_two]
    simp [f]
    ring
  have hdual : ∀ (θ : Module.Dual F (H1 F n)) (w : H1 F n), ∑ i, θ (e F n i) * w i = θ w := by
    intro θ w
    conv_rhs => rw [show w = ∑ i, w i • e F n i by ext j; simp [e, Pi.single_apply]]
    simp [map_sum, mul_comm]
  have hext : extPairing F n (c1P F n) (ExteriorAlgebra.ι F v₁ * ExteriorAlgebra.ι F v₂) =
      v₁.1 v₂.2 - v₂.1 v₁.2 := by
    rw [extPairing, LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_eq_single 2]
    · simp only [LinearMap.compl₁₂_apply, hsub, hc1P, map_sum, LinearMap.sum_apply, hterm]
      rw [Finset.sum_sub_distrib, hdual]
      simp_rw [mul_comm (v₂.1 (e F n _)) (v₁.2 _)]
      rw [← hdual v₂.1 v₁.2]
      simp_rw [mul_comm (v₂.1 (e F n _)) (v₁.2 _)]
    · intro k _ hk
      simp [LinearMap.compl₁₂_apply, hne k hk]
    · intro h2
      have hn : n = 0 := by simp at h2; omega
      subst hn
      simp [c1P]
  rw [hext, B0bar_apply, B0_apply, B0_apply]
  ring

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`; [Trautman, Th. 1(i)]): with `B₀`
replaced by `½(·,·)_V` (over a field of characteristic zero), the resulting isomorphism
`S ⊗ S → ⋀•V` (`varphiTildeSym = equivExterior ∘ φ`) is `Spin(V)`-equivariant, for `m ⊗ m` on
`S ⊗ S` and the grading-preserving action `⋀ρ` on `⋀•V` induced by `V`.

Reading: the action of `Spin(V)` on `S ⊗ S = S_X ⊗ S_X` is `m ⊗ m`, the one for which `φ`
(2.2.5) is equivariant ([Chevalley, III.3.1]: `φ(m_g u ⊗ m_g v) = g φ(u ⊗ v) g⁻¹`). -/
theorem remark2_3_1_sym_equivariant (g : Spin F n) (y : S F n ⊗[F] S F n) :
    varphiTildeSym F n (TensorProduct.map (m F n g) (m F n g) y) =
      rhoExt F n g (varphiTildeSym F n y) :=
  trautman_theorem1_i F n g y

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`): the symmetric variant
`S ⊗ S → ⋀•V` is an isomorphism. -/
theorem remark2_3_1_sym_bijective : Function.Bijective (varphiTildeSym F n) :=
  (CliffordAlgebra.equivExterior (Q F n)).bijective.comp (chevalley_III_3_1_bijective F n)

omit [CharZero F] in
/-- `changeForm` depends only on the bilinear form. -/
theorem s23_changeForm_congr {M : Type*} [AddCommGroup M] [Module F M]
    {Q₁ Q₂ : QuadraticForm F M} {B B' : LinearMap.BilinForm F M} (hBB : B = B')
    (h : B.toQuadraticMap = Q₂ - Q₁) (h' : B'.toQuadraticMap = Q₂ - Q₁) :
    CliffordAlgebra.changeForm h = CliffordAlgebra.changeForm h' := by
  subst hBB; rfl

/-- (Remark 2.3.1; used for Prop. 6.1.2) Since `B₀ = ½(·,·)_V + B̄₀`, `ψ` is the symmetric `ψ`
followed by the change of form by `B̄₀` ([Bourbaki, §9 Lemma 3], Mathlib's
`CliffordAlgebra.changeForm_changeForm`): `ψ = changeB0bar ∘ psiSym`. -/
theorem psi_eq_changeB0bar_comp_psiSym : psi F n = changeB0bar F n ∘ₗ psiSym F n := by
  have hcomp : changeB0bar F n ∘ₗ psiSym F n =
      CliffordAlgebra.changeForm (changeForm.add_proof
        (changeForm.associated_neg_proof (Q := Q F n)) (neg_B0bar_toQuadraticMap F n)) :=
    changeForm_comp_changeForm (changeForm.associated_neg_proof (Q := Q F n))
      (neg_B0bar_toQuadraticMap F n)
  rw [hcomp, psi]
  -- the two bilinear forms agree: `B₀ = ½(·,·)_V + B̄₀`
  have hassoc : ∀ v₁ v₂ : V F n, QuadraticMap.associated (R := F) (-(Q F n)) v₁ v₂ =
      -((2 : F)⁻¹ * pairing F n v₁ v₂) := by
    intro v₁ v₂
    have h2 := congrArg (fun B : LinearMap.BilinForm F (V F n) => B v₁ v₂)
      (QuadraticMap.two_nsmul_associated F (-(Q F n)))
    simp only [two_nsmul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, neg_apply] at h2
    simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    change QuadraticMap.associatedHom F (-(Q F n)) v₁ v₂ = _
    linear_combination (2 : F)⁻¹ * h2
  have hB : QuadraticMap.associated (R := F) (-(Q F n)) + -B0bar F n = -B0 F n := by
    rw [B0_eq_half_pairing_add_B0bar]
    refine LinearMap.ext₂ fun v₁ v₂ => ?_
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
      hassoc]
    ring
  exact s23_changeForm_congr F hB.symm _ _

/-! ## Lemma 2.3.2 -/

/-! ### The graded map `ψ̄` is multiplicative on leading terms -/

omit [CharZero F] in
theorem s23_CFilt_eq (k : ℕ) : CFilt F n k = CliffordAlgebra.filtration (Q F n) k := by
  rw [CliffordAlgebra.filtration_eq_iSup_pow, CFilt, iSup_subtype']

omit [CharZero F] in
theorem s23_mul_mem_CFilt {a b : ℕ} {x y : C F n} (hx : x ∈ CFilt F n a) (hy : y ∈ CFilt F n b) :
    x * y ∈ CFilt F n (a + b) := by
  rw [s23_CFilt_eq] at hx hy ⊢
  exact CliffordAlgebra.mul_mem_filtration _ hx hy

omit [CharZero F] in
theorem s23_prod_mem_CFilt (l : List (V F n)) :
    (l.map (CliffordAlgebra.ι (Q F n))).prod ∈ CFilt F n l.length := by
  rw [s23_CFilt_eq]
  exact CliffordAlgebra.prod_map_ι_mem_filtration _ le_rfl

omit [CharZero F] in
/-- Exterior multiplication by a vector raises degrees by one. -/
theorem s23_projDeg_ι_mul (v : V F n) (j : ℕ) (z : ExtV F n) :
    projDeg F n (j + 1) (ExteriorAlgebra.ι F v * z) = ExteriorAlgebra.ι F v * projDeg F n j z := by
  have hz : z ∈ ⨆ i : ℕ, ⋀[F]^i (V F n) := by
    rw [(DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[F]^i (V F n))).submodule_iSup_eq_top]
    exact Submodule.mem_top
  induction hz using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  | mem i z hz =>
    have h1 : ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (V F n) := by
      show ExteriorAlgebra.ι F v ∈ LinearMap.range (ExteriorAlgebra.ι F) ^ 1
      rw [pow_one]
      exact LinearMap.mem_range_self _ v
    have hvz : ExteriorAlgebra.ι F v * z ∈ ⋀[F]^(i + 1) (V F n) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded h1 hz
    by_cases hij : i = j
    · subst hij
      rw [s23_projDeg_of_mem F n hvz, s23_projDeg_of_mem F n hz]
    · rw [s23_projDeg_of_mem_ne F n hvz (by omega), s23_projDeg_of_mem_ne F n hz hij, mul_zero]

omit [CharZero F] in
/-- Contraction preserves `F^k(⋀•V)`. -/
theorem s23_contractLeft_mem_extFiltLE (d : Module.Dual F (V F n)) {k : ℕ} {z : ExtV F n}
    (hz : z ∈ extFiltLE F n k) : contractLeft d z ∈ extFiltLE F n k := by
  rw [← s23_filtration_zero_eq] at hz ⊢
  exact CliffordAlgebra.contractLeft_mem_filtration _ d hz

/-- The leading term of `ψ(v₁ ⋯ v_m y)` is `v₁ ∧ ⋯ ∧ v_m ∧ ψ̄(y)`. -/
theorem s23_psi_prod_mul (l : List (V F n)) {b : ℕ} {y : C F n} (hy : y ∈ CFilt F n b) :
    projDeg F n (l.length + b) (psi F n ((l.map (CliffordAlgebra.ι (Q F n))).prod * y)) =
      (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod *
        projDeg F n b (psi F n y) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have hmem : psi F n ((l.map (CliffordAlgebra.ι (Q F n))).prod * y) ∈
        extFiltLE F n (l.length + b) :=
      psi_mem_extFiltLE F n _ (s23_mul_mem_CFilt F n (s23_prod_mem_CFilt F n l) hy)
    rw [List.map_cons, List.prod_cons, mul_assoc, s23_psi_ι_mul, List.length_cons,
      show l.length + 1 + b = (l.length + b) + 1 by omega]
    simp only [Lprime, Lext, delta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mul_apply', map_add]
    rw [s23_projDeg_ι_mul, ih, s23_projDeg_eq_zero_of_mem_extFiltLE F n (Nat.lt_succ_self _)
      (s23_contractLeft_mem_extFiltLE F n _ hmem), add_zero, List.map_cons, List.prod_cons,
      mul_assoc]


/-- `ψ̄` is multiplicative: for `x ∈ C(V)_a` and `y ∈ C(V)_b`, the degree-`(a + b)` component of
`ψ(x y)` is the product of the degree-`a` component of `ψ(x)` and the degree-`b` component of
`ψ(y)` (the associated graded map of `ψ` is the identity of `⋀•V`). -/
theorem s23_projDeg_psi_mul {a b : ℕ} {x y : C F n} (hx : x ∈ CFilt F n a)
    (hy : y ∈ CFilt F n b) :
    projDeg F n (a + b) (psi F n (x * y)) =
      projDeg F n a (psi F n x) * projDeg F n b (psi F n y) := by
  let φ : C F n →ₗ[F] ExtV F n :=
    projDeg F n (a + b) ∘ₗ psi F n ∘ₗ LinearMap.mulRight F y -
      LinearMap.mulRight F (projDeg F n b (psi F n y)) ∘ₗ projDeg F n a ∘ₗ psi F n
  have hle : CFilt F n a ≤ LinearMap.ker φ := by
    rw [s23_CFilt_eq, CliffordAlgebra.filtration_le_iff]
    intro l hl
    rw [LinearMap.mem_ker]
    simp only [φ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]
    rcases hl.lt_or_eq with hlt | heq
    · have h1 := psi_mem_extFiltLE F n _ (s23_mul_mem_CFilt F n (s23_prod_mem_CFilt F n l) hy)
      rw [s23_projDeg_eq_zero_of_mem_extFiltLE F n (by omega) h1,
        s23_projDeg_eq_zero_of_mem_extFiltLE F n hlt (s23_psi_prod_mem F n l).1, zero_mul,
        sub_zero]
    · subst heq
      rw [s23_psi_prod_mul F n l hy, (s23_psi_prod_mem F n l).2, sub_self]
  have := hle hx
  rw [LinearMap.mem_ker] at this
  simp only [φ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    sub_eq_zero] at this
  exact this

/-! ### The computation in `C(V)` (proof of Lemma 2.3.2), in an arbitrary ring -/

/-- The identity `e₁ e₂ f₂ f₁ = f₁ f₂ e₂ e₁ + [e₁ f₁ + e₂ f₂] - 1` of the proof of Lemma 2.3.2,
from the Clifford relations `eᵢ fⱼ + fⱼ eᵢ = δᵢⱼ`, `eᵢ eⱼ = -eⱼ eᵢ`, `fᵢ fⱼ = -fⱼ fᵢ`. -/
private theorem pair_identity {R : Type*} [Ring R] {Ea Eb Fa Fb : R}
    (hEaFa : Ea * Fa + Fa * Ea = 1) (hEbFb : Eb * Fb + Fb * Eb = 1)
    (hEaFb : Ea * Fb = -(Fb * Ea)) (hEbFa : Eb * Fa = -(Fa * Eb))
    (hFF : Fb * Fa = -(Fa * Fb)) (hEE : Ea * Eb = -(Eb * Ea)) :
    Ea * Eb * Fb * Fa = Fa * Fb * Eb * Ea + (Ea * Fa + Eb * Fb) - 1 := by
  have hEaFa' : Ea * Fa = 1 - Fa * Ea := by rw [← hEaFa]; abel
  have hEbFb' : Eb * Fb = 1 - Fb * Eb := by rw [← hEbFb]; abel
  have hFbEb' : Fb * Eb = 1 - Eb * Fb := by rw [← hEbFb]; abel
  have hX : Ea * Fb * Eb * Fa = Fb * Eb - Fa * Fb * Eb * Ea := by
    calc Ea * Fb * Eb * Fa = (Ea * Fb) * (Eb * Fa) := by noncomm_ring
      _ = Fb * (Ea * Fa) * Eb := by rw [hEaFb, hEbFa]; noncomm_ring
      _ = Fb * (1 - Fa * Ea) * Eb := by rw [hEaFa']
      _ = Fb * Eb - (Fb * Fa) * (Ea * Eb) := by noncomm_ring
      _ = Fb * Eb - Fa * Fb * Eb * Ea := by rw [hFF, hEE]; noncomm_ring
  calc Ea * Eb * Fb * Fa = Ea * (Eb * Fb) * Fa := by noncomm_ring
    _ = Ea * (1 - Fb * Eb) * Fa := by rw [hEbFb']
    _ = Ea * Fa - Ea * Fb * Eb * Fa := by noncomm_ring
    _ = Ea * Fa - (Fb * Eb - Fa * Fb * Eb * Ea) := by rw [hX]
    _ = Fa * Fb * Eb * Ea + (Ea * Fa + Eb * Fb) - 1 := by rw [hFbEb']; noncomm_ring

/-- A product of two elements anticommuting with `x` commutes with `x`. -/
private theorem commute_mul_of_anticomm {R : Type*} [Ring R] {a b x : R}
    (ha : a * x = -(x * a)) (hb : b * x = -(x * b)) : Commute (a * b) x := by
  show a * b * x = x * (a * b)
  rw [mul_assoc, hb, mul_neg, ← mul_assoc, ha, neg_mul, neg_neg, mul_assoc]

private theorem list_range_two_mul_succ (m : ℕ) :
    List.range (2 * (m + 1)) = List.range (2 * m) ++ [2 * m, 2 * m + 1] := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.range_succ, List.range_succ, List.append_assoc]
  rfl

/-- Reversing a product of `2m` pairwise anticommuting factors gives the sign `(-1)^m`. -/
private theorem prod_reverse_of_anticomm {R : Type*} [Ring R] (g : ℕ → R)
    (hg : ∀ i j, i ≠ j → g i * g j = -(g j * g i)) (m : ℕ) :
    ((List.range (2 * m)).reverse.map g).prod = (-1) ^ m * ((List.range (2 * m)).map g).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomm : Commute (g (2 * m) * g (2 * m + 1)) ((List.range (2 * m)).map g).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_range] at hj
      exact commute_mul_of_anticomm (hg _ _ (by omega)) (hg _ _ (by omega))
    rw [list_range_two_mul_succ, List.reverse_append, List.map_append, List.prod_append, ih,
      List.map_append, List.prod_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hg (2 * m + 1) (2 * m) (by omega), neg_mul, ← mul_assoc]
    have hc : Commute ((-1 : R) ^ m) (g (2 * m) * g (2 * m + 1)) :=
      (Commute.neg_one_left _).pow_left m
    rw [← hc.eq, mul_assoc, hcomm.eq, pow_succ]
    noncomm_ring

/-- The product formula of the proof of Lemma 2.3.2:
`(e₁ ⋯ e_{2m})(f_{2m} ⋯ f₁) = ∏_{k ≤ m} e_{2k-1} e_{2k} f_{2k} f_{2k-1}` (indices from `0` here). -/
private theorem prod_formula {R : Type*} [Ring R] (E Fh : ℕ → R)
    (hFF : ∀ i j, Fh i * Fh j = -(Fh j * Fh i))
    (hEF : ∀ i j, i ≠ j → E i * Fh j = -(Fh j * E i)) (m : ℕ) :
    ((List.range (2 * m)).map E).prod * ((List.range (2 * m)).reverse.map Fh).prod =
      ((List.range m).map fun k =>
        E (2 * k) * E (2 * k + 1) * Fh (2 * k + 1) * Fh (2 * k)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomm : Commute (E (2 * m) * E (2 * m + 1) * Fh (2 * m + 1) * Fh (2 * m))
        ((List.range (2 * m)).reverse.map Fh).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_reverse, List.mem_range] at hj
      have h1 : Commute (E (2 * m) * E (2 * m + 1)) (Fh j) := commute_mul_of_anticomm
        (by rw [hEF _ _ (by omega)]) (by rw [hEF _ _ (by omega)])
      have h2 : Commute (Fh (2 * m + 1) * Fh (2 * m)) (Fh j) :=
        commute_mul_of_anticomm (hFF _ _) (hFF _ _)
      rw [mul_assoc (E (2 * m) * E (2 * m + 1))]
      exact h1.mul_left h2
    rw [list_range_two_mul_succ, List.reverse_append, List.map_append, List.prod_append,
      List.map_append, List.prod_append, List.range_succ, List.map_append, List.prod_append, ← ih]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc _ ((List.range (2 * m)).reverse.map Fh).prod, ← hcomm.eq]
    simp only [mul_assoc]

/-- The correction to the proof of Lemma 2.3.2: `(f₁ ⋯ f_{2m})(e₁ ⋯ e_{2m}) = (-1)^m ∏_k f_{2k-1}
f_{2k} e_{2k} e_{2k-1}` exactly (indices from `0` here). -/
private theorem prod_formula' {R : Type*} [Ring R] (E Fh : ℕ → R)
    (hEE : ∀ i j, E i * E j = -(E j * E i))
    (hEF : ∀ i j, i ≠ j → E i * Fh j = -(Fh j * E i)) (m : ℕ) :
    ((List.range (2 * m)).map Fh).prod * ((List.range (2 * m)).map E).prod =
      (-1) ^ m *
        ((List.range m).map fun k =>
          Fh (2 * k) * Fh (2 * k + 1) * E (2 * k + 1) * E (2 * k)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomm : Commute (Fh (2 * m) * Fh (2 * m + 1)) ((List.range (2 * m)).map E).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_range] at hj
      refine commute_mul_of_anticomm ?_ ?_
      · rw [hEF _ _ (by omega : j ≠ 2 * m), neg_neg]
      · rw [hEF _ _ (by omega : j ≠ 2 * m + 1), neg_neg]
    rw [list_range_two_mul_succ, List.map_append, List.prod_append, List.map_append,
      List.prod_append, List.range_succ, List.map_append, List.prod_append, ← mul_assoc _ _ _]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc _ (Fh (2 * m) * Fh (2 * m + 1)) _, hcomm.eq,
      ← mul_assoc _ ((List.range (2 * m)).map E).prod, ih, hEE (2 * m) (2 * m + 1), pow_succ]
    noncomm_ring


/-! ### The basis vectors `eⱼ`, `fⱼ` of `V` with natural-number indices -/

/-- `eⱼ ∈ H¹(X)` for `j < 2n` (`0` for `j ≥ 2n`). -/
private noncomputable def eN (j : ℕ) : H1 F n := if h : j < 2 * n then e F n ⟨j, h⟩ else 0

/-- `fⱼ ∈ H¹(X̂) = H¹(X)*` for `j < 2n` (`0` for `j ≥ 2n`). -/
private noncomputable def fN (j : ℕ) : Module.Dual F (H1 F n) :=
  if h : j < 2 * n then f F n ⟨j, h⟩ else 0

/-- `eⱼ` as a vector of `V`. -/
private noncomputable def ev (j : ℕ) : V F n := (0, eN F n j)

/-- `fⱼ` as a vector of `V`. -/
private noncomputable def fv (j : ℕ) : V F n := (fN F n j, 0)

omit [CharZero F] in
private theorem fN_eN (i j : ℕ) : fN F n j (eN F n i) = if i = j ∧ i < 2 * n then 1 else 0 := by
  unfold fN eN
  by_cases hi : i < 2 * n <;> by_cases hj : j < 2 * n <;> simp [hi, hj, e, f, Pi.single_apply]
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro h; omega

omit [CharZero F] in
private theorem pairing_ev_ev (i j : ℕ) : pairing F n (ev F n i) (ev F n j) = 0 := by
  simp [ev]

omit [CharZero F] in
private theorem pairing_fv_fv (i j : ℕ) : pairing F n (fv F n i) (fv F n j) = 0 := by
  simp [fv]

omit [CharZero F] in
private theorem pairing_ev_fv (i j : ℕ) :
    pairing F n (ev F n i) (fv F n j) = if i = j ∧ i < 2 * n then 1 else 0 := by
  simp [ev, fv, fN_eN]

omit [CharZero F] in
/-- The Clifford relations for the `eⱼ, fⱼ` in `C(V)`. -/
private theorem cliff_ee (i j : ℕ) :
    CliffordAlgebra.ι (Q F n) (ev F n i) * CliffordAlgebra.ι (Q F n) (ev F n j) =
      -(CliffordAlgebra.ι (Q F n) (ev F n j) * CliffordAlgebra.ι (Q F n) (ev F n i)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [CliffordAlgebra.ι_mul_ι_add_swap, ← QuadraticMap.polarBilin_apply_apply, ← pairing,
    pairing_ev_ev, map_zero]

omit [CharZero F] in
private theorem cliff_ff (i j : ℕ) :
    CliffordAlgebra.ι (Q F n) (fv F n i) * CliffordAlgebra.ι (Q F n) (fv F n j) =
      -(CliffordAlgebra.ι (Q F n) (fv F n j) * CliffordAlgebra.ι (Q F n) (fv F n i)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [CliffordAlgebra.ι_mul_ι_add_swap, ← QuadraticMap.polarBilin_apply_apply, ← pairing,
    pairing_fv_fv, map_zero]

omit [CharZero F] in
private theorem cliff_ef (i j : ℕ) (hij : i ≠ j) :
    CliffordAlgebra.ι (Q F n) (ev F n i) * CliffordAlgebra.ι (Q F n) (fv F n j) =
      -(CliffordAlgebra.ι (Q F n) (fv F n j) * CliffordAlgebra.ι (Q F n) (ev F n i)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [CliffordAlgebra.ι_mul_ι_add_swap, ← QuadraticMap.polarBilin_apply_apply, ← pairing,
    pairing_ev_fv]
  simp [hij]

omit [CharZero F] in
private theorem cliff_ef_self (i : ℕ) (hi : i < 2 * n) :
    CliffordAlgebra.ι (Q F n) (ev F n i) * CliffordAlgebra.ι (Q F n) (fv F n i) +
      CliffordAlgebra.ι (Q F n) (fv F n i) * CliffordAlgebra.ι (Q F n) (ev F n i) = 1 := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, ← QuadraticMap.polarBilin_apply_apply, ← pairing,
    pairing_ev_fv]
  simp [hi]

private theorem ofFn_eq_map_range' {α : Type*} (G : ℕ → α) (m : ℕ) :
    List.ofFn (fun i : Fin m => G i) = (List.range m).map G := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.range_succ, List.map_append, ← ih]
    simp

omit [CharZero F] in
/-- `[pt_X] = e₁ ∧ ⋯ ∧ e_{2n}`. -/
private theorem pt_eq_prod :
    pt F n = ((List.range (2 * n)).map fun j => ExteriorAlgebra.ι F (eN F n j)).prod := by
  have hcard : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by simp
  have hemb : ⇑((Finset.univ : Finset (Fin (2 * n))).orderEmbOfFin hcard) = id :=
    (Finset.orderEmbOfFin_unique hcard (f := id) (fun x => Finset.mem_univ x) strictMono_id).symm
  rw [pt, basisS, ExteriorAlgebra.basis_apply_ofCard _ hcard]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.val_ofCard]
  rw [hemb, ExteriorAlgebra.ιMulti_apply, ← ofFn_eq_map_range']
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp [eN, e, i.isLt]

omit [CharZero F] in
/-- `[pt_X̂] = f₁ ∧ ⋯ ∧ f_{2n}`. -/
private theorem ptHat_eq_prod :
    ptHat F n = ((List.range (2 * n)).map fun j => ExteriorAlgebra.ι F (fN F n j)).prod := by
  have hcard : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by simp
  have hemb : ⇑((Finset.univ : Finset (Fin (2 * n))).orderEmbOfFin hcard) = id :=
    (Finset.orderEmbOfFin_unique hcard (f := id) (fun x => Finset.mem_univ x) strictMono_id).symm
  rw [ptHat, basisSHat, ExteriorAlgebra.basis_apply_ofCard _ hcard]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.val_ofCard]
  rw [hemb, ExteriorAlgebra.ιMulti_apply, ← ofFn_eq_map_range']
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, id, fN, i.isLt, ↓reduceDIte]
  congr 1
  refine LinearMap.ext fun w => ?_
  simp [f]

omit [CharZero F] in
private theorem iotaX_ι (w : H1 F n) :
    iotaX F n (ExteriorAlgebra.ι F w) = CliffordAlgebra.ι (Q F n) (0, w) :=
  ExteriorAlgebra.lift_ι_apply F _ _ w

omit [CharZero F] in
private theorem iotaXHat_ι (θ : Module.Dual F (H1 F n)) :
    iotaXHat F n (ExteriorAlgebra.ι F θ) = CliffordAlgebra.ι (Q F n) (θ, 0) :=
  ExteriorAlgebra.lift_ι_apply F _ _ θ

omit [CharZero F] in
private theorem iotaX_pt :
    iotaX F n (pt F n) =
      ((List.range (2 * n)).map fun j => CliffordAlgebra.ι (Q F n) (ev F n j)).prod := by
  rw [pt_eq_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, iotaX_ι]
  rfl

omit [CharZero F] in
private theorem ptHatC_eq :
    ptHatC F n =
      ((List.range (2 * n)).map fun j => CliffordAlgebra.ι (Q F n) (fv F n j)).prod := by
  rw [ptHatC, ptHat_eq_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, iotaXHat_ι]
  rfl

omit [CharZero F] in
private theorem iotaX_tau_pt :
    iotaX F n (tau F n (pt F n)) =
      ((List.range (2 * n)).reverse.map fun j => CliffordAlgebra.ι (Q F n) (ev F n j)).prod := by
  have h : ((List.range (2 * n)).map fun j => ExteriorAlgebra.ι F (eN F n j)) =
      ((List.range (2 * n)).map (eN F n)).map
        (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n))) := by
    rw [List.map_map]; rfl
  rw [pt_eq_prod, h, tau, CliffordAlgebra.reverse_prod_map_ι, map_list_prod, List.map_reverse,
    List.map_map, List.map_map, ← List.map_reverse]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  exact iotaX_ι F n (eN F n j)

/-! ### `eⱼ`, `fⱼ` in `C(V)` and in `⋀•V`; the elements `A_k`, `P_k`, `T_k` of the proof -/

private noncomputable def Ec (j : ℕ) : C F n := CliffordAlgebra.ι (Q F n) (ev F n j)

private noncomputable def Fc (j : ℕ) : C F n := CliffordAlgebra.ι (Q F n) (fv F n j)

/-- `A_k = e_{2k} e_{2k+1} f_{2k+1} f_{2k}` (the paper's `e_{2k-1} e_{2k} f_{2k} f_{2k-1}`). -/
private noncomputable def Ak (k : ℕ) : C F n :=
  Ec F n (2 * k) * Ec F n (2 * k + 1) * Fc F n (2 * k + 1) * Fc F n (2 * k)

/-- `P_k = f_{2k} f_{2k+1} e_{2k+1} e_{2k}`. -/
private noncomputable def Pk (k : ℕ) : C F n :=
  Fc F n (2 * k) * Fc F n (2 * k + 1) * Ec F n (2 * k + 1) * Ec F n (2 * k)

/-- `T_k = e_{2k} f_{2k} + e_{2k+1} f_{2k+1}`. -/
private noncomputable def Tk (k : ℕ) : C F n :=
  Ec F n (2 * k) * Fc F n (2 * k) + Ec F n (2 * k + 1) * Fc F n (2 * k + 1)

private noncomputable def ew (j : ℕ) : ExtV F n := ExteriorAlgebra.ι F (ev F n j)

private noncomputable def fw (j : ℕ) : ExtV F n := ExteriorAlgebra.ι F (fv F n j)

/-- The leading terms `a_k`, `p_k`, `t_k` of `A_k`, `P_k`, `T_k - 1` in `⋀•V`. -/
private noncomputable def aW (k : ℕ) : ExtV F n :=
  ew F n (2 * k) * ew F n (2 * k + 1) * fw F n (2 * k + 1) * fw F n (2 * k)

private noncomputable def pW (k : ℕ) : ExtV F n :=
  fw F n (2 * k) * fw F n (2 * k + 1) * ew F n (2 * k + 1) * ew F n (2 * k)

private noncomputable def tW (k : ℕ) : ExtV F n :=
  ew F n (2 * k) * fw F n (2 * k) + ew F n (2 * k + 1) * fw F n (2 * k + 1)

omit [CharZero F] in
/-- The paper's identity `A_k = P_k + T_k - 1`. -/
private theorem Ak_eq (k : ℕ) (hk : k < n) : Ak F n k = Pk F n k + (Tk F n k - 1) := by
  simp only [Ak, Pk, Tk, Ec, Fc]
  rw [pair_identity (cliff_ef_self F n _ (by omega)) (cliff_ef_self F n _ (by omega))
    (cliff_ef F n _ _ (by omega)) (cliff_ef F n _ _ (by omega)) (cliff_ff F n _ _)
    (cliff_ee F n _ _)]
  abel

omit [CharZero F] in
/-- `ψ(A_k) ∈ F⁴` with leading term `a_k`. -/
private theorem lead_Ak (k : ℕ) :
    Ak F n k ∈ CFilt F n 4 ∧ projDeg F n 4 (psi F n (Ak F n k)) = aW F n k := by
  have h := s23_psi_prod_mem F n [ev F n (2 * k), ev F n (2 * k + 1), fv F n (2 * k + 1),
    fv F n (2 * k)]
  have hm := s23_prod_mem_CFilt F n [ev F n (2 * k), ev F n (2 * k + 1), fv F n (2 * k + 1),
    fv F n (2 * k)]
  have hA : ([ev F n (2 * k), ev F n (2 * k + 1), fv F n (2 * k + 1), fv F n (2 * k)].map
      (CliffordAlgebra.ι (Q F n))).prod = Ak F n k := by
    simp [Ak, Ec, Fc, mul_assoc]
  rw [hA] at h hm
  refine ⟨hm, h.2.trans ?_⟩
  simp [aW, ew, fw, mul_assoc]

omit [CharZero F] in
private theorem lead_Pk (k : ℕ) :
    Pk F n k ∈ CFilt F n 4 ∧ projDeg F n 4 (psi F n (Pk F n k)) = pW F n k := by
  have h := s23_psi_prod_mem F n [fv F n (2 * k), fv F n (2 * k + 1), ev F n (2 * k + 1),
    ev F n (2 * k)]
  have hm := s23_prod_mem_CFilt F n [fv F n (2 * k), fv F n (2 * k + 1), ev F n (2 * k + 1),
    ev F n (2 * k)]
  have hP : ([fv F n (2 * k), fv F n (2 * k + 1), ev F n (2 * k + 1), ev F n (2 * k)].map
      (CliffordAlgebra.ι (Q F n))).prod = Pk F n k := by
    simp [Pk, Ec, Fc, mul_assoc]
  rw [hP] at h hm
  refine ⟨hm, h.2.trans ?_⟩
  simp [pW, ew, fw, mul_assoc]

omit [CharZero F] in
private theorem lead_two (a b : V F n) :
    CliffordAlgebra.ι (Q F n) a * CliffordAlgebra.ι (Q F n) b ∈ CFilt F n 2 ∧
      projDeg F n 2 (psi F n (CliffordAlgebra.ι (Q F n) a * CliffordAlgebra.ι (Q F n) b)) =
        ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b := by
  have h := s23_psi_prod_mem F n [a, b]
  have hm := s23_prod_mem_CFilt F n [a, b]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil] at h hm
  exact ⟨hm, h.2⟩

private theorem lead_Tk (k : ℕ) :
    Tk F n k - 1 ∈ CFilt F n 2 ∧ projDeg F n 2 (psi F n (Tk F n k - 1)) = tW F n k := by
  have h1 := lead_two F n (ev F n (2 * k)) (fv F n (2 * k))
  have h2 := lead_two F n (ev F n (2 * k + 1)) (fv F n (2 * k + 1))
  have hone : (1 : C F n) ∈ CFilt F n 0 := by simpa using s23_prod_mem_CFilt F n []
  have hone' : psi F n 1 ∈ extFiltLE F n 0 := psi_mem_extFiltLE F n 0 hone
  simp only [Tk, Ec, Fc]
  refine ⟨sub_mem (add_mem h1.1 h2.1) (s23_CFilt_mono F n (Nat.zero_le 2) hone), ?_⟩
  rw [map_sub, map_add, map_sub, map_add, h1.2, h2.2,
    s23_projDeg_eq_zero_of_mem_extFiltLE F n (by norm_num) hone', sub_zero]
  rfl

/-- The leading term of `∏_{k<m} A_k` (resp. `∏_{k<m} P_k`) is `∏_{k<m} a_k` (resp. `∏ p_k`). -/
private theorem lead_prodA (m : ℕ) :
    ((List.range m).map (Ak F n)).prod ∈ CFilt F n (4 * m) ∧
      projDeg F n (4 * m) (psi F n ((List.range m).map (Ak F n)).prod) =
        ((List.range m).map (aW F n)).prod := by
  induction m with
  | zero =>
    have hone : (1 : C F n) ∈ CFilt F n 0 := by simpa using s23_prod_mem_CFilt F n []
    refine ⟨by simpa using hone, ?_⟩
    simpa using (s23_psi_prod_mem F n []).2
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [show 4 * (m + 1) = 4 * m + 4 by ring]
    exact ⟨s23_mul_mem_CFilt F n ih.1 (lead_Ak F n m).1,
      (s23_projDeg_psi_mul F n ih.1 (lead_Ak F n m).1).trans (by rw [ih.2, (lead_Ak F n m).2])⟩

private theorem lead_prodP (m : ℕ) :
    ((List.range m).map (Pk F n)).prod ∈ CFilt F n (4 * m) ∧
      projDeg F n (4 * m) (psi F n ((List.range m).map (Pk F n)).prod) =
        ((List.range m).map (pW F n)).prod := by
  induction m with
  | zero =>
    have hone : (1 : C F n) ∈ CFilt F n 0 := by simpa using s23_prod_mem_CFilt F n []
    refine ⟨by simpa using hone, ?_⟩
    simpa using (s23_psi_prod_mem F n []).2
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [show 4 * (m + 1) = 4 * m + 4 by ring]
    exact ⟨s23_mul_mem_CFilt F n ih.1 (lead_Pk F n m).1,
      (s23_projDeg_psi_mul F n ih.1 (lead_Pk F n m).1).trans (by rw [ih.2, (lead_Pk F n m).2])⟩

/-- The leading term `Σ_k (∏_{j<k} p_j) ∧ t_k ∧ (∏_{k<j<m} a_j)` of `∏_{k<m} A_k - ∏_{k<m} P_k`,
defined recursively. -/
private noncomputable def sW : ℕ → ExtV F n
  | 0 => 0
  | m + 1 => sW m * aW F n m + ((List.range m).map (pW F n)).prod * tW F n m

/-- The corrected computation of the proof of Lemma 2.3.2: `∏_{k<m} A_k - ∏_{k<m} P_k` lies in
`C(V)_{4m-2}`, with leading term `sW m` in `⋀^{4m-2} V`. -/
private theorem lead_diff (m : ℕ) (hm : m + 1 ≤ n) :
    ((List.range (m + 1)).map (Ak F n)).prod - ((List.range (m + 1)).map (Pk F n)).prod ∈
        CFilt F n (4 * m + 2) ∧
      projDeg F n (4 * m + 2) (psi F n (((List.range (m + 1)).map (Ak F n)).prod -
        ((List.range (m + 1)).map (Pk F n)).prod)) = sW F n (m + 1) := by
  -- telescoping: `∏A - ∏P = (∏'A - ∏'P) A_m + ∏'P (A_m - P_m)` and `A_m - P_m = T_m - 1`
  have htel : ∀ k, k < n →
      ((List.range (k + 1)).map (Ak F n)).prod - ((List.range (k + 1)).map (Pk F n)).prod =
        (((List.range k).map (Ak F n)).prod - ((List.range k).map (Pk F n)).prod) * Ak F n k +
          ((List.range k).map (Pk F n)).prod * (Tk F n k - 1) := by
    intro k hk
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [Ak_eq F n k hk]
    noncomm_ring
  induction m with
  | zero =>
    rw [htel 0 (by omega)]
    simp only [List.range_zero, List.map_nil, List.prod_nil, sub_self, zero_mul, one_mul,
      zero_add]
    exact ⟨(lead_Tk F n 0).1, by rw [(lead_Tk F n 0).2]; simp [sW]⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [htel (m + 1) (by omega)]
    have hA := lead_Ak F n (m + 1)
    have hP := lead_prodP F n (m + 1)
    have hT := lead_Tk F n (m + 1)
    have hmem1 := s23_mul_mem_CFilt F n ih1 hA.1
    have hmem2 := s23_mul_mem_CFilt F n hP.1 hT.1
    rw [show 4 * m + 2 + 4 = 4 * (m + 1) + 2 by ring] at hmem1
    refine ⟨add_mem hmem1 hmem2, ?_⟩
    rw [map_add, map_add]
    have e1 := s23_projDeg_psi_mul F n ih1 hA.1
    have e2 := s23_projDeg_psi_mul F n hP.1 hT.1
    rw [show 4 * m + 2 + 4 = 4 * (m + 1) + 2 by ring] at e1
    rw [e1, e2, ih2, hA.2, hP.2, hT.2]
    rfl

/-! ### Computations in `⋀•V` -/

omit [CharZero F] in
private theorem ι_anticomm (x y : V F n) :
    ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F y =
      -(ExteriorAlgebra.ι F y * ExteriorAlgebra.ι F x) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

omit [CharZero F] in
/-- A product of two vectors is central in `⋀•V`. -/
private theorem ι_mul_ι_comm (x y : V F n) (z : ExtV F n) :
    ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F y * z =
      z * (ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F y) :=
  s23_mul_comm_of_mem_even (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ x y) z

omit [CharZero F] in
/-- `a_k = p_k`: the leading terms of `A_k` and `P_k` agree. -/
private theorem aW_eq_pW (k : ℕ) : aW F n k = pW F n k := by
  simp only [aW, pW, ew, fw]
  rw [mul_assoc (ExteriorAlgebra.ι F (ev F n (2 * k)) * ExteriorAlgebra.ι F (ev F n (2 * k + 1))),
    ι_mul_ι_comm, ι_anticomm F n (fv F n (2 * k + 1)), ι_anticomm F n (ev F n (2 * k))]
  noncomm_ring

omit [CharZero F] in
private theorem u_mul_tW : (ew F n 1 * fw F n 1) * tW F n 0 = pW F n 0 := by
  simp only [tW, pW, ew, fw, Nat.mul_zero, zero_add]
  have h1 : ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (fv F n 1) *
      (ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (fv F n 1)) = 0 := by
    rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι F (fv F n 1)), ι_anticomm F n (fv F n 1)]
    simp only [neg_mul, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]
  have h2 : ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (fv F n 1) *
      (ExteriorAlgebra.ι F (ev F n 0) * ExteriorAlgebra.ι F (fv F n 0)) =
      ExteriorAlgebra.ι F (fv F n 0) * ExteriorAlgebra.ι F (fv F n 1) *
        ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (ev F n 0) := by
    rw [ι_mul_ι_comm, mul_assoc (ExteriorAlgebra.ι F (ev F n 0)),
      ← mul_assoc (ExteriorAlgebra.ι F (fv F n 0)), ι_anticomm F n (fv F n 0) (ev F n 1)]
    have h3 : ExteriorAlgebra.ι F (ev F n 0) * (-(ExteriorAlgebra.ι F (ev F n 1) *
        ExteriorAlgebra.ι F (fv F n 0)) * ExteriorAlgebra.ι F (fv F n 1)) =
        -(ExteriorAlgebra.ι F (ev F n 0) * ExteriorAlgebra.ι F (ev F n 1) *
          (ExteriorAlgebra.ι F (fv F n 0) * ExteriorAlgebra.ι F (fv F n 1))) := by
      noncomm_ring
    rw [h3, ι_mul_ι_comm F n (ev F n 0) (ev F n 1), ι_anticomm F n (ev F n 0) (ev F n 1)]
    noncomm_ring
  rw [mul_add, h1, add_zero, h2]

omit [CharZero F] in
private theorem u_mul_pW : (ew F n 1 * fw F n 1) * pW F n 0 = 0 := by
  simp only [pW, ew, fw, Nat.mul_zero, zero_add]
  have h : ExteriorAlgebra.ι F (fv F n 1) * ExteriorAlgebra.ι F (fv F n 0) *
      ExteriorAlgebra.ι F (fv F n 1) = 0 := by
    rw [ι_anticomm F n (fv F n 1) (fv F n 0), neg_mul, mul_assoc, ExteriorAlgebra.ι_sq_zero,
      mul_zero, neg_zero]
  calc ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (fv F n 1) *
        (ExteriorAlgebra.ι F (fv F n 0) * ExteriorAlgebra.ι F (fv F n 1) *
          ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (ev F n 0)) =
        ExteriorAlgebra.ι F (ev F n 1) * (ExteriorAlgebra.ι F (fv F n 1) *
          ExteriorAlgebra.ι F (fv F n 0) * ExteriorAlgebra.ι F (fv F n 1)) *
          ExteriorAlgebra.ι F (ev F n 1) * ExteriorAlgebra.ι F (ev F n 0) := by noncomm_ring
    _ = 0 := by rw [h]; simp

omit [CharZero F] in
/-- `u ∧ sW (m+1) = ∏_{k ≤ m} p_k` for `u = e₁ ∧ f₁`: the terms containing `p₀` die. -/
private theorem u_mul_sW (m : ℕ) :
    (ew F n 1 * fw F n 1) * sW F n (m + 1) = ((List.range (m + 1)).map (pW F n)).prod := by
  induction m with
  | zero => simp [sW, u_mul_tW]
  | succ m ih =>
    have h0 : (ew F n 1 * fw F n 1) * ((List.range (m + 1)).map (pW F n)).prod = 0 := by
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, ← mul_assoc, u_mul_pW, zero_mul]
    rw [sW, mul_add, ← mul_assoc, ih, ← mul_assoc, h0, zero_mul, add_zero, aW_eq_pW,
      List.range_succ (n := m + 1), List.map_append, List.prod_append]
    simp

omit [CharZero F] in
/-- `∏_{k<m} p_k = (f₀ ⋯ f_{2m-1}) ∧ ∏_{k<m} (e_{2k+1} ∧ e_{2k})`. -/
private theorem prod_pW_split (m : ℕ) :
    ((List.range m).map (pW F n)).prod =
      ((List.range (2 * m)).map (fw F n)).prod *
        ((List.range m).map fun k => ew F n (2 * k + 1) * ew F n (2 * k)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, list_range_two_mul_succ,
      List.map_append, List.prod_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pW, fw, ew]
    generalize (List.map (fun k => ExteriorAlgebra.ι F (ev F n (2 * k + 1)) *
      ExteriorAlgebra.ι F (ev F n (2 * k))) (List.range m)).prod = G
    have hc := ι_mul_ι_comm F n (fv F n (2 * m)) (fv F n (2 * m + 1)) G
    set fa := ExteriorAlgebra.ι F (fv F n (2 * m))
    set fb := ExteriorAlgebra.ι F (fv F n (2 * m + 1))
    set ea := ExteriorAlgebra.ι F (ev F n (2 * m))
    set eb := ExteriorAlgebra.ι F (ev F n (2 * m + 1))
    set Fw := (List.map (fw F n) (List.range (2 * m))).prod
    calc Fw * G * (fa * fb * eb * ea) = Fw * (G * (fa * fb)) * (eb * ea) := by noncomm_ring
      _ = Fw * (fa * fb * G) * (eb * ea) := by rw [hc]
      _ = Fw * (fa * fb) * (G * (eb * ea)) := by noncomm_ring

omit [CharZero F] in
private theorem prod_pairs_swap (m : ℕ) :
    ((List.range m).map fun k => ew F n (2 * k + 1) * ew F n (2 * k)).prod =
      (-1) ^ m * ((List.range (2 * m)).map (ew F n)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, list_range_two_mul_succ,
      List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ew]
    rw [ι_anticomm F n (ev F n (2 * m + 1)) (ev F n (2 * m)), pow_succ]
    noncomm_ring

private theorem neg_one_pow_mul_self {R : Type*} [Ring R] (m : ℕ) :
    (-1 : R) ^ m * (-1) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

omit [CharZero F] in
private theorem Fw_eq : ((List.range (2 * n)).map (fw F n)).prod = pullXHat F n (ptHat F n) := by
  rw [ptHat_eq_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [fw, fv, pullXHat, ExteriorAlgebra.map_apply_ι]

omit [CharZero F] in
private theorem Ew_eq : ((List.range (2 * n)).map (ew F n)).prod = pullX F n (pt F n) := by
  rw [pt_eq_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [ew, ev, pullX, ExteriorAlgebra.map_apply_ι]

omit [CharZero F] in
/-- `[pt_X̂] ∧ [pt_X] ≠ 0` (it is the Künneth image of a basis vector of `H*(X̂) ⊗ H*(X)`). -/
private theorem pt_mul_ne_zero : pullXHat F n (ptHat F n) * pullX F n (pt F n) ≠ 0 := by
  rw [← kunnethHatX_tmul]
  intro h
  have h2 : ptHat F n ⊗ₜ[F] pt F n = 0 := (kunnethHatX F n).injective (by rw [h, map_zero])
  have hb := ((basisSHat F n).tensorProduct (basisS F n)).ne_zero (Finset.univ, Finset.univ)
  rw [Module.Basis.tensorProduct_apply] at hb
  exact hb h2

omit [CharZero F] in
/-- `∏_{k<n} p_k = (-1)ⁿ [pt_X̂] ∧ [pt_X] ≠ 0`. -/
private theorem prod_pW_eq : ((List.range n).map (pW F n)).prod =
    (-1) ^ n * (pullXHat F n (ptHat F n) * pullX F n (pt F n)) := by
  rw [prod_pW_split, prod_pairs_swap, Fw_eq, Ew_eq, ← mul_assoc,
    ← ((Commute.neg_one_left (pullXHat F n (ptHat F n))).pow_left n).eq, mul_assoc]

omit [CharZero F] in
private theorem prod_pW_ne_zero : ((List.range n).map (pW F n)).prod ≠ 0 := by
  rw [prod_pW_eq]
  intro h
  apply pt_mul_ne_zero F n
  have := congrArg (fun z => (-1 : ExtV F n) ^ n * z) h
  simpa only [← mul_assoc, neg_one_pow_mul_self, one_mul, mul_zero] using this

omit [CharZero F] in
/-- The leading term `sW n` of the commutator is nonzero (`n ≥ 1`). -/
private theorem sW_ne_zero (hn : 1 ≤ n) : sW F n n ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  apply prod_pW_ne_zero F (m + 1)
  rw [← u_mul_sW, h, mul_zero]

/-! ### `φ([pt_X] ⊗ 1)` and `φ(1 ⊗ [pt_X])` -/

omit [CharZero F] in
private theorem neg_one_pow_smul_eq_mul (z : C F n) :
    ((-1 : F) ^ n) • z = (-1 : C F n) ^ n * z := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

omit [CharZero F] in
/-- The first display of the proof of Lemma 2.3.2:
`φ([pt_X] ⊗ 1) = [pt_X][pt_X̂] = (-1)ⁿ ∏_k A_k` and `φ(1 ⊗ [pt_X]) = (-1)ⁿ [pt_X̂][pt_X]`, with
`[pt_X̂][pt_X] = (-1)ⁿ ∏_k P_k`. -/
private theorem varphi_pt_one :
    varphi F n (pt F n ⊗ₜ[F] (1 : S F n)) =
      ((-1 : F) ^ n) • ((List.range n).map (Ak F n)).prod := by
  rw [varphi_tmul, show tau F n 1 = 1 from CliffordAlgebra.reverse.map_one, map_one, mul_one,
    iotaX_pt, ptHatC_eq]
  have hrev := prod_reverse_of_anticomm (fun j => CliffordAlgebra.ι (Q F n) (fv F n j))
    (fun i j _ => cliff_ff F n i j) n
  have hform := prod_formula (fun j => CliffordAlgebra.ι (Q F n) (ev F n j))
    (fun j => CliffordAlgebra.ι (Q F n) (fv F n j)) (cliff_ff F n)
    (fun i j h => cliff_ef F n i j h) n
  -- `f₁ ⋯ f_{2n} = (-1)ⁿ f_{2n} ⋯ f₁`
  have hF : ((List.range (2 * n)).map fun j => CliffordAlgebra.ι (Q F n) (fv F n j)).prod =
      (-1) ^ n *
        ((List.range (2 * n)).reverse.map fun j => CliffordAlgebra.ι (Q F n) (fv F n j)).prod := by
    rw [hrev, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [hF, neg_one_pow_smul_eq_mul, ← mul_assoc,
    ← ((Commute.neg_one_left _).pow_left n).eq, mul_assoc, hform]
  rfl

omit [CharZero F] in
private theorem varphi_one_pt :
    varphi F n ((1 : S F n) ⊗ₜ[F] pt F n) = ((List.range n).map (Pk F n)).prod := by
  rw [varphi_tmul, map_one, one_mul, iotaX_tau_pt, ptHatC_eq]
  have hrev := prod_reverse_of_anticomm (fun j => CliffordAlgebra.ι (Q F n) (ev F n j))
    (fun i j _ => cliff_ee F n i j) n
  have hform := prod_formula' (fun j => CliffordAlgebra.ι (Q F n) (ev F n j))
    (fun j => CliffordAlgebra.ι (Q F n) (fv F n j)) (cliff_ee F n)
    (fun i j h => cliff_ef F n i j h) n
  rw [hrev, ← mul_assoc, ← ((Commute.neg_one_left _).pow_left n).eq, mul_assoc, hform,
    ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rfl

/-- **Lemma 2.3.2(1)** (`lemma-symmetric-or-alternating-product-of-two-pure-spinors-has-weight-2`).
`φ̃([pt_X] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt_X])` belongs to `F^{4n-2}(⋀•V)` but not to `F^{4n-3}(⋀•V)`.

The hypothesis `1 ≤ n` (implied by the paper's standing assumption `n ≥ 2`) is needed: for `n = 0`
the element is `0`.

Proof as in the paper: `φ([pt_X] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt_X]) = [pt_X][pt_X̂] - [pt_X̂][pt_X]`; the
identity `e₁e₂f₂f₁ = f₁f₂e₂e₁ + [e₁f₁ + e₂f₂] - 1` and the product formula
`(e₁ ⋯ e_{2n})(f_{2n} ⋯ f₁) = ∏_k A_k`, `A_k = e_{2k-1}e_{2k}f_{2k}f_{2k-1}`, show that the
commutator lies in `C(V)_{4n-2}`, and its image in `C(V)_{4n-2}/C(V)_{4n-3} ≅ ⋀^{4n-2}V` is a
nonzero sum of `2n` terms; `ψ(C(V)_k) ⊆ F^k` and the injectivity of `ψ̄_{4n-2}` conclude.

**Departure from the paper (correction of one step).** The paper asserts that this image is
`2 Σ_k ⋀_{j≠k}(f_{2j-1} ∧ f_{2j} ∧ e_{2j} ∧ e_{2j-1}) ∧ [e_{2k-1} ∧ f_{2k-1} + e_{2k} ∧ f_{2k}]`;
the
factor `2` is wrong (for `n = 1` the commutator is `1 - e₁f₁ - e₂f₂`, with image
`-(e₁ ∧ f₁ + e₂ ∧ f₂)`). The paper does not expand `[pt_X̂][pt_X]`: it is exactly
`(-1)ⁿ ∏_k P_k`, `P_k = f_{2k-1}f_{2k}e_{2k}e_{2k-1}`, so the commutator is
`(-1)ⁿ (∏_k A_k - ∏_k P_k)` with `A_k - P_k = T_k - 1`, `T_k = e_{2k-1}f_{2k-1} + e_{2k}f_{2k}`, and
its image is `(-1)ⁿ Σ_k (∏_{j<k} p_j) ∧ t_k ∧ (∏_{j>k} p_j)` (`sW`), the same `2n` terms with the
factor `(-1)ⁿ` instead of `2`. That it does not vanish is checked by wedging with `e₂ ∧ f₂`, which
kills all terms but one and leaves `∏_k p_k = (-1)ⁿ [pt_X̂] ∧ [pt_X] ≠ 0`. -/
theorem lemma2_3_2_1 (hn : 1 ≤ n) :
    varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∈
        extFiltLE F n (4 * n - 2) ∧
      varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∉
        extFiltLE F n (4 * n - 3) := by
  -- It suffices to show that `x = φ([pt_X] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt_X]) = [pt_X][pt_X̂] - [pt_X̂][pt_X]`
  -- lies in `C(V)_{4n-2}` but not in `C(V)_{4n-3}`; we have `x = (-1)ⁿ (∏_k A_k - ∏_k P_k)`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hx : varphi F (m + 1) (pt F (m + 1) ⊗ₜ[F] (1 : S F (m + 1)) -
      (-1 : F) ^ (m + 1) • ((1 : S F (m + 1)) ⊗ₜ[F] pt F (m + 1))) =
      ((-1 : F) ^ (m + 1)) • (((List.range (m + 1)).map (Ak F (m + 1))).prod -
        ((List.range (m + 1)).map (Pk F (m + 1))).prod) := by
    rw [map_sub, map_smul, varphi_pt_one, varphi_one_pt, smul_sub]
  have hdeg : 4 * (m + 1) - 2 = 4 * m + 2 := by omega
  obtain ⟨hmem, hlead⟩ := lead_diff F (m + 1) m le_rfl
  rw [← hdeg] at hmem hlead
  have hxmem : varphi F (m + 1) (pt F (m + 1) ⊗ₜ[F] (1 : S F (m + 1)) -
      (-1 : F) ^ (m + 1) • ((1 : S F (m + 1)) ⊗ₜ[F] pt F (m + 1))) ∈
      CFilt F (m + 1) (4 * (m + 1) - 2) := by
    rw [hx]; exact Submodule.smul_mem _ _ hmem
  -- its image in `C(V)_{4n-2}/C(V)_{4n-3} ≅ ⋀^{4n-2}V` is `(-1)ⁿ sW n ≠ 0`
  have hne : projDeg F (m + 1) (4 * (m + 1) - 2) (psi F (m + 1) (varphi F (m + 1)
      (pt F (m + 1) ⊗ₜ[F] (1 : S F (m + 1)) -
        (-1 : F) ^ (m + 1) • ((1 : S F (m + 1)) ⊗ₜ[F] pt F (m + 1))))) ≠ 0 := by
    rw [hx, map_smul, map_smul, hlead]
    exact smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (sW_ne_zero F (m + 1) (by omega))
  have hnotLT := mt (psiBar_injective F (m + 1) _ hxmem).2 hne
  refine ⟨psi_mem_extFiltLE F (m + 1) _ hxmem, fun h => hnotLT ?_⟩
  exact (psiBar_injective F (m + 1) _ hxmem).1
    (s23_projDeg_eq_zero_of_mem_extFiltLE F (m + 1) (by omega) h)

/-- **Lemma 2.3.2(2)** (`lemma-symmetric-or-alternating-product-of-two-pure-spinors-has-weight-2`).
`φ̃([pt_X] ⊗ 1 + (-1)ⁿ 1 ⊗ [pt_X])` does not belong to `F^{4n-1}(⋀•V)`.

The hypothesis `1 ≤ n` (implied by the paper's standing assumption `n ≥ 2`) is needed: for `n = 0`
the element is `2 ∈ ⋀⁰V`.

"Clear from the above computation": the element is `ψ((-1)ⁿ (∏_k A_k + ∏_k P_k))`, whose
component of degree `4n` is `(-1)ⁿ 2 ∏_k p_k ≠ 0` (the leading terms of `A_k` and `P_k` agree). -/
theorem lemma2_3_2_2 (hn : 1 ≤ n) :
    varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) + (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∉
      extFiltLE F n (4 * n - 1) := by
  -- `φ([pt_X] ⊗ 1 + (-1)ⁿ 1 ⊗ [pt_X]) = (-1)ⁿ (∏_k A_k + ∏_k P_k)`, whose leading term in
  -- `⋀^{4n}V` is `(-1)ⁿ 2 ∏_k p_k ≠ 0` (the computation above).
  have hy : varphi F n (pt F n ⊗ₜ[F] (1 : S F n) + (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) =
      ((-1 : F) ^ n) •
        (((List.range n).map (Ak F n)).prod + ((List.range n).map (Pk F n)).prod) := by
    rw [map_add, map_smul, varphi_pt_one, varphi_one_pt, smul_add]
  have hA := lead_prodA F n n
  have hP := lead_prodP F n n
  have hlead : projDeg F n (4 * n) (psi F n (varphi F n (pt F n ⊗ₜ[F] (1 : S F n) +
      (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)))) =
      ((-1 : F) ^ n * 2) • ((List.range n).map (pW F n)).prod := by
    rw [hy, map_smul, map_smul, map_add, map_add, hA.2, hP.2,
      show aW F n = pW F n from funext (aW_eq_pW F n), mul_smul, two_smul]
  intro h
  have h0 := s23_projDeg_eq_zero_of_mem_extFiltLE F n (by omega : 4 * n - 1 < 4 * n) h
  rw [varphiTilde, LinearMap.comp_apply, hlead] at h0
  exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) two_ne_zero)
    (prod_pW_ne_zero F n) h0

end Field

/-! ## Integrality (§2.3 works over `ℤ`) -/

section Integral

variable (n : ℕ)

/-- `H*(X × X, ℤ) = S ⊗_ℤ S` inside `S_ℚ ⊗_ℚ S_ℚ`: the additive subgroup generated by the `s ⊗ t`
with `s, t ∈ H*(X, ℤ)`. -/
noncomputable def SZZ : AddSubgroup (S ℚ n ⊗[ℚ] S ℚ n) :=
  AddSubgroup.closure {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = s ⊗ₜ[ℚ] t}

theorem s23_mem_ExtZ_iff (α : ExtV ℚ n) :
    α ∈ ExtZ n ↔ α ∈ TauCeti.ExteriorAlgebra.integralLattice (basisV ℚ n) := by
  rw [TauCeti.ExteriorAlgebra.mem_integralLattice_iff]
  change (∀ K, ∃ z : ℤ, (basisExt ℚ n).repr α K = z) ↔ _
  exact forall_congr' fun K => exists_congr fun z => eq_comm

theorem s23_mem_VZ_iff (v : V ℚ n) :
    v ∈ VZ n ↔ ∀ j, ∃ z : ℤ, (basisV ℚ n).repr v j = z := by
  constructor
  · rintro ⟨h1, h2⟩ j
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rcases j' with i | i
    · rw [s23_basisV_repr_inl]; exact h1 i
    · rw [s23_basisV_repr_inr]; exact h2 i
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← s23_basisV_repr_inl]; exact h _
    · rw [← s23_basisV_repr_inr]; exact h _

theorem s23_basisV_mem_VZ (j : Fin (2 * n + 2 * n)) : basisV ℚ n j ∈ VZ n := by
  rw [s23_mem_VZ_iff]
  intro j'
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-- Exterior multiplication by an integral vector preserves `⋀•V` (integral lattice). -/
theorem s23_ι_mul_mem_ExtZ {v : V ℚ n} (hv : v ∈ VZ n) {z : ExtV ℚ n} (hz : z ∈ ExtZ n) :
    ExteriorAlgebra.ι ℚ v * z ∈ ExtZ n := by
  rw [s23_mem_ExtZ_iff] at hz ⊢
  refine TauCeti.ExteriorAlgebra.mul_mem_integralLattice _ ?_ hz
  rw [s23_mem_VZ_iff] at hv
  choose c hc using hv
  rw [← (basisV ℚ n).sum_repr v, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc j, map_smul, Int.cast_smul_eq_zsmul ℚ, ← TauCeti.ExteriorAlgebra.basis_singleton]
  exact Submodule.smul_mem _ _ (TauCeti.ExteriorAlgebra.basis_mem_integralLattice _ _)

/-- Contraction with a functional taking integral values on `V` preserves `⋀•V`. -/
theorem s23_contractLeft_mem_ExtZ {d : Module.Dual ℚ (V ℚ n)}
    (hd : ∀ j, ∃ z : ℤ, d (basisV ℚ n j) = z) {z : ExtV ℚ n} (hz : z ∈ ExtZ n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ (V ℚ n))) d z ∈ ExtZ n := by
  rw [s23_mem_ExtZ_iff] at hz ⊢
  choose c hc using hd
  rw [← (basisV ℚ n).sum_dual_apply_smul_coord d, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc j, map_smul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul ℚ]
  exact Submodule.smul_mem _ _
    (TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice _ j hz)

/-- `L'_v` preserves `⋀•V` for `v ∈ V` (`B₀` is integral). -/
theorem s23_Lprime_mem_ExtZ {v : V ℚ n} (hv : v ∈ VZ n) {z : ExtV ℚ n} (hz : z ∈ ExtZ n) :
    Lprime ℚ n v z ∈ ExtZ n := by
  refine add_mem (s23_ι_mul_mem_ExtZ n hv hz) (s23_contractLeft_mem_ExtZ n (fun j => ?_) hz)
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  change ∃ z : ℤ, B0 ℚ n v _ = z
  rcases j' with i | i
  · rw [s23_basisV_inl, B0_apply]
    exact hv.2 i
  · rw [s23_basisV_inr, B0_apply]
    exact ⟨0, by simp⟩

/-- `ψ'(x)` preserves `⋀•V` for `x` in the integral Clifford algebra. -/
theorem s23_psiPrime_mem_ExtZ {x : C ℚ n} (hx : x ∈ CZ n) {z : ExtV ℚ n} (hz : z ∈ ExtZ n) :
    psiPrime ℚ n x z ∈ ExtZ n := by
  induction hx using Subring.closure_induction generalizing z with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [psiPrime, lift_ι_apply]
    exact s23_Lprime_mem_ExtZ n hv hz
  | zero => simp
  | one => simpa using hz
  | add x y _ _ hx hy => simpa only [map_add, LinearMap.add_apply] using add_mem (hx hz) (hy hz)
  | neg x _ hx => simpa only [map_neg, LinearMap.neg_apply] using neg_mem (hx hz)
  | mul x y _ _ hx hy => simpa only [map_mul, Module.End.mul_apply] using hx (hy hz)

theorem s23_psi_mem_ExtZ {x : C ℚ n} (hx : x ∈ CZ n) : psi ℚ n x ∈ ExtZ n := by
  rw [psi_apply_eq_psiPrime]
  refine s23_psiPrime_mem_ExtZ n hx ?_
  rw [s23_mem_ExtZ_iff]
  exact TauCeti.ExteriorAlgebra.one_mem_integralLattice _

/-- The inductive step of the integral surjectivity: `ψ̄_k` is onto `⋀^k V` over `ℤ`, since the
basis vector `b_{j₁} ∧ ⋯ ∧ b_{j_k}` is the leading term of `ψ(b_{j₁} ⋯ b_{j_k})`, `b_{jᵢ} ∈ V`. -/
theorem s23_psi_lift_step (k : ℕ) {y : ExtV ℚ n} (hy : y ∈ ExtZ n) (hk : y ∈ extFiltLE ℚ n k) :
    ∃ x ∈ CZ n, y - psi ℚ n x ∈ ExtZ n ∧ y - psi ℚ n x ∈ extFiltLE ℚ n k ∧
      projDeg ℚ n k (y - psi ℚ n x) = 0 := by
  choose l hlen hbasis hprod using s23_basisExt_eq_prod ℚ n
  have hy' := hy
  change ∀ K, ∃ z : ℤ, (basisExt ℚ n).repr y K = z at hy'
  choose z hz using hy'
  set xK : Finset (Fin (2 * n + 2 * n)) → C ℚ n :=
    fun K => ((l K).map (CliffordAlgebra.ι (Q ℚ n))).prod with hxK
  have hxK_mem : ∀ K, xK K ∈ CZ n := fun K => by
    refine (CZ n).list_prod_mem fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, rfl⟩ := hbasis K v hv
    exact Subring.subset_closure ⟨_, s23_basisV_mem_VZ n j, rfl⟩
  have hψ : ∀ K, psi ℚ n (xK K) ∈ extFiltLE ℚ n K.card ∧
      projDeg ℚ n K.card (psi ℚ n (xK K)) = basisExt ℚ n K := fun K => by
    have := s23_psi_prod_mem ℚ n (l K)
    rw [hlen K] at this
    rw [hprod K]
    exact this
  -- coordinates above degree `k` vanish
  have hz0 : ∀ K, k < K.card → z K = 0 := by
    intro K hK
    have h1 : (basisExt ℚ n).repr (projDeg ℚ n K.card y) K = (basisExt ℚ n).repr y K := by
      rw [s23_repr_projDeg]; simp
    rw [s23_projDeg_eq_zero_of_mem_extFiltLE ℚ n hK hk, map_zero,
      Finsupp.zero_apply, hz K] at h1
    exact_mod_cast h1.symm
  refine ⟨∑ K, z K • xK K, Subring.sum_mem _ fun K _ => zsmul_mem (hxK_mem K) _, ?_, ?_, ?_⟩
  · exact sub_mem hy (s23_psi_mem_ExtZ n (Subring.sum_mem _ fun K _ => zsmul_mem (hxK_mem K) _))
  all_goals
    have hdecomp : y - psi ℚ n (∑ K, z K • xK K) =
        ∑ K, z K • (basisExt ℚ n K - psi ℚ n (xK K)) := by
      conv_lhs => rw [← (basisExt ℚ n).sum_repr y]
      simp only [map_sum, map_zsmul, hz, Int.cast_smul_eq_zsmul, ← Finset.sum_sub_distrib,
        smul_sub]
    rw [hdecomp]
  · refine Submodule.sum_mem _ fun K _ => ?_
    by_cases hK : K.card ≤ k
    · exact zsmul_mem (sub_mem (s23_mem_extFiltLE_of_mem ℚ n hK (s23_basisExt_mem ℚ n K))
        (s23_extFiltLE_mono ℚ n hK (hψ K).1)) _
    · rw [hz0 K (by omega), zero_smul]
      exact zero_mem _
  · rw [map_sum]
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [map_zsmul, map_sub]
    rcases lt_trichotomy K.card k with hK | hK | hK
    · rw [s23_projDeg_eq_zero_of_mem_extFiltLE ℚ n hK (hψ K).1,
        s23_projDeg_of_mem_ne ℚ n (s23_basisExt_mem ℚ n K) hK.ne, sub_zero, smul_zero]
    · subst hK
      rw [(hψ K).2, s23_projDeg_of_mem ℚ n (s23_basisExt_mem ℚ n K), sub_self, smul_zero]
    · rw [hz0 K hK, zero_smul]

/-- (§2.3, TeX lines 1065–1069) `ψ` is an isomorphism over `ℤ`: it maps the integral Clifford
algebra `C(V)` onto `⋀•V` (the integral lattice). -/
theorem psi_image_CZ : psi ℚ n '' (CZ n : Set (C ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact s23_psi_mem_ExtZ n hx
  -- `ψ̄_k` is onto `⋀^k V` over `ℤ` (a basis vector `e_{j₁} ∧ ⋯ ∧ e_{j_k}` is the leading term of
  -- `ψ(e_{j₁} ⋯ e_{j_k})`), and induction on the filtration
  · have key : ∀ k, ∀ y ∈ ExtZ n, y ∈ extFiltLE ℚ n k → ∃ x ∈ CZ n, psi ℚ n x = y := by
      intro k
      induction k with
      | zero =>
        intro y hy hk
        obtain ⟨x, hx, -, h1, h2⟩ := s23_psi_lift_step n 0 hy hk
        refine ⟨x, hx, (sub_eq_zero.1 (s23_eq_zero_of_projDeg ℚ n fun j => ?_)).symm⟩
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact h2
        · exact s23_projDeg_eq_zero_of_mem_extFiltLE ℚ n hj h1
      | succ k ih =>
        intro y hy hk
        obtain ⟨x, hx, hZ, h1, h2⟩ := s23_psi_lift_step n (k + 1) hy hk
        obtain ⟨x', hx', hx'y⟩ := ih _ hZ (s23_mem_extFiltLE_of_succ ℚ n h1 h2)
        exact ⟨x + x', add_mem hx hx', by rw [map_add, hx'y, add_sub_cancel]⟩
    intro y hy
    obtain ⟨k, hk⟩ := s23_exists_mem_extFiltLE ℚ n y
    obtain ⟨x, hx, rfl⟩ := key k y hy hk
    exact ⟨x, hx, rfl⟩

/-- (2.3.2) `φ̃ = ψ ∘ φ : S ⊗_ℤ S → ⋀•V` is an isomorphism over `ℤ` ("the choice of `B₀` is done so
that the construction is over the integers", Remark 2.3.1). -/
theorem varphiTilde_image_SZZ :
    varphiTilde ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  -- `φ` maps `S ⊗_ℤ S` onto `C(V)` (proof of Lemma 2.2.6), and `ψ` maps `C(V)` onto `⋀•V`
  have hφ : varphi ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (CZ n : Set (C ℚ n)) := by
    have h := AddMonoidHom.map_closure (varphi ℚ n).toAddMonoidHom
      {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = s ⊗ₜ[ℚ] t}
    have himg : (varphi ℚ n).toAddMonoidHom '' {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = s ⊗ₜ[ℚ] t} =
        {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = varphi ℚ n (s ⊗ₜ t)} := by
      ext x
      constructor
      · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
        exact ⟨s, hs, t, ht, rfl⟩
      · rintro ⟨s, hs, t, ht, rfl⟩
        exact ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    rw [himg, closure_varphi_SZ] at h
    have := congrArg (fun H : AddSubgroup (C ℚ n) => (H : Set (C ℚ n))) h
    simpa only [SZZ, AddSubgroup.coe_map, Subring.coe_toAddSubgroup,
      LinearMap.toAddMonoidHom_coe] using this
  rw [varphiTilde, LinearMap.coe_comp, Set.image_comp, hφ, psi_image_CZ]

end Integral

end WeilClasses
