module

public import WeilClasses.Orlov.Defs
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Basis computations for §2.3, §6.1 and §6.3 (helpers)

Helpers (prefix `s61_`, written by prover P10 for `WeilClasses.Orlov.Sec6_3` and
`WeilClasses.Orlov.Sec6_1`) moved upstream by prover SD, so that `WeilClasses.Chevalley.Sec2_3` (the
operator form of Remark 2.3.1, `PiMap_changeB0bar`) and the cited results in
`WeilClasses.External.Huybrechts`, `WeilClasses.External.GolyshevLuntsOrlov.Sec6_1` and
`WeilClasses.External.Orlov` can use them. The names and statements are unchanged. Together with the helpers of `WeilClasses.Orlov.Defs` (exterior bases as
ordered products, `ε_{K,L}`, the expansion of `exp(t c₁(𝒫))`, and `φ_𝒫`, `ψ_{𝒫⁻¹[n]}` on basis
vectors), they give:

* graded commutativity `x ∧ y = (-1)^{jk} y ∧ x` (`s61_mul_comm_of_mem`), homogeneity of exterior
  bases (`s61_repr_eq_zero_of_mem`, `s61_map_mem`) and contraction of an exterior basis vector by a
  coordinate (`s61_contractLeft_coord_basis`);
* the basis vectors `f_A ∧ e_B` of `⋀•V = H*(X̂ × X)` (`s61_beta_eq`, `s61_basisExt_eq_beta`), the
  contraction `δ_{e_a}` on them (`s61_delta_e_beta`), and `Π₀ = φ_𝒫 ⊗ ψ_{𝒫⁻¹}` on them
  (`s61_PiMap0_beta`), with `Π = (-1)ⁿ Π₀` (`s61_PiMap_eq_smul`);
* the decreasing filtration `F_k(⋀•V)` (6.1.5): membership, products, `⋀ρ_g`, degree components
  (`s61_mem_extFiltGE`, `s61_mul_mem_extFiltGE`, `s61_rhoExt_mem_extFiltGE`, `s61_projDeg_rhoExt`),
  and `exp(c)` for `c ∈ ⋀²V` (`s61_exp_sub_one_mem`, `s61_projDeg_two_exp`);
* the operator form of Remark 2.3.1: `E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})` (`s61_changeB0bar_eq_G`)
  and `Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π` (`s61_PiMap_D`), whence `PiMap_changeB0bar`
  (`WeilClasses.Chevalley.Sec2_3`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Graded commutativity and contraction in exterior algebras (generic) -/

section S61Graded

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]
  (b : Module.Basis ι R M)

/-- The exterior basis is homogeneous: a `k`-vector has no coordinates on index sets of other
cardinalities. -/
theorem s61_repr_eq_zero_of_mem {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M)
    {s : Finset ι} (hs : s.card ≠ k) : b.ExteriorAlgebra.repr x s = 0 := by
  rw [Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
    Set.powersetCard.prodEquiv_symm_apply]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (Ne.symm hs) hx

theorem s61_zsmul_neg_one_pow {A : Type*} [Ring A] [Algebra R A] (k : ℕ) (y : A) :
    ((-1 : ℤˣ) ^ k) • y = (-1 : R) ^ k • y := by
  rw [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    ← Int.cast_smul_eq_zsmul R]
  simp

/-- Graded commutativity: `x ∧ y = (-1)^{jk} y ∧ x` for `x ∈ ⋀^j`, `y ∈ ⋀^k`. -/
theorem s61_mul_comm_of_mem {j k : ℕ} {x y : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^j M)
    (hy : y ∈ ⋀[R]^k M) : x * y = (-1 : R) ^ (j * k) • (y * x) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, s61_zsmul_neg_one_pow (R := R), mul_comm k j]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_mul, smul_add]
    | smul r y _ hy => rw [mul_smul_comm, hy, smul_mul_assoc, smul_comm]
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul, hx, hz, mul_add, smul_add]
  | smul r x _ hx => rw [smul_mul_assoc, hx, mul_smul_comm, smul_comm]

theorem s61_ι_mul_comm_of_mem (v : M) {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    ExteriorAlgebra.ι R v * x = (-1 : R) ^ k • (x * ExteriorAlgebra.ι R v) := by
  have hv : ExteriorAlgebra.ι R v ∈ ⋀[R]^1 M := by simp
  rw [s61_mul_comm_of_mem hv hx, one_mul]

end S61Graded

section S61Graded2

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem s61_map_mem (g : M →ₗ[R] N) {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    ExteriorAlgebra.map g x ∈ ⋀[R]^k N := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact ExteriorAlgebra.ιMulti_range R k ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end S61Graded2

section S61Contract

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]
  (b : Module.Basis ι R M)

/-- Contraction by a coordinate erases it from an exterior basis vector, with the sign counting
the smaller indices. -/
theorem s61_contractLeft_coord_basis (i : ι) (s : Finset ι) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then (-1 : R) ^ (s.filter (· < i)).card • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    rw [s61_basis_empty, ite_eq_right (Finset.notMem_empty i)]
    exact contractLeft_one (Q := (0 : QuadraticForm R M)) (b.coord i)
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [s61_basis_insert_min b a s ha, contractLeft_ι_mul, ih, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hia : a = i
    · subst hia
      have hf : (insert a s).filter (· < a) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hx) hxa
        · exact lt_irrefl _ hxa
        · exact lt_asymm hxa (ha x hx)
      rw [ite_eq_left rfl, ite_eq_right has, mul_zero, sub_zero, one_smul,
        ite_eq_left (Finset.mem_insert_self _ _), hf, Finset.card_empty, pow_zero, one_smul,
        Finset.erase_insert has]
    · rw [ite_eq_right hia, zero_smul, zero_sub]
      by_cases his : i ∈ s
      · have hai : a < i := ha i his
        have hf : (insert a s).filter (· < i) = insert a (s.filter (· < i)) := by
          rw [Finset.filter_insert, ite_eq_left hai]
        have ha' : a ∉ s.filter (· < i) := fun h => has (Finset.mem_filter.mp h).1
        rw [ite_eq_left his, ite_eq_left (Finset.mem_insert_of_mem his), hf,
          Finset.card_insert_of_notMem ha', mul_smul_comm,
          ← s61_basis_insert_min b a (s.erase i) (fun x hx => ha x (Finset.mem_of_mem_erase hx)),
          Finset.erase_insert_of_ne hia, pow_succ, mul_neg_one, neg_smul]
      · have : i ∉ insert a s := by
          simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm hia, his⟩
        rw [ite_eq_right his, ite_eq_right this, mul_zero, neg_zero]

end S61Contract

/-! ## The model: `δ_{e_a}`, the basis vectors `f_A ∧ e_B` of `⋀•V`, and `Π` on them -/

section S61Delta

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- `B₀(e_i, ·) : (θ, w) ↦ θ(e_i)` is the coordinate of `basisV` at `f_i`. -/
theorem s61_B0_e_eq_coord (i : Fin (2 * n)) :
    B0 F n ((0, e F n i) : V F n) = (basisV F n).coord (Fin.castAdd (2 * n) i) := by
  refine (basisV F n).ext fun j => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, B0_apply]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · rw [s61_basisV_castAdd]
    simp only [f, e, LinearMap.proj_apply, Pi.single_apply]
    by_cases h : l = i
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right]
      exact fun h' => h (Fin.castAdd_injective _ _ h')
  · rw [s61_basisV_natAdd]
    simp only [LinearMap.zero_apply]
    rw [ite_eq_right]
    exact fun h => absurd h (by
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega)

omit [CharZero F] in
theorem s61_card_le_sumIdx (K : Finset (Fin (2 * n))) : K.card ≤ sumIdx n K := by
  rw [Finset.card_eq_sum_ones, sumIdx]
  exact Finset.sum_le_sum fun i _ => by omega

omit [CharZero F] in
theorem s61_sumIdx_insert {a : Fin (2 * n)} {K : Finset (Fin (2 * n))} (ha : a ∉ K) :
    sumIdx n (insert a K) = ((a : ℕ) + 1) + sumIdx n K := by
  rw [sumIdx, Finset.sum_insert ha, ← sumIdx]

omit [CharZero F] in
theorem s61_delta_e_basisExt (a : Fin (2 * n)) (M : Finset (Fin (2 * n + 2 * n))) :
    delta F n ((0, e F n a) : V F n) (basisExt F n M) =
      if Fin.castAdd (2 * n) a ∈ M then
        (-1 : F) ^ (M.filter (· < Fin.castAdd (2 * n) a)).card •
          basisExt F n (M.erase (Fin.castAdd (2 * n) a))
      else 0 := by
  rw [delta, LinearMap.comp_apply, s61_B0_e_eq_coord, basisExt, s61_contractLeft_coord_basis]

end S61Delta

section S61Beta

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- `π_X̂^*f_A ∪ π_X^*e_B` is the exterior basis vector indexed by `A ⊔ B`. -/
theorem s61_beta_eq (A B : Finset (Fin (2 * n))) :
    pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B) =
      basisExt F n (A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding) := by
  classical
  rw [s61_pullXHat_basisSHat, s61_pullX_basisS, basisExt, s61_basis_mul_basis, ite_eq_left]
  · have h0 : s61_inv (A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding)
        (B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_lt]
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
      simp only [RelEmbedding.coe_toEmbedding, Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply,
        Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    rw [h0, pow_zero, one_smul]
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
    have := congrArg Fin.val hj
    simp only [RelEmbedding.coe_toEmbedding, Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply,
      Fin.val_castAdd, Fin.val_natAdd] at this
    omega

omit [CharZero F] in
theorem s61_castAdd_lt_natAdd (i j : Fin (2 * n)) :
    (Fin.castAdd (2 * n) i : Fin (2 * n + 2 * n)) < Fin.natAdd (2 * n) j := by
  rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega

omit [CharZero F] in
theorem s61_natAdd_lt_natAdd (x a : Fin (2 * n)) :
    (Fin.natAddOrderEmb (2 * n)).toEmbedding x < (Fin.natAdd (2 * n) a : Fin (2 * n + 2 * n)) ↔
      x < a := by
  simp only [RelEmbedding.coe_toEmbedding, Fin.natAddOrderEmb_apply, Fin.lt_def, Fin.val_natAdd]
  omega

omit [CharZero F] in
/-- `δ_a (f_A ∧ e_B) = ± f_{A ∖ {a}} ∧ e_B`. -/
theorem s61_delta_e_beta (a : Fin (2 * n)) (A B : Finset (Fin (2 * n))) :
    delta F n ((0, e F n a) : V F n) (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) =
      if a ∈ A then (-1 : F) ^ (A.filter (· < a)).card •
        (pullXHat F n (basisSHat F n (A.erase a)) * pullX F n (basisS F n B)) else 0 := by
  classical
  rw [s61_beta_eq, s61_beta_eq, s61_delta_e_basisExt]
  have hmem : Fin.castAdd (2 * n) a ∈ A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
      B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding ↔ a ∈ A := by
    simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply]
    constructor
    · rintro (⟨i, hi, hi'⟩ | ⟨j, _, hj⟩)
      · rw [Fin.castAdd_inj] at hi'; exact hi' ▸ hi
      · exact absurd hj (s61_castAdd_lt_natAdd n a j).ne'
    · intro h; exact Or.inl ⟨a, h, rfl⟩
  by_cases haA : a ∈ A
  · rw [ite_eq_left (hmem.mpr haA), ite_eq_left haA]
    have hB : (B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).filter
        (· < Fin.castAdd (2 * n) a) = ∅ := by
      refine Finset.filter_false_of_mem fun x hx => ?_
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      exact not_lt.mpr (s61_castAdd_lt_natAdd n a j).le
    have hfilt : ((A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).filter (· < Fin.castAdd (2 * n) a)).card =
        (A.filter (· < a)).card := by
      rw [Finset.filter_union, hB, Finset.union_empty, Finset.filter_map, Finset.card_map]
      congr 1
    have hB' : (B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).erase (Fin.castAdd (2 * n) a) =
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
      refine Finset.erase_eq_of_notMem fun h => ?_
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
      simp only [RelEmbedding.coe_toEmbedding, Fin.natAddOrderEmb_apply] at hj
      exact (s61_castAdd_lt_natAdd n a j).ne' hj
    have hA' : (A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding).erase (Fin.castAdd (2 * n) a) =
        (A.erase a).map (Fin.castAddOrderEmb (2 * n)).toEmbedding := by
      rw [Finset.map_erase]; rfl
    have herase : (A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).erase (Fin.castAdd (2 * n) a) =
        (A.erase a).map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
          B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
      rw [Finset.erase_union_distrib, hA', hB']
    rw [hfilt, herase]
  · rw [ite_eq_right (fun h => haA (hmem.mp h)), ite_eq_right haA]

omit [CharZero F] in
/-- Every basis vector of `⋀•V` is `f_L ∧ e_K` for some `L, K`. -/
theorem s61_basisExt_eq_beta (M : Finset (Fin (2 * n + 2 * n))) :
    ∃ L K : Finset (Fin (2 * n)), L.card + K.card = M.card ∧
      basisExt F n M = pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K) := by
  classical
  set L := M.preimage (Fin.castAdd (2 * n)) (Fin.castAdd_injective _ _).injOn
  set K := M.preimage (Fin.natAdd (2 * n)) (Fin.natAdd_injective _ _).injOn
  have hM : M = L.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
      K.map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
    ext x
    refine Fin.addCases (fun i => ?_) (fun i => ?_) x
    · simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply, Finset.mem_preimage, L, K]
      constructor
      · intro h; exact Or.inl ⟨i, h, rfl⟩
      · rintro (⟨j, hj, hji⟩ | ⟨j, _, hj⟩)
        · rw [Fin.castAdd_inj] at hji; rwa [hji] at hj
        · exact absurd hj (s61_castAdd_lt_natAdd n i j).ne'
    · simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply, Finset.mem_preimage, L, K]
      constructor
      · intro h; exact Or.inr ⟨i, h, rfl⟩
      · rintro (⟨j, _, hj⟩ | ⟨j, hj, hji⟩)
        · exact absurd hj (s61_castAdd_lt_natAdd n j i).ne
        · rw [Fin.natAdd_inj] at hji; rwa [hji] at hj
  refine ⟨L, K, ?_, ?_⟩
  · conv_rhs => rw [hM]
    rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
    exact (s61_castAdd_lt_natAdd n i j).ne' hj
  · rw [s61_beta_eq, ← hM]

theorem s61_PiMap0_beta (L K : Finset (Fin (2 * n))) :
    PiMap0 F n (pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) =
      ((((-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2) * (-1 : F) ^ (Lᶜ.card * Lᶜ.card)) *
          (-1 : F) ^ s61_inv L Lᶜ) *
        (((-1 : F) ^ Kᶜ.card * (-1 : F) ^ (Kᶜ.card * (Kᶜ.card - 1) / 2)) *
          (-1 : F) ^ s61_inv K Kᶜ)) •
        (pullX F n (basisS F n Lᶜ) * pullXHat F n (basisSHat F n Kᶜ)) := by
  rw [PiMap0, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    ← kunnethHatX_tmul, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, s61_phiP_basisSHat,
    s61_psiPinv_basisS, TensorProduct.smul_tmul_smul, map_smul, kunnethXHat_tmul]

theorem s61_psiPinvShift_eq_smul : psiPinvShift F n = (-1 : F) ^ n • psiPinv F n := by
  rw [psiPinvShift, psiPinv, chPinvShift, map_smul, map_smul]

theorem s61_PiMap_eq_smul : PiMap F n = (-1 : F) ^ n • PiMap0 F n := by
  rw [PiMap, PiMap0, s61_psiPinvShift_eq_smul, TensorProduct.map_smul_right, LinearMap.smul_comp,
    LinearMap.comp_smul]

theorem s61_rhoExt_mem (g : Spin F n) {d : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^d (V F n)) :
    rhoExt F n g x ∈ ⋀[F]^d (V F n) := s61_map_mem _ hx

omit [CharZero F] in
theorem s61_commute_c1P (z : ExtV F n) : Commute (c1P F n) z := by
  rw [s61_c1P_eq]
  exact Commute.sum_left _ _ _ fun i _ => s61_commute_a F n i z

omit [CharZero F] in
theorem s61_isNilpotent_smul_c1P (t : F) : IsNilpotent (t • c1P F n) := by
  rw [s61_c1P_eq]; exact s61_isNilpotent_smul_sum F n t Finset.univ

end S61Beta

/-! ## The decreasing filtration `F_k(⋀•V)` (6.1.5) -/

section S61Filtration

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_mem_extFiltGE {k i : ℕ} (hi : k ≤ i) {x : ExtV F n} (hx : x ∈ ⋀[F]^i (V F n)) :
    x ∈ extFiltGE F n k :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hx)

omit [CharZero F] in
theorem s61_extFiltGE_induction {k : ℕ} {P : ExtV F n → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmem : ∀ i, k ≤ i → ∀ x ∈ ⋀[F]^i (V F n), P x)
    {x : ExtV F n} (hx : x ∈ extFiltGE F n k) : P x := by
  rw [extFiltGE] at hx
  refine Submodule.iSup_induction _ (motive := P) hx (fun i x hx' => ?_) h0 hadd
  exact Submodule.iSup_induction _ (motive := P) hx' (fun h y hy => hmem i h y hy) h0 hadd

omit [CharZero F] in
theorem s61_extFiltGE_mono {k l : ℕ} (h : k ≤ l) {x : ExtV F n} (hx : x ∈ extFiltGE F n l) :
    x ∈ extFiltGE F n k :=
  s61_extFiltGE_induction F n (zero_mem _) (fun _ _ => add_mem)
    (fun _ hi _ hy => s61_mem_extFiltGE F n (h.trans hi) hy) hx

theorem s61_rhoExt_mem_extFiltGE (g : Spin F n) {k : ℕ} {x : ExtV F n}
    (hx : x ∈ extFiltGE F n k) : rhoExt F n g x ∈ extFiltGE F n k :=
  s61_extFiltGE_induction F n (P := fun x => rhoExt F n g x ∈ extFiltGE F n k)
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun i hi y hy => s61_mem_extFiltGE F n hi (s61_rhoExt_mem F n g hy)) hx

omit [CharZero F] in
theorem s61_mul_mem_extFiltGE {a k : ℕ} {z y : ExtV F n} (hz : z ∈ extFiltGE F n a)
    (hy : y ∈ extFiltGE F n k) : z * y ∈ extFiltGE F n (a + k) := by
  refine s61_extFiltGE_induction F n (P := fun z => z * y ∈ extFiltGE F n (a + k))
    (by rw [zero_mul]; exact zero_mem _)
    (fun x x' hx hx' => by rw [add_mul]; exact add_mem hx hx') (fun i hi z hz => ?_) hz
  refine s61_extFiltGE_induction F n (P := fun y => z * y ∈ extFiltGE F n (a + k))
    (by rw [mul_zero]; exact zero_mem _)
    (fun x x' hx hx' => by rw [mul_add]; exact add_mem hx hx') (fun j hj y hy => ?_) hy
  exact s61_mem_extFiltGE F n (Nat.add_le_add hi hj) (SetLike.mul_mem_graded hz hy)

omit [CharZero F] in
theorem s61_projDeg_eq_zero_of_mem_extFiltGE {k : ℕ} {y : ExtV F n}
    (hy : y ∈ extFiltGE F n (k + 1)) : projDeg F n k y = 0 := by
  refine s61_extFiltGE_induction F n (P := fun y => projDeg F n k y = 0) (map_zero _)
    (fun x x' hx hx' => by rw [map_add, hx, hx', add_zero]) (fun i hi y hy => ?_) hy
  rw [projDeg, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) hy (by omega)]

omit [CharZero F] in
theorem s61_projDeg_of_mem {k : ℕ} {y : ExtV F n} (hy : y ∈ ⋀[F]^k (V F n)) :
    projDeg F n k y = y := by
  rw [projDeg, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) hy]

omit [CharZero F] in
theorem s61_projDeg_of_mem_ne {j k : ℕ} (h : j ≠ k) {y : ExtV F n} (hy : y ∈ ⋀[F]^j (V F n)) :
    projDeg F n k y = 0 := by
  rw [projDeg, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) hy h]

theorem s61_projDeg_rhoExt (g : Spin F n) (k : ℕ) (x : ExtV F n) :
    projDeg F n k (rhoExt F n g x) = rhoExt F n g (projDeg F n k x) := by
  have h : (projDeg F n k) ∘ₗ (rhoExt F n g).toLinearMap =
      (rhoExt F n g).toLinearMap ∘ₗ projDeg F n k := by
    refine (basisExt F n).ext fun M => ?_
    have hM : basisExt F n M ∈ ⋀[F]^M.card (V F n) := s61_basis_mem _ M
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    by_cases hk : M.card = k
    · subst hk
      rw [s61_projDeg_of_mem F n (s61_rhoExt_mem F n g hM), s61_projDeg_of_mem F n hM]
    · rw [s61_projDeg_of_mem_ne F n hk (s61_rhoExt_mem F n g hM), s61_projDeg_of_mem_ne F n hk hM,
        map_zero]
  exact congrArg (fun φ : ExtV F n →ₗ[F] ExtV F n => φ x) h

omit [CharZero F] in
/-- An element of `⋀^{2}V` is nilpotent (`⋀^d V = 0` for `d > 4n`). -/
theorem s61_isNilpotent_of_mem_two {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) : IsNilpotent c := by
  refine ⟨2 * n + 1, ?_⟩
  have hmem : c ^ (2 * n + 1) ∈ ⋀[F]^((2 * n + 1) • 2) (V F n) := SetLike.pow_mem_graded _ hc
  have hfin : Module.finrank F (V F n) < (2 * n + 1) • 2 := by
    rw [Module.finrank_eq_card_basis (basisV F n), Fintype.card_fin, smul_eq_mul]; omega
  have := exteriorPower.eq_zero_of_finrank_lt _ hfin ⟨_, hmem⟩
  exact congrArg Subtype.val this

/-- `exp(c) - 1 ∈ F_2(⋀•V)` for `c ∈ ⋀²V`. -/
theorem s61_exp_sub_one_mem {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp c - 1 ∈ extFiltGE F n 2 := by
  obtain ⟨N, hN⟩ := s61_isNilpotent_of_mem_two F n hc
  rw [IsNilpotent.exp_eq_sum (k := N + 1) (by rw [pow_succ, hN, zero_mul]),
    Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact s61_mem_extFiltGE F n (by simp) (SetLike.pow_mem_graded (j + 1) hc)

omit [CharZero F] in
theorem s61_ι_mem_one (v : V F n) : ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (V F n) := by simp

omit [CharZero F] in
theorem s61_ι_mul_ι_mem_two (u v : V F n) :
    ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v ∈ ⋀[F]^2 (V F n) :=
  SetLike.mul_mem_graded (s61_ι_mem_one F n u) (s61_ι_mem_one F n v)

omit [CharZero F] in
theorem s61_c1P_mem : c1P F n ∈ ⋀[F]^2 (V F n) := by
  rw [s61_c1P_eq]
  exact Submodule.sum_mem _ fun i _ => by rw [s61_a_eq]; exact s61_ι_mul_ι_mem_two F n _ _

theorem s61_beta_mem (g : Spin F n) :
    (2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n)) ∈ ⋀[F]^2 (V F n) :=
  Submodule.smul_mem _ _ (sub_mem (s61_c1P_mem F n) (s61_rhoExt_mem F n g (s61_c1P_mem F n)))

/-- `exp(c) - 1 - c ∈ F_4(⋀•V)` for `c ∈ ⋀²V`. -/
theorem s61_exp_sub_one_sub_mem {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp c - 1 - c ∈ extFiltGE F n 4 := by
  obtain ⟨N, hN⟩ := s61_isNilpotent_of_mem_two F n hc
  rw [IsNilpotent.exp_eq_sum (k := N + 2) (by rw [pow_add, hN, zero_mul]),
    Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    add_assoc, show ∀ s : ExtV F n, s + (c + 1) - 1 - c = s from fun s => by abel]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact s61_mem_extFiltGE F n (by simp; omega) (SetLike.pow_mem_graded (j + 1 + 1) hc)

/-- `c₁(N_g)` is determined by `ρ'_g`: the degree-`2` part of `exp(c)` is `c`. -/
theorem s61_projDeg_two_exp {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    projDeg F n 2 (IsNilpotent.exp c) = c := by
  have h1 : (1 : ExtV F n) ∈ ⋀[F]^0 (V F n) := SetLike.one_mem_graded _
  have h := s61_exp_sub_one_sub_mem F n hc
  have hd : IsNilpotent.exp c = (IsNilpotent.exp c - 1 - c) + c + 1 := by abel
  rw [hd, map_add, map_add, s61_projDeg_eq_zero_of_mem_extFiltGE F n (s61_extFiltGE_mono F n
    (by omega) h), s61_projDeg_of_mem F n hc, s61_projDeg_of_mem_ne F n (by omega) h1, zero_add,
    add_zero]

end S61Filtration

section S61Dual

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_dual_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    θ w = ∑ i, θ (e F n i) * w i := by
  conv_lhs => rw [show w = ∑ i, w i • e F n i by ext j; simp [e, Pi.single_apply]]
  simp [map_sum, mul_comm]

end S61Dual

/-! ## The operator form of Remark 2.3.1: `Π ∘ E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` -/

section S61Change

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `∂_j`: contraction by the `j`-th coordinate of the basis `basisV` of `V`. -/
noncomputable def s61_dd (j : Fin (2 * n + 2 * n)) : Module.End F (ExtV F n) :=
  contractLeft (Q := (0 : QuadraticForm F (V F n))) ((basisV F n).coord j)

omit [CharZero F] in
theorem s61_dd_cast_eq_delta (a : Fin (2 * n)) :
    s61_dd F n (Fin.castAdd (2 * n) a) = delta F n ((0, e F n a) : V F n) := by
  rw [s61_dd, ← s61_B0_e_eq_coord]; rfl

omit [CharZero F] in
/-- `∂_{e_a} (f_A ∧ e_B) = ± f_A ∧ e_{B ∖ {a}}`. -/
theorem s61_dd_nat_beta (a : Fin (2 * n)) (A B : Finset (Fin (2 * n))) :
    s61_dd F n (Fin.natAdd (2 * n) a) (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) =
      if a ∈ B then (-1 : F) ^ (A.card + (B.filter (· < a)).card) •
        (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n (B.erase a))) else 0 := by
  classical
  rw [s61_beta_eq, s61_beta_eq, s61_dd, basisExt, s61_contractLeft_coord_basis]
  have hmem : Fin.natAdd (2 * n) a ∈ A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
      B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding ↔ a ∈ B := by
    simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply]
    constructor
    · rintro (⟨i, _, hi⟩ | ⟨j, hj, hj'⟩)
      · exact absurd hi (s61_castAdd_lt_natAdd n i a).ne
      · rw [Fin.natAdd_inj] at hj'; exact hj' ▸ hj
    · intro h; exact Or.inr ⟨a, h, rfl⟩
  by_cases haB : a ∈ B
  · rw [ite_eq_left (hmem.mpr haB), ite_eq_left haB]
    have hfilt : ((A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).filter (· < Fin.natAdd (2 * n) a)).card =
        A.card + (B.filter (· < a)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint]
      · congr 1
        · rw [Finset.filter_true_of_mem, Finset.card_map]
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
          exact s61_castAdd_lt_natAdd n i a
        · rw [Finset.filter_map, Finset.card_map]
          congr 1
          exact Finset.filter_congr fun x _ => s61_natAdd_lt_natAdd n x a
      · rw [Finset.disjoint_left]
        intro x hx hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hx).1
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hy).1
        exact (s61_castAdd_lt_natAdd n i j).ne' hj
    have herase : (A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding).erase (Fin.natAdd (2 * n) a) =
        A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
          (B.erase a).map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
      rw [Finset.erase_union_distrib, Finset.map_erase, Finset.erase_eq_of_notMem]
      · rfl
      · intro h
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
        simp only [RelEmbedding.coe_toEmbedding, Fin.castAddOrderEmb_apply] at hj
        exact (s61_castAdd_lt_natAdd n j a).ne hj
    rw [hfilt, herase]
  · rw [ite_eq_right (fun h => haB (hmem.mp h)), ite_eq_right haB]

/-- `D_i = ∂_{f_i} ∂_{e_i}` (first contract `e_i`, then `f_i`). -/
noncomputable def s61_D (i : Fin (2 * n)) : Module.End F (ExtV F n) :=
  s61_dd F n (Fin.castAdd (2 * n) i) * s61_dd F n (Fin.natAdd (2 * n) i)

omit [CharZero F] in
theorem s61_ι_e_mul_basisS (i : Fin (2 * n)) (C : Finset (Fin (2 * n))) :
    ExteriorAlgebra.ι F (e F n i) * basisS F n C =
      if i ∈ C then 0 else (-1 : F) ^ (C.filter (· < i)).card • basisS F n (insert i C) := by
  rw [← s61_basisFun_apply, basisS, s61_ι_mul_basis]

omit [CharZero F] in
theorem s61_ι_f_mul_basisSHat (i : Fin (2 * n)) (D : Finset (Fin (2 * n))) :
    ExteriorAlgebra.ι F (f F n i) * basisSHat F n D =
      if i ∈ D then 0 else (-1 : F) ^ (D.filter (· < i)).card • basisSHat F n (insert i D) := by
  rw [← s61_dualBasis_apply, basisSHat, s61_ι_mul_basis]

omit [CharZero F] in
/-- `(e_i ∧ f_i) ∧ (e_C ∧ f_D) = ± e_{C ∪ {i}} ∧ f_{D ∪ {i}}`. -/
theorem s61_a_mul (i : Fin (2 * n)) (C D : Finset (Fin (2 * n))) :
    s61_a F n i * (pullX F n (basisS F n C) * pullXHat F n (basisSHat F n D)) =
      if i ∈ C ∨ i ∈ D then 0 else
        ((-1 : F) ^ C.card * (-1 : F) ^ (C.filter (· < i)).card *
          (-1 : F) ^ (D.filter (· < i)).card) •
          (pullX F n (basisS F n (insert i C)) * pullXHat F n (basisSHat F n (insert i D))) := by
  have hcomm : pullXHat F n (ExteriorAlgebra.ι F (f F n i)) * pullX F n (basisS F n C) =
      (-1 : F) ^ (1 * C.card) • (pullX F n (basisS F n C) * pullXHat F n (ExteriorAlgebra.ι F (f F n i))) :=
    s61_mul_comm_of_mem (s61_map_mem _ (by simp)) (s61_map_mem _ (s61_basis_mem _ C))
  have h : s61_a F n i * (pullX F n (basisS F n C) * pullXHat F n (basisSHat F n D)) =
      (-1 : F) ^ C.card • (pullX F n (ExteriorAlgebra.ι F (e F n i) * basisS F n C) *
        pullXHat F n (ExteriorAlgebra.ι F (f F n i) * basisSHat F n D)) := by
    rw [s61_a, map_mul, map_mul, mul_assoc, ← mul_assoc (pullXHat F n _) (pullX F n _), hcomm,
      one_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ _ (pullXHat F n _)]
  rw [h, s61_ι_e_mul_basisS, s61_ι_f_mul_basisSHat]
  by_cases hC : i ∈ C
  · rw [ite_eq_left hC, ite_eq_left (Or.inl hC), map_zero, zero_mul, smul_zero]
  · by_cases hD : i ∈ D
    · rw [ite_eq_left hD, ite_eq_left (Or.inr hD), map_zero, mul_zero, smul_zero]
    · rw [ite_eq_right hC, ite_eq_right hD, ite_eq_right (by tauto), map_smul, map_smul,
        smul_mul_smul_comm, smul_smul, mul_assoc]

omit [CharZero F] in
/-- The sign bookkeeping for removing `i` from both `A` and `B`. -/
theorem s61_erase_facts {i : Fin (2 * n)} {A : Finset (Fin (2 * n))} (hA : i ∈ A) :
    A.card = (A.erase i).card + 1 ∧ (A.erase i)ᶜ.card = Aᶜ.card + 1 ∧
      (A.erase i)ᶜ.card * ((A.erase i)ᶜ.card - 1) / 2 = Aᶜ.card * (Aᶜ.card - 1) / 2 + Aᶜ.card ∧
      s61_inv A Aᶜ = (Aᶜ.filter (· < i)).card + s61_inv (A.erase i) Aᶜ ∧
      s61_inv (A.erase i) (A.erase i)ᶜ = s61_inv (A.erase i) Aᶜ + ((A.erase i).filter (i < ·)).card ∧
      ((A.erase i).filter (· < i)).card + ((A.erase i).filter (i < ·)).card = (A.erase i).card ∧
      (A.filter (· < i)).card = ((A.erase i).filter (· < i)).card := by
  classical
  have hi' : i ∉ A.erase i := Finset.notMem_erase i A
  have hic : i ∉ Aᶜ := fun h => Finset.mem_compl.mp h hA
  have hcompl : (A.erase i)ᶜ = insert i Aᶜ := Finset.compl_erase
  have hcard : (A.erase i)ᶜ.card = Aᶜ.card + 1 := by
    rw [hcompl, Finset.card_insert_of_notMem hic]
  refine ⟨(Finset.card_erase_add_one hA).symm, hcard, ?_, ?_, ?_, s61_card_filter_lt_add_gt hi', ?_⟩
  · rw [hcard, Nat.add_sub_cancel, s61_tri_succ]
  · have := s61_inv_insert_left hi' Aᶜ
    rwa [Finset.insert_erase hA] at this
  · rw [hcompl, s61_inv_insert_right hic]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxi⟩; exact ⟨⟨hxi.ne, hx⟩, hxi⟩
    · rintro ⟨⟨_, hx⟩, hxi⟩; exact ⟨hx, hxi⟩

/-- **`Π D_i = a_i ∪ Π`** on the basis vectors `f_A ∧ e_B` (`a_i = e_i ∧ f_i`). -/
theorem s61_PiMap_D_beta (i : Fin (2 * n)) (A B : Finset (Fin (2 * n))) :
    PiMap F n (s61_D F n i (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B))) =
      s61_a F n i * PiMap F n (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) := by
  rw [s61_PiMap_eq_smul, LinearMap.smul_apply, LinearMap.smul_apply, s61_PiMap0_beta, smul_smul,
    mul_smul_comm, s61_a_mul, s61_D, Module.End.mul_apply, s61_dd_nat_beta]
  by_cases hB : i ∈ B
  · rw [ite_eq_left hB, map_smul, s61_dd_cast_eq_delta, s61_delta_e_beta]
    by_cases hA : i ∈ A
    · have hAc : i ∉ Aᶜ := fun h => Finset.mem_compl.mp h hA
      have hBc : i ∉ Bᶜ := fun h => Finset.mem_compl.mp h hB
      rw [ite_eq_left hA, ite_eq_right (by tauto), map_smul, map_smul, s61_PiMap0_beta,
        ← Finset.compl_erase, ← Finset.compl_erase]
      simp only [smul_smul]
      congr 1
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := s61_erase_facts n hA
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := s61_erase_facts n hB
      have c1 := s61_card_add_card_compl n A
      have c2 := s61_card_add_card_compl n B
      have q1 := s61_mul_self_mod_two Aᶜ.card
      have q2 := s61_mul_self_mod_two (A.erase i)ᶜ.card
      simp only [← pow_add]
      exact s61_neg_one_pow_congr (by omega)
    · rw [ite_eq_right hA, smul_zero, map_zero, smul_zero,
        ite_eq_left (Or.inl (Finset.mem_compl.mpr hA)), smul_zero]
  · rw [ite_eq_right hB, map_zero, map_zero, smul_zero,
      ite_eq_left (Or.inr (Finset.mem_compl.mpr hB)), smul_zero]

theorem s61_PiMap_D (i : Fin (2 * n)) (y : ExtV F n) :
    PiMap F n (s61_D F n i y) = s61_a F n i * PiMap F n y := by
  have h : PiMap F n ∘ₗ s61_D F n i = LinearMap.mulLeft F (s61_a F n i) ∘ₗ PiMap F n := by
    refine (basisExt F n).ext fun M => ?_
    obtain ⟨L, K, -, hM⟩ := s61_basisExt_eq_beta F n M
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, hM,
      s61_PiMap_D_beta]
  exact congrArg (fun φ : ExtV F n →ₗ[F] ExtV F n => φ y) h

omit [CharZero F] in
theorem s61_dd_dd_self (j : Fin (2 * n + 2 * n)) (x : ExtV F n) :
    s61_dd F n j (s61_dd F n j x) = 0 :=
  contractLeft_contractLeft _ x

omit [CharZero F] in
theorem s61_dd_comm (j k : Fin (2 * n + 2 * n)) (x : ExtV F n) :
    s61_dd F n j (s61_dd F n k x) = -(s61_dd F n k (s61_dd F n j x)) :=
  contractLeft_comm _ _ x

omit [CharZero F] in
theorem s61_dd_ι_mul (j : Fin (2 * n + 2 * n)) (v : V F n) (x : ExtV F n) :
    s61_dd F n j (ExteriorAlgebra.ι F v * x) =
      (basisV F n).coord j v • x - ExteriorAlgebra.ι F v * s61_dd F n j x :=
  contractLeft_ι_mul _ v x

omit [CharZero F] in
theorem s61_dd_D (j : Fin (2 * n + 2 * n)) (i : Fin (2 * n)) (x : ExtV F n) :
    s61_dd F n j (s61_D F n i x) = s61_D F n i (s61_dd F n j x) := by
  simp only [s61_D, Module.End.mul_apply]
  rw [s61_dd_comm F n j, s61_dd_comm F n j, map_neg, neg_neg]

omit [CharZero F] in
theorem s61_D_D_cast (i : Fin (2 * n)) (x : ExtV F n) :
    s61_dd F n (Fin.castAdd (2 * n) i) (s61_D F n i x) = 0 := by
  simp only [s61_D, Module.End.mul_apply, s61_dd_dd_self]

omit [CharZero F] in
theorem s61_D_D_nat (i : Fin (2 * n)) (x : ExtV F n) :
    s61_dd F n (Fin.natAdd (2 * n) i) (s61_D F n i x) = 0 := by
  rw [s61_dd_D, s61_D, Module.End.mul_apply, s61_dd_dd_self, map_zero]

omit [CharZero F] in
theorem s61_D_one (i : Fin (2 * n)) : s61_D F n i 1 = 0 := by
  simp only [s61_D, Module.End.mul_apply, s61_dd, contractLeft_one, map_zero]

/-- `K_i(v) = ½(e_i^*(v) ∂_{f_i} - f_i^*(v) ∂_{e_i})`: the commutator of `½ D_i` with `v ∧`. -/
noncomputable def s61_K (i : Fin (2 * n)) (v : V F n) : Module.End F (ExtV F n) :=
  (2 : F)⁻¹ • ((basisV F n).coord (Fin.natAdd (2 * n) i) v • s61_dd F n (Fin.castAdd (2 * n) i) -
    (basisV F n).coord (Fin.castAdd (2 * n) i) v • s61_dd F n (Fin.natAdd (2 * n) i))

omit [CharZero F] in
theorem s61_D_ι_mul (i : Fin (2 * n)) (v : V F n) (x : ExtV F n) :
    (1 + (2 : F)⁻¹ • s61_D F n i) (ExteriorAlgebra.ι F v * x) =
      ExteriorAlgebra.ι F v * (1 + (2 : F)⁻¹ • s61_D F n i) x + s61_K F n i v x := by
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, s61_K,
    LinearMap.sub_apply, s61_D, Module.End.mul_apply, s61_dd_ι_mul, map_sub, map_smul, mul_add,
    mul_smul_comm, smul_sub]
  abel

omit [CharZero F] in
theorem s61_K_D (i : Fin (2 * n)) (v : V F n) (x : ExtV F n) :
    s61_K F n i v ((1 + (2 : F)⁻¹ • s61_D F n i) x) = s61_K F n i v x := by
  simp only [s61_K, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul, s61_D_D_cast, s61_D_D_nat, sub_self, smul_zero,
    add_zero]

omit [CharZero F] in
theorem s61_K_comm (i j : Fin (2 * n)) (v : V F n) (x : ExtV F n) :
    s61_K F n i v ((1 + (2 : F)⁻¹ • s61_D F n j) x) =
      (1 + (2 : F)⁻¹ • s61_D F n j) (s61_K F n i v x) := by
  simp only [s61_K, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul, map_sub, s61_dd_D]
  module

/-- `G_l = ∏_{i ∈ l} (1 + ½ D_i)`. -/
noncomputable def s61_G (l : List (Fin (2 * n))) : Module.End F (ExtV F n) :=
  (l.map fun i => 1 + (2 : F)⁻¹ • s61_D F n i).prod

omit [CharZero F] in
theorem s61_Ksum_comm (l : List (Fin (2 * n))) (i : Fin (2 * n)) (v : V F n) (y : ExtV F n) :
    (1 + (2 : F)⁻¹ • s61_D F n i) ((l.map fun j => s61_K F n j v).sum y) =
      (l.map fun j => s61_K F n j v).sum ((1 + (2 : F)⁻¹ • s61_D F n i) y) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [LinearMap.add_apply (s61_K F n j v), LinearMap.add_apply (s61_K F n j v), map_add, ih,
      s61_K_comm]

omit [CharZero F] in
theorem s61_G_ι_mul (l : List (Fin (2 * n))) (v : V F n) (x : ExtV F n) :
    s61_G F n l (ExteriorAlgebra.ι F v * x) =
      ExteriorAlgebra.ι F v * s61_G F n l x + (l.map fun i => s61_K F n i v).sum (s61_G F n l x) := by
  induction l with
  | nil => simp [s61_G]
  | cons i l ih =>
    simp only [s61_G, List.map_cons, List.prod_cons, List.sum_cons, Module.End.mul_apply] at ih ⊢
    rw [ih, map_add, s61_D_ι_mul, s61_Ksum_comm, LinearMap.add_apply (s61_K F n i v), s61_K_D]
    abel

omit [CharZero F] in
theorem s61_G_one (l : List (Fin (2 * n))) : s61_G F n l 1 = 1 := by
  induction l with
  | nil => simp [s61_G]
  | cons i l ih =>
    simp only [s61_G, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih, LinearMap.add_apply, LinearMap.smul_apply, s61_D_one, smul_zero, add_zero,
      Module.End.one_apply]

omit [CharZero F] in
theorem s61_coord_castAdd (i : Fin (2 * n)) (w : V F n) :
    (basisV F n).coord (Fin.castAdd (2 * n) i) w = w.1 (e F n i) := by
  rw [← s61_B0_e_eq_coord, B0_apply]

omit [CharZero F] in
theorem s61_coord_natAdd (i : Fin (2 * n)) (w : V F n) :
    (basisV F n).coord (Fin.natAdd (2 * n) i) w = w.2 i := by
  have h : (basisV F n).coord (Fin.natAdd (2 * n) i) =
      (LinearMap.proj i : H1 F n →ₗ[F] F) ∘ₗ LinearMap.snd F _ _ := by
    refine (basisV F n).ext fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, LinearMap.comp_apply,
      LinearMap.snd_apply, LinearMap.proj_apply]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · rw [s61_basisV_castAdd, ite_eq_right]
      · rfl
      · exact fun h => absurd (congrArg Fin.val h) (by simp; omega)
    · rw [s61_basisV_natAdd]
      simp only [e, Pi.single_apply, Fin.natAdd_inj]
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl, Ne.symm hl]
  rw [h]; rfl

omit [CharZero F] in
/-- `Σᵢ K_i(v)` is contraction with `B̄₀(v, ·)`. -/
theorem s61_K_sum (v : V F n) :
    ((List.finRange (2 * n)).map fun i => s61_K F n i v).sum =
      contractLeft (Q := (0 : QuadraticForm F (V F n))) (B0bar F n v) := by
  rw [← Fin.sum_univ_def]
  have hfun : B0bar F n v = ∑ i, (2 : F)⁻¹ •
      ((basisV F n).coord (Fin.natAdd (2 * n) i) v • (basisV F n).coord (Fin.castAdd (2 * n) i) -
        (basisV F n).coord (Fin.castAdd (2 * n) i) v • (basisV F n).coord (Fin.natAdd (2 * n) i)) := by
    refine LinearMap.ext fun w => ?_
    rw [B0bar_apply, B0_apply, B0_apply, LinearMap.sum_apply, s61_dual_apply F n w.1,
      s61_dual_apply F n v.1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, s61_coord_castAdd, s61_coord_natAdd,
      smul_eq_mul]
    ring
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [s61_K, map_smul, map_sub, s61_dd]

omit [CharZero F] in
/-- `changeB0bar = ∏ᵢ (1 + ½ D_i)`: both satisfy the recursion of `changeForm`. -/
theorem s61_changeB0bar_eq_G (x : ExtV F n) :
    changeB0bar F n x = s61_G F n (List.finRange (2 * n)) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [changeB0bar, changeForm_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul, s61_G_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x m hx =>
    rw [show (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) m) = ExteriorAlgebra.ι F m from rfl,
      s61_G_ι_mul, s61_K_sum, changeB0bar, changeForm_ι_mul, ← changeB0bar, hx]
    rw [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, sub_neg_eq_add]

theorem s61_PiMap_G (l : List (Fin (2 * n))) (y : ExtV F n) :
    PiMap F n (s61_G F n l y) =
      (l.map fun i => 1 + (2 : F)⁻¹ • s61_a F n i).prod * PiMap F n y := by
  induction l with
  | nil => simp [s61_G]
  | cons i l ih =>
    simp only [s61_G, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul,
      s61_PiMap_D, ih]
    simp only [add_mul, one_mul, smul_mul_assoc, mul_assoc]

theorem s61_exp_list (t : F) (l : List (Fin (2 * n))) :
    IsNilpotent.exp (t • (l.map fun i => s61_a F n i).sum) =
      (l.map fun i => 1 + t • s61_a F n i).prod := by
  have hnil : ∀ l : List (Fin (2 * n)), IsNilpotent (t • (l.map fun i => s61_a F n i).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.sum_cons, smul_add]
      exact Commute.isNilpotent_add ((s61_commute_a F n i _).smul_left _ |>.smul_right _)
        (IsNilpotent.smul ⟨2, by rw [pow_two, s61_a_mul_self]⟩ t) ih
  induction l with
  | nil => simp [IsNilpotent.exp_zero]
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, IsNilpotent.exp_add_of_commute
      ((s61_commute_a F n i _).smul_left _ |>.smul_right _)
      (IsNilpotent.smul ⟨2, by rw [pow_two, s61_a_mul_self]⟩ t) (hnil l), ih,
      IsNilpotent.exp_eq_sum (k := 2) (by rw [pow_two, smul_mul_smul_comm, s61_a_mul_self, smul_zero]),
      List.map_cons, List.prod_cons]
    simp [Finset.sum_range_succ]

end S61Change

end WeilClasses
