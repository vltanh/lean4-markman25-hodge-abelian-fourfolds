module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Orlov.Basis
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.External.Huybrechts.Sec6_3
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# §6.3: Orlov's equivalence induces Chevalley's isomorphism `S ⊗ S ≅ ⋀•V`

Statements of the paper's §6.3 (TeX lines 2660–2855): Lemma 6.3.1 with the displayed equations
(6.3.1), (6.3.2) and the unnumbered formulas of its proof, the proof of Lemma 6.1.1
(`phiOrlov_eq_PiMap_comp_nuOrlov`), Lemma 6.3.2 and Remark 6.3.3.

Notation (proof of Lemma 6.3.1): `e_K = basisS F n K`, `f_K = basisSHat F n K` (increasing wedge
products), `π_X^*`, `π_X̂^*` (`pullX`, `pullXHat`), `ε_{K,L}` (`epsSign`), `Σ(K)` (`sumIdx`, indices
from `1`), `σ_K = (-1)^{k(k+3)/2}` for `k = |K|`, `I' = K \ I`, `I^c` the complement in
`{1, …, 2n}`. `H*(X × X) = S ⊗ S` with `π₁^*e_K ∧ π₂^*e_L = e_K ⊗ e_L`, and
`H*(X̂ × X) = H*(X × X̂) = ⋀•V` (see `WeilClasses.Correspondence.Defs`).

**Correction** (agreed with the project owner; REPORT.md): Lemma 6.3.2 as printed, with the sign
`(-1)^{d(d+1)/2}`, is false in odd degrees `d` for the sign of `c₁(𝒫)` under which Lemma 6.3.1 and
Proposition 6.1.2 hold; `lemma6_3_2` states it with the correct sign `(-1)^{d(d-1)/2}`.

The proofs follow the paper's basis computations. As in the paper, the footnote formulas for
`ψ_{𝒫⁻¹[n]}` (`psiPinvShift_eq_phiPX`, `psiPinvShift_basis`) and the computation of
`φ_𝒫 ⊗ ψ_{𝒫⁻¹}` in the proof of Lemma 6.3.2 (`sd_PiMap0_beta`) use [Huybrechts, Lemma 9.23,
Cor. 9.24] (`WeilClasses.External.Huybrechts.Sec6_3`). `import all` of
`Mathlib.LinearAlgebra.ExteriorPower.BilinForm` gives access to the determinant formula
`LinearMap.BilinForm.bilinForm_ιMulti_ιMulti` (non-exported in Mathlib), needed to compute
`extPairing` (`s61_extPairing_ιMulti`).

The last section holds the algebraic computation of `ρ'_g` from the identity of Lemma 6.1.1
(`sd_rhoPrime_of_lemma6_1_1`, with the `Spin(V)`-equivariance of `Π = ±PD`, `s61_PiMap_rhoExt`),
which proves Proposition 6.1.2 in `WeilClasses.Orlov.Sec6_1` and, upstream of §6.1, the cited
[Orlov, Th. 2.10] (`WeilClasses.External.Orlov.Sec6_1`); this is why this file imports
`WeilClasses.Chevalley.Sec2_3`. Part of the helpers written for this file (prefix `s61_`) are in
`WeilClasses.Orlov.Basis`, where `WeilClasses.Chevalley.Sec2_3` can use them.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P10) -/

section S61Sec63

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_tri_succ' (k : ℕ) : (k + 1) * (k + 2) / 2 = k * (k + 1) / 2 + (k + 1) := by
  have h := s61_tri_succ (k + 1)
  rw [Nat.add_sub_cancel] at h
  rw [show (k + 1) * (k + 2) = (k + 2) * (k + 1) by ring, show k + 2 = k + 1 + 1 by ring, h,
    mul_comm]

theorem s61_inv_compl_add (K : Finset (Fin (2 * n))) :
    s61_inv K Kᶜ + K.card * (K.card + 1) / 2 = sumIdx n K := by
  classical
  induction K using Finset.induction_on_max with
  | empty => simp [s61_inv, sumIdx]
  | insert m K hm ih =>
    have hmK : m ∉ K := fun h => lt_irrefl m (hm m h)
    have h1 : s61_inv K (insert m K)ᶜ = s61_inv K Kᶜ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨_, hy⟩, hyx⟩; exact ⟨hy, hyx⟩
      · rintro ⟨hy, hyx⟩; exact ⟨⟨fun h => lt_asymm (h ▸ hyx) (hm x hx), hy⟩, hyx⟩
    have h2 : ((insert m K)ᶜ.filter (· < m)).card + K.card = (m : ℕ) := by
      have hsub : K ⊆ Finset.Iio m := fun x hx => Finset.mem_Iio.mpr (hm x hx)
      have : (insert m K)ᶜ.filter (· < m) = Finset.Iio m \ K := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_insert, not_or, Finset.mem_sdiff,
          Finset.mem_Iio]
        constructor
        · rintro ⟨⟨_, hy⟩, hym⟩; exact ⟨hym, hy⟩
        · rintro ⟨hym, hy⟩; exact ⟨⟨hym.ne, hy⟩, hym⟩
      rw [this, Finset.card_sdiff_of_subset hsub, Fin.card_Iio]
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      omega
    rw [s61_inv_insert_left hmK, h1, Finset.card_insert_of_notMem hmK, sumIdx, Finset.sum_insert hmK,
      ← sumIdx, ← ih, s61_tri_succ']
    omega

end S61Sec63

section S61Sec63b

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_kk3 (k : ℕ) : k * (k + 3) / 2 = k * (k - 1) / 2 + 2 * k := by
  have h := s61_tri_succ k
  have h2 : k * (k + 3) = (k + 1) * k + 2 * k := by ring
  rw [h2, Nat.add_mul_div_left _ _ two_pos, h]
  omega

end S61Sec63b

section S61Mu

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The map `w ↦ (w, t w)` from `H¹(X)` to `H¹(X × X) = H¹(X) ⊕ H¹(X)`. -/
noncomputable def s61_diag (t : F) : H1 F n →ₗ[F] H1 F n × H1 F n :=
  LinearMap.inl F (H1 F n) (H1 F n) + t • LinearMap.inr F (H1 F n) (H1 F n)

omit [CharZero F] in
theorem s61_basisS_insert_min (a : Fin (2 * n)) (K : Finset (Fin (2 * n)))
    (h : ∀ x ∈ K, a < x) :
    basisS F n (insert a K) = ExteriorAlgebra.ι F (e F n a) * basisS F n K := by
  rw [basisS, s61_basis_insert_min _ a K h, s61_basisFun_apply]

omit [CharZero F] in
/-- `(w ↦ (w, t w))^*` expands `e_K` as `Σ_{I ⊆ K} t^{|K∖I|} ε_{I,K∖I} π₁^*e_I ∧ π₂^*e_{K∖I}`. -/
theorem s61_map_diag_basisS (t : F) (K : Finset (Fin (2 * n))) :
    ExteriorAlgebra.map (s61_diag F n t) (basisS F n K) =
      ∑ I ∈ K.powerset, (t ^ (K \ I).card * (-1 : F) ^ s61_inv I (K \ I)) •
        (pull1 F n (basisS F n I) * pull2 F n (basisS F n (K \ I))) := by
  classical
  induction K using Finset.induction_on_min with
  | empty => simp [basisS, s61_basis_empty, s61_inv]
  | insert a K ha ih =>
    have haK : a ∉ K := fun h => lt_irrefl a (ha a h)
    rw [s61_basisS_insert_min F n a K ha, map_mul, ExteriorAlgebra.map_apply_ι, ih,
      Finset.sum_powerset_insert haK, Finset.mul_sum, add_comm]
    have hι : ExteriorAlgebra.ι F (s61_diag F n t (e F n a)) =
        pull1 F n (ExteriorAlgebra.ι F (e F n a)) + t • pull2 F n (ExteriorAlgebra.ι F (e F n a)) := by
      simp only [s61_diag, pull1, pull2, ExteriorAlgebra.map_apply_ι, LinearMap.add_apply,
        LinearMap.smul_apply, ← map_smul, ← map_add]
    rw [hι]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · -- the terms `insert a I`
      refine Finset.sum_congr rfl fun I hI => ?_
      have hIK : I ⊆ K := Finset.mem_powerset.mp hI
      have haI : a ∉ I := fun h => haK (hIK h)
      have hsd : insert a K \ insert a I = K \ I := by
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem]
        simp [haK]
      have hinv : s61_inv (insert a I) (K \ I) = s61_inv I (K \ I) := by
        rw [s61_inv_insert_left haI]
        simp only [add_eq_right, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx
        exact not_lt.mpr (ha x (Finset.mem_sdiff.mp hx).1).le
      rw [hsd, hinv, s61_basisS_insert_min F n a I (fun x hx => ha x (hIK hx)), map_mul,
        mul_smul_comm, mul_assoc]
    · -- the terms `I ⊆ K`
      refine Finset.sum_congr rfl fun I hI => ?_
      have hIK : I ⊆ K := Finset.mem_powerset.mp hI
      have haI : a ∉ I := fun h => haK (hIK h)
      have hsd : insert a K \ I = insert a (K \ I) := Finset.insert_sdiff_of_notMem _ haI
      have haKI : a ∉ K \ I := fun h => haK (Finset.mem_sdiff.mp h).1
      have hinv : s61_inv I (insert a (K \ I)) = s61_inv I (K \ I) + I.card := by
        rw [s61_inv_insert_right haKI]
        congr 2
        exact Finset.filter_true_of_mem fun x hx => ha x (hIK hx)
      have hcomm : pull2 F n (ExteriorAlgebra.ι F (e F n a)) * pull1 F n (basisS F n I) =
          (-1 : F) ^ I.card • (pull1 F n (basisS F n I) * pull2 F n (ExteriorAlgebra.ι F (e F n a))) := by
        rw [pull2, ExteriorAlgebra.map_apply_ι]
        exact s61_ι_mul_comm_of_mem _ (s61_map_mem _ (s61_basis_mem _ I))
      rw [hsd, hinv, Finset.card_insert_of_notMem haKI,
        s61_basisS_insert_min F n a (K \ I) (fun x hx => ha x (Finset.mem_sdiff.mp hx).1), map_mul,
        mul_smul_comm, smul_mul_assoc, ← mul_assoc, hcomm, smul_mul_assoc, smul_smul, smul_smul,
        mul_assoc, pow_succ, pow_add]
      congr 1
      · ring
      · exact mul_assoc _ _ _

omit [CharZero F] in
theorem s61_kunnethXX_symm_pull (u v : S F n) :
    (kunnethXX F n).symm (pull1 F n u * pull2 F n v) = u ⊗ₜ[F] v := by
  rw [LinearEquiv.symm_apply_eq, kunnethXX_tmul]

omit [CharZero F] in
/-- The common expansion of `μ^*` (`t = 1`) and `(μ^*)⁻¹` (`t = -1`) on `e_K ⊗ e_L`. -/
theorem s61_mu_basis (t : F) (g : H1 F n × H1 F n →ₗ[F] H1 F n × H1 F n)
    (h1 : g ∘ₗ LinearMap.inl F (H1 F n) (H1 F n) = s61_diag F n t)
    (h2 : g ∘ₗ LinearMap.inr F (H1 F n) (H1 F n) = LinearMap.inr F (H1 F n) (H1 F n))
    (K L : Finset (Fin (2 * n))) :
    (kunnethXX F n).symm (ExteriorAlgebra.map g (kunnethXX F n (basisS F n K ⊗ₜ[F] basisS F n L))) =
      ∑ I ∈ K.powerset, (t ^ (K \ I).card * (epsSign F n I (K \ I) * epsSign F n (K \ I) L)) •
        (basisS F n I ⊗ₜ[F] basisS F n ((K \ I) ∪ L)) := by
  have hm1 : ∀ x, ExteriorAlgebra.map g (pull1 F n x) = ExteriorAlgebra.map (s61_diag F n t) x := by
    intro x
    rw [pull1, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h1]
  have hm2 : ∀ x, ExteriorAlgebra.map g (pull2 F n x) = pull2 F n x := by
    intro x
    rw [pull2, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h2]
  rw [kunnethXX_tmul, map_mul, hm1, hm2, s61_map_diag_basisS, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [smul_mul_assoc, mul_assoc, ← map_mul, s61_basisS_mul]
  simp only [map_smul, mul_smul_comm, smul_smul, s61_kunnethXX_symm_pull]
  rw [s61_epsSign_eq F n I, ite_eq_left Finset.disjoint_sdiff]
  ring_nf

omit [CharZero F] in
/-- `(μ^*)⁻¹(e_K ⊗ e_L) = Σ_{I ⊆ K} (-1)^{|I'|} ε_{I,I'} ε_{I',L} e_I ⊗ e_{I' ∪ L}`. -/
theorem s61_muStarInv_basis (K L : Finset (Fin (2 * n))) :
    muStarInv F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, ((-1 : F) ^ (K \ I).card * (epsSign F n I (K \ I) * epsSign F n (K \ I) L)) •
        (basisS F n I ⊗ₜ[F] basisS F n ((K \ I) ∪ L)) :=
  s61_mu_basis F n (-1) (mu1Inv F n) (by ext w <;> simp [mu1Inv, s61_diag])
    (by ext w <;> simp [mu1Inv]) K L

end S61Mu

section S61Nu

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- Reindexing a sum over the subsets of `K` by `I ↦ K ∖ I`. -/
theorem s61_sum_powerset_sdiff {β : Type*} [AddCommMonoid β] (K : Finset (Fin (2 * n)))
    (g : Finset (Fin (2 * n)) → β) :
    ∑ I ∈ K.powerset, g (K \ I) = ∑ J ∈ K.powerset, g J := by
  refine Finset.sum_nbij' (fun I => K \ I) (fun J => K \ J) ?_ ?_ ?_ ?_ ?_
  · intro I _; simp
  · intro J _; simp
  · intro I hI; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hI)
  · intro J hJ; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ)
  · intro I _; rfl

end S61Nu

section S61Phi

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- `τ(e_L) = (-1)^{ℓ(ℓ-1)/2} e_L`. -/
theorem s61_tau_basisS (L : Finset (Fin (2 * n))) :
    tau F n (basisS F n L) = (-1 : F) ^ (L.card * (L.card - 1) / 2) • basisS F n L := by
  classical
  induction L using Finset.induction_on_max with
  | empty => simp [tau, basisS, s61_basis_empty]
  | insert m L hm ih =>
    have hmL : m ∉ L := fun h => lt_irrefl m (hm m h)
    have hins : basisS F n (insert m L) = basisS F n L * ExteriorAlgebra.ι F (e F n m) := by
      rw [basisS, s61_basis_insert_max _ m L hm, s61_basisFun_apply]
    have hmem : basisS F n L ∈ ⋀[F]^L.card (H1 F n) := s61_basis_mem _ L
    rw [hins, tau, CliffordAlgebra.reverse.map_mul, reverse_ι, ← tau, ih, mul_smul_comm,
      show CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) (e F n m) =
        ExteriorAlgebra.ι F (e F n m) from rfl,
      s61_ι_mul_comm_of_mem _ hmem, smul_smul, ← pow_add,
      Finset.card_insert_of_notMem hmL, Nat.add_sub_cancel, s61_tri_succ]

omit [CharZero F] in
/-- `e_a ∧ (f_A ∧ e_B) = ± f_A ∧ e_{B ∪ {a}}`. -/
theorem s61_ι_e_mul_beta (a : Fin (2 * n)) (A B : Finset (Fin (2 * n))) :
    ExteriorAlgebra.ι F ((0, e F n a) : V F n) *
        (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) =
      if a ∈ B then 0 else (-1 : F) ^ (A.card + (B.filter (· < a)).card) •
        (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n (insert a B))) := by
  classical
  rw [s61_beta_eq, s61_beta_eq, ← s61_basisV_natAdd, basisExt, s61_ι_mul_basis]
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
  · rw [ite_eq_right (fun h => haB (hmem.mp h)), ite_eq_right haB]
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
    rw [hfilt, Finset.map_insert, Finset.union_insert]
    rfl

omit [CharZero F] in
/-- `ψ(v x) = L'_v ψ(x) = v ∧ ψ(x) + δ_v ψ(x)`. -/
theorem s61_psi_ι_mul (v : V F n) (x : C F n) :
    psi F n (CliffordAlgebra.ι (Q F n) v * x) =
      ExteriorAlgebra.ι F v * psi F n x + delta F n v (psi F n x) := by
  rw [psi, changeForm_ι_mul, sub_eq_add_neg]
  congr 1
  rw [delta, LinearMap.comp_apply, LinearMap.neg_apply, map_neg, LinearMap.neg_apply, neg_neg]

omit [CharZero F] in
theorem s61_delta_inl (θ : Module.Dual F (H1 F n)) (x : ExtV F n) :
    delta F n ((θ, 0) : V F n) x = 0 := by
  have : B0 F n ((θ, 0) : V F n) = 0 := LinearMap.ext fun v => by rw [B0_apply]; simp
  rw [delta, LinearMap.comp_apply, this, map_zero, LinearMap.zero_apply]

omit [CharZero F] in
theorem s61_iotaX_ι (w : H1 F n) :
    iotaX F n (ExteriorAlgebra.ι F w) = CliffordAlgebra.ι (Q F n) ((0, w) : V F n) :=
  ExteriorAlgebra.lift_ι_apply F _ _ w

omit [CharZero F] in
theorem s61_iotaXHat_ι (θ : Module.Dual F (H1 F n)) :
    iotaXHat F n (ExteriorAlgebra.ι F θ) = CliffordAlgebra.ι (Q F n) ((θ, 0) : V F n) :=
  ExteriorAlgebra.lift_ι_apply F _ _ θ

omit [CharZero F] in
theorem s61_delta_inr_pullX (w : H1 F n) (b : S F n) :
    delta F n ((0, w) : V F n) (pullX F n b) = 0 := by
  induction b using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, delta, LinearMap.comp_apply, contractLeft_algebraMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul x m hx =>
    rw [map_mul, show (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) m) = ExteriorAlgebra.ι F m
      from rfl, pullX, ExteriorAlgebra.map_apply_ι, ← pullX, delta, LinearMap.comp_apply,
      contractLeft_ι_mul, ← LinearMap.comp_apply (CliffordAlgebra.contractLeft) (B0 F n), ← delta, hx,
      mul_zero, sub_zero]
    simp [B0_apply]

omit [CharZero F] in
theorem s61_psi_iotaXHat_mul (a : SHat F n) (y : C F n) :
    psi F n (iotaXHat F n a * y) = pullXHat F n a * psi F n y := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | add x z hx hz => rw [map_add, add_mul, map_add, hx, hz, map_add, add_mul]
  | ι_mul x m hx =>
    rw [map_mul (iotaXHat F n), show (CliffordAlgebra.ι (0 : QuadraticForm F (Module.Dual F (H1 F n))) m) =
      ExteriorAlgebra.ι F m from rfl, s61_iotaXHat_ι]
    rw [mul_assoc, s61_psi_ι_mul, s61_delta_inl, add_zero, hx, map_mul, pullXHat,
      ExteriorAlgebra.map_apply_ι, ← pullXHat, LinearMap.inl_apply, mul_assoc]

omit [CharZero F] in
theorem s61_psi_iotaX (b : S F n) : psi F n (iotaX F n b) = pullX F n b := by
  induction b using CliffordAlgebra.left_induction with
  | algebraMap r => simp [psi, changeForm_algebraMap]
  | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]
  | ι_mul x m hx =>
    rw [map_mul (iotaX F n), show (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) m) =
      ExteriorAlgebra.ι F m from rfl, s61_iotaX_ι]
    rw [s61_psi_ι_mul, hx, s61_delta_inr_pullX, add_zero, map_mul, pullX,
      ExteriorAlgebra.map_apply_ι, ← pullX, LinearMap.inr_apply]

omit [CharZero F] in
theorem s61_varphi_insert_min (a : Fin (2 * n)) (K : Finset (Fin (2 * n))) (h : ∀ x ∈ K, a < x)
    (v : S F n) :
    varphi F n (basisS F n (insert a K) ⊗ₜ[F] v) =
      CliffordAlgebra.ι (Q F n) ((0, e F n a) : V F n) * varphi F n (basisS F n K ⊗ₜ[F] v) := by
  have h1 : ∀ u w : S F n, varphi F n (u ⊗ₜ w) = iotaX F n u * ptHatC F n * iotaX F n (tau F n w) :=
    fun u w => by simp [varphi]
  rw [h1, h1, s61_basisS_insert_min F n a K h, map_mul, s61_iotaX_ι, mul_assoc, mul_assoc,
    mul_assoc]

omit [CharZero F] in
theorem s61_epsSign_insert_left {a : Fin (2 * n)} {X : Finset (Fin (2 * n))} (haX : a ∉ X)
    (Y : Finset (Fin (2 * n))) :
    epsSign F n (insert a X) Y =
      (if a ∈ Y then 0 else (-1 : F) ^ (Y.filter (· < a)).card) * epsSign F n X Y := by
  classical
  rw [s61_epsSign_eq, s61_epsSign_eq, s61_inv_insert_left haX]
  by_cases haY : a ∈ Y
  · rw [ite_eq_left haY, zero_mul, ite_eq_right (fun h => (Finset.disjoint_insert_left.mp h).1 haY)]
  · rw [ite_eq_right haY]
    by_cases hXY : Disjoint X Y
    · rw [ite_eq_left (Finset.disjoint_insert_left.mpr ⟨haY, hXY⟩), ite_eq_left hXY, pow_add]
    · rw [ite_eq_right (fun h => hXY (Finset.disjoint_insert_left.mp h).2), ite_eq_right hXY,
        mul_zero]

omit [CharZero F] in
theorem s61_epsSign_insert_right {a : Fin (2 * n)} {Y : Finset (Fin (2 * n))} (haY : a ∉ Y)
    (X : Finset (Fin (2 * n))) :
    epsSign F n X (insert a Y) =
      (if a ∈ X then 0 else (-1 : F) ^ (X.filter (a < ·)).card) * epsSign F n X Y := by
  classical
  rw [s61_epsSign_eq, s61_epsSign_eq, s61_inv_insert_right haY]
  by_cases haX : a ∈ X
  · rw [ite_eq_left haX, zero_mul,
      ite_eq_right (fun h => (Finset.disjoint_insert_right.mp h).1 haX)]
  · rw [ite_eq_right haX]
    by_cases hXY : Disjoint X Y
    · rw [ite_eq_left (Finset.disjoint_insert_right.mpr ⟨haX, hXY⟩), ite_eq_left hXY, pow_add,
        mul_comm]
    · rw [ite_eq_right (fun h => hXY (Finset.disjoint_insert_right.mp h).2), ite_eq_right hXY,
        mul_zero]

omit [CharZero F] in
theorem s61_epsSign_empty_left (Y : Finset (Fin (2 * n))) : epsSign F n ∅ Y = 1 := by
  rw [s61_epsSign_eq, ite_eq_left (Finset.disjoint_empty_left Y), s61_inv_empty_left, pow_zero]

end S61Phi

section S61Pairing

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_projDegSub_coe (k : ℕ) (x : ExtV F n) :
    (projDegSub F n k x : ExtV F n) =
      (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x k : ExtV F n) := rfl

omit [CharZero F] in
theorem s61_projDegSub_of_mem_same {k : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^k (V F n)) :
    projDegSub F n k x = ⟨x, hx⟩ :=
  Subtype.ext (by rw [s61_projDegSub_coe, DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) hx])

omit [CharZero F] in
theorem s61_projDegSub_of_mem_ne {j k : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^j (V F n)) (h : j ≠ k) :
    projDegSub F n k x = 0 :=
  Subtype.ext (by rw [s61_projDegSub_coe, DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) hx h]; rfl)

omit [CharZero F] in
theorem s61_extPairing_of_mem {d : ℕ} (hd : d ≤ 4 * n) {x y : ExtV F n}
    (hx : x ∈ ⋀[F]^d (V F n)) (hy : y ∈ ⋀[F]^d (V F n)) :
    extPairing F n x y = (pairing F n).exteriorPower d ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [extPairing, LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_eq_single d]
  · rw [LinearMap.compl₁₂_apply, s61_projDegSub_of_mem_same F n hx,
      s61_projDegSub_of_mem_same F n hy]
  · intro k _ hk
    rw [LinearMap.compl₁₂_apply, s61_projDegSub_of_mem_ne F n hx (Ne.symm hk), map_zero,
      LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

omit [CharZero F] in
theorem s61_extPairing_of_mem_ne {d d' : ℕ} (h : d ≠ d') {x y : ExtV F n}
    (hx : x ∈ ⋀[F]^d (V F n)) (hy : y ∈ ⋀[F]^d' (V F n)) : extPairing F n x y = 0 := by
  rw [extPairing, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.compl₁₂_apply]
  by_cases hk : k = d
  · subst hk
    rw [s61_projDegSub_of_mem_ne F n hy (Ne.symm h), map_zero]
  · rw [s61_projDegSub_of_mem_ne F n hx (Ne.symm hk), map_zero, LinearMap.zero_apply]

omit [CharZero F] in
theorem s61_extPairing_ιMulti {d : ℕ} (hd : d ≤ 4 * n) (v w : Fin d → V F n) :
    extPairing F n (ExteriorAlgebra.ιMulti F d v) (ExteriorAlgebra.ιMulti F d w) =
      (Matrix.of fun i j => pairing F n (v j) (w i)).det := by
  rw [s61_extPairing_of_mem F n hd (ExteriorAlgebra.ιMulti_range F d ⟨v, rfl⟩)
    (ExteriorAlgebra.ιMulti_range F d ⟨w, rfl⟩)]
  exact LinearMap.BilinForm.bilinForm_ιMulti_ιMulti (pairing F n) d v w

omit [CharZero F] in
theorem s61_pairing_apply (v w : V F n) : pairing F n v w = v.1 w.2 + w.1 v.2 := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q,
    QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

omit [CharZero F] in
theorem s61_pairing_basisV (p q : Fin (2 * n + 2 * n)) :
    pairing F n (basisV F n p) (basisV F n q) = if q = finAddFlip p then 1 else 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q <;>
    simp only [s61_basisV_castAdd, s61_basisV_natAdd, finAddFlip_apply_castAdd,
      finAddFlip_apply_natAdd, s61_pairing_apply, map_zero, LinearMap.zero_apply, zero_add, add_zero]
  · rw [ite_eq_right (fun h => absurd (congrArg Fin.val h) (by simp; omega))]
  · simp only [f, e, LinearMap.proj_apply, Pi.single_apply, Fin.natAdd_inj, eq_comm]
  · simp only [f, e, LinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj]
  · rw [ite_eq_right (fun h => absurd (congrArg Fin.val h) (by simp; omega))]

omit [CharZero F] in
/-- The basis vector `basisExt M` as a product of basis vectors of `V` in increasing order. -/
theorem s61_basisExt_eq_ιMulti (M : Finset (Fin (2 * n + 2 * n))) :
    basisExt F n M = ExteriorAlgebra.ιMulti F M.card (fun i => basisV F n (M.orderEmbOfFin rfl i)) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

omit [CharZero F] in
/-- `basisExt M` pairs to zero with `basisExt N` unless `N` is the flip of `M` (the pairing pairs
`H¹(X)` with `H¹(X̂)`). -/
theorem s61_extPairing_basisExt_eq_zero (M N : Finset (Fin (2 * n + 2 * n)))
    (h : N ≠ M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding) :
    extPairing F n (basisExt F n M) (basisExt F n N) = 0 := by
  classical
  by_cases hc : M.card = N.card
  · have hd : M.card ≤ 4 * n := by
      have := M.card_le_univ; rw [Fintype.card_fin] at this; omega
    have hN : basisExt F n N =
        ExteriorAlgebra.ιMulti F M.card (fun i => basisV F n (N.orderEmbOfFin hc.symm i)) := by
      rw [basisExt, ExteriorAlgebra.basis_apply_ofCard _ hc.symm, ExteriorAlgebra.ιMulti_family,
        Set.powersetCard.ofFinEmbEquiv_symm_apply]
      rfl
    rw [s61_basisExt_eq_ιMulti, hN, s61_extPairing_ιMulti F n hd]
    obtain ⟨m, hm, hmN⟩ : ∃ m ∈ M, finAddFlip m ∉ N := by
      by_contra hcon
      push Not at hcon
      apply h
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact hcon y hy
      · rw [Finset.card_map, hc]
    obtain ⟨j, hj⟩ : ∃ j, M.orderEmbOfFin rfl j = m := by
      have := Finset.range_orderEmbOfFin M rfl
      have hm' : m ∈ Set.range (M.orderEmbOfFin rfl) := by rw [this]; exact hm
      exact hm'
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    rw [Matrix.of_apply, s61_pairing_basisV, hj, ite_eq_right]
    intro h'
    exact hmN (h' ▸ Finset.orderEmbOfFin_mem N hc.symm i)
  · exact s61_extPairing_of_mem_ne F n hc (s61_basis_mem _ M) (s61_basis_mem _ N)

omit [CharZero F] in
theorem s61_pullX_basisS_eq_ιMulti (B : Finset (Fin (2 * n))) :
    pullX F n (basisS F n B) =
      ExteriorAlgebra.ιMulti F B.card (fun i => ((0, e F n (B.orderEmbOfFin rfl i)) : V F n)) := by
  rw [basisS, ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, pullX, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  ext i : 1
  simp only [Function.comp_apply, LinearMap.inr_apply, s61_basisFun_apply]
  rfl

omit [CharZero F] in
theorem s61_pullXHat_basisSHat_eq_ιMulti (A : Finset (Fin (2 * n))) :
    pullXHat F n (basisSHat F n A) =
      ExteriorAlgebra.ιMulti F A.card (fun i => ((f F n (A.orderEmbOfFin rfl i), 0) : V F n)) := by
  rw [basisSHat, ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, pullXHat, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  ext i : 1
  simp only [Function.comp_apply, LinearMap.inl_apply, s61_dualBasis_apply]
  rfl

omit [CharZero F] in
theorem s61_f_e (a b : Fin (2 * n)) : f F n a (e F n b) = if a = b then 1 else 0 := by
  simp only [f, e, LinearMap.proj_apply, Pi.single_apply]

omit [CharZero F] in
/-- `(e_B ∧ f_A, f_B ∧ e_A) = 1`: the Gram matrix is the identity. -/
theorem s61_extPairing_identity (A B : Finset (Fin (2 * n))) :
    extPairing F n (pullX F n (basisS F n B) * pullXHat F n (basisSHat F n A))
      (pullXHat F n (basisSHat F n B) * pullX F n (basisS F n A)) = 1 := by
  have hA := A.card_le_univ
  have hB := B.card_le_univ
  rw [Fintype.card_fin] at hA hB
  rw [s61_pullX_basisS_eq_ιMulti, s61_pullXHat_basisSHat_eq_ιMulti,
    s61_pullX_basisS_eq_ιMulti, s61_pullXHat_basisSHat_eq_ιMulti,
    ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti,
    s61_extPairing_ιMulti F n (by omega)]
  convert Matrix.det_one (n := Fin (B.card + A.card)) (R := F)
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp only [Matrix.of_apply, Fin.append_left, Fin.append_right, s61_pairing_apply,
      map_zero, LinearMap.zero_apply, zero_add, add_zero, Matrix.one_apply]
  · rw [s61_f_e]
    by_cases h : i₁ = j₁
    · subst h; simp
    · simp [h]
  · rw [ite_eq_right (fun h => absurd (congrArg Fin.val h) (by simp; omega))]
  · rw [ite_eq_right (fun h => absurd (congrArg Fin.val h) (by simp; omega))]
  · rw [s61_f_e]
    by_cases h : i₂ = j₂
    · subst h; simp
    · simp [h, Ne.symm h]

omit [CharZero F] in
theorem s61_cast_nat_union_inj {L K L' K' : Finset (Fin (2 * n))}
    (h : L.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪ K.map (Fin.natAddOrderEmb (2 * n)).toEmbedding =
      L'.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        K'.map (Fin.natAddOrderEmb (2 * n)).toEmbedding) : L = L' ∧ K = K' := by
  have hc : ∀ (x : Fin (2 * n)) (A B : Finset (Fin (2 * n))),
      Fin.castAdd (2 * n) x ∈ A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding ↔ x ∈ A := by
    intro x A B
    simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply, Fin.castAdd_inj, exists_eq_right]
    constructor
    · rintro (h | ⟨j, _, hj⟩)
      · exact h
      · exact absurd hj (s61_castAdd_lt_natAdd n x j).ne'
    · exact Or.inl
  have hn : ∀ (x : Fin (2 * n)) (A B : Finset (Fin (2 * n))),
      Fin.natAdd (2 * n) x ∈ A.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        B.map (Fin.natAddOrderEmb (2 * n)).toEmbedding ↔ x ∈ B := by
    intro x A B
    simp only [Finset.mem_union, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      Fin.castAddOrderEmb_apply, Fin.natAddOrderEmb_apply, Fin.natAdd_inj, exists_eq_right]
    constructor
    · rintro (⟨j, _, hj⟩ | h)
      · exact absurd hj (s61_castAdd_lt_natAdd n j x).ne
      · exact h
    · exact Or.inr
  constructor
  · ext x; rw [← hc x L K, h, hc]
  · ext x; rw [← hn x L K, h, hn]

omit [CharZero F] in
/-- The pairing of the basis vectors `e_B ∧ f_A` and `f_{B'} ∧ e_{A'}` of `⋀•V`. -/
theorem s61_extPairing_beta (A B A' B' : Finset (Fin (2 * n))) :
    extPairing F n (pullX F n (basisS F n B) * pullXHat F n (basisSHat F n A))
      (pullXHat F n (basisSHat F n B') * pullX F n (basisS F n A')) =
      if B' = B ∧ A' = A then 1 else 0 := by
  classical
  by_cases h : B' = B ∧ A' = A
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_eq_left ⟨rfl, rfl⟩, s61_extPairing_identity]
  · rw [ite_eq_right h]
    have hcomm : pullX F n (basisS F n B) * pullXHat F n (basisSHat F n A) =
        (-1 : F) ^ (B.card * A.card) • (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) :=
      s61_mul_comm_of_mem (s61_map_mem _ (s61_basis_mem _ B)) (s61_map_mem _ (s61_basis_mem _ A))
    rw [hcomm, map_smul, LinearMap.smul_apply, s61_beta_eq, s61_beta_eq,
      s61_extPairing_basisExt_eq_zero, smul_zero]
    rw [Finset.map_union, Finset.map_map, Finset.map_map]
    intro h'
    have hflip1 : (Fin.castAddOrderEmb (2 * n)).toEmbedding.trans
        (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding =
        (Fin.natAddOrderEmb (2 * n)).toEmbedding :=
      Function.Embedding.ext fun x => finAddFlip_apply_castAdd x (2 * n)
    have hflip2 : (Fin.natAddOrderEmb (2 * n)).toEmbedding.trans
        (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding =
        (Fin.castAddOrderEmb (2 * n)).toEmbedding :=
      Function.Embedding.ext fun x => finAddFlip_apply_natAdd x (2 * n)
    rw [hflip1, hflip2, Finset.union_comm (A.map _)] at h'
    exact h (s61_cast_nat_union_inj n h')

omit [CharZero F] in
theorem s61_univ_eq_cast_nat :
    (Finset.univ : Finset (Fin (2 * n + 2 * n))) =
      (Finset.univ : Finset (Fin (2 * n))).map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        (Finset.univ : Finset (Fin (2 * n))).map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, true_and, true_iff]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

omit [CharZero F] in
theorem s61_integralExt_beta (A B : Finset (Fin (2 * n))) :
    integralExt F n (pullXHat F n (basisSHat F n A) * pullX F n (basisS F n B)) =
      if A = Finset.univ ∧ B = Finset.univ then 1 else 0 := by
  rw [s61_beta_eq, integralExt, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases h : A = Finset.univ ∧ B = Finset.univ
  · rw [ite_eq_left h, ite_eq_left]
    rw [h.1, h.2, ← s61_univ_eq_cast_nat]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    rw [s61_univ_eq_cast_nat] at h'
    exact h (s61_cast_nat_union_inj n h')

omit [CharZero F] in
theorem s61_eq_compl_iff (L L' : Finset (Fin (2 * n))) :
    L' = Lᶜ ↔ Disjoint L L' ∧ L ∪ L' = Finset.univ := by
  constructor
  · rintro rfl; exact ⟨disjoint_compl_right, Finset.union_compl L⟩
  · rintro ⟨hd, hu⟩
    ext x
    simp only [Finset.mem_compl]
    constructor
    · exact fun hx hL => Finset.disjoint_left.mp hd hL hx
    · intro hx
      have : x ∈ L ∪ L' := hu ▸ Finset.mem_univ x
      exact (Finset.mem_union.mp this).resolve_left hx

omit [CharZero F] in
/-- `∫_{X̂ × X} (f_L ∧ e_K) ∧ (f_{L'} ∧ e_{K'})`. -/
theorem s61_integralExt_beta_mul (L K L' K' : Finset (Fin (2 * n))) :
    integralExt F n ((pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) *
        (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K'))) =
      if L' = Lᶜ ∧ K' = Kᶜ then
        (-1 : F) ^ (K.card * Lᶜ.card) * (-1 : F) ^ s61_inv L Lᶜ * (-1 : F) ^ s61_inv K Kᶜ
      else 0 := by
  classical
  have hcomm : pullX F n (basisS F n K) * pullXHat F n (basisSHat F n L') =
      (-1 : F) ^ (K.card * L'.card) •
        (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K)) :=
    s61_mul_comm_of_mem (s61_map_mem _ (s61_basis_mem _ K)) (s61_map_mem _ (s61_basis_mem _ L'))
  have hrw : (pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) *
        (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K')) =
      (-1 : F) ^ (K.card * L'.card) • (pullXHat F n (basisSHat F n L * basisSHat F n L') *
        pullX F n (basisS F n K * basisS F n K')) := by
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (pullX F n _), hcomm, smul_mul_assoc,
      mul_smul_comm, mul_assoc, mul_assoc]
  rw [hrw, basisSHat, basisS, s61_basis_mul_basis, s61_basis_mul_basis, ← basisSHat, ← basisS]
  by_cases hL : Disjoint L L'
  · by_cases hK : Disjoint K K'
    · rw [ite_eq_left hL, ite_eq_left hK]
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_eq_mul]
      rw [s61_integralExt_beta]
      by_cases h : L' = Lᶜ ∧ K' = Kᶜ
      · obtain ⟨rfl, rfl⟩ := h
        rw [ite_eq_left ⟨Finset.union_compl L, Finset.union_compl K⟩, ite_eq_left ⟨rfl, rfl⟩]
        ring
      · rw [ite_eq_right h, ite_eq_right, mul_zero]
        rintro ⟨hu1, hu2⟩
        exact h ⟨(s61_eq_compl_iff n L L').mpr ⟨hL, hu1⟩, (s61_eq_compl_iff n K K').mpr ⟨hK, hu2⟩⟩
    · rw [ite_eq_right hK, map_zero, mul_zero, smul_zero, map_zero, ite_eq_right]
      exact fun h => hK ((s61_eq_compl_iff n K K').mp h.2).1
  · rw [ite_eq_right hL, map_zero, zero_mul, smul_zero, map_zero, ite_eq_right]
    exact fun h => hL ((s61_eq_compl_iff n L L').mp h.1).1

end S61Pairing

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## Combinatorics of the proof of Lemma 6.3.1 -/

/-- (§6.3, TeX line 2693) `ε_{K,K^c} = (-1)^{Σ(K) - k(k+1)/2}` (`Σ(K) ≥ k(k+1)/2`, so the natural
subtraction is the integer one). -/
theorem epsSign_compl (K : Finset (Fin (2 * n))) :
    epsSign F n K Kᶜ = (-1 : F) ^ (sumIdx n K - K.card * (K.card + 1) / 2) := by
  rw [s61_epsSign_eq, ite_eq_left disjoint_compl_right, ← s61_inv_compl_add n K, Nat.add_sub_cancel]

/-- (§6.3, TeX line 2694) `ε_{K^c,K} = (-1)^k ε_{K,K^c} = (-1)^{Σ(K) - k(k-1)/2}`. -/
theorem epsSign_compl_swap (K : Finset (Fin (2 * n))) :
    epsSign F n Kᶜ K = (-1 : F) ^ K.card * epsSign F n K Kᶜ ∧
      epsSign F n Kᶜ K = (-1 : F) ^ (sumIdx n K - K.card * (K.card - 1) / 2) := by
  have h1 := s61_inv_add_inv (disjoint_compl_left : Disjoint Kᶜ K)
  have h2 := s61_card_add_card_compl n K
  have h3 : Kᶜ.card * K.card + K.card * K.card = 2 * (n * K.card) := by
    rw [← add_mul, add_comm, h2, mul_assoc]
  have h4 := s61_mul_self_mod_two K.card
  have h5 := s61_inv_compl_add n K
  have h6 := s61_tri_succ K.card
  rw [mul_comm (K.card + 1)] at h6
  rw [s61_epsSign_eq, s61_epsSign_eq, ite_eq_left disjoint_compl_left,
    ite_eq_left disjoint_compl_right, ← pow_add]
  constructor
  · exact s61_neg_one_pow_congr (by omega)
  · exact s61_neg_one_pow_congr (by omega)

/-- (§6.3, TeX line 2695) Poincaré duality `PD_X` sends `e_K` to `∫_X e_K ∧ (•) = ε_{K,K^c}
f_{K^c}`:
`PD_X(s)` pairs with `t` to `∫_X s ∧ t` (under `H^k(X̂) = H^k(X)*`, `⟨f_A, e_B⟩ = δ_{AB}`). -/
theorem PDX_spec (s t : S F n) : pairSHatS F n (PDX F n s) t = integral F n (s * t) := by
  have h : (pairSHatS F n).comp (PDX F n) = (LinearMap.mul F (S F n)).compr₂ (integral F n) := by
    refine LinearMap.ext_basis (basisS F n) (basisS F n) fun K L => ?_
    rw [LinearMap.comp_apply, PDX, Module.Basis.constr_basis, map_smul, pairSHatS,
      Module.Basis.constr_basis, LinearMap.compr₂_apply, LinearMap.mul_apply', integral, basisS,
      s61_coord_univ_basis_mul, ← basisS, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, s61_epsSign_eq, ite_eq_left disjoint_compl_right]
    by_cases h : L = Kᶜ
    · rw [ite_eq_left h, ite_eq_left h, smul_eq_mul, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, smul_zero]
  exact congrArg (fun B : S F n →ₗ[F] S F n →ₗ[F] F => B s t) h

/-- (§6.3, TeX lines 2697–2703) `μ^*(π₁^*e_K ∧ π₂^*e_L) = Σ_{I ⊆ K} ε_{I,I'} ε_{I',L} π₁^*e_I ∧
π₂^*(e_{I' ∪ L})`, `I' = K \ I`. -/
theorem muStar_basis (K L : Finset (Fin (2 * n))) :
    muStar F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n I (K \ I) * epsSign F n (K \ I) L) •
        (basisS F n I ⊗ₜ[F] basisS F n ((K \ I) ∪ L)) := by
  have h := s61_mu_basis F n 1 (mu1 F n) (by ext w <;> simp [mu1, s61_diag])
    (by ext w <;> simp [mu1]) K L
  simp only [one_pow, one_mul] at h
  exact h

/-- `ψ_{𝒫⁻¹[n]}(e_K)` lies in `H^{2n-k}(X̂)`, `k = |K|` (footnote in §6.3): by
[Huybrechts, Lemma 9.23] for `X̂ → X` (`huybrechts_lemma9_23_Xhat`),
`φ_𝒫(f_{K^c}) = ± ε_{K,K^c} e_K`, and `ψ_{𝒫⁻¹[n]}` is the inverse of `φ_𝒫`
(`psiPinvShift_comp_phiP`), so
`ψ_{𝒫⁻¹[n]}(e_K) = ± f_{K^c}`. -/
theorem sd_psiPinvShift_basisS_mem (K : Finset (Fin (2 * n))) :
    psiPinvShift F n (basisS F n K) ∈ ⋀[F]^Kᶜ.card (Module.Dual F (H1 F n)) := by
  have hmem : basisSHat F n Kᶜ ∈ ⋀[F]^Kᶜ.card (Module.Dual F (H1 F n)) := s61_basis_mem _ Kᶜ
  have h := huybrechts_lemma9_23_Xhat F n Kᶜ.card hmem
  rw [sd_PDXinv_basisSHat, compl_compl, smul_smul, s61_epsSign_eq,
    ite_eq_left disjoint_compl_right, ← pow_add] at h
  have hsq : ((-1 : F) ^ (Kᶜ.card * (Kᶜ.card + 1) / 2 + n + s61_inv K Kᶜ)) *
      (-1 : F) ^ (Kᶜ.card * (Kᶜ.card + 1) / 2 + n + s61_inv K Kᶜ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have he : basisS F n K = (-1 : F) ^ (Kᶜ.card * (Kᶜ.card + 1) / 2 + n + s61_inv K Kᶜ) •
      phiP F n (basisSHat F n Kᶜ) := by
    rw [h, smul_smul, hsq, one_smul]
  rw [he, map_smul, ← LinearMap.comp_apply (psiPinvShift F n) (phiP F n), psiPinvShift_comp_phiP,
    LinearMap.id_apply]
  exact Submodule.smul_mem _ _ hmem

/-- (footnote in §6.3) The cohomological action of `Ψ_{𝒫⁻¹}[n]` restricts to `H^k(X)` as
`(-1)^{k+n} φ_𝒫`, where `φ_𝒫 : H*(X) → H*(X̂)`.
Proof (the footnote's): `Ψ_{𝒫⁻¹}[n]` is the inverse of `Φ_𝒫` (`phiP_comp_psiPinvShift`), and
`ψ_{𝒫⁻¹[n]}(e_K)` has degree `2n - k` (`sd_psiPinvShift_basisS_mem`, by [Huybrechts, Lemma 9.23]);
by [Huybrechts, Cor. 9.24] (`huybrechts_cor9_24`) the composition
`H^{2n-k}(X̂) → H^k(X) → H^{2n-k}(X̂)` of the two `φ_𝒫` is `(-1)^{2n-k+n} = (-1)^{k+n}`, so
`φ_𝒫(e_K) = φ_𝒫(φ_𝒫(ψ_{𝒫⁻¹[n]}(e_K))) = (-1)^{k+n} ψ_{𝒫⁻¹[n]}(e_K)`. -/
theorem psiPinvShift_eq_phiPX (k : ℕ) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    psiPinvShift F n s = (-1 : F) ^ (k + n) • phiPX F n s := by
  rw [← (basisS F n).sum_repr s]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : K.card = k
  · subst hK
    have h := huybrechts_cor9_24 F n Kᶜ.card (sd_psiPinvShift_basisS_mem F n K)
    rw [← LinearMap.comp_apply (phiP F n) (psiPinvShift F n), phiP_comp_psiPinvShift,
      LinearMap.id_apply] at h
    have h2 := s61_card_add_card_compl n K
    have hsgn : (-1 : F) ^ (K.card + n) * (-1 : F) ^ (Kᶜ.card + n) = 1 := by
      rw [← pow_add, s61_neg_one_pow_congr (b := 0) (by omega), pow_zero]
    rw [h, smul_smul, smul_smul]
    congr 1
    linear_combination (-(basisS F n).repr s K) * hsgn
  · have h0 : (basisS F n).repr s K = 0 := s61_repr_eq_zero_of_mem _ hs hK
    rw [h0, zero_smul, zero_smul, smul_zero]

/-- (§6.3, TeX lines 2705–2716 and footnote) The cohomological action of `Ψ_{𝒫⁻¹[n]}` is
`Ψ_{𝒫⁻¹[n]}(e_K) = σ_K PD(e_K) = σ_K ε_{K,K^c} f_{K^c}`, `σ_K = (-1)^{k(k+3)/2}`. (This, (6.3.1) and
(6.3.2) depend on the sign convention `c₁(𝒫) = +Σ eᵢ ∪ fᵢ`,
`WeilClasses.Correspondence.FourierMukai`.)
Proof (the footnote's): on `H^k(X)`, `ψ_{𝒫⁻¹[n]} = (-1)^{k+n} φ_𝒫` (`psiPinvShift_eq_phiPX`) and
`φ_𝒫 = (-1)^{k(k+1)/2+n} PD_k` by [Huybrechts, Lemma 9.23] (`huybrechts_lemma9_23_X`), so
`ψ_{𝒫⁻¹[n]} = (-1)^{k(k+3)/2} PD_k`, with `PD_X(e_K) = ε_{K,K^c} f_{K^c}`. -/
theorem psiPinvShift_basis (K : Finset (Fin (2 * n))) :
    psiPinvShift F n (basisS F n K) =
      ((-1 : F) ^ (K.card * (K.card + 3) / 2) * epsSign F n K Kᶜ) • basisSHat F n Kᶜ := by
  have hK : basisS F n K ∈ ⋀[F]^K.card (H1 F n) := s61_basis_mem _ K
  have h1 := s61_kk3 K.card
  have h2 := s61_tri_succ K.card
  rw [mul_comm (K.card + 1) K.card] at h2
  have hsgn : (-1 : F) ^ (K.card + n) * (-1 : F) ^ (K.card * (K.card + 1) / 2 + n) =
      (-1 : F) ^ (K.card * (K.card + 3) / 2) := by
    rw [← pow_add]; exact s61_neg_one_pow_congr (by omega)
  rw [psiPinvShift_eq_phiPX F n K.card hK, huybrechts_lemma9_23_X F n K.card hK, sd_PDX_basisS,
    smul_smul, smul_smul, hsgn]

/-- `σ_J ε_{J,J^c} = (-1)^{Σ(J) - |J|}`. -/
theorem s61_sigma_eps (J : Finset (Fin (2 * n))) :
    (-1 : F) ^ (J.card * (J.card + 3) / 2) * epsSign F n J Jᶜ =
      (-1 : F) ^ (sumIdx n J - J.card) := by
  rw [epsSign_compl, ← pow_add]
  have h1 := s61_inv_compl_add n J
  have h2 := s61_kk3 J.card
  have h3 := s61_tri_succ J.card
  rw [mul_comm (J.card + 1)] at h3
  exact s61_neg_one_pow_congr (by omega)

/-- **(6.3.1)** (`eq-phi-of-e-K-e-L`), both lines:
`ν(π₁^*e_K ∧ π₂^*e_L) = Σ_{I ⊆ K} ε_{I',I} ε_{I,L} σ_{I'} ε_{I',(I')^c} π_X̂^*f_{(I')^c} ∧
π_X^*(e_{I∪L})
= Σ_{I ⊆ K} ε_{I',I} ε_{I,L} (-1)^{Σ(I') - |I'|} π_X̂^*f_{(I')^c} ∧ π_X^*(e_{I∪L})`, `I' = K \ I`.
(Checked numerically for `n = 1, 2`.) -/
theorem equation6_3_1 (K L : Finset (Fin (2 * n))) :
    nuOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
        ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * epsSign F n I L *
              (-1 : F) ^ ((K \ I).card * ((K \ I).card + 3) / 2) *
              epsSign F n (K \ I) (K \ I)ᶜ) •
            (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) ∧
      nuOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
        ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * epsSign F n I L *
              (-1 : F) ^ (sumIdx n (K \ I) - (K \ I).card)) •
            (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) := by
  have h : nuOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ J ∈ K.powerset, (epsSign F n J (K \ J) * epsSign F n (K \ J) L *
          ((-1 : F) ^ (J.card * (J.card + 3) / 2) * epsSign F n J Jᶜ)) •
        (pullXHat F n (basisSHat F n Jᶜ) * pullX F n (basisS F n ((K \ J) ∪ L))) := by
    rw [nuOrlov, LinearMap.comp_apply, LinearMap.comp_apply, muStar_basis, map_sum, map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis,
      ← TensorProduct.smul_tmul', map_smul, LinearEquiv.coe_coe, kunnethHatX_tmul, smul_smul]
  constructor
  · rw [h, ← s61_sum_powerset_sdiff n K]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hI)]
    congr 1
    ring
  · rw [h, ← s61_sum_powerset_sdiff n K]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hI), s61_sigma_eps]

/-- (§6.3, TeX line 2785) `δ_K(f₁ ∧ ⋯ ∧ f_{2n}) = (-1)^{Σ(K) - |K|} f_{K^c}`, where
`δ_K = δ_{e_{i₁}} ⋯ δ_{e_{i_k}}` (`i₁ < ⋯ < i_k`) and `δ_{e_i}` is contraction with
`B₀(e_i, ·) = (e_i, ·)_V`. -/
theorem delta_prod_ptHat (K : Finset (Fin (2 * n))) :
    (List.map (fun i => delta F n (0, e F n i)) K.sort).prod (pullXHat F n (ptHat F n)) =
      (-1 : F) ^ (sumIdx n K - K.card) • pullXHat F n (basisSHat F n Kᶜ) := by
  classical
  induction K using Finset.induction_on_min with
  | empty => simp [ptHat, sumIdx]
  | insert a K ha ih =>
    have haK : a ∉ K := fun h => lt_irrefl a (ha a h)
    rw [Finset.sort_insert _ (fun x hx => (ha x hx).le) haK, List.map_cons, List.prod_cons,
      Module.End.mul_apply, ih, map_smul, s61_pullXHat_basisSHat, s61_delta_e_basisExt]
    have hmem : Fin.castAdd (2 * n) a ∈ Kᶜ.map (Fin.castAddOrderEmb (2 * n)).toEmbedding :=
      Finset.mem_map_of_mem _ (Finset.mem_compl.mpr haK)
    have hfilt : (Kᶜ.map (Fin.castAddOrderEmb (2 * n)).toEmbedding).filter
        (· < Fin.castAdd (2 * n) a) = (Finset.Iio a).map (Fin.castAddOrderEmb (2 * n)).toEmbedding := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_compl, Finset.mem_Iio]
      constructor
      · rintro ⟨⟨y, _, rfl⟩, hy⟩
        exact ⟨y, (Fin.castAddOrderEmb (2 * n)).lt_iff_lt.mp hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, fun h => lt_asymm hy (ha y h), rfl⟩,
          (Fin.castAddOrderEmb (2 * n)).lt_iff_lt.mpr hy⟩
    have herase : (Kᶜ.map (Fin.castAddOrderEmb (2 * n)).toEmbedding).erase (Fin.castAdd (2 * n) a) =
        (insert a K)ᶜ.map (Fin.castAddOrderEmb (2 * n)).toEmbedding := by
      rw [Finset.compl_insert, Finset.map_erase]
      rfl
    rw [ite_eq_left hmem, hfilt, herase, Finset.card_map, Fin.card_Iio, smul_smul, ← pow_add,
      ← s61_pullXHat_basisSHat, s61_sumIdx_insert n haK, Finset.card_insert_of_notMem haK]
    have := s61_card_le_sumIdx n K
    congr 2
    omega

/-- (§6.3, TeX lines 2767–2786) `φ̃(e_K ⊗ e_L) = Σ_{I ⊆ K} ε_{I',I} (-1)^{ℓ(ℓ-1)/2}
(-1)^{Σ(I') - |I'|} ε_{I,L} f_{(I')^c} ∧ e_{I∪L}`, `ℓ = |L|`, `I' = K \ I`. -/
theorem varphiTilde_basis (K L : Finset (Fin (2 * n))) :
    varphiTilde F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * (-1 : F) ^ (L.card * (L.card - 1) / 2) *
            (-1 : F) ^ (sumIdx n (K \ I) - (K \ I).card) * epsSign F n I L) •
          (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) := by
  classical
  rw [varphiTilde, LinearMap.comp_apply]
  induction K using Finset.induction_on_min with
  | empty =>
    have h1 : varphi F n (basisS F n ∅ ⊗ₜ[F] basisS F n L) =
        iotaXHat F n (ptHat F n) * iotaX F n (tau F n (basisS F n L)) := by
      simp [varphi, basisS, s61_basis_empty, ptHatC]
    rw [h1, s61_psi_iotaXHat_mul, s61_psi_iotaX, s61_tau_basisS, map_smul, mul_smul_comm]
    simp [s61_epsSign_empty_left, sumIdx, ptHat]
  | insert a K ha ih =>
    have haK : a ∉ K := fun h => lt_irrefl a (ha a h)
    rw [s61_varphi_insert_min F n a K ha, s61_psi_ι_mul, ih, Finset.mul_sum, map_sum,
      Finset.sum_powerset_insert haK, add_comm]
    congr 1
    · -- the contraction terms: `J = I ⊆ K`
      refine Finset.sum_congr rfl fun I hI => ?_
      have hIK : I ⊆ K := Finset.mem_powerset.mp hI
      have haI : a ∉ I := fun h => haK (hIK h)
      have hKI : insert a K \ I = insert a (K \ I) := Finset.insert_sdiff_of_notMem _ haI
      have haKI : a ∉ K \ I := fun h => haK (Finset.mem_sdiff.mp h).1
      have hfilt : ((K \ I)ᶜ.filter (· < a)).card = (a : ℕ) := by
        have : (K \ I)ᶜ.filter (· < a) = Finset.Iio a := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_Iio, Finset.mem_sdiff, not_and,
            not_not]
          constructor
          · exact fun h => h.2
          · intro hy
            exact ⟨fun hyK => absurd hy (not_lt.mpr (ha y hyK).le), hy⟩
        rw [this, Fin.card_Iio]
      have herase : (K \ I)ᶜ.erase a = (insert a (K \ I))ᶜ := Finset.compl_insert.symm
      have hIa : I.filter (· < a) = ∅ :=
        Finset.filter_false_of_mem fun x hx => not_lt.mpr (ha x (hIK hx)).le
      rw [map_smul, s61_delta_e_beta, ite_eq_left (Finset.mem_compl.mpr haKI), smul_smul, hKI,
        hfilt, herase, s61_epsSign_insert_left F n haKI, ite_eq_right haI, hIa, Finset.card_empty,
        pow_zero, one_mul, s61_sumIdx_insert n haKI, Finset.card_insert_of_notMem haKI]
      have hle := s61_card_le_sumIdx n (K \ I)
      have hexp : (a : ℕ) + 1 + sumIdx n (K \ I) - ((K \ I).card + 1) =
          (sumIdx n (K \ I) - (K \ I).card) + a := by omega
      rw [hexp, pow_add]
      congr 1
      ring
    · -- the creation terms: `J = insert a I`
      refine Finset.sum_congr rfl fun I hI => ?_
      have hIK : I ⊆ K := Finset.mem_powerset.mp hI
      have haI : a ∉ I := fun h => haK (hIK h)
      have haKI : a ∉ K \ I := fun h => haK (Finset.mem_sdiff.mp h).1
      have hKI : insert a K \ insert a I = K \ I := by
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem haK]
      have hIL : insert a I ∪ L = insert a (I ∪ L) := Finset.insert_union _ _ _
      rw [mul_smul_comm, s61_ι_e_mul_beta, hKI, hIL, s61_epsSign_insert_left F n haI L,
        s61_epsSign_insert_right F n haI (K \ I), ite_eq_right haKI]
      by_cases haL : a ∈ L
      · rw [ite_eq_left (Finset.mem_union_right _ haL), smul_zero, ite_eq_left haL, zero_mul,
          mul_zero, zero_smul]
      · have haIL : a ∉ I ∪ L := by simp [haI, haL]
        have hIa : I.filter (· < a) = ∅ :=
          Finset.filter_false_of_mem fun x hx => not_lt.mpr (ha x (hIK hx)).le
        have hKa : (K \ I).filter (a < ·) = K \ I :=
          Finset.filter_true_of_mem fun x hx => ha x (Finset.mem_sdiff.mp hx).1
        have hc := s61_card_add_card_compl n (K \ I)
        have hpow : (-1 : F) ^ (K \ I)ᶜ.card = (-1 : F) ^ (K \ I).card :=
          s61_neg_one_pow_congr (by omega)
        rw [ite_eq_right haIL, ite_eq_right haL, smul_smul, Finset.filter_union, hIa,
          Finset.empty_union, hKa, pow_add, hpow]
        congr 1
        ring

/-- **(6.3.2)** (`eq-orlov-isomorphism-categorifies-chevalley`)
`ν(π₁^*(e_K) ∧ π₂^*τ(e_L)) = φ̃(e_K ⊗ e_L)`. -/
theorem equation6_3_2 (K L : Finset (Fin (2 * n))) :
    nuOrlov F n (basisS F n K ⊗ₜ[F] tau F n (basisS F n L)) =
      varphiTilde F n (basisS F n K ⊗ₜ[F] basisS F n L) := by
  rw [s61_tau_basisS, TensorProduct.tmul_smul, map_smul, (equation6_3_1 F n K L).2,
    varphiTilde_basis, Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [smul_smul]
  congr 1
  ring

/-- **Lemma 6.3.1** (`lemma-nu-equal-tilde-varphi`). `ν ∘ (id ⊗ τ) = φ̃`, where
`ν : H*(X × X) → H*(X̂ × X)` is induced by `(Ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^*` and `φ̃` is (2.3.2).
(Checked numerically for `n = 1, 2`; this fixes the sign of `c₁(𝒫)`, see `c1P`.) -/
theorem lemma6_3_1 : nuOrlov F n ∘ₗ tauTensor F n = varphiTilde F n := by
  refine TensorProduct.ext (LinearMap.ext_basis (basisS F n) (basisS F n) fun K L => ?_)
  exact equation6_3_2 F n K L

/-- (Proof of Lemma 6.1.1, §6.3, TeX line 2799) `φ = (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^* =
(φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ ν` (because `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`). -/
theorem phiOrlov_eq_PiMap_comp_nuOrlov : phiOrlov F n = PiMap F n ∘ₗ nuOrlov F n := by
  have h : TensorProduct.map (phiP F n) (psiPinvShift F n) ∘ₗ
      TensorProduct.map (psiPinvShift F n) (LinearMap.id : S F n →ₗ[F] S F n) =
      TensorProduct.map LinearMap.id (psiPinvShift F n) := by
    rw [← TensorProduct.map_comp, phiP_comp_psiPinvShift, LinearMap.comp_id]
  refine LinearMap.ext fun x => ?_
  simp only [phiOrlov, PiMap, nuOrlov, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map (phiP F n) (psiPinvShift F n)), h]

/-- `ψ_{𝒫⁻¹} = (-1)ⁿ ψ_{𝒫⁻¹[n]}` (the shift `[n]` multiplies the Chern character by `(-1)ⁿ`). -/
theorem sd_psiPinv_eq_smul : psiPinv F n = (-1 : F) ^ n • psiPinvShift F n := by
  rw [s61_psiPinvShift_eq_smul, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_smul]

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹}` on the basis vector `f_L ∧ e_K`, by the route of the proof of Lemma 6.3.2:
`φ_𝒫(f_L) = (-1)^{ℓ(ℓ+1)/2+n} PD_ℓ(f_L) = (-1)^{ℓ(ℓ+1)/2+n} ε_{L^c,L} e_{L^c}`
([Huybrechts, Lemma 9.23], `huybrechts_lemma9_23_Xhat`, with `PD_ℓ` the inverse of `PD_X`) and
`ψ_{𝒫⁻¹}(e_K) = (-1)ⁿ ψ_{𝒫⁻¹[n]}(e_K) = (-1)ⁿ σ_K ε_{K,K^c} f_{K^c}` (the footnote formula,
`psiPinvShift_basis`). -/
theorem sd_PiMap0_beta (L K : Finset (Fin (2 * n))) :
    PiMap0 F n (pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) =
      (((-1 : F) ^ (L.card * (L.card + 1) / 2 + n) * epsSign F n Lᶜ L) *
        ((-1 : F) ^ n * ((-1 : F) ^ (K.card * (K.card + 3) / 2) * epsSign F n K Kᶜ))) •
        (pullX F n (basisS F n Lᶜ) * pullXHat F n (basisSHat F n Kᶜ)) := by
  have hL : basisSHat F n L ∈ ⋀[F]^L.card (Module.Dual F (H1 F n)) := s61_basis_mem _ L
  rw [PiMap0, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    ← kunnethHatX_tmul, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    huybrechts_lemma9_23_Xhat F n L.card hL, sd_PDXinv_basisSHat, sd_psiPinv_eq_smul,
    LinearMap.smul_apply, psiPinvShift_basis, smul_smul, smul_smul, TensorProduct.smul_tmul_smul,
    map_smul, kunnethXHat_tmul]

/-- Lemma 6.3.2 on the basis vectors `f_L ∧ e_K`, `f_{L'} ∧ e_{K'}` (the paper's computation, with
`φ_𝒫(f_L)` from [Huybrechts, Lemma 9.23] and `ψ_{𝒫⁻¹}(e_K)` from the footnote formula,
`sd_PiMap0_beta`; with `PD_ℓ = PD_X⁻¹` the signs give `(-1)^{d(d-1)/2}`, `d = ℓ + k`). -/
theorem s61_lemma6_3_2_basis (L K L' K' : Finset (Fin (2 * n))) :
    extPairing F n (PiMap0 F n (pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)))
        (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K')) =
      (-1 : F) ^ ((L.card + K.card) * (L.card + K.card - 1) / 2) *
        integralExt F n ((pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) *
          (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K'))) := by
  rw [sd_PiMap0_beta, map_smul, LinearMap.smul_apply, s61_extPairing_beta,
    s61_integralExt_beta_mul, smul_eq_mul, s61_epsSign_eq, ite_eq_left disjoint_compl_left,
    s61_epsSign_eq, ite_eq_left disjoint_compl_right]
  by_cases h : L' = Lᶜ ∧ K' = Kᶜ
  · rw [ite_eq_left h, ite_eq_left h, mul_one]
    have h1 := s61_card_add_card_compl n L
    have hinv := s61_inv_add_inv (disjoint_compl_right : Disjoint L Lᶜ)
    have h6 := s61_tri_add L.card K.card
    have h7 := s61_tri_succ L.card
    rw [mul_comm (L.card + 1) L.card] at h7
    have h8 := s61_kk3 K.card
    have h9 := s61_mul_self_mod_two L.card
    have hkm : K.card * Lᶜ.card + K.card * L.card = 2 * (n * K.card) := by
      rw [← mul_add, add_comm, h1]; ring
    have hlm : L.card * Lᶜ.card + L.card * L.card = 2 * (n * L.card) := by
      rw [← mul_add, add_comm, h1]; ring
    have hc : L.card * K.card = K.card * L.card := mul_comm _ _
    simp only [← pow_add]
    exact s61_neg_one_pow_congr (by omega)
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]

/-! ## Lemma 6.3.2 and Remark 6.3.3 -/

/-- **Lemma 6.3.2** (`lemma-phi-P-psi-P-inverse-is-PD-up-to-sign`):
`φ_𝒫 ⊗ ψ_{𝒫⁻¹} : H^d(X̂ × X) → H^{4n-d}(X × X̂)` equals `(-1)^{d(d-1)/2} PD_{X̂ × X}`, where
`(PD_{X̂×X}(α), •) = ∫_{X̂ × X} α ∧ •`, the pairing `( , )` of `H*(X × X̂)` with `H*(X̂ × X)` being
the one induced by `(·,·)_V` (`extPairing`).

Correction of the paper (REPORT.md): the paper prints the sign `(-1)^{d(d+1)/2}`, which differs from
the correct one in every odd degree. With `c₁(𝒫) = Σ eᵢ ∧ fᵢ`, the sign for which Lemma 6.3.1 and
Proposition 6.1.2 hold, `φ_𝒫(f_L) = (-1)^{n + ℓ(ℓ+1)/2 + ℓ} ε_{L,L^c} e_{L^c}`, while the proof uses
the footnote's `(-1)^{ℓ(ℓ+1)/2 + n} ε_{L,L^c} e_{L^c}`; they differ by `(-1)^ℓ`. Counterexample to the
printed sign: `n = 1`, `α = f₁`, `β = f₂ ∧ e₁ ∧ e₂`: the left side is `1`, the printed right side
`-1`. The paper only uses that the map reverses degrees (Proposition 6.4.1), which is unaffected.

Reading: `ψ_{𝒫⁻¹}` without shift, as printed. (The paper's proof says `φ_𝒫⁻¹ = ψ_{𝒫⁻¹}`, while
`φ_𝒫⁻¹ = ψ_{𝒫⁻¹[n]} = (-1)ⁿ ψ_{𝒫⁻¹}`; a factor `(-1)ⁿ` is lost between its first and second
displays. The statement for `ψ_{𝒫⁻¹}` is as printed.)

Proof: the paper's computation on the basis vectors `f_L ∧ e_K` (`s61_lemma6_3_2_basis`), with
`φ_𝒫(f_L) = (-1)^{ℓ(ℓ+1)/2+n} PD_ℓ(f_L)` by [Huybrechts, Lemma 9.23] (`huybrechts_lemma9_23_Xhat`,
`PD_ℓ` read as the inverse of `PD_X`, `PD_ℓ(f_L) = ε_{L^c,L} e_{L^c}`) and
`ψ_{𝒫⁻¹} = (-1)ⁿ ψ_{𝒫⁻¹[n]}` given by the footnote formula (`psiPinvShift_basis`)
(`sd_PiMap0_beta`); these two readings correct the two slips above. -/
theorem lemma6_3_2 (d : ℕ) {α : ExtV F n} (hα : α ∈ ⋀[F]^d (V F n)) (β : ExtV F n) :
    extPairing F n (PiMap0 F n α) β = (-1 : F) ^ (d * (d - 1) / 2) * integralExt F n (α * β) := by
  have hB : ∀ M : Finset (Fin (2 * n + 2 * n)), M.card = d → ∀ β : ExtV F n,
      extPairing F n (PiMap0 F n (basisExt F n M)) β =
        (-1 : F) ^ (d * (d - 1) / 2) * integralExt F n (basisExt F n M * β) := by
    intro M hM β
    obtain ⟨L, K, hLK, hMLK⟩ := s61_basisExt_eq_beta F n M
    have h : extPairing F n (PiMap0 F n (basisExt F n M)) =
        (-1 : F) ^ (d * (d - 1) / 2) • ((integralExt F n) ∘ₗ LinearMap.mulLeft F (basisExt F n M)) := by
      refine (basisExt F n).ext fun N => ?_
      obtain ⟨L', K', -, hN⟩ := s61_basisExt_eq_beta F n N
      rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul, hMLK, hN,
        s61_lemma6_3_2_basis, hLK, hM]
    rw [h, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]
  rw [← (basisExt F n).sum_repr α]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_mul,
    smul_mul_assoc, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  by_cases hM : M.card = d
  · rw [hB M hM β]; ring
  · have h0 : (basisExt F n).repr α M = 0 := s61_repr_eq_zero_of_mem _ hα hM
    rw [h0]; ring

/-- **Remark 6.3.3** (no label). Let `ς : X × X̂ → X̂ × X` be the transposition. The isomorphism
`ς_* : V = H¹(X × X̂) → H¹(X̂ × X) = V*` is the one induced by `(·,·)_V` (in the model both
`H*(X × X̂)` and `H*(X̂ × X)` are `⋀•V`, `ς_*` is the identity and `V*` is identified with `V` by
`(·,·)_V`, as in `extPairing`). Hence `(φ_𝒫 ⊗ ψ_{𝒫⁻¹}) ∘ ς_* : ⋀•V → ⋀•V` is an analogue of the
Hodge `*` operator [Huybrechts, Complex geometry, Sec. 1.2].

Reading: "analogue of the Hodge `*` operator" is formalized as: on each `⋀^d V` it is, up to a sign
`±1`, the Hodge star of the pairing `(·,·)_V` and the volume form `∫_{X̂ × X}`, i.e. it satisfies
`(⋆α, β) = ∫ α ∧ β` up to sign (cf. Mathlib's `exteriorPower.hodgeStar`). -/
theorem remark6_3_3 (d : ℕ) :
    ∃ s : F, (s = 1 ∨ s = -1) ∧ ∀ α ∈ ⋀[F]^d (V F n), ∀ β : ExtV F n,
      extPairing F n (PiMap0 F n α) β = s * integralExt F n (α * β) :=
  ⟨(-1 : F) ^ (d * (d - 1) / 2), neg_one_pow_eq_or F _, fun _ hα β => lemma6_3_2 F n d hα β⟩

end Field

/-! ## The algebraic computation of `ρ'_g` (Proposition 6.1.2 and [Orlov, Th. 2.10])

Helpers (prover P10, moved here from `WeilClasses.Orlov.Sec6_1` by prover SD): `⋀ρ_g` preserves the
pairing `( , )` and `∫_{X̂ × X}` (`ρ_g ∈ SO(V)`), so `Π = ±PD` (Lemma 6.3.2) commutes with `⋀ρ_g`
(`s61_PiMap_rhoExt`); and the computation `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g` from the
identity of Lemma 6.1.1 (`sd_rhoPrime_of_lemma6_1_1`). -/

section S61Equivariance

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_pairing_rho (g : Spin F n) (u v : V F n) :
    pairing F n (rho F n g u) (rho F n g v) = pairing F n u v := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, rho, ← map_add,
    spinVectorAction_map_app]

theorem s61_det_rho (g : Spin F n) : LinearMap.det (rho F n g : V F n →ₗ[F] V F n) = 1 := by
  have h := (CliffordAlgebra.spinToSpecialOrthogonal (Q F n) g).2
  rw [TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff] at h
  have heq : ((CliffordAlgebra.spinToSpecialOrthogonal (Q F n) g :
      TauCeti.QuadraticMap.specialOrthogonalGroup (Q F n)) : V F n ≃ₗ[F] V F n) = rho F n g :=
    LinearEquiv.ext fun m => CliffordAlgebra.coe_spinToSpecialOrthogonal_apply (Q F n) g m
  rw [heq] at h
  rw [← LinearEquiv.coe_det, h.2, Units.val_one]

omit [CharZero F] in
theorem s61_basisExt_eq_ιMulti' (N : Finset (Fin (2 * n + 2 * n))) {d : ℕ} (h : N.card = d) :
    basisExt F n N = ExteriorAlgebra.ιMulti F d (fun i => basisV F n (N.orderEmbOfFin h i)) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard _ h, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

/-- `⋀ρ_g` is an isometry of the pairing `( , )` on `⋀•V` induced by `(·,·)_V`. -/
theorem s61_extPairing_rhoExt (g : Spin F n) (x y : ExtV F n) :
    extPairing F n (rhoExt F n g x) (rhoExt F n g y) = extPairing F n x y := by
  have h : (extPairing F n).compl₁₂ (rhoExt F n g).toLinearMap (rhoExt F n g).toLinearMap =
      extPairing F n := by
    refine LinearMap.ext_basis (basisExt F n) (basisExt F n) fun M N => ?_
    rw [LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    by_cases hc : M.card = N.card
    · have hd : M.card ≤ 4 * n := by
        have := M.card_le_univ; rw [Fintype.card_fin] at this; omega
      rw [s61_basisExt_eq_ιMulti' F n M rfl, s61_basisExt_eq_ιMulti' F n N hc.symm, rhoExt,
        ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
        s61_extPairing_ιMulti F n hd, s61_extPairing_ιMulti F n hd]
      congr 1
      ext i j
      simp only [Matrix.of_apply, Function.comp_apply, LinearEquiv.coe_coe, s61_pairing_rho]
    · have hmM : basisExt F n M ∈ ⋀[F]^M.card (V F n) := s61_basis_mem _ M
      have hmN : basisExt F n N ∈ ⋀[F]^N.card (V F n) := s61_basis_mem _ N
      rw [s61_extPairing_of_mem_ne F n hc (s61_rhoExt_mem F n g hmM) (s61_rhoExt_mem F n g hmN),
        s61_extPairing_of_mem_ne F n hc hmM hmN]
  exact congrArg (fun B : ExtV F n →ₗ[F] ExtV F n →ₗ[F] F => B x y) h

/-- `ρ_g ∈ SO(V)` acts trivially on the top degree: `∫_{X̂ × X} ρ_g(x) = ∫_{X̂ × X} x`. -/
theorem s61_integralExt_rhoExt (g : Spin F n) (x : ExtV F n) :
    integralExt F n (rhoExt F n g x) = integralExt F n x := by
  classical
  have hN : (Finset.univ : Finset (Fin (2 * n + 2 * n))).card = 2 * n + 2 * n := by simp
  have htop : rhoExt F n g (basisExt F n Finset.univ) = basisExt F n Finset.univ := by
    have hid : (fun i => basisV F n ((Finset.univ : Finset (Fin (2 * n + 2 * n))).orderEmbOfFin hN i)) =
        basisV F n := by
      have := Finset.orderEmbOfFin_unique hN (f := id) (fun x => Finset.mem_univ x) strictMono_id
      funext i
      rw [← this]; rfl
    rw [s61_basisExt_eq_ιMulti' F n Finset.univ hN, hid, rhoExt, ExteriorAlgebra.map_apply_ιMulti]
    have h1 := exteriorPower.ιMulti_eq_basis_det_smul (basisV F n)
      ((rho F n g : V F n →ₗ[F] V F n) ∘ basisV F n)
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one, s61_det_rho, one_smul] at h1
    exact congrArg Subtype.val h1
  have h : (integralExt F n) ∘ₗ (rhoExt F n g).toLinearMap = integralExt F n := by
    refine (basisExt F n).ext fun M => ?_
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    by_cases hM : M = Finset.univ
    · rw [hM, htop]
    · have hc : M.card ≠ (Finset.univ : Finset (Fin (2 * n + 2 * n))).card :=
        fun h => hM (Finset.eq_univ_of_card M (by rw [h, Finset.card_univ]))
      have hmM : basisExt F n M ∈ ⋀[F]^M.card (V F n) := s61_basis_mem _ M
      have h0 : (basisExt F n).repr (rhoExt F n g (basisExt F n M)) Finset.univ = 0 :=
        s61_repr_eq_zero_of_mem _ (s61_rhoExt_mem F n g hmM) (Ne.symm hc)
      rw [integralExt, Module.Basis.coord_apply, Module.Basis.coord_apply, h0,
        Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hM]
  exact congrArg (fun φ : ExtV F n →ₗ[F] F => φ x) h

omit [CharZero F] in
theorem s61_flip_flip (M : Finset (Fin (2 * n + 2 * n))) :
    (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding).map
      (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding = M := by
  rw [Finset.map_map]
  convert Finset.map_refl
  ext x : 1
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · show finAddFlip (finAddFlip (Fin.castAdd (2 * n) i)) = Fin.castAdd (2 * n) i
    rw [finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
  · show finAddFlip (finAddFlip (Fin.natAdd (2 * n) i)) = Fin.natAdd (2 * n) i
    rw [finAddFlip_apply_natAdd, finAddFlip_apply_castAdd]

omit [CharZero F] in
theorem s61_extPairing_basisExt_flip_ne_zero (M : Finset (Fin (2 * n + 2 * n))) :
    extPairing F n (basisExt F n M)
      (basisExt F n (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding)) ≠ 0 := by
  obtain ⟨L, K, -, hM⟩ := s61_basisExt_eq_beta F n M
  have hMeq : M = L.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
      K.map (Fin.natAddOrderEmb (2 * n)).toEmbedding :=
    (basisExt F n).injective (hM.trans (s61_beta_eq F n L K))
  have hflip : M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding =
      K.map (Fin.castAddOrderEmb (2 * n)).toEmbedding ∪
        L.map (Fin.natAddOrderEmb (2 * n)).toEmbedding := by
    rw [hMeq, Finset.map_union, Finset.map_map, Finset.map_map, Finset.union_comm]
    congr 1
    · congr 1
      exact Function.Embedding.ext fun x => finAddFlip_apply_natAdd x (2 * n)
    · congr 1
      exact Function.Embedding.ext fun x => finAddFlip_apply_castAdd x (2 * n)
  rw [hflip, ← s61_beta_eq, hM]
  have hcomm : pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K) =
      (-1 : F) ^ (L.card * K.card) • (pullX F n (basisS F n K) * pullXHat F n (basisSHat F n L)) :=
    s61_mul_comm_of_mem (s61_map_mem _ (s61_basis_mem _ L)) (s61_map_mem _ (s61_basis_mem _ K))
  rw [hcomm, map_smul, LinearMap.smul_apply, s61_extPairing_identity, smul_eq_mul, mul_one]
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

omit [CharZero F] in
/-- The pairing `( , )` on `⋀•V` is nondegenerate. -/
theorem s61_extPairing_nondeg {z : ExtV F n} (h : ∀ y, extPairing F n z y = 0) : z = 0 := by
  classical
  refine (basisExt F n).ext_elem fun M => ?_
  have h1 := h (basisExt F n
    (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding))
  rw [← (basisExt F n).sum_repr z, map_sum, LinearMap.sum_apply, Finset.sum_eq_single M] at h1
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [map_zero, Finsupp.zero_apply]
    exact (mul_eq_zero.mp h1).resolve_right (s61_extPairing_basisExt_flip_ne_zero F n M)
  · intro N _ hN
    rw [map_smul, LinearMap.smul_apply, s61_extPairing_basisExt_eq_zero, smul_zero]
    intro h'
    apply hN
    have := congrArg (fun P : Finset (Fin (2 * n + 2 * n)) =>
      P.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding) h'
    simp only [s61_flip_flip] at this
    exact this.symm
  · intro h'; exact absurd (Finset.mem_univ M) h'

theorem s61_rhoExt_rhoExt_inv (g : Spin F n) (y : ExtV F n) :
    rhoExt F n g (rhoExt F n g⁻¹ y) = y := by
  have h : (rho F n g : V F n →ₗ[F] V F n) ∘ₗ (rho F n g⁻¹ : V F n →ₗ[F] V F n) = LinearMap.id := by
    have := spinVectorAction_mul (Q F n) g g⁻¹
    rw [mul_inv_cancel, spinVectorAction_one] at this
    refine LinearMap.ext fun v => ?_
    have h2 := congrArg (fun φ : V F n ≃ₗ[F] V F n => φ v) this
    simpa [rho] using h2.symm
  rw [rhoExt, rhoExt, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id,
    AlgHom.id_apply]

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD` is `Spin(V)`-equivariant (Poincaré duality commutes with `SO(V)`). -/
theorem s61_PiMap_rhoExt (g : Spin F n) (x : ExtV F n) :
    PiMap F n (rhoExt F n g x) = rhoExt F n g (PiMap F n x) := by
  have h : (PiMap F n) ∘ₗ (rhoExt F n g).toLinearMap = (rhoExt F n g).toLinearMap ∘ₗ PiMap F n := by
    refine (basisExt F n).ext fun M => ?_
    have hM : basisExt F n M ∈ ⋀[F]^M.card (V F n) := s61_basis_mem _ M
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, ← sub_eq_zero]
    apply s61_extPairing_nondeg
    intro y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    conv_rhs => rw [← s61_rhoExt_rhoExt_inv F n g y, s61_extPairing_rhoExt]
    rw [s61_PiMap_eq_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, lemma6_3_2 F n _ (s61_rhoExt_mem F n g hM),
      lemma6_3_2 F n _ hM, ← s61_integralExt_rhoExt F n g (basisExt F n M * rhoExt F n g⁻¹ y),
      map_mul (rhoExt F n g), s61_rhoExt_rhoExt_inv]
  exact congrArg (fun φ : ExtV F n →ₗ[F] ExtV F n => φ x) h

/-- **The algebraic computation of `ρ'_g`** (the proof of Proposition 6.1.2, by the authorized
algebraic argument; see the docstring of `proposition6_1_2`), from the identity of Lemma 6.1.1
`φ = Π ∘ φ̃ ∘ (id ⊗ τ)`, taken as the hypothesis `h`: `φ' = φ ∘ (id ⊗ τ) = Π ∘ E_{B̄₀} ∘ φ̃_sym`
(Lemma 6.1.1, Remark 2.3.1); `φ̃_sym` is `Spin(V)`-equivariant (Trautman),
`Π E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` (`PiMap_changeB0bar`, the operator form of Remark 2.3.1) and
`Π = ±PD` commutes with `⋀ρ_g` (Lemma 6.3.2, `ρ_g ∈ SO(V)`; `s61_PiMap_rhoExt`).
It is stated here, upstream of §6.1, with Lemma 6.1.1 as a hypothesis, so that both
Proposition 6.1.2 (`WeilClasses.Orlov.Sec6_1`, with `lemma6_1_1`) and the cited
[Orlov, Th. 2.10] (`WeilClasses.External.Orlov.Sec6_1`, which §6.1 cites for (6.1.8)) can use it. -/
theorem sd_rhoPrime_of_lemma6_1_1
    (h : phiOrlov F n = PiMap F n ∘ₗ varphiTilde F n ∘ₗ tauTensor F n) (g : Spin F n)
    (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x := by
  have hφ' : ∀ y, phiPrime F n y = PiMap F n (changeB0bar F n (varphiTildeSym F n y)) := by
    intro y
    rw [phiPrime, LinearMap.comp_apply, h, LinearMap.comp_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (tauTensor F n) (tauTensor F n), tauTensor_comp_tauTensor,
      LinearMap.id_apply, varphiTilde, LinearMap.comp_apply, psi_eq_changeB0bar_comp_psiSym,
      LinearMap.comp_apply, varphiTildeSym, LinearMap.comp_apply]
  have hc : ∀ t : F, IsNilpotent (t • c1P F n) := s61_isNilpotent_smul_c1P F n
  set y := phiPrimeInv F n x with hy
  have hx : phiPrime F n y = x := by
    rw [hy, ← LinearMap.comp_apply, phiPrime_comp_phiPrimeInv, LinearMap.id_apply]
  have hw : PiMap F n (varphiTildeSym F n y) =
      IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x := by
    have hcomm1 : Commute (-((2 : F)⁻¹ • c1P F n)) ((2 : F)⁻¹ • c1P F n) :=
      ((s61_commute_c1P F n _).smul_left _).neg_left
    rw [← hx, hφ', PiMap_changeB0bar, ← mul_assoc,
      ← IsNilpotent.exp_add_of_commute hcomm1 (hc _).neg (hc _), neg_add_cancel,
      IsNilpotent.exp_zero, one_mul]
  have hρc : IsNilpotent (rhoExt F n g ((2 : F)⁻¹ • c1P F n)) := (hc _).map _
  calc rhoPrime F n g x
      = PiMap F n (changeB0bar F n (varphiTildeSym F n
          (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y))) := by
        rw [rhoPrime, LinearMap.comp_apply, LinearMap.comp_apply, hφ']
    _ = PiMap F n (changeB0bar F n (rhoExt F n g (varphiTildeSym F n y))) := by
        rw [remark2_3_1_sym_equivariant]
    _ = IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) * rhoExt F n g (PiMap F n (varphiTildeSym F n y)) := by
        rw [PiMap_changeB0bar, s61_PiMap_rhoExt]
    _ = IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) *
          (IsNilpotent.exp (-(rhoExt F n g ((2 : F)⁻¹ • c1P F n))) * rhoExt F n g x) := by
        rw [hw, map_mul, IsNilpotent.map_exp (hc _).neg, map_neg]
    _ = IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x := by
        rw [← mul_assoc, ← IsNilpotent.exp_add_of_commute ?_ (hc _) hρc.neg, map_smul, smul_sub,
          sub_eq_add_neg]
        exact ((s61_commute_c1P F n _).smul_left _)

end S61Equivariance

end WeilClasses
