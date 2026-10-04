module

public import WeilClasses.Orlov.Defs
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

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

The proofs follow the paper's basis computations. `import all` of
`Mathlib.LinearAlgebra.ExteriorPower.BilinForm` gives access to the determinant formula
`LinearMap.BilinForm.bilinForm_ιMulti_ιMulti` (private in Mathlib), needed to compute `extPairing`
(`s61_extPairing_ιMulti`).
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

section S61Sec63b

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_kk3 (k : ℕ) : k * (k + 3) / 2 = k * (k - 1) / 2 + 2 * k := by
  have h := s61_tri_succ k
  have h2 : k * (k + 3) = (k + 1) * k + 2 * k := by ring
  rw [h2, Nat.add_mul_div_left _ _ two_pos, h]
  omega

end S61Sec63b

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

/-- Lemma 6.3.2 on the basis vectors `f_L ∧ e_K`, `f_{L'} ∧ e_{K'}` (the paper's computation). -/
theorem s61_lemma6_3_2_basis (L K L' K' : Finset (Fin (2 * n))) :
    extPairing F n (PiMap0 F n (pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)))
        (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K')) =
      (-1 : F) ^ ((L.card + K.card) * (L.card + K.card - 1) / 2) *
        integralExt F n ((pullXHat F n (basisSHat F n L) * pullX F n (basisS F n K)) *
          (pullXHat F n (basisSHat F n L') * pullX F n (basisS F n K'))) := by
  rw [s61_PiMap0_beta, map_smul, LinearMap.smul_apply, s61_extPairing_beta,
    s61_integralExt_beta_mul, smul_eq_mul]
  by_cases h : L' = Lᶜ ∧ K' = Kᶜ
  · rw [ite_eq_left h, ite_eq_left h, mul_one]
    have h1 := s61_card_add_card_compl n L
    have h2 := s61_card_add_card_compl n K
    have h3 := s61_tri_add L.card Lᶜ.card
    have h4 := s61_tri_add K.card Kᶜ.card
    have h5 := s61_tri_two_mul n
    have h6 := s61_tri_add L.card K.card
    have h7 := s61_mul_self_mod_two Lᶜ.card
    have h8 := s61_mul_self_mod_two Kᶜ.card
    have hm1 : L.card * Lᶜ.card + Lᶜ.card * Lᶜ.card = 2 * (n * Lᶜ.card) := by
      rw [← add_mul, h1, mul_assoc]
    have hk1 : K.card * Kᶜ.card + Kᶜ.card * Kᶜ.card = 2 * (n * Kᶜ.card) := by
      rw [← add_mul, h2, mul_assoc]
    have hkm : K.card * Lᶜ.card + K.card * L.card = 2 * (n * K.card) := by
      rw [← mul_add, add_comm, h1]; ring
    have hc : L.card * K.card = K.card * L.card := mul_comm _ _
    rw [h1] at h3
    rw [h2] at h4
    simp only [← pow_add]
    exact s61_neg_one_pow_congr (by omega)
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]

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

/-- (§6.3, TeX lines 2705–2716 and footnote) The cohomological action of `Ψ_{𝒫⁻¹[n]}` is
`Ψ_{𝒫⁻¹[n]}(e_K) = σ_K PD(e_K) = σ_K ε_{K,K^c} f_{K^c}`, `σ_K = (-1)^{k(k+3)/2}`. (This, (6.3.1) and
(6.3.2) depend on the sign convention `c₁(𝒫) = +Σ eᵢ ∪ fᵢ`, `WeilClasses.Correspondence.FourierMukai`.)
Proof: computed from the kernel `ch(𝒫⁻¹[n]) = (-1)ⁿ exp(-c₁(𝒫))` of `ψ_{𝒫⁻¹[n]}`
(`s61_psiPinvShift_basisS`); the footnote's appeal to [Huybrechts, Lemma 9.23, Cor. 9.24] (cited
results, `WeilClasses.External.Huybrechts.Sec6_3`) is not needed in the model. -/
theorem psiPinvShift_basis (K : Finset (Fin (2 * n))) :
    psiPinvShift F n (basisS F n K) =
      ((-1 : F) ^ (K.card * (K.card + 3) / 2) * epsSign F n K Kᶜ) • basisSHat F n Kᶜ := by
  rw [s61_psiPinvShift_basisS, s61_epsSign_eq, ite_eq_left disjoint_compl_right]
  congr 1
  have h2 := s61_card_add_card_compl n K
  have h3 := s61_tri_add K.card Kᶜ.card
  have h4 := s61_tri_two_mul n
  have h5 := s61_mul_self_mod_two K.card
  have h6 := s61_kk3 K.card
  have h7 : Kᶜ.card * K.card + K.card * K.card = 2 * (n * K.card) := by
    rw [← add_mul, add_comm, h2, mul_assoc]
  rw [h2] at h3
  simp only [← pow_add]
  exact s61_neg_one_pow_congr (by rw [mul_comm K.card Kᶜ.card] at h3; omega)

/-- (footnote in §6.3) The cohomological action of `Ψ_{𝒫⁻¹}[n]` restricts to `H^k(X)` as
`(-1)^{k+n} φ_𝒫`, where `φ_𝒫 : H*(X) → H*(X̂)`.
Proof: comparison of the two kernels on basis vectors (`s61_psiPinvShift_basisS`,
`s61_phiPX_basisS`) instead of [Huybrechts, Cor. 9.24]. -/
theorem psiPinvShift_eq_phiPX (k : ℕ) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    psiPinvShift F n s = (-1 : F) ^ (k + n) • phiPX F n s := by
  rw [← (basisS F n).sum_repr s]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : K.card = k
  · rw [s61_psiPinvShift_basisS, s61_phiPX_basisS]
    simp only [smul_smul]
    congr 1
    have h2 := s61_card_add_card_compl n K
    have hm : (-1 : F) ^ Kᶜ.card = (-1 : F) ^ (k + n) * (-1 : F) ^ n := by
      rw [← pow_add]; exact s61_neg_one_pow_congr (by omega)
    rw [hm]
    have hn : (-1 : F) ^ n * (-1 : F) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination ((-1 : F) ^ (k + n) * (-1 : F) ^ (Kᶜ.card * (Kᶜ.card - 1) / 2) *
      (-1 : F) ^ s61_inv K Kᶜ * (basisS F n).repr s K) * hn
  · have h0 : (basisS F n).repr s K = 0 := s61_repr_eq_zero_of_mem _ hs hK
    rw [h0]; simp

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
displays. The statement for `ψ_{𝒫⁻¹}` is as printed.) -/
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

end WeilClasses
