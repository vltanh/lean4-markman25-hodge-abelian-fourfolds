module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Orlov.Basis
public import WeilClasses.Spinor.Integral
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.Orlov.Sec6_3
public import WeilClasses.External.Orlov.Sec6_1
public import WeilClasses.External.Huybrechts.Sec6_1

/-!
# §6.1: `Spin(V)`-equivariance properties of Orlov's equivalence

Statements of the paper's §6.1 (TeX lines 2139–2348), in the model where Orlov's cohomological
isomorphism `φ` (6.1.3) is the composite `(id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*` (`phiOrlov`, see
`WeilClasses.Orlov.Defs`):

* `φ` is an isomorphism (`phiOrlov_bijective`), integrally (`phiOrlov_image_SZZ`); (6.1.4) as
  printed (`rhoPrime_eq_phiOrlov_conj`);
* Lemma 6.1.1 (`lemma6_1_1`);
* `ρ'_g` preserves the decreasing filtration (6.1.5) with associated graded action `ρ`
  (`rhoPrime_mem_extFiltGE`, `rhoPrime_projDeg`; [GLO, Prop. 4.3.7, Cor. 4.3.8]);
* (6.1.8) (`equation6_1_8`, `equation6_1_8_integral`; [Orlov, Th. 2.10]) and the cocycle identity
  (6.1.9) (`equation6_1_9`; [Huybrechts, Ex. 9.41]);
* Proposition 6.1.2 = (6.1.10) (`proposition6_1_2`) and the integrality of
  `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` (`c1P_pairing_mod_two`, `half_c1P_sub_rho_mem_ExtZ`).

**Reading (coefficients).** The paper states Proposition 6.1.2, (6.1.8) and (6.1.9) for `g` in the
integral group `Spin(V)`, but applies them to `K`-points (Lemma 6.2.6 uses `Spin(V_K)_{ℓ₁,ℓ₂}`);
the identities are algebraic, and we state them for `g : Spin F n` over every field `F` of
characteristic `0`, the integrality claims separately for the integral group `SpinZ n`.

**Left out (sheaf-theoretic).** The derived equivalences (6.1.1), (6.1.2) themselves, the
intertwining of the actions of `Aut(Dᵇ(X))` ([Huybrechts, Cor. 9.37]), the identification of `φ`
with the Chern character of Orlov's kernel (GRR), the existence of the line bundles `N_g` (only
their classes `c₁(N_g) ∈ H²(X × X̂)` appear), the identity `φ_{𝒢^∨[n]} = τ φ_𝒢 τ`, the group
cohomology interpretation of (6.1.9), and the reduction of Proposition 6.1.2 to abelian surfaces
(its proof; replaced by an algebraic proof, see `notes/design.md`).

**Proofs.** Lemma 6.1.1 is the paper's (Lemma 6.3.1 and `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`). Proposition 6.1.2
is proved by the authorized algebraic argument (`s61_proposition6_1_2`, see the docstring of
`proposition6_1_2`): the computation `sd_rhoPrime_of_lemma6_1_1` (`WeilClasses.Orlov.Sec6_3`)
applied to Lemma 6.1.1; its two inputs are the `Spin(V)`-equivariance of
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD` (`s61_PiMap_rhoExt`, from Lemma 6.3.2) and the operator form of
Remark 2.3.1 (`PiMap_changeB0bar`, `WeilClasses.Chevalley.Sec2_3`). As in the paper, (6.1.8) is
[Orlov, Th. 2.10] (`orlov_theorem2_10`) and (6.1.9) is [Huybrechts, Ex. 9.41] (`huybrechts_ex9_41`);
these cited results are proved in `WeilClasses.External` (in the model, from the computation behind
Proposition 6.1.2, which does not use them, resp. from `ρ'` being a representation). The filtration
claims are proved by the paper's "more direct" route through Lemma 6.1.1 (via Proposition 6.1.2)
instead of [GLO, Prop. 4.3.7, Cor. 4.3.8] (`glo_prop4_3_7`, also proved in `WeilClasses.External`).
The helpers of this section (prefix `s61_`) not listed below are in `WeilClasses.Orlov.Basis` and
`WeilClasses.Orlov.Sec6_3`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P10) -/

section S61Pair2

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_ι_mul_ι_eq_ιMulti (u v : V F n) :
    ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v = ExteriorAlgebra.ιMulti F 2 ![u, v] := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

omit [CharZero F] in
/-- The alternating form of `c₁(𝒫)`: `(c₁(𝒫), x ∧ y) = θ_x(w_y) - θ_y(w_x)`. -/
theorem s61_extPairing_c1P (x y : V F n) :
    extPairing F n (c1P F n) (ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F y) = x.1 y.2 - y.1 x.2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hH : ∀ w : H1 F 0, w = 0 := fun w => funext fun i => absurd i.2 (by simp)
    have hV : ∀ v : V F 0, v = 0 := fun v =>
      Prod.ext (LinearMap.ext fun w => by rw [hH w, map_zero]; rfl) (hH v.2)
    rw [hV x, hV y]
    simp
  rw [s61_c1P_eq, map_sum, LinearMap.sum_apply, s61_dual_apply F n x.1, s61_dual_apply F n y.1,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s61_a_eq, s61_ι_mul_ι_eq_ιMulti, s61_ι_mul_ι_eq_ιMulti, s61_extPairing_ιMulti F n (by omega),
    Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, s61_pairing_apply,
    map_zero, LinearMap.zero_apply, zero_add, add_zero, f, LinearMap.proj_apply]
  ring

omit [CharZero F] in
theorem s61_extPairing_basisExt_flip_eq (M : Finset (Fin (2 * n + 2 * n))) :
    ∃ k : ℕ, extPairing F n (basisExt F n M)
      (basisExt F n (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding)) =
      (-1 : F) ^ k := by
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
  exact ⟨_, rfl⟩

omit [CharZero F] in
theorem s61_repr_mul_extPairing_flip (ω : ExtV F n) (M : Finset (Fin (2 * n + 2 * n))) :
    (basisExt F n).repr ω M * extPairing F n (basisExt F n M)
      (basisExt F n (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding)) =
      extPairing F n ω
        (basisExt F n (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding)) := by
  classical
  conv_rhs => rw [← (basisExt F n).sum_repr ω]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single M]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro N _ hN
    rw [map_smul, LinearMap.smul_apply, s61_extPairing_basisExt_eq_zero, smul_zero]
    intro h'
    apply hN
    have := congrArg (fun P : Finset (Fin (2 * n + 2 * n)) =>
      P.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding) h'
    simp only [s61_flip_flip] at this
    exact this.symm
  · intro h'; exact absurd (Finset.mem_univ M) h'

omit [CharZero F] in
theorem s61_basisExt_card_two (N : Finset (Fin (2 * n + 2 * n))) (h : N.card = 2) :
    ∃ a b, basisExt F n N = ExteriorAlgebra.ι F (basisV F n a) * ExteriorAlgebra.ι F (basisV F n b) :=
  ⟨N.orderEmbOfFin h 0, N.orderEmbOfFin h 1, by
    rw [s61_basisExt_eq_ιMulti' F n N h, s61_ι_mul_ι_eq_ιMulti]
    congr 1
    ext i : 1
    fin_cases i <;> rfl⟩

theorem s61_extPairing_rhoExt_left (g : Spin F n) (c z : ExtV F n) :
    extPairing F n (rhoExt F n g c) z = extPairing F n c (rhoExt F n g⁻¹ z) := by
  conv_lhs => rw [← s61_rhoExt_rhoExt_inv F n g z]
  exact s61_extPairing_rhoExt F n g c _

end S61Pair2

section S61Int

variable (n : ℕ)

theorem s61_basisV_mem_VZ (a : Fin (2 * n + 2 * n)) : basisV ℚ n a ∈ VZ n := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · rw [s61_basisV_castAdd]
    refine ⟨fun j => ?_, fun j => ⟨0, rfl⟩⟩
    rw [s61_f_e]
    by_cases h : i = j
    · exact ⟨1, by rw [ite_eq_left h]; simp⟩
    · exact ⟨0, by rw [ite_eq_right h]; simp⟩
  · rw [s61_basisV_natAdd]
    refine ⟨fun j => ⟨0, rfl⟩, fun j => ?_⟩
    by_cases h : j = i
    · exact ⟨1, by simp [e, h]⟩
    · exact ⟨0, by simp [e, h]⟩

theorem s61_neg_one_pow_mem_int (k : ℕ) : (-1 : ℚ) ^ k ∈ (Int.castRingHom ℚ).range :=
  ⟨(-1) ^ k, by simp⟩

theorem s61_epsSign_mem_int (K L : Finset (Fin (2 * n))) :
    epsSign ℚ n K L ∈ (Int.castRingHom ℚ).range := by
  rw [s61_epsSign_eq]
  split_ifs
  · exact s61_neg_one_pow_mem_int _
  · exact zero_mem _

theorem s61_smul_mem_ExtZ {q : ℚ} (hq : q ∈ (Int.castRingHom ℚ).range) {x : ExtV ℚ n}
    (hx : x ∈ ExtZ n) : q • x ∈ ExtZ n := by
  obtain ⟨z, rfl⟩ := hq
  rw [eq_intCast, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem s61_smul_mem_SZZ {q : ℚ} (hq : q ∈ (Int.castRingHom ℚ).range)
    {x : S ℚ n ⊗[ℚ] S ℚ n} (hx : x ∈ SZZ n) : q • x ∈ SZZ n := by
  obtain ⟨z, rfl⟩ := hq
  rw [eq_intCast, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem s61_basisExt_mem_ExtZ (M : Finset (Fin (2 * n + 2 * n))) : basisExt ℚ n M ∈ ExtZ n := by
  intro K
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s61_basisS_mem_SZ (K : Finset (Fin (2 * n))) : basisS ℚ n K ∈ SZ n := by
  intro L
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s61_tmul_mem_SZZ (K L : Finset (Fin (2 * n))) :
    basisS ℚ n K ⊗ₜ[ℚ] basisS ℚ n L ∈ SZZ n :=
  AddSubgroup.subset_closure ⟨_, s61_basisS_mem_SZ n K, _, s61_basisS_mem_SZ n L, rfl⟩

theorem s61_pullX_mul_pullXHat_mem_ExtZ (I J : Finset (Fin (2 * n))) :
    pullX ℚ n (basisS ℚ n I) * pullXHat ℚ n (basisSHat ℚ n J) ∈ ExtZ n := by
  rw [s61_pullX_basisS, s61_pullXHat_basisSHat, basisExt, s61_basis_mul_basis]
  split_ifs
  · exact s61_smul_mem_ExtZ n (s61_neg_one_pow_mem_int _) (s61_basisExt_mem_ExtZ n _)
  · exact zero_mem _

theorem s61_phiOrlov_basis_mem_ExtZ (K L : Finset (Fin (2 * n))) :
    phiOrlov ℚ n (basisS ℚ n K ⊗ₜ[ℚ] basisS ℚ n L) ∈ ExtZ n := by
  rw [phiOrlov, LinearMap.comp_apply, LinearMap.comp_apply, muStar_basis, map_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun I _ => ?_
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis,
    TensorProduct.tmul_smul, map_smul, LinearEquiv.coe_coe, kunnethXHat_tmul]
  exact s61_smul_mem_ExtZ n (Subring.mul_mem _ (s61_epsSign_mem_int n _ _)
    (s61_epsSign_mem_int n _ _)) (s61_smul_mem_ExtZ n (Subring.mul_mem _
      (s61_neg_one_pow_mem_int _) (s61_epsSign_mem_int n _ _))
        (s61_pullX_mul_pullXHat_mem_ExtZ n _ _))

theorem s61_phiOrlov_tmul_mem_ExtZ {s t : S ℚ n} (hs : s ∈ SZ n) (ht : t ∈ SZ n) :
    phiOrlov ℚ n (s ⊗ₜ[ℚ] t) ∈ ExtZ n := by
  rw [← (basisS ℚ n).sum_repr s, ← (basisS ℚ n).sum_repr t, TensorProduct.sum_tmul, map_sum]
  refine AddSubgroup.sum_mem _ fun K _ => ?_
  rw [TensorProduct.tmul_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun L _ => ?_
  rw [TensorProduct.smul_tmul_smul, map_smul]
  obtain ⟨z₁, hz₁⟩ := hs K
  obtain ⟨z₂, hz₂⟩ := ht L
  rw [hz₁, hz₂]
  exact s61_smul_mem_ExtZ n ⟨z₁ * z₂, by simp⟩ (s61_phiOrlov_basis_mem_ExtZ n K L)

theorem s61_phiOrlovInv_basisExt_mem_SZZ (M : Finset (Fin (2 * n + 2 * n))) :
    phiOrlovInv ℚ n (basisExt ℚ n M) ∈ SZZ n := by
  obtain ⟨L, K, -, hM⟩ := s61_basisExt_eq_beta ℚ n M
  have hcomm : pullXHat ℚ n (basisSHat ℚ n L) * pullX ℚ n (basisS ℚ n K) =
      (-1 : ℚ) ^ (L.card * K.card) • (pullX ℚ n (basisS ℚ n K) * pullXHat ℚ n (basisSHat ℚ n L)) :=
    s61_mul_comm_of_mem (s61_map_mem _ (s61_basis_mem _ L)) (s61_map_mem _ (s61_basis_mem _ K))
  rw [hM, hcomm, ← kunnethXHat_tmul, map_smul, phiOrlovInv, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, s61_phiP_basisSHat, TensorProduct.tmul_smul,
    map_smul, s61_muStarInv_basis]
  refine s61_smul_mem_SZZ n (s61_neg_one_pow_mem_int _) (s61_smul_mem_SZZ n ?_ ?_)
  · exact Subring.mul_mem _ (Subring.mul_mem _ (s61_neg_one_pow_mem_int _)
      (s61_neg_one_pow_mem_int _)) (s61_neg_one_pow_mem_int _)
  · refine AddSubgroup.sum_mem _ fun I _ => s61_smul_mem_SZZ n ?_ (s61_tmul_mem_SZZ n _ _)
    exact Subring.mul_mem _ (s61_neg_one_pow_mem_int _)
      (Subring.mul_mem _ (s61_epsSign_mem_int n _ _) (s61_epsSign_mem_int n _ _))

end S61Int

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- (6.1.3) Orlov's cohomological map `φ : S ⊗ S → ⋀•V` is an isomorphism. -/
theorem phiOrlov_bijective : Function.Bijective (phiOrlov F n) :=
  Function.bijective_iff_has_inverse.mpr ⟨phiOrlovInv F n,
    fun y => LinearMap.congr_fun (phiOrlovInv_comp_phiOrlov F n) y,
    fun x => LinearMap.congr_fun (phiOrlov_comp_phiOrlovInv F n) x⟩

/-- (6.1.3) over the integers: `φ` maps `H*(X × X, ℤ) = S_ℤ ⊗ S_ℤ` onto `H*(X × X̂, ℤ) = ⋀•V_ℤ` (the
paper's `φ` is the correspondence isomorphism of an equivalence of derived categories, between
integral cohomology groups; checked numerically for `n = 1, 2`). -/
theorem phiOrlov_image_SZZ (n : ℕ) :
    phiOrlov ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, hs, t, ht, rfl⟩ := hy
      exact s61_phiOrlov_tmul_mem_ExtZ n hs ht
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro hx
    refine ⟨phiOrlovInv ℚ n x, ?_, LinearMap.congr_fun (phiOrlov_comp_phiOrlovInv ℚ n) x⟩
    have hx' : x ∈ ExtZ n := hx
    rw [← (basisExt ℚ n).sum_repr x, map_sum]
    refine AddSubgroup.sum_mem _ fun M _ => ?_
    obtain ⟨z, hz⟩ := hx' M
    rw [map_smul, hz]
    exact s61_smul_mem_SZZ n ⟨z, by simp⟩ (s61_phiOrlovInv_basisExt_mem_SZZ n M)

/-- **(6.1.4)** (`rho-prime-g`) as printed: `ρ'_g = φ (m_g × m†_g) φ⁻¹`. -/
theorem rhoPrime_eq_phiOrlov_conj (g : Spin F n) :
    rhoPrime F n g =
      phiOrlov F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (mDagger F n (g : C F n)) ∘ₗ
        phiOrlovInv F n := by
  have h : tauTensor F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) ∘ₗ
      tauTensor F n = TensorProduct.map (m F n (g : C F n)) (mDagger F n (g : C F n)) := by
    refine TensorProduct.ext' fun u v => ?_
    simp [tauTensor, mDagger]
  rw [rhoPrime, phiPrime, phiPrimeInv, ← h]
  simp only [LinearMap.comp_assoc]

/-- **Lemma 6.1.1** (`lemma-orlov-isomorphism-is-chevalley`).
`φ = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ φ̃ ∘ (id ⊗ τ)`, where `φ̃ : H*(X × X) → H*(X̂ × X)` is Chevalley's
isomorphism (2.3.2) and `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)`. (Checked numerically for
`n = 1, 2` with the sign convention of `c1P`.) -/
theorem lemma6_1_1 : phiOrlov F n = PiMap F n ∘ₗ varphiTilde F n ∘ₗ tauTensor F n := by
  rw [← lemma6_3_1, LinearMap.comp_assoc, tauTensor_comp_tauTensor, LinearMap.comp_id,
    phiOrlov_eq_PiMap_comp_nuOrlov]

/-- The proof of Proposition 6.1.2 (`proposition6_1_2`, stated below), by the authorized algebraic
argument (see its docstring): `φ' = φ ∘ (id ⊗ τ) = Π ∘ E_{B̄₀} ∘ φ̃_sym` (Lemma 6.1.1, Lemma 6.3.1,
Remark 2.3.1); `φ̃_sym` is `Spin(V)`-equivariant (Trautman), `Π E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` (operator
form of Remark 2.3.1) and `Π = ±PD` commutes with `⋀ρ_g` (Lemma 6.3.2, `ρ_g ∈ SO(V)`). The
computation is `sd_rhoPrime_of_lemma6_1_1` (`WeilClasses.Orlov.Sec6_3`), applied to Lemma 6.1.1. -/
theorem s61_proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x :=
  sd_rhoPrime_of_lemma6_1_1 F n (lemma6_1_1 F n) g x

/-- (§6.1, TeX lines 2228–2235; [GLO, Prop. 4.3.7, Cor. 4.3.8], "more directly by Lemma 6.1.1")
`ρ'_g` preserves the decreasing filtration `F_k(⋀•V) = ⊕_{i ≥ k} ⋀^i V` (6.1.5).
Proof in the model: by Lemma 6.1.1 through Proposition 6.1.2 (`s61_proposition6_1_2`),
`ρ'_g = exp(β) ∪ ρ_g` with `β ∈ ⋀²V` (instead of citing [GLO]). -/
theorem rhoPrime_mem_extFiltGE (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    rhoPrime F n g x ∈ extFiltGE F n k := by
  have h1 := s61_exp_sub_one_mem F n (s61_beta_mem F n g)
  have h2 := s61_rhoExt_mem_extFiltGE F n g hx
  rw [s61_proposition6_1_2, ← sub_add_cancel (IsNilpotent.exp _) 1, add_mul, one_mul]
  exact add_mem (s61_extFiltGE_mono F n (by omega) (s61_mul_mem_extFiltGE F n h1 h2)) h2

/-- (§6.1, TeX lines 2228–2235; [GLO, Prop. 4.3.7, Cor. 4.3.8]) The graded action induced by `ρ'_g`
on `F_k / F_{k+1} = ⋀^k V` is `⋀^k ρ_g`, induced from `ρ : Spin(V) → SO(V)`.
Proof in the model: from Proposition 6.1.2 (`s61_proposition6_1_2`), `exp(β) - 1 ∈ F_2`. -/
theorem rhoPrime_projDeg (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  have h1 := s61_exp_sub_one_mem F n (s61_beta_mem F n g)
  have h2 := s61_rhoExt_mem_extFiltGE F n g hx
  rw [s61_proposition6_1_2, ← sub_add_cancel (IsNilpotent.exp _) 1, add_mul, one_mul, map_add,
    s61_projDeg_eq_zero_of_mem_extFiltGE F n
      (s61_extFiltGE_mono F n (by omega) (s61_mul_mem_extFiltGE F n h1 h2)),
    zero_add, s61_projDeg_rhoExt]

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10], [Huybrechts, Prop. 9.39]) For every `g ∈ Spin(V)`
there is a (topological) line bundle `N_g` on `X × X̂` with `ρ'_g = ch(N_g) ∪ ρ_g`. In the model:
there is a class `c = c₁(N_g) ∈ H²(X × X̂) = ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g`.
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0` (the integral version, `c` integral for
`g` integral, is `equation6_1_8_integral`).
Proof: [Orlov, Th. 2.10] (`orlov_theorem2_10`, the paper's citation). -/
theorem equation6_1_8 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x :=
  orlov_theorem2_10 F n g

/-- **(6.1.9)** (`eq-1-cocycle-identity`; [Huybrechts, Ex. 9.41]) The cocycle identity
`c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`, for all `g₁, g₂ ∈ Spin(V)`, where `c₁(N_g)` is
any class satisfying (6.1.8) for `g` (it is unique: `exp(c) = ρ'_g(1)`).
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`.
Proof: [Huybrechts, Ex. 9.41] (`huybrechts_ex9_41`, the paper's citation). -/
theorem equation6_1_9 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ :=
  huybrechts_ex9_41 F n g₁ g₂ c₁ c₂ c₁₂ hc₁ hc₂ hc₁₂ h₁ h₂ h₁₂

/-- **Proposition 6.1.2**
(`prop-extension-class-of-decreasing-filtration-of-spin-V-representations`),
equation **(6.1.10)** (`eq-relating-rho-and-rho-prime`):
`ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`.
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`. (Checked numerically for `n = 1, 2`
with the sign convention of `c1P`;
it fails for the opposite sign.)

Departure from the paper (authorized by the project owner; `notes/proof-plans.md`): the paper
reduces the statement to abelian surfaces (Lemma 6.2.5, via Orlov's Th. 2.10, Verbitsky's Zariski
density and Obata's Th. B), which needs sheaves and algebraic groups not available here. The proof
(`s61_proposition6_1_2`) is the algebraic argument through the symmetric Chevalley isomorphism of
Remark 2.3.1: by Lemma 6.1.1 and Lemma 6.3.1, `φ' = φ ∘ (id ⊗ τ) = Π ∘ ψ ∘ φ_Chev` with
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}`, and `ψ = E_{B̄₀} ∘ ψ_sym` (`psi_eq_changeB0bar_comp_psiSym`). The symmetric
`φ̃_sym = ψ_sym ∘ φ_Chev` is `Spin(V)`-equivariant ([Trautman, Th. 1(i)],
`remark2_3_1_sym_equivariant`); `Π ∘ E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` (the operator form of Remark 2.3.1,
`PiMap_changeB0bar`, proved from `E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})` and
`Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π`); and `Π = ±PD` (Lemma 6.3.2) commutes with `⋀ρ_g` because
`ρ_g ∈ SO(V)` preserves the pairing and the volume form (`s61_PiMap_rhoExt`). Hence
`ρ'_g = exp(½c₁(𝒫)) ∪ ⋀ρ_g ∘ exp(-½c₁(𝒫)) ∪ = exp(½[c₁(𝒫) - ρ_g c₁(𝒫)]) ∪ ρ_g`. -/
theorem proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x :=
  s61_proposition6_1_2 F n g x

end Field

section Integral

variable (n : ℕ)

/-- (§6.1, TeX lines 2273–2274) The integral alternating bilinear form `c₁(𝒫)` (the class
`c₁(𝒫) ∈ ⋀²V` paired with `x ∧ y` by the determinant pairing of `(·,·)_V`) and the symmetric
pairing `(·,·)_V` agree modulo `2` on the lattice `V`. -/
theorem c1P_pairing_mod_two (x y : V ℚ n) (hx : x ∈ VZ n) (hy : y ∈ VZ n) :
    ∃ k : ℤ, extPairing ℚ n (c1P ℚ n) (ExteriorAlgebra.ι ℚ x * ExteriorAlgebra.ι ℚ y) -
      pairing ℚ n x y = 2 * k := by
  have hx' : (∀ i, ∃ z : ℤ, x.1 (e ℚ n i) = z) ∧ ∀ i, ∃ z : ℤ, x.2 i = z := hx
  have hy' : (∀ i, ∃ z : ℤ, y.1 (e ℚ n i) = z) ∧ ∀ i, ∃ z : ℤ, y.2 i = z := hy
  choose zx hzx using hx'.2
  choose zy hzy using hy'.1
  refine ⟨-∑ i, zy i * zx i, ?_⟩
  rw [s61_extPairing_c1P, s61_pairing_apply, s61_dual_apply ℚ n y.1 x.2]
  simp only [hzx, hzy]
  push_cast
  ring

/-- (§6.1, TeX lines 2273–2275) The class `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` is integral for every `g` in the
integral group `Spin(V)`. -/
theorem half_c1P_sub_rho_mem_ExtZ (g : Spin ℚ n) (hg : g ∈ SpinZ n) :
    (2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)) ∈ ExtZ n := by
  intro M
  have hω := s61_beta_mem ℚ n g
  by_cases hM : M.card = 2
  · obtain ⟨k, hk⟩ := s61_extPairing_basisExt_flip_eq ℚ n M
    have hrepr := s61_repr_mul_extPairing_flip ℚ n
      ((2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n))) M
    obtain ⟨a, b, hab⟩ := s61_basisExt_card_two ℚ n
      (M.map (finAddFlip : Fin (2 * n + 2 * n) ≃ Fin (2 * n + 2 * n)).toEmbedding)
      (by rw [Finset.card_map, hM])
    rw [hk, hab] at hrepr
    have hu := s61_basisV_mem_VZ n a
    have hv := s61_basisV_mem_VZ n b
    have hginv : g⁻¹ ∈ SpinZ n := inv_mem hg
    have hu' : rho ℚ n g⁻¹ (basisV ℚ n a) ∈ VZ n := hginv.2 _ hu
    have hv' : rho ℚ n g⁻¹ (basisV ℚ n b) ∈ VZ n := hginv.2 _ hv
    obtain ⟨k₁, hk₁⟩ := c1P_pairing_mod_two n _ _ hu hv
    obtain ⟨k₂, hk₂⟩ := c1P_pairing_mod_two n _ _ hu' hv'
    rw [s61_pairing_rho] at hk₂
    have hpair : extPairing ℚ n ((2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)))
        (ExteriorAlgebra.ι ℚ (basisV ℚ n a) * ExteriorAlgebra.ι ℚ (basisV ℚ n b)) = k₁ - k₂ := by
      rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, s61_extPairing_rhoExt_left,
        map_mul (rhoExt ℚ n g⁻¹), rhoExt, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
        smul_eq_mul]
      push_cast
      linear_combination (2 : ℚ)⁻¹ * hk₁ - (2 : ℚ)⁻¹ * hk₂
    rw [hpair] at hrepr
    refine ⟨(-1) ^ k * (k₁ - k₂), ?_⟩
    have hsq : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    push_cast
    linear_combination (-1 : ℚ) ^ k * hrepr - (basisExt ℚ n).repr
      ((2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n))) M * hsq
  · have h0 : (basisExt ℚ n).repr ((2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n))) M = 0 :=
      s61_repr_eq_zero_of_mem _ hω hM
    exact ⟨0, by rw [h0]; simp⟩

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10]) for the integral group: for `g ∈ Spin(V)` the class
`c₁(N_g)` of the line bundle `N_g` is integral. -/
theorem equation6_1_8_integral (g : Spin ℚ n) (hg : g ∈ SpinZ n) :
    ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧ ∀ x : ExtV ℚ n,
      rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x :=
  ⟨_, s61_beta_mem ℚ n g, half_c1P_sub_rho_mem_ExtZ n g hg, proposition6_1_2 ℚ n g⟩

end Integral

end WeilClasses
