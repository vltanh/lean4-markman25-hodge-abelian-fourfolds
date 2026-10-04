module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Spinor.Integral
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.Orlov.Sec6_3
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
import TauCeti.LinearAlgebra.ExteriorPower.Basic

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
`proposition6_1_2`), whose two inputs proved here are the `Spin(V)`-equivariance of
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD` (`s61_PiMap_rhoExt`, from Lemma 6.3.2) and the operator form of
Remark 2.3.1 (`s61_PiMap_changeB0bar`). The cited facts [GLO, Prop. 4.3.7], [Orlov, Th. 2.10] and
[Huybrechts, Ex. 9.41] are not used: in the model, the filtration claims and (6.1.8) follow from
Proposition 6.1.2, and (6.1.9) from `ρ'` being a representation.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P10) -/

section S61Equivariance

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_psiPinvShift_eq_smul : psiPinvShift F n = (-1 : F) ^ n • psiPinv F n := by
  rw [psiPinvShift, psiPinv, chPinvShift, map_smul, map_smul]

theorem s61_PiMap_eq_smul : PiMap F n = (-1 : F) ^ n • PiMap0 F n := by
  rw [PiMap, PiMap0, s61_psiPinvShift_eq_smul, TensorProduct.map_smul_right, LinearMap.smul_comp,
    LinearMap.comp_smul]

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

theorem s61_rhoExt_mem (g : Spin F n) {d : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^d (V F n)) :
    rhoExt F n g x ∈ ⋀[F]^d (V F n) := s61_map_mem _ hx

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

omit [CharZero F] in
theorem s61_commute_c1P (z : ExtV F n) : Commute (c1P F n) z := by
  rw [s61_c1P_eq]
  exact Commute.sum_left _ _ _ fun i _ => s61_commute_a F n i z

omit [CharZero F] in
theorem s61_isNilpotent_smul_c1P (t : F) : IsNilpotent (t • c1P F n) := by
  rw [s61_c1P_eq]; exact s61_isNilpotent_smul_sum F n t Finset.univ

end S61Equivariance

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

section S61Pair2

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_dual_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    θ w = ∑ i, θ (e F n i) * w i := by
  conv_lhs => rw [show w = ∑ i, w i • e F n i by ext j; simp [e, Pi.single_apply]]
  simp [map_sum, mul_comm]

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

/-- **The operator form of Remark 2.3.1** (P05's `PiMap_changeB0bar`, proved here from the explicit
transforms): `Π(E_{B̄₀} x) = exp(½c₁(𝒫)) ∪ Π(x)`, since `E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})` and
`Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π`. -/
theorem s61_PiMap_changeB0bar (x : ExtV F n) :
    PiMap F n (changeB0bar F n x) =
      IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) * PiMap F n x := by
  rw [s61_changeB0bar_eq_G, s61_PiMap_G, s61_c1P_eq, Fin.sum_univ_def, s61_exp_list]

end S61Change

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
form of Remark 2.3.1) and `Π = ±PD` commutes with `⋀ρ_g` (Lemma 6.3.2, `ρ_g ∈ SO(V)`). -/
theorem s61_proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x := by
  have hφ' : ∀ y, phiPrime F n y = PiMap F n (changeB0bar F n (varphiTildeSym F n y)) := by
    intro y
    rw [phiPrime, LinearMap.comp_apply, lemma6_1_1, LinearMap.comp_apply, LinearMap.comp_apply,
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
    rw [← hx, hφ', s61_PiMap_changeB0bar, ← mul_assoc,
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
        rw [s61_PiMap_changeB0bar, s61_PiMap_rhoExt]
    _ = IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) *
          (IsNilpotent.exp (-(rhoExt F n g ((2 : F)⁻¹ • c1P F n))) * rhoExt F n g x) := by
        rw [hw, map_mul, IsNilpotent.map_exp (hc _).neg, map_neg]
    _ = IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x := by
        rw [← mul_assoc, ← IsNilpotent.exp_add_of_commute ?_ (hc _) hρc.neg, map_smul, smul_sub,
          sub_eq_add_neg]
        exact ((s61_commute_c1P F n _).smul_left _)

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
Proof in the model: `c = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]` by Proposition 6.1.2 (`s61_proposition6_1_2`;
the existence of `N_g` is not formalized, so [Orlov, Th. 2.10] is not used). -/
theorem equation6_1_8 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x :=
  ⟨_, s61_beta_mem F n g, s61_proposition6_1_2 F n g⟩

/-- **(6.1.9)** (`eq-1-cocycle-identity`; [Huybrechts, Ex. 9.41]) The cocycle identity
`c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`, for all `g₁, g₂ ∈ Spin(V)`, where `c₁(N_g)` is
any class satisfying (6.1.8) for `g` (it is unique: `exp(c) = ρ'_g(1)`).
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`.
Proof in the model (the content of [Huybrechts, Ex. 9.41]): `ρ'` is a representation, so evaluating
`ρ'_{g₁g₂} = ρ'_{g₁} ρ'_{g₂}` at `1` gives `exp(c₁₂) = exp(c₁ + ρ_{g₁}c₂)`; the degree-`2` parts
agree. -/
theorem equation6_1_9 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ := by
  -- `ρ'` is a representation: `ρ'_{g₁g₂} = ρ'_{g₁} ρ'_{g₂}`; evaluate at `1`
  have hrep : rhoPrime F n (g₁ * g₂) 1 = rhoPrime F n g₁ (rhoPrime F n g₂ 1) := by
    have h := (rhoPrimeRep F n).map_mul g₁ g₂
    have h' : rhoPrime F n (g₁ * g₂) = rhoPrime F n g₁ * rhoPrime F n g₂ := h
    rw [h', Module.End.mul_apply]
  have hρc₂ := s61_rhoExt_mem F n g₁ hc₂
  have hcomm : Commute c₁ (rhoExt F n g₁ c₂) := by
    have := s61_mul_comm_of_mem hc₁ hρc₂
    show c₁ * _ = _ * c₁
    rw [this, show (2 * 2 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  have e1 : rhoPrime F n (g₁ * g₂) 1 = IsNilpotent.exp c₁₂ := by
    rw [h₁₂, map_one, mul_one]
  have e2 : rhoPrime F n g₂ 1 = IsNilpotent.exp c₂ := by
    rw [h₂, map_one, mul_one]
  have e3 : rhoPrime F n g₁ (IsNilpotent.exp c₂) = IsNilpotent.exp (c₁ + rhoExt F n g₁ c₂) := by
    rw [h₁, IsNilpotent.map_exp (s61_isNilpotent_of_mem_two F n hc₂) (rhoExt F n g₁),
      IsNilpotent.exp_add_of_commute hcomm (s61_isNilpotent_of_mem_two F n hc₁)
        (s61_isNilpotent_of_mem_two F n hρc₂)]
  rw [e1, e2, e3] at hrep
  have := congrArg (projDeg F n 2) hrep
  rwa [s61_projDeg_two_exp F n hc₁₂, s61_projDeg_two_exp F n (add_mem hc₁ hρc₂)] at this

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
`PiMap_changeB0bar`, proved here as `s61_PiMap_changeB0bar` from `E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})`
and `Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π`); and `Π = ±PD` (Lemma 6.3.2) commutes with `⋀ρ_g` because `ρ_g ∈ SO(V)`
preserves the pairing and the volume form (`s61_PiMap_rhoExt`). Hence
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
