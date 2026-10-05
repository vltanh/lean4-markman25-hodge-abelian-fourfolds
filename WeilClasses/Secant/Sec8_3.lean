module

public import WeilClasses.Secant.Sec8_2
public import WeilClasses.PureSpinor.Lemma2_2_7
public import WeilClasses.Orlov.Sec6_2
public import WeilClasses.Orlov.Sec6_4
import WeilClasses.Orlov.Cor1_3_2

/-!
# §8.3 up to Lemma 8.3.1: the `κ₃`-class of `Φ(F₁ ⊠ F₁)` is independent of `h³`

Statements of the paper's §8.3, TeX lines 3963–4041 (`n = 3`, the notation of Lemma 8.2.1:
`Θ = ThetaStd ℚ 3` ample for the complex structure `J` of `X`, `w = ch(F₁) = chF1 d`,
`P = span{α, β}` the plane of the `K`-secant `P_Θ` (`PJac`), `λ₁ = exp(√-dΘ) = P.u₁`,
`λ₂ = λ̄₁ = P.u₂`).

* `(α, β)_S = ∫_X τ(α) β = ∫_X α β = -4d ≠ 0` (`tau_alphaJac`, `mukai_alphaJac_betaJac`), so
  Assumption 2.4.1 holds (`PJac_not_isIsotropic`, `PJac_assumption2_4_1`).
* `h`: the class `Ξ_P^♯` (`KSecant.hClass`), which spans `H²(X × X̂, ℚ)^{Spin(V)_P}` and is ample
  (`WeilClasses.Main.Intro`; the paper: "an ample class `h` in the rank `1` subgroup
  `H²(X × X̂, ℤ)^{Spin(V)_P}`"; the statements below only depend on the line `ℚh`).
* **Lemma 8.3.1** (`lemma8_3_1_rank`, `lemma8_3_1`), with `ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w) = φ'(w ⊗ τ w)`
  (`lemma8_3_1_ch`; `φ(ch F₁ ⊠ ch F₁)` is the Chern character of `Φ(F₁ ⊠ F₁)` by GRR, not
  formalized), the invariance of the two classes (`lemma8_3_1_invariant`; for `κ₃` by
  Corollary 1.3.2, `corollary1_3_2` in `WeilClasses.Orlov.Cor1_3_2`), the value of the rank
  (`lemma8_3_1_rank_eq`: `8d`), and the claims of the proof (`chF1_eq_lambda`, `tau_lambda`,
  `chF1_tmul_tau_decomp`; `λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂` is not `Spin(V_K)_{ℓ₁,ℓ₂}`-invariant by Lemma 2.2.7
  and Proposition 6.4.1(1), `s8_HW_not_invariant`).

Checked numerically (exact arithmetic, `d = 1, 2, 3, 5, 7`): `(α, β)_S = -4d`, the rank of
`φ(w ⊗ w)` is `8d`, `h³` and `κ₃(φ(w ⊗ w))` are linearly independent, and
`κ₃ ∈ ℚh³ ⊕ ĤW_P`.

**Left out (sheaf-theoretic).** After the proof of Lemma 8.3.1 (TeX lines 4027–4041): the
deformations of `F = I_{∪Cᵢ}` and the injective homomorphism (8.3.1) into `Ext¹(F, F)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (d : ℚ)

/-! ## `(α, β)_S = -4d` -/

/-- (§8.3, TeX line 3967) `τ(α) = α` (`α` has degrees `0` and `4`). -/
theorem tau_alphaJac : tau ℚ 3 (alphaJac d) = alphaJac d := by
  have hT := s8_ThetaStd_mem ℚ 3
  rw [alphaJac, map_sub, map_smul, s8_tau_one, s8_tau_pow ℚ 3 hT, neg_sq]

/-- (§8.3, TeX line 3967) `(α, β)_S = ∫_X τ(α) ∪ β = ∫_X α ∪ β = -4d`. -/
theorem mukai_alphaJac_betaJac : mukai ℚ 3 (alphaJac d) (betaJac d) = -4 * d := by
  -- `∫ αβ = ∫ (Θ - (2d/3)Θ³) = -4d` (`∫ Θ = 0`, `Θ³ = 6[pt]`, `Θ⁵ = 0`)
  have hT := s8_ThetaStd_mem ℚ 3
  have h5 : ThetaStd ℚ 3 ^ 5 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have hI : integral ℚ 3 (ThetaStd ℚ 3) = 0 :=
    s8_integral_eq_zero_of_mem ℚ 3 (by norm_num : (2 : ℕ) ≠ 2 * 3) hT
  have hI3 : integral ℚ 3 (ThetaStd ℚ 3 ^ 3) = 6 := by
    rw [s8_Theta_cube, map_smul, s8_integral_pt, smul_eq_mul, mul_one]
  change integral ℚ 3 (tau ℚ 3 (alphaJac d) * betaJac d) = _
  rw [tau_alphaJac, alphaJac, betaJac, s8_pt_three]
  simp only [sub_mul, mul_sub, one_mul, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← pow_add,
    Nat.reduceAdd, h5, smul_zero, sub_zero, map_sub, map_smul, hI, hI3, smul_eq_mul]
  ring

/-- (§8.3, TeX lines 3966–3967) "Assumption 2.4.1 is satisfied, since `(α, β)_S = -4d ≠ 0`": the
plane `P = span{α, β}` is not isotropic for the Mukai pairing. -/
theorem PJac_not_isIsotropic {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd : 0 < d) : ¬ (PJac d hΘ hd).IsIsotropic := by
  intro h
  have hα : alphaJac d ∈ (PJac d hΘ hd).Pℚ := by
    rw [PJac_Pℚ_eq d hΘ hd]; exact Submodule.subset_span (by simp)
  have hβ : betaJac d ∈ (PJac d hΘ hd).Pℚ := by
    rw [PJac_Pℚ_eq d hΘ hd]; exact Submodule.subset_span (by simp)
  have := h _ hα _ hβ
  rw [mukai_alphaJac_betaJac] at this
  linarith

/-- (§8.3, TeX lines 3966–3967) `P_Θ` satisfies Assumption 2.4.1 (`PTheta_assumption2_4_1`). -/
theorem PJac_assumption2_4_1 {J : Module.End ℝ (H1 ℝ 3)} (hJ : IsComplexStructure J)
    (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) : Assumption2_4_1 (PJac d hΘ hd) J :=
  PTheta_assumption2_4_1 3 d hd (by norm_num) J hJ (ThetaStd ℚ 3) hΘ

/-! ## Helpers (prefix `s8_`): `φ` on basis vectors and the rank of `φ(x ⊗ y)` -/

section S8Phi

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `φ(e_K ⊗ e_L)` in the basis, from `μ^*` and `ψ_{𝒫⁻¹[n]}` on basis vectors (§6.3,
`muStar_basis`, `psiPinvShift_basis`). -/
theorem s8_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, ((epsSign F n I (K \ I) * epsSign F n (K \ I) L) *
          ((-1 : F) ^ ((K \ I ∪ L).card * ((K \ I ∪ L).card + 3) / 2) *
            epsSign F n (K \ I ∪ L) (K \ I ∪ L)ᶜ)) •
        (pullX F n (basisS F n I) * pullXHat F n (basisSHat F n (K \ I ∪ L)ᶜ)) := by
  simp only [phiOrlov, LinearMap.comp_apply, LinearEquiv.coe_coe, muStar_basis, map_sum, map_smul,
    TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis, tmul_smul, kunnethXHat_tmul,
    smul_smul]

/-- The rank of `φ(e_K ⊗ e_L)` (only the term `I = ∅` of `μ^*` contributes in degree `0`). -/
theorem s8_rank_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    rankExt F n (phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L)) =
      if K ∪ L = Finset.univ then (-1 : F) ^ n * epsSign F n K L else 0 := by
  rw [s8_phiOrlov_basis, map_sum]
  simp only [map_smul, map_mul, rankExt, pullX, pullXHat, s8_algebraMapInv_map,
    s8_algebraMapInv_basisS, s8_algebraMapInv_basisSHat, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (∅ : Finset (Fin (2 * n)))]
  · simp only [Finset.sdiff_empty, ite_true, s8_epsSign_empty_left, one_mul,
      Finset.compl_eq_empty_iff]
    split_ifs with h
    · rw [h, Finset.card_univ, Fintype.card_fin, s8_neg_one_pow_top, Finset.compl_univ,
        s8_epsSign_empty_right, mul_one, mul_comm]
    · rfl
  · intro I _ hI
    simp [hI]
  · intro h
    exact absurd (Finset.empty_mem_powerset K) h

/-- The rank of `φ(x ⊗ y)` is `(-1)ⁿ ∫_X x y`. -/
theorem s8_rank_phiOrlov (x y : S F n) :
    rankExt F n (phiOrlov F n (x ⊗ₜ[F] y)) = (-1 : F) ^ n * integral F n (x * y) := by
  conv_lhs => rw [← (basisS F n).sum_repr x, ← (basisS F n).sum_repr y]
  conv_rhs => rw [← (basisS F n).sum_repr x, ← (basisS F n).sum_repr y]
  simp only [sum_tmul, tmul_sum, smul_tmul_smul, map_sum, map_smul, s8_rank_phiOrlov_basis,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, s8_integral_basisS_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  split_ifs <;> ring

end S8Phi

/-! ## Helpers (prefix `s8_`): base change of `φ`, invariance of `h` -/

section S8BCExt
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s8_bcDual_f (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  change ∑ j, algebraMap F F' (f F n i (e F n j)) • f F' n j = f F' n i
  simp [f, e, Pi.single_apply]

theorem s8_bcV_basisV (k : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n k) = basisV F' n k := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [s61_basisV_castAdd, s61_basisV_castAdd]
    simp [bcV, s8_bcDual_f]
  · rw [s61_basisV_natAdd, s61_basisV_natAdd]
    simp [bcV, s8_bcH1_e]

theorem s8_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) :=
  ExteriorAlgebra.lift_ι_apply F _ _ v

theorem s8_bcExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcV F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp [s8_bcExt_ι]

theorem s8_bcExt_basisExt (M : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n M) = basisExt F' n M := by
  rw [s61_basisExt_eq_ιMulti' F n M rfl, s61_basisExt_eq_ιMulti' F' n M rfl, s8_bcExt_ιMulti]
  congr 1
  funext i
  exact s8_bcV_basisV F F' n _

omit [CharZero F] [CharZero F'] in
theorem s8_epsSign_bc (K L : Finset (Fin (2 * n))) :
    epsSign F' n K L = algebraMap F F' (epsSign F n K L) := by
  rw [epsSign, epsSign, ← s8_bcS_basisS F F', ← s8_bcS_basisS F F', ← map_mul, s8_repr_bcS]

theorem s8_bcExt_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    bcExt F F' n (phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L)) =
      phiOrlov F' n (basisS F' n K ⊗ₜ[F'] basisS F' n L) := by
  rw [s8_phiOrlov_basis, s8_phiOrlov_basis, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_smul, map_mul, s61_pullX_basisS, s61_pullXHat_basisSHat, s8_bcExt_basisExt,
    s8_bcExt_basisExt, ← s61_pullX_basisS, ← s61_pullXHat_basisSHat, ← algebraMap_smul F']
  congr 1
  simp only [map_mul, map_pow, map_neg, map_one, s8_epsSign_bc F F']

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_eq_sum (x : S F n) :
    bcS F F' n x = ∑ K, algebraMap F F' ((basisS F n).repr x K) • basisS F' n K := by
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [map_smul, s8_bcS_basisS, algebraMap_smul]

/-- Base change of Orlov's `φ`. -/
theorem s8_bcExt_phiOrlov (x y : S F n) :
    bcExt F F' n (phiOrlov F n (x ⊗ₜ[F] y)) =
      phiOrlov F' n (bcS F F' n x ⊗ₜ[F'] bcS F F' n y) := by
  conv_lhs => rw [← (basisS F n).sum_repr x, ← (basisS F n).sum_repr y]
  rw [s8_bcS_eq_sum, s8_bcS_eq_sum]
  simp only [sum_tmul, tmul_sum, smul_tmul_smul, map_sum, map_smul, s8_bcExt_phiOrlov_basis]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  rw [← algebraMap_smul F', map_mul]

theorem s8_tau_bcS (x : S F n) : tau F' n (bcS F F' n x) = bcS F F' n (tau F n x) :=
  (s8_bcS_tau x).symm

theorem s8_algebraMapInv_bcExt (x : ExtV F n) :
    ExteriorAlgebra.algebraMapInv (bcExt F F' n x) =
      algebraMap F F' (ExteriorAlgebra.algebraMapInv x) := by
  have h : ((ExteriorAlgebra.algebraMapInv : ExtV F' n →ₐ[F'] F').restrictScalars F).comp
      (bcExt F F' n) = (Algebra.ofId F F').comp ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [s8_bcExt_ι, ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun h x

end S8BCExt

section S8Inv

variable {n : ℕ} {d : ℚ}

/-- `ρ(Spin(V_ℚ)_P)` commutes with `f = η_{√-d}` (Lemma 2.2.4, `f ∈ Õ(V_ℚ)`). -/
theorem s8_fη_rho (P : KSecant n d) (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) (v : V ℚ n) :
    P.fη hW (rho ℚ n g v) = rho ℚ n g (P.fη hW v) := by
  obtain ⟨g', -, hfg⟩ := P.fη_mem_Otilde hW
  have h := ((lemma2_2_4 P hd hn hP g').mpr
    ⟨Kd.sqrtNeg d, s8_sqrtNeg_ne_zero hd, hfg⟩).2 g hg
  have hv := congrArg (fun A : V ℚ n ≃ₗ[ℚ] V ℚ n => A v) h
  simp only [LinearEquiv.mul_apply] at hv
  rw [← hfg]
  exact hv

/-- `Ξ_P` is `Spin(V_ℚ)_P`-invariant. -/
theorem s8_XiQ_rho (P : KSecant n d) (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) (x y : V ℚ n) :
    P.XiQ hW (rho ℚ n g x) (rho ℚ n g y) = P.XiQ hW x y := by
  simp only [KSecant.XiQ, LinearMap.BilinForm.compLeft_apply]
  rw [s8_fη_rho P hd hn hP hW g hg, s61_pairing_rho]

/-- `⟪ρ_g ξ, x ∧ y⟫ = ⟪ξ, ρ_g⁻¹x ∧ ρ_g⁻¹y⟫`. -/
theorem s8_ev2_rhoExt (F : Type*) [Field F] [CharZero F] (g : Spin F n) (ξ : ExtV F n)
    (x y : V F n) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
        (contractLeft (Q := 0) (pairing F n x) (rhoExt F n g ξ))) =
      ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n ((rho F n g).symm y))
        (contractLeft (Q := 0) (pairing F n ((rho F n g).symm x)) ξ)) := by
  have hp : ∀ z : V F n, pairing F n z ∘ₗ (rho F n g : V F n →ₗ[F] V F n) =
      pairing F n ((rho F n g).symm z) := by
    intro z
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    conv_lhs => rw [← (rho F n g).apply_symm_apply z]
    exact s61_pairing_rho F n g _ _
  rw [rhoExt, s8_contractLeft_map, hp, s8_contractLeft_map, hp, s8_algebraMapInv_map]

/-- A `2`-vector `ξ` with `⟪ξ, x ∧ y⟫ = 0` for all `x, y` is zero. -/
theorem s8_eq_zero_of_ev2 (F : Type*) [Field F] [CharZero F] {ξ : ExtV F n}
    (hξ : ξ ∈ ⋀[F]^2 (V F n))
    (h : ∀ x y : V F n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
        (contractLeft (Q := 0) (pairing F n x) ξ)) = 0) : ξ = 0 := by
  -- every functional on `V` is `(y, ·)_V`
  have hsurj : ∀ φ : Module.Dual F (V F n), ∃ y : V F n, pairing F n y = φ := by
    intro φ
    refine ⟨(φ ∘ₗ LinearMap.inr F _ _, ∑ i, φ (f F n i, 0) • e F n i), ?_⟩
    refine LinearMap.ext fun z => ?_
    rw [s8_pairing_apply]
    have hz : z = (z.1, 0) + (0, z.2) := by simp
    conv_rhs => rw [hz, map_add]
    rw [add_comm]
    congr 1
    conv_rhs => rw [s8_dual_eq_sum F n z.1]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [show ((∑ i, z.1 (e F n i) • f F n i, (0 : H1 F n)) : V F n) =
        ∑ i, z.1 (e F n i) • ((f F n i, 0) : V F n) by
          ext1 <;> simp [Prod.fst_sum, Prod.snd_sum], map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  have h1 : ∀ x : V F n, contractLeft (Q := 0) (pairing F n x) ξ = 0 := by
    intro x
    have hη : contractLeft (Q := 0) (pairing F n x) ξ ∈ ⋀[F]^1 (V F n) := s8_contractLeft_mem _ hξ
    refine s8_eq_zero_of_contractLeft (basisV F n) one_pos hη fun φ => ?_
    obtain ⟨y, rfl⟩ := hsurj φ
    have h0 := s8_contractLeft_mem (pairing F n y) hη
    rw [s8_eq_algebraMap_of_mem_zero h0, h x y, map_zero]
  refine s8_eq_zero_of_contractLeft (basisV F n) two_pos hξ fun φ => ?_
  obtain ⟨x, rfl⟩ := hsurj φ
  exact h1 x

/-- `h = Ξ_P^♯` is `Spin(V_ℚ)_P`-invariant. -/
theorem s8_rhoExt_hClass (P : KSecant n d) (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) :
    rhoExt ℚ n g (P.hClass hW) = P.hClass hW := by
  have hmem : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  rw [← sub_eq_zero]
  refine s8_eq_zero_of_ev2 ℚ (sub_mem (s61_rhoExt_mem ℚ n g hmem) hmem) fun x y => ?_
  rw [map_sub, map_sub, map_sub, s8_ev2_rhoExt, KSecant.hClass_spec, KSecant.hClass_spec,
    ← s8_XiQ_rho P hd hn hP hW g hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    sub_self]


/-- `x = Σ_{k ≤ 4n} x_k` (the graded pieces of `⋀• V`). -/
theorem s8_eq_sum_projDeg (F : Type*) [Field F] [CharZero F] (x : ExtV F n) :
    x = ∑ k ∈ Finset.range (4 * n + 1), projDeg F n k x := by
  conv_lhs => rw [← (basisExt F n).sum_repr x]
  conv_rhs => rw [← (basisExt F n).sum_repr x]
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  have hM : basisExt F n M ∈ ⋀[F]^M.card (V F n) := s61_basis_mem _ M
  have hcard : M.card < 4 * n + 1 := by
    have := M.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  rw [Finset.sum_eq_single M.card]
  · rw [s61_projDeg_of_mem F n hM]
  · intro k _ hk
    rw [s61_projDeg_of_mem_ne F n (Ne.symm hk) hM, smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hcard) h

end S8Inv

/-! ## Helpers (prefix `s8_`): weights -/

section S8Weight

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- Classes in `F_k = ⊕_{i ≥ k} ⋀^i V`, `k > 0`, have rank `0`. -/
theorem s8_rank_eq_zero_of_mem_extFiltGE {k : ℕ} (hk : 0 < k) {x : ExtV F n}
    (hx : x ∈ extFiltGE F n k) : rankExt F n x = 0 :=
  s61_extFiltGE_induction F n (P := fun y => rankExt F n y = 0) (map_zero _)
    (fun y z hy hz => by rw [map_add, hy, hz, add_zero])
    (fun i hi y hy => s8_algebraMapInv_eq_zero_of_mem (by omega) hy) hx

/-- A class of rank `0` lies in `F_1 = ⊕_{i ≥ 1} ⋀^i V`. -/
theorem s8_mem_extFiltGE_one_of_rank {x : ExtV F n} (hx : rankExt F n x = 0) :
    x ∈ extFiltGE F n 1 := by
  have hdec := s8_eq_sum_projDeg F x
  have h0 : projDeg F n 0 x = 0 := by
    have hmem : projDeg F n 0 x ∈ ⋀[F]^0 (V F n) := by
      rw [projDeg, GradedAlgebra.proj_apply]
      exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x 0).2
    rw [s8_eq_algebraMap_of_mem_zero hmem]
    have hr : ExteriorAlgebra.algebraMapInv (projDeg F n 0 x) = rankExt F n x := by
      conv_rhs => rw [hdec]
      rw [rankExt, map_sum, Finset.sum_eq_single 0]
      · intro k _ hk
        refine s8_algebraMapInv_eq_zero_of_mem (Nat.pos_of_ne_zero hk) ?_
        rw [projDeg, GradedAlgebra.proj_apply]
        exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x k).2
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
    rw [hr, hx, map_zero]
  rw [hdec, Finset.sum_range_succ', h0, add_zero]
  refine Submodule.sum_mem _ fun k _ => s61_mem_extFiltGE F n (by omega : 1 ≤ k + 1) ?_
  rw [projDeg, GradedAlgebra.proj_apply]
  exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x (k + 1)).2

end S8Weight

/-! ## Helpers (prefix `s8_`): `λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂` is not `Spin(V_K)_{ℓ₁,ℓ₂}`-invariant -/

section S8HW

variable {n : ℕ} {d : ℚ}

/-- (Proof of Lemma 8.3.1, TeX line 4021) For `P` as in §6.4 (Assumption 2.4.1),
`λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂ ∈ HW_{P_K} = ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}` (`λᵢ = uᵢ`) is not
`Spin(V_K)_{ℓ₁,ℓ₂}`-invariant, "by Lemma 2.2.7 and Proposition 6.4.1(1)". By Proposition 6.4.1(1)
(`proposition6_4_1_1_line₁/₂`), `φ'` maps it into `F_{2n} = ⊕_{k ≥ 2n} H^k(X × X̂, K)`, with
projection `v₁ + v₂` to `H^{2n}`, `vᵢ` spanning `⋀^{2n} Wᵢ`, a line (Lemma 2.2.7,
`lemma2_2_7_K_finrank`). If it were invariant, `ρ'_g` would fix its image (`φ'` intertwines
`m_g ⊗ m_g` with `ρ'_g`, (6.1.4)), so `ρ_g` would fix `v₁ + v₂` (`ρ'_g` induces `ρ_g` on the graded
pieces, `rhoPrime_projDeg`). But `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `⋀^{2n} Wᵢ` by `detᵢ` and
`⋀^{2n} W₁ ⊕ ⋀^{2n} W₂` is direct (Lemma 2.2.7, `lemma2_2_7_K_det₁/₂`, `lemma2_2_7_K_indep`), and
`det₁` is non-trivial (§6.4, TeX line 2860, `exists_det₁_ne`). -/
theorem s8_HW_not_invariant (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hA : Assumption2_4_1 P J) :
    ¬ ∀ g : P.spinL₁L₂, TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (P.u₁ ⊗ₜ[Kd d] P.u₁ + P.u₂ ⊗ₜ[Kd d] P.u₂) = P.u₁ ⊗ₜ[Kd d] P.u₁ + P.u₂ ⊗ₜ[Kd d] P.u₂ := by
  intro hinv
  have hd := hA.pos
  have hP := hA.nonIsotropic
  -- Proposition 6.4.1(1): `φ'(λᵢ ⊠ λᵢ) ∈ F_{2n}`, with projection `vᵢ` spanning `⋀^{2n} Wᵢ`
  obtain ⟨hF₁, hproj₁⟩ := proposition6_4_1_1_line₁ P J hA
  obtain ⟨hF₂, hproj₂⟩ := proposition6_4_1_1_line₂ P J hA
  obtain ⟨v₁, hv₁def⟩ : ∃ v, v = projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁)) :=
    ⟨_, rfl⟩
  obtain ⟨v₂, hv₂def⟩ : ∃ v, v = projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)) :=
    ⟨_, rfl⟩
  have hv₁ : v₁ ∈ pqPiece P.W₁ P.W₂ (2 * n) 0 := by
    rw [hv₁def, s62_pqPiece_zero_right, ← hproj₁]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  have hv₂ : v₂ ∈ pqPiece P.W₁ P.W₂ 0 (2 * n) := by
    rw [hv₂def, s62_pqPiece_zero_left, ← hproj₂]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  -- `v₁ ≠ 0`: `⋀^{2n} W₁ = span{v₁}` is a line (Lemma 2.2.7)
  have hv₁0 : v₁ ≠ 0 := by
    have hspan : Submodule.span (Kd d) {v₁} = pqPiece P.W₁ P.W₂ (2 * n) 0 := by
      rw [s62_pqPiece_zero_right, ← hproj₁, Submodule.map_span, Set.image_singleton, hv₁def]
    intro h0
    have h1 := (lemma2_2_7_K_finrank P hd hP).1
    rw [← hspan, h0, Submodule.span_zero_singleton, finrank_bot] at h1
    exact zero_ne_one h1
  -- `g` with `det₁ g ≠ 1` (§6.4: `ℓ̃₁^{⊗2}` is a non-trivial character)
  obtain ⟨g, hg⟩ := (P.exists_det₁_ne hd hP).1
  -- `ρ'_g` fixes `φ'(λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂)`, so `ρ_g` fixes its projection `v₁ + v₂` to `H^{2n}`
  have hmemF : phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁ + P.u₂ ⊗ₜ[Kd d] P.u₂) ∈
      extFiltGE (Kd d) n (2 * n) := by
    rw [map_add]; exact add_mem hF₁ hF₂
  have hfix := rhoPrime_projDeg (Kd d) n (g : Spin (Kd d) n) (2 * n) hmemF
  rw [← s62_phiPrime_map, hinv g, map_add, map_add, map_add, ← hv₁def, ← hv₂def,
    lemma2_2_7_K_det₁ P hd hP g v₁ hv₁, lemma2_2_7_K_det₂ P hd hP g v₂ hv₂] at hfix
  -- `(det₁ g - 1) v₁ + (det₂ g - 1) v₂ = 0` in `⋀^{2n} W₁ ⊕ ⋀^{2n} W₂`
  have key : (P.det₁ g - 1) • v₁ + (P.det₂ g - 1) • v₂ = 0 :=
    calc (P.det₁ g - 1) • v₁ + (P.det₂ g - 1) • v₂
        = (P.det₁ g • v₁ + P.det₂ g • v₂) - (v₁ + v₂) := by module
      _ = 0 := by rw [← hfix, sub_self]
  have h0 := (s62_indep_three (lemma2_2_7_K_indep P hd hP) (i := 0) (j := 1) (by decide)
    (Submodule.smul_mem _ _ hv₁) (Submodule.smul_mem _ _ hv₂) key).1
  exact hg (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv₁0))

end S8HW

/-! ## Lemma 8.3.1 -/

section Lemma831

variable {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d)

/-- (Proof of Lemma 8.3.1, TeX lines 3980–3983) `ch(Φ(F₁ ⊠ F₁)) = φ(ch F₁ ⊠ ch F₁) =
φ'(ch F₁ ⊠ τ(ch F₁))`, `φ' = φ ∘ (id ⊗ τ)` (the first equality, GRR, is the model's definition of the
Chern character of `Φ(F₁ ⊠ F₁)`). -/
theorem lemma8_3_1_ch :
    phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) = phiPrime ℚ 3 (chF1 d ⊗ₜ[ℚ] tau ℚ 3 (chF1 d)) := by
  simp [phiPrime, tauTensor, tau_tau]

/-- (Proof of Lemma 8.3.1, TeX lines 3984–3988) `ch(F₁) = ½[(λ₁ + λ₂) + (λ₁ - λ₂)/√-d]` in
`H^{ev}(X, K)`, `λ₁ = exp(√-dΘ)`, `λ₂ = λ̄₁`. -/
theorem chF1_eq_lambda :
    bcS ℚ (Kd d) 3 (chF1 d) =
      (2 : Kd d)⁻¹ • ((PJac d hΘ hd).u₁ + (PJac d hΘ hd).u₂ +
        (Kd.sqrtNeg d)⁻¹ • ((PJac d hΘ hd).u₁ - (PJac d hΘ hd).u₂)) := by
  -- `λ₁ = α + √-d β`, `λ₂ = α - √-d β`, `ch(F₁) = α + β`
  have hs := s8_sqrtNeg_ne_zero hd
  rw [s8_PJac_u₁ d hΘ hd, s8_PJac_u₂ d hΘ hd, (lemma8_2_1 d hΘ hd).1, map_add]
  set A := bcS ℚ (Kd d) 3 (alphaJac d)
  set B := bcS ℚ (Kd d) 3 (betaJac d)
  set s := Kd.sqrtNeg d
  have h : s⁻¹ • (A + s • B - (A + (-s) • B)) = (2 : Kd d) • B := by
    rw [show A + s • B - (A + (-s) • B) = (2 * s) • B by module, smul_smul]
    congr 1
    field_simp
  rw [h, show A + s • B + (A + (-s) • B) + (2 : Kd d) • B = (2 : Kd d) • (A + B) by module,
    smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- (Proof of Lemma 8.3.1, TeX line 3989) "`τ` interchanges `λ₁` and `λ₂`". -/
theorem tau_lambda :
    tau (Kd d) 3 (PJac d hΘ hd).u₁ = (PJac d hΘ hd).u₂ ∧
      tau (Kd d) 3 (PJac d hΘ hd).u₂ = (PJac d hΘ hd).u₁ := by
  -- `τ(exp u) = exp(τ u) = exp(-u)` for `u ∈ H²`
  have hu : uΘ 3 d (ThetaStd ℚ 3) ∈ ⋀[Kd d]^2 (H1 (Kd d) 3) :=
    uΘ_mem 3 d _ (s8_ThetaStd_mem ℚ 3)
  have h1 : (PJac d hΘ hd).u₁ = IsNilpotent.exp (uΘ 3 d (ThetaStd ℚ 3)) := rfl
  have h2 : (PJac d hΘ hd).u₂ = IsNilpotent.exp (-uΘ 3 d (ThetaStd ℚ 3)) := by
    rw [PJac, PTheta_u₂]
  refine ⟨?_, ?_⟩
  · rw [h1, h2, s8_tau_exp (Kd d) 3 hu]
  · rw [h1, h2, s8_tau_exp (Kd d) 3 (neg_mem hu), neg_neg]

/-- (Proof of Lemma 8.3.1, TeX lines 3990–4009) In `H^{ev}(X × X, K) = S_K ⊗ S_K`:
`ch(F₁) ⊠ τ(ch F₁) = ((d+1)/(4d)) [λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂] + ((d-1)/(4d)) [λ₁ ⊠ λ₂ + λ₂ ⊠ λ₁]
+ (√-d/(2d)) [λ₂ ⊠ λ₁ - λ₁ ⊠ λ₂]`. -/
theorem chF1_tmul_tau_decomp :
    bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)) =
      ((d + 1) / (4 * d) : ℚ) • ((PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ +
          (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂) +
        ((d - 1) / (4 * d) : ℚ) • ((PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ +
          (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁) +
        (Kd.sqrtNeg d / (2 * (d : Kd d))) • ((PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ -
          (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂) := by
  have hs := s8_sqrtNeg_mul_self hd.le
  have hs0 := s8_sqrtNeg_ne_zero hd
  have hd0 : (algebraMap ℚ (Kd d) d) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective]; exact hd.ne'
  have hu₁ := s8_PJac_u₁ d hΘ hd
  have hu₂ := s8_PJac_u₂ d hΘ hd
  set u₁ := (PJac d hΘ hd).u₁
  set u₂ := (PJac d hΘ hd).u₂
  set s := Kd.sqrtNeg d
  -- `ch(F₁) = α + β`, `τ(ch F₁) = α - β`, `α = (λ₁ + λ₂)/2`, `β = (λ₁ - λ₂)/(2√-d)`
  rw [s8_tau_chF1, (lemma8_2_1 d hΘ hd).1, map_add, map_sub]
  set A := bcS ℚ (Kd d) 3 (alphaJac d)
  set B := bcS ℚ (Kd d) 3 (betaJac d)
  have hA : A = (2 : Kd d)⁻¹ • (u₁ + u₂) := by rw [hu₁, hu₂]; module
  have hB : B = (2 * s)⁻¹ • (u₁ - u₂) := by
    rw [hu₁, hu₂, show A + s • B - (A + (-s) • B) = (2 * s) • B by module, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero hs0), one_smul]
  rw [hA, hB]
  simp only [← algebraMap_smul (Kd d) ((d + 1) / (4 * d) : ℚ),
    ← algebraMap_smul (Kd d) ((d - 1) / (4 * d) : ℚ)]
  simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, ← smul_tmul', tmul_smul, smul_add, smul_sub,
    smul_smul]
  have hcast : (d : Kd d) = algebraMap ℚ (Kd d) d := rfl
  simp only [map_div₀, map_add, map_sub, map_mul, map_one, map_ofNat, hcast]
  rw [map_neg] at hs
  have hs' : s * s = -(d : Kd d) := by rw [hcast]; exact hs
  -- compare the coefficients of `λᵢ ⊠ λⱼ`, using `(√-d)² = -d`
  match_scalars <;> field_simp
  · linear_combination (-4 : Kd d) * hs'
  · linear_combination (4 - 8 * s) * hs'
  · linear_combination (4 + 8 * s) * hs'
  · linear_combination (-4 : Kd d) * hs'

/-- `rank φ(w ⊗ w) = 8d` for `w = ch(F₁)` (`rank φ(x ⊗ y) = (-1)ⁿ ∫_X x y`). -/
theorem s8_rank_chF1 : rankExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = 8 * d := by
  -- `rank φ(w ⊗ w) = -∫_X w²` and `∫_X w² = -8d` (`Θ³ = 6[pt]`, `Θ⁴ = 0`)
  have hT := s8_ThetaStd_mem ℚ 3
  have h4 : ThetaStd ℚ 3 ^ 4 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have h5 : ThetaStd ℚ 3 ^ 5 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have h6 : ThetaStd ℚ 3 ^ 6 = 0 := s8_Theta_pow_eq_zero ℚ (by norm_num)
  have hI0 : integral ℚ 3 (1 : S ℚ 3) = 0 :=
    s8_integral_eq_zero_of_mem ℚ 3 (by norm_num : (0 : ℕ) ≠ 2 * 3) SetLike.GradedOne.one_mem
  have hI1 : integral ℚ 3 (ThetaStd ℚ 3) = 0 :=
    s8_integral_eq_zero_of_mem ℚ 3 (by norm_num : (2 : ℕ) ≠ 2 * 3) hT
  have hI2 : integral ℚ 3 (ThetaStd ℚ 3 ^ 2) = 0 :=
    s8_integral_eq_zero_of_mem ℚ 3 (by norm_num : (2 * 2 : ℕ) ≠ 2 * 3) (s8_pow_mem ℚ 3 hT 2)
  have hI3 : integral ℚ 3 (ThetaStd ℚ 3 ^ 3) = 6 := by
    rw [s8_Theta_cube, map_smul, s8_integral_pt, smul_eq_mul, mul_one]
  rw [s8_rank_phiOrlov, chF1, s8_pt_three]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  have hTT : ThetaStd ℚ 3 * ThetaStd ℚ 3 = ThetaStd ℚ 3 ^ 2 := (pow_two _).symm
  simp only [hTT, ← pow_succ, ← pow_succ', ← pow_add, Nat.reduceAdd, h4, h5, h6, smul_zero,
    sub_zero, add_zero]
  simp only [map_add, map_sub, map_smul, hI0, hI1, hI2, hI3, smul_eq_mul]
  ring

/-- **Lemma 8.3.1** (`lemma-kappa-3-is-linearly-independent-from-h-cube`), first sentence: the rank
of `Φ(F₁ ⊠ F₁)` is non-zero. Model: the rank is the degree-`0` coefficient of
`ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w)`, `w = chF1 d`; `d > 0` (the paper: a positive integer). -/
theorem lemma8_3_1_rank (hd : 0 < d) : rankExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) ≠ 0 := by
  -- the setting of §6.4 for `P = P_Θ`: a complex structure `J₀` for which `Θ` is ample
  -- (Assumption 2.4.1); the paper's `X` is a Jacobian, any such `X` gives the same `P`
  have hΘ₀ := s8_ample_J0 3
  have hA := PJac_assumption2_4_1 d (s8_J0_isComplex 3) hΘ₀ hd
  set P := PJac d hΘ₀ hd
  -- over `K`: `φ'(ch F₁ ⊠ τ ch F₁)` in terms of `λ₁ = u₁`, `λ₂ = u₂`
  have hbc : bcExt ℚ (Kd d) 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = phiPrime (Kd d) 3
      (bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d))) := by
    rw [s8_bcExt_phiOrlov, phiPrime, LinearMap.comp_apply, tauTensor, TensorProduct.map_tmul,
      LinearMap.id_apply, s8_tau_bcS, tau_tau]
  rw [chF1_tmul_tau_decomp d hΘ₀ hd] at hbc
  -- Proposition 6.4.1: `φ'(λᵢ ⊠ λᵢ) ∈ F_6`, `φ'(λ₁λ₂)` has weight `2`, `φ'(λ₁ ∧ λ₂)` weight `0`
  have h1 : rankExt (Kd d) 3 (phiPrime (Kd d) 3 (P.u₁ ⊗ₜ[Kd d] P.u₁)) = 0 :=
    s8_rank_eq_zero_of_mem_extFiltGE _ 3 (by norm_num)
      (proposition6_4_1_1_line₁ P (s8_J0 3) hA).1
  have h2 : rankExt (Kd d) 3 (phiPrime (Kd d) 3 (P.u₂ ⊗ₜ[Kd d] P.u₂)) = 0 :=
    s8_rank_eq_zero_of_mem_extFiltGE _ 3 (by norm_num)
      (proposition6_4_1_1_line₂ P (s8_J0 3) hA).1
  obtain ⟨hw2, hw0⟩ := proposition6_4_1_2_odd P (s8_J0 3) hA (by decide)
  have h3 : rankExt (Kd d) 3
      (phiPrime (Kd d) 3 (P.u₁ ⊗ₜ[Kd d] P.u₂ + P.u₂ ⊗ₜ[Kd d] P.u₁)) = 0 :=
    s8_rank_eq_zero_of_mem_extFiltGE _ 3 (by norm_num)
      (hw2.1 (Submodule.mem_span_singleton_self _))
  have h4 : rankExt (Kd d) 3
      (phiPrime (Kd d) 3 (P.u₁ ⊗ₜ[Kd d] P.u₂ - P.u₂ ⊗ₜ[Kd d] P.u₁)) ≠ 0 := by
    intro h
    exact hw0.2 ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (s8_mem_extFiltGE_one_of_rank _ 3 h))
  -- the rank is the coefficient of `λ₂ ⊠ λ₁ - λ₁ ⊠ λ₂` times a non-zero number
  intro h0
  have hK := congrArg (rankExt (Kd d) 3) hbc
  simp only [rankExt] at hK h0 h1 h2 h3 h4
  rw [s8_algebraMapInv_bcExt, h0, map_zero] at hK
  simp only [map_add, map_sub, map_smul, map_rat_smul] at hK h3 h4
  rw [h1, h2, h3, add_zero, smul_zero, smul_zero, zero_add, zero_add, smul_eq_mul] at hK
  have hc : Kd.sqrtNeg d / (2 * (d : Kd d)) ≠ 0 := by
    have hd0 : (d : Kd d) ≠ 0 := by exact_mod_cast hd.ne'
    exact div_ne_zero (s8_sqrtNeg_ne_zero hd) (mul_ne_zero two_ne_zero hd0)
  have h5 := (mul_eq_zero.mp hK.symm).resolve_left hc
  apply h4
  linear_combination -h5

/-- The rank of `Φ(F₁ ⊠ F₁)` is `8d` (the rank of the sheaf `E` of Theorem 1.4.1(2); checked
numerically for `d = 1, 2, 3, 5, 7`). -/
theorem lemma8_3_1_rank_eq : rankExt ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = 8 * d :=
  s8_rank_chF1 d

/-- `ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ τ(τ w))` is `ρ'`-invariant under `Spin(V)_P` (Lemma 6.2.3; `w, τ w ∈ P`). -/
theorem s8_rhoPrime_invariant (g : Spin ℚ 3) (hg : g ∈ (PJac d hΘ hd).spinPZ) :
    rhoPrime ℚ 3 g (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) := by
  have h := lemma6_2_3_rhoPrime_invariant (PJac d hΘ hd) (tau ℚ 3 (chF1 d)) (chF1 d)
    (lemma8_2_1 d hΘ hd).2.2 (lemma8_2_1 d hΘ hd).2.1 g hg
  have h2 : secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d)) =
      phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) := by
    rw [secantSqClass, tau_tau]
  rw [h2] at h
  exact h

/-- `κ(Φ(F₁ ⊠ F₁))` is `Spin(V)_P`-invariant, by Corollary 1.3.2 (`corollary1_3_2`):
`Φ(F₁ ⊠ F₁) = Φ(F₁ ⊠ F₂^∨)` for `F₂ = F₁^∨` is a `P`-secant`^{⊠2}`-object (`ch F₁ = w` and
`ch F₂ = τ w` lie in `P` by Lemma 8.2.1, and `φ(w ⊗ τ(τ w)) = φ(w ⊗ w)`), of non-zero rank by the
first sentence of Lemma 8.3.1 (`lemma8_3_1_rank`). -/
theorem s8_kappa_invariant (g : Spin ℚ 3) (hg : g ∈ (PJac d hΘ hd).spinPZ) :
    rhoExt ℚ 3 g (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) =
      kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) := by
  have hE : secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d)) =
      phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) := by
    rw [secantSqClass, tau_tau]
  have hr : rankExt ℚ 3 (secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d))) ≠ 0 := by
    rw [hE]; exact lemma8_3_1_rank d hd
  have h := corollary1_3_2 (PJac d hΘ hd) (chF1 d) (tau ℚ 3 (chF1 d)) (lemma8_2_1 d hΘ hd).2.1
    (lemma8_2_1 d hΘ hd).2.2 hr g hg
  rwa [hE] at h

/-- (Lemma 8.3.1, "the `Spin(V)_P`-invariant classes `h³` and `κ₃(Φ(F₁ ⊠ F₁))`") Both classes are
invariant under the integral group `Spin(V)_P` acting by `ρ` (for `κ₃`: Corollary 1.3.2, as
`w ⊗ w = w ⊗ τ(τ w)` with `w, τ w ∈ P`). -/
theorem lemma8_3_1_invariant :
    (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 ∈ invariantsExt ℚ 3 (PJac d hΘ hd).spinPZ ∧
      kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) ∈
        invariantsExt ℚ 3 (PJac d hΘ hd).spinPZ := by
  have hP := PJac_not_isIsotropic d hΘ hd
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · -- `h` is invariant (`Ξ_P` is, Lemma 2.2.4), hence so is `h³`
    rw [map_pow, s8_rhoExt_hClass _ hd (by norm_num) hP _ g (Subgroup.mem_inf.mp hg).2]
  · -- `κ₃` is a graded piece of `κ`, which is invariant (Corollary 1.3.2)
    change rhoExt ℚ 3 g (projDeg ℚ 3 (2 * 3) _) = projDeg ℚ 3 (2 * 3) _
    rw [← s61_projDeg_rhoExt, s8_kappa_invariant d hΘ hd g hg]

/-- `h = Ξ_P^♯` lies in `(⋀² V_ℚ)^{Spin(V)_P}`, and `h³ ≠ 0` (Lemma 2.2.7, note: `h⁶ ≠ 0`). -/
theorem s8_hClass_props :
    (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ∈ (PJac d hΘ hd).invQ 2 ∧
      (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 ≠ 0 := by
  have hP := PJac_not_isIsotropic d hΘ hd
  have hW := PJac_isCompl d hΘ hd
  have hh : (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ∈ (PJac d hΘ hd).invQ 2 :=
    ⟨formToExt2_mem ℚ 3 _, fun g hg =>
      s8_rhoExt_hClass _ hd (by norm_num) hP _ g (Subgroup.mem_inf.mp hg).2⟩
  have hh0 : (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ≠ 0 := by
    intro h0
    have hv : ((0 : Module.Dual ℚ (H1 ℚ 3)), e ℚ 3 0) = (0 : V ℚ 3) := by
      refine ((PJac d hΘ hd).XiQ_nondegenerate hW).1 _ fun y => ?_
      rw [← KSecant.hClass_spec, h0, map_zero, map_zero, map_zero]
    have := congrArg (fun v : V ℚ 3 => v.2 0) hv
    simp [e] at this
  refine ⟨hh, fun h3 => (lemma2_2_7_note _ hd (by norm_num) hP _ hh hh0).1 ?_⟩
  have h33 : (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ (2 * 3) =
      (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 *
        (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 := by
    rw [← pow_add]
  rw [h33, h3, zero_mul]

/-- (Proof of Lemma 8.3.1) If `κ₃ = c h³`, then `κ(Φ(F₁ ⊠ F₁))` lies in the subring generated by
`h` (Lemma 2.2.7), hence is `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ`-invariant (Lemma 2.2.7). -/
theorem s8_kappa_K_invariant (c : ℚ)
    (hc : kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) =
      c • (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3)
    (g : Spin (Kd d) 3) (hg : g ∈ (PJac d hΘ hd).spinL₁L₂) :
    rhoExt (Kd d) 3 g (bcExt ℚ (Kd d) 3 (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)))) =
      bcExt ℚ (Kd d) 3 (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) := by
  have hP := PJac_not_isIsotropic d hΘ hd
  have hh := (s8_hClass_props d hΘ hd).1
  have hhK : rhoExt (Kd d) 3 g (bcExt ℚ (Kd d) 3 ((PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd))) =
      bcExt ℚ (Kd d) 3 ((PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd)) :=
    lemma2_2_7_trivial _ hd hP 1 (by norm_num) (by norm_num) _ hh ⟨g, hg⟩
  rw [s8_eq_sum_projDeg ℚ (kappa ℚ 3 _), map_sum, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk13 : k < 13 := Finset.mem_range.mp hk
  have hmem : projDeg ℚ 3 k (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) ∈
      (PJac d hΘ hd).invQ k := by
    refine ⟨?_, fun g' hg' => ?_⟩
    · rw [projDeg, GradedAlgebra.proj_apply]
      exact (DirectSum.decompose (fun i : ℕ => ⋀[ℚ]^i (V ℚ 3)) _ k).2
    · rw [← s61_projDeg_rhoExt, s8_kappa_invariant d hΘ hd g' hg']
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
  · by_cases hj3 : j = 3
    · subst hj3
      have h6 : projDeg ℚ 3 (3 + 3) (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) =
          c • (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 := hc
      rw [h6, map_smul, map_pow, map_rat_smul, map_pow, hhK]
    · rw [show j + j = 2 * j by ring] at hmem ⊢
      exact lemma2_2_7_trivial _ hd hP j hj3 (by omega) _ hmem ⟨g, hg⟩
  · have : Module.Finite ℚ (ExtV ℚ 3) := Module.Finite.of_basis (basisExt ℚ 3)
    have h0 := lemma2_2_7_odd _ hd hP k hodd
    rw [Submodule.finrank_eq_zero] at h0
    rw [h0] at hmem
    rw [(Submodule.mem_bot ℚ).mp hmem, map_zero, map_zero]

/-- (Proof of Lemma 8.3.1) If `ch(Φ(F₁ ⊠ F₁))` is `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ'`-invariant, then
`ch(F₁) ⊠ τ(ch F₁)` is invariant under `m_g ⊗ m_g` (`φ' = φ ∘ (id ⊗ τ)` is `ρ'`-equivariant). -/
theorem s8_tensor_invariant (g : Spin (Kd d) 3)
    (hg : rhoPrime (Kd d) 3 g (bcExt ℚ (Kd d) 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) =
      bcExt ℚ (Kd d) 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))) :
    TensorProduct.map (m (Kd d) 3 (g : C (Kd d) 3)) (m (Kd d) 3 (g : C (Kd d) 3))
        (bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d))) =
      bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)) := by
  have hbc : bcExt ℚ (Kd d) 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) = phiPrime (Kd d) 3
      (bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d))) := by
    rw [s8_bcExt_phiOrlov, phiPrime, LinearMap.comp_apply, tauTensor, TensorProduct.map_tmul,
      LinearMap.id_apply, s8_tau_bcS, tau_tau]
  have hinv : ∀ z, phiPrimeInv (Kd d) 3 (phiPrime (Kd d) 3 z) = z := fun z => by
    rw [← LinearMap.comp_apply (phiPrimeInv _ _), phiPrimeInv_comp_phiPrime, LinearMap.id_apply]
  rw [hbc, rhoPrime, LinearMap.comp_apply, LinearMap.comp_apply, hinv] at hg
  have hy := congrArg (phiPrimeInv (Kd d) 3) hg
  rwa [hinv, hinv] at hy

/-- (Proof of Lemma 8.3.1, TeX lines 4019–4023) `ch(F₁) ⊠ τ(ch F₁)` is not
`Spin(V_K)_{ℓ₁,ℓ₂}`-invariant. In the decomposition `chF1_tmul_tau_decomp`, the summands
`λ₁ ⊠ λ₂ + λ₂ ⊠ λ₁` and `λ₂ ⊠ λ₁ - λ₁ ⊠ λ₂` are invariant (`map_m_u₁_tmul_u₂`), while the first
summand `λ₁ ⊠ λ₁ + λ₂ ⊠ λ₂` is not, by Lemma 2.2.7 and Proposition 6.4.1(1)
(`s8_HW_not_invariant`, for `P_Θ` with the complex structure `J₀` for which `Θ` is ample:
Assumption 2.4.1); its coefficient `(d+1)/(4d)` is non-zero. -/
theorem s8_not_tensor_invariant :
    ¬ ∀ g : (PJac d hΘ hd).spinL₁L₂,
      TensorProduct.map (m (Kd d) 3 ((g : Spin (Kd d) 3) : C (Kd d) 3))
          (m (Kd d) 3 ((g : Spin (Kd d) 3) : C (Kd d) 3))
          (bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d))) =
        bcS ℚ (Kd d) 3 (chF1 d) ⊗ₜ[Kd d] bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)) := by
  intro hall
  have hP := PJac_not_isIsotropic d hΘ hd
  -- the first summand is not invariant (Lemma 2.2.7, Proposition 6.4.1(1))
  refine s8_HW_not_invariant (PJac d hΘ hd) (s8_J0 3)
    (PJac_assumption2_4_1 d (s8_J0_isComplex 3) (s8_ample_J0 3) hd) fun g => ?_
  -- but it would be, as the other two summands are invariant and its coefficient is non-zero
  have hy := hall g
  rw [chF1_tmul_tau_decomp d hΘ hd] at hy
  have h12 := (PJac d hΘ hd).map_m_u₁_tmul_u₂ hd hP g
  set T := TensorProduct.map (m (Kd d) 3 ((g : Spin (Kd d) 3) : C (Kd d) 3))
    (m (Kd d) 3 ((g : Spin (Kd d) 3) : C (Kd d) 3)) with hT
  set A := (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ +
    (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ with hA
  have hB : T ((PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ +
      (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁) =
      (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ +
        (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ := by
    rw [map_add, h12.1, h12.2]
  have hC : T ((PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ -
      (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂) =
      (PJac d hΘ hd).u₂ ⊗ₜ[Kd d] (PJac d hΘ hd).u₁ -
        (PJac d hΘ hd).u₁ ⊗ₜ[Kd d] (PJac d hΘ hd).u₂ := by
    rw [map_sub, h12.1, h12.2]
  rw [map_add, map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, map_smul, hB,
    hC] at hy
  have hc : ((d + 1) / (4 * d) : ℚ) ≠ 0 := by positivity
  exact smul_right_injective _ hc (add_right_cancel (add_right_cancel hy))

/-- **Lemma 8.3.1** (`lemma-kappa-3-is-linearly-independent-from-h-cube`), second sentence: the
`Spin(V)_P`-invariant classes `h³` and `κ₃(Φ(F₁ ⊠ F₁))` are linearly independent.

Model: `ch(Φ(F₁ ⊠ F₁)) = φ(w ⊗ w)` (`lemma8_3_1_ch`), `κ₃` its `κ`-class in `H⁶(X × X̂, ℚ)`
(`kappaDeg ℚ 3 3`); `h = Ξ_P^♯` (`hClass`; any non-zero class of the invariant line gives the same
statement). (Checked numerically for `d = 1, 2, 3, 5, 7`.) -/
theorem lemma8_3_1 :
    LinearIndependent ℚ
      ![(PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3,
        kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d))] := by
  have hP := PJac_not_isIsotropic d hΘ hd
  obtain ⟨hh, hh3⟩ := s8_hClass_props d hΘ hd
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_contra hne
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := fun ha => hne ⟨ha, rfl⟩
    rw [zero_smul, add_zero] at hab
    exact hh3 ((smul_eq_zero.mp hab).resolve_left ha)
  -- by contradiction: `κ₃ = c h³`
  have hκ3 : kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) =
      (-(a / b)) • (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3 := by
    have h1 : b • kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) =
        -(a • (PJac d hΘ hd).hClass (PJac_isCompl d hΘ hd) ^ 3) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
    rw [← inv_smul_smul₀ hb (kappaDeg ℚ 3 3 _), h1, smul_neg, smul_smul, neg_smul,
      div_eq_inv_mul]
  -- then `κ` is `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ`-invariant, so `ch` is `ρ'`-invariant (Lemma 6.2.6(2))
  have hρ' := (lemma6_2_6_2 (PJac d hΘ hd) hd (by norm_num) hP _ (lemma8_3_1_rank d hd)
    (s8_rhoPrime_invariant d hΘ hd)).mpr (s8_kappa_K_invariant d hΘ hd _ hκ3)
  -- so `ch(F₁) ⊠ τ(ch F₁)` would be invariant, a contradiction
  exact s8_not_tensor_invariant d hΘ hd fun g => s8_tensor_invariant d g (hρ' g g.2)

end Lemma831

end WeilClasses
