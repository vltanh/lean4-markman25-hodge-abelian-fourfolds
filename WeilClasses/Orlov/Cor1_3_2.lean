module

public import WeilClasses.Orlov.Sec6_1
public import WeilClasses.PeriodDomain.SemiHodge
public import WeilClasses.Secant.Defs
public import WeilClasses.PureSpinor.Lemma2_2_7
import WeilClasses.AbelianVariety.Lemmas

/-!
# Corollary 1.3.2: `κ(E)` of a `P`-secant`^{⊠2}`-object is `Spin(V)_P`-invariant

The paper's Corollary 1.3.2 (TeX lines 452–485), in the model of `WeilClasses.Secant.Defs`:
`ch(E) = φ(w₁ ⊗ τ w₂)` (`secantSqClass ℚ n w₁ w₂`) for `E = Φ(F₁ ⊠ F₂^∨)` with `wᵢ = ch(Fᵢ) ∈ P`,
`Spin(V)_P` the integral group of (2.2.2) (`P.spinPZ`) acting on `⋀• V_ℚ` by `ρ`.

* **Corollary 1.3.2** (`corollary1_3_2`: `κ(E)` is `Spin(V)_P`-invariant; `corollary1_3_2_hodge`:
  hence it remains of Hodge type on the period domain `Ω_P`), and the invariance over every field
  `F` of characteristic `0` (`corollary1_3_2_field`: for `g ∈ Spin(V_F)` fixing `w₁` and `w₂`;
  `corollary1_3_2_baseChange`: for `Spin(V_F)_P`).

The paper's proof (TeX lines 463–485) uses Proposition 6.1.2 (`proposition6_1_2`) and
Corollary 4.0.4 (`corollary4_0_4`) only, so the corollary is stated and proved here, upstream of
§8: the proof of Lemma 8.3.1 (`WeilClasses.Secant.Sec8_3`) uses it. `WeilClasses.Main.Intro`, the
module of the introduction's other results, imports this module.

The helpers (prefix `main_`, shared with `WeilClasses.Main.Intro`) are those the proofs need: `κ`,
`exp` and the grading on `⋀• V`, and the base change of `⋀• V`, of Orlov's `φ` and of `κ`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable {n : ℕ}

/-! ## Helpers: `κ`, `exp` and the grading on `⋀• V` -/

section KappaHelpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem main_algebraMapInv_of_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {k : ℕ} (hk : k ≠ 0) {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    ExteriorAlgebra.algebraMapInv x = 0 := by
  have h := main_proj_zero x
  rw [main_proj_of_mem hx] at h
  simp only [Ne.symm hk, ↓reduceIte] at h
  exact (ExteriorAlgebra.algebraMap_eq_zero_iff M _).mp h.symm

omit [CharZero F] in
theorem main_rankExt_apply (y : ExtV F n) :
    rankExt F n y = ExteriorAlgebra.algebraMapInv y := rfl

omit [CharZero F] in
theorem main_projDeg_apply (k : ℕ) (y : ExtV F n) :
    projDeg F n k y = GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (V F n)) k y := rfl

omit [CharZero F] in
theorem main_projDeg_mem (k : ℕ) (y : ExtV F n) : projDeg F n k y ∈ ⋀[F]^k (V F n) := by
  rw [main_projDeg_apply, GradedAlgebra.proj_apply]
  exact SetLike.coe_mem _

omit [CharZero F] in
theorem main_isNilpotent_two {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) : IsNilpotent c :=
  main_isNilpotent_of_mem two_ne_zero hc

theorem main_rankExt_exp_mul {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (y : ExtV F n) :
    rankExt F n (IsNilpotent.exp c * y) = rankExt F n y := by
  rw [map_mul, rankExt, IsNilpotent.map_exp (main_isNilpotent_two F n hc),
    main_algebraMapInv_of_mem two_ne_zero hc, IsNilpotent.exp_zero, one_mul]

theorem main_projDeg_two_exp_mul {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (y : ExtV F n) :
    projDeg F n 2 (IsNilpotent.exp c * y) = rankExt F n y • c + projDeg F n 2 y := by
  obtain ⟨k, hk⟩ := main_isNilpotent_two F n hc
  have hk2 : c ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  rw [IsNilpotent.exp_eq_sum hk2, Finset.sum_mul, map_sum, Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hterm : ∀ i : ℕ, projDeg F n 2 (((i + 2).factorial : ℚ)⁻¹ • c ^ (i + 2) * y) = 0 := by
    intro i
    have : ¬ 2 * (i + 2) ≤ 2 := by omega
    rw [smul_mul_assoc, map_rat_smul, main_projDeg_apply,
      main_proj_mul_of_mem_left (main_pow_mem hc (i + 2))]
    simp only [this, ↓reduceIte, smul_zero]
  simp only [hterm, Finset.sum_const_zero, zero_add, pow_one, pow_zero, one_mul,
    Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [main_projDeg_apply, main_proj_mul_of_mem_left hc]
  simp only [le_refl, ↓reduceIte, Nat.sub_self]
  rw [main_proj_zero, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

/-- `κ(exp(c) y) = κ(y)` for a class `c` of degree `2` (when `y` has nonzero rank). -/
theorem main_kappa_exp_mul {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (y : ExtV F n)
    (hr : rankExt F n y ≠ 0) : kappa F n (IsNilpotent.exp c * y) = kappa F n y := by
  have hy2 := main_projDeg_mem F n 2 y
  rw [kappa, kappa, main_rankExt_exp_mul F n hc, main_projDeg_two_exp_mul F n hc, smul_add,
    smul_smul, neg_mul, inv_mul_cancel₀ hr, neg_smul, one_smul, ← mul_assoc]
  have hc' : -c ∈ ⋀[F]^2 (V F n) := Submodule.neg_mem _ hc
  have hy' : (-(rankExt F n y)⁻¹) • projDeg F n 2 y ∈ ⋀[F]^2 (V F n) :=
    Submodule.smul_mem _ _ hy2
  rw [add_comm, IsNilpotent.exp_add_of_commute (main_commute_of_mem_two hy' _)
      (main_isNilpotent_two F n hy') (main_isNilpotent_two F n hc'),
    mul_assoc _ (IsNilpotent.exp (-c)),
    IsNilpotent.exp_neg_mul_exp_self (main_isNilpotent_two F n hc), mul_one]

/-- `κ` commutes with the action of a linear map on `⋀• V`. -/
theorem main_kappa_map (T : V F n →ₗ[F] V F n) (y : ExtV F n) :
    kappa F n (ExteriorAlgebra.map T y) = ExteriorAlgebra.map T (kappa F n y) := by
  have hy2 := main_projDeg_mem F n 2 y
  have hnil : IsNilpotent ((-(rankExt F n y)⁻¹) • projDeg F n 2 y) :=
    main_isNilpotent_two F n (Submodule.smul_mem _ _ hy2)
  rw [kappa, kappa, map_mul, IsNilpotent.map_exp hnil, map_smul, main_rankExt_apply,
    main_rankExt_apply, main_algebraMapInv_map, main_projDeg_apply, main_projDeg_apply,
    main_proj_map]

theorem main_ι_mem_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (v : M) :
    ExteriorAlgebra.ι R v ∈ ⋀[R]^1 M := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ v

omit [CharZero F] in
theorem main_c1P_mem : c1P F n ∈ ⋀[F]^2 (V F n) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  simp only [pullX, pullXHat, ExteriorAlgebra.map_apply_ι]
  exact main_mul_mem (main_ι_mem_one _) (main_ι_mem_one _)

theorem main_rhoExt_eq (g : Spin F n) (y : ExtV F n) :
    rhoExt F n g y = ExteriorAlgebra.map (rho F n g : V F n →ₗ[F] V F n) y := rfl

end KappaHelpers

/-! ## Helpers: base change of `⋀• V` -/

section BcExtHelpers

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem main_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) := by
  unfold bcExt
  erw [ExteriorAlgebra.lift_ι_apply]
  rfl

theorem main_bcExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcV F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, main_bcExt_ι]

theorem main_algebraMapInv_bcExt (ξ : ExtV F n) :
    ExteriorAlgebra.algebraMapInv (bcExt F F' n ξ) =
      algebraMap F F' (ExteriorAlgebra.algebraMapInv ξ) := by
  have : (ExteriorAlgebra.algebraMapInv.restrictScalars F).comp (bcExt F F' n) =
      (Algebra.ofId F F').comp ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [main_bcExt_ι, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun g => g ξ) this

theorem main_bcExt_mem (k : ℕ) {ξ : ExtV F n} (hξ : ξ ∈ ⋀[F]^k (V F n)) :
    bcExt F F' n ξ ∈ ⋀[F']^k (V F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hξ
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [main_bcExt_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' k (Set.mem_range_self _)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, ← algebraMap_smul F' c]; exact Submodule.smul_mem _ _ hx

end BcExtHelpers

/-! ## Helpers: Orlov's `φ` and `κ` commute with base change

`φ` is defined over `ℚ`: its matrix in the bases `e_K ⊗ e_L` and `π_X^*e_I ∪ π_X̂^*f_J` is given by
the signs of `muStar_basis` and `psiPinvShift_basis` (proof of Lemma 6.3.1). -/

section BaseChangeOrlov

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem main_repr_bcS (x : S ℚ n) (M : Finset (Fin (2 * n))) :
    (basisS F n).repr (bcS ℚ F n x) M = algebraMap ℚ F ((basisS ℚ n).repr x M) := by
  conv_lhs => rw [← (basisS ℚ n).sum_repr x]
  rw [map_sum]
  have h : ∀ M', bcS ℚ F n ((basisS ℚ n).repr x M' • basisS ℚ n M') =
      algebraMap ℚ F ((basisS ℚ n).repr x M') • basisS F n M' := fun M' => by
    rw [map_smul, main_lef_bcS_basisS, algebraMap_smul]
  simp only [h]
  rw [Module.Basis.repr_sum_self]

theorem main_epsSign_bc (K L : Finset (Fin (2 * n))) :
    epsSign F n K L = algebraMap ℚ F (epsSign ℚ n K L) := by
  simp only [epsSign]
  rw [← main_repr_bcS, map_mul (bcS ℚ F n), main_lef_bcS_basisS, main_lef_bcS_basisS]

theorem main_bcExt_pullX (s : S ℚ n) : bcExt ℚ F n (pullX ℚ n s) = pullX F n (bcS ℚ F n s) := by
  induction s using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply ℚ F (S F n), AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  | ι v =>
    simp only [pullX, ExteriorAlgebra.map_apply_ι, main_bcExt_ι, main_bcS_ι]
    congr 1
    simp [bcV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem main_bcExt_pullXHat_basis (M : Finset (Fin (2 * n))) :
    bcExt ℚ F n (pullXHat ℚ n (basisSHat ℚ n M)) = pullXHat F n (basisSHat F n M) := by
  simp only [basisSHat]
  rw [ExteriorAlgebra.basis_apply_ofCard _ (s := M) rfl,
    ExteriorAlgebra.basis_apply_ofCard _ (s := M) rfl]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [pullXHat, pullXHat, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
    main_bcExt_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, bcV, LinearMap.coe_inl, LinearMap.prodMap_apply, map_zero]
  congr 1
  refine LinearMap.ext fun w => ?_
  simp [bcDual, f, e, Pi.single_apply, apply_ite, Finset.sum_ite_eq]

theorem main_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n I (K \ I) * epsSign F n (K \ I) L) •
        (((-1 : F) ^ ((K \ I ∪ L).card * ((K \ I ∪ L).card + 3) / 2) *
            epsSign F n (K \ I ∪ L) (K \ I ∪ L)ᶜ) •
          (pullX F n (basisS F n I) * pullXHat F n (basisSHat F n (K \ I ∪ L)ᶜ))) := by
  simp only [phiOrlov, LinearMap.comp_apply, muStar_basis, map_sum, map_smul,
    TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis, TensorProduct.tmul_smul,
    LinearEquiv.coe_coe, kunnethXHat_tmul]

theorem main_bcExt_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    bcExt ℚ F n (phiOrlov ℚ n (basisS ℚ n K ⊗ₜ[ℚ] basisS ℚ n L)) =
      phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) := by
  rw [main_phiOrlov_basis, main_phiOrlov_basis, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_smul, map_smul, map_mul, main_bcExt_pullX, main_lef_bcS_basisS,
    main_bcExt_pullXHat_basis,
    algebra_compatible_smul F (epsSign ℚ n I (K \ I) * epsSign ℚ n (K \ I) L),
    algebra_compatible_smul F ((-1 : ℚ) ^ ((K \ I ∪ L).card * ((K \ I ∪ L).card + 3) / 2) *
      epsSign ℚ n (K \ I ∪ L) (K \ I ∪ L)ᶜ)]
  simp only [map_mul, map_pow, map_neg, map_one, ← main_epsSign_bc]

theorem main_bcS_tau (v : S ℚ n) : bcS ℚ F n (tau ℚ n v) = tau F n (bcS ℚ F n v) := by
  induction v using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp only [tau, CliffordAlgebra.reverse.commutes, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply ℚ F (S F n), CliffordAlgebra.reverse.commutes]
  | ι v => simp only [tau, CliffordAlgebra.reverse_ι, main_bcS_ι]
  | mul a b ha hb =>
    simp only [tau, CliffordAlgebra.reverse.map_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem main_bcExt_phiOrlov (u v : S ℚ n) :
    bcExt ℚ F n (phiOrlov ℚ n (u ⊗ₜ[ℚ] v)) = phiOrlov F n (bcS ℚ F n u ⊗ₜ[F] bcS ℚ F n v) := by
  let B : S ℚ n →ₗ[ℚ] S ℚ n →ₗ[ℚ] ExtV F n :=
    (TensorProduct.mk ℚ (S ℚ n) (S ℚ n)).compr₂
      ((bcExt ℚ F n).toLinearMap ∘ₗ phiOrlov ℚ n)
  let B' : S ℚ n →ₗ[ℚ] S ℚ n →ₗ[ℚ] ExtV F n :=
    LinearMap.mk₂ ℚ (fun u v => phiOrlov F n (bcS ℚ F n u ⊗ₜ[F] bcS ℚ F n v))
      (fun u u' v => by rw [map_add, TensorProduct.add_tmul, map_add])
      (fun c u v => by
        rw [map_smul, algebra_compatible_smul F, ← TensorProduct.smul_tmul', map_smul,
          ← algebra_compatible_smul])
      (fun u v v' => by rw [map_add, TensorProduct.tmul_add, map_add])
      (fun c u v => by
        rw [map_smul, algebra_compatible_smul F, TensorProduct.tmul_smul, map_smul,
          ← algebra_compatible_smul])
  have hB : B = B' := LinearMap.ext_basis (basisS ℚ n) (basisS ℚ n) fun K L => by
    simp only [B, B', LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.mk₂_apply, main_lef_bcS_basisS]
    exact main_bcExt_phiOrlov_basis F n K L
  exact congrArg (fun B : S ℚ n →ₗ[ℚ] S ℚ n →ₗ[ℚ] ExtV F n => B u v) hB

theorem main_bcExt_secantSqClass (w₁ w₂ : S ℚ n) :
    bcExt ℚ F n (secantSqClass ℚ n w₁ w₂) =
      secantSqClass F n (bcS ℚ F n w₁) (bcS ℚ F n w₂) := by
  rw [secantSqClass, secantSqClass, main_bcExt_phiOrlov, main_bcS_tau]

theorem main_bcExt_projDeg (k : ℕ) (y : ExtV ℚ n) :
    bcExt ℚ F n (projDeg ℚ n k y) = projDeg F n k (bcExt ℚ F n y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[ℚ]^i (V ℚ n)) with
  | zero => simp
  | @homogeneous j x =>
    rw [main_projDeg_apply, main_projDeg_apply, main_proj_of_mem x.2,
      main_proj_of_mem (main_bcExt_mem ℚ F n j x.2)]
    split_ifs <;> simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem main_bcExt_kappa (y : ExtV ℚ n) :
    bcExt ℚ F n (kappa ℚ n y) = kappa F n (bcExt ℚ F n y) := by
  have h2 : -(rankExt ℚ n y)⁻¹ • projDeg ℚ n 2 y ∈ ⋀[ℚ]^2 (V ℚ n) :=
    Submodule.smul_mem _ _ (main_projDeg_mem ℚ n 2 y)
  rw [kappa, kappa, map_mul, IsNilpotent.map_exp (main_isNilpotent_two ℚ n h2), map_smul,
    main_bcExt_projDeg, algebra_compatible_smul F, main_rankExt_apply, main_rankExt_apply,
    main_algebraMapInv_bcExt, map_neg, map_inv₀]

end BaseChangeOrlov

/-! ## Corollary 1.3.2 -/

/-- The proof of Corollary 1.3.2 over a field `F` (`corollary1_3_2_field`). -/
theorem main_corollary1_3_2_field (F : Type*) [Field F] [CharZero F] (g : Spin F n)
    (w₁ w₂ : S F n) (h₁ : m F n (g : C F n) w₁ = w₁) (h₂ : m F n (g : C F n) w₂ = w₂)
    (hr : rankExt F n (secantSqClass F n w₁ w₂) ≠ 0) :
    rhoExt F n g (kappa F n (secantSqClass F n w₁ w₂)) = kappa F n (secantSqClass F n w₁ w₂) := by
  set x := secantSqClass F n w₁ w₂ with hx_def
  -- `m_g ⊗ m_g` leaves `w₁ ⊗ w₂` invariant, so `ρ'_g(ch E) = ch E`: `φ' = φ ∘ (id ⊗ τ)` intertwines
  -- `m ⊗ m` with `ρ'` (Proposition 6.1.2)
  have hx : rhoPrime F n g x = x := by
    rw [hx_def, secantSqClass_eq_phiPrime, rhoPrime, LinearMap.comp_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (phiPrimeInv F n), phiPrimeInv_comp_phiPrime, LinearMap.id_apply,
      TensorProduct.map_tmul, h₁, h₂]
  -- the upper square of (1.3.1): `ch(E) ∪ exp(-c₁(𝒫)/2)` is `ρ_g`-invariant
  have h612 := proposition6_1_2 F n g x
  rw [hx] at h612
  have hc1 := main_c1P_mem F n
  have hρc1 : rhoExt F n g (c1P F n) ∈ ⋀[F]^2 (V F n) := by
    rw [main_rhoExt_eq]; exact main_map_mem_exteriorPower _ 2 hc1
  have ha : -((2 : F)⁻¹ • c1P F n) ∈ ⋀[F]^2 (V F n) :=
    Submodule.neg_mem _ (Submodule.smul_mem _ _ hc1)
  have hb : (2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n)) ∈ ⋀[F]^2 (V F n) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hc1 hρc1)
  have hinv : rhoExt F n g (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x) =
      IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x := by
    rw [map_mul, IsNilpotent.map_exp (main_isNilpotent_two F n ha), map_neg, map_smul]
    conv_rhs => rw [h612, ← mul_assoc, ← IsNilpotent.exp_add_of_commute
      (main_commute_of_mem_two ha _) (main_isNilpotent_two F n ha) (main_isNilpotent_two F n hb)]
    congr 2
    rw [smul_sub]; abel
  -- applying `κ`: `κ(ch E) = κ(ρ_g(ch E)) = ρ_g κ(ch E)`
  have hr' : rankExt F n x ≠ 0 := hr
  calc rhoExt F n g (kappa F n x)
      = rhoExt F n g (kappa F n (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x)) := by
        rw [main_kappa_exp_mul F n ha x hr']
    _ = kappa F n (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x) := by
        rw [main_rhoExt_eq, ← main_kappa_map, ← main_rhoExt_eq, hinv]
    _ = kappa F n x := main_kappa_exp_mul F n ha x hr'

/-- **Corollary 1.3.2** (`cor-kappa-class-is-Spin-V-P-invariant`), first sentence. If the rank `r`
of a `P`-secant`^{⊠2}`-object `E := Φ(F₁ ⊠ F₂^∨)` is non-zero, then its characteristic class `κ(E)` is
`Spin(V)_P`-invariant with respect to the representation `ρ`.

Model: `ch(E) = φ(w₁ ⊗ τ w₂)` (`secantSqClass ℚ n w₁ w₂`) with `wᵢ = ch(Fᵢ) ∈ P`; `Spin(V)_P` the
integral group of (2.2.2) (`P.spinPZ`) acting on `⋀• V_ℚ` by `ρ`. Any `K`-secant `P`. -/
theorem corollary1_3_2 {d : ℚ} (P : KSecant n d) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ)
    (hw₂ : w₂ ∈ P.Pℚ) (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) :
    kappa ℚ n (secantSqClass ℚ n w₁ w₂) ∈ invariantsExt ℚ n P.spinPZ := by
  -- every `g ∈ Spin(V)_P` fixes `w₁, w₂ ∈ P`
  intro g hg
  obtain ⟨-, hgP⟩ := Subgroup.mem_inf.mp hg
  exact main_corollary1_3_2_field ℚ g w₁ w₂ (hgP w₁ hw₁) (hgP w₂ hw₂) hr

/-- **Corollary 1.3.2** (`cor-kappa-class-is-Spin-V-P-invariant`), second sentence: "Consequently,
`κ(E)` remains of Hodge type under every deformation of `(X × X̂, η, h)` as a polarized abelian variety
of Weil type". Model: the deformations are parametrized by the period domain `Ω_P` (Lemma 4.0.2,
Corollary 4.0.4), and "of Hodge type" is membership in the Hodge ring `hodgeRingV n I`. Stated for
every `K`-secant satisfying Assumption 2.4.1 (the paper: `P = P_Θ`). -/
theorem corollary1_3_2_hodge {d : ℚ} (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ P.OmegaP hP.isCompl) :
    kappa ℚ n (secantSqClass ℚ n w₁ w₂) ∈ hodgeRingV n I :=
  -- `Spin(V)_P`-invariant classes remain of Hodge type on `Ω_P` (Corollary 4.0.4)
  corollary4_0_4 P J hP _ (corollary1_3_2 P w₁ w₂ hw₁ hw₂ hr) I hI

/-- The invariance of Corollary 1.3.2 over any field `F` of characteristic `0` (the proof of the
corollary): if `g ∈ Spin(V_F)` fixes `w₁` and `w₂` (`m_g wᵢ = wᵢ`) and `φ(w₁ ⊗ τ w₂)` has non-zero
rank, then `ρ_g κ(φ(w₁ ⊗ τ w₂)) = κ(φ(w₁ ⊗ τ w₂))`. -/
theorem corollary1_3_2_field (F : Type*) [Field F] [CharZero F] (g : Spin F n) (w₁ w₂ : S F n)
    (h₁ : m F n (g : C F n) w₁ = w₁) (h₂ : m F n (g : C F n) w₂ = w₂)
    (hr : rankExt F n (secantSqClass F n w₁ w₂) ≠ 0) :
    rhoExt F n g (kappa F n (secantSqClass F n w₁ w₂)) = kappa F n (secantSqClass F n w₁ w₂) :=
  main_corollary1_3_2_field F g w₁ w₂ h₁ h₂ hr

/-- Corollary 1.3.2 for `Spin(V_F)_P`, `F` any field of characteristic `0`: the base change of
`κ(E)` is invariant under every `g ∈ Spin(V_F)` fixing the `F`-span of `P` pointwise. -/
theorem corollary1_3_2_baseChange {d : ℚ} (P : KSecant n d) (F : Type*) [Field F] [CharZero F]
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₁ w₂) ≠ 0) (g : Spin F n)
    (hg : g ∈ fixingSpin F n (Submodule.span F (bcS ℚ F n '' P.Pℚ))) :
    rhoExt F n g (bcExt ℚ F n (kappa ℚ n (secantSqClass ℚ n w₁ w₂))) =
      bcExt ℚ F n (kappa ℚ n (secantSqClass ℚ n w₁ w₂)) := by
  -- `κ(φ(w₁ ⊗ τ w₂))` is defined over `ℚ`, and `bcS wᵢ ∈ P_F` are fixed by `g`
  have hmem : ∀ w ∈ P.Pℚ, bcS ℚ F n w ∈ Submodule.span F (bcS ℚ F n '' P.Pℚ) :=
    fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
  have hr' : rankExt F n (secantSqClass F n (bcS ℚ F n w₁) (bcS ℚ F n w₂)) ≠ 0 := by
    rw [← main_bcExt_secantSqClass, main_rankExt_apply, main_algebraMapInv_bcExt,
      ← main_rankExt_apply]
    exact (map_ne_zero (algebraMap ℚ F)).mpr hr
  rw [main_bcExt_kappa, main_bcExt_secantSqClass]
  exact main_corollary1_3_2_field F g _ _ (hg _ (hmem w₁ hw₁)) (hg _ (hmem w₂ hw₂)) hr'

end WeilClasses
