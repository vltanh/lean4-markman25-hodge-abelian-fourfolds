module

public import WeilClasses.Secant.Sec8_3
public import WeilClasses.Orlov.Cor1_3_2
public import WeilClasses.Orlov.Sec6_2
public import WeilClasses.Orlov.Sec6_4
public import WeilClasses.PeriodDomain.SemiHodge
public import WeilClasses.Igusa.Defs
public import WeilClasses.AbelianVariety.Lemmas
public import WeilClasses.Main.Compare
public import WeilClasses.Igusa.Secant
public import WeilClasses.External.Chevalley.Sec2_2

/-!
# The introduction (paper §§1.2–1.4): Proposition 1.2.1, Theorem 1.4.1

Statements of the introduction's results on secant classes (TeX lines 311–532), in the model of
`WeilClasses.Secant.Defs`.

## §1.2 and §1.3

`P = P_Θ` is the oriented `K`-secant (1.2.4) = (2.4.5) of an ample class `Θ` of `X` (complex structure
`J` of `H¹(X, ℝ)`), `u = √-dΘ`, `ℓ̃₁ = K exp(u)`, `ℓ̃₂ = K exp(ū)` (`WeilClasses.PAmple`).

* **Proposition 1.2.1** (`proposition1_2_1`) and the sentence after it
  (`proposition1_2_1_rational`): `φ ∘ (id ⊗ τ)` (`phiPrime`) maps `ℓ̃ᵢ ⊗ ℓ̃ᵢ` into
  `⊕_{k ≥ 2n} H^k(X × X̂, K)` with projection `⋀^{2n} Wᵢ` to `H^{2n}`, and `HW_P` onto a plane
  projecting onto `ĤW_P`. (= Proposition 6.4.1(1).)
* §1.3, before Corollary 1.3.2: `H²(X × X̂, ℚ)^{Spin(V)_P}` is the line spanned by `h = Ξ_P^♯`
  (`intro_invQ_two`), `h` is ample (`intro_hClass_isAmple`, for the standard complex structure
  `-I_{V_ℝ}` of `X × X̂`, transported to the model `H¹(X × X̂) = ℚ^{4n}` by `coordV`), and
  `η(k) h = Nm(k) h` (`intro_eta_hClass`), with `Nm(a + b√-d) = a² + d b²` (`Kd_Nm`, a compared
  theorem of `Challenge.lean`).
* **Corollary 1.3.2** (`corollary1_3_2`, `corollary1_3_2_hodge`; and `corollary1_3_2_field`,
  `corollary1_3_2_baseChange`: the invariance holds for `Spin(V_F)_P` for every field `F`) is stated
  and proved in `WeilClasses.Orlov.Cor1_3_2`, imported here: its proof uses only Proposition 6.1.2
  and Corollary 4.0.4, and Lemma 8.3.1 (`WeilClasses.Secant.Sec8_3`) uses it. The `main_` helpers
  of its proof (`κ` and `exp`; base change of `⋀• V`, of `φ` and of `κ`) are there too.

## §1.4, Theorem 1.4.1 (`n = 3`)

`X` is the Jacobian of a non-hyperelliptic genus-`3` curve; in the model `Θ = ThetaStd ℚ 3` is ample
for the complex structure `J`; `d ≥ 3`; `ch(F₁) = ch(F₂) = w = chF1 d` (`F₁ = I_{∪Cᵢ}(Θ)`,
`F₂ = I_{∪Σᵢ}(Θ)`; geometric input, see `WeilClasses.Secant.Defs`); `E` is the sheaf with
`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]`, `ch(E) = τ(φ(w ⊗ w))` (`chE`), `κ₃(E) = kappa3E d`; `P = P_Θ` (`PJac`).

* (1) `theorem1_4_1_1`; (3) `theorem1_4_1_3`; (4) `theorem1_4_1_4`, `theorem1_4_1_4_finrank`;
  the cohomological part of (2): the rank of `E` is `8d` (`theorem1_4_1_2_rank`, from `rank_chE`,
  a compared theorem of `Challenge.lean`, for every `d`);
  `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))` (`kappa3E_eq_neg`), relating (4) to Lemma 8.3.1.
* **Left out (sheaf-theoretic):** item (2) (`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]` with `E` a simple reflexive sheaf)
  except the value of the rank, and item (5) (first-order deformations of `E` as a twisted sheaf).

Numerical checks (exact arithmetic in `ℚ(√-d)`, `d = 1, 2, 3, 5, 7`): the rank of `φ(w ⊗ w)` is `8d`;
`κ₃` and `h³` are independent; the `η(K)`-translates of `κ₃` and `h³` span the `3`-dimensional
`ℚh³ ⊕ ĤW_P`; on the line through `τ(w)` and `w` only the points `exp(±√-dΘ)` are pure (kernel of
`m` of dimension `6`); `κ(φ(w₁ ⊗ τ w₂))` is invariant under elements `1 + xy`
(`x ∈ W₁`, `y ∈ W₂`, `(x, y)_V = 0`) of `Spin(V_K)_P` (`n = 2, 3`); `h` is ample for `-I_{V_ℝ}`
(`n = 1, 2, 3`, random `J` for which `Θ` is ample).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable {n : ℕ}

/-- The oriented `K`-secant `P_Θ` of (1.2.4) = (2.4.5) for an ample class `Θ` (`0 < n`, `0 < d`). -/
noncomputable abbrev PAmple {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ)
    (hn : 0 < n) (d : ℚ) (hd : 0 < d) : KSecant n d :=
  PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)

/-- `V_K = W₁ ⊕ W₂` for `P_Θ`. -/
theorem PAmple_isCompl {J : Module.End ℝ (H1 ℝ n)} {Θ : S ℚ n} (hΘ : IsAmple n J Θ) (hn : 0 < n)
    (d : ℚ) (hd : 0 < d) : IsCompl (PAmple hΘ hn d hd).W₁ (PAmple hΘ hn d hd).W₂ :=
  PTheta_isCompl n d hd _ _ _ hΘ.bijective_thetaMap

/-! ## Helpers: `κ`, `exp` and the grading on `⋀• V` -/

section KappaHelpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem main_tauExt_apply (y : ExtV F n) :
    tauExt F n y = CliffordAlgebra.reverse (Q := (0 : QuadraticForm F (V F n))) y := rfl

theorem main_commute_exp_of_mem_two {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (x : ExtV F n) :
    Commute (IsNilpotent.exp c) x := by
  obtain ⟨k, hk⟩ := main_isNilpotent_two F n hc
  rw [IsNilpotent.exp_eq_sum hk]
  exact Commute.sum_left _ _ _ fun i _ =>
    (((main_commute_of_mem_two hc x).pow_left i).smul_left _)

omit [CharZero F] in
theorem main_proj_reverse (k : ℕ) (y : ExtV F n) :
    projDeg F n k (tauExt F n y) = tauExt F n (projDeg F n k y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[F]^i (V F n)) with
  | zero => simp
  | @homogeneous j x =>
    obtain ⟨x, hx⟩ := x
    simp only [main_tauExt_apply, main_projDeg_apply]
    rw [main_reverse_of_mem hx, map_smul, main_proj_of_mem hx]
    split_ifs with h
    · rw [main_reverse_of_mem hx]
    · simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit [CharZero F] in
theorem main_reverse_pow (z : ExtV F n) (i : ℕ) : tauExt F n (z ^ i) = (tauExt F n z) ^ i := by
  simp only [main_tauExt_apply]
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, CliffordAlgebra.reverse.map_mul, ih, pow_succ']

theorem main_reverse_exp {z : ExtV F n} (hz : z ∈ ⋀[F]^2 (V F n)) :
    tauExt F n (IsNilpotent.exp z) = IsNilpotent.exp (-z) := by
  have hτz : tauExt F n z = -z := by
    rw [main_tauExt_apply, main_reverse_of_mem hz]; norm_num
  obtain ⟨k, hk⟩ := main_isNilpotent_two F n hz
  have hk' : (-z) ^ k = 0 := by rw [neg_pow, hk, mul_zero]
  rw [IsNilpotent.exp_eq_sum hk, IsNilpotent.exp_eq_sum hk', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, main_reverse_pow, hτz]

/-- `κ(τ y) = τ(κ y)`. -/
theorem main_kappa_reverse (y : ExtV F n) :
    kappa F n (tauExt F n y) = tauExt F n (kappa F n y) := by
  have hy2 := main_projDeg_mem F n 2 y
  have hz2 : (-(rankExt F n y)⁻¹) • projDeg F n 2 y ∈ ⋀[F]^2 (V F n) :=
    Submodule.smul_mem _ _ hy2
  have hτy2 : projDeg F n 2 (tauExt F n y) = -projDeg F n 2 y := by
    rw [main_proj_reverse, main_tauExt_apply, main_reverse_of_mem hy2]; norm_num
  have hrank : rankExt F n (tauExt F n y) = rankExt F n y := by
    rw [main_rankExt_apply, main_tauExt_apply, main_algebraMapInv_reverse]; rfl
  have hmul : tauExt F n (IsNilpotent.exp ((-(rankExt F n y)⁻¹) • projDeg F n 2 y) * y) =
      tauExt F n y * tauExt F n (IsNilpotent.exp ((-(rankExt F n y)⁻¹) • projDeg F n 2 y)) := by
    simp only [main_tauExt_apply, CliffordAlgebra.reverse.map_mul]
  rw [kappa, kappa, hrank, hτy2, hmul, main_reverse_exp F n hz2,
    ← (main_commute_exp_of_mem_two F n (Submodule.neg_mem _ hz2) _).eq, smul_neg]

omit [CharZero F] in
theorem main_tau_mem_hodgeRingV {n : ℕ} {I : Module.End ℝ (V ℝ n)} {x : ExtV ℚ n}
    (hx : x ∈ hodgeRingV n I) : tauExt ℚ n x ∈ hodgeRingV n I := by
  refine Submodule.iSup_induction _ (motive := fun x => tauExt ℚ n x ∈ hodgeRingV n I)
    hx (fun p y hy => ?_) ?_ (fun y z hy hz => ?_)
  · rw [main_tauExt_apply, main_reverse_of_mem ((mem_hodgeClassesV_iff n I p y).mp hy).1]
    exact Submodule.mem_iSup_of_mem p (Submodule.smul_mem _ _ hy)
  · rw [map_zero]; exact Submodule.zero_mem _
  · rw [map_add]; exact Submodule.add_mem _ hy hz

end KappaHelpers

/-! ## Helpers: classes of degree `2` on `X × X̂` via the pairing `(·,·)_V` -/

section SharpHelpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- Every functional on `V_F` is `(x, ·)_V` (the pairing (1.2.2) is nondegenerate). -/
theorem main_pairing_surjective (a : Module.Dual F (V F n)) : ∃ x, pairing F n x = a := by
  have hinj : Function.Injective (pairing F n) := fun x y hxy =>
    sub_eq_zero.mp (main_pairing_eq_zero F n _ fun z => by
      rw [map_sub, LinearMap.sub_apply, hxy, sub_self])
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj a

/-- Two classes of degree `2` on `X × X̂` with the same values `⟪ξ, (x,·)_V ∧ (y,·)_V⟫` are
equal. -/
theorem main_eq_of_pairing_dc {ξ η : ExtV F n} (hξ : ξ ∈ ⋀[F]^2 (V F n)) (hη : η ∈ ⋀[F]^2 (V F n))
    (h : ∀ x y : V F n,
      ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
        (contractLeft (Q := 0) (pairing F n x) ξ)) =
      ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
        (contractLeft (Q := 0) (pairing F n x) η))) : ξ = η := by
  refine main_eq_of_dc hξ hη fun a b => ?_
  obtain ⟨x, rfl⟩ := main_pairing_surjective F n a
  obtain ⟨y, rfl⟩ := main_pairing_surjective F n b
  exact h x y

end SharpHelpers

/-! ## Helpers: base change of `⋀• V` -/

section BcExtHelpers

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem main_bcV_basisV (i : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n i) = basisV F' n i := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
      Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply, bcV, LinearMap.prodMap_apply, map_zero]
    congr 1
    refine LinearMap.ext fun w => ?_
    simp [bcDual, f, e, Pi.single_apply]
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
      Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply, bcV, LinearMap.prodMap_apply, map_zero]
    congr 1
    funext k
    simp [bcH1, Pi.basisFun_apply, Pi.single_apply]

theorem main_bcExt_basisExt (s : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n s) = basisExt F' n s := by
  simp only [basisExt]
  rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl,
    ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [main_bcExt_ιMulti]
  congr 1
  funext i
  simp [main_bcV_basisV]

/-- Base change `⋀• V_F → ⋀• V_{F'}` is injective. -/
theorem main_bcExt_injective : Function.Injective (bcExt F F' n) := by
  refine (injective_iff_map_eq_zero (bcExt F F' n)).mpr fun x hx => ?_
  have hli : LinearIndependent F (fun s => basisExt F' n s) :=
    (basisExt F' n).linearIndependent.restrict_scalars' F
  rw [← (basisExt F n).sum_repr x, map_sum] at hx
  simp only [map_smul, main_bcExt_basisExt] at hx
  have h0 := Fintype.linearIndependent_iff.mp hli _ hx
  rw [← (basisExt F n).sum_repr x]
  simp [h0]

/-- Base change commutes with the action of compatible linear maps. -/
theorem main_bcExt_map (T : V F n →ₗ[F] V F n) (T' : V F' n →ₗ[F'] V F' n)
    (hT : ∀ v, T' (bcV F F' n v) = bcV F F' n (T v)) (x : ExtV F n) :
    bcExt F F' n (ExteriorAlgebra.map T x) = ExteriorAlgebra.map T' (bcExt F F' n x) := by
  have : (bcExt F F' n).comp (ExteriorAlgebra.map T) =
      ((ExteriorAlgebra.map T').restrictScalars F).comp (bcExt F F' n) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι, AlgHom.restrictScalars_apply]
    rw [main_bcExt_ι, main_bcExt_ι, ExteriorAlgebra.map_apply_ι, hT]
  exact congrArg (fun g => g x) this

theorem main_pairing_bcV (u v : V F n) :
    pairing F' n (bcV F F' n u) (bcV F F' n v) = algebraMap F F' (pairing F n u v) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, Q_bcV,
    map_sub]

theorem main_contractLeft_bcExt (a : Module.Dual F (V F n)) (a' : Module.Dual F' (V F' n))
    (ha : ∀ v, a' (bcV F F' n v) = algebraMap F F' (a v)) (ξ : ExtV F n) :
    contractLeft (Q := 0) a' (bcExt F F' n ξ) = bcExt F F' n (contractLeft (Q := 0) a ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExteriorAlgebra F' (V F' n))]
    simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul m x hx =>
    rw [map_mul]
    erw [main_bcExt_ι, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
    erw [hx]
    rw [ha, map_sub, map_mul, map_smul, algebraMap_smul]
    erw [main_bcExt_ι]

/-- Base change of double contractions with `(x, ·)_V`. -/
theorem main_dc_bcExt (u v : V F n) (ξ : ExtV F n) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F' n (bcV F F' n v))
      (contractLeft (Q := 0) (pairing F' n (bcV F F' n u)) (bcExt F F' n ξ))) =
    algebraMap F F' (ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n v)
      (contractLeft (Q := 0) (pairing F n u) ξ))) := by
  rw [main_contractLeft_bcExt F F' n (pairing F n u) _ (main_pairing_bcV F F' n u),
    main_contractLeft_bcExt F F' n (pairing F n v) _ (main_pairing_bcV F F' n v),
    main_algebraMapInv_bcExt]

end BcExtHelpers

section RealHelpers

variable (n : ℕ)

theorem main_bcH1_coordV (v : V ℚ n) :
    bcH1 ℚ ℝ (2 * n) (coordV ℚ n v) = coordV ℝ n (bcV ℚ ℝ n v) := by
  have : (bcH1 ℚ ℝ (2 * n)) ∘ₗ (coordV ℚ n).toLinearMap =
      ((coordV ℝ n).toLinearMap.restrictScalars ℚ) ∘ₗ bcV ℚ ℝ n := by
    refine (basisV ℚ n).ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, main_bcV_basisV]
    simp only [coordV, LinearEquiv.trans_apply]
    funext k
    simp only [bcH1, LinearMap.compLeft_apply, Function.comp_apply,
      LinearEquiv.funCongrLeft_apply, Algebra.linearMap_apply, LinearMap.funLeft_apply]
    rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]
    split_ifs <;> simp
  exact congrArg (fun g => g v) this

theorem main_bcS_map_coordV (ξ : ExtV ℚ n) :
    bcS ℚ ℝ (2 * n) (ExteriorAlgebra.map (coordV ℚ n).toLinearMap ξ) =
      ExteriorAlgebra.map (coordV ℝ n).toLinearMap (bcExt ℚ ℝ n ξ) := by
  have : (bcS ℚ ℝ (2 * n)).comp (ExteriorAlgebra.map (coordV ℚ n).toLinearMap) =
      ((ExteriorAlgebra.map (coordV ℝ n).toLinearMap).restrictScalars ℚ).comp (bcExt ℚ ℝ n) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι, AlgHom.restrictScalars_apply,
      LinearEquiv.coe_coe]
    rw [main_bcS_ι, main_bcExt_ι, ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe,
      main_bcH1_coordV]
  exact congrArg (fun g => g ξ) this

theorem main_eval2_map_coordV (ξ : ExtV ℝ n) (a b : Module.Dual ℝ (H1 ℝ (2 * n))) :
    eval2 ℝ (2 * n) (ExteriorAlgebra.map (coordV ℝ n).toLinearMap ξ) a b =
      ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (b ∘ₗ (coordV ℝ n).toLinearMap)
        (contractLeft (Q := 0) (a ∘ₗ (coordV ℝ n).toLinearMap) ξ)) := by
  rw [eval2, D, main_coord_empty, AlgHom.toLinearMap_apply, main_dc_map]

/-- The double contractions `⟪ξ, (x,·)_V ∧ (y,·)_V⟫` of a real class are determined by their values
on rational vectors. -/
theorem main_dc_eq_of_rational (ξ : ExtV ℝ n) (B : LinearMap.BilinForm ℝ (V ℝ n))
    (h : ∀ u v : V ℚ n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0)
      (pairing ℝ n (bcV ℚ ℝ n v)) (contractLeft (Q := 0) (pairing ℝ n (bcV ℚ ℝ n u)) ξ)) =
        B (bcV ℚ ℝ n u) (bcV ℚ ℝ n v)) (x y : V ℝ n) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing ℝ n y)
      (contractLeft (Q := 0) (pairing ℝ n x) ξ)) = B x y := by
  set B' : LinearMap.BilinForm ℝ (V ℝ n) := LinearMap.mk₂ ℝ
    (fun x y => ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing ℝ n y)
      (contractLeft (Q := 0) (pairing ℝ n x) ξ)))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun x y y' => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]) with hB'
  have hBB : B' = B := by
    refine LinearMap.BilinForm.ext_basis (basisV ℝ n) fun i j => ?_
    rw [← main_bcV_basisV ℚ ℝ n i, ← main_bcV_basisV ℚ ℝ n j, hB', LinearMap.mk₂_apply, h]
  rw [← hBB, hB', LinearMap.mk₂_apply]

end RealHelpers

/-! ## Helpers: the action of `η(K)` on the Hodge–Weil plane -/

section HWHelpers

theorem main_map_topWedge_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (T : M →ₗ[R] M) (W : Submodule R M) (c : R) (hT : ∀ v ∈ W, T v = c • v) (k : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ topWedge W k) : ExteriorAlgebra.map T x = c ^ k • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    have : T ∘ v = fun i => c • v i := funext fun i => hT _ (hv i)
    rw [this, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul a y _ hy => rw [map_smul, hy, smul_comm]

theorem main_pqPiece_left {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (k : ℕ) : pqPiece A B k 0 = topWedge A k := by
  simp only [pqPiece, topWedge, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  congr 1
  ext x
  constructor
  · rintro ⟨a, b, ha, -, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, 0, ha, fun j => j.elim0, rfl⟩

theorem main_pqPiece_right {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (k : ℕ) : pqPiece A B 0 k = topWedge B k := by
  simp only [pqPiece, topWedge, ExteriorAlgebra.ιMulti_zero_apply, one_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨a, b, -, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨0, b, fun j => j.elim0, hb, rfl⟩

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

theorem main_ηK_of_mem_W₁ (hW : IsCompl P.W₁ P.W₂) (k : Kd d) {v : V (Kd d) n} (hv : v ∈ P.W₁) :
    P.ηK hW k v = k • v := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_left hW hv,
    Submodule.projectionOnto_apply_of_mem_right hW.symm hv, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, add_zero]

theorem main_ηK_of_mem_W₂ (hW : IsCompl P.W₁ P.W₂) (k : Kd d) {v : V (Kd d) n} (hv : v ∈ P.W₂) :
    P.ηK hW k v = Kd.σ d k • v := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_right hW hv,
    Submodule.projectionOnto_apply_of_mem_left hW.symm hv, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, zero_add]

/-- On `ĤW_P`, `η_k` acts by `k^{2n}` on the `⋀^{2n} W₁`-component and by `σ(k)^{2n}` on the
`⋀^{2n} W₂`-component. -/
theorem main_hwPlane_η (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) {x : ExtV ℚ n}
    (hx : x ∈ P.hwPlane) : ∃ x₁ ∈ topWedge P.W₁ (2 * n), ∃ x₂ ∈ topWedge P.W₂ (2 * n),
      bcExt ℚ (Kd d) n x = x₁ + x₂ ∧ ∀ k : Kd d,
        bcExt ℚ (Kd d) n (ExteriorAlgebra.map (P.η hW k) x) =
          k ^ (2 * n) • x₁ + Kd.σ d k ^ (2 * n) • x₂ := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := Submodule.mem_sup.mp hx
  have hsum' : bcExt ℚ (Kd d) n x = x₁ + x₂ := hsum.symm
  refine ⟨x₁, hx₁, x₂, hx₂, hsum', fun k => ?_⟩
  rw [main_bcExt_map ℚ (Kd d) n _ (P.ηK hW k) (fun v => P.ηK_bcV hd hW k v), hsum', map_add,
    main_map_topWedge_smul _ _ _ (fun v hv => main_ηK_of_mem_W₁ P hW k hv) _ hx₁,
    main_map_topWedge_smul _ _ _ (fun v hv => main_ηK_of_mem_W₂ P hW k hv) _ hx₂]

/-- `η(K)` preserves `ĤW_P`. -/
theorem main_map_η_mem_hwPlane (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) {x : ExtV ℚ n}
    (hx : x ∈ P.hwPlane) (k : Kd d) : ExteriorAlgebra.map (P.η hW k) x ∈ P.hwPlane := by
  obtain ⟨x₁, hx₁, x₂, hx₂, -, hη⟩ := main_hwPlane_η P hd hW hx
  rw [KSecant.hwPlane, Submodule.mem_comap, Submodule.restrictScalars_mem,
    AlgHom.toLinearMap_apply, hη k]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hx₁) (Submodule.smul_mem _ _ hx₂)

theorem main_Kd_sqrtNeg_sq (hd : 0 < d) : Kd.sqrtNeg d ^ 2 = -(d : Kd d) := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subfield.coe_neg, SubfieldClass.coe_ratCast]
  exact sqrtNeg_sq hd.le

/-- `η(√-d)` acts on `ĤW_P` by `(√-d)^{2n} = (-d)ⁿ`. -/
theorem main_η_sqrtNeg_hwPlane (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) {x : ExtV ℚ n}
    (hx : x ∈ P.hwPlane) : ExteriorAlgebra.map (P.η hW (Kd.sqrtNeg d)) x = (-d) ^ n • x := by
  obtain ⟨x₁, -, x₂, -, hsum, hη⟩ := main_hwPlane_η P hd hW hx
  apply main_bcExt_injective ℚ (Kd d) n
  have hσ : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := Subtype.ext (by
    simp [Kd.sqrtNeg, WeilClasses.sqrtNeg, Complex.conj_ofReal])
  rw [hη, map_smul, hsum, hσ, pow_mul, pow_mul, neg_sq, main_Kd_sqrtNeg_sq hd, smul_add,
    ← algebraMap_smul (Kd d) ((-d) ^ n), ← algebraMap_smul (Kd d) ((-d) ^ n)]
  simp

end HWHelpers

/-! ## Helpers: `exp(u)` is a pure spinor (Theorem 1.4.1(1) over `ℂ`) -/

section PureHelpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem main_ThetaStd_mem : ThetaStd F n ∈ ⋀[F]^2 (H1 F n) :=
  Submodule.sum_mem _ fun _ _ => main_mul_mem (main_ι_mem_one _) (main_ι_mem_one _)

omit [CharZero F] in
theorem main_mem_evenOdd_zero_of_mem_two {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    u ∈ Splus F n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, mul_one]
    exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem main_exp_mem_Splus {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    IsNilpotent.exp u ∈ Splus F n := by
  have hu0 := main_mem_evenOdd_zero_of_mem_two F n hu
  have hpow : ∀ i : ℕ, u ^ i ∈ Splus F n := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero]
      exact CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    | succ i ih =>
      rw [pow_succ]
      have := CliffordAlgebra.evenOdd_mul_le (0 : QuadraticForm F (H1 F n)) 0 0
        (Submodule.mul_mem_mul ih hu0)
      rw [add_zero] at this
      exact this
  obtain ⟨k, hk⟩ := main_isNilpotent_of_mem two_ne_zero hu
  rw [IsNilpotent.exp_eq_sum hk]
  exact Submodule.sum_mem _ fun i _ => by
    rw [← algebraMap_smul F]; exact Submodule.smul_mem _ _ (hpow i)

theorem main_ann_exp {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    ann F n (IsNilpotent.exp u) = ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥).map
      (rho F n ⟨IsNilpotent.exp (iotaX F n u), chevalley_III_1_7_mem F n u hu⟩).toLinearMap := by
  have hm : m F n (IsNilpotent.exp (iotaX F n u)) 1 = IsNilpotent.exp u := by
    rw [m_exp_jH F n u hu, LinearMap.mulLeft_apply, mul_one]
  rw [← hm, ← ann_one F n]
  exact ann_m_spin F n ⟨_, chevalley_III_1_7_mem F n u hu⟩ 1

theorem main_exp_isEvenPureSpinor {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    IsEvenPureSpinor F n (IsNilpotent.exp u) := by
  refine ⟨main_exp_mem_Splus F n hu, fun v hv => ?_, ?_⟩
  · rw [main_ann_exp F n hu] at hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    rw [LinearEquiv.coe_coe, rho, spinVectorAction_map_app]
    obtain ⟨-, hw2⟩ := Submodule.mem_prod.mp hw
    rw [Submodule.mem_bot] at hw2
    simp [Q, hw2]
  · rw [main_ann_exp F n hu, LinearEquiv.finrank_map_eq]
    have : ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥) =
        LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) := by
      ext ⟨a, b⟩
      simp [Submodule.mem_prod, eq_comm]
    rw [this, LinearMap.finrank_range_of_inj LinearMap.inl_injective, Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]

/-- `exp(u)` and `exp(-u)` have transversal annihilators when `y ↦ y ⌋ u` is injective. -/
theorem main_ann_exp_inf {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n))
    (hinj : Function.Injective (contractOne F n u)) :
    ann F n (IsNilpotent.exp u) ⊓ ann F n (IsNilpotent.exp (-u)) = ⊥ := by
  have hu' : -u ∈ ⋀[F]^2 (H1 F n) := Submodule.neg_mem _ hu
  rw [eq_bot_iff]
  rintro v ⟨hv₁, hv₂⟩
  have hneg : ∀ y, contractOne F n (-u) y = -contractOne F n u y := fun y => by
    simp [contractOne]
  rw [main_ann_exp F n hu] at hv₁
  rw [main_ann_exp F n hu'] at hv₂
  obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hv₁
  obtain ⟨w₂, hw₂, heq⟩ := Submodule.mem_map.mp hv₂
  rw [Submodule.mem_prod, Submodule.mem_bot] at hw₁ hw₂
  simp only [LinearEquiv.coe_coe] at heq ⊢
  rw [chevalley_III_1_7_rho F n u hu] at heq ⊢
  rw [chevalley_III_1_7_rho F n (-u) hu'] at heq
  rw [hw₁.2, hw₂.2, hneg] at heq
  rw [hw₁.2]
  simp only [Prod.mk.injEq, zero_sub, neg_neg] at heq
  obtain ⟨h1, h2⟩ := heq
  rw [h1] at h2
  have hc : contractOne F n u w₁.1 = 0 := by
    have : (2 : F) • contractOne F n u w₁.1 = 0 := by
      rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have hw0 : w₁.1 = 0 := hinj (by rw [hc, map_zero])
  simp [hw0]

omit [CharZero F] in
theorem main_contractOne_smul (c : F) (ξ : S F n) (y : Module.Dual F (H1 F n)) :
    contractOne F n (c • ξ) y = c • contractOne F n ξ y := by
  simp [contractOne]

/-- `y ↦ y ⌋ Θ` is injective for `Θ = ThetaStd`. -/
theorem main_contractOne_ThetaStd_injective :
    Function.Injective (contractOne F n (ThetaStd F n)) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  have hD : D F n y (ThetaStd F n) = 0 := by
    rw [← ι_contractOne F n _ (main_ThetaStd_mem F n) y, hy, map_zero]
  have hev : ∀ b, eval2 F n (ThetaStd F n) y b = 0 := fun b => by
    rw [eval2, hD, map_zero, map_zero]
  have hsum : ∀ b, eval2 F n (ThetaStd F n) y b = ∑ i : Fin n,
      (y (e F n ⟨2 * i, by omega⟩) * b (e F n ⟨2 * i + 1, by omega⟩) -
        y (e F n ⟨2 * i + 1, by omega⟩) * b (e F n ⟨2 * i, by omega⟩)) := fun b => by
    rw [main_eval2_eq, ThetaStd, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← main_eval2_eq, main_eval2_ι_mul_ι]
  have hf : ∀ j k : Fin (2 * n), f F n j (e F n k) = if j = k then 1 else 0 := fun j k => by
    simp [f, e, Pi.single_apply]
  have hodd : ∀ i : Fin n, y (e F n ⟨2 * i, by omega⟩) = 0 := fun i => by
    have h := hev (f F n ⟨2 * i + 1, by omega⟩)
    rw [hsum, Finset.sum_eq_single i] at h
    · simpa [hf, Fin.ext_iff] using h
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      simp only [hf, Fin.mk.injEq]
      split_ifs <;> first | omega | ring
    · simp
  have heven : ∀ i : Fin n, y (e F n ⟨2 * i + 1, by omega⟩) = 0 := fun i => by
    have h := hev (f F n ⟨2 * i, by omega⟩)
    rw [hsum, Finset.sum_eq_single i] at h
    · simpa [hf, Fin.ext_iff] using h
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      simp only [hf, Fin.mk.injEq]
      split_ifs <;> first | omega | ring
    · simp
  refine (Pi.basisFun F (Fin (2 * n))).ext fun k => ?_
  rw [Pi.basisFun_apply, LinearMap.zero_apply]
  rcases Nat.mod_two_eq_zero_or_one k.val with h | h
  · have hk : k = ⟨2 * (k.val / 2), by omega⟩ := Fin.ext (by simp; omega)
    have := hodd ⟨k.val / 2, by omega⟩
    rw [hk]; exact this
  · have hk : k = ⟨2 * (k.val / 2) + 1, by omega⟩ := Fin.ext (by simp; omega)
    have := heven ⟨k.val / 2, by omega⟩
    rw [hk]; exact this

end PureHelpers

/-- `Nm(a + b√-d) = a² + d b²` (a compared theorem of `Challenge.lean`). -/
theorem Kd_Nm (d : ℚ) (hd : 0 < d) (a b : ℚ) :
    Kd.Nm d ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d) = a ^ 2 + d * b ^ 2 := by
  have h := Kd.coe_Nm hd ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d)
  apply_fun ((↑) : ℚ → ℂ) using Rat.cast_injective
  rw [h]
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hd.le)]
    simp
  simp only [Kd.sqrtNeg, WeilClasses.sqrtNeg, Subfield.coe_add, Subfield.coe_mul, map_add,
    map_mul, SubfieldClass.coe_ratCast, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  linear_combination (b : ℂ) ^ 2 * hs -
    (b : ℂ) ^ 2 * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 * Complex.I_sq

/-! ## Proposition 1.2.1 -/

/-- **Proposition 1.2.1** (no label; = Proposition 6.4.1(1)). The image `φ(ℓ̃ᵢ ⊗ τ(ℓ̃ᵢ))` via
`φ ∘ (id ⊗ τ)` of the tensor square `ℓ̃ᵢ ⊗ ℓ̃ᵢ` of each of the two pure spinor lines in `P` is
contained in `⊕_{k=2n}^{4n} H^k(X × X̂, K)`, and its projection to `H^{2n}(X × X̂, K)` is `⋀^{2n} Wᵢ`.

Model: `P = P_Θ` for `Θ` ample for `J`, `d > 0` (the paper: a positive integer), `ℓ̃ᵢ = K uᵢ`;
`φ ∘ (id ⊗ τ) = phiPrime`, where the intro's `φ` of (1.2.5) is Orlov's `φ` (`phiOrlov`) by
Proposition 1.3.1 (`proposition1_3_1_eq`). (The intro's `n ≥ 2` is not needed; `0 < n` makes `P_Θ` a
secant.) -/
theorem proposition1_2_1 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    (phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₁ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₁) ∈
          extFiltGE (Kd d) n (2 * n) ∧
        (Submodule.span (Kd d)
            {phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₁ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₁)}).map
            (projDeg (Kd d) n (2 * n)) = topWedge (PAmple hΘ hn d hd).W₁ (2 * n)) ∧
      (phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₂ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₂) ∈
          extFiltGE (Kd d) n (2 * n) ∧
        (Submodule.span (Kd d)
            {phiPrime (Kd d) n ((PAmple hΘ hn d hd).u₂ ⊗ₜ[Kd d] (PAmple hΘ hn d hd).u₂)}).map
            (projDeg (Kd d) n (2 * n)) = topWedge (PAmple hΘ hn d hd).W₂ (2 * n)) := by
  -- Proposition 6.4.1(1) for `P_Θ`, which satisfies Assumption 2.4.1
  have hP := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  exact ⟨proposition6_4_1_1_line₁ _ J hP, proposition6_4_1_1_line₂ _ J hP⟩

/-- (§1.2, after Proposition 1.2.1, TeX lines 392–393) "In particular, the isomorphism `φ ∘ (id ⊗ τ)`
maps the `2`-dimensional rational subspace `HW_P` of `P ⊗ P` to a `2`-dimensional subspace of
`H^{even}(X × X̂, ℚ)`, and the latter projects onto the `2`-dimensional subspace `ĤW_P` of Hodge–Weil
classes in `H^{2n}(X × X̂, ℚ)`." -/
theorem proposition1_2_1_rational (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    Module.finrank ℚ ((PAmple hΘ hn d hd).HWP.map (phiPrime ℚ n)) = 2 ∧
      ((PAmple hΘ hn d hd).HWP.map (phiPrime ℚ n)).map (projDeg ℚ n (2 * n)) =
        (PAmple hΘ hn d hd).hwPlane := by
  have hP := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  obtain ⟨-, -, -, hproj⟩ := proposition6_4_1_1 _ J hP
  refine ⟨?_, hproj⟩
  -- `φ'` is an isomorphism, so `φ'(HW_P)` is a plane
  have hinj : Function.Injective (phiPrime ℚ n) := fun x y h => by
    have := congrArg (phiPrimeInv ℚ n) h
    rwa [← LinearMap.comp_apply (phiPrimeInv ℚ n), ← LinearMap.comp_apply (phiPrimeInv ℚ n),
      phiPrimeInv_comp_phiPrime, LinearMap.id_apply, LinearMap.id_apply] at this
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  exact KSecant.finrank_HWP _ hd

/-! ## The polarization `h` (§1.3) -/

/-- (§1.3, TeX lines 446–447) "When `P` is given by (1.2.4) the subspace
`H²(X × X̂, ℚ)^{Spin(V)_P}` is one-dimensional spanned by an ample class `h`": the
`Spin(V)_P`-invariants of `⋀² V_ℚ` (integral `Spin(V)_P`) are spanned by `h = Ξ_P^♯` (`hClass`; its
ampleness is `intro_hClass_isAmple`). Needs `n ≥ 2` (the intro's standing assumption): for `n = 1`
the invariants of `⋀² V_ℚ` are three-dimensional. Proof: `h` is invariant, as `ρ(Spin(V_ℚ)_P)`
preserves `(·,·)_V` and commutes with `f` by Lemma 2.2.4 (TeX line 1240; `s8_rhoExt_hClass`), and
the invariants form a line by Lemma 2.2.7 (`lemma2_2_7_even`). -/
theorem intro_invQ_two (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 2 ≤ n) (d : ℚ) (hd : 0 < d) :
    (PAmple hΘ (by omega) d hd).invQ 2 =
      Submodule.span ℚ {(PAmple hΘ (by omega) d hd).hClass (PAmple_isCompl hΘ (by omega) d hd)} := by
  have hn0 : 0 < n := by omega
  set P := PAmple hΘ hn0 d hd with hP_def
  set hW := PAmple_isCompl hΘ hn0 d hd
  have hP : Assumption2_4_1 P J := PTheta_assumption2_4_1 n d hd hn0 J hJ Θ hΘ
  have hh : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  -- `h = Ξ_P^♯` is `Spin(V)_P`-invariant: `ρ_g` preserves `(·,·)_V` and commutes with `f = η_{√-d}`
  -- (Lemma 2.2.4, TeX line 1240: `f` lies in the centralizer of `ρ(Spin(V_ℚ)_P)`)
  have hinv : P.hClass hW ∈ P.invQ 2 :=
    ⟨hh, fun g hg => s8_rhoExt_hClass P hd hn hP.nonIsotropic hW g (Subgroup.mem_inf.mp hg).2⟩
  -- `h ≠ 0` (`Ξ_P` is nondegenerate)
  have hne : P.hClass hW ≠ 0 := by
    intro h0
    have hx : ((0 : Module.Dual ℚ (H1 ℚ n)), e ℚ n ⟨0, by omega⟩) ≠ (0 : V ℚ n) := by
      intro h; have := congrArg (fun v : V ℚ n => v.2 ⟨0, by omega⟩) h; simp [e] at this
    obtain ⟨y, hy⟩ : ∃ y, P.XiQ hW (0, e ℚ n ⟨0, by omega⟩) y ≠ 0 := by
      by_contra! hall
      exact hx ((P.XiQ_nondegenerate hW).1 _ hall)
    apply hy
    rw [← P.hClass_spec hW, h0]
    simp
  -- `(⋀² V_ℚ)^{Spin(V)_P}` is a line (Lemma 2.2.7, `2 ≠ 2n` as `n ≥ 2`)
  have hdim := lemma2_2_7_even P hd hP.nonIsotropic 2 even_two (by omega) (by omega)
  have : FiniteDimensional ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hinv
  · rw [finrank_span_singleton hne, hdim]

/-- (§1.3, TeX line 447, "by Proposition 2.4.4") `h = Ξ_P^♯` is ample on `X × X̂`: in the model
`H¹(X × X̂, ℚ) = V_ℚ ≅ ℚ^{4n}` (`coordV`), with the standard complex structure `-I_{V_ℝ}` of
`X × X̂` (`I_{V_ℝ} = productStructure n J` is the paper's convention, the negative of the standard
one), `h` is ample in the sense of `IsAmple`. (Checked numerically for `n = 1, 2, 3`.) -/
theorem intro_hClass_isAmple (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n)
    (hΘ : IsAmple n J Θ) (hn : 0 < n) (d : ℚ) (hd : 0 < d) :
    IsAmple (2 * n)
      ((coordV ℝ n).toLinearMap ∘ₗ (-productStructure n J) ∘ₗ (coordV ℝ n).symm.toLinearMap)
      (ExteriorAlgebra.map (coordV ℚ n).toLinearMap
        ((PAmple hΘ hn d hd).hClass (PAmple_isCompl hΘ hn d hd))) := by
  set P := PAmple hΘ hn d hd with hP_def
  set hW := PAmple_isCompl hΘ hn d hd
  have hP : Assumption2_4_1 P J := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  set I := productStructure n J with hI_def
  have hIc : IsComplexStructure I := isComplexStructure_productStructure J hJ
  have hh : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  -- the real double contractions of `h` are `Ξ_P` on `V_ℝ`
  have hstar : ∀ x y : V ℝ n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0)
      (pairing ℝ n y) (contractLeft (Q := 0) (pairing ℝ n x) (bcExt ℚ ℝ n (P.hClass hW)))) =
        P.XiR hP.isCompl x y :=
    main_dc_eq_of_rational n _ _ fun u v => by
      rw [main_dc_bcExt, P.hClass_spec hW, P.XiR_bcV hP.isCompl]; rfl
  -- the adjoint of `I` for `(·,·)_V` is `-I`
  have hadjI : ∀ x, pairing ℝ n x ∘ₗ I = pairing ℝ n (-I x) := fun x => LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, map_neg, LinearMap.neg_apply,
      pairing_productStructure_left J hJ x z, neg_neg]
  refine ⟨?_, fun a ha => ?_⟩
  · -- `h` is of type `(1,1)`: `I` fixes `h_ℝ` (`Ξ_P` is of type `(1,1)`, §2.4)
    rw [show (coordV ℝ n).toLinearMap ∘ₗ (-productStructure n J) ∘ₗ
        (coordV ℝ n).symm.toLinearMap = transportEnd n (-I) from rfl,
      map_mem_hodgeClassesX_iff n I hIc 1, mem_hodgeClassesV_one_iff I hIc _ hh]
    refine main_eq_of_pairing_dc ℝ n (main_map_mem_exteriorPower _ 2 (main_bcExt_mem ℚ ℝ n 2 hh))
      (main_bcExt_mem ℚ ℝ n 2 hh) fun x y => ?_
    rw [main_dc_map, hadjI, hadjI, hstar, hstar, map_neg, map_neg, LinearMap.neg_apply, neg_neg,
      P.XiR_productStructure J hP]
  · -- Kähler positivity: `⟪h, a ∧ (a ∘ (-I))⟫ = Ξ_P(x, I x) = g_I(x, x) = -g_P(x, x) > 0`
    -- (Proposition 2.4.4)
    obtain ⟨x, hx⟩ := main_pairing_surjective ℝ n (a ∘ₗ (coordV ℝ n).toLinearMap)
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply ha
      refine LinearMap.ext fun w => ?_
      have := congrArg (fun b : Module.Dual ℝ (V ℝ n) => b ((coordV ℝ n).symm w)) hx
      simpa using this.symm
    have ha' : (a ∘ₗ ((coordV ℝ n).toLinearMap ∘ₗ (-productStructure n J) ∘ₗ
        (coordV ℝ n).symm.toLinearMap)) ∘ₗ (coordV ℝ n).toLinearMap = pairing ℝ n (I x) := by
      refine LinearMap.ext fun z => ?_
      have hz := congrArg (fun b : Module.Dual ℝ (V ℝ n) => b (-(I z))) hx
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.neg_apply] at hz ⊢
      rw [← hz, map_neg, pairing_productStructure_left J hJ x z]
    rw [main_bcS_map_coordV, main_eval2_map_coordV, ← hx, ha', hstar]
    have hpos := proposition2_4_4 n d hd hn J hJ Θ hΘ x hx0
    have hgI := congrArg (fun B : LinearMap.BilinForm ℝ (V ℝ n) => B x x)
      (P.gI_productStructure J hP)
    simp only [KSecant.gI, LinearMap.BilinForm.compRight_apply, LinearMap.neg_apply] at hgI
    rw [hgI]
    exact neg_pos.mpr hpos

/-- (§1.3, TeX lines 447–448) "Given an element `k ∈ K`, the rational endomorphism `η(k)` maps `h` to
`Nm(k) h`", `η(k)` acting on `H²(X × X̂, ℚ) = ⋀² V_ℚ` by `⋀² η_k`. (Checked numerically, `n = 3`.)
Stated for every `K`-secant `P` with `V_K = W₁ ⊕ W₂` (the paper: `P = P_Θ`). The paper gives no
proof. Here: `(f x, f y)_V = d (x, y)_V` (TeX line 1240) gives `Ξ_P(f x, f y) = d Ξ_P(x, y)`, the
condition on the polarization of [van Geemen, Def. 4.9], which gives `η(k)^* h = Nm(k) h`
(`s24b_map_η_hClass`, also used for the Weil-type period domain in `weilDomain_eq_image_OmegaP`). -/
theorem intro_eta_hClass {d : ℚ} (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (k : Kd d) :
    ExteriorAlgebra.map (P.η hW k) (P.hClass hW) = (Kd.Nm d k : ℚ) • P.hClass hW :=
  -- `Ξ_P(f x, f y) = (f² x, f y)_V = d (f x, y)_V = d Ξ_P(x, y)`
  s24b_map_η_hClass P hd hW (fun x y => P.pairing_fη_fη hW (P.fη hW x) y) k

/-! ## Theorem 1.4.1 -/

section Theorem141

variable {J : Module.End ℝ (H1 ℝ 3)} {d : ℚ}

theorem pos_of_three_le (hd3 : 3 ≤ d) : 0 < d := by linarith

/-- **Theorem 1.4.1(1)** (`main-theorem-introduction`). The line `ℙ` in `ℙ(H^{even}(X, ℚ))` through
`ch(F₁^∨)` and `ch(F₂)` intersects the spinor variety at the two complex conjugate pure spinors
`exp(u)` and `exp(ū)` defined over `K = ℚ(√-d)`.

Model: `ch(F₂) = w`, `ch(F₁^∨) = τ(w)`, `w = chF1 d`. Stated: the plane spanned by `τ(w)` and `w` is
the plane `P` of `P_Θ` (whose `K`-span is `P_K = span_K{exp(u), exp(ū)}`), and over `ℂ` it is a
transversal secant meeting the even spinor variety exactly in the lines of `exp(±√-dΘ)`
(`IsTransversalSecant`, Lemma 10.1.1). -/
theorem theorem1_4_1_1 (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd3 : 3 ≤ d) :
    Submodule.span ℚ {tau ℚ 3 (chF1 d), chF1 d} = (PJac d hΘ (pos_of_three_le hd3)).Pℚ ∧
      Submodule.span (Kd d) {bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)), bcS ℚ (Kd d) 3 (chF1 d)} =
        (PJac d hΘ (pos_of_three_le hd3)).PK ∧
      IsTransversalSecant ℂ 3
        (Submodule.span ℂ {bcS ℚ ℂ 3 (tau ℚ 3 (chF1 d)), bcS ℚ ℂ 3 (chF1 d)})
        (IsNilpotent.exp (sqrtNeg d • bcS ℚ ℂ 3 (ThetaStd ℚ 3)))
        (IsNilpotent.exp (-(sqrtNeg d • bcS ℚ ℂ 3 (ThetaStd ℚ 3)))) := by
  have hd := pos_of_three_le hd3
  set P := PJac d hΘ hd with hP_def
  obtain ⟨hwαβ, hw, hτw⟩ := lemma8_2_1 d hΘ hd
  -- `τ(ch F₁) = α - β` (`τ = 1` on `α`, `τ = -1` on `Θ` and on `[pt]`)
  have hτβ : tau ℚ 3 (betaJac d) = -betaJac d := by
    have hpt : pt ℚ 3 ∈ ⋀[ℚ]^6 (H1 ℚ 3) := by
      rw [pt, basisS, ExteriorAlgebra.basis_apply_ofCard _ (s := Finset.univ) rfl]
      exact ExteriorAlgebra.ιMulti_range ℚ _ (Set.mem_range_self _)
    have h1 : tau ℚ 3 (ThetaStd ℚ 3) = -ThetaStd ℚ 3 := by
      rw [show tau ℚ 3 (ThetaStd ℚ 3) = CliffordAlgebra.reverse (Q := 0) (ThetaStd ℚ 3) from rfl,
        main_reverse_of_mem (main_ThetaStd_mem ℚ 3)]; norm_num
    have h2 : tau ℚ 3 (pt ℚ 3) = -pt ℚ 3 := by
      rw [show tau ℚ 3 (pt ℚ 3) = CliffordAlgebra.reverse (Q := 0) (pt ℚ 3) from rfl,
        main_reverse_of_mem hpt, show Nat.choose 6 2 = 15 from rfl]
      norm_num
    rw [betaJac, map_sub, map_smul, h1, h2, smul_neg, neg_sub_neg, neg_sub]
  have hτw' : tau ℚ 3 (chF1 d) = alphaJac d - betaJac d := by
    rw [hwαβ, map_add, tau_alphaJac, hτβ, sub_eq_add_neg]
  -- (1) the line through `ch(F₁^∨)` and `ch(F₂)` is `P` (Lemma 8.2.1)
  have h1 : Submodule.span ℚ {tau ℚ 3 (chF1 d), chF1 d} = P.Pℚ := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hτw, hw⟩
    · rw [PJac_Pℚ_eq d hΘ hd, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · rw [show alphaJac d = (2 : ℚ)⁻¹ • (tau ℚ 3 (chF1 d) + chF1 d) by
          rw [hτw', hwαβ]; module]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (Or.inl rfl))
          (Submodule.subset_span (Or.inr rfl)))
      · rw [show betaJac d = (2 : ℚ)⁻¹ • (chF1 d - tau ℚ 3 (chF1 d)) by
          rw [hτw', hwαβ]; module]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (Or.inr rfl))
          (Submodule.subset_span (Or.inl rfl)))
  -- the `K`- and `ℂ`-spans of the base changes of a rational set
  have hspanK : ∀ t : Set (S ℚ 3), Submodule.span (Kd d) (bcS ℚ (Kd d) 3 '' ↑(Submodule.span ℚ t))
      = Submodule.span (Kd d) (bcS ℚ (Kd d) 3 '' t) := fun t => by
    rw [show ⇑(bcS ℚ (Kd d) 3) = ⇑(bcS ℚ (Kd d) 3).toLinearMap from rfl, ← Submodule.map_coe,
      Submodule.map_span, Submodule.span_span_of_tower]
  -- (1) over `K`: `P_K = span_K{exp(u), exp(ū)}`
  have h2 : Submodule.span (Kd d) {bcS ℚ (Kd d) 3 (tau ℚ 3 (chF1 d)), bcS ℚ (Kd d) 3 (chF1 d)} =
      P.PK := by
    rw [← P.span_bcS_Pℚ, ← h1, hspanK, Set.image_pair]
  refine ⟨h1, h2, ?_⟩
  -- over `ℂ`: the secant through `exp(±√-d Θ)`
  set u := sqrtNeg d • bcS ℚ ℂ 3 (ThetaStd ℚ 3) with hu_def
  have hΘc : bcS ℚ ℂ 3 (ThetaStd ℚ 3) = ThetaStd ℂ 3 := main_bcS_ThetaStd ℚ 3 ℂ
  have hu : u ∈ ⋀[ℂ]^2 (H1 ℂ 3) := by
    rw [hu_def, hΘc]; exact Submodule.smul_mem _ _ (main_ThetaStd_mem ℂ 3)
  have hu' : -u ∈ ⋀[ℂ]^2 (H1 ℂ 3) := Submodule.neg_mem _ hu
  have hpure₁ := main_exp_isEvenPureSpinor ℂ 3 hu
  have hpure₂ := main_exp_isEvenPureSpinor ℂ 3 hu'
  have hsd : sqrtNeg d ≠ 0 := by
    intro h
    have := sqrtNeg_sq hd.le
    rw [h] at this
    have : (d : ℂ) = 0 := by linear_combination this
    exact hd.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (contractOne ℂ 3 u) := by
    intro y y' h
    simp only [hu_def, hΘc, main_contractOne_smul] at h
    exact main_contractOne_ThetaStd_injective ℂ 3 (smul_right_injective _ hsd h)
  have hW := main_ann_exp_inf ℂ 3 hu hinj
  -- the plane: base change of `P_K = span_K{exp(u), exp(ū)}` to `ℂ`
  have htower : ∀ x : S ℚ 3, bcS (Kd d) ℂ 3 (bcS ℚ (Kd d) 3 x) = bcS ℚ ℂ 3 x := fun x => by
    have : ((bcS (Kd d) ℂ 3).restrictScalars ℚ).comp (bcS ℚ (Kd d) 3) = bcS ℚ ℂ 3 := by
      refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, AlgHom.restrictScalars_apply, main_bcS_ι]
      congr 1
    exact congrArg (fun g => g x) this
  have hbcK : ∀ x : S (Kd d) 3, ∀ c : Kd d,
      bcS (Kd d) ℂ 3 (c • x) = (c : ℂ) • bcS (Kd d) ℂ 3 x := fun x c => by
    rw [map_smul]; rfl
  have hu₁ : bcS (Kd d) ℂ 3 P.u₁ = IsNilpotent.exp u := by
    have hnil : IsNilpotent (uΘ 3 d (ThetaStd ℚ 3)) :=
      main_isNilpotent_of_mem two_ne_zero (uΘ_mem 3 d _ hΘ.mem_exteriorPower_two)
    show bcS (Kd d) ℂ 3 (expUS 3 d (ThetaStd ℚ 3)) = _
    rw [expUS, IsNilpotent.map_exp hnil, uΘ, hbcK, htower]; rfl
  have hu₂ : bcS (Kd d) ℂ 3 P.u₂ = IsNilpotent.exp (-u) := by
    have hnil : IsNilpotent (-uΘ 3 d (ThetaStd ℚ 3)) :=
      main_isNilpotent_of_mem two_ne_zero
        (Submodule.neg_mem _ (uΘ_mem 3 d _ hΘ.mem_exteriorPower_two))
    rw [PTheta_u₂, IsNilpotent.map_exp hnil, map_neg, uΘ, hbcK, htower, hu_def]
    rfl
  have hspanC : ∀ t : Set (S (Kd d) 3),
      Submodule.span ℂ (bcS (Kd d) ℂ 3 '' ↑(Submodule.span (Kd d) t)) =
        Submodule.span ℂ (bcS (Kd d) ℂ 3 '' t) := fun t => by
    rw [show ⇑(bcS (Kd d) ℂ 3) = ⇑(bcS (Kd d) ℂ 3).toLinearMap from rfl, ← Submodule.map_coe,
      Submodule.map_span, Submodule.span_span_of_tower]
  have hplane : Submodule.span ℂ {bcS ℚ ℂ 3 (tau ℚ 3 (chF1 d)), bcS ℚ ℂ 3 (chF1 d)} =
      Submodule.span ℂ {IsNilpotent.exp u, IsNilpotent.exp (-u)} := by
    rw [← htower, ← htower, ← Set.image_pair, ← hspanC, h2, KSecant.PK, hspanC, Set.image_pair,
      hu₁, hu₂]
  -- `exp(u)` and `exp(-u)` are linearly independent (their annihilators are transversal)
  have hne : ∀ v : S ℂ 3, v ∈ ⋀[ℂ]^2 (H1 ℂ 3) → IsNilpotent.exp v ≠ 0 := fun v hv h0 => by
    have := congrArg ExteriorAlgebra.algebraMapInv h0
    rw [IsNilpotent.map_exp (main_isNilpotent_of_mem two_ne_zero hv),
      main_algebraMapInv_of_mem two_ne_zero hv, IsNilpotent.exp_zero, map_zero] at this
    exact one_ne_zero this
  have hli : LinearIndependent ℂ ![IsNilpotent.exp u, IsNilpotent.exp (-u)] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.mp hab).resolve_right (hne u hu), rfl⟩
    exfalso
    have hab' : IsNilpotent.exp (-u) = (-a / b) • IsNilpotent.exp u := by
      have h' : b • IsNilpotent.exp (-u) = -(a • IsNilpotent.exp u) :=
        eq_neg_of_add_eq_zero_right hab
      calc IsNilpotent.exp (-u) = b⁻¹ • (b • IsNilpotent.exp (-u)) := by
            rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = (-a / b) • IsNilpotent.exp u := by
            rw [h', smul_neg, smul_smul, ← neg_smul]; congr 1; ring
    have hc : -a / b ≠ 0 := by
      intro hc; rw [hc, zero_smul] at hab'; exact hne (-u) hu' hab'
    have hann : ann ℂ 3 (IsNilpotent.exp (-u)) = ann ℂ 3 (IsNilpotent.exp u) := by
      rw [hab', ann, ann]
      have : mOf ℂ 3 ((-a / b) • IsNilpotent.exp u) = (-a / b) • mOf ℂ 3 (IsNilpotent.exp u) := by
        simp [mOf, LinearMap.smul_comp]
      rw [this, LinearMap.ker_smul _ _ hc]
    rw [hann, inf_idem] at hW
    have := hpure₁.2.2
    rw [hW, finrank_bot] at this
    norm_num at this
  refine ⟨hplane, hli, hpure₁, hpure₂, hW, fun v hv hvpure => ?_⟩
  rw [hplane, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, rfl⟩ := hv
  rcases chevalley_III_1_12 ℂ 3 (by norm_num) _ _ hpure₁ hpure₂ hW a b hvpure with ha | hb
  · right
    rw [ha, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · left
    rw [hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The sheaf `E` of Theorem 1.4.1(2) has rank `8d` (a compared theorem of `Challenge.lean`, for
every `d`): the degree-`0` part of `ch(E) = τ(φ(w ⊗ w))` is that of `φ(w ⊗ w)` (`τ` fixes it), which
is `8d` (`lemma8_3_1_rank_eq`). -/
theorem rank_chE (d : ℚ) : ExteriorAlgebra.algebraMapInv (chE d) = 8 * d := by
  rw [chE, main_tauExt_apply, main_algebraMapInv_reverse]
  exact lemma8_3_1_rank_eq d

/-- **Theorem 1.4.1(2)** (`main-theorem-introduction`), cohomological part: the rank of `E` is `8d`
(the rank of `ch(E) = τ(φ(w ⊗ w))`, `rank_chE`). The rest of (2) (`Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]`, `E`
simple reflexive) is sheaf-theoretic. (Checked numerically for `d = 1, 2, 3, 5, 7`.)

Departure from the paper (reason 3): the paper reads the rank off the sheaf, `E ≅ 𝒢₁^*` for the
reflexive sheaf `𝒢₁ = R¹π_{23,*}(π₁^*F₁ ⊗ 𝓕₂)` of rank `8d` (Proposition 9.2.2, TeX lines
5455–5463); the model has no sheaves, and computes the rank as the degree-`0` part of `ch(E)`. -/
theorem theorem1_4_1_2_rank : rankExt ℚ 3 (chE d) = 8 * d := by
  rw [main_rankExt_apply]
  exact rank_chE d

/-- **Theorem 1.4.1(3)** (`main-theorem-introduction`). The characteristic class
`κ(E) = exp(-c₁(E)/rank(E)) ch(E)` remains of Hodge type under every deformation of
`(X × X̂, η, h)` as a polarized abelian sixfold of Weil type: `κ(E)` is a Hodge class for every
complex structure `I` in the period domain `Ω_P` of `P = P_Θ`. -/
theorem theorem1_4_1_3 (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd3 : 3 ≤ d)
    (I : Module.End ℝ (V ℝ 3))
    (hI : I ∈ (PJac d hΘ (pos_of_three_le hd3)).OmegaP (PJac_isCompl d hΘ (pos_of_three_le hd3))) :
    kappa ℚ 3 (chE d) ∈ hodgeRingV 3 I := by
  have hd := pos_of_three_le hd3
  have hP := PJac_assumption2_4_1 d hJ hΘ hd
  -- `ch(Φ(F₂ ⊠ F₁)) = φ(w ⊗ w) = φ(w ⊗ τ(τ w))` with `w = ch F₂`, `τ w = ch F₁^∨` in `P`
  -- (Lemma 8.2.1)
  obtain ⟨-, hw, hτw⟩ := lemma8_2_1 d hΘ hd
  have hsec : phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) =
      secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d)) := by
    rw [secantSqClass, tau_tau]
  have hr : rankExt ℚ 3 (secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d))) ≠ 0 := by
    rw [← hsec]; exact lemma8_3_1_rank d hd
  -- Lemma 6.2.3 for `k = 0` (Remark 6.2.4): `κ(Φ(F₂ ⊠ F₁))` is `Spin(V)_P`-invariant, hence of
  -- Hodge type on `Ω_P` (Corollary 4.0.4)
  have hinv := (remark6_2_4 _ J hP (by norm_num) (tau ℚ 3 (chF1 d)) (chF1 d) hτw hw hr).1
  have hhodge := corollary4_0_4 _ J hP _ hinv I hI
  -- `κ(E) = κ(τ ch Φ(F₂ ⊠ F₁)) = τ κ(Φ(F₂ ⊠ F₁))`
  rw [chE, main_kappa_reverse, hsec]
  exact main_tau_mem_hodgeRingV hhodge

/-- Corollary 1.3.2 applied to the sheaf `E` of Theorem 1.4.1, as in the paragraph before
Theorem 1.5.1 (TeX 570: "`κ(E)` remains of Hodge type over the locus, where `(X × X̂, η, h)` deforms
as an abelian variety of Weil-type, by Corollary 1.3.2"): `κ(E)` is a Hodge class for every complex
structure `I` in the period domain `Ω_P` of `P = P_Θ`. The inputs are Lemma 8.2.1
(`ch F₁, τ ch F₁ ∈ P`) and the rank `8d ≠ 0` of `E`. -/
theorem main_kappa_chE_hodge (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd3 : 3 ≤ d) (I : Module.End ℝ (V ℝ 3))
    (hI : I ∈ (PJac d hΘ (pos_of_three_le hd3)).OmegaP (PJac_isCompl d hΘ (pos_of_three_le hd3))) :
    kappa ℚ 3 (chE d) ∈ hodgeRingV 3 I := by
  have hd := pos_of_three_le hd3
  have hP := PJac_assumption2_4_1 d hJ hΘ hd
  -- `ch(Φ(F₂ ⊠ F₁)) = φ(w₁ ⊗ τ w₂)` with `w₁ = ch F₁`, `w₂ = τ ch F₁` in `P` (Lemma 8.2.1)
  obtain ⟨-, hw, hτw⟩ := lemma8_2_1 d hΘ hd
  have hsec : phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d) =
      secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d)) := by
    rw [secantSqClass, tau_tau]
  have hr : rankExt ℚ 3 (secantSqClass ℚ 3 (chF1 d) (tau ℚ 3 (chF1 d))) ≠ 0 := by
    rw [← hsec]; exact lemma8_3_1_rank d hd
  -- Corollary 1.3.2: `κ(Φ(F₂ ⊠ F₁))` remains of Hodge type on `Ω_P`
  have hhodge := corollary1_3_2_hodge _ J hP (chF1 d) (tau ℚ 3 (chF1 d)) hw hτw hr I hI
  -- `κ(E) = κ(τ ch Φ(F₂ ⊠ F₁)) = τ κ(Φ(F₂ ⊠ F₁))`
  rw [chE, main_kappa_reverse, hsec]
  exact main_tau_mem_hodgeRingV hhodge

theorem main_kappa3E_eq_neg (d : ℚ) :
    kappa3E d = -kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) := by
  have h6 := main_projDeg_mem ℚ 3 6 (kappa ℚ 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)))
  rw [kappa3E, kappaDeg, kappaDeg, chE, main_kappa_reverse, main_proj_reverse, main_tauExt_apply,
    main_reverse_of_mem h6, show (6 : ℕ).choose 2 = 15 from rfl]
  norm_num

/-- `ĤW_P` consists of `Spin(V)_P`-invariant classes (Proposition 6.4.1(1): it is the projection
of `φ'(HW_P)`, which is fixed by `Spin(V)_P` acting by `ρ'`, and `ρ'` induces `ρ` on the graded
pieces). -/
theorem main_hwPlane_le_invQ {n : ℕ} {d : ℚ} (hd : 0 < d) (hn : 0 < n)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    (PAmple hΘ hn d hd).hwPlane ≤ (PAmple hΘ hn d hd).invQ (2 * n) := by
  set P := PAmple hΘ hn d hd with hP_def
  have hP := PTheta_assumption2_4_1 n d hd hn J hJ Θ hΘ
  obtain ⟨-, hwt, -, hproj⟩ := proposition6_4_1_1 P J hP
  -- `P ⊗ P` is fixed pointwise by `Spin(V_ℚ)_P` (acting by `m ⊗ m`)
  have hPℚ := equation2_4_5 n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)
  have hre : reS n d P.u₁ ∈ P.Pℚ := by
    rw [hPℚ]; exact Submodule.subset_span (Set.mem_insert _ _)
  have him : imS n d P.u₁ ∈ P.Pℚ := by
    rw [hPℚ]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hHWP : ∀ g ∈ P.spinPℚ, ∀ t ∈ P.HWP,
      TensorProduct.map (m ℚ n (g : C ℚ n)) (m ℚ n (g : C ℚ n)) t = t := by
    intro g hg t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [map_sub, map_smul, P.map_m_tmul_of_mem_Pℚ g hg _ _ hre hre,
          P.map_m_tmul_of_mem_Pℚ g hg _ _ him him]
      · rw [map_add, P.map_m_tmul_of_mem_Pℚ g hg _ _ hre him,
          P.map_m_tmul_of_mem_Pℚ g hg _ _ him hre]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  intro x hx
  rw [← hproj] at hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine ⟨main_projDeg_mem ℚ n (2 * n) y, fun g hg => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hy
  have hfix : rhoPrime ℚ n g (phiPrime ℚ n t) = phiPrime ℚ n t := by
    rw [rhoPrime, LinearMap.comp_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (phiPrimeInv ℚ n), phiPrimeInv_comp_phiPrime, LinearMap.id_apply,
      hHWP g (Subgroup.mem_inf.mp hg).2 t ht]
  rw [← rhoPrime_projDeg ℚ n g (2 * n) (hwt.1 hy), hfix]

/-- There is `k ∈ K` with `k⁶ ∉ ℚ` (`k = 1 + √-d` or `2 + √-d`). -/
theorem main_exists_pow_six_not_rat {d : ℚ} (hd : 0 < d) :
    ∃ k : Kd d, ∀ q : ℚ, k ^ 6 ≠ algebraMap ℚ (Kd d) q := by
  set s := Kd.sqrtNeg d
  have hs : s ^ 2 = -(d : Kd d) := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, Subfield.coe_neg, SubfieldClass.coe_ratCast]
    exact sqrtNeg_sq hd.le
  -- `(c + s)⁶ = A + B s`
  have hpow : ∀ c : ℚ, ((c : Kd d) + s) ^ 6 =
      (((c ^ 2 - d) ^ 3 - 3 * (c ^ 2 - d) * (2 * c) ^ 2 * d : ℚ) : Kd d) +
        (((2 * c) * (3 * (c ^ 2 - d) ^ 2 - (2 * c) ^ 2 * d) : ℚ) : Kd d) * s := by
    intro c
    have h3 : s ^ 3 = -(d : Kd d) * s := by rw [pow_succ, hs]
    have h4 : s ^ 4 = (d : Kd d) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]; ring
    have h5 : s ^ 5 = (d : Kd d) ^ 2 * s := by rw [pow_succ, h4]
    have h6 : s ^ 6 = -(d : Kd d) ^ 3 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hs]; ring
    push_cast
    linear_combination (15 * (c : Kd d) ^ 4) * hs + (20 * (c : Kd d) ^ 3) * h3 +
      (15 * (c : Kd d) ^ 2) * h4 + (6 * (c : Kd d)) * h5 + h6
  -- `s ∉ ℚ` (`s² = -d < 0`)
  have hsq : ∀ q : ℚ, s ≠ algebraMap ℚ (Kd d) q := by
    intro q hq
    have : ((q : Kd d)) ^ 2 = -(d : Kd d) := by rw [← hs, hq, eq_ratCast]
    have h' : q ^ 2 = -d := by exact_mod_cast this
    nlinarith [sq_nonneg q]
  -- if `(c + s)⁶ ∈ ℚ` then the coefficient `B` of `s` vanishes
  have hB : ∀ c q : ℚ, ((c : Kd d) + s) ^ 6 = algebraMap ℚ (Kd d) q →
      (2 * c) * (3 * (c ^ 2 - d) ^ 2 - (2 * c) ^ 2 * d) = 0 := by
    intro c q hcq
    by_contra hB
    set A : ℚ := (c ^ 2 - d) ^ 3 - 3 * (c ^ 2 - d) * (2 * c) ^ 2 * d
    set B : ℚ := (2 * c) * (3 * (c ^ 2 - d) ^ 2 - (2 * c) ^ 2 * d)
    rw [hpow, eq_ratCast] at hcq
    have hBs : (B : Kd d) * s = ((q - A : ℚ) : Kd d) := by
      push_cast; linear_combination hcq
    have hB' : (B : Kd d) ≠ 0 := by exact_mod_cast hB
    apply hsq ((q - A) / B)
    rw [eq_ratCast]
    push_cast
    rw [eq_div_iff hB', mul_comm, hBs]
    push_cast; ring
  by_cases h1 : ∀ q : ℚ, (((1 : ℚ) : Kd d) + s) ^ 6 ≠ algebraMap ℚ (Kd d) q
  · exact ⟨_, h1⟩
  · refine ⟨((2 : ℚ) : Kd d) + s, fun q hq => ?_⟩
    simp only [not_forall, not_not] at h1
    obtain ⟨q₁, hq₁⟩ := h1
    have e1 := hB 1 q₁ hq₁
    have e2 := hB 2 q hq
    nlinarith [e1, e2]

theorem main_theorem1_4_1_4_finrank {J : Module.End ℝ (H1 ℝ 3)} {d : ℚ}
    (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd3 : 3 ≤ d) :
    Disjoint (Submodule.span ℚ
        {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3})
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane ∧
      Module.finrank ℚ (Submodule.span ℚ
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3} ⊔
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane : Submodule ℚ (ExtV ℚ 3)) = 3 := by
  have hd := pos_of_three_le hd3
  set P := PJac d hΘ hd with hP_def
  set hW := PJac_isCompl d hΘ hd
  have hP := PJac_assumption2_4_1 d hJ hΘ hd
  -- `h³ ≠ 0` (Lemma 8.3.1)
  have hh3 : P.hClass hW ^ 3 ≠ 0 := (lemma8_3_1 d hΘ hd).ne_zero 0
  -- `h³ ∉ ĤW_P`: `η(√-d)` acts on `h³` by `Nm(√-d)³ = d³` and on `ĤW_P` by `(√-d)⁶ = -d³`
  have hnot : P.hClass hW ^ 3 ∉ P.hwPlane := by
    intro hmem
    have h1 := main_η_sqrtNeg_hwPlane P hd hW hmem
    have hNm : Kd.Nm d (Kd.sqrtNeg d) = d := by simpa using Kd_Nm d hd 0 1
    rw [map_pow, intro_eta_hClass P hd hW, smul_pow, hNm] at h1
    have h2 : (2 * d ^ 3) • P.hClass hW ^ 3 = 0 := by
      rw [show 2 * d ^ 3 = d ^ 3 - (-d) ^ 3 by ring, sub_smul, h1, sub_self]
    exact hh3 ((smul_eq_zero.mp h2).resolve_left (by positivity))
  have hdisj : Disjoint (Submodule.span ℚ {P.hClass hW ^ 3}) P.hwPlane :=
    ((Submodule.disjoint_span_singleton' hh3).mpr hnot).symm
  refine ⟨hdisj, ?_⟩
  have : FiniteDimensional ℚ (ExtV ℚ 3) := Module.Finite.of_basis (basisExt ℚ 3)
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℚ {P.hClass hW ^ 3}) P.hwPlane
  rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hh3,
    KSecant.finrank_hwPlane P J hP] at this
  omega

/-- **Theorem 1.4.1(4)** (`thm-item-K-translates-of-kappa-3-and-h-cube-span-HW`). The
`η(K)`-translates of the graded summand `κ₃(E)` of `κ(E)` in `H^{3,3}(X × X̂, ℚ)`, together with `h³`,
span the `3`-dimensional subspace `ℚh³ ⊕ ĤW_P`.

Model: `η(k)` acts on `H⁶(X × X̂, ℚ) = ⋀⁶ V_ℚ` by `⋀ η_k` (`ExteriorAlgebra.map`, (2.2.4));
`h = Ξ_P^♯` (`hClass`); `ĤW_P = hwPlane`; `κ₃(E) = kappa3E d`. The dimension is
`theorem1_4_1_4_finrank`. -/
theorem theorem1_4_1_4 (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd3 : 3 ≤ d) :
    Submodule.span ℚ
        (Set.range (fun k : Kd d =>
            ExteriorAlgebra.map ((PJac d hΘ (pos_of_three_le hd3)).η
              (PJac_isCompl d hΘ (pos_of_three_le hd3)) k) (kappa3E d)) ∪
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3}) =
      Submodule.span ℚ
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3} ⊔
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane := by
  have hd := pos_of_three_le hd3
  set P := PJac d hΘ hd with hP_def
  set hW := PJac_isCompl d hΘ hd
  have hP := PJac_assumption2_4_1 d hJ hΘ hd
  have hfin := main_theorem1_4_1_4_finrank hJ hΘ hd3
  have : FiniteDimensional ℚ (ExtV ℚ 3) := Module.Finite.of_basis (basisExt ℚ 3)
  set h3 := P.hClass hW ^ 3 with hh3_def
  have hh : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ 3) := formToExt2_mem ℚ 3 _
  obtain ⟨hinvh3, hinvκ'⟩ := lemma8_3_1_invariant d hΘ hd
  -- `(⋀⁶ V_ℚ)^{Spin(V)_P} = ℚh³ ⊕ ĤW_P` (Lemma 2.2.7: dimension `3`; Proposition 6.4.1)
  have hinvQ : P.invQ (2 * 3) = Submodule.span ℚ {h3} ⊔ P.hwPlane := by
    have hle : Submodule.span ℚ {h3} ⊔ P.hwPlane ≤ P.invQ (2 * 3) :=
      sup_le (by rw [Submodule.span_le, Set.singleton_subset_iff]
                 exact ⟨main_pow_mem hh 3, hinvh3⟩)
        (main_hwPlane_le_invQ hd (by norm_num) J hJ (ThetaStd ℚ 3) hΘ)
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (by rw [hfin.2, lemma2_2_7_middle P hd hP.nonIsotropic])).symm
  -- `κ₃(E) = -κ₃(Φ(F₁ ⊠ F₁))` is `Spin(V)_P`-invariant and independent of `h³` (Lemma 8.3.1)
  have hκ : kappa3E d ∈ P.invQ (2 * 3) := by
    rw [main_kappa3E_eq_neg]
    exact Submodule.neg_mem _ ⟨main_projDeg_mem ℚ 3 _ _, hinvκ'⟩
  have hκnot : kappa3E d ∉ Submodule.span ℚ {h3} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [main_kappa3E_eq_neg] at hc
    have := LinearIndependent.pair_iff.mp (lemma8_3_1 d hΘ hd) c 1
      (by rw [one_smul, hc, neg_add_cancel])
    exact one_ne_zero this.2
  -- `κ₃(E) = c h³ + w` with `0 ≠ w ∈ ĤW_P`
  rw [hinvQ] at hκ
  obtain ⟨y, hy, w, hw, hκyw⟩ := Submodule.mem_sup.mp hκ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hw0 : w ≠ 0 := by
    intro h0; apply hκnot
    rw [← hκyw, h0, add_zero]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- `η_k h³ = Nm(k)³ h³`
  have hηh3 : ∀ k, ExteriorAlgebra.map (P.η hW k) h3 = (Kd.Nm d k) ^ 3 • h3 := fun k => by
    rw [hh3_def, map_pow, intro_eta_hClass P hd hW, smul_pow]
  set Sp := Submodule.span ℚ
    (Set.range (fun k : Kd d => ExteriorAlgebra.map (P.η hW k) (kappa3E d)) ∪ {h3}) with hSp
  have hh3S : h3 ∈ Sp := Submodule.subset_span (Or.inr rfl)
  have hηw : ∀ k, ExteriorAlgebra.map (P.η hW k) w ∈ Sp := fun k => by
    have h1 : ExteriorAlgebra.map (P.η hW k) w =
        ExteriorAlgebra.map (P.η hW k) (kappa3E d) - (c * (Kd.Nm d k) ^ 3) • h3 := by
      rw [← hκyw, map_add, map_smul, hηh3, smul_smul]; abel
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.subset_span (Or.inl ⟨k, rfl⟩))
      (Submodule.smul_mem _ _ hh3S)
  apply le_antisymm
  · -- the translates lie in `ℚh³ ⊕ ĤW_P`
    rw [Submodule.span_le]
    rintro _ (⟨k, rfl⟩ | rfl)
    · dsimp only
      rw [← hκyw, map_add, map_smul, hηh3, smul_smul]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        (main_map_η_mem_hwPlane P hd hW hw k)
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  · refine sup_le (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hh3S) ?_
    -- `w` and `η_{k₀} w` (`k₀⁶ ∉ ℚ`) span `ĤW_P`
    obtain ⟨k₀, hk₀⟩ := main_exists_pow_six_not_rat hd
    obtain ⟨w₁, hw₁, w₂, hw₂, hsum, hη⟩ := main_hwPlane_η P hd hW hw
    have hdisj : Disjoint (topWedge P.W₁ (2 * 3)) (topWedge P.W₂ (2 * 3)) := by
      have := (lemma2_2_7_K_indep P hd hP.nonIsotropic).pairwiseDisjoint
        (show (0 : Fin 3) ≠ 1 by decide)
      simpa [Function.onFun, main_pqPiece_left, main_pqPiece_right] using this
    have hsplit : ∀ a b : Kd d, a • w₁ + b • w₂ = 0 → a • w₁ = 0 ∧ b • w₂ = 0 := by
      intro a b hab
      have hmem : a • w₁ ∈ topWedge P.W₁ (2 * 3) ⊓ topWedge P.W₂ (2 * 3) :=
        ⟨Submodule.smul_mem _ _ hw₁, by
          rw [eq_neg_of_add_eq_zero_left hab]
          exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hw₂)⟩
      rw [hdisj.eq_bot, Submodule.mem_bot] at hmem
      exact ⟨hmem, by rwa [hmem, zero_add] at hab⟩
    have hσσ : ∀ z : Kd d, Kd.σ d (Kd.σ d z) = z := fun z => Subtype.ext (by simp)
    have hindep : LinearIndependent ℚ ![w, ExteriorAlgebra.map (P.η hW k₀) w] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have hbc := congrArg (bcExt ℚ (Kd d) 3) hab
      rw [map_add, map_smul, map_smul, hη, hsum, map_zero, ← algebraMap_smul (Kd d) a,
        ← algebraMap_smul (Kd d) b, smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
        ← add_smul, ← add_smul] at hbc
      obtain ⟨h1, h2⟩ := hsplit _ _ hbc
      by_cases hb : b = 0
      · subst hb
        simp only [zero_smul, add_zero] at hab
        exact ⟨(smul_eq_zero.mp hab).resolve_right hw0, rfl⟩
      exfalso
      have hb' : algebraMap ℚ (Kd d) b ≠ 0 := by simpa using hb
      have hw12 : w₁ ≠ 0 ∨ w₂ ≠ 0 := by
        by_contra! h
        apply hw0
        apply main_bcExt_injective ℚ (Kd d) 3
        rw [hsum, h.1, h.2, add_zero, map_zero]
      rcases hw12 with h0 | h0
      · have hc := (smul_eq_zero.mp h1).resolve_right h0
        apply hk₀ (-a / b)
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hc
      · have hc := (smul_eq_zero.mp h2).resolve_right h0
        apply hk₀ (-a / b)
        rw [eq_ratCast (algebraMap ℚ (Kd d)), eq_ratCast (algebraMap ℚ (Kd d))] at hc
        have := congrArg (Kd.σ d) hc
        rw [map_add, map_mul, map_pow, hσσ, map_ratCast, map_ratCast, map_zero] at this
        rw [eq_ratCast (algebraMap ℚ (Kd d))]
        have hb'' : ((b : ℚ) : Kd d) ≠ 0 := by simpa [eq_ratCast] using hb'
        push_cast
        field_simp
        linear_combination this
    have hspan : Submodule.span ℚ (Set.range ![w, ExteriorAlgebra.map (P.η hW k₀) w]) =
        P.hwPlane := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hw
        · exact main_map_η_mem_hwPlane P hd hW hw k₀
      · rw [finrank_span_eq_card hindep, Fintype.card_fin, KSecant.finrank_hwPlane P J hP]
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have := hηw 1
      rwa [P.η_one hd hW, show (1 : Module.End ℚ (V ℚ 3)) = LinearMap.id from rfl,
        ExteriorAlgebra.map_id, AlgHom.id_apply] at this
    · exact hηw k₀

/-- **Theorem 1.4.1(4)**, "the `3`-dimensional subspace `ℚh³ ⊕ ĤW_P`": the sum is direct and
three-dimensional. -/
theorem theorem1_4_1_4_finrank (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (hd3 : 3 ≤ d) :
    Disjoint (Submodule.span ℚ
        {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3})
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane ∧
      Module.finrank ℚ (Submodule.span ℚ
          {(PJac d hΘ (pos_of_three_le hd3)).hClass (PJac_isCompl d hΘ (pos_of_three_le hd3)) ^ 3} ⊔
        (PJac d hΘ (pos_of_three_le hd3)).hwPlane : Submodule ℚ (ExtV ℚ 3)) = 3 :=
  main_theorem1_4_1_4_finrank hJ hΘ hd3

/-- `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))`: `ch(E) = τ(ch Φ(F₂ ⊠ F₁))`, `τ` is a ring automorphism of `H^{ev}`
acting by `(-1)^i` on `H^{2i}`, so `κ(τ x) = τ(κ x)`. Relates Theorem 1.4.1(4) to Lemma 8.3.1 (which
is about `Φ(F₁ ⊠ F₁)`, with the same Chern character as `Φ(F₂ ⊠ F₁)`). -/
theorem kappa3E_eq_neg :
    kappa3E d = -kappaDeg ℚ 3 3 (phiOrlov ℚ 3 (chF1 d ⊗ₜ[ℚ] chF1 d)) :=
  main_kappa3E_eq_neg d

end Theorem141

end WeilClasses
