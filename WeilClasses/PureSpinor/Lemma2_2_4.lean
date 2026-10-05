module

public import WeilClasses.PureSpinor.CM
public import WeilClasses.PureSpinor.Lemma2_2_1
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection

/-!
# The action of `K` on `V_ℚ` and Lemma 2.2.4 (paper §2.2)

Setting of the paper (§2.2, before Lemma 2.2.4): `P ⊆ S⁺_ℚ` is a non-isotropic rational plane
meeting the spinor variety in two `σ`-conjugate points `ℓ₁, ℓ₂` (a `WeilClasses.KSecant` with
`¬ P.IsIsotropic`); then `W₁ ∩ W₂ = 0` by Lemma 2.2.1, i.e. `V_K = W₁ ⊕ W₂`
(`WeilClasses.KSecant.isCompl_of_not_isIsotropic`). The similarity group `Õ(V_ℚ)` (2.2.3)
(`WeilClasses.Otilde`) and the action `η_λ` (2.2.4) (`WeilClasses.KSecant.ηK` on `V_K`,
`WeilClasses.KSecant.η` on `V_ℚ`) are in `WeilClasses.PureSpinor.CM`.

## Statements

* `KSecant.range_bcV_eq`: "the subset `V_ℚ` of `V_K` is `{v₁ + σ(v₁) : v₁ ∈ W₁}`";
* `KSecant.σV_ηK`, `KSecant.ηK_bcV`: `η_λ` commutes with `σ` and leaves `V_ℚ` invariant;
* `KSecant.ηHom`: `η` as a ring homomorphism `K → End_ℚ(V_ℚ)` (the paper's homomorphism
  `η : K^× → GL(V_ℚ)` (2.2.4), "an embedding of `K` in `End(V_ℚ)`" in the table of notation), with
  `KSecant.ηHom_injective`;
* `KSecant.pairing_η`: `(η_λ(v), η_λ(v'))_V = Nm(λ)(v, v')_V` (proof of Lemma 2.2.4; used in §2.4
  for `f = η_{√-d}`);
* **Lemma 2.2.4** (`lemma2_2_4`): the centralizer of `ρ(Spin(V_ℚ)_P)` in `Õ(V_ℚ)` is `η(K^×)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers: the field `K`, coordinates of `V`, base change and `σ` -/

section Helpers

theorem s22b_σ_sqrtNeg (d : ℚ) : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp [Kd.sqrtNeg, WeilClasses.sqrtNeg]

theorem s22b_σ_σ {d : ℚ} (z : Kd d) : Kd.σ d (Kd.σ d z) = z := by
  apply Subtype.ext
  simp

theorem s22b_σ_algebraMap {d : ℚ} (q : ℚ) :
    Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp

theorem s22b_sqrtNeg_ne_zero {d : ℚ} (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := congrArg (fun z : Kd d => (z : ℂ)) h
  simp [Kd.sqrtNeg, WeilClasses.sqrtNeg] at this
  have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  linarith

/-- A `σ`-fixed element of `K` is rational. -/
theorem s22b_eq_algebraMap_of_σ_eq {d : ℚ} (hd : 0 < d) (z : Kd d) (h : Kd.σ d z = z) :
    z = algebraMap ℚ (Kd d) (Kd.ratPart d z) := by
  have hz := Kd.eq_ratPart_add_sqrtNegCoeff hd z
  set a := Kd.ratPart d z
  set b := Kd.sqrtNegCoeff d z
  have h2 : Kd.σ d z = algebraMap ℚ (Kd d) a - algebraMap ℚ (Kd d) b * Kd.sqrtNeg d := by
    conv_lhs => rw [hz]
    rw [map_add, map_mul, s22b_σ_algebraMap, s22b_σ_algebraMap, s22b_σ_sqrtNeg]; ring
  have h3 : (2 : Kd d) * algebraMap ℚ (Kd d) b * Kd.sqrtNeg d = 0 := by
    have := h2.symm.trans (h.trans hz)
    linear_combination -this
  have h4 : algebraMap ℚ (Kd d) b = 0 := by
    rcases mul_eq_zero.mp h3 with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 two_ne_zero
      · exact h6
    · exact absurd h5 (s22b_sqrtNeg_ne_zero hd)
  rw [hz, h4, zero_mul, add_zero]

variable {F : Type*} [Field F] {n : ℕ}

theorem s22b_dual_ext {θ θ' : Module.Dual F (H1 F n)} (h : ∀ i, θ (e F n i) = θ' (e F n i)) :
    θ = θ' :=
  (Pi.basisFun F (Fin (2 * n))).ext fun i => by simpa [e] using h i

theorem s22b_V_ext {v w : V F n} (h1 : ∀ i, v.1 (e F n i) = w.1 (e F n i))
    (h2 : ∀ i, v.2 i = w.2 i) : v = w :=
  Prod.ext (s22b_dual_ext h1) (funext h2)

@[simp]
theorem s22b_sum_smul_f_apply (c : Fin (2 * n) → F) (j : Fin (2 * n)) :
    (∑ i, c i • f F n i) (e F n j) = c j := by
  simp [f, e, Pi.single_apply]

variable [CharZero F]

theorem s22b_conjV_fst (c : F ≃+* F) (v : V F n) (i : Fin (2 * n)) :
    (conjV c n v).1 (e F n i) = c (v.1 (e F n i)) := by
  simp [conjV]

theorem s22b_conjV_snd (c : F ≃+* F) (v : V F n) (i : Fin (2 * n)) :
    (conjV c n v).2 i = c (v.2 i) := rfl

variable {F' : Type*} [Field F'] [CharZero F'] [Algebra F F']

theorem s22b_bcV_fst (w : V F n) (i : Fin (2 * n)) :
    (bcV F F' n w).1 (e F' n i) = algebraMap F F' (w.1 (e F n i)) :=
  s22b_sum_smul_f_apply (fun j => algebraMap F F' (w.1 (e F n j))) i

theorem s22b_bcV_snd (w : V F n) (i : Fin (2 * n)) :
    (bcV F F' n w).2 i = algebraMap F F' (w.2 i) := by
  simp [bcV, bcH1]

theorem s22b_bcV_injective : Function.Injective (bcV F F' n) := by
  intro v w h
  apply s22b_V_ext
  · intro i
    have := congrArg (fun x : V F' n => x.1 (e F' n i)) h
    simpa [s22b_bcV_fst] using this
  · intro i
    have := congrArg (fun x : V F' n => x.2 i) h
    simpa [s22b_bcV_snd] using this

theorem s22b_bcV_fst' (v : V F n) : (bcV F F' n v).1 = bcDual F F' n v.1 := rfl

theorem s22b_bcV_snd' (v : V F n) : (bcV F F' n v).2 = bcH1 F F' n v.2 := rfl

theorem s22b_bcDual_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  have hw : w = ∑ i, w i • e F n i := by
    ext j; simp [e, Pi.single_apply]
  conv_rhs => rw [hw]
  show (∑ i, algebraMap F F' (θ (e F n i)) • f F' n i) (bcH1 F F' n w) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul, map_mul, f, LinearMap.proj_apply, bcH1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

omit [CharZero F] [CharZero F'] in
theorem s22b_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) :=
  ExteriorAlgebra.lift_ι_apply F _ _ w

theorem s22b_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) :=
  ExteriorAlgebra.lift_ι_apply F _ _ v

theorem s22b_bcC_ι (v : V F n) : bcC F F' n (ι (Q F n) v) = ι (Q F' n) (bcV F F' n v) := by
  simp [bcC]

theorem s22b_bcC_involute (x : C F n) : bcC F F' n (involute x) = involute (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp [s22b_bcC_ι]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

theorem s22b_bcC_reverse (x : C F n) : bcC F F' n (reverse x) = reverse (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.reverse.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (C F' n), CliffordAlgebra.reverse.commutes]
  | ι v => simp [s22b_bcC_ι]
  | mul a b ha hb => simp [reverse.map_mul, ha, hb]
  | add a b ha hb => simp [ha, hb]

theorem s22b_bcC_star (x : C F n) : bcC F F' n (star x) = star (bcC F F' n x) := by
  rw [CliffordAlgebra.star_def, CliffordAlgebra.star_def, s22b_bcC_reverse, s22b_bcC_involute]

/-- `ρ` commutes with the change of coefficients. -/
theorem s22b_rho_bcSpin (g : Spin F n) (v : V F n) :
    rho F' n (bcSpin F F' n g) (bcV F F' n v) = bcV F F' n (rho F n g v) := by
  apply CliffordAlgebra.ι_injective (Q F' n)
  conv_rhs => rw [← s22b_bcC_ι, ι_rho]
  rw [ι_rho, ← s22b_bcC_ι]
  simp [bcSpin, s22b_bcC_star]

/-- The contraction `D_θ` commutes with the change of coefficients. -/
theorem s22b_D_bcS (θ : Module.Dual F (H1 F n)) (s : S F n) :
    D F' n (bcDual F F' n θ) (bcS F F' n s) = bcS F F' n (D F n θ s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, AlgHom.commutes, contractLeft_algebraMap, map_zero]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x w hx =>
    have h1 : (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w) = ExteriorAlgebra.ι F w := rfl
    rw [h1, map_mul, s22b_bcS_ι]
    simp only [D]
    rw [contractLeft_ι_mul, contractLeft_ι_mul]
    simp only [D] at hx
    rw [hx, s22b_bcDual_bcH1, map_sub, map_smul, map_mul, s22b_bcS_ι, algebraMap_smul]

/-- The spin representation `m` commutes with the change of coefficients. -/
theorem s22b_m_bcC_bcS (x : C F n) (s : S F n) :
    m F' n (bcC F F' n x) (bcS F F' n s) = bcS F F' n (m F n x s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n), AlgHom.commutes,
      AlgHom.commutes]
    simp [Module.algebraMap_end_apply]
  | ι v =>
    rw [s22b_bcC_ι]
    simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply, L, LinearMap.mul_apply',
      map_add, s22b_bcV_fst', s22b_bcV_snd']
    rw [s22b_D_bcS, map_mul, s22b_bcS_ι]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, hb, ha]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [CharZero F] [CharZero F'] in
/-- An `F`-algebra map of exterior algebras induced by `φ` on generators maps `ιMulti` to
`ιMulti`. -/
theorem s22b_map_ιMulti {M M' : Type*} [AddCommGroup M] [Module F M] [AddCommGroup M']
    [Module F' M'] [Module F M'] [IsScalarTower F F' M']
    (Φ : ExteriorAlgebra F M →ₐ[F] ExteriorAlgebra F' M') (φ : M → M')
    (h : ∀ m, Φ (ExteriorAlgebra.ι F m) = ExteriorAlgebra.ι F' (φ m)) (k : ℕ) (v : Fin k → M) :
    Φ (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (φ ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [h]

omit [CharZero F] [CharZero F'] in
theorem s22b_map_basis_exteriorAlgebra {M M' : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F' M'] [Module F M'] [IsScalarTower F F' M'] {I : Type*}
    [LinearOrder I] (b : Module.Basis I F M)
    (b' : Module.Basis I F' M') (Φ : ExteriorAlgebra F M →ₐ[F] ExteriorAlgebra F' M')
    (φ : M → M') (h : ∀ m, Φ (ExteriorAlgebra.ι F m) = ExteriorAlgebra.ι F' (φ m))
    (hb : ∀ i, φ (b i) = b' i) (s : Finset I) :
    Φ (b.ExteriorAlgebra s) = b'.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply, s22b_map_ιMulti Φ φ h]
  congr 1
  funext i
  simp [hb]

omit [CharZero F] [CharZero F'] in
/-- A linear map sending an `F`-basis to an `F'`-basis is injective. -/
theorem s22b_injective_of_basis {M M' : Type*} [AddCommGroup M] [Module F M] [AddCommGroup M']
    [Module F' M'] [Module F M'] [IsScalarTower F F' M'] {I : Type*} (b : Module.Basis I F M)
    (b' : Module.Basis I F' M') (Φ : M →ₗ[F] M') (hb : ∀ i, Φ (b i) = b' i) :
    Function.Injective Φ := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have key : ∀ i, algebraMap F F' (b.repr x i) = b'.repr (Φ x) i := by
    intro i
    conv_rhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Finsupp.sum_apply]
    simp only [map_smul, hb]
    rw [Finsupp.sum, Finset.sum_eq_single i]
    · rw [← algebraMap_smul F', map_smul, b'.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [← algebraMap_smul F', map_smul, b'.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_of_ne hj.symm, smul_zero]
    · intro hi
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul, map_zero, Finsupp.zero_apply]
  apply b.repr.injective
  ext i
  have := key i
  rw [hx, map_zero, Finsupp.zero_apply] at this
  simpa using this

omit [CharZero F] in
theorem s22b_dualBasis_eq_f (i : Fin (2 * n)) :
    (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
  apply s22b_dual_ext
  intro j
  simp [f, e, Pi.single_apply]

omit [CharZero F] in
theorem s22b_basisV_inl (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inl i)) = (f F n i, 0) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply]
  rw [s22b_dualBasis_eq_f]

omit [CharZero F] in
theorem s22b_basisV_inr (j : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inr j)) = (0, e F n j) := by
  rw [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply]
  simp [e]

theorem s22b_bcDual_f (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  apply s22b_dual_ext
  intro j
  show (∑ k, algebraMap F F' (f F n i (e F n k)) • f F' n k) (e F' n j) = _
  rw [s22b_sum_smul_f_apply]
  simp [f, e, Pi.single_apply]

theorem s22b_bcV_basisV (k : Fin (2 * n + 2 * n)) :
    bcV F F' n (basisV F n k) = basisV F' n k := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | j
  · rw [s22b_basisV_inl, s22b_basisV_inl]
    refine Prod.ext (s22b_bcDual_f i) ?_
    show bcH1 F F' n 0 = 0
    exact map_zero _
  · rw [s22b_basisV_inr (F := F), s22b_basisV_inr (F := F')]
    refine Prod.ext ?_ ?_
    · show bcDual F F' n 0 = 0
      exact map_zero _
    · show bcH1 F F' n (e F n j) = e F' n j
      ext k; simp [bcH1, e, Pi.single_apply]

omit [CharZero F] [CharZero F'] in
theorem s22b_bcS_basisS (s : Finset (Fin (2 * n))) :
    bcS F F' n (basisS F n s) = basisS F' n s :=
  s22b_map_basis_exteriorAlgebra _ _ (bcS F F' n) (bcH1 F F' n) s22b_bcS_ι
    (fun i => by ext j; simp [bcH1, Pi.single_apply]) s

omit [CharZero F] [CharZero F'] in
theorem s22b_bcS_injective : Function.Injective (bcS F F' n) :=
  s22b_injective_of_basis (basisS F n) (basisS F' n) (bcS F F' n).toLinearMap s22b_bcS_basisS

theorem s22b_bcExt_basisExt (s : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n s) = basisExt F' n s :=
  s22b_map_basis_exteriorAlgebra _ _ (bcExt F F' n) (bcV F F' n) s22b_bcExt_ι
    s22b_bcV_basisV s

theorem s22b_bcExt_injective : Function.Injective (bcExt F F' n) :=
  s22b_injective_of_basis (basisExt F n) (basisExt F' n) (bcExt F F' n).toLinearMap
    s22b_bcExt_basisExt

/-- `V_{F'}` is spanned by the vectors of `V_F`. -/
theorem s22b_span_bcV : Submodule.span F' (Set.range (bcV F F' n)) = ⊤ := by
  rw [eq_top_iff, ← (basisV F' n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨_, s22b_bcV_basisV k⟩

/-- Two `F'`-linear maps on `V_{F'}` agreeing on `V_F` are equal. -/
theorem s22b_linearMap_ext_bcV {M : Type*} [AddCommGroup M] [Module F' M]
    {A B : V F' n →ₗ[F'] M} (h : ∀ v, A (bcV F F' n v) = B (bcV F F' n v)) : A = B :=
  LinearMap.ext_on_range s22b_span_bcV h

end Helpers

section Helpers2

variable {n : ℕ} {F : Type*} [Field F] [CharZero F]

theorem s22b_Q_nondegenerate (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

theorem s22b_m_ι_ι_self (v : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) v) s) = Q F n v • s := by
  have h := congrArg (fun x => m F n x s) (ι_sq_scalar (Q F n) v)
  simp only [map_mul, Module.End.mul_apply, AlgHom.commutes, Module.algebraMap_end_apply] at h
  exact h

theorem s22b_m_ι_ι_swap (v w : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) =
      pairing F n v w • s - m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) := by
  have h := congrArg (fun x => m F n x s) (ι_mul_ι_add_swap (Q := Q F n) v w)
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, AlgHom.commutes,
    Module.algebraMap_end_apply] at h
  rw [eq_sub_iff_add_eq, h]
  rfl

omit [CharZero F] in
/-- The pairing (1.2.2) on `V_F` is nondegenerate. -/
theorem s22b_pairing_nondeg (v : V F n) (h : ∀ w, pairing F n v w = 0) : v = 0 := by
  apply s22b_V_ext
  · intro i
    have := h (0, e F n i)
    simpa [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd] using this
  · intro i
    have := h (f F n i, 0)
    simpa [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, f] using this

omit [CharZero F] in
theorem s22b_bilin_mem_of_basis {K M E : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup E] [Module K E] {ι : Type*} [Fintype ι] (b : Module.Basis ι K M)
    (G : M →ₗ[K] M →ₗ[K] E) (N : Submodule K E) (h : ∀ k l, G (b k) (b l) ∈ N) (X Y : M) :
    G X Y ∈ N := by
  rw [← b.sum_repr X, ← b.sum_repr Y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (h k l))

omit [CharZero F] in
theorem s22b_pairing_comm (x y : V F n) :
    pairing F n x y = pairing F n y x := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.polar_comm _ _ _

/-- `D_{a,c} z = (c, z) a - (a, z) c`, an element of `so(V)`. -/
noncomputable def s22b_Dop (a c : V F n) : Module.End F (V F n) :=
  (pairing F n c).smulRight a - (pairing F n a).smulRight c

omit [CharZero F] in
theorem s22b_Dop_apply (a c z : V F n) :
    s22b_Dop a c z = pairing F n c z • a - pairing F n a z • c := rfl

omit [CharZero F] in
theorem s22b_Dop_swap (a c : V F n) : s22b_Dop c a = -s22b_Dop a c := by
  refine LinearMap.ext fun z => ?_
  rw [s22b_Dop_apply, LinearMap.neg_apply, s22b_Dop_apply, neg_sub]

omit [CharZero F] in
/-- Two linearly independent vectors in a subspace of dimension `≥ 2`. -/
theorem s22b_exists_pair {E : Type*} [AddCommGroup E] [Module F E] (C : Submodule F E)
    [FiniteDimensional F C] (hC : 2 ≤ Module.finrank F C) :
    ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∀ β₁ β₂ : F, β₁ • c₁ + β₂ • c₂ = 0 → β₁ = 0 ∧ β₂ = 0 := by
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank F C)
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := F)
    (by omega : 1 < Module.finrank F C) hx
  refine ⟨x, x.2, y, y.2, fun β₁ β₂ h => ?_⟩
  refine LinearIndependent.pair_iff.mp hy β₁ β₂ ?_
  apply Subtype.ext
  simpa using h

/-- **The Schur step** (proof of Lemma 2.2.4, filled by the plan): let `A, B ⊆ V` with `A`
isotropic, `A ∩ B = 0`, `dim B ≥ 3`, every nonzero `c ∈ B` pairing nontrivially with `A`. If `G`
commutes with all `D_{a,c}` (`a ∈ A`, `c ∈ B`, `(a, c) = 0`), every `a ∈ A` is an eigenvector
of `G`. -/
theorem s22b_eigen_of_commute (A B : Submodule F (V F n)) [FiniteDimensional F B]
    (hA : ∀ a ∈ A, ∀ a' ∈ A, pairing F n a a' = 0) (hAB : A ⊓ B = ⊥)
    (hB : 3 ≤ Module.finrank F B)
    (hnd : ∀ c ∈ B, c ≠ 0 → ∃ z ∈ A, pairing F n z c ≠ 0) (G : Module.End F (V F n))
    (hG : ∀ a ∈ A, ∀ c ∈ B, pairing F n a c = 0 → G * s22b_Dop a c = s22b_Dop a c * G)
    (a : V F n) (ha : a ∈ A) : ∃ μ : F, G a = μ • a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp⟩
  -- the orthogonal of `a` in `B`
  let φ : B →ₗ[F] F := (pairing F n a).comp B.subtype
  have hker : 2 ≤ Module.finrank F (LinearMap.ker φ) := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : Module.finrank F (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank F (LinearMap.range φ) ≤ Module.finrank F F :=
            Submodule.finrank_le _
        _ = 1 := Module.finrank_self F
    omega
  obtain ⟨c₁, hc₁, c₂, hc₂, hind⟩ := s22b_exists_pair (LinearMap.ker φ) hker
  -- for `c ∈ B ∩ a^⊥` nonzero, `G a ∈ span {a, c}`
  have key : ∀ c : B, φ c = 0 → (c : V F n) ≠ 0 →
      ∃ α β : F, G a = α • a + β • (c : V F n) := by
    intro c hc hc0
    obtain ⟨z, hzA, hz⟩ := hnd c c.2 hc0
    set z' := (pairing F n z c)⁻¹ • z
    have hz' : z' ∈ A := A.smul_mem _ hzA
    have hD : s22b_Dop a c z' = a := by
      rw [s22b_Dop_apply, hA a ha z' hz', zero_smul, sub_zero, s22b_pairing_comm, map_smul,
        LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hz, one_smul]
    refine ⟨pairing F n c (G z'), -pairing F n a (G z'), ?_⟩
    have := congrArg (fun T : Module.End F (V F n) => T z') (hG a ha c c.2 hc)
    simp only [Module.End.mul_apply, hD] at this
    rw [this, s22b_Dop_apply, neg_smul, sub_eq_add_neg]
  have hc₁0 : (c₁ : V F n) ≠ 0 := by
    intro h
    have h' : c₁ = 0 := Subtype.ext h
    have := (hind 1 0 (by rw [h']; simp)).1
    exact one_ne_zero this
  have hc₂0 : (c₂ : V F n) ≠ 0 := by
    intro h
    have h' : c₂ = 0 := Subtype.ext h
    have := (hind 0 1 (by rw [h']; simp)).2
    exact one_ne_zero this
  obtain ⟨α₁, β₁, h₁⟩ := key c₁ (LinearMap.mem_ker.mp hc₁) (by simpa using hc₁0)
  obtain ⟨α₂, β₂, h₂⟩ := key c₂ (LinearMap.mem_ker.mp hc₂) (by simpa using hc₂0)
  -- `(α₁ - α₂) a = β₂ c₂ - β₁ c₁ ∈ A ∩ B = 0`
  have hmem : (α₁ - α₂) • a ∈ A ⊓ B := by
    refine ⟨A.smul_mem _ ha, ?_⟩
    have : (α₁ - α₂) • a = β₂ • (c₂ : V F n) - β₁ • (c₁ : V F n) := by
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, ← h₁, add_comm, ← h₂]
    rw [this]
    exact B.sub_mem (B.smul_mem _ (c₂ : B).2) (B.smul_mem _ (c₁ : B).2)
  rw [hAB, Submodule.mem_bot] at hmem
  have hβ : (-β₁) • (c₁ : V F n) + β₂ • (c₂ : V F n) = 0 := by
    have : β₂ • (c₂ : V F n) - β₁ • (c₁ : V F n) = 0 := by
      rw [← hmem]; rw [sub_smul, sub_eq_sub_iff_add_eq_add, ← h₁, add_comm, ← h₂]
    rw [neg_smul, add_comm, ← sub_eq_add_neg]; exact this
  have hβ' : (-β₁) • c₁ + β₂ • c₂ = 0 := by
    apply Subtype.ext; simpa using hβ
  have := (hind (-β₁) β₂ hβ').1
  refine ⟨α₁, ?_⟩
  rw [h₁, neg_eq_zero.mp this, zero_smul, add_zero]


variable {F' : Type*} [Field F'] [CharZero F'] [Algebra F F']

/-- The `F'`-linear extension of an endomorphism of `V_F` (same matrix in the bases `basisV`). -/
noncomputable def s22b_bcEnd (A : V F n →ₗ[F] V F n) : V F' n →ₗ[F'] V F' n :=
  (basisV F' n).constr F' fun k => bcV F F' n (A (basisV F n k))

theorem s22b_bcEnd_bcV (A : V F n →ₗ[F] V F n) (v : V F n) :
    s22b_bcEnd (F' := F') A (bcV F F' n v) = bcV F F' n (A v) := by
  have : ((s22b_bcEnd (F' := F') A).restrictScalars F) ∘ₗ bcV F F' n = bcV F F' n ∘ₗ A := by
    apply (basisV F n).ext
    intro k
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      s22b_bcV_basisV, s22b_bcEnd, Module.Basis.constr_basis]
  exact LinearMap.congr_fun this v

end Helpers2

section HelpersK

variable {n : ℕ} {d : ℚ}

theorem s22b_σV_smul (c : Kd d) (v : V (Kd d) n) :
    σV n d (c • v) = Kd.σ d c • σV n d v := by
  apply s22b_V_ext
  · intro i; simp [s22b_conjV_fst]
  · intro i; simp [s22b_conjV_snd]

theorem s22b_σV_σV (v : V (Kd d) n) : σV n d (σV n d v) = v := by
  apply s22b_V_ext
  · intro i; simp only [s22b_conjV_fst]; apply Subtype.ext; simp
  · intro i; simp only [s22b_conjV_snd]; apply Subtype.ext; simp

theorem s22b_σV_bcV (w : V ℚ n) : σV n d (bcV ℚ (Kd d) n w) = bcV ℚ (Kd d) n w := by
  apply s22b_V_ext
  · intro i; simp only [s22b_conjV_fst, s22b_bcV_fst, s22b_σ_algebraMap]
  · intro i; simp only [s22b_conjV_snd, s22b_bcV_snd, s22b_σ_algebraMap]

/-- A `σ`-fixed vector of `V_K` is rational. -/
theorem s22b_bcV_ratPartV (hd : 0 < d) (v : V (Kd d) n) (h : σV n d v = v) :
    bcV ℚ (Kd d) n (ratPartV n d v) = v := by
  apply s22b_V_ext
  · intro i
    rw [s22b_bcV_fst]
    have hi : Kd.σ d (v.1 (e (Kd d) n i)) = v.1 (e (Kd d) n i) := by
      have := congrArg (fun x : V (Kd d) n => x.1 (e (Kd d) n i)) h
      simpa [s22b_conjV_fst] using this
    rw [s22b_eq_algebraMap_of_σ_eq hd _ hi]
    simp [ratPartV]
  · intro i
    rw [s22b_bcV_snd]
    have hi : Kd.σ d (v.2 i) = v.2 i := by
      have := congrArg (fun x : V (Kd d) n => x.2 i) h
      simpa [s22b_conjV_snd] using this
    rw [s22b_eq_algebraMap_of_σ_eq hd _ hi]
    simp [ratPartV]

theorem s22b_algebraMap_Nm (hd : 0 < d) (l : Kd d) :
    algebraMap ℚ (Kd d) (Kd.Nm d l) = l * Kd.σ d l := by
  apply Subtype.ext
  rw [eq_ratCast, SubfieldClass.coe_ratCast, Kd.coe_Nm hd l]
  rfl

theorem s22b_pairing_bcV {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (x y : V F n) :
    pairing F' n (bcV F F' n x) (bcV F F' n y) = algebraMap F F' (pairing F n x y) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    Q_bcV, map_sub]

end HelpersK

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- `ηK` on a sum `a + b` with `a ∈ W₁`, `b ∈ W₂`. -/
theorem s22b_ηK_add_mem (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {a b : V (Kd d) n}
    (ha : a ∈ P.W₁) (hb : b ∈ P.W₂) : P.ηK hW l (a + b) = l • a + Kd.σ d l • b := by
  simp only [ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
    Submodule.projectionOnto_apply_of_mem_left hW ha,
    Submodule.projectionOnto_apply_of_mem_right hW hb,
    Submodule.projectionOnto_apply_of_mem_left hW.symm hb,
    Submodule.projectionOnto_apply_of_mem_right hW.symm ha]
  simp

theorem s22b_ηK_of_mem_W₁ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {a : V (Kd d) n}
    (ha : a ∈ P.W₁) : P.ηK hW l a = l • a := by
  simpa using P.s22b_ηK_add_mem hW l ha P.W₂.zero_mem

theorem s22b_ηK_of_mem_W₂ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {b : V (Kd d) n}
    (hb : b ∈ P.W₂) : P.ηK hW l b = Kd.σ d l • b := by
  simpa using P.s22b_ηK_add_mem hW l P.W₁.zero_mem hb

theorem s22b_decomp (hW : IsCompl P.W₁ P.W₂) (v : V (Kd d) n) :
    P.W₁.projection P.W₂ hW v + P.W₂.projection P.W₁ hW.symm v = v :=
  Submodule.projection_add_projection_eq_self hW v

theorem s22b_proj₁_mem (hW : IsCompl P.W₁ P.W₂) (v : V (Kd d) n) :
    P.W₁.projection P.W₂ hW v ∈ P.W₁ := Submodule.projection_apply_mem _ _

theorem s22b_proj₂_mem (hW : IsCompl P.W₁ P.W₂) (v : V (Kd d) n) :
    P.W₂.projection P.W₁ hW.symm v ∈ P.W₂ := Submodule.projection_apply_mem _ _

/-- Uniqueness of the decomposition `V_K = W₁ ⊕ W₂`. -/
theorem s22b_decomp_unique (hW : IsCompl P.W₁ P.W₂) {a a' b b' : V (Kd d) n}
    (ha : a ∈ P.W₁) (ha' : a' ∈ P.W₁) (hb : b ∈ P.W₂) (hb' : b' ∈ P.W₂)
    (h : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' ∈ P.W₁ := P.W₁.sub_mem ha ha'
  have h2 : a - a' ∈ P.W₂ := by
    have : a - a' = b' - b := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]; exact P.W₂.sub_mem hb' hb
  have h3 : a - a' = 0 := (Submodule.disjoint_def.mp hW.disjoint) _ h1 h2
  refine ⟨sub_eq_zero.mp h3, ?_⟩
  rw [sub_eq_zero.mp h3] at h
  exact add_left_cancel h

theorem s22b_ηK_mul (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) (v : V (Kd d) n) :
    P.ηK hW (l * l') v = P.ηK hW l (P.ηK hW l' v) := by
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, P.s22b_ηK_add_mem hW _ ha hb,
    P.s22b_ηK_add_mem hW _ (P.W₁.smul_mem _ ha) (P.W₂.smul_mem _ hb), map_mul, mul_smul,
    mul_smul]

theorem s22b_ηK_add (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) (v : V (Kd d) n) :
    P.ηK hW (l + l') v = P.ηK hW l v + P.ηK hW l' v := by
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, P.s22b_ηK_add_mem hW _ ha hb,
    P.s22b_ηK_add_mem hW _ ha hb, map_add, add_smul, add_smul]
  abel

theorem s22b_ηK_one (hW : IsCompl P.W₁ P.W₂) (v : V (Kd d) n) : P.ηK hW 1 v = v := by
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, map_one, one_smul, one_smul]

theorem s22b_ηK_zero (hW : IsCompl P.W₁ P.W₂) (v : V (Kd d) n) : P.ηK hW 0 v = 0 := by
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, map_zero, zero_smul, zero_smul,
    add_zero]

include P in
/-- A rational `K`-secant only exists for `n ≥ 1` (for `n = 0`, `S_K = K` is a line). -/
theorem s22b_n_pos : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    exfalso
    have := Module.Finite.of_basis (basisS (Kd d) 0)
    have h1 : Module.finrank (Kd d) (S (Kd d) 0) = 1 := by
      rw [Module.finrank_eq_card_basis (basisS (Kd d) 0)]
      simp
    have := P.linIndep.fintype_card_le_finrank
    simp [h1] at this
  · exact h

/-- `W₁` is totally isotropic for the pairing. -/
theorem s22b_pairing_W₁ {a b : V (Kd d) n} (ha : a ∈ P.W₁) (hb : b ∈ P.W₁) :
    pairing (Kd d) n a b = 0 := by
  have h := P.isPure.2.1
  simp [pairing, QuadraticMap.polar, h _ ha, h _ hb, h _ (P.W₁.add_mem ha hb)]

/-- `W₂` is totally isotropic for the pairing. -/
theorem s22b_pairing_W₂ {a b : V (Kd d) n} (ha : a ∈ P.W₂) (hb : b ∈ P.W₂) :
    pairing (Kd d) n a b = 0 := by
  have h := P.isPure₂.2.1
  simp [pairing, QuadraticMap.polar, h _ ha, h _ hb, h _ (P.W₂.add_mem ha hb)]

theorem s22b_pairing_add_add {a a' b b' : V (Kd d) n} (ha : a ∈ P.W₁) (ha' : a' ∈ P.W₁)
    (hb : b ∈ P.W₂) (hb' : b' ∈ P.W₂) :
    pairing (Kd d) n (a + b) (a' + b') = pairing (Kd d) n a b' + pairing (Kd d) n b a' := by
  simp only [map_add, LinearMap.add_apply, P.s22b_pairing_W₁ ha ha', P.s22b_pairing_W₂ hb hb']
  ring

/-- `σ` exchanges `W₁` and `W₂`: `σ(W₂) ⊆ W₁`. -/
theorem s22b_σV_mem_W₁ {b : V (Kd d) n} (hb : b ∈ P.W₂) : σV n d b ∈ P.W₁ := by
  rw [← P.σV_mem_W₂_iff, s22b_σV_σV]; exact hb


/-- "**The subset `V_ℚ` of `V_K` is equal to `{v₁ + σ(v₁) : v₁ ∈ W₁}`**" (§2.2), when
`V_K = W₁ ⊕ W₂`. -/
theorem range_bcV_eq (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    Set.range (bcV ℚ (Kd d) n) = {v | ∃ v₁ ∈ P.W₁, v = v₁ + σV n d v₁} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    set v := bcV ℚ (Kd d) n w
    have ha := P.s22b_proj₁_mem hW v
    have hb := P.s22b_proj₂_mem hW v
    -- `σ(v) = v`, and `σ` exchanges the two summands of `v = a + b`
    have hv : σV n d (P.W₁.projection P.W₂ hW v + P.W₂.projection P.W₁ hW.symm v) =
        P.W₁.projection P.W₂ hW v + P.W₂.projection P.W₁ hW.symm v := by
      rw [P.s22b_decomp hW v]; exact s22b_σV_bcV w
    rw [map_add, add_comm] at hv
    have hσa : σV n d (P.W₁.projection P.W₂ hW v) ∈ P.W₂ := (P.σV_mem_W₂_iff _).mpr ha
    obtain ⟨_, h2⟩ := P.s22b_decomp_unique hW (P.s22b_σV_mem_W₁ hb) ha hσa hb hv
    refine ⟨P.W₁.projection P.W₂ hW v, ha, ?_⟩
    conv_lhs => rw [← P.s22b_decomp hW v]
    rw [h2]
  · rintro ⟨v₁, -, rfl⟩
    refine ⟨ratPartV n d (v₁ + σV n d v₁), s22b_bcV_ratPartV hd _ ?_⟩
    rw [map_add, s22b_σV_σV, add_comm]

/-- `η_λ` commutes with the Galois involution `σ` of `V_K` (§2.2). -/
theorem σV_ηK (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V (Kd d) n) :
    σV n d (P.ηK hW l v) = P.ηK hW l (σV n d v) := by
  have _ := hd
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, map_add, map_add, s22b_σV_smul,
    s22b_σV_smul, add_comm (σV n d _) (σV n d _),
    P.s22b_ηK_add_mem hW _ (P.s22b_σV_mem_W₁ hb) ((P.σV_mem_W₂_iff _).mpr ha), s22b_σ_σ,
    add_comm]

/-- "**`η_λ` leaves `V_ℚ` invariant**" (§2.2): the rational endomorphism `η_λ` of (2.2.4) is the
restriction of `η_λ` on `V_K` to `V_ℚ`. -/
theorem ηK_bcV (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V ℚ n) :
    P.ηK hW l (bcV ℚ (Kd d) n v) = bcV ℚ (Kd d) n (P.η hW l v) :=
  (bcV_descend n d (P.ηK hW l) (fun w => P.σV_ηK hd hW l w) v).symm

/-- `η_1 = id` (`η` is a homomorphism, (2.2.4)). -/
theorem η_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : P.η hW 1 = 1 := by
  refine LinearMap.ext fun v => ?_
  apply s22b_bcV_injective (F' := Kd d)
  rw [← P.ηK_bcV hd hW, P.s22b_ηK_one hW]
  rfl

/-- `η_{λλ'} = η_λ ∘ η_{λ'}` (`η` is a homomorphism, (2.2.4)). -/
theorem η_mul (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.η hW (l * l') = P.η hW l * P.η hW l' := by
  refine LinearMap.ext fun v => ?_
  apply s22b_bcV_injective (F' := Kd d)
  rw [Module.End.mul_apply, ← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW,
    P.s22b_ηK_mul hW]

/-- `η_{λ+λ'} = η_λ + η_{λ'}` (`η` is additive: `K` embeds in `End(V_ℚ)`). -/
theorem η_add (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.η hW (l + l') = P.η hW l + P.η hW l' := by
  refine LinearMap.ext fun v => ?_
  apply s22b_bcV_injective (F' := Kd d)
  rw [LinearMap.add_apply, map_add, ← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW,
    P.s22b_ηK_add hW]

/-- `η_0 = 0`. -/
theorem η_zero (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : P.η hW 0 = 0 := by
  refine LinearMap.ext fun v => ?_
  apply s22b_bcV_injective (F' := Kd d)
  rw [← P.ηK_bcV hd hW, P.s22b_ηK_zero hW, LinearMap.zero_apply, map_zero]

/-- The homomorphism (2.2.4) `η : K → End_ℚ(V_ℚ)`, `λ ↦ η_λ`, as a ring homomorphism (the paper
restricts it to `K^× → GL(V_ℚ)`; the table of notation calls it "an embedding of `K` in
`End(V_ℚ)`"). -/
noncomputable def ηHom (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : Kd d →+* Module.End ℚ (V ℚ n) where
  toFun := P.η hW
  map_one' := P.η_one hd hW
  map_mul' := P.η_mul hd hW
  map_zero' := P.η_zero hd hW
  map_add' := P.η_add hd hW

/-- `η` is injective (§10.2: "the injective group homomorphism `η : K^× → GL(V_ℚ)`"). -/
theorem ηHom_injective (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    Function.Injective (P.ηHom hd hW) := by
  have hn := P.s22b_n_pos
  have : Nontrivial (V ℚ n) := by
    refine ⟨⟨(0, e ℚ n ⟨0, by omega⟩), 0, fun h => ?_⟩⟩
    have := congrArg (fun x : V ℚ n => x.2 ⟨0, by omega⟩) h
    simp [e] at this
  exact (P.ηHom hd hW).injective

/-- **`η_λ` is a similarity with multiplier `Nm(λ)`** (proof of Lemma 2.2.4):
`(η_λ(v), η_λ(v'))_V = Nm(λ) (v, v')_V`. In particular `η_λ ∈ Õ(V_ℚ)` for `λ ≠ 0`; for
`f = η_{√-d}` this gives `(f(x), f(y))_V = d (x, y)_V` (§2.4). -/
theorem pairing_η (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v v' : V ℚ n) :
    pairing ℚ n (P.η hW l v) (P.η hW l v') = Kd.Nm d l * pairing ℚ n v v' := by
  apply (algebraMap ℚ (Kd d)).injective
  rw [map_mul, ← s22b_pairing_bcV, ← s22b_pairing_bcV, ← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW,
    s22b_algebraMap_Nm hd]
  set x := bcV ℚ (Kd d) n v
  set y := bcV ℚ (Kd d) n v'
  have ha := P.s22b_proj₁_mem hW x
  have hb := P.s22b_proj₂_mem hW x
  have ha' := P.s22b_proj₁_mem hW y
  have hb' := P.s22b_proj₂_mem hW y
  rw [← P.s22b_decomp hW x, ← P.s22b_decomp hW y, P.s22b_ηK_add_mem hW _ ha hb,
    P.s22b_ηK_add_mem hW _ ha' hb',
    P.s22b_pairing_add_add (P.W₁.smul_mem _ ha) (P.W₁.smul_mem _ ha') (P.W₂.smul_mem _ hb)
      (P.W₂.smul_mem _ hb'), P.s22b_pairing_add_add ha ha' hb hb']
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## Unitary transvections in `Spin(V_ℚ)_P` (the plan for the gap in Lemmas 2.2.4/2.2.7)

For an isotropic `x ∈ V_ℚ` and `t ∈ ℚ`, `E_{x,t} = 1 + t ι(f x) ι(x)` (`f = η_{√-d}`) lies in
`Spin(V_ℚ)_P` and acts on `V_ℚ` by `1 + t N_x`, `N_x(y) = (y, x) f x - (y, f x) x`. The `K`-span `𝔫`
of the operators `N_x` (extended to `V_K`) contains all `D_{a,c}`, `a ∈ W₁`, `c ∈ W₂`,
`(a, c) = 0`: it acts on `V_K = W₁ ⊕ W₂` as `sl(W₁)`. -/

/-- `f = η_{√-d}` on `V_K`: `f(a + b) = √-d a - √-d b`. -/
theorem s22b_fK_add_mem (hW : IsCompl P.W₁ P.W₂) {a b : V (Kd d) n} (ha : a ∈ P.W₁)
    (hb : b ∈ P.W₂) :
    P.ηK hW (Kd.sqrtNeg d) (a + b) = Kd.sqrtNeg d • a - Kd.sqrtNeg d • b := by
  rw [P.s22b_ηK_add_mem hW _ ha hb, s22b_σ_sqrtNeg, neg_smul, sub_eq_add_neg]

/-- `(x, f x)_V = 0` for `x ∈ V_ℚ` (`f` is anti-self-adjoint). -/
theorem s22b_pairing_self_fη (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    pairing ℚ n x (P.fη hW x) = 0 := by
  apply (algebraMap ℚ (Kd d)).injective
  rw [map_zero, ← s22b_pairing_bcV, fη, ← P.ηK_bcV hd hW]
  set X := bcV ℚ (Kd d) n x
  have ha := P.s22b_proj₁_mem hW X
  have hb := P.s22b_proj₂_mem hW X
  rw [← P.s22b_decomp hW X, P.s22b_fK_add_mem hW ha hb, sub_eq_add_neg, ← smul_neg,
    P.s22b_pairing_add_add ha (P.W₁.smul_mem _ ha) hb (P.W₂.smul_mem _ (P.W₂.neg_mem hb))]
  simp only [map_smul, map_neg, smul_eq_mul]
  rw [s22b_pairing_comm (P.W₂.projection P.W₁ hW.symm X)]
  ring

/-- `m_a u₁ = 0` for `a ∈ W₁`. -/
theorem s22b_m_W₁ {a : V (Kd d) n} (ha : a ∈ P.W₁) : m (Kd d) n (ι (Q (Kd d) n) a) P.u₁ = 0 :=
  ha

/-- `m_b u₂ = 0` for `b ∈ W₂`. -/
theorem s22b_m_W₂ {b : V (Kd d) n} (hb : b ∈ P.W₂) : m (Kd d) n (ι (Q (Kd d) n) b) P.u₂ = 0 :=
  hb

/-- The unitary transvection `1 + ι(Y) ι(X)`, `X = a + b` isotropic and `Y = α a + β b`, fixes the
pure spinors `u₁` and `u₂`. -/
theorem s22b_m_transv_u₁ {a b : V (Kd d) n} (ha : a ∈ P.W₁) (hb : b ∈ P.W₂)
    (hab : pairing (Kd d) n a b = 0) (α β : Kd d) :
    m (Kd d) n (ι (Q (Kd d) n) (α • a + β • b)) (m (Kd d) n (ι (Q (Kd d) n) (a + b)) P.u₁) =
      0 := by
  have h1 : m (Kd d) n (ι (Q (Kd d) n) (a + b)) P.u₁ = m (Kd d) n (ι (Q (Kd d) n) b) P.u₁ := by
    rw [map_add, map_add, LinearMap.add_apply, P.s22b_m_W₁ ha, zero_add]
  rw [h1, map_add (ι (Q (Kd d) n)), map_add (m (Kd d) n), LinearMap.add_apply,
    map_smul (ι (Q (Kd d) n)), map_smul (ι (Q (Kd d) n)), map_smul (m (Kd d) n),
    map_smul (m (Kd d) n), LinearMap.smul_apply, LinearMap.smul_apply, s22b_m_ι_ι_swap,
    P.s22b_m_W₁ ha, map_zero, sub_zero, hab, zero_smul, smul_zero, zero_add,
    s22b_m_ι_ι_self, P.isPure₂.2.1 b hb, zero_smul, smul_zero]

theorem s22b_m_transv_u₂ {a b : V (Kd d) n} (ha : a ∈ P.W₁) (hb : b ∈ P.W₂)
    (hab : pairing (Kd d) n a b = 0) (α β : Kd d) :
    m (Kd d) n (ι (Q (Kd d) n) (α • a + β • b)) (m (Kd d) n (ι (Q (Kd d) n) (a + b)) P.u₂) =
      0 := by
  have h1 : m (Kd d) n (ι (Q (Kd d) n) (a + b)) P.u₂ = m (Kd d) n (ι (Q (Kd d) n) a) P.u₂ := by
    rw [map_add, map_add, LinearMap.add_apply, P.s22b_m_W₂ hb, add_zero]
  rw [h1, map_add (ι (Q (Kd d) n)), map_add (m (Kd d) n), LinearMap.add_apply,
    map_smul (ι (Q (Kd d) n)), map_smul (ι (Q (Kd d) n)), map_smul (m (Kd d) n),
    map_smul (m (Kd d) n), LinearMap.smul_apply, LinearMap.smul_apply,
    s22b_m_ι_ι_self, P.isPure.2.1 a ha, zero_smul, smul_zero, zero_add, s22b_m_ι_ι_swap,
    P.s22b_m_W₂ hb, map_zero, sub_zero, s22b_pairing_comm, hab, zero_smul, smul_zero]

/-- An isotropic rational vector decomposes as `a + b` with `a ∈ W₁`, `b ∈ W₂`, `(a, b)_V = 0`. -/
theorem s22b_decomp_isotropic (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) (hx : Q ℚ n x = 0) :
    ∃ a ∈ P.W₁, ∃ b ∈ P.W₂, bcV ℚ (Kd d) n x = a + b ∧ pairing (Kd d) n a b = 0 := by
  refine ⟨_, P.s22b_proj₁_mem hW (bcV ℚ (Kd d) n x), _,
    P.s22b_proj₂_mem hW (bcV ℚ (Kd d) n x), (P.s22b_decomp hW _).symm, ?_⟩
  have h := Q_bcV ℚ (Kd d) n x
  rw [hx, map_zero, ← P.s22b_decomp hW (bcV ℚ (Kd d) n x), QuadraticMap.map_add (Q (Kd d) n),
    P.isPure.2.1 _ (P.s22b_proj₁_mem hW _), P.isPure₂.2.1 _ (P.s22b_proj₂_mem hW _), zero_add,
    zero_add, ← QuadraticMap.polarBilin_apply_apply] at h
  exact h

theorem s22b_polar_x_tfx (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n) :
    QuadraticMap.polar (Q ℚ n) x (t • P.fη hW x) = 0 := by
  rw [QuadraticMap.polar_smul_right, ← QuadraticMap.polarBilin_apply_apply]
  have := P.s22b_pairing_self_fη hd hW x
  simp only [pairing] at this
  rw [this, smul_zero]

/-- **The unitary transvection** `E_{x,t} = 1 + t ι(f x) ι(x) ∈ Spin(V_ℚ)` for an isotropic
`x ∈ V_ℚ` (TauCeti's spin lift of the Eichler transvection; `f = η_{√-d}`). -/
noncomputable def s22b_E (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) : Spin ℚ n :=
  CliffordAlgebra.spinTransvection (s22b_Q_nondegenerate ℚ n) hx (P.s22b_polar_x_tfx hd hW t x)

theorem s22b_coe_E (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) :
    ((P.s22b_E hd hW t x hx : Spin ℚ n) : C ℚ n) =
      1 + ι (Q ℚ n) (t • P.fη hW x) * ι (Q ℚ n) x :=
  CliffordAlgebra.coe_spinTransvection _ _ _

/-- `E_{x,t} ∈ Spin(V_ℚ)_P`: it fixes the pure spinors `u₁`, `u₂`, hence `P`. -/
theorem s22b_E_mem_spinPℚ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) : P.s22b_E hd hW t x hx ∈ P.spinPℚ := by
  intro p hp
  rw [s22b_coe_E, map_add, map_one, map_mul, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply, add_eq_left]
  apply s22b_bcS_injective (F' := Kd d)
  rw [map_zero, ← s22b_m_bcC_bcS, ← s22b_m_bcC_bcS, s22b_bcC_ι, s22b_bcC_ι]
  have hp' : bcS ℚ (Kd d) n p ∈ P.PK := hp
  obtain ⟨a, ha, b, hb, hX, hab⟩ := P.s22b_decomp_isotropic hW x hx
  have hY : bcV ℚ (Kd d) n (t • P.fη hW x) =
      (algebraMap ℚ (Kd d) t * Kd.sqrtNeg d) • a + (-(algebraMap ℚ (Kd d) t * Kd.sqrtNeg d)) • b := by
    rw [map_smul, fη, ← P.ηK_bcV hd hW, hX, P.s22b_fK_add_mem hW ha hb, ← algebraMap_smul (Kd d) t,
      smul_sub, smul_smul, smul_smul, neg_smul, sub_eq_add_neg]
  rw [hX, hY]
  have hker : P.PK ≤ LinearMap.ker ((m (Kd d) n (ι (Q (Kd d) n)
      ((algebraMap ℚ (Kd d) t * Kd.sqrtNeg d) • a +
        (-(algebraMap ℚ (Kd d) t * Kd.sqrtNeg d)) • b))) ∘ₗ m (Kd d) n (ι (Q (Kd d) n) (a + b))) := by
    rw [PK, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact P.s22b_m_transv_u₁ ha hb hab _ _
    · exact P.s22b_m_transv_u₂ ha hb hab _ _
  exact hker hp'

theorem s22b_Q_fη (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) (hx : Q ℚ n x = 0) :
    Q ℚ n (P.fη hW x) = 0 := by
  have h := P.pairing_η hd hW (Kd.sqrtNeg d) x x
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hx,
    smul_zero, mul_zero] at h
  rw [← fη, nsmul_eq_mul, Nat.cast_ofNat] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- `ρ(E_{x,t}) y = y + t((y, x) f x - (y, f x) x)`. -/
theorem s22b_rho_E (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) (y : V ℚ n) :
    rho ℚ n (P.s22b_E hd hW t x hx) y =
      y + t • (pairing ℚ n y x • P.fη hW x - pairing ℚ n y (P.fη hW x) • x) := by
  rw [rho, ← coe_spinToSpecialOrthogonal_apply, s22b_E,
    coe_spinToSpecialOrthogonal_spinTransvection, QuadraticMap.transvection_apply,
    QuadraticMap.map_smul, P.s22b_Q_fη hd hW x hx, smul_zero, zero_mul, zero_smul, sub_zero,
    QuadraticMap.polar_smul_right]
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  module



noncomputable def s22b_Mbil (hW : IsCompl P.W₁ P.W₂) :
    V (Kd d) n →ₗ[Kd d] V (Kd d) n →ₗ[Kd d] Module.End (Kd d) (V (Kd d) n) :=
  LinearMap.mk₂ (Kd d) (fun X Y =>
      (pairing (Kd d) n X).smulRight (P.ηK hW (Kd.sqrtNeg d) Y) +
        (pairing (Kd d) n Y).smulRight (P.ηK hW (Kd.sqrtNeg d) X) -
        (pairing (Kd d) n (P.ηK hW (Kd.sqrtNeg d) X)).smulRight Y -
        (pairing (Kd d) n (P.ηK hW (Kd.sqrtNeg d) Y)).smulRight X)
    (by intro X X' Y; refine LinearMap.ext fun z => ?_
        simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smulRight_apply, add_smul]; module)
    (by intro c X Y; refine LinearMap.ext fun z => ?_
        simp only [map_smul, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]; module)
    (by intro X Y Y'; refine LinearMap.ext fun z => ?_
        simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smulRight_apply, add_smul]; module)
    (by intro c X Y; refine LinearMap.ext fun z => ?_
        simp only [map_smul, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]; module)

theorem s22b_Mbil_comm (hW : IsCompl P.W₁ P.W₂) (X Y : V (Kd d) n) :
    P.s22b_Mbil hW X Y = P.s22b_Mbil hW Y X := by
  refine LinearMap.ext fun z => ?_
  show _ = _
  simp only [s22b_Mbil, LinearMap.mk₂_apply, LinearMap.add_apply, LinearMap.sub_apply]
  abel

theorem s22b_Mbil_apply (hW : IsCompl P.W₁ P.W₂) (X Y z : V (Kd d) n) :
    P.s22b_Mbil hW X Y z =
      pairing (Kd d) n X z • P.ηK hW (Kd.sqrtNeg d) Y +
        pairing (Kd d) n Y z • P.ηK hW (Kd.sqrtNeg d) X -
        pairing (Kd d) n (P.ηK hW (Kd.sqrtNeg d) X) z • Y -
        pairing (Kd d) n (P.ηK hW (Kd.sqrtNeg d) Y) z • X := rfl

theorem s22b_Mbil_add_add (hW : IsCompl P.W₁ P.W₂) (X Y : V (Kd d) n) :
    P.s22b_Mbil hW (X + Y) (X + Y) =
      P.s22b_Mbil hW X X + (P.s22b_Mbil hW X Y + P.s22b_Mbil hW X Y) + P.s22b_Mbil hW Y Y := by
  rw [LinearMap.map_add₂, map_add (P.s22b_Mbil hW X) X Y, map_add (P.s22b_Mbil hW Y) X Y,
      P.s22b_Mbil_comm hW Y X]
  abel

/-- The `K`-span `𝔫` of the infinitesimal unitary transvections `M(x, x) = 2 N_x`, `x ∈ V_ℚ`
isotropic. -/
noncomputable def s22b_nK (hW : IsCompl P.W₁ P.W₂) :
    Submodule (Kd d) (Module.End (Kd d) (V (Kd d) n)) :=
  Submodule.span (Kd d) {T | ∃ x : V ℚ n, Q ℚ n x = 0 ∧
    T = P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n x)}

theorem s22b_mem_nK_of_two_smul (hW : IsCompl P.W₁ P.W₂) {T : Module.End (Kd d) (V (Kd d) n)}
    (h : T + T ∈ P.s22b_nK hW) : T ∈ P.s22b_nK hW := by
  have h5 := Submodule.smul_mem _ (2 : Kd d)⁻¹ h
  rwa [← two_smul (Kd d), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at h5

theorem s22b_Mbil_mem_nK_of_rat (hW : IsCompl P.W₁ P.W₂) {x y : V ℚ n} (hx : Q ℚ n x = 0)
    (hy : Q ℚ n y = 0) (hxy : pairing ℚ n x y = 0) :
    P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n y) ∈ P.s22b_nK hW := by
  have h1 : P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n x) ∈ P.s22b_nK hW :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have h2 : P.s22b_Mbil hW (bcV ℚ (Kd d) n y) (bcV ℚ (Kd d) n y) ∈ P.s22b_nK hW :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  have hxy' : Q ℚ n (x + y) = 0 := by
    have h := QuadraticMap.map_add (Q ℚ n) x y
    rw [hx, hy, zero_add, zero_add] at h
    rw [h, ← QuadraticMap.polarBilin_apply_apply]
    exact hxy
  have h3 : P.s22b_Mbil hW (bcV ℚ (Kd d) n (x + y)) (bcV ℚ (Kd d) n (x + y)) ∈
      P.s22b_nK hW := Submodule.subset_span ⟨x + y, hxy', rfl⟩
  rw [map_add, P.s22b_Mbil_add_add] at h3
  apply P.s22b_mem_nK_of_two_smul hW
  have h4 := Submodule.sub_mem _ (Submodule.sub_mem _ h3 h1) h2
  have e : ∀ a b c : Module.End (Kd d) (V (Kd d) n), a + b + c - a - c = b := by
    intros; abel
  rwa [e] at h4

theorem s22b_Mbil_sub_add (hW : IsCompl P.W₁ P.W₂) (a₁ a₀ b₁ b₀ : V (Kd d) n) :
    P.s22b_Mbil hW (a₁ - a₀) (b₁ + b₀) =
      P.s22b_Mbil hW a₁ b₁ - P.s22b_Mbil hW a₀ b₀ +
        (P.s22b_Mbil hW a₁ b₀ - P.s22b_Mbil hW a₀ b₁) := by
  rw [LinearMap.map_sub₂, map_add (P.s22b_Mbil hW a₁), map_add (P.s22b_Mbil hW a₀)]
  abel

theorem s22b_pairing_inl_inr (i j : Fin (2 * n)) :
    pairing ℚ n ((f ℚ n i, 0) : V ℚ n) ((0, e ℚ n j) : V ℚ n) = if i = j then 1 else 0 := by
  simp [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, f, e,
    Pi.single_apply]

theorem s22b_pairing_inr_inl (i j : Fin (2 * n)) :
    pairing ℚ n ((0, e ℚ n i) : V ℚ n) ((f ℚ n j, 0) : V ℚ n) = if j = i then 1 else 0 := by
  simp [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, f, e,
    Pi.single_apply]

/-- The diagonal terms `M(fᵢ, eᵢ)` are congruent modulo `𝔫`. -/
theorem s22b_Mbil_diag_mem_nK (hW : IsCompl P.W₁ P.W₂) (i i₀ : Fin (2 * n)) :
    P.s22b_Mbil hW (bcV ℚ (Kd d) n (f ℚ n i, 0)) (bcV ℚ (Kd d) n (0, e ℚ n i)) -
      P.s22b_Mbil hW (bcV ℚ (Kd d) n (f ℚ n i₀, 0)) (bcV ℚ (Kd d) n (0, e ℚ n i₀)) ∈
      P.s22b_nK hW := by
  rcases eq_or_ne i i₀ with rfl | hi
  · rw [sub_self]; exact Submodule.zero_mem _
  have hA : Q ℚ n ((f ℚ n i - f ℚ n i₀, 0) : V ℚ n) = 0 := by simp
  have hB : Q ℚ n ((0, e ℚ n i + e ℚ n i₀) : V ℚ n) = 0 := by simp
  have hAB : pairing ℚ n ((f ℚ n i - f ℚ n i₀, 0) : V ℚ n) ((0, e ℚ n i + e ℚ n i₀) : V ℚ n)
      = 0 := by
    simp [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, f, e, hi,
      hi.symm]
  have h1 := P.s22b_Mbil_mem_nK_of_rat hW hA hB hAB
  have h2 := P.s22b_Mbil_mem_nK_of_rat hW (x := (f ℚ n i, 0)) (y := (0, e ℚ n i₀))
    (by simp) (by simp) (by rw [s22b_pairing_inl_inr]; simp [hi])
  have h3 := P.s22b_Mbil_mem_nK_of_rat hW (x := (f ℚ n i₀, 0)) (y := (0, e ℚ n i))
    (by simp) (by simp) (by rw [s22b_pairing_inl_inr]; simp [hi.symm])
  have hsplitA : ((f ℚ n i - f ℚ n i₀, 0) : V ℚ n) = (f ℚ n i, 0) - (f ℚ n i₀, 0) := by simp
  have hsplitB : ((0, e ℚ n i + e ℚ n i₀) : V ℚ n) = (0, e ℚ n i) + (0, e ℚ n i₀) := by simp
  rw [hsplitA, hsplitB, map_sub, map_add, s22b_Mbil_sub_add] at h1
  have h4 := Submodule.sub_mem _ h1 (Submodule.sub_mem _ h2 h3)
  rwa [add_sub_cancel_right] at h4

/-- The difference `M(X, Y) - (X, Y)_V M(f₀, e₀)` lies in `𝔫` on basis vectors. -/
theorem s22b_Mbil_basis_mem_nK (hW : IsCompl P.W₁ P.W₂) (i₀ : Fin (2 * n))
    (k l : Fin (2 * n) ⊕ Fin (2 * n)) :
    P.s22b_Mbil hW (bcV ℚ (Kd d) n (basisV ℚ n (finSumFinEquiv k)))
        (bcV ℚ (Kd d) n (basisV ℚ n (finSumFinEquiv l))) -
      algebraMap ℚ (Kd d) (pairing ℚ n (basisV ℚ n (finSumFinEquiv k))
        (basisV ℚ n (finSumFinEquiv l))) •
        P.s22b_Mbil hW (bcV ℚ (Kd d) n (f ℚ n i₀, 0)) (bcV ℚ (Kd d) n (0, e ℚ n i₀)) ∈
      P.s22b_nK hW := by
  have hrat : ∀ x y : V ℚ n, Q ℚ n x = 0 → Q ℚ n y = 0 → pairing ℚ n x y = 0 →
      P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n y) -
        algebraMap ℚ (Kd d) (pairing ℚ n x y) •
          P.s22b_Mbil hW (bcV ℚ (Kd d) n (f ℚ n i₀, 0)) (bcV ℚ (Kd d) n (0, e ℚ n i₀)) ∈
        P.s22b_nK hW := by
    intro x y hx hy hxy
    rw [hxy, map_zero, zero_smul, sub_zero]
    exact P.s22b_Mbil_mem_nK_of_rat hW hx hy hxy
  rcases k with i | i <;> rcases l with j | j <;> simp only [s22b_basisV_inl, s22b_basisV_inr]
  · exact hrat _ _ (by simp) (by simp) (by simp [pairing, QuadraticMap.polarBilin_apply_apply])
  · by_cases hij : i = j
    · subst hij
      rw [s22b_pairing_inl_inr]
      simp only [↓reduceIte, map_one, one_smul]
      exact P.s22b_Mbil_diag_mem_nK hW i i₀
    · exact hrat _ _ (by simp) (by simp)
        (by rw [s22b_pairing_inl_inr]; simp [hij])
  · by_cases hij : j = i
    · subst hij
      rw [P.s22b_Mbil_comm hW (bcV ℚ (Kd d) n (0, e ℚ n j)) (bcV ℚ (Kd d) n (f ℚ n j, 0)),
        s22b_pairing_inr_inl]
      simp only [↓reduceIte, map_one, one_smul]
      exact P.s22b_Mbil_diag_mem_nK hW j i₀
    · exact hrat _ _ (by simp) (by simp)
        (by rw [s22b_pairing_inr_inl]; simp [hij])
  · exact hrat _ _ (by simp) (by simp) (by simp [pairing, QuadraticMap.polarBilin_apply_apply])

/-- **The `K`-span of the infinitesimal unitary transvections contains `M(X, Y)` for every
orthogonal pair `X, Y ∈ V_K`** (the plan for the gap in Lemmas 2.2.4/2.2.7: polarization). -/
theorem s22b_Mbil_mem_nK (hW : IsCompl P.W₁ P.W₂) {X Y : V (Kd d) n}
    (hXY : pairing (Kd d) n X Y = 0) : P.s22b_Mbil hW X Y ∈ P.s22b_nK hW := by
  have hn := P.s22b_n_pos
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = P.s22b_Mbil hW (bcV ℚ (Kd d) n (f ℚ n ⟨0, by omega⟩, 0))
      (bcV ℚ (Kd d) n (0, e ℚ n ⟨0, by omega⟩)) := ⟨_, rfl⟩
  have key := s22b_bilin_mem_of_basis (basisV (Kd d) n)
    (P.s22b_Mbil hW - (pairing (Kd d) n).compr₂ (LinearMap.toSpanSingleton (Kd d) _ M₀))
    (P.s22b_nK hW) (fun k l => by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.compr₂_apply,
        LinearMap.toSpanSingleton_apply, ← s22b_bcV_basisV (F := ℚ) k,
        ← s22b_bcV_basisV (F := ℚ) l, s22b_pairing_bcV, hM₀]
      obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
      obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
      exact P.s22b_Mbil_basis_mem_nK hW _ k l) X Y
  rwa [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.compr₂_apply,
    LinearMap.toSpanSingleton_apply, hXY, zero_smul, sub_zero] at key


/-! ## Proof of Lemma 2.2.4 -/

/-- `M(a, c) = 2√-d D_{a,c}` for `a ∈ W₁`, `c ∈ W₂`. -/
theorem s22b_Mbil_W₁_W₂ (hW : IsCompl P.W₁ P.W₂) {a c : V (Kd d) n} (ha : a ∈ P.W₁)
    (hc : c ∈ P.W₂) : P.s22b_Mbil hW a c = (2 * Kd.sqrtNeg d) • s22b_Dop a c := by
  refine LinearMap.ext fun z => ?_
  rw [s22b_Mbil_apply, LinearMap.smul_apply, s22b_Dop_apply, P.s22b_ηK_of_mem_W₁ hW _ ha,
    P.s22b_ηK_of_mem_W₂ hW _ hc, s22b_σ_sqrtNeg, map_smul, map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, smul_sub, smul_smul]
  module

/-- `D_{a,c} ∈ 𝔫` for `a ∈ W₁`, `c ∈ W₂`, `(a, c) = 0`. -/
theorem s22b_Dop_mem_nK (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) {a c : V (Kd d) n}
    (ha : a ∈ P.W₁) (hc : c ∈ P.W₂) (hac : pairing (Kd d) n a c = 0) :
    s22b_Dop a c ∈ P.s22b_nK hW := by
  have h := Submodule.smul_mem _ (2 * Kd.sqrtNeg d)⁻¹ (P.s22b_Mbil_mem_nK hW hac)
  rwa [P.s22b_Mbil_W₁_W₂ hW ha hc, smul_smul, inv_mul_cancel₀, one_smul] at h
  exact mul_ne_zero two_ne_zero (s22b_sqrtNeg_ne_zero hd)

/-- The pairing between `W₁` and `W₂` is nondegenerate. -/
theorem s22b_nd₁₂ (hW : IsCompl P.W₁ P.W₂) (c : V (Kd d) n) (hc : c ∈ P.W₂) (hc0 : c ≠ 0) :
    ∃ z ∈ P.W₁, pairing (Kd d) n z c ≠ 0 := by
  by_contra h
  push Not at h
  apply hc0
  apply s22b_pairing_nondeg
  intro v
  rw [s22b_pairing_comm, ← P.s22b_decomp hW v, map_add, LinearMap.add_apply,
    h _ (P.s22b_proj₁_mem hW v), P.s22b_pairing_W₂ (P.s22b_proj₂_mem hW v) hc, add_zero]

theorem s22b_nd₂₁ (hW : IsCompl P.W₁ P.W₂) (c : V (Kd d) n) (hc : c ∈ P.W₁) (hc0 : c ≠ 0) :
    ∃ z ∈ P.W₂, pairing (Kd d) n z c ≠ 0 := by
  by_contra h
  push Not at h
  apply hc0
  apply s22b_pairing_nondeg
  intro v
  rw [s22b_pairing_comm, ← P.s22b_decomp hW v, map_add, LinearMap.add_apply,
    P.s22b_pairing_W₁ (P.s22b_proj₁_mem hW v) hc, h _ (P.s22b_proj₂_mem hW v), add_zero]

theorem s22b_Mbil_bcV_self (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n y) =
      bcV ℚ (Kd d) n ((2 : ℚ) • (pairing ℚ n y x • P.fη hW x - pairing ℚ n y (P.fη hW x) • x)) := by
  rw [s22b_Mbil_apply, P.ηK_bcV hd hW, ← fη, s22b_pairing_bcV, s22b_pairing_bcV,
    s22b_pairing_comm x y, s22b_pairing_comm (P.fη hW x) y]
  simp only [map_smul, map_sub, algebraMap_smul]
  module

/-- An endomorphism commuting with all `N_x` (`x` rational isotropic) commutes with `𝔫`. -/
theorem s22b_commute_nK (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x : V ℚ n, Q ℚ n x = 0 → ∀ y, g (pairing ℚ n y x • P.fη hW x -
      pairing ℚ n y (P.fη hW x) • x) = pairing ℚ n (g y) x • P.fη hW x -
      pairing ℚ n (g y) (P.fη hW x) • x)
    (T : Module.End (Kd d) (V (Kd d) n)) (hT : T ∈ P.s22b_nK hW) :
    s22b_bcEnd (F' := Kd d) g * T = T * s22b_bcEnd (F' := Kd d) g := by
  let Z : Submodule (Kd d) (Module.End (Kd d) (V (Kd d) n)) :=
    LinearMap.ker (LinearMap.mulLeft (Kd d) (s22b_bcEnd (F' := Kd d) g) -
      LinearMap.mulRight (Kd d) (s22b_bcEnd (F' := Kd d) g))
  have hle : P.s22b_nK hW ≤ Z := by
    rw [s22b_nK, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show _ = _
    rw [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero]
    apply s22b_linearMap_ext_bcV (F := ℚ)
    intro y
    rw [Module.End.mul_apply, Module.End.mul_apply, s22b_bcEnd_bcV, P.s22b_Mbil_bcV_self hd hW,
      P.s22b_Mbil_bcV_self hd hW, s22b_bcEnd_bcV, map_smul, hg x hx y]
  have := hle hT
  simpa [Z, sub_eq_zero] using this

theorem s22b_not_li_of_eq_smul {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (v w : E) (μ : K) (h : w = μ • v) : ¬ LinearIndependent K ![v, w] := by
  intro hli
  have := (LinearIndependent.pair_iff.mp hli μ (-1) (by rw [h, neg_one_smul, add_neg_cancel])).2
  exact one_ne_zero (neg_eq_zero.mp this)

/-- An endomorphism of `V_K` all of whose vectors in a subspace `A` are eigenvectors acts on `A`
by a scalar. -/
theorem s22b_scalar_of_eigen (G : Module.End (Kd d) (V (Kd d) n)) (A : Submodule (Kd d) (V (Kd d) n))
    (h : ∀ a ∈ A, ∃ μ : Kd d, G a = μ • a) : ∃ μ : Kd d, ∀ a ∈ A, G a = μ • a := by
  have hA : ∀ a ∈ A, G a ∈ A := by
    intro a ha
    obtain ⟨μ, hμ⟩ := h a ha
    rw [hμ]; exact A.smul_mem _ ha
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := G.restrict hA) (fun v => by
      obtain ⟨ν, hν⟩ := h v v.2
      apply s22b_not_li_of_eq_smul _ _ ν
      apply Subtype.ext
      simp [hν])
  refine ⟨μ, fun a ha => ?_⟩
  have := LinearMap.congr_fun hμ ⟨a, ha⟩
  simpa using congrArg Subtype.val this

/-- The direction "`⇒`" of Lemma 2.2.4: a linear automorphism of `V_ℚ` commuting with
`ρ(Spin(V_ℚ)_P)` is some `η_λ`, `λ ≠ 0`. -/
theorem s22b_centralizer (hd : 0 < d) (hn : 2 ≤ n) (hW : IsCompl P.W₁ P.W₂)
    (g : V ℚ n ≃ₗ[ℚ] V ℚ n) (hcomm : ∀ h ∈ P.spinPℚ, g * rho ℚ n h = rho ℚ n h * g) :
    ∃ l : Kd d, l ≠ 0 ∧ (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.η hW l := by
  -- Step 1: `g` commutes with the infinitesimal transvections `N_x`.
  have hN : ∀ x : V ℚ n, Q ℚ n x = 0 → ∀ y, (g : V ℚ n →ₗ[ℚ] V ℚ n)
      (pairing ℚ n y x • P.fη hW x - pairing ℚ n y (P.fη hW x) • x) =
      pairing ℚ n (g y) x • P.fη hW x - pairing ℚ n (g y) (P.fη hW x) • x := by
    intro x hx y
    have h := congrArg (fun e : V ℚ n ≃ₗ[ℚ] V ℚ n => e y)
      (hcomm _ (P.s22b_E_mem_spinPℚ hd hW 1 x hx))
    simp only [LinearEquiv.mul_apply, P.s22b_rho_E hd hW, one_smul, map_add] at h
    simpa using h
  set G := s22b_bcEnd (F' := Kd d) (g : V ℚ n →ₗ[ℚ] V ℚ n)
  -- Step 2: `G` commutes with `D_{a,c}` for `a ∈ W₁`, `c ∈ W₂`, `(a, c) = 0`, and conversely.
  have hD₁ : ∀ a ∈ P.W₁, ∀ c ∈ P.W₂, pairing (Kd d) n a c = 0 →
      G * s22b_Dop a c = s22b_Dop a c * G := fun a ha c hc hac =>
    P.s22b_commute_nK hd hW _ hN _ (P.s22b_Dop_mem_nK hd hW ha hc hac)
  have hD₂ : ∀ a ∈ P.W₂, ∀ c ∈ P.W₁, pairing (Kd d) n a c = 0 →
      G * s22b_Dop a c = s22b_Dop a c * G := fun a ha c hc hac => by
    rw [s22b_Dop_swap, mul_neg, neg_mul, hD₁ c hc a ha (by rw [s22b_pairing_comm]; exact hac)]
  have h2n₁ : 3 ≤ Module.finrank (Kd d) P.W₁ := by
    have := P.isPure.2.2; rw [show P.W₁ = ann (Kd d) n P.u₁ from rfl]; omega
  have h2n₂ : 3 ≤ Module.finrank (Kd d) P.W₂ := by
    have := P.isPure₂.2.2; rw [show P.W₂ = ann (Kd d) n P.u₂ from rfl]; omega
  -- Step 3: `G` acts on `W₁` and on `W₂` by scalars.
  obtain ⟨l₁, hl₁⟩ := s22b_scalar_of_eigen G P.W₁ fun a ha =>
    s22b_eigen_of_commute P.W₁ P.W₂ (fun a ha a' ha' => P.s22b_pairing_W₁ ha ha')
      hW.inf_eq_bot h2n₂ (P.s22b_nd₁₂ hW) G hD₁ a ha
  obtain ⟨l₂, hl₂⟩ := s22b_scalar_of_eigen G P.W₂ fun a ha =>
    s22b_eigen_of_commute P.W₂ P.W₁ (fun a ha a' ha' => P.s22b_pairing_W₂ ha ha')
      (by rw [inf_comm]; exact hW.inf_eq_bot) h2n₁ (P.s22b_nd₂₁ hW) G hD₂ a ha
  -- Step 4: `σ`-equivariance gives `l₂ = σ(l₁)`.
  have hn0 := P.s22b_n_pos
  have hl : l₂ = Kd.σ d l₁ := by
    let v₀ : V ℚ n := (0, e ℚ n ⟨0, by omega⟩)
    have hv₀ : v₀ ≠ 0 := by
      intro h
      have := congrArg (fun x : V ℚ n => x.2 ⟨0, by omega⟩) h
      simp [v₀, e] at this
    have hr := P.range_bcV_eq hd hW
    obtain ⟨a, ha, hav⟩ : bcV ℚ (Kd d) n v₀ ∈ {v | ∃ v₁ ∈ P.W₁, v = v₁ + σV n d v₁} := by
      rw [← hr]; exact ⟨v₀, rfl⟩
    obtain ⟨a', ha', hav'⟩ : bcV ℚ (Kd d) n (g v₀) ∈
        {v | ∃ v₁ ∈ P.W₁, v = v₁ + σV n d v₁} := by
      rw [← hr]; exact ⟨g v₀, rfl⟩
    have hσa : σV n d a ∈ P.W₂ := (P.σV_mem_W₂_iff a).mpr ha
    have hGv : bcV ℚ (Kd d) n (g v₀) = l₁ • a + l₂ • σV n d a := by
      have := s22b_bcEnd_bcV (F' := Kd d) (g : V ℚ n →ₗ[ℚ] V ℚ n) v₀
      rw [← LinearEquiv.coe_coe, ← this, hav, map_add, hl₁ a ha, hl₂ _ hσa]
    rw [hav'] at hGv
    obtain ⟨-, h2⟩ := P.s22b_decomp_unique hW ha' (P.W₁.smul_mem _ ha)
      ((P.σV_mem_W₂_iff a').mpr ha') (P.W₂.smul_mem _ hσa) hGv
    have h1 := (P.s22b_decomp_unique hW ha' (P.W₁.smul_mem _ ha)
      ((P.σV_mem_W₂_iff a').mpr ha') (P.W₂.smul_mem _ hσa) hGv).1
    rw [h1, s22b_σV_smul] at h2
    have ha0 : σV n d a ≠ 0 := by
      intro h0
      have : a = 0 := by rw [← s22b_σV_σV a, h0, map_zero]
      apply hv₀
      apply s22b_bcV_injective (F' := Kd d)
      rw [hav, this, map_zero, add_zero, map_zero]
    have := sub_eq_zero.mpr h2
    rw [← sub_smul] at this
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right ha0)).symm
  -- Step 5: `G = η_{l₁}` on `V_K`, hence `g = η_{l₁}`.
  have hG : ∀ v, G v = P.ηK hW l₁ v := by
    intro v
    rw [← P.s22b_decomp hW v, map_add, hl₁ _ (P.s22b_proj₁_mem hW v),
      hl₂ _ (P.s22b_proj₂_mem hW v), P.s22b_ηK_add_mem hW _ (P.s22b_proj₁_mem hW v)
      (P.s22b_proj₂_mem hW v), hl]
  have hgη : (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.η hW l₁ := by
    refine LinearMap.ext fun y => s22b_bcV_injective (F' := Kd d) ?_
    rw [← s22b_bcEnd_bcV, hG, P.ηK_bcV hd hW]
  refine ⟨l₁, fun h0 => ?_, hgη⟩
  have : (g : V ℚ n →ₗ[ℚ] V ℚ n) = 0 := by rw [hgη, h0, P.η_zero hd hW]
  have hv : (0, e ℚ n ⟨0, by omega⟩) = (0 : V ℚ n) := by
    apply g.injective
    rw [map_zero]
    exact LinearMap.congr_fun this _
  have := congrArg (fun x : V ℚ n => x.2 ⟨0, by omega⟩) hv
  simp [e] at this

/-- An element of `Spin(V_ℚ)_P` acts trivially on `P_K` after change of coefficients. -/
theorem s22b_bcSpin_fix_PK (h : Spin ℚ n) (hh : h ∈ P.spinPℚ) (p : S (Kd d) n)
    (hp : p ∈ P.PK) : m (Kd d) n (bcC ℚ (Kd d) n h) p = p := by
  rw [← P.span_bcS_Pℚ] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, hq, rfl⟩ := hx
    rw [s22b_m_bcC_bcS, hh q hq]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem s22b_bcSpin_mem_spinL₁L₂ (h : Spin ℚ n) (hh : h ∈ P.spinPℚ) :
    bcSpin ℚ (Kd d) n h ∈ P.spinL₁L₂ :=
  ⟨⟨1, by
      rw [one_smul]
      exact P.s22b_bcSpin_fix_PK h hh _ (Submodule.subset_span (by simp))⟩,
    ⟨1, by
      rw [one_smul]
      exact P.s22b_bcSpin_fix_PK h hh _ (Submodule.subset_span (by simp))⟩⟩

/-- `ρ(Spin(V_K)_{ℓ₁,ℓ₂})` commutes with `η_λ` on `V_K`. -/
theorem s22b_rho_ηK (hW : IsCompl P.W₁ P.W₂) (g : P.spinL₁L₂) (l : Kd d) (v : V (Kd d) n) :
    rho (Kd d) n g (P.ηK hW l v) = P.ηK hW l (rho (Kd d) n g v) := by
  have ha := P.s22b_proj₁_mem hW v
  have hb := P.s22b_proj₂_mem hW v
  rw [← P.s22b_decomp hW v, P.s22b_ηK_add_mem hW _ ha hb, map_add, map_add, map_smul, map_smul,
    P.s22b_ηK_add_mem hW _ (P.rho_mem_W₁ g _ ha) (P.rho_mem_W₂ g _ hb)]

/-- The direction "`⇐`" of Lemma 2.2.4: `η_λ` commutes with `ρ(Spin(V_ℚ)_P)`. -/
theorem s22b_η_commute (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (h : Spin ℚ n)
    (hh : h ∈ P.spinPℚ) (y : V ℚ n) :
    P.η hW l (rho ℚ n h y) = rho ℚ n h (P.η hW l y) := by
  apply s22b_bcV_injective (F' := Kd d)
  rw [← P.ηK_bcV hd hW, ← s22b_rho_bcSpin, ← s22b_rho_bcSpin, ← P.ηK_bcV hd hW]
  exact (P.s22b_rho_ηK hW ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ h hh⟩ l _).symm

theorem s22b_lemma2_2_4 (hd : 0 < d) (hn : 2 ≤ n) (hW : IsCompl P.W₁ P.W₂)
    (g : V ℚ n ≃ₗ[ℚ] V ℚ n) :
    (g ∈ Otilde n d ∧ ∀ h ∈ P.spinPℚ, g * rho ℚ n h = rho ℚ n h * g) ↔
      ∃ l : Kd d, l ≠ 0 ∧ (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.η hW l := by
  constructor
  · rintro ⟨-, hcomm⟩
    exact P.s22b_centralizer hd hn hW g hcomm
  · rintro ⟨l, hl, hg⟩
    have hg' : ∀ x, g x = P.η hW l x := fun x => LinearMap.congr_fun hg x
    refine ⟨⟨Kd.Nm d l, ⟨l, hl, rfl⟩, fun x y => ?_⟩, fun h hh => ?_⟩
    · rw [hg', hg', P.pairing_η hd hW]
    · refine LinearEquiv.ext fun y => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg', hg', P.s22b_η_commute hd hW l h hh]

/-- **Lemma 2.2.4** (`lemma-centralizer-of-rho-Spin-V-P`): the centralizer of `ρ(Spin(V_ℚ)_P)` in
`Õ(V_ℚ)` is `η(K^×)`. That is, for `g ∈ GL(V_ℚ)`: `g ∈ Õ(V_ℚ)` and `g` commutes with every `ρ(h)`,
`h ∈ Spin(V_ℚ)_P`, if and only if `g = η_λ` for some `λ ∈ K^×`.

Hypotheses of the paper at this point: `P` non-isotropic (hence `V_K = W₁ ⊕ W₂`, which is needed to
define `η`), `K` imaginary quadratic (`0 < d`). The group is the rational group `Spin(V_ℚ)_P`, as
printed. We add `2 ≤ n` (the paper's standing hypothesis), which the statement needs: for `n = 1`,
`Spin(V_K)_P ≅ SL₂(K)` and `W₁ ≅ W₁* ≅ W₂` as representations, so the commutant of
`ρ(Spin(V_ℚ)_P)` is a quaternion algebra over `ℚ`, larger than `K`.

Proof (the paper's, `s22b_lemma2_2_4`): `η(K^×)` centralizes `ρ(Spin(V_ℚ)_P)` (`s22b_η_commute`) and
`(η_λ v, η_λ v')_V = Nm(λ)(v, v')_V` (`pairing_η`); conversely `g` acts on `W₁`, `W₂` by scalars
`λ₁, λ₂`, and `σ g σ = g` gives `λ₂ = σ(λ₁)` (`s22b_centralizer`, steps 4–5).

Gap in the paper (filled): "`W₁` and `W₂` are `g`-invariant and `g` acts on `Wᵢ` via
multiplication by a scalar" is stated without argument. It needs that `W₁`, `W₂` are non-isomorphic
absolutely irreducible representations of `Spin(V_ℚ)_P`, i.e. the Zariski density of `Spin(V_ℚ)_P`
in the algebraic group `Spin(V_K)_P ≅ SL(W₁)`, which the paper does not prove. Filled in
`s22b_centralizer` (steps 1–3): for isotropic `x ∈ V_ℚ` the unitary transvection
`E_{x,1} = 1 + ι(f x) ι(x)` (`f = η_{√-d}`) lies in `Spin(V_ℚ)_P` (`s22b_E_mem_spinPℚ`) and acts by
`1 + N_x`, so `g` commutes with every `N_x`; the `K`-span of the `N_x` contains the operators
`D_{a,c}` (`a ∈ W₁`, `c ∈ W₂`, `(a, c) = 0`) (`s22b_Dop_mem_nK`); and an endomorphism of `V_K`
commuting with all `D_{a,c}` preserves `W₁` and `W₂` and acts on each by a scalar (Schur step
`s22b_eigen_of_commute`, then `s22b_scalar_of_eigen`). -/
theorem _root_.WeilClasses.lemma2_2_4 (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (g : V ℚ n ≃ₗ[ℚ] V ℚ n) :
    (g ∈ Otilde n d ∧ ∀ h ∈ P.spinPℚ, g * rho ℚ n h = rho ℚ n h * g) ↔
      ∃ l : Kd d, l ≠ 0 ∧
        (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.η (P.isCompl_of_not_isIsotropic hd hP) l :=
  P.s22b_lemma2_2_4 hd hn (P.isCompl_of_not_isIsotropic hd hP) g

end KSecant

end WeilClasses
