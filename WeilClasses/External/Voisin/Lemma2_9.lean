module

public import WeilClasses.AbelianVariety.Product

/-!
# [Schoen, Prop. 10] from push-forward, by Voisin's Lemma 2.9

Corollary 1.6.1 uses [Schoen, Prop. 10] (`SchoenDegeneration`): if the Hodge–Weil classes of all
polarized abelian sixfolds of Weil type for `K = ℚ(√-d)` with discriminant `-1` are algebraic, so are
those of all abelian fourfolds of Weil type for `K`. This file proves it
(`schoenDegeneration_of_pushforward`) from `PullbackClosed`, `SubalgebraClosed`, `LefschetzOneOne`
and the push-forward hypothesis `PushforwardClosed` (`WeilClasses.Defs`), by the
argument of C. Voisin (Séminaire Bourbaki, exposé 1248, January 2026, Lemme 2.9 and
Corollaire 2.10): the Weil classes of `A₂` are push-forwards `pr₂,*(pr₁^*w₁' ∪ w)` of Weil classes
`w` of `A₁ × A₂`, for `A₁` a Weil surface, whose Weil classes are algebraic by Lefschetz `(1,1)`.

Let `A₂` be an abelian fourfold of Weil type and `w₂` a Hodge–Weil class of `A₂`.

1. **A compatible polarization** (`vo_polarize`): for an ample `Θ`, `h = Θ + η(√-d)^*Θ / d` is ample
   and `η(k)^*h = Nm(k) h` (it suffices to check `k = √-d`, `vo_norm_of_sqrtNeg`). **Its
   discriminant is positive** (`vo_disc_pos`): in a `K`-basis, the Gram determinant `δ` of van
   Geemen's form `H` is rational and `δ > 0`. The latter is the sign `(-1)^m` of the determinant of a
   Hermitian form of signature `(m, m)` (`vo_herm_det_sign`): over `ℂ`, `H` is the form
   `E(ū, v)` on the `√-d`-eigenspace `W*` of `η(√-d)ᵀ` in `H₁(A, ℂ)`, definite of opposite signs on
   the two eigenspaces of `Jᵀ` in `W*` (ampleness), which are `H`-orthogonal (`h` is of type
   `(1,1)`) and of dimension `m` (the Weil condition, through the contraction `θ_h`); a block
   decomposition gives the sign (`vo_det_sign`).
2. **A Weil surface of discriminant `-δ`** (`vo_XS`): `A₁ = E₊ × E₋`, the product of the elliptic
   curves `ℚ²` with `η(√-d) = f`, `f e₀ = e₁`, `f e₁ = -d e₀`, and the two CM types `J = ± f/√d`,
   polarized by `pr₁^*Θ₊ + δ pr₂^*Θ₋`; its Hermitian form is `diag(d, -dδ)` (`vo_det_gram_surface`).
3. **The sixfold** `A₁ × A₂` (`vo_X6`, an `AbVar (2 * 3)` since `2 * 1 + 2 * 2` reduces to `2 * 3`),
   with `η = η₁ × η₂` and `h = pr₁^*h₁ + pr₂^*h₂`, is a polarized abelian sixfold of Weil type of
   discriminant `-d²δ · δ = -Nm(dδ)`, i.e. `-1` (`vo_X6_discIs`; block-diagonal Gram matrix).
4. **A Hodge–Weil class of the product** (`vo_w_mem_HW`): with `A = a₁ ∧ b₁ - d a₀ ∧ b₀` and
   `B = a₀ ∧ b₁ + a₁ ∧ b₀` on `A₁` (`aᵢ = pr₁^*eᵢ`, `bⱼ = pr₂^*eⱼ`), which satisfy `2A = ω₁ + ω̄₁`,
   `2√-d B = ω₁ - ω̄₁` for the generators `ω₁` of `⋀²W₁` and `ω̄₁` of `⋀²W̄₁`, and
   `v₂ = (√-d)·(ω - ω̄)` (a rational class, `vo_v2`) if `w₂ = ω + ω̄` over `K`, the class
   `w = pr₁^*A ∪ pr₂^*w₂ + pr₁^*B ∪ pr₂^*v₂` is `pr₁^*ω₁ ∪ pr₂^*ω + pr₁^*ω̄₁ ∪ pr₂^*ω̄` over `K`,
   a Hodge–Weil class of `A₁ × A₂`.
5. `w` is algebraic by the sixfold statement; `A` is of type `(1,1)` (`vo_AS_hodge`), so `pr₁^*A`
   and `pr₁^*A ∪ w` are algebraic.
6. `pr₂,*(pr₁^*A ∪ w) = (∫ A²) w₂ + (∫ AB) v₂ = 2d w₂` (`vo_pushSnd_w`; `A² = 2d [pt]`, `AB = 0`), so
   `w₂` is algebraic by `PushforwardClosed`.

Two points of the argument need care: the surface of step 2 exists only for `δ > 0` (a Weil surface
has signature `(1,1)`, so its discriminant is negative), hence the positivity of `δ` in step 1; and
the product `pr₁^*w₁ ∪ pr₂^*w₂` of two Hodge–Weil classes is not a Hodge–Weil class of the product
(its parts `ω₁ ∧ ω̄` and `ω̄₁ ∧ ω` have mixed type), hence the class `w` of step 4. The surface has
discriminant `-δ`, which is `-δ⁻¹` modulo norms (`δ² = Nm(δ)`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ### Actions of `K = ℚ(√-d)` -/

section KAction

variable {d : ℚ}

/-- The action of `K` with `√-d ↦ φ`, for `φ² = -d`: `a + b√-d ↦ a + b φ`. -/
noncomputable def vo_etaOf {M : Type*} [AddCommGroup M] [Module ℚ M] (hd : 0 < d)
    (φ : Module.End ℚ M) (hφ : φ * φ = -(d • 1)) : Kd d →+* Module.End ℚ M where
  toFun k := Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • φ
  map_one' := by
    rw [show (1 : Kd d) = algebraMap ℚ (Kd d) 1 from (map_one _).symm, s24b_ratPart_algebraMap,
      s24b_sqrtNegCoeff_algebraMap hd]
    simp
  map_mul' x y := by
    rw [s24b_ratPart_mul hd, s24b_sqrtNegCoeff_mul hd]
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hφ]
    module
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, add_smul]
    abel

theorem vo_etaOf_sqrtNeg {M : Type*} [AddCommGroup M] [Module ℚ M] (hd : 0 < d)
    (φ : Module.End ℚ M) (hφ : φ * φ = -(d • 1)) : vo_etaOf hd φ hφ (Kd.sqrtNeg d) = φ := by
  show Kd.ratPart d (Kd.sqrtNeg d) • (1 : Module.End ℚ M) + Kd.sqrtNegCoeff d (Kd.sqrtNeg d) • φ = φ
  rw [s24b_ratPart_sqrtNeg, s24b_sqrtNegCoeff_sqrtNeg hd, zero_smul, one_smul, zero_add]

/-- Every action of `K` is `a + b√-d ↦ a + b η(√-d)`. -/
theorem vo_eta_apply {M : Type*} [AddCommGroup M] [Module ℚ M] (hd : 0 < d)
    (η : Kd d →+* Module.End ℚ M) (k : Kd d) :
    η k = Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • η (Kd.sqrtNeg d) := by
  conv_lhs => rw [Kd.eq_ratPart_add_sqrtNegCoeff hd k]
  rw [map_add, map_mul, RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- `η(√-d)² = -d`. -/
theorem vo_eta_sq {M : Type*} [AddCommGroup M] [Module ℚ M] (hd : 0 < d)
    (η : Kd d →+* Module.End ℚ M) : η (Kd.sqrtNeg d) * η (Kd.sqrtNeg d) = -(d • 1) := by
  rw [← map_mul, s24b_sqrtNeg_mul_self hd.le, RingHom.map_rat_algebraMap,
    Algebra.algebraMap_eq_smul_one, neg_smul]

/-- The action `η₁ × η₂` of `K` on `H¹(A₁ × A₂)`. -/
noncomputable def vo_prodη {g₁ g₂ : ℕ} (η₁ : Kd d →+* Module.End ℚ (H1 ℚ g₁))
    (η₂ : Kd d →+* Module.End ℚ (H1 ℚ g₂)) : Kd d →+* Module.End ℚ (H1 ℚ (g₁ + g₂)) :=
  vo_prodEndHom.comp (η₁.prod η₂)

@[simp]
theorem vo_prodη_apply {g₁ g₂ : ℕ} (η₁ : Kd d →+* Module.End ℚ (H1 ℚ g₁))
    (η₂ : Kd d →+* Module.End ℚ (H1 ℚ g₂)) (k : Kd d) :
    vo_prodη η₁ η₂ k = vo_prodEnd (η₁ k) (η₂ k) := rfl

/-- `(√-d)² = -d` in `ℂ`. -/
theorem vo_sqrtNeg_mul_self (hd : 0 < d) : sqrtNeg d * sqrtNeg d = -(d : ℂ) := by
  rw [← sq, sqrtNeg_sq hd.le]

/-- `Nm(a + b√-d) = a² + d b²`. -/
theorem vo_Nm_eq (hd : 0 < d) (k : Kd d) :
    Kd.Nm d k = Kd.ratPart d k ^ 2 + d * Kd.sqrtNegCoeff d k ^ 2 := by
  apply Rat.cast_injective (α := ℂ)
  rw [Kd.coe_Nm hd]
  have hk := congrArg (fun z : Kd d => (z : ℂ)) (Kd.eq_ratPart_add_sqrtNegCoeff hd k)
  simp only [Subfield.coe_add, Subfield.coe_mul, s24b_coe_algebraMap] at hk
  rw [hk]
  have hs : (Kd.sqrtNeg d : ℂ) = WeilClasses.sqrtNeg d := rfl
  rw [hs, map_add, map_mul, map_ratCast, map_ratCast, fnd_conj_sqrtNeg]
  have hsq := sqrtNeg_sq hd.le
  push_cast
  linear_combination (-(Kd.sqrtNegCoeff d k : ℂ) ^ 2) * hsq

/-- `1, √-d` is a `ℚ`-basis of `K`. -/
noncomputable def vo_basisK (hd : 0 < d) : Module.Basis (Fin 2) ℚ (Kd d) :=
  Module.Basis.mk (v := ![1, Kd.sqrtNeg d])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h := congrArg (fun x : Kd d => (x : ℂ)) hst
      simp only [Subfield.coe_add, Kd.fnd_coe_smul, Subfield.coe_one, mul_one,
        Subfield.coe_zero] at h
      exact Kd.fnd_linIndep hd h)
    (by
      rintro z -
      rw [Kd.eq_ratPart_add_sqrtNegCoeff hd z, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))

theorem vo_basisK_zero (hd : 0 < d) : vo_basisK hd 0 = 1 := by simp [vo_basisK]

theorem vo_basisK_one (hd : 0 < d) : vo_basisK hd 1 = Kd.sqrtNeg d := by simp [vo_basisK]

/-- **`K`-bases**: if `φ² = -d` on a `ℚ`-vector space of dimension `2k`, there are `b₁, …, b_k` such
that `bᵢ, φ(bᵢ)` are linearly independent (a basis of `M` over `K = ℚ(√-d)` acting through `φ`). -/
theorem vo_exists_kBasis {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (hd : 0 < d) (φ : Module.End ℚ M) (hφ : φ * φ = -(d • 1)) {k : ℕ}
    (hk : Module.finrank ℚ M = 2 * k) :
    ∃ b : Fin k → M, LinearIndependent ℚ (Sum.elim b (fun i => φ (b i))) := by
  let _ : Module (Kd d) M := Module.compHom M (vo_etaOf hd φ hφ)
  have hsmul : ∀ (c : Kd d) (x : M), c • x = vo_etaOf hd φ hφ c x := fun _ _ => rfl
  have _ : IsScalarTower ℚ (Kd d) M := ⟨fun q c x => by
    rw [hsmul, hsmul, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap,
      Algebra.algebraMap_eq_smul_one, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]⟩
  have _ : Module.Finite (Kd d) M := Module.Finite.of_restrictScalars_finite ℚ (Kd d) M
  have hfin := Module.finrank_mul_finrank ℚ (Kd d) M
  rw [Module.finrank_eq_card_basis (vo_basisK hd), Fintype.card_fin, hk] at hfin
  have hkM : Module.finrank (Kd d) M = k := by omega
  let bK : Module.Basis (Fin k) (Kd d) M := (Module.finBasis (Kd d) M).reindex (finCongr hkM)
  let bQ := (vo_basisK hd).smulTower bK
  refine ⟨fun i => bK i, ?_⟩
  have heq : Sum.elim (fun i => bK i) (fun i => φ (bK i)) =
      bQ ∘ Sum.elim (fun i => ((0 : Fin 2), i)) (fun i => ((1 : Fin 2), i)) := by
    funext x
    rcases x with i | i
    · simp [bQ, Module.Basis.smulTower_apply, vo_basisK_zero]
    · simp only [Sum.elim_inr, Function.comp_apply, bQ, Module.Basis.smulTower_apply,
        vo_basisK_one, hsmul, vo_etaOf_sqrtNeg]
  rw [heq]
  refine bQ.linearIndependent.comp _ ?_
  rintro (i | i) (j | j) h <;> simp_all

end KAction

/-! ### The polarization: from `η(√-d)` to all of `K` -/

section Norm

variable {d : ℚ}

theorem vo_eval2_eq_dc {F : Type*} [Field F] [CharZero F] {n : ℕ} (ξ : S F n)
    (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ a b = ExteriorAlgebra.algebraMapInv
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) b
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) a ξ)) := by
  simp only [eval2, D, main_coord_empty, AlgHom.toLinearMap_apply]

/-- If `η(√-d)` multiplies `h` by `d`, then `E(a ∘ η(√-d), b) = -E(a, b ∘ η(√-d))`. -/
theorem vo_eval2_skew {g : ℕ} (hd : 0 < d) (η : Kd d →+* Module.End ℚ (H1 ℚ g)) {h : S ℚ g}
    (hs : ExteriorAlgebra.map (η (Kd.sqrtNeg d)) h = d • h) (a b : Module.Dual ℚ (H1 ℚ g)) :
    eval2 ℚ g h (a ∘ₗ η (Kd.sqrtNeg d)) b = -eval2 ℚ g h a (b ∘ₗ η (Kd.sqrtNeg d)) := by
  set φ := η (Kd.sqrtNeg d) with hφ
  have hE : ∀ a b, eval2 ℚ g h (a ∘ₗ φ) (b ∘ₗ φ) = d * eval2 ℚ g h a b := by
    intro a b
    rw [← vo_eval2_map, hs, vo_eval2_smul]
  have hsq : φ ∘ₗ φ = -(d • LinearMap.id) := by
    rw [← Module.End.mul_eq_comp, hφ, vo_eta_sq hd η]
    rfl
  have h1 := hE a (b ∘ₗ φ)
  rw [LinearMap.comp_assoc, hsq] at h1
  have hb : b ∘ₗ (-(d • LinearMap.id)) = (-d) • b := by
    ext x; simp
  rw [hb, main_eval2_smul_right] at h1
  have hd0 : d ≠ 0 := hd.ne'
  have : d * (eval2 ℚ g h (a ∘ₗ φ) b + eval2 ℚ g h a (b ∘ₗ φ)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hd0
  · linarith

/-- If `η(√-d)` multiplies a class `h` of degree `2` by `d = Nm(√-d)`, then `η(k)` multiplies it by
`Nm(k)` for every `k ∈ K`. -/
theorem vo_norm_of_sqrtNeg {g : ℕ} (hd : 0 < d) (η : Kd d →+* Module.End ℚ (H1 ℚ g))
    {h : S ℚ g} (h2 : h ∈ ⋀[ℚ]^2 (H1 ℚ g))
    (hs : ExteriorAlgebra.map (η (Kd.sqrtNeg d)) h = d • h) (k : Kd d) :
    ExteriorAlgebra.map (η k) h = Kd.Nm d k • h := by
  set φ := η (Kd.sqrtNeg d) with hφ
  have hE : ∀ a b, eval2 ℚ g h (a ∘ₗ φ) (b ∘ₗ φ) = d * eval2 ℚ g h a b := by
    intro a b
    rw [← vo_eval2_map, hs, vo_eval2_smul]
  have hskew : ∀ a b, eval2 ℚ g h (a ∘ₗ φ) b = -eval2 ℚ g h a (b ∘ₗ φ) :=
    vo_eval2_skew hd η hs
  have hk : η k = Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • φ := vo_eta_apply hd η k
  apply main_eq_of_dc (main_map_mem_exteriorPower _ 2 h2) (Submodule.smul_mem _ _ h2)
  intro a b
  rw [← vo_eval2_eq_dc, ← vo_eval2_eq_dc, vo_eval2_map, vo_eval2_smul, vo_Nm_eq hd, hk]
  have hc : ∀ c : Module.Dual ℚ (H1 ℚ g), c ∘ₗ (Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • φ) =
      Kd.ratPart d k • c + Kd.sqrtNegCoeff d k • (c ∘ₗ φ) := by
    intro c; ext x; simp
  rw [hc, hc]
  simp only [vo_eval2_add_left, vo_eval2_add_right, vo_eval2_smul_left, main_eval2_smul_right, hE]
  rw [hskew]
  ring

/-- `map (c • id)` multiplies classes of degree `2` by `c²`. -/
theorem vo_map_smul_id_two {F : Type*} [Field F] {n : ℕ} (c : F) {x : S F n}
    (hx : x ∈ ⋀[F]^2 (H1 F n)) :
    ExteriorAlgebra.map (c • LinearMap.id : H1 F n →ₗ[F] H1 F n) x = c ^ 2 • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    have : (c • LinearMap.id : H1 F n →ₗ[F] H1 F n) ∘ w = fun i => c • w i := by
      funext i; simp
    rw [this, main_lef_ιMulti_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul a y _ hy => rw [map_smul, hy, smul_comm]

end Norm

/-! ### Step 1: a polarization compatible with `η` -/

section Polarize

variable {d : ℚ} {m : ℕ} {A : AbVar (2 * m)}

/-- The class `h = Θ + η(√-d)^*Θ / d` of step 1, for the ample class `Θ` chosen on `A`. -/
noncomputable def vo_polClass (X : WeilType A d) : S ℚ (2 * m) :=
  A.polarizable.choose + d⁻¹ • ExteriorAlgebra.map (X.η (Kd.sqrtNeg d)) A.polarizable.choose

theorem vo_polClass_mem (X : WeilType A d) : vo_polClass X ∈ ⋀[ℚ]^2 (H1 ℚ (2 * m)) := by
  have hΘ2 := A.polarizable.choose_spec.mem_exteriorPower_two
  exact Submodule.add_mem _ hΘ2 (Submodule.smul_mem _ _ (main_map_mem_exteriorPower _ 2 hΘ2))

theorem vo_polClass_sqrtNeg (hd : 0 < d) (X : WeilType A d) :
    ExteriorAlgebra.map (X.η (Kd.sqrtNeg d)) (vo_polClass X) = d • vo_polClass X := by
  have hΘ2 := A.polarizable.choose_spec.mem_exteriorPower_two
  set Θ := A.polarizable.choose
  set φ := X.η (Kd.sqrtNeg d) with hφ
  have hsq : ExteriorAlgebra.map φ (ExteriorAlgebra.map φ Θ) = d ^ 2 • Θ := by
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Module.End.mul_eq_comp, hφ,
      vo_eta_sq hd X.η]
    have h1 : (-(d • 1) : Module.End ℚ (H1 ℚ (2 * m))) = (-d) • LinearMap.id := by
      ext x; simp
    rw [h1, vo_map_smul_id_two _ hΘ2, neg_sq]
  have hd0 := hd.ne'
  rw [vo_polClass, map_add, map_smul, hsq, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hd0,
    one_smul, show d⁻¹ * d ^ 2 = d by field_simp, add_comm]

theorem vo_polClass_ample (X : WeilType A d) (hd : 0 < d) : IsAmple (2 * m) A.J (vo_polClass X) := by
  have hΘ := A.polarizable.choose_spec
  set Θ := A.polarizable.choose
  set φ := X.η (Kd.sqrtNeg d)
  have hcomm : bcMap ℚ ℝ φ ∘ₗ A.J = A.J ∘ₗ bcMap ℚ ℝ φ := X.isHodge _
  have hbc : bcS ℚ ℝ (2 * m) (vo_polClass X) = bcS ℚ ℝ (2 * m) Θ +
      d⁻¹ • ExteriorAlgebra.map (bcMap ℚ ℝ φ) (bcS ℚ ℝ (2 * m) Θ) := by
    rw [vo_polClass, map_add, map_smul, main_bcS_map]
  have hJΘ := main_lef_map_bcS_of_hodge hΘ.1
  refine ⟨main_lef_hodge_one_of_map A.isComplex (vo_polClass_mem X) ?_, fun a ha => ?_⟩
  · rw [hbc, map_add, map_rat_smul, hJΘ, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← hcomm,
      ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply, hJΘ]
  · rw [hbc, vo_eval2_add, ← algebraMap_smul ℝ d⁻¹, vo_eval2_smul, vo_eval2_map]
    have e1 : (a ∘ₗ A.J) ∘ₗ bcMap ℚ ℝ φ = (a ∘ₗ bcMap ℚ ℝ φ) ∘ₗ A.J := by
      rw [LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc]
    rw [e1]
    have hpos := hΘ.2 a ha
    have hnn : 0 ≤ eval2 ℝ (2 * m) (bcS ℚ ℝ (2 * m) Θ) (a ∘ₗ bcMap ℚ ℝ φ)
        ((a ∘ₗ bcMap ℚ ℝ φ) ∘ₗ A.J) := by
      by_cases h0 : a ∘ₗ bcMap ℚ ℝ φ = 0
      · rw [h0, vo_eval2_zero_left]
      · exact (hΘ.2 _ h0).le
    have hdi : (0 : ℝ) ≤ algebraMap ℚ ℝ d⁻¹ := by
      rw [eq_ratCast]; exact_mod_cast (inv_pos.mpr hd).le
    nlinarith

/-- **Step 1.** An abelian variety of Weil type has a polarization compatible with `η`:
`h = Θ + η(√-d)^*Θ / d` for an ample class `Θ` (ample, with `η(k)^*h = Nm(k) h`). -/
noncomputable def vo_polarize (hd : 0 < d) (X : WeilType A d) : PolarizedWeilType A d where
  toWeilType := X
  h := vo_polClass X
  ample := vo_polClass_ample X hd
  norm := vo_norm_of_sqrtNeg hd X.η (vo_polClass_mem X) (vo_polClass_sqrtNeg hd X)

theorem vo_polarize_η (hd : 0 < d) (X : WeilType A d) : (vo_polarize hd X).η = X.η := rfl

theorem vo_polarize_HW (hd : 0 < d) (X : WeilType A d) : (vo_polarize hd X).HW = X.HW := rfl

end Polarize

/-! ### Products of polarized abelian varieties of Weil type -/

section ProductWeil

variable {d : ℚ}

/-- The dimensions in the Weil condition add up on products. -/
theorem vo_finrank_weil_prod {g₁ g₂ : ℕ} (η₁ : Kd d →+* Module.End ℚ (H1 ℚ g₁))
    (η₂ : Kd d →+* Module.End ℚ (H1 ℚ g₂)) (J₁ : Module.End ℝ (H1 ℝ g₁))
    (J₂ : Module.End ℝ (H1 ℝ g₂)) (μ : ℂ) :
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (vo_prodη η₁ η₂ (Kd.sqrtNeg d))) μ ⊓
        H10 (g₁ + g₂) (prodJ J₁ J₂)) =
      Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η₁ (Kd.sqrtNeg d))) μ ⊓ H10 g₁ J₁) +
        Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η₂ (Kd.sqrtNeg d))) μ ⊓
          H10 g₂ J₂) := by
  rw [vo_prodη_apply, vo_bcMap_prodEnd, H10, H10, H10, vo_complexifyH1_prodJ,
    vo_finrank_eigenspace_inf_prodEnd]

theorem vo_map_prodEnd_prod {F : Type*} [Field F] {g₁ g₂ : ℕ} (φ₁ : Module.End F (H1 F g₁))
    (φ₂ : Module.End F (H1 F g₂)) (x₁ : S F g₁) (x₂ : S F g₂) :
    ExteriorAlgebra.map (vo_prodEnd φ₁ φ₂)
        (ExteriorAlgebra.map (prodInl F g₁ g₂) x₁ + ExteriorAlgebra.map (prodInr F g₁ g₂) x₂) =
      ExteriorAlgebra.map (prodInl F g₁ g₂) (ExteriorAlgebra.map φ₁ x₁) +
        ExteriorAlgebra.map (prodInr F g₁ g₂) (ExteriorAlgebra.map φ₂ x₂) := by
  have e₁ : (vo_prodEnd φ₁ φ₂).comp (prodInl F g₁ g₂) = (prodInl F g₁ g₂).comp φ₁ :=
    LinearMap.ext fun x => by simp
  have e₂ : (vo_prodEnd φ₁ φ₂).comp (prodInr F g₁ g₂) = (prodInr F g₁ g₂).comp φ₂ :=
    LinearMap.ext fun x => by simp
  rw [map_add, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, e₁, e₂, ← ExteriorAlgebra.map_comp_map,
    ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply, AlgHom.comp_apply]

theorem vo_Nm_sqrtNeg (hd : 0 < d) : Kd.Nm d (Kd.sqrtNeg d) = d := by
  rw [vo_Nm_eq hd, s24b_ratPart_sqrtNeg, s24b_sqrtNegCoeff_sqrtNeg hd]
  ring

theorem vo_Nm_algebraMap (hd : 0 < d) (q : ℚ) : Kd.Nm d (algebraMap ℚ (Kd d) q) = q ^ 2 := by
  rw [vo_Nm_eq hd, s24b_ratPart_algebraMap, s24b_sqrtNegCoeff_algebraMap hd]
  ring

/-- The product polarization is compatible with `η₁ × η₂`. -/
theorem vo_norm_prod {g₁ g₂ : ℕ} (η₁ : Kd d →+* Module.End ℚ (H1 ℚ g₁))
    (η₂ : Kd d →+* Module.End ℚ (H1 ℚ g₂)) {h₁ : S ℚ g₁} {h₂ : S ℚ g₂}
    (hn₁ : ∀ k, ExteriorAlgebra.map (η₁ k) h₁ = Kd.Nm d k • h₁)
    (hn₂ : ∀ k, ExteriorAlgebra.map (η₂ k) h₂ = Kd.Nm d k • h₂) (k : Kd d) :
    ExteriorAlgebra.map (vo_prodη η₁ η₂ k)
        (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) h₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) h₂) =
      Kd.Nm d k •
        (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) h₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) h₂) := by
  rw [vo_prodη_apply, vo_map_prodEnd_prod, hn₁, hn₂, map_smul, map_smul, smul_add]

theorem vo_mem_two_prod {g₁ g₂ : ℕ} {h₁ : S ℚ g₁} {h₂ : S ℚ g₂}
    (hh₁ : h₁ ∈ ⋀[ℚ]^2 (H1 ℚ g₁)) (hh₂ : h₂ ∈ ⋀[ℚ]^2 (H1 ℚ g₂)) :
    ExteriorAlgebra.map (prodInl ℚ g₁ g₂) h₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) h₂ ∈
      ⋀[ℚ]^2 (H1 ℚ (g₁ + g₂)) :=
  Submodule.add_mem _ (main_map_mem_exteriorPower _ 2 hh₁) (main_map_mem_exteriorPower _ 2 hh₂)

/-- Van Geemen's form `H(x, y) = E(x, φᵀ y) + √-d E(x, y)` for a class `h` and `φ = η(√-d)`
(`PolarizedWeilType.herm`). -/
noncomputable def vo_herm (d : ℚ) {g : ℕ} (h : S ℚ g) (φ : Module.End ℚ (H1 ℚ g))
    (x y : Module.Dual ℚ (H1 ℚ g)) : ℂ :=
  (eval2 ℚ g h x (y ∘ₗ φ) : ℂ) + sqrtNeg d * (eval2 ℚ g h x y : ℂ)

theorem vo_herm_eq {m : ℕ} {A : AbVar (2 * m)} (X : PolarizedWeilType A d)
    (x y : Module.Dual ℚ (H1 ℚ (2 * m))) : X.herm x y = vo_herm d X.h (X.η (Kd.sqrtNeg d)) x y :=
  rfl

variable {g₁ g₂ : ℕ}

theorem vo_comp_prodFst_prodInl (x : Module.Dual ℚ (H1 ℚ g₁)) :
    (x ∘ₗ prodFst ℚ g₁ g₂) ∘ₗ prodInl ℚ g₁ g₂ = x := by
  rw [LinearMap.comp_assoc, vo_prodFst_comp_prodInl, LinearMap.comp_id]

theorem vo_comp_prodFst_prodInr (x : Module.Dual ℚ (H1 ℚ g₁)) :
    (x ∘ₗ prodFst ℚ g₁ g₂) ∘ₗ prodInr ℚ g₁ g₂ = 0 := by
  rw [LinearMap.comp_assoc, vo_prodFst_comp_prodInr, LinearMap.comp_zero]

theorem vo_comp_prodSnd_prodInl (x : Module.Dual ℚ (H1 ℚ g₂)) :
    (x ∘ₗ prodSnd ℚ g₁ g₂) ∘ₗ prodInl ℚ g₁ g₂ = 0 := by
  rw [LinearMap.comp_assoc, vo_prodSnd_comp_prodInl, LinearMap.comp_zero]

theorem vo_comp_prodSnd_prodInr (x : Module.Dual ℚ (H1 ℚ g₂)) :
    (x ∘ₗ prodSnd ℚ g₁ g₂) ∘ₗ prodInr ℚ g₁ g₂ = x := by
  rw [LinearMap.comp_assoc, vo_prodSnd_comp_prodInr, LinearMap.comp_id]

theorem vo_comp_prodFst_prodEnd (x : Module.Dual ℚ (H1 ℚ g₁)) (φ₁ : Module.End ℚ (H1 ℚ g₁))
    (φ₂ : Module.End ℚ (H1 ℚ g₂)) :
    (x ∘ₗ prodFst ℚ g₁ g₂) ∘ₗ vo_prodEnd φ₁ φ₂ = (x ∘ₗ φ₁) ∘ₗ prodFst ℚ g₁ g₂ :=
  LinearMap.ext fun v => by simp

theorem vo_comp_prodSnd_prodEnd (x : Module.Dual ℚ (H1 ℚ g₂)) (φ₁ : Module.End ℚ (H1 ℚ g₁))
    (φ₂ : Module.End ℚ (H1 ℚ g₂)) :
    (x ∘ₗ prodSnd ℚ g₁ g₂) ∘ₗ vo_prodEnd φ₁ φ₂ = (x ∘ₗ φ₂) ∘ₗ prodSnd ℚ g₁ g₂ :=
  LinearMap.ext fun v => by simp

/-- The Hermitian form of `A₁ × A₂` restricted to the factors. -/
theorem vo_herm_prod (h₁ : S ℚ g₁) (h₂ : S ℚ g₂) (φ₁ : Module.End ℚ (H1 ℚ g₁))
    (φ₂ : Module.End ℚ (H1 ℚ g₂)) (p q : Module.Dual ℚ (H1 ℚ g₁) ⊕ Module.Dual ℚ (H1 ℚ g₂)) :
    vo_herm d (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) h₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) h₂)
        (vo_prodEnd φ₁ φ₂) (Sum.elim (· ∘ₗ prodFst ℚ g₁ g₂) (· ∘ₗ prodSnd ℚ g₁ g₂) p)
        (Sum.elim (· ∘ₗ prodFst ℚ g₁ g₂) (· ∘ₗ prodSnd ℚ g₁ g₂) q) =
      match p, q with
      | Sum.inl x, Sum.inl y => vo_herm d h₁ φ₁ x y
      | Sum.inr x, Sum.inr y => vo_herm d h₂ φ₂ x y
      | _, _ => 0 := by
  rcases p with x | x <;> rcases q with y | y <;>
    simp only [vo_herm, Sum.elim_inl, Sum.elim_inr, vo_comp_prodFst_prodEnd,
      vo_comp_prodSnd_prodEnd, vo_eval2_prod, vo_comp_prodFst_prodInl, vo_comp_prodFst_prodInr,
      vo_comp_prodSnd_prodInl, vo_comp_prodSnd_prodInr, vo_eval2_zero_left, vo_eval2_zero_right,
      add_zero, zero_add, Rat.cast_zero, mul_zero]

/-- The `K`-basis of `H₁(A₁ × A₂)` made of `K`-bases of the factors. -/
noncomputable def vo_prodBasis {n₁ n₂ : ℕ} (b₁ : Fin n₁ → Module.Dual ℚ (H1 ℚ g₁))
    (b₂ : Fin n₂ → Module.Dual ℚ (H1 ℚ g₂)) (k : Fin (n₁ + n₂)) :
    Module.Dual ℚ (H1 ℚ (g₁ + g₂)) :=
  Sum.elim (· ∘ₗ prodFst ℚ g₁ g₂) (· ∘ₗ prodSnd ℚ g₁ g₂) (Sum.map b₁ b₂ (finSumFinEquiv.symm k))

/-- **The Gram matrix of `H` on `A₁ × A₂` is block diagonal**, so its determinant is the product of
those of the factors. -/
theorem vo_det_gram_prod {n₁ n₂ : ℕ} (h₁ : S ℚ g₁) (h₂ : S ℚ g₂) (φ₁ : Module.End ℚ (H1 ℚ g₁))
    (φ₂ : Module.End ℚ (H1 ℚ g₂)) (b₁ : Fin n₁ → Module.Dual ℚ (H1 ℚ g₁))
    (b₂ : Fin n₂ → Module.Dual ℚ (H1 ℚ g₂)) :
    (Matrix.of fun k l => vo_herm d (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) h₁ +
        ExteriorAlgebra.map (prodInr ℚ g₁ g₂) h₂) (vo_prodEnd φ₁ φ₂) (vo_prodBasis b₁ b₂ k)
        (vo_prodBasis b₁ b₂ l)).det =
      (Matrix.of fun i j => vo_herm d h₁ φ₁ (b₁ i) (b₁ j)).det *
        (Matrix.of fun i j => vo_herm d h₂ φ₂ (b₂ i) (b₂ j)).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin n₁) (Fin n₂) ℂ),
    ← Matrix.det_submatrix_equiv_self (finSumFinEquiv.symm : Fin (n₁ + n₂) ≃ Fin n₁ ⊕ Fin n₂)]
  congr 1
  ext k l
  simp only [Matrix.submatrix_apply, Matrix.of_apply, vo_prodBasis]
  rcases finSumFinEquiv.symm k with i | i <;> rcases finSumFinEquiv.symm l with j | j <;>
    simp only [Sum.map_inl, Sum.map_inr, vo_herm_prod, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply, Matrix.zero_apply]

theorem vo_linIndep_sum_fst_snd {ι₁ ι₂ : Type*} {u : ι₁ → Module.Dual ℚ (H1 ℚ g₁)}
    {v : ι₂ → Module.Dual ℚ (H1 ℚ g₂)} (hu : LinearIndependent ℚ u)
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℚ (Sum.elim (fun i => u i ∘ₗ prodFst ℚ g₁ g₂)
      (fun j => v j ∘ₗ prodSnd ℚ g₁ g₂)) := by
  let P₁ : Module.Dual ℚ (H1 ℚ g₁) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ (g₁ + g₂)) :=
    LinearMap.lcomp ℚ ℚ (prodFst ℚ g₁ g₂)
  let P₂ : Module.Dual ℚ (H1 ℚ g₂) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ (g₁ + g₂)) :=
    LinearMap.lcomp ℚ ℚ (prodSnd ℚ g₁ g₂)
  have hP₁ : ∀ x, P₁ x = x ∘ₗ prodFst ℚ g₁ g₂ := fun x => rfl
  have hP₂ : ∀ x, P₂ x = x ∘ₗ prodSnd ℚ g₁ g₂ := fun x => rfl
  have hinj₁ : LinearMap.ker P₁ = ⊥ := LinearMap.ker_eq_bot.mpr fun x y h => by
    rw [hP₁, hP₁] at h
    have := congrArg (fun z => z ∘ₗ prodInl ℚ g₁ g₂) h
    simpa only [vo_comp_prodFst_prodInl] using this
  have hinj₂ : LinearMap.ker P₂ = ⊥ := LinearMap.ker_eq_bot.mpr fun x y h => by
    rw [hP₂, hP₂] at h
    have := congrArg (fun z => z ∘ₗ prodInr ℚ g₁ g₂) h
    simpa only [vo_comp_prodSnd_prodInr] using this
  have hfam : Sum.elim (fun i => u i ∘ₗ prodFst ℚ g₁ g₂) (fun j => v j ∘ₗ prodSnd ℚ g₁ g₂) =
      Sum.elim (⇑P₁ ∘ u) (⇑P₂ ∘ v) := rfl
  rw [hfam]
  refine LinearIndependent.sum_type (hu.map' P₁ hinj₁) (hv.map' P₂ hinj₂) ?_
  rw [Submodule.disjoint_def]
  intro z hz₁ hz₂
  let R₁ : Module.Dual ℚ (H1 ℚ (g₁ + g₂)) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ g₂) :=
    LinearMap.lcomp ℚ ℚ (prodInr ℚ g₁ g₂)
  let R₂ : Module.Dual ℚ (H1 ℚ (g₁ + g₂)) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ g₁) :=
    LinearMap.lcomp ℚ ℚ (prodInl ℚ g₁ g₂)
  have k₁ : Submodule.span ℚ (Set.range (⇑P₁ ∘ u)) ≤ LinearMap.ker R₁ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (u i ∘ₗ prodFst ℚ g₁ g₂) ∘ₗ prodInr ℚ g₁ g₂ = 0
    exact vo_comp_prodFst_prodInr _
  have k₂ : Submodule.span ℚ (Set.range (⇑P₂ ∘ v)) ≤ LinearMap.ker R₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (v i ∘ₗ prodSnd ℚ g₁ g₂) ∘ₗ prodInl ℚ g₁ g₂ = 0
    exact vo_comp_prodSnd_prodInl _
  have e₁ : z ∘ₗ prodInr ℚ g₁ g₂ = 0 := k₁ hz₁
  have e₂ : z ∘ₗ prodInl ℚ g₁ g₂ = 0 := k₂ hz₂
  exact vo_dual_eq_zero e₂ e₁

/-- The family `bᵢ, η(√-d)ᵀ bᵢ` of the product `K`-basis is linearly independent. -/
theorem vo_linIndep_prodBasis {n₁ n₂ : ℕ} (φ₁ : Module.End ℚ (H1 ℚ g₁))
    (φ₂ : Module.End ℚ (H1 ℚ g₂)) (b₁ : Fin n₁ → Module.Dual ℚ (H1 ℚ g₁))
    (b₂ : Fin n₂ → Module.Dual ℚ (H1 ℚ g₂))
    (h₁ : LinearIndependent ℚ (Sum.elim b₁ (fun i => b₁ i ∘ₗ φ₁)))
    (h₂ : LinearIndependent ℚ (Sum.elim b₂ (fun i => b₂ i ∘ₗ φ₂))) :
    LinearIndependent ℚ (Sum.elim (vo_prodBasis b₁ b₂)
      (fun k => vo_prodBasis b₁ b₂ k ∘ₗ vo_prodEnd φ₁ φ₂)) := by
  have hU := vo_linIndep_sum_fst_snd (g₁ := g₁) (g₂ := g₂) h₁ h₂
  let σ : Fin (n₁ + n₂) ⊕ Fin (n₁ + n₂) ≃ (Fin n₁ ⊕ Fin n₁) ⊕ (Fin n₂ ⊕ Fin n₂) :=
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans (Equiv.sumSumSumComm _ _ _ _)
  rw [← linearIndependent_equiv σ] at hU
  convert hU using 1
  funext x
  rcases x with k | k <;> simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, σ,
    Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, vo_prodBasis] <;>
    rcases finSumFinEquiv.symm k with i | i <;>
    simp [Equiv.sumSumSumComm, vo_comp_prodFst_prodEnd, vo_comp_prodSnd_prodEnd]

end ProductWeil

/-! ### The sign of the determinant of a Hermitian matrix -/

section MatrixSign

open Matrix
open scoped ComplexOrder

theorem vo_entry {m n o : Type*} [Fintype m] (G : Matrix m m ℂ) (A : Matrix m n ℂ)
    (B : Matrix m o ℂ) (i : n) (j : o) :
    (Aᴴ * G * B) i j = star (fun r => A r i) ⬝ᵥ G *ᵥ (fun r => B r j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem vo_quad_conj {m n : Type*} [Fintype m] [Fintype n] (G : Matrix m m ℂ) (B : Matrix m n ℂ)
    (x : n → ℂ) : star x ⬝ᵥ (Bᴴ * G * B) *ᵥ x = star (B *ᵥ x) ⬝ᵥ G *ᵥ (B *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-- A positive complex number is a positive real number. -/
theorem vo_pos_of_re_im {z : ℂ} (hre : 0 < z.re) (him : z.im = 0) : 0 < z :=
  Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

/-- **Sylvester's law of inertia, in the form used**: if `ℂⁿ = P ⊕ N` with the Hermitian form of `G`
positive definite on `P`, negative definite on `N`, and `P ⊥ N`, then `(-1)^{dim N} det G > 0`. -/
theorem vo_det_sign {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.IsHermitian)
    (P N : Submodule ℂ (Fin n → ℂ)) (hPN : IsCompl P N)
    (hP : ∀ z ∈ P, z ≠ 0 → 0 < (star z ⬝ᵥ G *ᵥ z).re)
    (hN : ∀ z ∈ N, z ≠ 0 → (star z ⬝ᵥ G *ᵥ z).re < 0)
    (horth : ∀ z ∈ P, ∀ w ∈ N, star z ⬝ᵥ G *ᵥ w = 0)
    (horth' : ∀ z ∈ N, ∀ w ∈ P, star z ⬝ᵥ G *ᵥ w = 0) :
    0 < (-1 : ℝ) ^ Module.finrank ℂ N * G.det.re ∧ G.det.im = 0 := by
  set p := Module.finrank ℂ P
  set q := Module.finrank ℂ N
  let bP := Module.finBasis ℂ P
  let bN := Module.finBasis ℂ N
  let SP : Matrix (Fin n) (Fin p) ℂ := Matrix.of fun r i => (bP i : Fin n → ℂ) r
  let SN : Matrix (Fin n) (Fin q) ℂ := Matrix.of fun r j => (bN j : Fin n → ℂ) r
  -- `SP x = Σ xᵢ bPᵢ ∈ P`, nonzero for `x ≠ 0`
  have hSP : ∀ x : Fin p → ℂ, SP *ᵥ x = ((∑ i, x i • bP i : P) : Fin n → ℂ) := by
    intro x; funext r
    simp [SP, Matrix.mulVec, dotProduct, mul_comm]
  have hSN : ∀ x : Fin q → ℂ, SN *ᵥ x = ((∑ i, x i • bN i : N) : Fin n → ℂ) := by
    intro x; funext r
    simp [SN, Matrix.mulVec, dotProduct, mul_comm]
  have hne : ∀ {k : ℕ} {U : Submodule ℂ (Fin n → ℂ)} (b : Module.Basis (Fin k) ℂ U)
      (x : Fin k → ℂ), x ≠ 0 → ((∑ i, x i • b i : U) : Fin n → ℂ) ≠ 0 := by
    intro k U b x hx h0
    apply hx
    have h1 : (∑ i, x i • b i : U) = 0 := Subtype.ext h0
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent x h1 i
  -- the diagonal blocks are definite
  have hMP : (SPᴴ * G * SP).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_conjTranspose_mul_mul SP hG)
      fun x hx => ?_
    rw [vo_quad_conj, hSP]
    refine vo_pos_of_re_im (hP _ (Submodule.coe_mem _) (hne bP x hx)) ?_
    exact hG.im_star_dotProduct_mulVec_self ((∑ i, x i • bP i : P) : Fin n → ℂ)
  have hMN : (SNᴴ * (-G) * SN).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_conjTranspose_mul_mul SN hG.neg) fun x hx => ?_
    rw [vo_quad_conj, hSN, Matrix.neg_mulVec, dotProduct_neg]
    refine vo_pos_of_re_im ?_ ?_
    · rw [Complex.neg_re]
      exact neg_pos.mpr (hN _ (Submodule.coe_mem _) (hne bN x hx))
    · rw [Complex.neg_im, neg_eq_zero]
      exact hG.im_star_dotProduct_mulVec_self ((∑ i, x i • bN i : N) : Fin n → ℂ)
  -- the square matrix of the basis `bP ∪ bN`
  have hcard : p + q = n := by
    have := Submodule.finrank_add_eq_of_isCompl hPN
    simpa using this
  let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hcard)
  let S : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ := Matrix.fromCols SP SN
  let T : Matrix (Fin n) (Fin n) ℂ := S.submatrix id e.symm
  have hblock : Sᴴ * G * S = Matrix.fromBlocks (SPᴴ * G * SP) 0 0 (SNᴴ * G * SN) := by
    rw [Matrix.mul_assoc, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    · ext i j
      rw [vo_entry, Matrix.zero_apply]
      exact horth _ (bP i).2 _ (bN j).2
    · ext i j
      rw [vo_entry, Matrix.zero_apply]
      exact horth' _ (bN i).2 _ (bP j).2
  have hT : Tᴴ * G * T = (Sᴴ * G * S).submatrix e.symm e.symm := by
    ext i j
    rw [Matrix.submatrix_apply, vo_entry, vo_entry]
    rfl
  have hdetT : T.det ≠ 0 := by
    have hli : LinearIndependent ℂ T.col := by
      have hc : LinearIndependent ℂ (Sum.elim (fun i => (bP i : Fin n → ℂ))
          (fun j => (bN j : Fin n → ℂ))) := by
        refine LinearIndependent.sum_type (bP.linearIndependent.map' P.subtype P.ker_subtype)
          (bN.linearIndependent.map' N.subtype N.ker_subtype) ?_
        refine hPN.disjoint.mono ?_ ?_
        · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (bP i).2
        · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (bN i).2
      have : T.col = Sum.elim (fun i => (bP i : Fin n → ℂ)) (fun j => (bN j : Fin n → ℂ)) ∘
          e.symm := by
        funext k r
        simp only [T, S, Matrix.col_apply, Matrix.submatrix_apply, id, Function.comp_apply]
        rcases e.symm k with i | j <;> simp [SP, SN]
      rw [this]
      exact hc.comp _ e.symm.injective
    exact (Matrix.isUnit_iff_isUnit_det T).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hli) |>.ne_zero
  -- determinants
  have hdet : star T.det * G.det * T.det =
      (SPᴴ * G * SP).det * ((-1) ^ q * (SNᴴ * (-G) * SN).det) := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.det_mul, hT,
      Matrix.det_submatrix_equiv_self, hblock, Matrix.det_fromBlocks_zero₂₁]
    congr 1
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.det_neg, Fintype.card_fin, ← mul_assoc,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have ha := hMP.det_pos
  have hb := hMN.det_pos
  rw [Complex.lt_def] at ha hb
  set a := (SPᴴ * G * SP).det
  set b := (SNᴴ * (-G) * SN).det
  have hc : 0 < Complex.normSq T.det := Complex.normSq_pos.mpr hdetT
  have hstar : star T.det * G.det * T.det = (Complex.normSq T.det : ℂ) * G.det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [hstar] at hdet
  -- `(-1)^q det G = a b / |det T|²`
  have hkey : ((-1 : ℂ) ^ q * G.det) * (Complex.normSq T.det : ℂ) = a * b := by
    have h1 : ((-1 : ℂ) ^ q) * ((-1 : ℂ) ^ q) = 1 := by rw [← mul_pow]; norm_num
    calc ((-1 : ℂ) ^ q * G.det) * (Complex.normSq T.det : ℂ)
        = (-1 : ℂ) ^ q * ((Complex.normSq T.det : ℂ) * G.det) := by ring
      _ = (-1 : ℂ) ^ q * (a * ((-1) ^ q * b)) := by rw [hdet]
      _ = ((-1 : ℂ) ^ q * (-1 : ℂ) ^ q) * (a * b) := by ring
      _ = a * b := by rw [h1, one_mul]
  have hre := congrArg Complex.re hkey
  have him := congrArg Complex.im hkey
  have hsgn : ((-1 : ℂ) ^ q) = (((-1 : ℝ) ^ q : ℝ) : ℂ) := by push_cast; rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, add_zero, hsgn, zero_mul] at hre him
  simp only [Complex.zero_re, Complex.zero_im] at ha hb
  rw [← ha.2, ← hb.2] at hre him
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hre him
  constructor
  · have h1 : 0 < (-1 : ℝ) ^ q * G.det.re * Complex.normSq T.det := by
      have : 0 < a.re * b.re := mul_pos ha.1 hb.1
      linarith
    exact (mul_pos_iff_of_pos_right hc).mp h1
  · have hq : ((-1 : ℝ) ^ q) ≠ 0 := pow_ne_zero _ (by norm_num)
    have : (-1 : ℝ) ^ q * G.det.im * Complex.normSq T.det = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact (mul_eq_zero.mp h).resolve_left hq
    · exact absurd h hc.ne'

end MatrixSign

/-! ### The Hermitian form of a polarized abelian variety of Weil type, over `ℂ`

For a polarized abelian `2m`-fold of Weil type `(A, η, h)` and a `K`-basis `b` of `H₁(A, ℚ)`, the
Gram matrix `G = (H(bᵢ, bⱼ))` of van Geemen's form satisfies `z^* G w = E(conj Φz, p w)` on `ℂ^{2m}`,
where `Φ z = Σ zᵢ bᵢ ∈ H₁(A, ℂ)`, `p = (f + √-d) Φ` (`f = η(√-d)ᵀ`) maps `ℂ^{2m}` onto the
`√-d`-eigenspace `W*` of `f`, and `E` is the polarization. `W*` is the sum of its intersections
with the eigenspaces of `Jᵀ` (eigenvalues `±i`); `H` is definite on each (of opposite signs, by
ampleness), they are orthogonal (`h` is of type `(1,1)`), and the second one is carried by the
contraction `θ` with `h` onto `W̄ ∩ H^{1,0}`, of dimension `m` (the Weil condition). Hence
`(-1)^m det G > 0` (`vo_herm_det_sign`). -/

section HermC

variable {d : ℚ} {m : ℕ} {A : AbVar (2 * m)}

/-- `f = η(√-d)` on `H¹(A, ℂ)`. -/
noncomputable def vo_fC (X : PolarizedWeilType A d) : Module.End ℂ (H1 ℂ (2 * m)) :=
  bcMap ℚ ℂ (X.η (Kd.sqrtNeg d))

/-- The polarization `h ∈ H²(A, ℂ)`. -/
noncomputable def vo_hC (X : PolarizedWeilType A d) : S ℂ (2 * m) := bcS ℚ ℂ (2 * m) X.h

theorem vo_bcMap_neg {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {g g' : ℕ}
    (φ : H1 F g →ₗ[F] H1 F g') : bcMap F F' (-φ) = -bcMap F F' φ := by
  rw [show -φ = (-1 : F) • φ by simp, main_bcMap_smul]
  simp

theorem vo_bcMap_bcMap {g g' : ℕ} (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g') :
    bcMap ℝ ℂ (bcMap ℚ ℝ φ) = bcMap ℚ ℂ φ := by
  simp only [bcMap, LinearMap.toMatrix'_toLin', Matrix.map_map]
  congr 2

theorem vo_fC_sq (hd : 0 < d) (X : PolarizedWeilType A d) :
    vo_fC X * vo_fC X = -((d : ℂ) • 1) := by
  rw [vo_fC, Module.End.mul_eq_comp, ← main_bcMap_comp, ← Module.End.mul_eq_comp, vo_eta_sq hd,
    vo_bcMap_neg, main_bcMap_smul]
  have : bcMap ℚ ℂ (1 : Module.End ℚ (H1 ℚ (2 * m))) = 1 := main_bcMap_id
  rw [this, eq_ratCast]

theorem vo_map_fC_hC (hd : 0 < d) (X : PolarizedWeilType A d) :
    ExteriorAlgebra.map (vo_fC X) (vo_hC X) = (d : ℂ) • vo_hC X := by
  rw [vo_fC, vo_hC, ← main_bcS_map, X.norm, vo_Nm_sqrtNeg hd, map_smul, ← algebraMap_smul ℂ d,
    eq_ratCast]

theorem vo_hC_mem_pq (X : PolarizedWeilType A d) :
    vo_hC X ∈ pqPiece (H10 (2 * m) A.J) (H01 (2 * m) A.J) 1 1 :=
  ((mem_hodgeClassesX_iff (2 * m) A.J 1 X.h).mp X.ample.1).2

theorem vo_map_JC_hC (X : PolarizedWeilType A d) :
    ExteriorAlgebra.map (complexifyH1 (2 * m) A.J) (vo_hC X) = vo_hC X :=
  main_lef_map_pqPiece_pp (2 * m) A.J 1 (vo_hC_mem_pq X)

theorem vo_hC_mem_two (X : PolarizedWeilType A d) : vo_hC X ∈ ⋀[ℂ]^2 (H1 ℂ (2 * m)) :=
  main_lef_bcS_mem ℚ ℂ (2 * m) X.ample.mem_exteriorPower_two

theorem vo_fC_eq (X : PolarizedWeilType A d) :
    vo_fC X = complexifyH1 (2 * m) (bcMap ℚ ℝ (X.η (Kd.sqrtNeg d))) := by
  rw [vo_fC, main_lef_complexifyH1_eq, vo_bcMap_bcMap]

theorem vo_fC_JC (X : PolarizedWeilType A d) :
    vo_fC X ∘ₗ complexifyH1 (2 * m) A.J = complexifyH1 (2 * m) A.J ∘ₗ vo_fC X := by
  rw [vo_fC_eq, main_lef_complexifyH1_eq, main_lef_complexifyH1_eq, ← main_bcMap_comp,
    ← main_bcMap_comp, X.isHodge]

theorem vo_JC_sq (A : AbVar (2 * m)) (u : Module.Dual ℂ (H1 ℂ (2 * m))) :
    (u ∘ₗ complexifyH1 (2 * m) A.J) ∘ₗ complexifyH1 (2 * m) A.J = -u := by
  ext v
  simp only [LinearMap.comp_apply, s24b_complexifyH1_sq (2 * m) A.J A.isComplex, map_neg,
    LinearMap.neg_apply]

theorem vo_fC_sq_apply (hd : 0 < d) (X : PolarizedWeilType A d) (u : Module.Dual ℂ (H1 ℂ (2 * m))) :
    (u ∘ₗ vo_fC X) ∘ₗ vo_fC X = -((d : ℂ) • u) := by
  rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, vo_fC_sq hd]
  ext v
  simp

/-- `E(u ∘ f, v ∘ f) = d E(u, v)`. -/
theorem vo_EC_fC (hd : 0 < d) (X : PolarizedWeilType A d) (u v : Module.Dual ℂ (H1 ℂ (2 * m))) :
    eval2 ℂ (2 * m) (vo_hC X) (u ∘ₗ vo_fC X) (v ∘ₗ vo_fC X) =
      d * eval2 ℂ (2 * m) (vo_hC X) u v := by
  rw [← vo_eval2_map, vo_map_fC_hC hd, vo_eval2_smul]

/-- `E(u ∘ J, v ∘ J) = E(u, v)` (`h` is of type `(1,1)`). -/
theorem vo_EC_JC (X : PolarizedWeilType A d) (u v : Module.Dual ℂ (H1 ℂ (2 * m))) :
    eval2 ℂ (2 * m) (vo_hC X) (u ∘ₗ complexifyH1 (2 * m) A.J) (v ∘ₗ complexifyH1 (2 * m) A.J) =
      eval2 ℂ (2 * m) (vo_hC X) u v := by
  rw [← vo_eval2_map, vo_map_JC_hC]

/-- `E` vanishes on the `√-d`-eigenspace of `f`. -/
theorem vo_EC_W (hd : 0 < d) (X : PolarizedWeilType A d) {u v : Module.Dual ℂ (H1 ℂ (2 * m))}
    (hu : u ∘ₗ vo_fC X = sqrtNeg d • u) (hv : v ∘ₗ vo_fC X = sqrtNeg d • v) :
    eval2 ℂ (2 * m) (vo_hC X) u v = 0 := by
  have h := vo_EC_fC hd X u v
  rw [hu, hv, vo_eval2_smul_left, main_eval2_smul_right, ← mul_assoc,
    vo_sqrtNeg_mul_self hd] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (2 * (d : ℂ)) * eval2 ℂ (2 * m) (vo_hC X) u v = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (mul_ne_zero two_ne_zero hd')
  · exact h0

/-- `E` vanishes on an eigenspace of `J` (eigenvalue `μ = ±i`). -/
theorem vo_EC_T (X : PolarizedWeilType A d) {u v : Module.Dual ℂ (H1 ℂ (2 * m))} {μ : ℂ}
    (hμ : μ * μ = -1) (hu : u ∘ₗ complexifyH1 (2 * m) A.J = μ • u)
    (hv : v ∘ₗ complexifyH1 (2 * m) A.J = μ • v) : eval2 ℂ (2 * m) (vo_hC X) u v = 0 := by
  have h := vo_EC_JC X u v
  rw [hu, hv, vo_eval2_smul_left, main_eval2_smul_right, ← mul_assoc, hμ] at h
  linear_combination -h / 2

end HermC

section HermC2

variable {d : ℚ} {m : ℕ} {A : AbVar (2 * m)}

theorem vo_conj_fC (X : PolarizedWeilType A d) (u : Module.Dual ℂ (H1 ℂ (2 * m))) :
    s24b_conjDual (2 * m) (u ∘ₗ vo_fC X) = s24b_conjDual (2 * m) u ∘ₗ vo_fC X := by
  rw [vo_fC_eq, s24b_conjDual_comp]

theorem vo_conj_bcDual {n : ℕ} (y : Module.Dual ℚ (H1 ℚ n)) :
    s24b_conjDual n (bcDual ℚ ℂ n y) = bcDual ℚ ℂ n y := by
  apply s24b_dual_ext
  intro i
  rw [s24b_conjDual_e, s24b_bcDual_e, eq_ratCast, map_ratCast]

/-- Complex conjugation on `H₁(A, ℂ)`, as an additive map. -/
noncomputable def vo_conjAdd (n : ℕ) : Module.Dual ℂ (H1 ℂ n) →+ Module.Dual ℂ (H1 ℂ n) where
  toFun := s24b_conjDual n
  map_zero' := by
    apply s24b_dual_ext; intro i; simp [s24b_conjDual_e]
  map_add' := s24b_conjDual_add n

/-- `E(u, v) = ⟪h, u ∧ v⟫` as a bilinear form. -/
noncomputable def vo_E2 {F : Type*} [Field F] [CharZero F] (n : ℕ) (ξ : S F n) :
    Module.Dual F (H1 F n) →ₗ[F] Module.Dual F (H1 F n) →ₗ[F] F :=
  LinearMap.mk₂ F (eval2 F n ξ) (vo_eval2_add_left ξ) (fun c a b => vo_eval2_smul_left ξ c a b)
    (vo_eval2_add_right ξ) (fun c a b => main_eval2_smul_right F n ξ a b c)

theorem vo_E2_apply {F : Type*} [Field F] [CharZero F] (n : ℕ) (ξ : S F n)
    (a b : Module.Dual F (H1 F n)) : vo_E2 n ξ a b = eval2 F n ξ a b := rfl

theorem vo_eval2_self {F : Type*} [Field F] [CharZero F] {n : ℕ} (ξ : S F n)
    (a : Module.Dual F (H1 F n)) : eval2 F n ξ a a = 0 := by
  have h := s24b_eval2_swap F n ξ a a
  have : (2 : F) * eval2 F n ξ a a = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- Real and imaginary parts of functionals are unique. -/
theorem vo_reim_inj {n : ℕ} {a b a' b' : Module.Dual ℝ (H1 ℝ n)}
    (h : bcDual ℝ ℂ n a + Complex.I • bcDual ℝ ℂ n b =
      bcDual ℝ ℂ n a' + Complex.I • bcDual ℝ ℂ n b') : a = a' ∧ b = b' := by
  have hk : ∀ k, (a (e ℝ n k) : ℂ) + Complex.I * b (e ℝ n k) =
      a' (e ℝ n k) + Complex.I * b' (e ℝ n k) := by
    intro k
    have := LinearMap.congr_fun h (e ℂ n k)
    simpa [s24b_bcDual_e] using this
  constructor
  · refine s24b_dual_ext ℝ n fun k => ?_
    have := congrArg Complex.re (hk k)
    simpa using this
  · refine s24b_dual_ext ℝ n fun k => ?_
    have := congrArg Complex.im (hk k)
    simpa using this

/-- **Positivity** (ampleness): on the `±i`-eigenspaces of `J` in `H₁(A, ℂ)`,
`E(ū, u) = -2 ε P` with `P > 0` for `u ≠ 0` (`ε = ±i` the eigenvalue). -/
theorem vo_EC_conj_self (X : PolarizedWeilType A d) {u : Module.Dual ℂ (H1 ℂ (2 * m))} {ε : ℂ}
    (hε : ε = Complex.I ∨ ε = -Complex.I) (hu : u ∘ₗ complexifyH1 (2 * m) A.J = ε • u)
    (hu0 : u ≠ 0) : ∃ P : ℝ, 0 < P ∧
      eval2 ℂ (2 * m) (vo_hC X) (s24b_conjDual (2 * m) u) u = -2 * ε * P := by
  obtain ⟨x, y, hxy, hcxy⟩ := s24b_re_im (2 * m) u
  have hT : u ∘ₗ complexifyH1 (2 * m) A.J =
      bcDual ℝ ℂ (2 * m) (x ∘ₗ A.J) + Complex.I • bcDual ℝ ℂ (2 * m) (y ∘ₗ A.J) := by
    rw [hxy, LinearMap.add_comp, LinearMap.smul_comp, s24b_bcDual_comp, s24b_bcDual_comp]
  have hE : eval2 ℂ (2 * m) (vo_hC X) (s24b_conjDual (2 * m) u) u =
      2 * Complex.I * (eval2 ℝ (2 * m) (bcS ℚ ℝ (2 * m) X.h) x y : ℂ) := by
    rw [hcxy, hxy, sub_eq_add_neg, ← neg_smul, vo_eval2_add_left, vo_eval2_add_right,
      vo_eval2_add_right, vo_eval2_smul_left, vo_eval2_smul_left, main_eval2_smul_right,
      main_eval2_smul_right, vo_eval2_self, vo_eval2_self,
      s24b_eval2_swap ℂ (2 * m) _ (bcDual ℝ ℂ (2 * m) y), vo_hC, ← s24b_bcS_bcS (2 * m) ℚ ℝ ℂ,
      s24b_eval2_bcS]
    simp only [Complex.coe_algebraMap]
    ring
  -- `y = σ (x ∘ J)`, `σ = -1` for `ε = i` and `σ = 1` for `ε = -i`
  obtain ⟨σ, hσ, hy⟩ : ∃ σ : ℝ, (σ : ℂ) = ε * Complex.I ∧ y = σ • (x ∘ₗ A.J) := by
    rcases hε with rfl | rfl
    · refine ⟨-1, by simp, ?_⟩
      rw [hT, hxy] at hu
      have h := (vo_reim_inj (a := x ∘ₗ A.J) (b := y ∘ₗ A.J) (a' := -y) (b' := x) (by
        rw [hu]; simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
        abel)).1
      rw [h]; simp
    · refine ⟨1, by simp, ?_⟩
      rw [hT, hxy] at hu
      have h := (vo_reim_inj (a := x ∘ₗ A.J) (b := y ∘ₗ A.J) (a' := y) (b' := -x) (by
        rw [hu]; simp only [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
          map_neg, smul_neg, neg_smul]
        abel)).1
      rw [h]; simp
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hu0
    rw [hxy, hy]
    simp
  refine ⟨eval2 ℝ (2 * m) (bcS ℚ ℝ (2 * m) X.h) x (x ∘ₗ A.J), X.ample.2 x hx0, ?_⟩
  rw [hE, hy, main_eval2_smul_right]
  push_cast
  rw [hσ]
  linear_combination (2 * ε * (eval2 ℝ (2 * m) (bcS ℚ ℝ (2 * m) X.h) x (x ∘ₗ A.J) : ℂ)) *
    Complex.I_sq

/-- Naturality of the contraction: `θ_{φ^*ξ}(a) = φ(θ_ξ(a ∘ φ))`. -/
theorem vo_contractOne_map {F : Type*} [Field F] [CharZero F] {n n' : ℕ}
    (φ : H1 F n →ₗ[F] H1 F n') {ξ : S F n} (hξ : ξ ∈ ⋀[F]^2 (H1 F n))
    (a : Module.Dual F (H1 F n')) :
    contractOne F n' (ExteriorAlgebra.map φ ξ) a = φ (contractOne F n ξ (a ∘ₗ φ)) := by
  apply (ExteriorAlgebra.ι_inj F _ _).mp
  rw [ι_contractOne F n' _ (main_map_mem_exteriorPower φ 2 hξ), ← ExteriorAlgebra.map_apply_ι,
    ι_contractOne F n _ hξ]
  simp only [D]
  exact main_contractLeft_map φ a ξ

/-- `θ(u ∘ f) = -f(θ u)`, for `θ` the contraction with `h`. -/
theorem vo_theta_fC (hd : 0 < d) (X : PolarizedWeilType A d) (u : Module.Dual ℂ (H1 ℂ (2 * m))) :
    contractOne ℂ (2 * m) (vo_hC X) (u ∘ₗ vo_fC X) =
      -vo_fC X (contractOne ℂ (2 * m) (vo_hC X) u) := by
  have h1 := vo_contractOne_map (vo_fC X) (vo_hC_mem_two X) u
  rw [vo_map_fC_hC hd, s24b_contractOne_smul, LinearMap.smul_apply] at h1
  have h2 := congrArg (vo_fC X) h1
  rw [map_smul, ← Module.End.mul_apply, vo_fC_sq hd] at h2
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply] at h2
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h3 : (d : ℂ) • (contractOne ℂ (2 * m) (vo_hC X) (u ∘ₗ vo_fC X) +
      vo_fC X (contractOne ℂ (2 * m) (vo_hC X) u)) = 0 := by
    rw [smul_add, h2]; abel
  rw [smul_eq_zero] at h3
  exact eq_neg_of_add_eq_zero_left (h3.resolve_left hd')

/-- `θ(u ∘ J) = -J(θ u)`. -/
theorem vo_theta_JC (X : PolarizedWeilType A d) (u : Module.Dual ℂ (H1 ℂ (2 * m))) :
    contractOne ℂ (2 * m) (vo_hC X) (u ∘ₗ complexifyH1 (2 * m) A.J) =
      -complexifyH1 (2 * m) A.J (contractOne ℂ (2 * m) (vo_hC X) u) := by
  have h := s24b_contractOne_hodge (2 * m) A.J _ (vo_hC_mem_pq X) u
  rw [map_neg] at h
  rw [← h, neg_neg]

/-- The contraction with an ample class is bijective over `ℂ`. -/
theorem vo_theta_bijective (X : PolarizedWeilType A d) :
    Function.Bijective (contractOne ℂ (2 * m) (vo_hC X)) := by
  have hsurj : Function.Surjective (contractOne ℂ (2 * m) (vo_hC X)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun ℂ (Fin (2 * (2 * m)))).span_eq,
      Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨y, hy⟩ := (IsAmple.bijective_thetaMap X.ample).2 (e ℚ (2 * m) k)
    refine ⟨bcDual ℚ ℂ (2 * m) y, ?_⟩
    rw [vo_hC, s24b_contractOne_bcS]
    rw [show thetaMap (2 * m) X.h y = contractOne ℚ (2 * m) X.h y from rfl] at hy
    rw [hy, main_bcH1_e]
    simp [e]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mpr hsurj, hsurj⟩

end HermC2

section HermSign

open Matrix

variable {d : ℚ} {m : ℕ} {A : AbVar (2 * m)}

theorem vo_bcDual_comp_bcMap {n : ℕ} (y : Module.Dual ℚ (H1 ℚ n)) (φ : Module.End ℚ (H1 ℚ n)) :
    bcDual ℚ ℂ n (y ∘ₗ φ) = bcDual ℚ ℂ n y ∘ₗ bcMap ℚ ℂ φ := by
  apply s24b_dual_ext
  intro i
  rw [LinearMap.comp_apply, ← s24b_bcH1_e ℚ ℂ n i, main_bcMap_bcH1, s24b_bcDual_bcH1,
    s24b_bcDual_bcH1, LinearMap.comp_apply]

/-- Rational linearly independent functionals stay linearly independent over `ℂ`. -/
theorem vo_linIndep_bcDual {ι : Type*} {n : ℕ} {v : ι → Module.Dual ℚ (H1 ℚ n)}
    (hv : LinearIndependent ℚ v) : LinearIndependent ℂ (fun i => bcDual ℚ ℂ n (v i)) := by
  let cQ : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] (Fin (2 * n) → ℚ) :=
    LinearMap.pi fun k => Module.Dual.eval ℚ _ (e ℚ n k)
  let cC : Module.Dual ℂ (H1 ℂ n) →ₗ[ℂ] (Fin (2 * n) → ℂ) :=
    LinearMap.pi fun k => Module.Dual.eval ℂ _ (e ℂ n k)
  have hcQ : LinearMap.ker cQ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    refine s24b_dual_ext ℚ n fun k => ?_
    have := congrFun hy k
    simpa [cQ] using this
  have h2 : LinearIndependent ℂ (fun i => algebraMap ℚ ℂ ∘ (cQ ∘ v) i) :=
    linearIndependent_algebraMap_comp_iff.mpr (hv.map' cQ hcQ)
  have h3 : (fun i => algebraMap ℚ ℂ ∘ (cQ ∘ v) i) = cC ∘ (fun i => bcDual ℚ ℂ n (v i)) := by
    funext i k
    simp [cQ, cC, s24b_bcDual_e]
  rw [h3] at h2
  exact h2.of_comp

/-- `Φ z = Σ zᵢ bᵢ ∈ H₁(A, ℂ)`. -/
noncomputable def vo_Φ {k n : ℕ} (b : Fin k → Module.Dual ℚ (H1 ℚ n)) :
    (Fin k → ℂ) →ₗ[ℂ] Module.Dual ℂ (H1 ℂ n) :=
  Fintype.linearCombination ℂ fun i => bcDual ℚ ℂ n (b i)

/-- `p_c z = (f + c) Φ z`. -/
noncomputable def vo_p (X : PolarizedWeilType A d) (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (c : ℂ) : (Fin (2 * m) → ℂ) →ₗ[ℂ] Module.Dual ℂ (H1 ℂ (2 * m)) :=
  ((vo_fC X).dualMap + c • LinearMap.id) ∘ₗ vo_Φ b

theorem vo_p_apply (X : PolarizedWeilType A d) (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (c : ℂ) (z : Fin (2 * m) → ℂ) : vo_p X b c z = vo_Φ b z ∘ₗ vo_fC X + c • vo_Φ b z := rfl

theorem vo_p_sum (X : PolarizedWeilType A d) (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (c : ℂ) (z : Fin (2 * m) → ℂ) : vo_p X b c z =
      ∑ j, z j • (bcDual ℚ ℂ (2 * m) (b j) ∘ₗ vo_fC X + c • bcDual ℚ ℂ (2 * m) (b j)) := by
  rw [vo_p, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    vo_Φ, Fintype.linearCombination_apply, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.dualMap_apply', smul_add, smul_comm c]

theorem vo_p_injective (X : PolarizedWeilType A d)
    {b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m))}
    (hb : LinearIndependent ℚ (Sum.elim b fun i => X.fT (b i))) (c : ℂ) :
    Function.Injective (vo_p X b c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hU := vo_linIndep_bcDual hb
  have hsum : ∑ x, (Sum.elim (fun i => c * z i) z x) •
      bcDual ℚ ℂ (2 * m) (Sum.elim b (fun i => X.fT (b i)) x) = vo_p X b c z := by
    rw [vo_p_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [show X.fT (b i) = b i ∘ₗ X.η (Kd.sqrtNeg d) from rfl, vo_bcDual_comp_bcMap, smul_add,
      smul_smul, add_comm, mul_comm c (z i)]
    rfl
  rw [hz] at hsum
  funext i
  exact Fintype.linearIndependent_iff.mp hU _ hsum (Sum.inr i)

/-- `p_{√-d}` lands in the `√-d`-eigenspace of `fᵀ`. -/
theorem vo_p_mem (hd : 0 < d) (X : PolarizedWeilType A d)
    (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m))) {c : ℂ} (hc : c * c = -(d : ℂ))
    (z : Fin (2 * m) → ℂ) : vo_p X b c z ∘ₗ vo_fC X = c • vo_p X b c z := by
  rw [vo_p_apply, LinearMap.add_comp, LinearMap.smul_comp, vo_fC_sq_apply hd, smul_add,
    smul_smul, hc]
  module

theorem vo_sqrtNeg_conj : (starRingEnd ℂ) (sqrtNeg d) = -sqrtNeg d := fnd_conj_sqrtNeg d

theorem vo_dot_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z w : Fin n → ℂ) :
    star z ⬝ᵥ M *ᵥ w = ∑ i, ∑ j, star (z i) * M i j * w j := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The Gram matrix of `H` as a quadratic form: `z^* G w = E(Φ̄ z, p w)`. -/
theorem vo_gram_quad (X : PolarizedWeilType A d) (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (z w : Fin (2 * m) → ℂ) :
    star z ⬝ᵥ (Matrix.of fun i j => X.herm (b i) (b j)) *ᵥ w =
      eval2 ℂ (2 * m) (vo_hC X) (s24b_conjDual (2 * m) (vo_Φ b z)) (vo_p X b (sqrtNeg d) w) := by
  have hG : ∀ i j, X.herm (b i) (b j) = vo_E2 (2 * m) (vo_hC X) (bcDual ℚ ℂ (2 * m) (b i))
      (bcDual ℚ ℂ (2 * m) (b j) ∘ₗ vo_fC X + sqrtNeg d • bcDual ℚ ℂ (2 * m) (b j)) := by
    intro i j
    rw [vo_herm_eq, vo_herm, vo_E2_apply, vo_eval2_add_right, main_eval2_smul_right, vo_fC,
      ← vo_bcDual_comp_bcMap, vo_hC, s24b_eval2_bcS, s24b_eval2_bcS]
    simp
  have hconj : s24b_conjDual (2 * m) (vo_Φ b z) =
      ∑ i, (starRingEnd ℂ) (z i) • bcDual ℚ ℂ (2 * m) (b i) := by
    rw [vo_Φ, Fintype.linearCombination_apply]
    change vo_conjAdd (2 * m) _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change s24b_conjDual (2 * m) _ = _
    rw [s24b_conjDual_smul, vo_conj_bcDual]
  have hR : eval2 ℂ (2 * m) (vo_hC X) (s24b_conjDual (2 * m) (vo_Φ b z)) (vo_p X b (sqrtNeg d) w) =
      ∑ i, ∑ j, ((starRingEnd ℂ) (z i) * w j) * vo_E2 (2 * m) (vo_hC X)
        (bcDual ℚ ℂ (2 * m) (b i))
        (bcDual ℚ ℂ (2 * m) (b j) ∘ₗ vo_fC X + sqrtNeg d • bcDual ℚ ℂ (2 * m) (b j)) := by
    rw [← vo_E2_apply, hconj, vo_p_sum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [vo_dot_mulVec, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.of_apply, hG, Complex.star_def]
  ring

/-- The Gram matrix of `H` is Hermitian. -/
theorem vo_gram_hermitian (hd : 0 < d) (X : PolarizedWeilType A d)
    (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m))) :
    (Matrix.of fun i j => X.herm (b i) (b j)).IsHermitian := by
  have hs : ExteriorAlgebra.map (X.η (Kd.sqrtNeg d)) X.h = d • X.h := by
    rw [X.norm, vo_Nm_sqrtNeg hd]
  have hE : ∀ x y : Module.Dual ℚ (H1 ℚ (2 * m)),
      eval2 ℚ (2 * m) X.h y (x ∘ₗ X.η (Kd.sqrtNeg d)) =
        eval2 ℚ (2 * m) X.h x (y ∘ₗ X.η (Kd.sqrtNeg d)) := by
    intro x y
    rw [s24b_eval2_swap ℚ (2 * m) X.h y, vo_eval2_skew hd X.η hs x y, neg_neg]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, PolarizedWeilType.herm,
    PolarizedWeilType.E, PolarizedWeilType.fT, LinearMap.dualMap_apply', star_add, star_mul',
    Complex.star_def, map_ratCast, vo_sqrtNeg_conj]
  rw [hE, s24b_eval2_swap ℚ (2 * m) X.h (b j) (b i)]
  push_cast
  ring

end HermSign

section HermSignMain

open Matrix

variable {d : ℚ} {m : ℕ} {A : AbVar (2 * m)}

/-- **The sign of the discriminant** of a polarized abelian `2m`-fold of Weil type: in every
`K`-basis `b` of `H₁(A, ℚ)`, `(-1)^m det(H(bᵢ, bⱼ)) > 0` (`H` has signature `(m, m)`). -/
theorem vo_herm_det_sign (hd : 0 < d) (X : PolarizedWeilType A d)
    (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (hb : LinearIndependent ℚ (Sum.elim b fun i => X.fT (b i))) :
    0 < (-1 : ℝ) ^ m * (Matrix.of fun i j => X.herm (b i) (b j)).det.re ∧
      (Matrix.of fun i j => X.herm (b i) (b j)).det.im = 0 := by
  set s := sqrtNeg d with hs_def
  set G := Matrix.of fun i j => X.herm (b i) (b j)
  set JC := complexifyH1 (2 * m) A.J
  set fC := vo_fC X
  set p := vo_p X b s
  set p' := vo_p X b (-s)
  set W := Module.End.eigenspace (LinearMap.dualMap fC) s
  have hss : s * s = -(d : ℂ) := vo_sqrtNeg_mul_self hd
  have hss' : (-s) * (-s) = -(d : ℂ) := by rw [neg_mul_neg, hss]
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hs_def, sqrtNeg] at this
    exact hsd.ne' this
  have hpinj := vo_p_injective X hb s
  have hp'inj := vo_p_injective X hb (-s)
  have hpW : ∀ z, p z ∈ W := fun z =>
    Module.End.mem_eigenspace_iff.mpr (vo_p_mem hd X b hss z)
  have hW' : ∀ z, p' z ∈ Module.End.eigenspace (LinearMap.dualMap fC) (-s) := fun z =>
    Module.End.mem_eigenspace_iff.mpr (vo_p_mem hd X b hss' z)
  have hfin : Module.finrank ℂ (Fin (2 * m) → ℂ) = 2 * m := Module.finrank_fin_fun ℂ
  -- `p` maps `ℂ^{2m}` onto `W`
  have hrange : LinearMap.range p = W := by
    refine Submodule.eq_of_le_of_finrank_le (by rintro _ ⟨z, rfl⟩; exact hpW z) ?_
    rw [LinearMap.finrank_range_of_inj hpinj, hfin]
    have h1 : Module.finrank ℂ (LinearMap.range p') = 2 * m := by
      rw [LinearMap.finrank_range_of_inj hp'inj, hfin]
    have h2 : LinearMap.range p' ≤ Module.End.eigenspace (LinearMap.dualMap fC) (-s) := by
      rintro _ ⟨z, rfl⟩; exact hW' z
    have h3 := Submodule.finrank_mono h2
    have hdisj : W ⊓ Module.End.eigenspace (LinearMap.dualMap fC) (-s) = ⊥ := by
      refine eq_bot_iff.mpr fun u hu => ?_
      obtain ⟨h₁, h₂⟩ := hu
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h₁ h₂
      have : (2 * s) • u = 0 := by
        have e : (2 * s) • u = s • u - (-s) • u := by module
        rw [e, ← h₁, ← h₂, sub_self]
      exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp this).resolve_left
        (mul_ne_zero two_ne_zero hs0))
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq W
      (Module.End.eigenspace (LinearMap.dualMap fC) (-s))
    rw [hdisj, finrank_bot, add_zero] at h4
    have h5 := Submodule.finrank_le (W ⊔ Module.End.eigenspace (LinearMap.dualMap fC) (-s))
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h5
    omega
  -- `J` preserves `W`
  have hTW : ∀ u ∈ W, u ∘ₗ JC ∈ W := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    rw [LinearMap.dualMap_apply'] at hu ⊢
    have hcomm : JC ∘ₗ fC = fC ∘ₗ JC := (vo_fC_JC X).symm
    rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hu, LinearMap.smul_comp]
  let P' : Submodule ℂ (Fin (2 * m) → ℂ) :=
    (Module.End.eigenspace (LinearMap.dualMap JC) Complex.I).comap p
  let N' : Submodule ℂ (Fin (2 * m) → ℂ) :=
    (Module.End.eigenspace (LinearMap.dualMap JC) (-Complex.I)).comap p
  have hmemP : ∀ z, z ∈ P' ↔ p z ∘ₗ JC = Complex.I • p z := fun z => by
    simp only [P', Submodule.mem_comap, Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply']
  have hmemN : ∀ z, z ∈ N' ↔ p z ∘ₗ JC = (-Complex.I) • p z := fun z => by
    simp only [N', Submodule.mem_comap, Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply']
  -- `ℂ^{2m} = P' ⊕ N'`
  have hcompl : IsCompl P' N' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro z hz1 hz2
      rw [hmemP] at hz1
      rw [hmemN] at hz2
      have h3 : (2 * Complex.I) • p z = 0 := by
        have e : (2 * Complex.I) • p z = Complex.I • p z - (-Complex.I) • p z := by module
        rw [e, ← hz1, ← hz2, sub_self]
      have h4 : p z = 0 := (smul_eq_zero.mp h3).resolve_left
        (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      exact hpinj (h4.trans (map_zero p).symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro z _
      set u := p z
      have hu : u ∈ W := hpW z
      have hTu : u ∘ₗ JC ∈ W := hTW u hu
      have ha : (2 : ℂ)⁻¹ • (u - Complex.I • (u ∘ₗ JC)) ∈ LinearMap.range p := by
        rw [hrange]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hTu))
      have hc : (2 : ℂ)⁻¹ • (u + Complex.I • (u ∘ₗ JC)) ∈ LinearMap.range p := by
        rw [hrange]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ hu (Submodule.smul_mem _ _ hTu))
      obtain ⟨z₁, hz₁⟩ := ha
      obtain ⟨z₂, hz₂⟩ := hc
      have hJJ := vo_JC_sq A u
      have hz₁P : z₁ ∈ P' := by
        rw [hmemP, hz₁, LinearMap.smul_comp, LinearMap.sub_comp, LinearMap.smul_comp, hJJ]
        linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (u ∘ₗ JC))
      have hz₂N : z₂ ∈ N' := by
        rw [hmemN, hz₂, LinearMap.smul_comp, LinearMap.add_comp, LinearMap.smul_comp, hJJ]
        linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (u ∘ₗ JC))
      have hz : z = z₁ + z₂ := hpinj (by
        rw [map_add, hz₁, hz₂]
        module)
      rw [hz]
      exact Submodule.add_mem_sup hz₁P hz₂N
  -- `dim N' = m`, through `θ` and the Weil condition
  have hN : Module.finrank ℂ N' = m := by
    have hmap : Submodule.map p N' =
        W ⊓ Module.End.eigenspace (LinearMap.dualMap JC) (-Complex.I) := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hpW z, hz⟩
      · rintro ⟨hu, hu'⟩
        obtain ⟨z, rfl⟩ : u ∈ LinearMap.range p := by rw [hrange]; exact hu
        exact ⟨z, hu', rfl⟩
    set θ := contractOne ℂ (2 * m) (vo_hC X)
    have hθ := vo_theta_bijective X
    have hmapθ : Submodule.map θ (W ⊓ Module.End.eigenspace (LinearMap.dualMap JC) (-Complex.I)) =
        Module.End.eigenspace fC (-s) ⊓ H10 (2 * m) A.J := by
      ext v
      constructor
      · rintro ⟨u, ⟨hu, hu'⟩, rfl⟩
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply'] at hu hu'
        refine ⟨?_, ?_⟩
        · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
          have h1 := vo_theta_fC hd X u
          rw [hu, map_smul] at h1
          linear_combination (norm := module) h1
        · rw [SetLike.mem_coe, H10, Module.End.mem_eigenspace_iff]
          have h1 := vo_theta_JC X u
          rw [hu', map_smul] at h1
          linear_combination (norm := module) h1
      · rintro ⟨hv, hv'⟩
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
        rw [SetLike.mem_coe, H10, Module.End.mem_eigenspace_iff] at hv'
        obtain ⟨u, rfl⟩ := hθ.2 v
        refine ⟨u, ⟨?_, ?_⟩, rfl⟩
        · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply']
          apply hθ.1
          rw [vo_theta_fC hd X u, hv, map_smul, neg_smul, neg_neg]
        · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply']
          apply hθ.1
          rw [vo_theta_JC X u, hv', map_smul, neg_smul]
    rw [(Submodule.equivMapOfInjective p hpinj N').finrank_eq, hmap,
      (Submodule.equivMapOfInjective θ hθ.1 _).finrank_eq, hmapθ]
    exact X.weil₂
  -- `-2√-d · conj Φ z = conj(p z) - conj(p' z)`
  have hrel : ∀ z, (-(2 * s)) • s24b_conjDual (2 * m) (vo_Φ b z) =
      s24b_conjDual (2 * m) (p z) - s24b_conjDual (2 * m) (p' z) := by
    intro z
    have h1 : p z - p' z = (2 * s) • vo_Φ b z := by
      rw [vo_p_apply, vo_p_apply]
      module
    change _ = vo_conjAdd (2 * m) (p z) - vo_conjAdd (2 * m) (p' z)
    rw [← map_sub, h1]
    change _ = s24b_conjDual (2 * m) _
    rw [s24b_conjDual_smul, map_mul, vo_sqrtNeg_conj, map_ofNat, mul_neg]
  have hconjW : ∀ z, s24b_conjDual (2 * m) (p' z) ∘ₗ fC = s • s24b_conjDual (2 * m) (p' z) := by
    intro z
    rw [← vo_conj_fC, vo_p_mem hd X b hss' z, s24b_conjDual_smul, map_neg, vo_sqrtNeg_conj,
      neg_neg]
  have hQ : ∀ z w, (-(2 * s)) * (star z ⬝ᵥ G *ᵥ w) =
      eval2 ℂ (2 * m) (vo_hC X) (s24b_conjDual (2 * m) (p z)) (p w) := by
    intro z w
    rw [vo_gram_quad, ← vo_eval2_smul_left, hrel, sub_eq_add_neg, vo_eval2_add_left,
      ← neg_one_smul ℂ (s24b_conjDual (2 * m) (p' z)), vo_eval2_smul_left,
      vo_EC_W hd X (hconjW z) (vo_p_mem hd X b hss w), mul_zero, add_zero]
  have hsI : s = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := rfl
  have hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  -- definiteness
  have hdef : ∀ z (ε : ℂ), (ε = Complex.I ∨ ε = -Complex.I) → p z ∘ₗ JC = ε • p z → z ≠ 0 →
      ∃ P : ℝ, 0 < P ∧ star z ⬝ᵥ G *ᵥ z * ((Real.sqrt d : ℝ) : ℂ) = -Complex.I * ε * P := by
    intro z ε hε hz hz0
    have hpz : p z ≠ 0 := fun h => hz0 (hpinj (h.trans (map_zero p).symm))
    obtain ⟨P, hP, hE⟩ := vo_EC_conj_self X hε hz hpz
    refine ⟨P, hP, ?_⟩
    have h1 := hQ z z
    rw [hE, hsI] at h1
    linear_combination (Complex.I / 2) * h1 +
      (star z ⬝ᵥ G *ᵥ z * ((Real.sqrt d : ℝ) : ℂ)) * Complex.I_sq
  have hP : ∀ z ∈ P', z ≠ 0 → 0 < (star z ⬝ᵥ G *ᵥ z).re := by
    intro z hz hz0
    obtain ⟨P, hP, h⟩ := hdef z Complex.I (Or.inl rfl) ((hmemP z).mp hz) hz0
    have : star z ⬝ᵥ G *ᵥ z = ((P / Real.sqrt d : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff hr0, h]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, Complex.ofReal_re]
    exact div_pos hP hsd
  have hNneg : ∀ z ∈ N', z ≠ 0 → (star z ⬝ᵥ G *ᵥ z).re < 0 := by
    intro z hz hz0
    obtain ⟨P, hP, h⟩ := hdef z (-Complex.I) (Or.inr rfl) ((hmemN z).mp hz) hz0
    have : star z ⬝ᵥ G *ᵥ z = ((-P / Real.sqrt d : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff hr0, h]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hP) hsd
  -- orthogonality
  have horth : ∀ (μ : ℂ), μ * μ = -1 → ∀ z w, p z ∘ₗ JC = (-μ) • p z → p w ∘ₗ JC = μ • p w →
      star z ⬝ᵥ G *ᵥ w = 0 := by
    intro μ hμ z w hz hw
    have h1 := hQ z w
    have hcz : s24b_conjDual (2 * m) (p z) ∘ₗ JC = μ • s24b_conjDual (2 * m) (p z) := by
      have hc : (starRingEnd ℂ) (-μ) = μ := by
        have hμ' : μ = Complex.I ∨ μ = -Complex.I := by
          have : (μ - Complex.I) * (μ + Complex.I) = 0 := by
            linear_combination hμ - Complex.I_sq
          rcases mul_eq_zero.mp this with h | h
          · left; linear_combination h
          · right; linear_combination h
        rcases hμ' with rfl | rfl <;> simp
      rw [← s24b_conjDual_comp, hz, s24b_conjDual_smul, hc]
    rw [vo_EC_T X hμ hcz hw] at h1
    exact (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hs0))
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hI' : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  have h := vo_det_sign G (vo_gram_hermitian hd X b) P' N' hcompl hP hNneg
    (fun z hz w hw => horth (-Complex.I) hI' z w (by rw [neg_neg]; exact (hmemP z).mp hz)
      ((hmemN w).mp hw))
    (fun z hz w hw => horth Complex.I hI z w ((hmemN z).mp hz) ((hmemP w).mp hw))
  rwa [hN] at h

/-- The Gram determinant of `H` in a `K`-basis is rational. -/
theorem vo_det_rat (hd : 0 < d) (X : PolarizedWeilType A d)
    (b : Fin (2 * m) → Module.Dual ℚ (H1 ℚ (2 * m)))
    (him : (Matrix.of fun i j => X.herm (b i) (b j)).det.im = 0) :
    ∃ δ : ℚ, (Matrix.of fun i j => X.herm (b i) (b j)).det = (δ : ℂ) := by
  have hmem : ∀ i j, X.herm (b i) (b j) ∈ Kd d := fun i j =>
    (Kd.mem_iff d).mpr ⟨X.E (b i) (X.fT (b j)), X.E (b i) (b j), by
      simp only [PolarizedWeilType.herm]; ring⟩
  have hdet : (Matrix.of fun i j => X.herm (b i) (b j)).det ∈ Kd d := by
    have := RingHom.map_det (Kd d).subtype (Matrix.of fun i j => (⟨X.herm (b i) (b j), hmem i j⟩ : Kd d))
    have h2 : (Kd d).subtype.mapMatrix (Matrix.of fun i j => (⟨X.herm (b i) (b j), hmem i j⟩ : Kd d)) =
        Matrix.of fun i j => X.herm (b i) (b j) := by
      ext i j; rfl
    rw [h2] at this
    rw [← this]
    exact Subtype.mem _
  obtain ⟨a, c, hac⟩ := (Kd.mem_iff d).mp hdet
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hc : c = 0 := by
    rw [hac] at him
    simp [sqrtNeg] at him
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h hsd.ne'
  exact ⟨a, by rw [hac, hc]; simp⟩

/-- **Step 1 (discriminant).** A polarized abelian fourfold of Weil type has a `K`-basis in which
the Gram determinant of `H` is a positive rational number `δ`. -/
theorem vo_disc_pos (hd : 0 < d) {A : AbVar (2 * 2)} (X : PolarizedWeilType A d) :
    ∃ b : Fin (2 * 2) → Module.Dual ℚ (H1 ℚ (2 * 2)),
      LinearIndependent ℚ (Sum.elim b fun i => X.fT (b i)) ∧
      ∃ δ : ℚ, 0 < δ ∧ (Matrix.of fun i j => X.herm (b i) (b j)).det = (δ : ℂ) := by
  have hφ : X.fT * X.fT = -(d • 1) := by
    refine LinearMap.ext fun y => LinearMap.ext fun v => ?_
    simp only [PolarizedWeilType.fT, Module.End.mul_apply, LinearMap.dualMap_apply',
      LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply,
      ← Module.End.mul_apply (X.η (Kd.sqrtNeg d)), vo_eta_sq hd X.η]
    simp
  obtain ⟨b, hb⟩ := vo_exists_kBasis (M := Module.Dual ℚ (H1 ℚ (2 * 2))) hd X.fT hφ
    (k := 2 * 2) (by rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun])
  refine ⟨b, hb, ?_⟩
  obtain ⟨hre, him⟩ := vo_herm_det_sign hd X b hb
  obtain ⟨δ, hδ⟩ := vo_det_rat hd X b him
  refine ⟨δ, ?_, hδ⟩
  rw [hδ, Complex.ratCast_re] at hre
  have : (0 : ℝ) < δ := by simpa using hre
  exact_mod_cast this

end HermSignMain

/-! ### Step 2: the Weil surface `E₊ × E₋`

`E₊` and `E₋` are the elliptic curves `H¹ = ℚ²` with complex multiplication by `K`, `η(√-d) = f`,
`f(e₀) = e₁`, `f(e₁) = -d e₀`, and the complex structures `J = ± f/√d` (the two CM types). On the
surface `E₊ × E₋`, `√-d` acts on `H^{1,0}` with the eigenvalues `√-d` and `-√-d`, once each: it is
an abelian surface of Weil type. -/

section Surface

/-- `f(e₀) = e₁`, `f(e₁) = -c e₀` on `H¹(E, F) = F²`. -/
noncomputable def vo_fE (F : Type*) [Field F] (c : F) : Module.End F (H1 F 1) :=
  Matrix.toLin' !![0, -c; 1, 0]

theorem vo_fE_apply (F : Type*) [Field F] (c : F) (v : H1 F 1) :
    vo_fE F c v = (![-c * v 1, v 0] : H1 F 1) := by
  funext i
  fin_cases i <;> simp [vo_fE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem vo_fE_sq (F : Type*) [Field F] (c : F) : vo_fE F c * vo_fE F c = -(c • 1) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Module.End.mul_apply, vo_fE_apply, vo_fE_apply]
  fin_cases i <;> simp

theorem vo_bcMap_fE {F F' : Type*} [Field F] [Field F'] [Algebra F F'] (c : F) :
    bcMap F F' (vo_fE F c) = vo_fE F' (algebraMap F F' c) := by
  simp only [bcMap, vo_fE, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `(μ, 1)` is an eigenvector of `f` with eigenvalue `μ` when `μ² = -c`. -/
theorem vo_fE_eigvec (F : Type*) [Field F] (c μ : F) (hμ : μ * μ = -c) :
    vo_fE F c (![μ, 1] : H1 F 1) = μ • (![μ, 1] : H1 F 1) := by
  rw [vo_fE_apply]
  funext i
  fin_cases i <;> simp [hμ]

theorem vo_eigenspace_fE (F : Type*) [Field F] (c μ : F) (hμ : μ * μ = -c) :
    Module.End.eigenspace (vo_fE F c) μ = Submodule.span F {(![μ, 1] : H1 F 1)} := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v 1, funext fun i => ?_⟩
    have h1 := congrFun h 1
    rw [vo_fE_apply] at h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul] at h1
    fin_cases i
    · simp [h1, mul_comm]
    · simp
  · rintro ⟨a, rfl⟩
    rw [map_smul, vo_fE_eigvec F c μ hμ, smul_comm]

theorem vo_finrank_eigenspace_fE (F : Type*) [Field F] (c μ : F) (hμ : μ * μ = -c) :
    Module.finrank F (Module.End.eigenspace (vo_fE F c) μ) = 1 := by
  rw [vo_eigenspace_fE F c μ hμ]
  refine finrank_span_singleton fun h => ?_
  have := congrFun h 1
  simp at this

/-- On an eigenspace of `φ` with eigenvalue `μ`, `c φ` acts by `c μ`. -/
theorem vo_eigenspace_inf_smul_of_eq {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (φ : Module.End F M) {c μ ν : F} (h : c * μ = ν) :
    Module.End.eigenspace φ μ ⊓ Module.End.eigenspace (c • φ) ν = Module.End.eigenspace φ μ := by
  refine inf_eq_left.mpr fun v hv => ?_
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [LinearMap.smul_apply, hv, smul_smul, h]

theorem vo_eigenspace_inf_smul_of_ne {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (φ : Module.End F M) {c μ ν : F} (h : c * μ ≠ ν) :
    Module.End.eigenspace φ μ ⊓ Module.End.eigenspace (c • φ) ν = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  obtain ⟨h1, h2⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 h2
  rw [LinearMap.smul_apply, h1, smul_smul] at h2
  have : (c * μ - ν) • v = 0 := by rw [sub_smul, h2, sub_self]
  exact (Submodule.mem_bot F).mpr ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h))

variable {d : ℚ}

/-- The complex structure `J = ε f/√d` of `H¹(E, ℝ)` (`ε = ±1`). -/
noncomputable def vo_JE (d : ℚ) (ε : ℝ) : Module.End ℝ (H1 ℝ 1) :=
  (ε / Real.sqrt d) • vo_fE ℝ (d : ℝ)

theorem vo_bcMap_fE_real (d : ℚ) : bcMap ℚ ℝ (vo_fE ℚ d) = vo_fE ℝ (d : ℝ) := by
  rw [vo_bcMap_fE, eq_ratCast]

theorem vo_bcMap_fE_complex (d : ℚ) : bcMap ℚ ℂ (vo_fE ℚ d) = vo_fE ℂ (d : ℂ) := by
  rw [vo_bcMap_fE, eq_ratCast]

theorem vo_JE_isComplex (hd : 0 < d) {ε : ℝ} (hε : ε * ε = 1) : IsComplexStructure (vo_JE d ε) := by
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have hs0 : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [IsComplexStructure, vo_JE, smul_mul_smul_comm, vo_fE_sq, smul_neg, smul_smul]
  have : ε / Real.sqrt d * (ε / Real.sqrt d) * (d : ℝ) = 1 := by
    field_simp
    nlinarith
  rw [this, one_smul]

theorem vo_complexifyH1_JE (d : ℚ) (ε : ℝ) :
    complexifyH1 1 (vo_JE d ε) = (((ε / Real.sqrt d : ℝ)) : ℂ) • vo_fE ℂ (d : ℂ) := by
  rw [main_lef_complexifyH1_eq, vo_JE, main_bcMap_smul, vo_bcMap_fE]
  congr 1

/-- `(ε/√d) √-d = ε i`. -/
theorem vo_JE_coeff (hd : 0 < d) (ε : ℝ) :
    (((ε / Real.sqrt d : ℝ)) : ℂ) * sqrtNeg d = ε * Complex.I := by
  have hs0 : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [sqrtNeg]
  push_cast
  field_simp

/-- The ample class `-r e₀ ∧ e₁` on `E`. -/
noncomputable def vo_ΘE (r : ℚ) : S ℚ 1 :=
  (-r) • (ExteriorAlgebra.ι ℚ (e ℚ 1 0) * ExteriorAlgebra.ι ℚ (e ℚ 1 1))

theorem vo_e_one_apply (F : Type*) [Field F] (v : H1 F 1) :
    v = v 0 • e F 1 0 + v 1 • e F 1 1 := by
  funext i
  fin_cases i <;> simp [e]

theorem vo_fE_e0 (F : Type*) [Field F] (c : F) : vo_fE F c (e F 1 0) = e F 1 1 := by
  rw [vo_fE_apply]; funext i; fin_cases i <;> simp [e]

theorem vo_fE_e1 (F : Type*) [Field F] (c : F) : vo_fE F c (e F 1 1) = -c • e F 1 0 := by
  rw [vo_fE_apply]; funext i; fin_cases i <;> simp [e]

theorem vo_ΘE_mem (r : ℚ) : vo_ΘE r ∈ ⋀[ℚ]^2 (H1 ℚ 1) := by
  refine Submodule.smul_mem _ _ ?_
  have h := main_lef_ιMulti_two (F := ℚ) (g := 1) ![e ℚ 1 0, e ℚ 1 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h]
  exact ExteriorAlgebra.ιMulti_range ℚ 2 ⟨_, rfl⟩

theorem vo_bcS_ΘE (F : Type*) [Field F] [CharZero F] (r : ℚ) :
    bcS ℚ F 1 (vo_ΘE r) = (algebraMap ℚ F (-r)) •
      (ExteriorAlgebra.ι F (e F 1 0) * ExteriorAlgebra.ι F (e F 1 1)) := by
  rw [vo_ΘE, map_smul, map_mul, main_bcS_ι, main_bcS_ι, main_bcH1_e, main_bcH1_e,
    algebraMap_smul]

/-- `-r e₀ ∧ e₁` is ample for `J = ε f/√d` when `r ε > 0`. -/
theorem vo_ΘE_ample (hd : 0 < d) {ε : ℝ} (hε : ε * ε = 1) {r : ℚ} (hr : 0 < (r : ℝ) * ε) :
    IsAmple 1 (vo_JE d ε) (vo_ΘE r) := by
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have hsp : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  set c : ℝ := ε / Real.sqrt d with hc
  have hJ0 : vo_JE d ε (e ℝ 1 0) = c • e ℝ 1 1 := by
    rw [vo_JE, LinearMap.smul_apply, vo_fE_e0]
  have hJ1 : vo_JE d ε (e ℝ 1 1) = (-(c * d)) • e ℝ 1 0 := by
    rw [vo_JE, LinearMap.smul_apply, vo_fE_e1, smul_smul, ← hc, mul_neg]
  have hcd : c * c * (d : ℝ) = 1 := by
    rw [hc]; field_simp; nlinarith
  refine ⟨main_lef_hodge_one_of_map (vo_JE_isComplex hd hε) (vo_ΘE_mem r) ?_, fun a ha => ?_⟩
  · rw [vo_bcS_ΘE, map_smul, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
      hJ0, hJ1, map_smul, map_smul, smul_mul_smul_comm,
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e ℝ 1 1) (e ℝ 1 0)),
      smul_neg, ← neg_smul, show -(c * -(c * (d : ℝ))) = c * c * d by ring, hcd, one_smul]
  · rw [vo_bcS_ΘE, vo_eval2_smul, main_eval2_ι_mul_ι]
    simp only [LinearMap.comp_apply, hJ0, hJ1, map_smul, smul_eq_mul, eq_ratCast]
    have ha' : a (e ℝ 1 0) ≠ 0 ∨ a (e ℝ 1 1) ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply ha
      refine LinearMap.ext fun v => ?_
      rw [vo_e_one_apply ℝ v, map_add, map_smul, map_smul, h.1, h.2]
      simp
    have hpos : 0 < (d : ℝ) * a (e ℝ 1 0) ^ 2 + a (e ℝ 1 1) ^ 2 := by
      rcases ha' with h | h
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        nlinarith [sq_nonneg (a (e ℝ 1 1))]
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        nlinarith [sq_nonneg (a (e ℝ 1 0))]
    have hrc : 0 < (r : ℝ) * c := by
      rw [hc, mul_div_assoc']; exact div_pos hr hsp
    have : (((-r : ℚ) : ℝ)) * (a (e ℝ 1 0) * (-(c * d) * a (e ℝ 1 0)) -
        a (e ℝ 1 1) * (c * a (e ℝ 1 1))) =
        ((r : ℝ) * c) * ((d : ℝ) * a (e ℝ 1 0) ^ 2 + a (e ℝ 1 1) ^ 2) := by
      push_cast; ring
    rw [this]
    exact mul_pos hrc hpos

/-- An elliptic curve `E = (ℚ², ε f/√d)` with complex multiplication by `K` (`ε = ±1`). -/
noncomputable def vo_E (hd : 0 < d) (ε : ℝ) (hε : ε * ε = 1) : AbVar 1 where
  J := vo_JE d ε
  isComplex := vo_JE_isComplex hd hε
  polarizable := by
    rcases mul_self_eq_one_iff.mp hε with h | h
    · exact ⟨vo_ΘE 1, vo_ΘE_ample hd hε (by rw [h]; norm_num)⟩
    · exact ⟨vo_ΘE (-1), vo_ΘE_ample hd hε (by rw [h]; norm_num)⟩

/-- The action of `K` on `H¹(E, ℚ)`, `η(√-d) = f`. -/
noncomputable def vo_ηE (hd : 0 < d) : Kd d →+* Module.End ℚ (H1 ℚ 1) :=
  vo_etaOf hd (vo_fE ℚ d) (vo_fE_sq ℚ d)

theorem vo_ηE_sqrtNeg (hd : 0 < d) : vo_ηE hd (Kd.sqrtNeg d) = vo_fE ℚ d :=
  vo_etaOf_sqrtNeg hd _ _

theorem vo_bcMap_add {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {g g' : ℕ}
    (φ ψ : H1 F g →ₗ[F] H1 F g') : bcMap F F' (φ + ψ) = bcMap F F' φ + bcMap F F' ψ := by
  simp only [bcMap, map_add]
  rw [Matrix.map_add _ (map_add (algebraMap F F')), map_add]

/-- If `J` commutes with `η(√-d)`, every `η(k)` is a morphism of Hodge structures. -/
theorem vo_isHodge_of_sqrtNeg {g : ℕ} (hd : 0 < d) (η : Kd d →+* Module.End ℚ (H1 ℚ g))
    (J : Module.End ℝ (H1 ℝ g)) (h : IsHodgeMap J J (η (Kd.sqrtNeg d))) (k : Kd d) :
    IsHodgeMap J J (η k) := by
  rw [vo_eta_apply hd η k, IsHodgeMap, vo_bcMap_add, main_bcMap_smul, main_bcMap_smul]
  rw [IsHodgeMap] at h
  have h1 : bcMap ℚ ℝ (1 : Module.End ℚ (H1 ℚ g)) = LinearMap.id := main_bcMap_id
  rw [h1, LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.smul_comp,
    LinearMap.comp_smul, LinearMap.comp_smul, h, LinearMap.id_comp, LinearMap.comp_id]

theorem vo_isHodge_E (hd : 0 < d) (ε : ℝ) (k : Kd d) :
    IsHodgeMap (vo_JE d ε) (vo_JE d ε) (vo_ηE hd k) := by
  refine vo_isHodge_of_sqrtNeg hd _ _ ?_ k
  rw [vo_ηE_sqrtNeg, IsHodgeMap, vo_bcMap_fE_real, vo_JE, LinearMap.comp_smul, LinearMap.smul_comp]

/-- The `μ`-eigenspace of `f` (`μ = ±√-d`) lies in `H^{1,0}(E)` if `J` acts on it by `i`. -/
theorem vo_weil_E_one (hd : 0 < d) {ε : ℝ} {μ : ℂ} (hμ : μ * μ = -(d : ℂ))
    (h : ((ε / Real.sqrt d : ℝ) : ℂ) * μ = Complex.I) :
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (vo_ηE hd (Kd.sqrtNeg d))) μ ⊓
        H10 1 (vo_JE d ε)) = 1 := by
  rw [vo_ηE_sqrtNeg, vo_bcMap_fE_complex, H10, vo_complexifyH1_JE,
    vo_eigenspace_inf_smul_of_eq _ h, vo_finrank_eigenspace_fE ℂ _ μ hμ]

/-- ... and meets it in `0` otherwise. -/
theorem vo_weil_E_zero (hd : 0 < d) {ε : ℝ} {μ : ℂ}
    (h : ((ε / Real.sqrt d : ℝ) : ℂ) * μ ≠ Complex.I) :
    Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (vo_ηE hd (Kd.sqrtNeg d))) μ ⊓
        H10 1 (vo_JE d ε)) = 0 := by
  rw [vo_ηE_sqrtNeg, vo_bcMap_fE_complex, H10, vo_complexifyH1_JE,
    vo_eigenspace_inf_smul_of_ne _ h, finrank_bot]

end Surface

/-! ### The Weil surface `E₊ × E₋` as a polarized abelian surface of Weil type -/

section SurfaceX

variable {d : ℚ}

/-- **The Weil surface** `E₊ × E₋` (`J = f/√d` on the first factor, `-f/√d` on the second). -/
noncomputable def vo_surface (hd : 0 < d) : AbVar (2 * 1) :=
  (vo_E hd 1 (by norm_num)).prod (vo_E hd (-1) (by norm_num))

theorem vo_surface_J (hd : 0 < d) : (vo_surface hd).J = prodJ (vo_JE d 1) (vo_JE d (-1)) := rfl

/-- The polarization `h₁ = pr₁^*Θ₊ + pr₂^*(δ Θ₋)` of `E₊ × E₋` (`Θ₊ = -e₀ ∧ e₁`,
`Θ₋ = e₀ ∧ e₁`). -/
noncomputable def vo_hS (δ : ℚ) : S ℚ (2 * 1) :=
  ExteriorAlgebra.map (prodInl ℚ 1 1) (vo_ΘE 1) + ExteriorAlgebra.map (prodInr ℚ 1 1) (vo_ΘE (-δ))

theorem vo_map_fE_ΘE (r : ℚ) :
    ExteriorAlgebra.map (vo_fE ℚ d) (vo_ΘE r) = d • vo_ΘE r := by
  rw [vo_ΘE, map_smul, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
    vo_fE_e0, vo_fE_e1, map_smul, mul_smul_comm,
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e ℚ 1 1) (e ℚ 1 0)), smul_neg,
    ← neg_smul, neg_neg, smul_comm]

theorem vo_norm_E (hd : 0 < d) (r : ℚ) (k : Kd d) :
    ExteriorAlgebra.map (vo_ηE hd k) (vo_ΘE r) = Kd.Nm d k • vo_ΘE r :=
  vo_norm_of_sqrtNeg hd _ (vo_ΘE_mem r) (by rw [vo_ηE_sqrtNeg, vo_map_fE_ΘE]) k

theorem vo_coeff_plus (hd : 0 < d) : ((1 / Real.sqrt d : ℝ) : ℂ) * sqrtNeg d = Complex.I := by
  simpa using vo_JE_coeff hd 1

theorem vo_coeff_minus (hd : 0 < d) : ((-1 / Real.sqrt d : ℝ) : ℂ) * sqrtNeg d = -Complex.I := by
  simpa using vo_JE_coeff hd (-1)

theorem vo_I_ne_neg_I : -Complex.I ≠ Complex.I := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- **Step 2.** `E₊ × E₋` with `η = η_E × η_E` and the polarization `h₁ = pr₁^*Θ₊ + δ pr₂^*Θ₋` is a
polarized abelian surface of Weil type. Its Hermitian form is `diag(d, -dδ)` in the `K`-basis
`(f₀ ∘ pr₁, f₀ ∘ pr₂)` (`vo_det_gram_surface`), so its discriminant is `-δ` for `δ > 0`. -/
noncomputable def vo_XS (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) : PolarizedWeilType (vo_surface hd) d where
  η := vo_prodη (g₁ := 1) (g₂ := 1) (vo_ηE hd) (vo_ηE hd)
  isHodge k := vo_isHodgeMap_prodEnd (vo_isHodge_E hd 1 k) (vo_isHodge_E hd (-1) k)
  weil₁ := (vo_finrank_weil_prod (vo_ηE hd) (vo_ηE hd) (vo_JE d 1) (vo_JE d (-1)) _).trans (by
    rw [vo_weil_E_one hd (vo_sqrtNeg_mul_self hd) (vo_coeff_plus hd),
      vo_weil_E_zero hd (by rw [vo_coeff_minus hd]; exact vo_I_ne_neg_I)])
  weil₂ := (vo_finrank_weil_prod (vo_ηE hd) (vo_ηE hd) (vo_JE d 1) (vo_JE d (-1)) _).trans (by
    rw [vo_weil_E_zero hd (by rw [mul_neg, vo_coeff_plus hd]; exact vo_I_ne_neg_I),
      vo_weil_E_one hd (by rw [neg_mul_neg, vo_sqrtNeg_mul_self hd])
        (by rw [mul_neg, vo_coeff_minus hd, neg_neg])])
  h := vo_hS δ
  ample := vo_isAmple_prod (vo_JE_isComplex hd (by norm_num)) (vo_JE_isComplex hd (by norm_num))
    (vo_ΘE_ample hd (by norm_num) (by norm_num))
    (vo_ΘE_ample hd (by norm_num) (by
      have : (0 : ℝ) < δ := by exact_mod_cast hδ
      push_cast; linarith))
  norm := vo_norm_prod _ _ (vo_norm_E hd 1) (vo_norm_E hd (-δ))

theorem vo_XS_η (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) :
    (vo_XS hd hδ).η = vo_prodη (g₁ := 1) (g₂ := 1) (vo_ηE hd) (vo_ηE hd) := rfl

theorem vo_XS_h (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) : (vo_XS hd hδ).h = vo_hS δ := rfl

/-- `f₀ ∘ f = -d f₁`. -/
theorem vo_f0_comp_fE : f ℚ 1 0 ∘ₗ vo_fE ℚ d = (-d) • f ℚ 1 1 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, vo_fE_apply]
  simp [f]

theorem vo_herm_ΘE (r : ℚ) :
    vo_herm d (vo_ΘE r) (vo_fE ℚ d) (f ℚ 1 0) (f ℚ 1 0) = ((d * r : ℚ) : ℂ) := by
  rw [vo_herm, vo_f0_comp_fE, main_eval2_smul_right, vo_ΘE, vo_eval2_smul, vo_eval2_smul,
    main_eval2_ι_mul_ι, main_eval2_ι_mul_ι]
  simp [f, e]

/-- The `K`-basis `(f₀ ∘ pr₁, f₀ ∘ pr₂)` of `H₁(E₊ × E₋)`. -/
noncomputable def vo_bS : Fin (1 + 1) → Module.Dual ℚ (H1 ℚ (1 + 1)) :=
  vo_prodBasis (fun _ : Fin 1 => f ℚ 1 0) (fun _ : Fin 1 => f ℚ 1 0)

theorem vo_det_gram_surface (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) :
    (Matrix.of fun i j => (vo_XS hd hδ).herm (vo_bS i) (vo_bS j)).det = ((-(d ^ 2 * δ) : ℚ) : ℂ) := by
  have h := vo_det_gram_prod (d := d) (vo_ΘE 1) (vo_ΘE (-δ)) (vo_ηE hd (Kd.sqrtNeg d))
    (vo_ηE hd (Kd.sqrtNeg d)) (fun _ : Fin 1 => f ℚ 1 0) (fun _ : Fin 1 => f ℚ 1 0)
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at h
  refine h.trans ?_
  simp only [Matrix.of_apply, vo_ηE_sqrtNeg, vo_herm_ΘE]
  push_cast
  ring

theorem vo_linIndep_E (hd : 0 < d) :
    LinearIndependent ℚ (Sum.elim (fun _ : Fin 1 => f ℚ 1 0)
      (fun _ : Fin 1 => f ℚ 1 0 ∘ₗ vo_ηE hd (Kd.sqrtNeg d))) := by
  rw [vo_ηE_sqrtNeg, vo_f0_comp_fE, Fintype.linearIndependent_iff]
  intro c hc x
  have h0 := LinearMap.congr_fun hc (e ℚ 1 0)
  have h1 := LinearMap.congr_fun hc (e ℚ 1 1)
  have hd0 : d ≠ 0 := hd.ne'
  simp [Fintype.sum_sum_type, f, e, hd0] at h0 h1
  rcases x with i | i <;> rw [Subsingleton.elim i 0] <;> assumption

theorem vo_linIndep_surface (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) :
    LinearIndependent ℚ (Sum.elim vo_bS (fun i => (vo_XS hd hδ).fT (vo_bS i))) :=
  vo_linIndep_prodBasis _ _ _ _ (vo_linIndep_E hd) (vo_linIndep_E hd)

end SurfaceX

/-! ### Classes on the Weil surface

With `aᵢ = pr₁^*eᵢ` and `bⱼ = pr₂^*eⱼ` (`i, j ∈ {0, 1}`), the rational classes
`A = a₁ ∧ b₁ - d a₀ ∧ b₀` and `B = a₀ ∧ b₁ + a₁ ∧ b₀` satisfy `2A = ω + ω̄` and `2√-d B = ω - ω̄`,
where `ω = pr₁^*w ∧ pr₂^*w`, `w = √-d e₀ + e₁`, spans `⋀²W` and `ω̄ = pr₁^*w̄ ∧ pr₂^*w̄` spans
`⋀²W̄`. `A` is of type `(1,1)`, `A² = 2d [pt]` and `AB = 0`. -/

section SurfaceClasses

variable {d : ℚ}

/-- `aᵢ = pr₁^*eᵢ ∈ H¹(E₊ × E₋, F)`. -/
noncomputable def vo_a (F : Type*) [Field F] (i : Fin (2 * 1)) : S F (1 + 1) :=
  ExteriorAlgebra.ι F (prodInl F 1 1 (e F 1 i))

/-- `bⱼ = pr₂^*eⱼ ∈ H¹(E₊ × E₋, F)`. -/
noncomputable def vo_b (F : Type*) [Field F] (j : Fin (2 * 1)) : S F (1 + 1) :=
  ExteriorAlgebra.ι F (prodInr F 1 1 (e F 1 j))

/-- `A = a₁ ∧ b₁ - d a₀ ∧ b₀`. -/
noncomputable def vo_AS (d : ℚ) : S ℚ (1 + 1) := vo_a ℚ 1 * vo_b ℚ 1 - d • (vo_a ℚ 0 * vo_b ℚ 0)

/-- `B = a₀ ∧ b₁ + a₁ ∧ b₀`. -/
noncomputable def vo_BS : S ℚ (1 + 1) := vo_a ℚ 0 * vo_b ℚ 1 + vo_a ℚ 1 * vo_b ℚ 0

/-- `w_t = t e₀ + e₁`. -/
noncomputable def vo_wE (F : Type*) [Field F] (t : F) : H1 F 1 := ![t, 1]

/-- `ω_t = pr₁^*w_t ∧ pr₂^*w_t`. -/
noncomputable def vo_ωS (F : Type*) [Field F] (t : F) : S F (1 + 1) :=
  ExteriorAlgebra.ι F (prodInl F 1 1 (vo_wE F t)) * ExteriorAlgebra.ι F (prodInr F 1 1 (vo_wE F t))

theorem vo_wE_eq (F : Type*) [Field F] (t : F) : vo_wE F t = t • e F 1 0 + e F 1 1 := by
  conv_lhs => rw [vo_e_one_apply F (vo_wE F t)]
  simp [vo_wE]

theorem vo_ωS_eq (F : Type*) [Field F] (t : F) :
    vo_ωS F t = (t • vo_a F 0 + vo_a F 1) * (t • vo_b F 0 + vo_b F 1) := by
  simp only [vo_ωS, vo_wE_eq, map_add, map_smul, vo_a, vo_b]

theorem vo_bcS_a (F : Type*) [Field F] [CharZero F] (i : Fin (2 * 1)) :
    bcS ℚ F (1 + 1) (vo_a ℚ i) = vo_a F i := by
  rw [vo_a, vo_a, main_bcS_ι, ← main_bcMap_bcH1, vo_bcMap_prodInl, main_bcH1_e]

theorem vo_bcS_b (F : Type*) [Field F] [CharZero F] (j : Fin (2 * 1)) :
    bcS ℚ F (1 + 1) (vo_b ℚ j) = vo_b F j := by
  rw [vo_b, vo_b, main_bcS_ι, ← main_bcMap_bcH1, vo_bcMap_prodInr, main_bcH1_e]

/-- `2A = ω_t + ω_{-t}` for `t² = -d`. -/
theorem vo_two_bcS_AS (F : Type*) [Field F] [CharZero F] {t : F}
    (ht : t * t = -algebraMap ℚ F d) :
    (2 : F) • bcS ℚ F (1 + 1) (vo_AS d) = vo_ωS F t + vo_ωS F (-t) := by
  have key : ∀ X₀ Y₀ X₁ Y₁ : S F (1 + 1), (t • X₀ + X₁) * (t • Y₀ + Y₁) +
      ((-t) • X₀ + X₁) * ((-t) • Y₀ + Y₁) = (2 * (t * t)) • (X₀ * Y₀) + (2 : F) • (X₁ * Y₁) := by
    intro X₀ Y₀ X₁ Y₁
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  rw [vo_AS, map_sub, map_smul, map_mul, map_mul, vo_bcS_a, vo_bcS_a, vo_bcS_b, vo_bcS_b,
    vo_ωS_eq, vo_ωS_eq, key, ht, ← algebraMap_smul F d]
  module

/-- `2t B = ω_t - ω_{-t}`. -/
theorem vo_two_bcS_BS (F : Type*) [Field F] [CharZero F] (t : F) :
    (2 * t) • bcS ℚ F (1 + 1) vo_BS = vo_ωS F t - vo_ωS F (-t) := by
  rw [vo_BS, map_add, map_mul, map_mul, vo_bcS_a, vo_bcS_a, vo_bcS_b, vo_bcS_b, vo_ωS_eq,
    vo_ωS_eq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

theorem vo_fE_wE (F : Type*) [Field F] [CharZero F] {t : F} (ht : t * t = -algebraMap ℚ F d) :
    bcMap ℚ F (vo_fE ℚ d) (vo_wE F t) = t • vo_wE F t := by
  rw [vo_bcMap_fE, vo_wE]
  exact vo_fE_eigvec F _ t ht

/-- `ω_t ∈ ⋀²W_t`, `W_t` the `t`-eigenspace of `η(√-d)` on `H¹(E₊ × E₋, F)`. -/
theorem vo_ωS_mem (hd : 0 < d) (F : Type*) [Field F] [CharZero F] {t : F}
    (ht : t * t = -algebraMap ℚ F d) :
    vo_ωS F t ∈ topWedge (Module.End.eigenspace (bcMap ℚ F
      (vo_prodη (g₁ := 1) (g₂ := 1) (vo_ηE hd) (vo_ηE hd) (Kd.sqrtNeg d))) t) 2 := by
  rw [vo_prodη_apply, vo_ηE_sqrtNeg, vo_bcMap_prodEnd]
  have h1 : prodInl F 1 1 (vo_wE F t) ∈ Module.End.eigenspace
      (vo_prodEnd (bcMap ℚ F (vo_fE ℚ d)) (bcMap ℚ F (vo_fE ℚ d))) t := by
    rw [Module.End.mem_eigenspace_iff, vo_prodEnd_prodInl, vo_fE_wE F ht, map_smul]
  have h2 : prodInr F 1 1 (vo_wE F t) ∈ Module.End.eigenspace
      (vo_prodEnd (bcMap ℚ F (vo_fE ℚ d)) (bcMap ℚ F (vo_fE ℚ d))) t := by
    rw [Module.End.mem_eigenspace_iff, vo_prodEnd_prodInr, vo_fE_wE F ht, map_smul]
  have hι := main_lef_ιMulti_two (F := F) (g := 1 + 1)
    ![prodInl F 1 1 (vo_wE F t), prodInr F 1 1 (vo_wE F t)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hι
  rw [vo_ωS, ← hι]
  refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
  fin_cases i
  · exact h1
  · exact h2

/-- `A` is of type `(1,1)` on `E₊ × E₋`. -/
theorem vo_AS_hodge (hd : 0 < d) : vo_AS d ∈ (vo_surface hd).hodge 1 := by
  have hs : sqrtNeg d * sqrtNeg d = -algebraMap ℚ ℂ d := by
    rw [vo_sqrtNeg_mul_self hd, eq_ratCast]
  have hs' : (-sqrtNeg d) * (-sqrtNeg d) = -algebraMap ℚ ℂ d := by rw [neg_mul_neg, hs]
  have hJ : complexifyH1 (1 + 1) (vo_surface hd).J = vo_prodEnd
      ((((1 / Real.sqrt d : ℝ)) : ℂ) • vo_fE ℂ (d : ℂ))
      ((((-1 / Real.sqrt d : ℝ)) : ℂ) • vo_fE ℂ (d : ℂ)) := by
    rw [vo_surface_J, vo_complexifyH1_prodJ, vo_complexifyH1_JE, vo_complexifyH1_JE]
  have hw : ∀ t : ℂ, t * t = -algebraMap ℚ ℂ d → vo_fE ℂ (d : ℂ) (vo_wE ℂ t) = t • vo_wE ℂ t :=
    fun t ht => by rw [← vo_bcMap_fE_complex, vo_fE_wE ℂ ht]
  have hmem : ∀ (t c : ℂ), t * t = -algebraMap ℚ ℂ d →
      (c • vo_fE ℂ (d : ℂ)) (vo_wE ℂ t) = (c * t) • vo_wE ℂ t := fun t c ht => by
    rw [LinearMap.smul_apply, hw t ht, smul_smul]
  rw [AbVar.hodge, mem_hodgeClassesX_iff]
  refine ⟨?_, ?_⟩
  · have h2 : ∀ x y : H1 ℚ (1 + 1), ExteriorAlgebra.ι ℚ x * ExteriorAlgebra.ι ℚ y ∈
        ⋀[ℚ]^(2 * 1) (H1 ℚ (1 + 1)) :=
      fun x y => main_mul_mem (i := 1) (j := 1) (main_lef_ι_mem_one x) (main_lef_ι_mem_one y)
    exact Submodule.sub_mem _ (h2 _ _) (Submodule.smul_mem _ _ (h2 _ _))
  · have h2 := vo_two_bcS_AS ℂ hs
    have hA : bcS ℚ ℂ (2 * 1) (vo_AS d) = (2 : ℂ)⁻¹ • (vo_ωS ℂ (sqrtNeg d) + vo_ωS ℂ (-sqrtNeg d)) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [hA]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
    · refine main_lef_gen_mem_pq11 (2 * 1) (vo_surface hd).J ?_ ?_
      · rw [H10, Module.End.mem_eigenspace_iff, hJ, vo_prodEnd_prodInl, hmem _ _ hs,
          vo_coeff_plus hd, map_smul]
      · rw [H01, Module.End.mem_eigenspace_iff, hJ, vo_prodEnd_prodInr, hmem _ _ hs,
          vo_coeff_minus hd, map_smul]
    · rw [vo_ωS, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
        (prodInl ℂ 1 1 (vo_wE ℂ (-sqrtNeg d))) (prodInr ℂ 1 1 (vo_wE ℂ (-sqrtNeg d))))]
      refine Submodule.neg_mem _ (main_lef_gen_mem_pq11 (2 * 1) (vo_surface hd).J ?_ ?_)
      · rw [H10, Module.End.mem_eigenspace_iff, hJ, vo_prodEnd_prodInr, hmem _ _ hs',
          mul_neg, vo_coeff_minus hd, neg_neg, map_smul]
      · rw [H01, Module.End.mem_eigenspace_iff, hJ, vo_prodEnd_prodInl, hmem _ _ hs',
          mul_neg, vo_coeff_plus hd, map_smul]

theorem vo_ι_swap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x y : M)
    (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R x * (ExteriorAlgebra.ι R y * z) =
      -(ExteriorAlgebra.ι R y * (ExteriorAlgebra.ι R x * z)) := by
  rw [← mul_assoc, ← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y),
    neg_mul]

theorem vo_ι_self {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M)
    (z : ExteriorAlgebra R M) : ExteriorAlgebra.ι R x * (ExteriorAlgebra.ι R x * z) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- `[pt] = a₀ ∧ a₁ ∧ b₀ ∧ b₁` on `E₊ × E₋`. -/
theorem vo_pt_surface : pt ℚ (1 + 1) = vo_a ℚ 0 * (vo_a ℚ 1 * (vo_b ℚ 0 * vo_b ℚ 1)) := by
  rw [vo_pt_eq]
  simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
    Matrix.vecTail, Function.comp_apply, vo_a, vo_b, vo_prodInl_e, vo_prodInr_e]
  rfl

theorem vo_AS_mul_AS : vo_AS d * vo_AS d = (2 * d) • pt ℚ (1 + 1) := by
  rw [vo_pt_surface, vo_AS]
  simp only [vo_a, vo_b] 
  set a₀ := prodInl ℚ 1 1 (e ℚ 1 0)
  set a₁ := prodInl ℚ 1 1 (e ℚ 1 1)
  set b₀ := prodInr ℚ 1 1 (e ℚ 1 0)
  set b₁ := prodInr ℚ 1 1 (e ℚ 1 1)
  have hYY : ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁ *
      (ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁) = 0 := by
    rw [mul_assoc, vo_ι_swap b₁ a₁, mul_neg, vo_ι_self, neg_zero]
  have hXX : ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀ *
      (ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀) = 0 := by
    rw [mul_assoc, vo_ι_swap b₀ a₀, mul_neg, vo_ι_self, neg_zero]
  have hXY : ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀ *
      (ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁) =
      -(ExteriorAlgebra.ι ℚ a₀ * (ExteriorAlgebra.ι ℚ a₁ *
        (ExteriorAlgebra.ι ℚ b₀ * ExteriorAlgebra.ι ℚ b₁))) := by
    rw [mul_assoc, vo_ι_swap b₀ a₁, mul_neg]
  have hYX : ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁ *
      (ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀) =
      -(ExteriorAlgebra.ι ℚ a₀ * (ExteriorAlgebra.ι ℚ a₁ *
        (ExteriorAlgebra.ι ℚ b₀ * ExteriorAlgebra.ι ℚ b₁))) := by
    rw [mul_assoc, vo_ι_swap b₁ a₀, mul_neg, vo_ι_swap a₁ a₀, neg_neg,
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b₁ b₀), mul_neg, mul_neg]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hYY, hXX, hXY, hYX, smul_zero,
    sub_zero, zero_sub, smul_neg]
  module

theorem vo_AS_mul_BS : vo_AS d * vo_BS = 0 := by
  rw [vo_AS, vo_BS]
  simp only [vo_a, vo_b]
  set a₀ := prodInl ℚ 1 1 (e ℚ 1 0)
  set a₁ := prodInl ℚ 1 1 (e ℚ 1 1)
  set b₀ := prodInr ℚ 1 1 (e ℚ 1 0)
  set b₁ := prodInr ℚ 1 1 (e ℚ 1 1)
  have h1 : ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁ *
      (ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₁) = 0 := by
    rw [mul_assoc, vo_ι_swap b₁ a₀, mul_neg, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero,
      neg_zero]
  have h2 : ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₁ *
      (ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₀) = 0 := by
    rw [mul_assoc, vo_ι_swap b₁ a₁, mul_neg, vo_ι_self, neg_zero]
  have h3 : ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀ *
      (ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₁) = 0 := by
    rw [mul_assoc, vo_ι_swap b₀ a₀, mul_neg, vo_ι_self, neg_zero]
  have h4 : ExteriorAlgebra.ι ℚ a₀ * ExteriorAlgebra.ι ℚ b₀ *
      (ExteriorAlgebra.ι ℚ a₁ * ExteriorAlgebra.ι ℚ b₀) = 0 := by
    rw [mul_assoc, vo_ι_swap b₀ a₁, mul_neg, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero,
      neg_zero]
  simp only [sub_mul, mul_add, smul_mul_assoc, h1, h2, h3, h4, add_zero, smul_zero, sub_zero]

theorem vo_integral_AS_mul_AS : integral ℚ (1 + 1) (vo_AS d * vo_AS d) = 2 * d := by
  rw [vo_AS_mul_AS, map_smul, vo_integral_pt, smul_eq_mul, mul_one]

end SurfaceClasses

/-! ### Step 3: the sixfold `A₁ × A₂` of discriminant `-1` -/

section Sixfold

variable {d : ℚ}

/-- The sixfold `A₁ × A₂`, for the Weil surface `A₁ = E₊ × E₋` and an abelian fourfold `A₂`. -/
noncomputable def vo_A6 (hd : 0 < d) (A₂ : AbVar (2 * 2)) : AbVar (2 * 3) := (vo_surface hd).prod A₂

theorem vo_A6_J (hd : 0 < d) (A₂ : AbVar (2 * 2)) :
    (vo_A6 hd A₂).J = prodJ (vo_surface hd).J A₂.J := rfl

/-- **Step 3.** For the Weil surface `A₁ = E₊ × E₋` of `vo_XS` and a polarized abelian fourfold `X₂`
of Weil type, `A₁ × A₂` with `η = η₁ × η₂` and `h = pr₁^*h₁ + pr₂^*h₂` is a polarized abelian sixfold
of Weil type. -/
noncomputable def vo_X6 (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) {A₂ : AbVar (2 * 2)}
    (X₂ : PolarizedWeilType A₂ d) : PolarizedWeilType (vo_A6 hd A₂) d where
  η := vo_prodη (g₁ := 2 * 1) (g₂ := 2 * 2) (vo_XS hd hδ).η X₂.η
  isHodge k := vo_isHodgeMap_prodEnd ((vo_XS hd hδ).isHodge k) (X₂.isHodge k)
  weil₁ := (vo_finrank_weil_prod (vo_XS hd hδ).η X₂.η (vo_surface hd).J A₂.J _).trans (by
    rw [(vo_XS hd hδ).weil₁, X₂.weil₁])
  weil₂ := (vo_finrank_weil_prod (vo_XS hd hδ).η X₂.η (vo_surface hd).J A₂.J _).trans (by
    rw [(vo_XS hd hδ).weil₂, X₂.weil₂])
  h := ExteriorAlgebra.map (prodInl ℚ (2 * 1) (2 * 2)) (vo_XS hd hδ).h +
    ExteriorAlgebra.map (prodInr ℚ (2 * 1) (2 * 2)) X₂.h
  ample := vo_isAmple_prod (vo_surface hd).isComplex A₂.isComplex (vo_XS hd hδ).ample X₂.ample
  norm := vo_norm_prod _ _ (vo_XS hd hδ).norm X₂.norm

/-- **The discriminant of `A₁ × A₂` is `-1`** when `A₂` has Gram determinant `δ` in a `K`-basis
`b₂`: in the `K`-basis `(f₀ ∘ pr₁, f₀ ∘ pr₂, b₂)` the Gram matrix is `diag(d, -dδ) ⊕ G₂`, of
determinant `-d²δ · δ = -Nm(dδ)`. -/
theorem vo_X6_discIs (hd : 0 < d) {δ : ℚ} (hδ : 0 < δ) {A₂ : AbVar (2 * 2)}
    (X₂ : PolarizedWeilType A₂ d) (b₂ : Fin (2 * 2) → Module.Dual ℚ (H1 ℚ (2 * 2)))
    (hb₂ : LinearIndependent ℚ (Sum.elim b₂ fun i => X₂.fT (b₂ i)))
    (hdet : (Matrix.of fun i j => X₂.herm (b₂ i) (b₂ j)).det = (δ : ℂ)) :
    (vo_X6 hd hδ X₂).DiscIs (-1) := by
  refine ⟨vo_prodBasis (g₁ := 2 * 1) vo_bS b₂, vo_linIndep_prodBasis _ _ _ _
    (vo_linIndep_surface hd hδ) hb₂, algebraMap ℚ (Kd d) (d * δ), ?_, ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective]
    exact mul_ne_zero hd.ne' hδ.ne'
  · have h := vo_det_gram_prod (d := d) (g₁ := 2 * 1) (vo_XS hd hδ).h X₂.h
      ((vo_XS hd hδ).η (Kd.sqrtNeg d)) (X₂.η (Kd.sqrtNeg d)) vo_bS b₂
    refine h.trans ?_
    have h1 := vo_det_gram_surface hd hδ
    simp only [← vo_herm_eq] at h1 ⊢
    rw [h1, hdet, vo_Nm_algebraMap hd]
    push_cast
    ring

end Sixfold

/-! ### Step 4: a Hodge–Weil class of `A₁ × A₂` -/

section Kunneth

variable {d : ℚ}

/-- `map φ` acts on `⋀^k U` by `c^k` if `φ` acts on `U` by `c`. -/
theorem vo_map_topWedge {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (φ : M →ₗ[K] M) {U : Submodule K M} {c : K} (hφ : ∀ v ∈ U, φ v = c • v) {k : ℕ}
    {x : ExteriorAlgebra K M} (hx : x ∈ topWedge U k) : ExteriorAlgebra.map φ x = c ^ k • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    have : φ ∘ v = fun i => c • v i := funext fun i => hφ _ (hv i)
    rw [this, main_lef_ιMulti_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul a y _ hy => rw [map_smul, hy, smul_comm]

/-- `pr₁^*x ∪ pr₂^*y ∈ H*(A₁ × A₂)`. -/
noncomputable def vo_kun {F : Type*} [Field F] {g₁ g₂ : ℕ} (x : S F g₁) (y : S F g₂) :
    S F (g₁ + g₂) :=
  ExteriorAlgebra.map (prodInl F g₁ g₂) x * ExteriorAlgebra.map (prodInr F g₁ g₂) y

/-- **Künneth**: `pr₁^*(⋀^{k₁}U₁) ∧ pr₂^*(⋀^{k₂}U₂) ⊆ ⋀^{k₁+k₂}U` if `U ⊇ U₁ ⊕ U₂`. -/
theorem vo_topWedge_prod {K : Type*} [Field K] {g₁ g₂ k₁ k₂ : ℕ} {U₁ : Submodule K (H1 K g₁)}
    {U₂ : Submodule K (H1 K g₂)} {U : Submodule K (H1 K (g₁ + g₂))}
    (h₁ : ∀ v ∈ U₁, prodInl K g₁ g₂ v ∈ U) (h₂ : ∀ v ∈ U₂, prodInr K g₁ g₂ v ∈ U)
    {x : S K g₁} (hx : x ∈ topWedge U₁ k₁) {y : S K g₂} (hy : y ∈ topWedge U₂ k₂) :
    vo_kun x y ∈ topWedge U (k₁ + k₂) := by
  rw [vo_kun]
  induction hx using Submodule.span_induction with
  | mem x' hx' =>
    obtain ⟨v, hv, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨v', hv', rfl⟩ := hy'
      rw [ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
        ExteriorAlgebra.ιMulti_mul_ιMulti]
      refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact h₁ _ (hv j)
      · rw [Fin.append_right]; exact h₂ _ (hv' j)
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      simp only [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => simp only [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c ha

theorem vo_prodEnd_eig_inl {K : Type*} [Field K] {g₁ g₂ : ℕ} (φ₁ : Module.End K (H1 K g₁))
    (φ₂ : Module.End K (H1 K g₂)) (μ : K) :
    ∀ v ∈ Module.End.eigenspace φ₁ μ,
      prodInl K g₁ g₂ v ∈ Module.End.eigenspace (vo_prodEnd φ₁ φ₂) μ := fun v hv => by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [vo_prodEnd_prodInl, hv, map_smul]

theorem vo_prodEnd_eig_inr {K : Type*} [Field K] {g₁ g₂ : ℕ} (φ₁ : Module.End K (H1 K g₁))
    (φ₂ : Module.End K (H1 K g₂)) (μ : K) :
    ∀ v ∈ Module.End.eigenspace φ₂ μ,
      prodInr K g₁ g₂ v ∈ Module.End.eigenspace (vo_prodEnd φ₁ φ₂) μ := fun v hv => by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [vo_prodEnd_prodInr, hv, map_smul]

/-- `v₂ = t⁻¹(ψ^*w₂ - r w₂)` for `ψ = 1 + 2 η(√-d) = η(1 + 2√-d)`, `r = 1 - 24 d + 16 d²`,
`t = 8 (1 - 4 d)`: if `w₂ = ω + ω̄` over `K` (`ω ∈ ⋀⁴W`, `ω̄ ∈ ⋀⁴W̄`), then `v₂ = √-d (ω - ω̄)`,
since `(1 ± 2√-d)⁴ = r ± t √-d`. -/
noncomputable def vo_v2 {m : ℕ} {A : AbVar (2 * m)} (X : WeilType A d) (w : S ℚ (2 * m)) :
    S ℚ (2 * m) :=
  (8 * (1 - 4 * d))⁻¹ • (ExteriorAlgebra.map (1 + (2 : ℚ) • X.η (Kd.sqrtNeg d)) w -
    (1 - 24 * d + 16 * d ^ 2) • w)

theorem vo_bcS_v2 (hd : 0 < d) (hd4 : 1 - 4 * d ≠ 0) {A : AbVar (2 * 2)} (X : WeilType A d)
    {w : S ℚ (2 * 2)} {ω ω' : S (Kd d) (2 * 2)} (hω : ω ∈ topWedge X.W (2 * 2))
    (hω' : ω' ∈ topWedge X.Wbar (2 * 2)) (hw : bcS ℚ (Kd d) (2 * 2) w = ω + ω') :
    bcS ℚ (Kd d) (2 * 2) (vo_v2 X w) = Kd.sqrtNeg d • (ω - ω') := by
  set s := Kd.sqrtNeg d
  have hs : s * s = -algebraMap ℚ (Kd d) d := by
    rw [s24b_sqrtNeg_mul_self hd.le, map_neg]
  have hψ : bcMap ℚ (Kd d) (1 + (2 : ℚ) • X.η s) =
      1 + algebraMap ℚ (Kd d) 2 • bcMap ℚ (Kd d) (X.η s) := by
    rw [vo_bcMap_add, main_bcMap_smul, show (1 : Module.End ℚ (H1 ℚ (2 * 2))) = LinearMap.id from
      rfl, main_bcMap_id]
    rfl
  have hW : ∀ v ∈ X.W, bcMap ℚ (Kd d) (1 + (2 : ℚ) • X.η s) v = (1 + 2 * s) • v := by
    intro v hv
    rw [WeilType.W, Module.End.mem_eigenspace_iff] at hv
    rw [hψ, LinearMap.add_apply, LinearMap.smul_apply, hv, Module.End.one_apply, smul_smul,
      add_smul, one_smul, map_ofNat]
  have hW' : ∀ v ∈ X.Wbar, bcMap ℚ (Kd d) (1 + (2 : ℚ) • X.η s) v = (1 - 2 * s) • v := by
    intro v hv
    rw [WeilType.Wbar, Module.End.mem_eigenspace_iff] at hv
    rw [hψ, LinearMap.add_apply, LinearMap.smul_apply, hv, Module.End.one_apply, smul_smul,
      sub_smul, one_smul, map_ofNat, mul_neg, neg_smul, sub_eq_add_neg]
  have hk₁ : (1 + 2 * s) ^ (2 * 2) = algebraMap ℚ (Kd d) (1 - 24 * d + 16 * d ^ 2) +
      algebraMap ℚ (Kd d) (8 * (1 - 4 * d)) * s := by
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    linear_combination (24 + 32 * s + 16 * s ^ 2 - 16 * algebraMap ℚ (Kd d) d) * hs
  have hk₂ : (1 - 2 * s) ^ (2 * 2) = algebraMap ℚ (Kd d) (1 - 24 * d + 16 * d ^ 2) -
      algebraMap ℚ (Kd d) (8 * (1 - 4 * d)) * s := by
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    linear_combination (24 - 32 * s + 16 * s ^ 2 - 16 * algebraMap ℚ (Kd d) d) * hs
  have ht : algebraMap ℚ (Kd d) (8 * (1 - 4 * d)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective]
    exact mul_ne_zero (by norm_num) hd4
  rw [vo_v2, map_smul, map_sub, map_smul, main_bcS_map, hw, map_add,
    vo_map_topWedge _ hW hω, vo_map_topWedge _ hW' hω', hk₁, hk₂, ← algebraMap_smul (Kd d),
    ← algebraMap_smul (Kd d) (1 - 24 * d + 16 * d ^ 2)]
  set t := algebraMap ℚ (Kd d) (8 * (1 - 4 * d))
  rw [map_inv₀]
  set r := algebraMap ℚ (Kd d) (1 - 24 * d + 16 * d ^ 2)
  have : (r + t * s) • ω + (r - t * s) • ω' - r • (ω + ω') = t • (s • (ω - ω')) := by module
  rw [this, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- **The Künneth class** `w = pr₁^*A ∪ pr₂^*w₂ + pr₁^*B ∪ pr₂^*v₂` on `A₁ × A₂`. -/
noncomputable def vo_w {A : AbVar (2 * 2)} (X : WeilType A d) (w : S ℚ (2 * 2)) :
    S ℚ (2 * 1 + 2 * 2) :=
  vo_kun (g₁ := 2 * 1) (vo_AS d) w + vo_kun (g₁ := 2 * 1) vo_BS (vo_v2 X w)

/-- Over `K`, `w = pr₁^*ω₁ ∪ pr₂^*ω + pr₁^*ω̄₁ ∪ pr₂^*ω̄` when `w₂ = ω + ω̄`. -/
theorem vo_bcS_w (hd : 0 < d) (hd4 : 1 - 4 * d ≠ 0) {A₂ : AbVar (2 * 2)} (X₂ : WeilType A₂ d)
    {w : S ℚ (2 * 2)} {ω ω' : S (Kd d) (2 * 2)} (hω : ω ∈ topWedge X₂.W (2 * 2))
    (hω' : ω' ∈ topWedge X₂.Wbar (2 * 2)) (hw : bcS ℚ (Kd d) (2 * 2) w = ω + ω') :
    bcS ℚ (Kd d) (2 * 1 + 2 * 2) (vo_w X₂ w) =
      vo_kun (g₁ := 2 * 1) (vo_ωS (Kd d) (Kd.sqrtNeg d)) ω +
        vo_kun (g₁ := 2 * 1) (vo_ωS (Kd d) (-Kd.sqrtNeg d)) ω' := by
  have hs : Kd.sqrtNeg d * Kd.sqrtNeg d = -algebraMap ℚ (Kd d) d := by
    rw [s24b_sqrtNeg_mul_self hd.le, map_neg]
  have hv2 := vo_bcS_v2 hd hd4 X₂ hω hω' hw
  have hA := vo_two_bcS_AS (Kd d) hs
  have hB := vo_two_bcS_BS (Kd d) (Kd.sqrtNeg d)
  have hbcS : ∀ (x : S ℚ (2 * 1)) (y : S ℚ (2 * 2)), bcS ℚ (Kd d) (2 * 1 + 2 * 2) (vo_kun x y) =
      vo_kun (bcS ℚ (Kd d) (2 * 1) x) (bcS ℚ (Kd d) (2 * 2) y) := by
    intro x y
    rw [vo_kun, vo_kun, map_mul, main_bcS_map, main_bcS_map, vo_bcMap_prodInl, vo_bcMap_prodInr]
  have hlin₁ : ∀ (c : Kd d) (x : S (Kd d) (2 * 1)) (y : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) (c • x) y = c • vo_kun x y := by
    intro c x y; rw [vo_kun, vo_kun, map_smul, smul_mul_assoc]
  have hlin₂ : ∀ (c : Kd d) (x : S (Kd d) (2 * 1)) (y : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) x (c • y) = c • vo_kun x y := by
    intro c x y; rw [vo_kun, vo_kun, map_smul, mul_smul_comm]
  have hadd₁ : ∀ (x x' : S (Kd d) (2 * 1)) (y : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) (x + x') y = vo_kun x y + vo_kun x' y := by
    intro x x' y; rw [vo_kun, vo_kun, vo_kun, map_add, add_mul]
  have hadd₂ : ∀ (x : S (Kd d) (2 * 1)) (y y' : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) x (y + y') = vo_kun x y + vo_kun x y' := by
    intro x y y'; rw [vo_kun, vo_kun, vo_kun, map_add, mul_add]
  have hsub₁ : ∀ (x x' : S (Kd d) (2 * 1)) (y : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) (x - x') y = vo_kun x y - vo_kun x' y := by
    intro x x' y; rw [vo_kun, vo_kun, vo_kun, map_sub, sub_mul]
  have hsub₂ : ∀ (x : S (Kd d) (2 * 1)) (y y' : S (Kd d) (2 * 2)),
      vo_kun (F := Kd d) (g₁ := 2 * 1) (g₂ := 2 * 2) x (y - y') = vo_kun x y - vo_kun x y' := by
    intro x y y'; rw [vo_kun, vo_kun, vo_kun, map_sub, mul_sub]
  have e1 : bcS ℚ (Kd d) (2 * 1) (vo_AS d) = (2 : Kd d)⁻¹ •
      (vo_ωS (Kd d) (Kd.sqrtNeg d) + vo_ωS (Kd d) (-Kd.sqrtNeg d)) := by
    rw [← hA, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have e2 : Kd.sqrtNeg d • bcS ℚ (Kd d) (2 * 1) vo_BS = (2 : Kd d)⁻¹ •
      (vo_ωS (Kd d) (Kd.sqrtNeg d) - vo_ωS (Kd d) (-Kd.sqrtNeg d)) := by
    rw [← hB, smul_smul, ← mul_assoc (2 : Kd d)⁻¹ 2 (Kd.sqrtNeg d), inv_mul_cancel₀ two_ne_zero,
      one_mul]
  rw [vo_w, map_add, hbcS, hbcS, hw, hv2, hlin₂, ← hlin₁, e1, e2]
  simp only [hlin₁, hadd₁, hadd₂, hsub₁, hsub₂]
  module

/-- **Step 4.** The Künneth class `w` is a Hodge–Weil class of `A₁ × A₂`: over `K` it is
`pr₁^*ω₁ ∪ pr₂^*ω + pr₁^*ω̄₁ ∪ pr₂^*ω̄ ∈ ⋀⁶W ⊕ ⋀⁶W̄`. (The product `pr₁^*w₁ ∪ pr₂^*w₂` of two
Hodge–Weil classes is not one: its components `ω₁ ∧ ω̄` and `ω̄₁ ∧ ω` lie in `⋀²W ∧ ⋀⁴W̄` and
`⋀²W̄ ∧ ⋀⁴W`.) -/
theorem vo_w_mem_HW (hd : 0 < d) (hd4 : 1 - 4 * d ≠ 0) {δ : ℚ} (hδ : 0 < δ) {A₂ : AbVar (2 * 2)}
    (X₂ : PolarizedWeilType A₂ d) {w : S ℚ (2 * 2)} (hw : w ∈ X₂.HW) :
    vo_w X₂.toWeilType w ∈ (vo_X6 hd hδ X₂).HW := by
  obtain ⟨hw4, hwK⟩ := (WeilType.mem_HW_iff _ _).mp hw
  obtain ⟨ω, hω, ω', hω', hωω⟩ := Submodule.mem_sup.mp hwK
  have hs : Kd.sqrtNeg d * Kd.sqrtNeg d = -algebraMap ℚ (Kd d) d := by
    rw [s24b_sqrtNeg_mul_self hd.le, map_neg]
  have hs' : (-Kd.sqrtNeg d) * (-Kd.sqrtNeg d) = -algebraMap ℚ (Kd d) d := by
    rw [neg_mul_neg, hs]
  rw [WeilType.mem_HW_iff]
  constructor
  · have hA2 : vo_AS d ∈ ⋀[ℚ]^2 (H1 ℚ (2 * 1)) := (vo_AS_hodge hd).1
    have hB2 : vo_BS ∈ ⋀[ℚ]^2 (H1 ℚ (2 * 1)) := by
      have h2 : ∀ x y : H1 ℚ (1 + 1), ExteriorAlgebra.ι ℚ x * ExteriorAlgebra.ι ℚ y ∈
          ⋀[ℚ]^2 (H1 ℚ (1 + 1)) :=
        fun x y => main_mul_mem (i := 1) (j := 1) (main_lef_ι_mem_one x) (main_lef_ι_mem_one y)
      exact Submodule.add_mem _ (h2 _ _) (h2 _ _)
    have hv4 : vo_v2 X₂.toWeilType w ∈ ⋀[ℚ]^(2 * 2) (H1 ℚ (2 * 2)) :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (main_map_mem_exteriorPower _ _ hw4)
        (Submodule.smul_mem _ _ hw4))
    exact Submodule.add_mem _
      (main_mul_mem (i := 2) (j := 2 * 2) (main_map_mem_exteriorPower _ 2 hA2)
        (main_map_mem_exteriorPower _ _ hw4))
      (main_mul_mem (i := 2) (j := 2 * 2) (main_map_mem_exteriorPower _ 2 hB2)
        (main_map_mem_exteriorPower _ _ hv4))
  · have hW : ∀ μ : Kd d, ∀ v ∈ Module.End.eigenspace
        (bcMap ℚ (Kd d) ((vo_XS hd hδ).η (Kd.sqrtNeg d))) μ,
        prodInl (Kd d) (2 * 1) (2 * 2) v ∈ Module.End.eigenspace
          (bcMap ℚ (Kd d) ((vo_X6 hd hδ X₂).η (Kd.sqrtNeg d))) μ := fun μ => by
      show ∀ v ∈ _, _ ∈ Module.End.eigenspace (bcMap ℚ (Kd d)
        (vo_prodEnd ((vo_XS hd hδ).η (Kd.sqrtNeg d)) (X₂.η (Kd.sqrtNeg d)))) μ
      rw [vo_bcMap_prodEnd]
      exact vo_prodEnd_eig_inl _ _ _
    have hW₂ : ∀ μ : Kd d, ∀ v ∈ Module.End.eigenspace
        (bcMap ℚ (Kd d) (X₂.η (Kd.sqrtNeg d))) μ,
        prodInr (Kd d) (2 * 1) (2 * 2) v ∈ Module.End.eigenspace
          (bcMap ℚ (Kd d) ((vo_X6 hd hδ X₂).η (Kd.sqrtNeg d))) μ := fun μ => by
      show ∀ v ∈ _, _ ∈ Module.End.eigenspace (bcMap ℚ (Kd d)
        (vo_prodEnd ((vo_XS hd hδ).η (Kd.sqrtNeg d)) (X₂.η (Kd.sqrtNeg d)))) μ
      rw [vo_bcMap_prodEnd]
      exact vo_prodEnd_eig_inr _ _ _
    have key : bcS ℚ (Kd d) (2 * 1 + 2 * 2) (vo_w X₂.toWeilType w) ∈
        topWedge (vo_X6 hd hδ X₂).W (2 * 1 + 2 * 2) ⊔
          topWedge (vo_X6 hd hδ X₂).Wbar (2 * 1 + 2 * 2) := by
      rw [vo_bcS_w hd hd4 X₂.toWeilType hω hω' hωω.symm]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · exact vo_topWedge_prod (k₁ := 2 * 1) (k₂ := 2 * 2) (hW _) (hW₂ _)
          (vo_ωS_mem hd (Kd d) hs) hω
      · exact vo_topWedge_prod (k₁ := 2 * 1) (k₂ := 2 * 2) (hW _) (hW₂ _)
          (vo_ωS_mem hd (Kd d) hs') hω'
    exact key

/-- **Steps 5–6.** `pr₂,*(pr₁^*A ∪ w) = (∫ A²) w₂ = 2d w₂`, since `AB = 0`. -/
theorem vo_pushSnd_w {A : AbVar (2 * 2)} (X : WeilType A d) (w : S ℚ (2 * 2)) :
    pushSnd ℚ (2 * 1) (2 * 2) (ExteriorAlgebra.map (prodInl ℚ (2 * 1) (2 * 2)) (vo_AS d) *
      vo_w X w) = (2 * d) • w := by
  have h1 : ExteriorAlgebra.map (prodInl ℚ (2 * 1) (2 * 2)) (vo_AS d) * vo_w X w =
      vo_kun (g₁ := 2 * 1) (vo_AS d * vo_AS d) w := by
    simp only [vo_w, vo_kun, mul_add, ← mul_assoc, ← map_mul, vo_AS_mul_BS, map_zero, zero_mul,
      add_zero]
  rw [h1, vo_kun, pushSnd_prodInl_mul_prodInr]
  congr 1
  exact vo_integral_AS_mul_AS

end Kunneth

/-! ### Steps 5–6: [Schoen, Prop. 10] -/

/-- **[Schoen, Prop. 10]**: if the Hodge–Weil classes of all polarized abelian sixfolds of Weil type
for `K` with discriminant `-1` are algebraic, so are those of all abelian fourfolds of Weil type for
`K`. -/
class SchoenDegeneration (Z : CycleClasses) : Prop where
  imp : ∀ d : ℕ, 0 < d →
    (∀ (A : AbVar (2 * 3)) (X : PolarizedWeilType A d), X.DiscIs (-1) → X.HW ≤ Z.alg (2 * 3) A.J) →
    ∀ (A : AbVar (2 * 2)) (X : WeilType A d), X.HW ≤ Z.alg (2 * 2) A.J

/-- **[Schoen, Prop. 10]**, in the form used in Corollary 1.6.1 (`SchoenDegeneration`), proved from
`PullbackClosed`, `SubalgebraClosed`, `LefschetzOneOne` and push-forward along a projection
(`PushforwardClosed`).

Departure from the source (reason 2): Schoen proves the statement by degenerating abelian varieties,
which the model does not have. The proof is C. Voisin's argument (Séminaire Bourbaki 1248,
Lemme 2.9 and Corollaire 2.10): the Hodge–Weil classes of a fourfold `A₂` are push-forwards
`pr₂,*(pr₁^*A ∪ w)` of Hodge–Weil classes `w` of `A₁ × A₂`, for a Weil surface `A₁` of suitable
discriminant (see the module docstring). -/
theorem schoenDegeneration_of_pushforward (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [PushforwardClosed Z] : SchoenDegeneration Z := by
  refine ⟨fun d hd H6 A₂ X₂ w₂ hw₂ => ?_⟩
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hd4 : 1 - 4 * (d : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  -- Step 1: a compatible polarization of `A₂`, and a `K`-basis with Gram determinant `δ > 0`
  obtain ⟨b₂, hb₂, δ, hδ, hdet⟩ := vo_disc_pos hd' (vo_polarize hd' X₂)
  -- Steps 2–3: `A₁ × A₂`, `A₁` the Weil surface of discriminant `-δ`, has discriminant `-1`
  have hdisc := vo_X6_discIs hd' hδ (vo_polarize hd' X₂) b₂ hb₂ hdet
  -- Step 4: the Künneth class `w` is a Hodge–Weil class of `A₁ × A₂`
  have hw : vo_w X₂ w₂ ∈ (vo_X6 hd' hδ (vo_polarize hd' X₂)).HW :=
    vo_w_mem_HW hd' hd4 hδ (vo_polarize hd' X₂) (by rwa [vo_polarize_HW])
  -- Step 5: `w` is algebraic (the sixfold statement), and so is `pr₁^*A` (`A` is of type `(1,1)`)
  have hwalg := H6 _ (vo_X6 hd' hδ (vo_polarize hd' X₂)) hdisc hw
  have hA : vo_AS (d : ℚ) ∈ Z.alg (2 * 1) (vo_surface hd').J :=
    LefschetzOneOne.le (vo_surface hd') (vo_AS_hodge hd')
  have hAP := PullbackClosed.map_mem (vo_surface hd') (vo_A6 hd' A₂) (prodInl ℚ (2 * 1) (2 * 2))
    (vo_isHodgeMap_prodInl _ _) _ hA
  have hprod := SubalgebraClosed.mul_mem (vo_A6 hd' A₂) _ _ hAP hwalg
  -- Step 6: `pr₂,*(pr₁^*A ∪ w) = 2d w₂` is algebraic
  have hpush := PushforwardClosed.mem (vo_surface hd') A₂ _ hprod
  rw [vo_pushSnd_w] at hpush
  have h2d : (2 * (d : ℚ)) ≠ 0 := mul_ne_zero two_ne_zero hd'.ne'
  have := Submodule.smul_mem _ (2 * (d : ℚ))⁻¹ hpush
  rwa [smul_smul, inv_mul_cancel₀ h2d, one_smul] at this

end WeilClasses
