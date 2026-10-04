module

public import WeilClasses.Igusa.Secant
public import WeilClasses.PureSpinor.Lemma2_2_4
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection

/-!
# Complex multiplication from a rational class with positive Igusa invariant (paper §10.2)

Here `X` is an abelian threefold (`n = 3`). For `w ∈ S⁺_ℚ` the Igusa invariant `d := J(w)` is
rational (`J` is defined over `ℚ`, `J_bcS`); when `d > 0` we set `K := ℚ(√-d)` (`Kd (J ℚ w)`, with
the paper's `√-d = i√d`); `-d` is then not a rational square.

* **Lemma 10.2.1**: the two maximal isotropic subspaces of `V_ℂ` invariant under `Spin(V_ℚ)_w` are
  defined over `K`, not over `ℚ`, and exchanged by `σ` (`lemma10_2_1`); the centralizer of
  `ρ(Spin(V_ℚ)_w)` in `Õ(V_ℚ)` (2.2.3) is isomorphic to `K^×` (`lemma10_2_1_centralizer`).
  Claims of its proof: the secant through `w` is a rational `K`-secant with `V_K = W₁ ⊕ W₂`
  (`lemma10_2_1_secant`) and `Spin(V_ℚ)_w = Spin(V_ℚ)_P` (`lemma10_2_1_spinStab_eq`, from
  Remark 2.2.3, `n = 3` odd). The text after the lemma: the image of `η : K^× → GL(V_ℚ)` (2.2.4) is
  the centralizer (`eta_centralizer_spinStab`).
* **Example 10.2.2** (`example-gulbrandsen`): `J(2 - dΘ²) = 16d³`, so `K = ℚ(√-d)`, for
  `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` as printed; this `Θ` has `Θ³ = -6[pt_X]`, so it is not a
  principal polarization in the orientation `∫_X e₁ ∧ ⋯ ∧ e₆ = 1` of §10.1 (slip of the paper); the
  value is the same for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, `Θ'³ = 6[pt_X]`
  (`example10_2_2_principal`), and `2 - dΘ'² = 2α` for the class `α = 1 - (d/2)Θ'²` of
  Lemma 8.2.1.
* **Example 10.2.3**: `J(1 - m[pt_X]) = -m²/4 = -(m/2)²` (`m` the length of a zero-dimensional
  subscheme), so `-J` is a rational square and `K = ℚ`.

The sheaf-theoretic content of the examples (Gulbrandsen's moduli spaces, Chern characters of
vector bundles and ideal sheaves) is not formalized; only the cohomological identities are.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prefix `s10_`): the field `K = ℚ(√-d)`, rational points, descent of purity -/

section S10Field

variable {d : ℚ}

theorem s10_σ_sqrtNeg (d : ℚ) : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp [Kd.sqrtNeg, WeilClasses.sqrtNeg]

theorem s10_σ_σ (z : Kd d) : Kd.σ d (Kd.σ d z) = z := by
  apply Subtype.ext
  simp

theorem s10_σ_algebraMap (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp

theorem s10_sqrtNeg_ne_zero (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := congrArg (fun z : Kd d => (z : ℂ)) h
  simp only [Kd.sqrtNeg, WeilClasses.sqrtNeg, ZeroMemClass.coe_zero, mul_eq_zero,
    Complex.I_ne_zero, Complex.ofReal_eq_zero, false_or] at this
  have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  linarith

theorem s10_sqrtNeg_sq (hd : 0 < d) : Kd.sqrtNeg d ^ 2 = -algebraMap ℚ (Kd d) d := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, show ((Kd.sqrtNeg d : Kd d) : ℂ) = WeilClasses.sqrtNeg d from rfl,
    sqrtNeg_sq hd.le]
  simp

/-- A `σ`-fixed element of `K` is rational. -/
theorem s10_eq_algebraMap_of_σ (hd : 0 < d) {z : Kd d} (h : Kd.σ d z = z) :
    z = algebraMap ℚ (Kd d) (Kd.ratPart d z) := by
  have hz := Kd.eq_ratPart_add_sqrtNegCoeff hd z
  set a := Kd.ratPart d z
  set b := Kd.sqrtNegCoeff d z
  have h2 : Kd.σ d z = algebraMap ℚ (Kd d) a - algebraMap ℚ (Kd d) b * Kd.sqrtNeg d := by
    conv_lhs => rw [hz]
    rw [map_add, map_mul, s10_σ_algebraMap, s10_σ_algebraMap, s10_σ_sqrtNeg]
    ring
  have h3 : (2 : Kd d) * algebraMap ℚ (Kd d) b * Kd.sqrtNeg d = 0 := by
    have : z - Kd.σ d z = 0 := by rw [h, sub_self]
    rw [h2] at this
    conv_lhs at this => rw [hz]
    linear_combination this
  have hb : algebraMap ℚ (Kd d) b = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 two_ne_zero
      · exact h5
    · exact absurd h4 (s10_sqrtNeg_ne_zero hd)
  rw [hz, hb, zero_mul, add_zero]

theorem s10_algebraMap_injective : Function.Injective (algebraMap ℚ (Kd d)) :=
  (algebraMap ℚ (Kd d)).injective

/-- A `σ`-fixed spinor of `S_K` is rational. -/
theorem s10_rat_of_σS (hd : 0 < d) (x : S (Kd d) 3) (h : σS 3 d x = x) :
    ∃ r : S ℚ 3, bcS ℚ (Kd d) 3 r = x := by
  refine ⟨∑ K, Kd.ratPart d ((basisS (Kd d) 3).repr x K) • basisS ℚ 3 K, ?_⟩
  apply s10_S_ext
  intro K
  rw [s10_repr_bcS]
  have hK : Kd.σ d ((basisS (Kd d) 3).repr x K) = (basisS (Kd d) 3).repr x K := by
    have := congrArg (fun y => (basisS (Kd d) 3).repr y K) h
    rw [σS, s10_repr_conjS] at this
    exact this
  rw [s10_eq_algebraMap_of_σ hd hK]
  congr 1
  simp [Finsupp.single_apply]

theorem s10_bcV_fst (v : V ℚ 3) (i : Fin 6) :
    (bcV ℚ (Kd d) 3 v).1 (e (Kd d) 3 i) = algebraMap ℚ (Kd d) (v.1 (e ℚ 3 i)) := by
  show (∑ j, algebraMap ℚ (Kd d) (v.1 (e ℚ 3 j)) • f (Kd d) 3 j) (e (Kd d) 3 i) = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp [s10_f_e]
  · intro j _ hj
    simp [s10_f_e, hj]
  · simp

theorem s10_bcV_snd (v : V ℚ 3) (i : Fin 6) :
    (bcV ℚ (Kd d) 3 v).2 i = algebraMap ℚ (Kd d) (v.2 i) := rfl

theorem s10_V_ext {F : Type*} [Field F] [CharZero F] {v w : V F 3}
    (h1 : ∀ i, v.1 (e F 3 i) = w.1 (e F 3 i)) (h2 : ∀ i, v.2 i = w.2 i) : v = w := by
  refine Prod.ext ?_ (funext h2)
  rw [s10_dual_eq_sum v.1, s10_dual_eq_sum w.1]
  simp only [h1]

/-- A `σ`-fixed vector of `V_K` is rational. -/
theorem s10_rat_of_σV (hd : 0 < d) (v : V (Kd d) 3) (h : σV 3 d v = v) :
    ∃ r : V ℚ 3, bcV ℚ (Kd d) 3 r = v := by
  have h1 : ∀ i, Kd.σ d (v.1 (e (Kd d) 3 i)) = v.1 (e (Kd d) 3 i) := by
    intro i
    have := congrArg (fun y : V (Kd d) 3 => y.1 (e (Kd d) 3 i)) h
    simp only [σV, s10_conjV_fst, LinearMap.sum_apply, LinearMap.smul_apply, s10_f_e,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    exact this
  have h2 : ∀ i, Kd.σ d (v.2 i) = v.2 i := by
    intro i
    have := congrArg (fun y : V (Kd d) 3 => y.2 i) h
    simpa [σV, s10_conjV_snd] using this
  refine ⟨(∑ i, Kd.ratPart d (v.1 (e (Kd d) 3 i)) • f ℚ 3 i,
    fun i => Kd.ratPart d (v.2 i)), ?_⟩
  apply s10_V_ext
  · intro i
    rw [s10_bcV_fst]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, s10_f_e, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (s10_eq_algebraMap_of_σ hd (h1 i)).symm
  · intro i
    rw [s10_bcV_snd]
    exact (s10_eq_algebraMap_of_σ hd (h2 i)).symm

theorem s10_σS_smul (c : Kd d) (x : S (Kd d) 3) : σS 3 d (c • x) = Kd.σ d c • σS 3 d x :=
  s10_conjS_smul _ c x

/-- Complex conjugation on `ℂ`, as a ring automorphism. -/
noncomputable abbrev s10_cc : ℂ ≃+* ℂ := starRingAut

theorem s10_cc_bcS (x : S (Kd d) 3) :
    conjS s10_cc 3 (bcS (Kd d) ℂ 3 x) = bcS (Kd d) ℂ 3 (σS 3 d x) := by
  apply s10_S_ext
  intro K
  rw [s10_repr_conjS, s10_repr_bcS, s10_repr_bcS, σS, s10_repr_conjS]
  rfl

end S10Field

section S10Descend

variable {d : ℚ}

theorem s10_pairing_nondeg {F : Type*} [Field F] [CharZero F] (v : V F 3)
    (h : ∀ w, pairing F 3 v w = 0) : v = 0 := by
  apply s10_V_ext
  · intro i
    have := h (0, e F 3 i)
    rw [s10_pairing_apply] at this
    simpa using this
  · intro i
    have := h (f F 3 i, 0)
    rw [s10_pairing_apply] at this
    simpa [f] using this

theorem s10_finrank_V (F : Type*) [Field F] [CharZero F] : Module.finrank F (V F 3) = 12 := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq, s10_finrank_H1]

/-- **Witt's bound**: an isotropic subspace of `V` (`dim V = 12`, nondegenerate) has dimension
`≤ 6`. -/
theorem s10_finrank_isotropic_le {F : Type*} [Field F] [CharZero F] (W : Submodule F (V F 3))
    (hW : ∀ v ∈ W, Q F 3 v = 0) : Module.finrank F W ≤ 6 := by
  have hnd : (pairing F 3).Nondegenerate :=
    ⟨fun v hv => s10_pairing_nondeg v hv, fun v hv => s10_pairing_nondeg v fun w => by
      rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact hv w⟩
  have hle : W ≤ (pairing F 3).orthogonal W := by
    intro v hv w hw
    show pairing F 3 w v = 0
    rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hW _ (W.add_mem hw hv),
      hW _ hw, hW _ hv, sub_zero, sub_zero]
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
  have h2 := Submodule.finrank_mono hle
  rw [h1, s10_finrank_V] at h2
  have h3 : Module.finrank F W ≤ 12 := by
    have := Submodule.finrank_le W
    rwa [s10_finrank_V] at this
  omega

theorem s10_σV_σV (v : V (Kd d) 3) : σV 3 d (σV 3 d v) = v := by
  have := s10_conjV_symm_conjV (Kd.σ d) v
  rwa [show (Kd.σ d).symm = Kd.σ d from RingEquiv.ext fun z => rfl] at this

theorem s10_finrank_span_bcV_le (A : Submodule ℚ (V ℚ 3)) :
    Module.finrank (Kd d) (Submodule.span (Kd d) (bcV ℚ (Kd d) 3 '' A)) ≤ Module.finrank ℚ A := by
  let b := Module.finBasis ℚ A
  have h : Submodule.span (Kd d) (bcV ℚ (Kd d) 3 '' A) =
      Submodule.span (Kd d) (Set.range fun i => bcV ℚ (Kd d) 3 (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      have hsum := b.sum_repr ⟨a, ha⟩
      have ha' : a = ∑ i, (b.repr ⟨a, ha⟩ i) • (b i : V ℚ 3) := by
        have := congrArg (Subtype.val : A → V ℚ 3) hsum
        rw [AddSubmonoidClass.coe_finsetSum] at this
        simp only [SetLike.val_smul] at this
        exact this.symm
      rw [ha', map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul, ← algebraMap_smul (Kd d)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  rw [h]
  exact (finrank_range_le_card _).trans (by simp)

/-- **Descent of purity** from `K` to `ℚ`: a rational spinor which is an even pure spinor over `K`
is an even pure spinor over `ℚ` (its annihilator is `σ`-stable, hence spanned by rational
vectors). -/
theorem s10_pure_descent (hd : 0 < d) {r : S ℚ 3}
    (hr : IsEvenPureSpinor (Kd d) 3 (bcS ℚ (Kd d) 3 r)) : IsEvenPureSpinor ℚ 3 r := by
  set x := bcS ℚ (Kd d) 3 r with hx
  have hmem : ∀ a : V ℚ 3, a ∈ ann ℚ 3 r ↔ bcV ℚ (Kd d) 3 a ∈ ann (Kd d) 3 x := by
    intro a
    rw [ann, ann, LinearMap.mem_ker, LinearMap.mem_ker, s10_mOf_eq, s10_mOf_eq, hx,
      ← s10_bcS_m_ι]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      exact s10_bcS_injective (by rw [h, map_zero])
  have hiso : ∀ a ∈ ann ℚ 3 r, Q ℚ 3 a = 0 := by
    intro a ha
    have := hr.2.1 _ ((hmem a).mp ha)
    rw [Q_bcV] at this
    exact (algebraMap ℚ (Kd d)).injective (by rw [this, map_zero])
  refine ⟨?_, hiso, ?_⟩
  · rw [s10_mem_Splus_iff]
    intro K hK
    have := (s10_mem_Splus_iff x).mp hr.1 K hK
    rw [hx, s10_repr_bcS] at this
    exact (algebraMap ℚ (Kd d)).injective (by rw [this, map_zero])
  · apply le_antisymm (s10_finrank_isotropic_le _ hiso)
    have hσ : ∀ y ∈ ann (Kd d) 3 x, σV 3 d y ∈ ann (Kd d) 3 x := by
      intro y hy
      have h1 := s10_ann_conjS (Kd.σ d) x
      rw [show conjS (Kd.σ d) 3 x = x from s10_conjS_bcS _ r] at h1
      rw [h1]
      exact Submodule.mem_map_of_mem hy
    have hs := s10_sqrtNeg_ne_zero hd
    have hle : ann (Kd d) 3 x ≤ Submodule.span (Kd d) (bcV ℚ (Kd d) 3 '' (ann ℚ 3 r)) := by
      intro y hy
      obtain ⟨a, ha⟩ := s10_rat_of_σV hd (y + σV 3 d y) (by
        rw [map_add, s10_σV_σV, add_comm])
      obtain ⟨b, hb⟩ := s10_rat_of_σV hd (Kd.sqrtNeg d • (y - σV 3 d y)) (by
        rw [show σV 3 d = conjV (Kd.σ d) 3 from rfl, s10_conjV_smul, map_sub,
          show conjV (Kd.σ d) 3 (conjV (Kd.σ d) 3 y) = y from s10_σV_σV y, s10_σ_sqrtNeg]
        module)
      have haA : a ∈ ann ℚ 3 r := (hmem a).mpr (ha ▸ add_mem hy (hσ y hy))
      have hbA : b ∈ ann ℚ 3 r := (hmem b).mpr (hb ▸ Submodule.smul_mem _ _ (sub_mem hy (hσ y hy)))
      have hy' : y = (2 : Kd d)⁻¹ • (bcV ℚ (Kd d) 3 a + (Kd.sqrtNeg d)⁻¹ • bcV ℚ (Kd d) 3 b) := by
        rw [ha, hb, smul_smul, inv_mul_cancel₀ hs, one_smul]
        rw [show (y + σV 3 d y + (y - σV 3 d y)) = (2 : Kd d) • y by module, smul_smul,
          inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨a, haA, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hbA, rfl⟩)))
    calc 2 * 3 = Module.finrank (Kd d) (ann (Kd d) 3 x) := hr.2.2.symm
      _ ≤ _ := Submodule.finrank_mono hle
      _ ≤ _ := s10_finrank_span_bcV_le _

end S10Descend

section S10Core

theorem s10_isTransversalSecant_swap {F : Type*} [Field F] [CharZero F] {n : ℕ}
    {P : Submodule F (S F n)} {u₁ u₂ : S F n} (h : IsTransversalSecant F n P u₁ u₂) :
    IsTransversalSecant F n P u₂ u₁ := by
  obtain ⟨hP, hli, h₁, h₂, hW, hpure⟩ := h
  refine ⟨by rw [hP, Set.pair_comm], ?_, h₂, h₁, by rw [inf_comm]; exact hW,
    fun u hu hup => (hpure u hu hup).symm⟩
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro a b hab
  have := hli b a (by rw [add_comm]; exact hab)
  exact ⟨this.2, this.1⟩

theorem s10_pair_eq_cases {α : Type*} {A B C D : α} (h : ({A, B} : Set α) = {C, D})
    (hAB : A ≠ B) : (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  have hA : A ∈ ({C, D} : Set α) := h ▸ (by simp)
  have hB : B ∈ ({C, D} : Set α) := h ▸ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact absurd rfl hAB
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hAB

/-- Descent of a line: if `bcS x ∈ F' · bcS y` with `y ≠ 0`, then `x ∈ F · y`. -/
theorem s10_mem_span_of_bcS {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] {x y : S F 3} (hy : y ≠ 0)
    (h : bcS F F' 3 x ∈ Submodule.span F' {bcS F F' 3 y}) : x ∈ Submodule.span F {y} := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  obtain ⟨K, hK⟩ : ∃ K, (basisS F 3).repr y K ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hy ((basisS F 3).repr.injective (Finsupp.ext fun K => by simpa using h' K))
  have hcK := congrArg (fun z => (basisS F' 3).repr z K) hc
  simp only [map_smul, Finsupp.smul_apply, s10_repr_bcS, smul_eq_mul] at hcK
  have hc' : c = algebraMap F F' ((basisS F 3).repr x K / (basisS F 3).repr y K) := by
    rw [map_div₀, ← hcK, mul_div_assoc, div_self ((map_ne_zero_iff _ (algebraMap F F').injective).mpr
      hK), mul_one]
  refine Submodule.mem_span_singleton.mpr ⟨(basisS F 3).repr x K / (basisS F 3).repr y K, ?_⟩
  apply s10_bcS_injective (F' := F')
  rw [map_smul, ← algebraMap_smul F', ← hc', hc]

theorem s10_bcV_injective {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] : Function.Injective (bcV F F' 3) := by
  intro v w h
  apply s10_V_ext
  · intro i
    have := congrArg (fun y : V F' 3 => y.1 (e F' 3 i)) h
    have h1 : (bcV F F' 3 v).1 (e F' 3 i) = algebraMap F F' (v.1 (e F 3 i)) := by
      show bcDual F F' 3 v.1 (e F' 3 i) = _
      rw [← s10_bcH1_e F 3 F' i, s10_bcDual_apply_bcH1]
    have h2 : (bcV F F' 3 w).1 (e F' 3 i) = algebraMap F F' (w.1 (e F 3 i)) := by
      show bcDual F F' 3 w.1 (e F' 3 i) = _
      rw [← s10_bcH1_e F 3 F' i, s10_bcDual_apply_bcH1]
    rw [h1, h2] at this
    exact (algebraMap F F').injective this
  · intro i
    have := congrArg (fun y : V F' 3 => y.2 i) h
    exact (algebraMap F F').injective this

variable {w : S ℚ 3}

/-- The lines of the secant `P_K` through `w` are permuted by `σ` (Remark 10.1.2(2) with complex
conjugation, i.e. "`P_w` is defined over `ℚ`" of Lemma 10.1.1). -/
theorem s10_lines_σ {d : ℚ} (hdJ : J ℚ w = d) (hw : w ∈ Splus ℚ 3) (hd : 0 < d)
    (g : Spin (Kd d) 3)
    (hg : m (Kd d) 3 (g : C (Kd d) 3) (bcS ℚ (Kd d) 3 w) = 1 + (2 * Kd.sqrtNeg d) • pt (Kd d) 3) :
    (σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)} ∧
      σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1}) ∨
    (σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1} ∧
      σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)}) := by
  have hinv : bcSpin (Kd d) ℂ 3 g⁻¹ = (bcSpin (Kd d) ℂ 3 g)⁻¹ := map_inv _ g
  have hU : bcS (Kd d) ℂ 3 (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)) =
      m ℂ 3 (((bcSpin (Kd d) ℂ 3 g)⁻¹ : Spin ℂ 3) : C ℂ 3) (pt ℂ 3) := by
    rw [s10_bcS_m_spin, hinv, show bcS (Kd d) ℂ 3 (pt (Kd d) 3) = pt ℂ 3 from
      s10_bcS_basisS _ _ _ _]
  have hU' : bcS (Kd d) ℂ 3 (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1) =
      m ℂ 3 (((bcSpin (Kd d) ℂ 3 g)⁻¹ : Spin ℂ 3) : C ℂ 3) 1 := by
    rw [s10_bcS_m_spin, hinv, map_one]
  have hPc := s10_isTransversalSecant_swap
    (s10_isTransversalSecant_map (bcSpin (Kd d) ℂ 3 g)⁻¹ (isTransversalSecant_one_pt ℂ))
  rw [← hU, ← hU'] at hPc
  have hwP : bcS ℚ ℂ 3 w ∈ (Submodule.span ℂ {1, pt ℂ 3}).map
      (m ℂ 3 (((bcSpin (Kd d) ℂ 3 g)⁻¹ : Spin ℂ 3) : C ℂ 3)) := by
    refine Submodule.mem_map.mpr ⟨1 + (algebraMap (Kd d) ℂ (2 * Kd.sqrtNeg d)) • pt ℂ 3,
      s10_one_add_mem_span _, ?_⟩
    have h1 : bcS ℚ (Kd d) 3 w =
        m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (1 + (2 * Kd.sqrtNeg d) • pt (Kd d) 3) := by
      rw [← hg, s10_m_inv_m]
    rw [← s10_bcS_bcS (F' := Kd d), h1, s10_bcS_m_spin, hinv]
    congr 1
    rw [map_add, map_one, map_smul, show bcS (Kd d) ℂ 3 (pt (Kd d) 3) = pt ℂ 3 from
      s10_bcS_basisS _ _ _ _, algebraMap_smul]
  have hrat := remark10_1_2_rational w hw (by rw [hdJ]; exact hd.ne') _ _ _ hPc hwP s10_cc
  rw [s10_cc_bcS, s10_cc_bcS] at hrat
  have hli := (s10_isTransversalSecant_conj s10_cc hPc).2.1
  rw [s10_cc_bcS, s10_cc_bcS] at hli
  have hne : ∀ x y : S ℂ 3, LinearIndependent ℂ ![x, y] →
      Submodule.span ℂ {x} ≠ Submodule.span ℂ {y} := by
    intro x y hxy h
    exact s10_not_mem_span_of_li hxy (h ▸ Submodule.mem_span_singleton_self _)
  have hu0 : m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3) ≠ 0 :=
    (s10_isEvenPureSpinor_m g⁻¹ (s10_isEvenPureSpinor_pt (Kd d) 3)).ne_zero (by norm_num)
  have hu0' : m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1 ≠ 0 :=
    (s10_isEvenPureSpinor_m g⁻¹ (s10_isEvenPureSpinor_one (Kd d) 3)).ne_zero (by norm_num)
  have key : ∀ x y : S (Kd d) 3, y ≠ 0 →
      Submodule.span ℂ {bcS (Kd d) ℂ 3 x} = Submodule.span ℂ {bcS (Kd d) ℂ 3 y} →
        x ∈ Submodule.span (Kd d) {y} :=
    fun x y hy h => s10_mem_span_of_bcS hy (h ▸ Submodule.mem_span_singleton_self _)
  rcases s10_pair_eq_cases hrat (hne _ _ hli) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key _ _ hu0 h1, key _ _ hu0' h2⟩
  · exact Or.inr ⟨key _ _ hu0' h1, key _ _ hu0 h2⟩

/-- **The paper's argument that `W₁, W₂` are not defined over `ℚ`** (proof of Lemma 10.2.1): if
`σ` fixed the two pure spinor lines of `P_K`, they would be spanned by rational pure spinors, so
`P_w` would be a `Spin(V_ℚ)`-translate of `span{1, [pt_X]}` ([Chevalley, §3.3 Lemma 1, III.1.4]
over `ℚ`), and `J` would be `≤ 0` on its rational points by (10.1.1), contradicting `J(w) > 0`. -/
theorem s10_not_fixed_lines {d : ℚ} (hdJ : J ℚ w = d) (hd : 0 < d)
    (g : Spin (Kd d) 3)
    (hg : m (Kd d) 3 (g : C (Kd d) 3) (bcS ℚ (Kd d) 3 w) = 1 + (2 * Kd.sqrtNeg d) • pt (Kd d) 3)
    (h1 : σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)})
    (h2 : σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1) ∈
        Submodule.span (Kd d) {m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1}) : False := by
  set u := m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3) with hu
  set u' := m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1 with hu'
  set s := Kd.sqrtNeg d with hs
  have hs0 : s ≠ 0 := s10_sqrtNeg_ne_zero hd
  have hT := s10_isTransversalSecant_map g⁻¹ (isTransversalSecant_one_pt (Kd d))
  have hli : LinearIndependent (Kd d) ![u', u] := hT.2.1
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h2
  -- `w_K = u' + 2s u` and `σ(w_K) = w_K`
  have hwK : bcS ℚ (Kd d) 3 w = u' + (2 * s) • u := by
    rw [hu', hu, ← map_smul, ← map_add, ← hg, s10_m_inv_m]
  have hσw : σS 3 d (bcS ℚ (Kd d) 3 w) = bcS ℚ (Kd d) 3 w := s10_conjS_bcS _ w
  rw [hwK, map_add, s10_σS_smul, ← hl, ← hμ, map_mul, s10_σ_sqrtNeg,
    show Kd.σ d 2 = 2 from map_ofNat _ 2] at hσw
  rw [← hs] at hσw
  have hco := LinearIndependent.pair_iff.mp hli (μ - 1) (-(2 * s) * l - 2 * s) (by
    rw [show (μ - 1) • u' + (-(2 * s) * l - 2 * s) • u =
      (μ • u' + (2 * -s) • l • u) - (u' + (2 * s) • u) by module, hσw, sub_self])
  have hμ1 : μ = 1 := sub_eq_zero.mp hco.1
  have hl1 : l = -1 := by
    have := hco.2
    have h2s : (2 : Kd d) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    have : (2 * s) * (l + 1) = 0 := by linear_combination -this
    have := (mul_eq_zero.mp this).resolve_left h2s
    linear_combination this
  -- the rational pure spinors `r' = u'`, `r = s u`
  have hσu' : σS 3 d u' = u' := by rw [← hμ, hμ1, one_smul]
  have hσsu : σS 3 d (s • u) = s • u := by
    rw [s10_σS_smul, ← hl, hl1, s10_σ_sqrtNeg, ← hs]
    module
  obtain ⟨r', hr'⟩ := s10_rat_of_σS hd u' hσu'
  obtain ⟨r, hr⟩ := s10_rat_of_σS hd (s • u) hσsu
  have hwr : w = r' + (2 : ℚ) • r := by
    apply s10_bcS_injective (F' := Kd d)
    rw [hwK, map_add, map_smul, hr', hr]
    congr 1
    rw [mul_smul, two_smul, two_smul]
  have hpu : IsEvenPureSpinor (Kd d) 3 u := hT.2.2.2.1
  have hpu' : IsEvenPureSpinor (Kd d) 3 u' := hT.2.2.1
  have hp' : IsEvenPureSpinor ℚ 3 r' := s10_pure_descent hd (hr' ▸ hpu')
  have hp : IsEvenPureSpinor ℚ 3 r := s10_pure_descent hd (hr ▸ s10_isEvenPureSpinor_smul hs0 hpu)
  have htrans : ann ℚ 3 r' ⊓ ann ℚ 3 r = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv1' : m ℚ 3 (ι (Q ℚ 3) v) r' = 0 := hv.1
    have hv2' : m ℚ 3 (ι (Q ℚ 3) v) r = 0 := hv.2
    have hv1 : bcV ℚ (Kd d) 3 v ∈ ann (Kd d) 3 u' := by
      show m (Kd d) 3 (ι (Q (Kd d) 3) (bcV ℚ (Kd d) 3 v)) u' = 0
      rw [← hr', ← s10_bcS_m_ι, hv1', map_zero]
    have hv2 : bcV ℚ (Kd d) 3 v ∈ ann (Kd d) 3 u := by
      show m (Kd d) 3 (ι (Q (Kd d) 3) (bcV ℚ (Kd d) 3 v)) u = 0
      have h' : m (Kd d) 3 (ι (Q (Kd d) 3) (bcV ℚ (Kd d) 3 v)) (s • u) = 0 := by
        rw [← hr, ← s10_bcS_m_ι, hv2', map_zero]
      rw [map_smul, smul_eq_zero] at h'
      exact h'.resolve_left hs0
    have h0 : bcV ℚ (Kd d) 3 v = 0 := by
      have := hT.2.2.2.2.1
      rw [eq_bot_iff] at this
      exact (Submodule.mem_bot _).mp (this ⟨hv1, hv2⟩)
    rw [Submodule.mem_bot]
    exact s10_bcV_injective (by rw [h0, map_zero])
  -- [Chevalley, §3.3 Lemma 1] over `ℚ`: `P` is a `Spin(V_ℚ)`-translate of `span{1, [pt]}`
  obtain ⟨h, hh1, hh2⟩ := chevalley_sec3_3_lemma1 ℚ 3 1 (pt ℚ 3) r' r
    (s10_isEvenPureSpinor_one ℚ 3) (s10_isEvenPureSpinor_pt ℚ 3) hp' hp
    (s10_ann_one_inf_ann_pt ℚ 3) htrans
  have hm1 := s10_isEvenPureSpinor_m h (s10_isEvenPureSpinor_one ℚ 3)
  have hm2 := s10_isEvenPureSpinor_m h (s10_isEvenPureSpinor_pt ℚ 3)
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (chevalley_III_1_4_unique ℚ 3 _ r'
    (hm1.ne_zero (by norm_num)) hm1.2 (by rw [ann_m_spin, hh1]))
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (chevalley_III_1_4_unique ℚ 3 _ r
    (hm2.ne_zero (by norm_num)) hm2.2 (by rw [ann_m_spin, hh2]))
  have hw' : w = m ℚ 3 (h : C ℚ 3) (α • 1 + (2 * β) • pt ℚ 3) := by
    rw [hwr, ← hα, ← hβ, map_add, map_smul, map_smul, smul_smul]
  have hJw := igusa_prop3_invariant ℚ h (α • 1 + (2 * β) • pt ℚ 3)
    (add_mem (Submodule.smul_mem _ _ (s10_one_mem_Splus ℚ 3))
      (Submodule.smul_mem _ _ (s10_pt_mem_Splus ℚ 3)))
  rw [← hw', s10_J_add_smul_pt, hdJ] at hJw
  have : d ≤ 0 := by rw [hJw]; nlinarith [sq_nonneg (α * (2 * β))]
  linarith

theorem s10_isTransversalSecant_smul_right {F : Type*} [Field F] [CharZero F] {n : ℕ}
    {P : Submodule F (S F n)} {u₁ u₂ : S F n} (h : IsTransversalSecant F n P u₁ u₂) {c : F}
    (hc : c ≠ 0) : IsTransversalSecant F n P u₁ (c • u₂) := by
  obtain ⟨hP, hli, h₁, h₂, hW, hpure⟩ := h
  refine ⟨?_, ?_, h₁, s10_isEvenPureSpinor_smul hc h₂, by rw [s10_ann_smul hc]; exact hW, ?_⟩
  · rw [hP, show u₁ = (1 : F) • u₁ from (one_smul F u₁).symm, s10_span_pair_smul one_ne_zero hc,
      one_smul]
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro a b hab
    have := hli a (b * c) (by rw [mul_smul]; exact hab)
    exact ⟨this.1, (mul_eq_zero.mp this.2).resolve_right hc⟩
  · intro u hu hup
    rcases hpure u hu hup with h | h
    · exact Or.inl h
    · right
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
      exact Submodule.mem_span_singleton.mpr ⟨a * c⁻¹, by rw [mul_smul, inv_smul_smul₀ hc]⟩

theorem s10_bcSubS_span {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (X : Set (S F 3)) :
    bcSubS F F' 3 (Submodule.span F X) = Submodule.span F' (bcS F F' 3 '' X) := by
  apply le_antisymm
  · rw [bcSubS, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul F']
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, Submodule.subset_span hx, rfl⟩

/-- **The rational `K`-secant through `w`** (proof of Lemma 10.2.1): for `g ∈ Spin(V_K)` with
`g(w) = 1 + 2√-d [pt_X]` ([Igusa, Prop. 3], last paragraph), `σ` exchanges the lines of
`g⁻¹[pt_X]` and `g⁻¹ 1`.
Departure from the paper (order of the steps): the paper first shows that `W₁, W₂` are not defined
over `ℚ` (otherwise `J ≤ 0` on the rational points of a `Spin(V_ℚ)`-translate of
`span{1, [pt_X]}`) and deduces `σ(W₁) = W₂` from the `σ`-invariance of the pair. Here the same
`J`-argument is applied to `σ`-fixed lines (`s10_not_fixed_lines`), which gives `σ(ℓ̃₁) = ℓ̃₂`
directly; that `W₁, W₂` are not defined over `ℚ` then follows in `lemma10_2_1`, since complex
conjugation exchanges `(W₁)_ℂ` and `(W₂)_ℂ` and fixes every subspace defined over `ℚ`. -/
theorem s10_cm_secant {d : ℚ} (hdJ : J ℚ w = d) (hw : w ∈ Splus ℚ 3) (hd : 0 < d) :
    ∃ g : Spin (Kd d) 3,
      m (Kd d) 3 (g : C (Kd d) 3) (bcS ℚ (Kd d) 3 w) = 1 + (2 * Kd.sqrtNeg d) • pt (Kd d) 3 ∧
      ∃ c : Kd d, c ≠ 0 ∧
        σS 3 d (m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) (pt (Kd d) 3)) =
          c • m (Kd d) 3 ((g⁻¹ : Spin (Kd d) 3) : C (Kd d) 3) 1 := by
  subst hdJ
  obtain ⟨g, hg⟩ := igusa_prop3_normalForm w hw hd
  refine ⟨g, hg, ?_⟩
  rcases s10_lines_σ rfl hw hd g hg with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact (s10_not_fixed_lines rfl hd g hg h1 h2).elim
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    rw [zero_smul] at hc
    have hu0 := (s10_isEvenPureSpinor_m g⁻¹ (s10_isEvenPureSpinor_pt (Kd (J ℚ w)) 3)).ne_zero
      (by norm_num)
    apply hu0
    apply s10_conjS_injective (Kd.σ (J ℚ w))
    rw [map_zero]
    exact hc.symm

end S10Core

section S10Eta

variable {d : ℚ} (P : KSecant 3 d) (hW : IsCompl P.W₁ P.W₂)

theorem s10_ηK_W₁ (l : Kd d) {a : V (Kd d) 3} (ha : a ∈ P.W₁) : P.ηK hW l a = l • a := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.projectionOnto_apply_left hW ⟨a, ha⟩,
    Submodule.projectionOnto_apply_right hW.symm ⟨a, ha⟩, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, add_zero]

theorem s10_ηK_W₂ (l : Kd d) {b : V (Kd d) 3} (hb : b ∈ P.W₂) :
    P.ηK hW l b = Kd.σ d l • b := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.projectionOnto_apply_right hW ⟨b, hb⟩,
    Submodule.projectionOnto_apply_left hW.symm ⟨b, hb⟩, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, zero_add]

include hW in
theorem s10_decomp (v : V (Kd d) 3) : ∃ a ∈ P.W₁, ∃ b ∈ P.W₂, v = a + b := by
  have : v ∈ P.W₁ ⊔ P.W₂ := hW.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
  exact ⟨a, ha, b, hb, rfl⟩

theorem s10_ηK_add (l : Kd d) {a b : V (Kd d) 3} (ha : a ∈ P.W₁) (hb : b ∈ P.W₂) :
    P.ηK hW l (a + b) = l • a + Kd.σ d l • b := by
  rw [map_add, s10_ηK_W₁ P hW l ha, s10_ηK_W₂ P hW l hb]

theorem s10_σV_W₁ {a : V (Kd d) 3} (ha : a ∈ P.W₁) : σV 3 d a ∈ P.W₂ := (P.σV_mem_W₂_iff a).mpr ha

theorem s10_σV_W₂ {b : V (Kd d) 3} (hb : b ∈ P.W₂) : σV 3 d b ∈ P.W₁ := by
  have := (P.σV_mem_W₂_iff (σV 3 d b)).mp
  rw [s10_σV_σV] at this
  exact this hb

theorem s10_σV_smul (c : Kd d) (v : V (Kd d) 3) : σV 3 d (c • v) = Kd.σ d c • σV 3 d v :=
  s10_conjV_smul _ c v

/-- `η_λ` commutes with `σ`. -/
theorem s10_σV_ηK (l : Kd d) (v : V (Kd d) 3) :
    σV 3 d (P.ηK hW l v) = P.ηK hW l (σV 3 d v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := s10_decomp P hW v
  rw [s10_ηK_add P hW l ha hb, map_add, map_add, s10_σV_smul, s10_σV_smul, s10_σ_σ, add_comm
    (σV 3 d a), s10_ηK_add P hW l (s10_σV_W₂ P hb) (s10_σV_W₁ P ha), add_comm]

theorem s10_bcV_η (l : Kd d) (v : V ℚ 3) :
    bcV ℚ (Kd d) 3 (P.η hW l v) = P.ηK hW l (bcV ℚ (Kd d) 3 v) :=
  bcV_descend 3 d (P.ηK hW l) (s10_σV_ηK P hW l) v

theorem s10_ηK_mul (l l' : Kd d) (v : V (Kd d) 3) :
    P.ηK hW l (P.ηK hW l' v) = P.ηK hW (l * l') v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := s10_decomp P hW v
  rw [s10_ηK_add P hW l' ha hb, s10_ηK_add P hW l (P.W₁.smul_mem _ ha) (P.W₂.smul_mem _ hb),
    s10_ηK_add P hW (l * l') ha hb, smul_smul, smul_smul, map_mul]

theorem s10_ηK_injective {l : Kd d} (hl : l ≠ 0) : Function.Injective (P.ηK hW l) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := s10_decomp P hW v
  rw [s10_ηK_add P hW l ha hb] at hv
  have hσl : Kd.σ d l ≠ 0 := (map_ne_zero _).mpr hl
  have hmem : l • a ∈ P.W₁ ⊓ P.W₂ :=
    ⟨P.W₁.smul_mem _ ha, by rw [eq_neg_of_add_eq_zero_left hv]; exact P.W₂.neg_mem (P.W₂.smul_mem _ hb)⟩
  rw [hW.inf_eq_bot, Submodule.mem_bot, smul_eq_zero] at hmem
  have ha0 : a = 0 := hmem.resolve_left hl
  rw [ha0, smul_zero, zero_add, smul_eq_zero] at hv
  rw [ha0, hv.resolve_left hσl, add_zero]
  exact Submodule.zero_mem _

theorem s10_span_bcV_eq_top : Submodule.span (Kd d) (Set.range (bcV ℚ (Kd d) 3)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, v.1 (e (Kd d) 3 i) • ((f (Kd d) 3 i, 0) : V (Kd d) 3) +
      ∑ i, v.2 i • ((0, e (Kd d) 3 i) : V (Kd d) 3) := by
    apply s10_V_ext
    · intro i
      simp [Prod.fst_sum, LinearMap.sum_apply, s10_f_e]
    · intro i
      simp [Prod.snd_sum, Finset.sum_apply, e, Pi.single_apply]
  rw [hv]
  have h1 : ∀ i, ((f (Kd d) 3 i, 0) : V (Kd d) 3) = bcV ℚ (Kd d) 3 (f ℚ 3 i, 0) := by
    intro i
    apply s10_V_ext
    · intro j
      rw [s10_bcV_fst]
      simp [s10_f_e]
    · intro j; simp [s10_bcV_snd]
  have h2 : ∀ i, ((0, e (Kd d) 3 i) : V (Kd d) 3) = bcV ℚ (Kd d) 3 (0, e ℚ 3 i) := by
    intro i
    apply s10_V_ext
    · intro j; rw [s10_bcV_fst]; simp
    · intro j
      rw [s10_bcV_snd]
      simp [e, Pi.single_apply]
  refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
  · rw [h1]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [h2]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem s10_η_injective {l : Kd d} (hl : l ≠ 0) : Function.Injective (P.η hW l) := by
  intro x y h
  apply s10_bcV_injective (F' := Kd d)
  apply s10_ηK_injective P hW hl
  rw [← s10_bcV_η, ← s10_bcV_η, h]

theorem s10_η_mul (l l' : Kd d) (v : V ℚ 3) : P.η hW l (P.η hW l' v) = P.η hW (l * l') v := by
  apply s10_bcV_injective (F' := Kd d)
  rw [s10_bcV_η, s10_bcV_η, s10_bcV_η, s10_ηK_mul]

theorem s10_η_inj_param {l l' : Kd d} (h : P.η hW l = P.η hW l') : l = l' := by
  have hK : P.ηK hW l = P.ηK hW l' := by
    apply LinearMap.ext_on_range (s10_span_bcV_eq_top (d := d))
    intro v
    rw [← s10_bcV_η, ← s10_bcV_η, h]
  obtain ⟨a, ha⟩ : ∃ a : P.W₁, a ≠ 0 := by
    have hfr : Module.finrank (Kd d) P.W₁ = 6 := P.isPure.2.2
    have hpos : 0 < Module.finrank (Kd d) P.W₁ := by rw [hfr]; norm_num
    exact Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have h1 := LinearMap.congr_fun hK a
  rw [s10_ηK_W₁ P hW l a.2, s10_ηK_W₁ P hW l' a.2] at h1
  have h2 : (l - l') • (a : V (Kd d) 3) = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd (Subtype.ext h3) ha

theorem s10_pairing_bcV (x y : V ℚ 3) :
    pairing (Kd d) 3 (bcV ℚ (Kd d) 3 x) (bcV ℚ (Kd d) 3 y) = algebraMap ℚ (Kd d) (pairing ℚ 3 x y) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, Q_bcV,
    map_sub]

theorem s10_pairing_W {W : Submodule (Kd d) (V (Kd d) 3)} (hW' : ∀ v ∈ W, Q (Kd d) 3 v = 0)
    {a a' : V (Kd d) 3} (ha : a ∈ W) (ha' : a' ∈ W) : pairing (Kd d) 3 a a' = 0 := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hW' _ (W.add_mem ha ha'),
    hW' _ ha, hW' _ ha', sub_zero, sub_zero]

/-- `η_λ` is a similarity with multiplier `Nm(λ)`. -/
theorem s10_pairing_η (hd : 0 < d) (l : Kd d) (x y : V ℚ 3) :
    pairing ℚ 3 (P.η hW l x) (P.η hW l y) = Kd.Nm d l * pairing ℚ 3 x y := by
  apply (algebraMap ℚ (Kd d)).injective
  rw [map_mul, ← s10_pairing_bcV, ← s10_pairing_bcV, s10_bcV_η, s10_bcV_η]
  have hNm : algebraMap ℚ (Kd d) (Kd.Nm d l) = l * Kd.σ d l := by
    apply Subtype.ext
    have h1 : ((algebraMap ℚ (Kd d) (Kd.Nm d l) : Kd d) : ℂ) = ((Kd.Nm d l : ℚ) : ℂ) := by simp
    rw [h1, Kd.coe_Nm hd l, Subfield.coe_mul, Kd.coe_σ]
  rw [hNm]
  obtain ⟨a, ha, b, hb, hX⟩ := s10_decomp P hW (bcV ℚ (Kd d) 3 x)
  obtain ⟨a', ha', b', hb', hY⟩ := s10_decomp P hW (bcV ℚ (Kd d) 3 y)
  rw [hX, hY, s10_ηK_add P hW l ha hb, s10_ηK_add P hW l ha' hb']
  have h1 := P.isPure.2.1
  have h2 := P.isPure₂.2.1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    s10_pairing_W h1 ha ha', s10_pairing_W h2 hb hb']
  ring

end S10Eta

section S10Main

/-- (Proof of Lemma 10.2.1, l. 9792–9796.) The secant through `w`, with its construction: for
`g ∈ Spin(V_K)` with `g(w) = 1 + 2√-d [pt_X]` ([Igusa, Prop. 3], last paragraph), the rational
`K`-secant `P` with `u₁ = g⁻¹[pt_X]` and `u₂ = σ(u₁) = c · g⁻¹ 1`, so that `W₁ = g⁻¹(H¹(X))` and
`W₂ = g⁻¹(H¹(X̂))`; `V_K = W₁ ⊕ W₂`, `w ∈ P`, and `P_K ⊗ ℂ` is the transversal secant through `w`
of Lemma 10.1.1 and the base change of `P`. -/
theorem s10_secant_data (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ (g : Spin (Kd (J ℚ w)) 3) (c : Kd (J ℚ w)) (P : KSecant 3 (J ℚ w)), c ≠ 0 ∧
      P.u₁ = m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3)
        (pt (Kd (J ℚ w)) 3) ∧
      P.u₂ = c • m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3) 1 ∧
      IsCompl P.W₁ P.W₂ ∧ w ∈ P.Pℚ ∧
      IsTransversalSecant ℂ 3 (bcSubS (Kd (J ℚ w)) ℂ 3 P.PK)
        (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) ∧
      bcSubS (Kd (J ℚ w)) ℂ 3 P.PK = bcSubS ℚ ℂ 3 P.Pℚ := by
  -- the normal form `g(w) = 1 + 2√-d [pt_X]` over `K` ([Igusa, Prop. 3]); `σ` exchanges the lines
  obtain ⟨g, hg, c, hc, hσ⟩ := s10_cm_secant rfl hw hd
  have hT := s10_isTransversalSecant_map g⁻¹ (isTransversalSecant_one_pt (Kd (J ℚ w)))
  have hT' := s10_isTransversalSecant_smul_right (s10_isTransversalSecant_swap hT) hc
  have hli : LinearIndependent (Kd (J ℚ w))
      ![m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3) (pt (Kd (J ℚ w)) 3),
        σS 3 (J ℚ w)
          (m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3) (pt (Kd (J ℚ w)) 3))] := by
    rw [hσ]
    exact hT'.2.1
  obtain ⟨P, hu₁⟩ : ∃ P : KSecant 3 (J ℚ w),
      P.u₁ = m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3) (pt (Kd (J ℚ w)) 3) :=
    ⟨⟨_, hT.2.2.2.1, hli⟩, rfl⟩
  have hu₂ : P.u₂ = c • m (Kd (J ℚ w)) 3 ((g⁻¹ : Spin (Kd (J ℚ w)) 3) : C (Kd (J ℚ w)) 3) 1 := by
    rw [← hσ, ← hu₁]
    rfl
  have hinv : bcSpin (Kd (J ℚ w)) ℂ 3 g⁻¹ = (bcSpin (Kd (J ℚ w)) ℂ 3 g)⁻¹ := map_inv _ g
  refine ⟨g, c, P, hc, hu₁, hu₂, ?_, ?_, ?_, ?_⟩
  · apply P.isCompl_of_inf_eq_bot
    show ann _ 3 P.u₁ ⊓ ann _ 3 P.u₂ = ⊥
    rw [hu₁, hu₂, s10_ann_smul hc, inf_comm]
    exact hT.2.2.2.2.1
  · show bcS ℚ (Kd (J ℚ w)) 3 w ∈ P.PK
    rw [KSecant.PK, hu₁, hu₂]
    have h1 : bcS ℚ (Kd (J ℚ w)) 3 w = (2 * Kd.sqrtNeg (J ℚ w)) •
        m _ 3 ((g⁻¹ : Spin _ 3) : C _ 3) (pt _ 3) + c⁻¹ • (c • m _ 3 ((g⁻¹ : Spin _ 3) : C _ 3) 1) := by
      rw [inv_smul_smul₀ hc, ← map_smul, ← map_add, add_comm, ← hg, s10_m_inv_m]
    rw [h1]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · -- the base change to `ℂ`: the transversal secant `g⁻¹ span{1, [pt]}` (Lemma 10.1.1)
    have hPc := s10_isTransversalSecant_smul_right (s10_isTransversalSecant_swap
      (s10_isTransversalSecant_map (bcSpin (Kd (J ℚ w)) ℂ 3 g)⁻¹ (isTransversalSecant_one_pt ℂ)))
      (show algebraMap (Kd (J ℚ w)) ℂ c ≠ 0 from
        (map_ne_zero_iff _ (algebraMap (Kd (J ℚ w)) ℂ).injective).mpr hc)
    have hU : bcS (Kd (J ℚ w)) ℂ 3 P.u₁ = m ℂ 3 (((bcSpin _ ℂ 3 g)⁻¹ : Spin ℂ 3) : C ℂ 3) (pt ℂ 3) := by
      rw [hu₁, s10_bcS_m_spin, hinv, show bcS (Kd (J ℚ w)) ℂ 3 (pt _ 3) = pt ℂ 3 from
        s10_bcS_basisS _ _ _ _]
    have hU' : bcS (Kd (J ℚ w)) ℂ 3 P.u₂ = algebraMap (Kd (J ℚ w)) ℂ c •
        m ℂ 3 (((bcSpin _ ℂ 3 g)⁻¹ : Spin ℂ 3) : C ℂ 3) 1 := by
      rw [hu₂, map_smul, s10_bcS_m_spin, hinv, map_one, algebraMap_smul]
    rw [KSecant.PK, s10_bcSubS_span, Set.image_pair, hU, hU', ← hPc.1]
    exact hPc
  · rw [← P.span_bcS_Pℚ, s10_bcSubS_span, Set.image_image, bcSubS]
    congr 1
    exact Set.image_congr fun r _ => s10_bcS_bcS r

theorem s10_secant (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ P : KSecant 3 (J ℚ w), IsCompl P.W₁ P.W₂ ∧ w ∈ P.Pℚ ∧
      IsTransversalSecant ℂ 3 (bcSubS (Kd (J ℚ w)) ℂ 3 P.PK)
        (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) ∧
      bcSubS (Kd (J ℚ w)) ℂ 3 P.PK = bcSubS ℚ ℂ 3 P.Pℚ := by
  obtain ⟨-, -, P, -, -, -, h⟩ := s10_secant_data w hw hd
  exact ⟨P, h⟩

theorem s10_spinStab_eq (w : S ℚ 3) (_hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    spinStab ℚ 3 w = P.spinPℚ := by
  have hwK : bcS ℚ (Kd (J ℚ w)) 3 w ∈ P.PK := hwP
  -- `w` lies on neither line `ℓ̃ᵢ`: otherwise it would be pure over `ℂ`, while `J(w) ≠ 0`
  have hnot : ∀ u ∈ ({P.u₁, P.u₂} : Set (S (Kd (J ℚ w)) 3)),
      bcS ℚ (Kd (J ℚ w)) 3 w ∉ Submodule.span (Kd (J ℚ w)) {u} := by
    intro u hu hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hu0 : u ≠ 0 := by
      rcases hu with rfl | rfl
      · exact P.u₁_ne_zero
      · exact P.isPure₂.ne_zero (by norm_num)
    have hpure : IsEvenPureSpinor ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 u) := by
      have hmemc : bcS (Kd (J ℚ w)) ℂ 3 u ∈
          Submodule.span ℂ {bcS (Kd (J ℚ w)) ℂ 3 P.u₁, bcS (Kd (J ℚ w)) ℂ 3 P.u₂} := by
        rcases hu with rfl | rfl
        · exact Submodule.subset_span (by simp)
        · exact Submodule.subset_span (by simp)
      rw [P.isEvenPureSpinor_iff_of_mem_span hd (by norm_num) hW.inf_eq_bot _ hmemc]
      refine ⟨fun h0 => hu0 (s10_bcS_injective (by rw [h0, map_zero])), ?_⟩
      rcases hu with rfl | rfl
      · exact Or.inl (Submodule.mem_span_singleton_self _)
      · exact Or.inr (Submodule.mem_span_singleton_self _)
    have hJ0 := (s10_singular _ hpure).1
    apply s10_J_bcS_ne_zero (F := ℂ) hd.ne'
    rw [← s10_bcS_bcS (F' := Kd (J ℚ w)), ← ha, map_smul, ← algebraMap_smul ℂ a, J_smul, hJ0,
      mul_zero]
  -- Remark 2.2.3 (`n = 3` odd): the stabilizer of `w` is `Spin(V_K)_P`
  have hfix := remark2_2_3_odd P hd (by norm_num) (by decide) hW.inf_eq_bot _ hwK
    (hnot P.u₁ (by simp)) (hnot P.u₂ (by simp))
  ext h
  constructor
  · intro hh r hr
    have hhw : m ℚ 3 (h : C ℚ 3) w = w := hh
    have hbc : bcSpin ℚ (Kd (J ℚ w)) 3 h ∈
        fixingSpin (Kd (J ℚ w)) 3 (Submodule.span (Kd (J ℚ w)) {bcS ℚ (Kd (J ℚ w)) 3 w}) := by
      intro p hp
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hp
      rw [map_smul, ← s10_bcS_m_spin, hhw]
    rw [hfix] at hbc
    apply s10_bcS_injective (F' := Kd (J ℚ w))
    rw [s10_bcS_m_spin]
    exact hbc _ hr
  · intro hh
    exact hh w hwP

theorem s10_eta_centralizer (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    (∀ l l' : (Kd (J ℚ w))ˣ, P.η hW l = P.η hW l' → l = l') ∧
      (∀ l : (Kd (J ℚ w))ˣ, ∃ h ∈ Otilde 3 (J ℚ w), (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l) ∧
      ∀ h : V ℚ 3 ≃ₗ[ℚ] V ℚ 3,
        h ∈ Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓
            Otilde 3 (J ℚ w) ↔
          ∃ l : (Kd (J ℚ w))ˣ, (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l := by
  refine ⟨fun l l' h => Units.ext (s10_η_inj_param P hW h), fun l => ?_, fun h => ?_⟩
  · -- `η_λ` is an injective endomorphism, hence an automorphism, and a similarity
    refine ⟨LinearEquiv.ofInjectiveEndo (P.η hW l) (s10_η_injective P hW l.ne_zero),
      ⟨Kd.Nm (J ℚ w) l, ⟨l, l.ne_zero, rfl⟩, fun x y => ?_⟩, rfl⟩
    exact s10_pairing_η P hW hd l x y
  · -- Lemma 2.2.4 with `Spin(V_ℚ)_w = Spin(V_ℚ)_P` (Remark 2.2.3)
    have hP : ¬ P.IsIsotropic := fun h' => (lemma2_2_1 P hd).mp h' hW.inf_eq_bot
    have hstab := s10_spinStab_eq w hw hd P hW hwP
    have key := lemma2_2_4 P hd (by norm_num) hP h
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hc, hO⟩
      obtain ⟨l, hl, hhl⟩ := key.mp ⟨hO, fun g hg => by
        rw [← hstab] at hg
        exact (hc _ ⟨g, hg, rfl⟩).symm⟩
      exact ⟨Units.mk0 l hl, hhl⟩
    · rintro ⟨l, hhl⟩
      obtain ⟨hO, hcomm⟩ := key.mpr ⟨l, l.ne_zero, hhl⟩
      refine ⟨?_, hO⟩
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, hstab] at hg
      exact (hcomm g hg).symm

end S10Main

/-! ## Density of `Spin(V_ℚ)_w` (a gap in the proof of Lemma 10.2.1)

The paper calls `W₁, W₂` "the two maximal isotropic subspaces of `V_ℂ` invariant under
`Spin(V_ℚ)_w`". That no other maximal isotropic subspace is invariant needs that `Spin(V_ℚ)_w` is
Zariski dense in `Spin(V_ℂ)_w ≅ SL(W₁)`, which the paper does not discuss. We prove the needed
consequence directly, along the plan of `notes/proof-plans.md` (unitary transvections):

* for an isotropic `u ∈ V_ℚ` and `f = η(√-d)`, the unipotent `E_u = 1 + ι(f u) ι(u)` (Tau Ceti's
  `spinTransvection`) lies in `Spin(V_ℚ)_P = Spin(V_ℚ)_w` and acts on `V_ℂ` by `1 + Ñ(u, u)`,
  `Ñ(v, v') = D_{f v', v}`, `D_{x,y} = (y, ·) x - (x, ·) y` (`s10_transvection_mem`,
  `s10_rho_bcSpin_transvection`);
* a quadratic map vanishing on the null cone of `Q` is, modulo a subspace, a multiple of `Q`
  (`s10_quad_mod`, with the hyperbolic pair `(f₀, 0), (0, e₀)` of `V_ℚ`);
* for `a ∈ W₁`, `b ∈ W₂` with `(a, b)_V = 0`, `D_{a,b}` is a combination of polarizations of `Ñ`
  whose `Q`-part is `(a, b)_V = 0`, so it preserves every `Spin(V_ℚ)_w`-invariant subspace
  (`s10_D_mem`); in the frame `g⁻¹(H¹(X̂) ⊕ H¹(X))` these are the nilpotents of the proof of
  Lemma 10.1.1, which leave only `W₁` and `W₂` (`s10_eq_A_or_B`). -/

section S10Quad

theorem s10_Q_add {F : Type*} [Field F] [CharZero F] (x y : V F 3) :
    Q F 3 (x + y) = Q F 3 x + Q F 3 y + pairing F 3 x y :=
  QuadraticMap.map_add _ x y

theorem s10_Q_smul {F : Type*} [Field F] [CharZero F] (c : F) (x : V F 3) :
    Q F 3 (c • x) = c * c * Q F 3 x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem s10_pairing_self {F : Type*} [Field F] [CharZero F] (x : V F 3) :
    pairing F 3 x x = 2 * Q F 3 x := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
    Nat.cast_ofNat]

theorem s10_pairing_comm {F : Type*} [Field F] [CharZero F] (x y : V F 3) :
    pairing F 3 x y = pairing F 3 y x := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm]

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (N : V ℚ 3 →ₗ[ℚ] V ℚ 3 →ₗ[ℚ] M)
  (S : Submodule ℚ M)

/-- For a hyperbolic pair `a, b` and `z ⊥ a, b`, the vectors `x_t = -(t² Q z) a + b + t z` are
isotropic; the coefficients of `t` and `t²` in `N(x_t, x_t)` lie in `S`. -/
theorem s10_quad_step (hN : ∀ x, Q ℚ 3 x = 0 → N x x ∈ S) {a b : V ℚ 3}
    (ha : Q ℚ 3 a = 0) (hb : Q ℚ 3 b = 0) (hab : pairing ℚ 3 a b = 1) {z : V ℚ 3}
    (haz : pairing ℚ 3 a z = 0) (hbz : pairing ℚ 3 b z = 0) :
    N b z + N z b ∈ S ∧ N z z - Q ℚ 3 z • (N a b + N b a) ∈ S := by
  set q := Q ℚ 3 z with hq
  let x : ℚ → V ℚ 3 := fun t => (-(t ^ 2 * q)) • a + b + t • z
  have hiso : ∀ t, Q ℚ 3 (x t) = 0 := by
    intro t
    simp only [x, s10_Q_add, s10_Q_smul, ha, hb, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hab, haz, hbz, ← hq]
    ring
  have hX : ∀ t, N (x t) (x t) = (t ^ 4 * q ^ 2) • N a a + N b b + t • (N b z + N z b) +
      t ^ 2 • (N z z - q • (N a b + N b a)) + (-(t ^ 3 * q)) • (N a z + N z a) := by
    intro t
    simp only [x, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    module
  have h1 := hN _ (hiso 1)
  have h2 := hN _ (hiso (-1))
  have h3 := hN _ (hiso 2)
  have haa := hN a ha
  have hbb := hN b hb
  constructor
  · have e : N b z + N z b = N (x 1) (x 1) - (1 / 3 : ℚ) • N (x (-1)) (x (-1)) -
        (1 / 6 : ℚ) • N (x 2) (x 2) + (2 * q ^ 2) • N a a - (1 / 2 : ℚ) • N b b := by
      rw [hX, hX, hX]
      module
    rw [e]
    exact sub_mem (add_mem (sub_mem (sub_mem h1 (S.smul_mem _ h2)) (S.smul_mem _ h3))
      (S.smul_mem _ haa)) (S.smul_mem _ hbb)
  · have e : N z z - q • (N a b + N b a) = (1 / 2 : ℚ) • N (x 1) (x 1) +
        (1 / 2 : ℚ) • N (x (-1)) (x (-1)) - (q ^ 2) • N a a - N b b := by
      rw [hX, hX]
      module
    rw [e]
    exact sub_mem (sub_mem (add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)) (S.smul_mem _ haa)) hbb

/-- **A quadratic map vanishing on the null cone of `Q`** (modulo a subspace `S`) is a multiple of
`Q`: if `N(x, x) ∈ S` whenever `Q(x) = 0`, then `N(v, v) ≡ Q(v) N₀` modulo `S`, with
`N₀ = N(p, p') + N(p', p)` for a hyperbolic pair `p, p'`. -/
theorem s10_quad_mod (hN : ∀ x, Q ℚ 3 x = 0 → N x x ∈ S) {p p' : V ℚ 3}
    (hp : Q ℚ 3 p = 0) (hp' : Q ℚ 3 p' = 0) (hpp : pairing ℚ 3 p p' = 1) (v : V ℚ 3) :
    N v v - Q ℚ 3 v • (N p p' + N p' p) ∈ S := by
  have hp'p : pairing ℚ 3 p' p = 1 := by rw [s10_pairing_comm]; exact hpp
  obtain ⟨α, β, z, hpz, hp'z, rfl⟩ : ∃ α β : ℚ, ∃ z : V ℚ 3, pairing ℚ 3 p z = 0 ∧
      pairing ℚ 3 p' z = 0 ∧ v = α • p + β • p' + z := by
    refine ⟨pairing ℚ 3 v p', pairing ℚ 3 v p,
      v - pairing ℚ 3 v p' • p - pairing ℚ 3 v p • p', ?_, ?_, by abel⟩
    · simp only [map_sub, map_smul, smul_eq_mul, s10_pairing_self, hp, hpp, mul_zero, sub_zero,
        mul_one]
      rw [s10_pairing_comm, sub_self]
    · simp only [map_sub, map_smul, smul_eq_mul, s10_pairing_self, hp', hp'p, mul_zero,
        sub_zero, mul_one]
      rw [s10_pairing_comm, sub_self]
  obtain ⟨h1, h2⟩ := s10_quad_step N S hN hp hp' hpp hpz hp'z
  obtain ⟨h3, -⟩ := s10_quad_step N S hN hp' hp hp'p hp'z hpz
  have hQ : Q ℚ 3 (α • p + β • p' + z) = α * β + Q ℚ 3 z := by
    simp only [s10_Q_add, s10_Q_smul, hp, hp', map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hpp, hpz, hp'z]
    ring
  have e : N (α • p + β • p' + z) (α • p + β • p' + z) -
      Q ℚ 3 (α • p + β • p' + z) • (N p p' + N p' p) =
      (α * α) • N p p + (β * β) • N p' p' + α • (N p z + N z p) + β • (N p' z + N z p') +
        (N z z - Q ℚ 3 z • (N p p' + N p' p)) := by
    rw [hQ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    module
  rw [e]
  exact add_mem (add_mem (add_mem (add_mem (S.smul_mem _ (hN p hp)) (S.smul_mem _ (hN p' hp')))
    (S.smul_mem _ h3)) (S.smul_mem _ h1)) h2

/-- The polarized form of `s10_quad_mod`. -/
theorem s10_polar_mod (hN : ∀ x, Q ℚ 3 x = 0 → N x x ∈ S) {p p' : V ℚ 3}
    (hp : Q ℚ 3 p = 0) (hp' : Q ℚ 3 p' = 0) (hpp : pairing ℚ 3 p p' = 1) (v v' : V ℚ 3) :
    N v v' + N v' v - pairing ℚ 3 v v' • (N p p' + N p' p) ∈ S := by
  have h := sub_mem (sub_mem (s10_quad_mod N S hN hp hp' hpp (v + v'))
    (s10_quad_mod N S hN hp hp' hpp v)) (s10_quad_mod N S hN hp hp' hpp v')
  convert h using 1
  rw [s10_Q_add]
  simp only [map_add, LinearMap.add_apply]
  module

end S10Quad

section S10Ops

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F]

/-- The operator `D_{x,y} : z ↦ (y, z) x - (x, z) y` of `V` (the element `x ∧ y` of `so(V)`). -/
noncomputable def s10_D (x y : V F 3) : Module.End F (V F 3) :=
  (pairing F 3 y).smulRight x - (pairing F 3 x).smulRight y

theorem s10_D_apply (x y z : V F 3) :
    s10_D x y z = pairing F 3 y z • x - pairing F 3 x z • y := rfl

theorem s10_D_swap (x y z : V F 3) : s10_D y x z = -s10_D x y z := by
  rw [s10_D_apply, s10_D_apply, neg_sub]

theorem s10_D_add_left (x x' y : V F 3) : s10_D (x + x') y = s10_D x y + s10_D x' y :=
  LinearMap.ext fun z => by
    simp only [s10_D_apply, LinearMap.add_apply, map_add]
    module

theorem s10_D_add_right (x y y' : V F 3) : s10_D x (y + y') = s10_D x y + s10_D x y' :=
  LinearMap.ext fun z => by
    simp only [s10_D_apply, LinearMap.add_apply, map_add]
    module

theorem s10_D_smul_left (c : F) (x y : V F 3) : s10_D (c • x) y = c • s10_D x y :=
  LinearMap.ext fun z => by
    simp only [s10_D_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    module

theorem s10_D_smul_right (c : F) (x y : V F 3) : s10_D x (c • y) = c • s10_D x y :=
  LinearMap.ext fun z => by
    simp only [s10_D_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    module

theorem s10_rho_D (g : Spin F 3) (x y z : V F 3) :
    s10_D (rho F 3 g x) (rho F 3 g y) (rho F 3 g z) = rho F 3 g (s10_D x y z) := by
  rw [s10_D_apply, s10_D_apply, s10_rho_isometry, s10_rho_isometry, map_sub, map_smul, map_smul]

/-- The nilpotent `s10_N i j` of the proof of Lemma 10.1.1 is `D_{(f_i, 0), (0, e_j)}`. -/
theorem s10_N_eq_D (i j : Fin 6) (z : V F 3) :
    s10_N i j z = s10_D ((f F 3 i, 0) : V F 3) (0, e F 3 j) z := by
  rw [s10_D_apply, s10_pairing_apply, s10_pairing_apply, s10_N_apply]
  refine Prod.ext ?_ ?_
  · simp
  · simp [f]

end S10Ops

section S10BCV

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']

theorem s10_bcV_fst' (v : V F 3) (i : Fin 6) :
    (bcV F F' 3 v).1 (e F' 3 i) = algebraMap F F' (v.1 (e F 3 i)) := by
  show bcDual F F' 3 v.1 (e F' 3 i) = _
  rw [← s10_bcH1_e F 3 F' i, s10_bcDual_apply_bcH1]

theorem s10_bcV_snd' (v : V F 3) (i : Fin 6) :
    (bcV F F' 3 v).2 i = algebraMap F F' (v.2 i) := rfl

theorem s10_bcV_bcV {F'' : Type*} [Field F''] [CharZero F''] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (x : V F 3) : bcV F' F'' 3 (bcV F F' 3 x) = bcV F F'' 3 x := by
  apply s10_V_ext
  · intro i
    rw [s10_bcV_fst', s10_bcV_fst', s10_bcV_fst', ← IsScalarTower.algebraMap_apply]
  · intro i
    rw [s10_bcV_snd', s10_bcV_snd', s10_bcV_snd', ← IsScalarTower.algebraMap_apply]

theorem s10_pairing_bcV' (x y : V F 3) :
    pairing F' 3 (bcV F F' 3 x) (bcV F F' 3 y) = algebraMap F F' (pairing F 3 x y) := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, Q_bcV,
    map_sub]

theorem s10_bcV_f (i : Fin 6) : bcV F F' 3 ((f F 3 i, 0) : V F 3) = (f F' 3 i, 0) := by
  apply s10_V_ext
  · intro j
    rw [s10_bcV_fst']
    simp [s10_f_e]
  · intro j
    rw [s10_bcV_snd']
    simp

theorem s10_bcV_e (i : Fin 6) : bcV F F' 3 ((0, e F 3 i) : V F 3) = (0, e F' 3 i) := by
  apply s10_V_ext
  · intro j
    rw [s10_bcV_fst']
    simp
  · intro j
    rw [s10_bcV_snd']
    simp [e, Pi.single_apply]

theorem s10_bcC_star (x : C F 3) : bcC F F' 3 (star x) = star (bcC F F' 3 x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [star_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' 3),
      star_algebraMap]
  | ι v => simp [s10_bcC_ι, star_ι]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

/-- `ρ` commutes with change of coefficients. -/
theorem s10_bcV_rho (g : Spin F 3) (x : V F 3) :
    bcV F F' 3 (rho F 3 g x) = rho F' 3 (bcSpin F F' 3 g) (bcV F F' 3 x) := by
  apply CliffordAlgebra.ι_injective (Q F' 3)
  rw [ι_rho, ← s10_bcC_ι, ι_rho, map_mul, map_mul, s10_bcC_ι, s10_bcC_star]
  rfl

end S10BCV

section S10Transvection

/-- The Clifford relation on spinors: `m_x m_y = (x, y) - m_y m_x`. -/
theorem s10_m_ι_m_ι {F : Type*} [Field F] [CharZero F] (x y : V F 3) (s : S F 3) :
    m F 3 (ι (Q F 3) x) (m F 3 (ι (Q F 3) y) s) =
      pairing F 3 x y • s - m F 3 (ι (Q F 3) y) (m F 3 (ι (Q F 3) x) s) := by
  have h := congrArg (fun c => m F 3 c s) (ι_mul_ι_add_swap (Q := Q F 3) x y)
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, AlgHom.commutes,
    Module.algebraMap_end_apply] at h
  rw [eq_sub_iff_add_eq, h]
  rfl

theorem s10_m_ι_sq {F : Type*} [Field F] [CharZero F] (x : V F 3) (s : S F 3) :
    m F 3 (ι (Q F 3) x) (m F 3 (ι (Q F 3) x) s) = Q F 3 x • s := by
  rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The unipotent `E = 1 + ι(w') ι(u)` (Tau Ceti's `spinTransvection`, `u` isotropic, `w' ⊥ u`,
`w'` isotropic) acts on `V_ℂ` by `z ↦ z + D_{w', u} z`. -/
theorem s10_rho_bcSpin_transvection {u w' : V ℚ 3} (hu : Q ℚ 3 u = 0)
    (huw : QuadraticMap.polar (Q ℚ 3) u w' = 0) (hw' : Q ℚ 3 w' = 0) (z : V ℂ 3) :
    rho ℂ 3 (bcSpin ℚ ℂ 3 (spinTransvection (s10_Q_nondegenerate ℚ 3) hu huw)) z =
      z + s10_D (bcV ℚ ℂ 3 w') (bcV ℚ ℂ 3 u) z := by
  have hu' : Q ℂ 3 (bcV ℚ ℂ 3 u) = 0 := by rw [Q_bcV, hu, map_zero]
  have huw' : QuadraticMap.polar (Q ℂ 3) (bcV ℚ ℂ 3 u) (bcV ℚ ℂ 3 w') = 0 := by
    have := s10_pairing_bcV' (F := ℚ) (F' := ℂ) u w'
    rw [pairing, QuadraticMap.polarBilin_apply_apply, pairing, QuadraticMap.polarBilin_apply_apply,
      huw, map_zero] at this
    exact this
  have heq : bcSpin ℚ ℂ 3 (spinTransvection (s10_Q_nondegenerate ℚ 3) hu huw) =
      spinTransvection (s10_Q_nondegenerate ℂ 3) hu' huw' := by
    apply Subtype.ext
    have h1 : ((bcSpin ℚ ℂ 3 (spinTransvection (s10_Q_nondegenerate ℚ 3) hu huw) : Spin ℂ 3) :
        C ℂ 3) = bcC ℚ ℂ 3 (spinTransvection (s10_Q_nondegenerate ℚ 3) hu huw : C ℚ 3) := rfl
    rw [h1, coe_spinTransvection, coe_spinTransvection, map_add, map_one, map_mul, s10_bcC_ι,
      s10_bcC_ι]
  rw [heq, rho, ← coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_spinTransvection,
    QuadraticMap.transvection_apply, Q_bcV, hw', map_zero, zero_mul, zero_smul, sub_zero,
    s10_D_apply, pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm _ z, QuadraticMap.polar_comm _ z]
  abel

variable {d : ℚ} (P : KSecant 3 d) (hW : IsCompl P.W₁ P.W₂)

/-- For an isotropic rational `u`: `(u, f u) = 0` and `Q(f u) = 0`, `f = η(√-d)`. -/
theorem s10_fη_isotropic {u : V ℚ 3} (hu : Q ℚ 3 u = 0) :
    QuadraticMap.polar (Q ℚ 3) u (P.fη hW u) = 0 ∧ Q ℚ 3 (P.fη hW u) = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := s10_decomp P hW (bcV ℚ (Kd d) 3 u)
  have hf : bcV ℚ (Kd d) 3 (P.fη hW u) = Kd.sqrtNeg d • a + Kd.σ d (Kd.sqrtNeg d) • b := by
    rw [KSecant.fη, s10_bcV_η, hab, s10_ηK_add P hW _ ha hb]
  have hQa := P.isPure.2.1 a ha
  have hQb := P.isPure₂.2.1 b hb
  have hB : pairing (Kd d) 3 a b = 0 := by
    have h1 : Q (Kd d) 3 (a + b) = 0 := by rw [← hab, Q_bcV, hu, map_zero]
    rw [s10_Q_add, hQa, hQb, zero_add, zero_add] at h1
    exact h1
  constructor
  · apply (algebraMap ℚ (Kd d)).injective
    rw [map_zero, show QuadraticMap.polar (Q ℚ 3) u (P.fη hW u) = pairing ℚ 3 u (P.fη hW u) from
      rfl, ← s10_pairing_bcV, hab, hf]
    simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, s10_pairing_self, hQa, hQb, hB,
      s10_pairing_comm b a]
    ring
  · apply (algebraMap ℚ (Kd d)).injective
    rw [map_zero, ← Q_bcV, hf, s10_Q_add, s10_Q_smul, s10_Q_smul, hQa, hQb]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB]
    ring

/-- **Unitary transvections lie in `Spin(V_ℚ)_P`**: for an isotropic rational `u`, the unipotent
`E_u = 1 + ι(f u) ι(u)` fixes the plane `P` (it kills `ℓ̃₁` and `ℓ̃₂` up to the identity). -/
theorem s10_transvection_mem {u : V ℚ 3} (hu : Q ℚ 3 u = 0)
    (huf : QuadraticMap.polar (Q ℚ 3) u (P.fη hW u) = 0) :
    spinTransvection (s10_Q_nondegenerate ℚ 3) hu huf ∈ P.spinPℚ := by
  intro p hp
  show m ℚ 3 (spinTransvection (s10_Q_nondegenerate ℚ 3) hu huf : C ℚ 3) p = p
  rw [coe_spinTransvection, map_add, map_one, map_mul, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply]
  suffices h : m ℚ 3 (ι (Q ℚ 3) (P.fη hW u)) (m ℚ 3 (ι (Q ℚ 3) u) p) = 0 by rw [h, add_zero]
  apply s10_bcS_injective (F' := Kd d)
  rw [s10_bcS_m_ι, s10_bcS_m_ι, map_zero]
  obtain ⟨a, ha, b, hb, hab⟩ := s10_decomp P hW (bcV ℚ (Kd d) 3 u)
  have hf : bcV ℚ (Kd d) 3 (P.fη hW u) = Kd.sqrtNeg d • a + Kd.σ d (Kd.sqrtNeg d) • b := by
    rw [KSecant.fη, s10_bcV_η, hab, s10_ηK_add P hW _ ha hb]
  have hQa := P.isPure.2.1 a ha
  have hQb := P.isPure₂.2.1 b hb
  have hB : pairing (Kd d) 3 a b = 0 := by
    have h1 : Q (Kd d) 3 (a + b) = 0 := by rw [← hab, Q_bcV, hu, map_zero]
    rw [s10_Q_add, hQa, hQb, zero_add, zero_add] at h1
    exact h1
  have hB' : pairing (Kd d) 3 b a = 0 := by rw [s10_pairing_comm]; exact hB
  have ha' : m (Kd d) 3 (ι (Q (Kd d) 3) a) P.u₁ = 0 := ha
  have hb' : m (Kd d) 3 (ι (Q (Kd d) 3) b) P.u₂ = 0 := hb
  have hpK : bcS ℚ (Kd d) 3 p ∈ P.PK := hp
  rw [hf, hab]
  set T : Module.End (Kd d) (S (Kd d) 3) :=
    m (Kd d) 3 (ι (Q (Kd d) 3) (Kd.sqrtNeg d • a + Kd.σ d (Kd.sqrtNeg d) • b)) *
      m (Kd d) 3 (ι (Q (Kd d) 3) (a + b)) with hT
  have hlin : ∀ (x y : V (Kd d) 3) (c c' : Kd d) (t : S (Kd d) 3),
      m (Kd d) 3 (ι (Q (Kd d) 3) (c • x + c' • y)) t =
        c • m (Kd d) 3 (ι (Q (Kd d) 3) x) t + c' • m (Kd d) 3 (ι (Q (Kd d) 3) y) t := by
    intro x y c c' t
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  have hlin' : ∀ (x y : V (Kd d) 3) (t : S (Kd d) 3),
      m (Kd d) 3 (ι (Q (Kd d) 3) (x + y)) t =
        m (Kd d) 3 (ι (Q (Kd d) 3) x) t + m (Kd d) 3 (ι (Q (Kd d) 3) y) t := by
    intro x y t
    simp only [map_add, LinearMap.add_apply]
  have hT1 : T P.u₁ = 0 := by
    rw [hT, Module.End.mul_apply, hlin' a b, ha', zero_add, hlin, s10_m_ι_m_ι a b, hB, zero_smul,
      ha', map_zero, sub_zero, s10_m_ι_sq, hQb, zero_smul, smul_zero, smul_zero, add_zero]
  have hT2 : T P.u₂ = 0 := by
    rw [hT, Module.End.mul_apply, hlin' a b, hb', add_zero, hlin, s10_m_ι_sq, hQa, zero_smul,
      s10_m_ι_m_ι b a, hB', zero_smul, hb', map_zero, sub_zero, smul_zero, smul_zero, add_zero]
  have hle : P.PK ≤ LinearMap.ker T := by
    rw [KSecant.PK, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hT1, hT2⟩
  exact hle hpK

end S10Transvection

section S10Dense

/-- The operators of `V_ℂ` preserving a subspace `W`. -/
def s10_stabEnd (W : Submodule ℂ (V ℂ 3)) : Submodule ℂ (Module.End ℂ (V ℂ 3)) where
  carrier := {T | ∀ x ∈ W, T x ∈ W}
  add_mem' := fun hT hT' x hx => W.add_mem (hT x hx) (hT' x hx)
  zero_mem' := fun _ _ => W.zero_mem
  smul_mem' := fun c _ hT x hx => W.smul_mem c (hT x hx)

/-- The operators `Ñ(v, v') = D_{φ v', v}` of `V_ℂ` (`v, v' ∈ V_ℚ`, `φ` a rational endomorphism), as
a `ℚ`-bilinear map; `Ñ(u, u) + 1` is the action of the unitary transvection `1 + ι(φ u) ι(u)`. -/
noncomputable def s10_Nop (φ : V ℚ 3 →ₗ[ℚ] V ℚ 3) :
    V ℚ 3 →ₗ[ℚ] V ℚ 3 →ₗ[ℚ] Module.End ℂ (V ℂ 3) :=
  LinearMap.mk₂ ℚ (fun v v' => s10_D (bcV ℚ ℂ 3 (φ v')) (bcV ℚ ℂ 3 v))
    (fun v₁ v₂ v' => by rw [map_add, s10_D_add_right])
    (fun c v v' => by
      rw [map_smul, ← Rat.cast_smul_eq_qsmul ℂ c (bcV ℚ ℂ 3 v), s10_D_smul_right,
        Rat.cast_smul_eq_qsmul])
    (fun v v'₁ v'₂ => by rw [map_add, map_add, s10_D_add_left])
    (fun c v v' => by
      rw [map_smul, map_smul, ← Rat.cast_smul_eq_qsmul ℂ c (bcV ℚ ℂ 3 (φ v')), s10_D_smul_left,
        Rat.cast_smul_eq_qsmul])

theorem s10_Nop_apply (φ : V ℚ 3 →ₗ[ℚ] V ℚ 3) (v v' : V ℚ 3) :
    s10_Nop φ v v' = s10_D (bcV ℚ ℂ 3 (φ v')) (bcV ℚ ℂ 3 v) := rfl

variable {d : ℚ} (P : KSecant 3 d) (hW : IsCompl P.W₁ P.W₂)

include hW in
/-- **Density of `Spin(V_ℚ)_P`** (the step of the proof of Lemma 10.2.1 that the paper does not
discuss): a subspace `W ⊆ V_ℂ` invariant under `Spin(V_ℚ)_P` is invariant under `D_{a,b}` for all
`a ∈ W₁`, `b ∈ W₂` with `(a, b)_V = 0`. The unitary transvections `1 + ι(f u) ι(u)` (`u ∈ V_ℚ`
isotropic, `f = η(√-d)`) lie in `Spin(V_ℚ)_P` and act by `1 + Ñ(u, u)`; a quadratic map vanishing
on the null cone of `Q` is a multiple of `Q` (`s10_polar_mod`), and `D_{a,b}` is a combination of
polarizations of `Ñ` whose `Q`-part is `(a, b)_V = 0`.
Departure from the paper (a gap filled): the paper uses without comment that `W₁, W₂` are the only
invariant maximal isotropic subspaces; this lemma, with `s10_eq_A_or_B`, proves it (plan of
`notes/proof-plans.md`). -/
theorem s10_D_mem (hd : 0 < d) (W : Submodule ℂ (V ℂ 3))
    (hinv : IsInvariantUnder ℚ ℂ 3 P.spinPℚ W) {a b : V (Kd d) 3} (ha : a ∈ P.W₁)
    (hb : b ∈ P.W₂) (hab : pairing (Kd d) 3 a b = 0) (x : V ℂ 3) (hx : x ∈ W) :
    s10_D (bcV (Kd d) ℂ 3 a) (bcV (Kd d) ℂ 3 b) x ∈ W := by
  set φ := P.fη hW with hφdef
  -- the unitary transvections preserve `W`
  have hN : ∀ u, Q ℚ 3 u = 0 → s10_Nop φ u u ∈ (s10_stabEnd W).restrictScalars ℚ := by
    intro u hu y hy
    obtain ⟨huf, hfu⟩ := s10_fη_isotropic P hW hu
    have h1 := hinv _ (s10_transvection_mem P hW hu huf) y hy
    rw [s10_rho_bcSpin_transvection hu huf hfu] at h1
    have h2 := W.sub_mem h1 hy
    rwa [add_sub_cancel_left] at h2
  -- the hyperbolic pair `p = (f₀, 0)`, `p' = (0, e₀)` of `V_ℚ`
  have hp : Q ℚ 3 ((f ℚ 3 0, 0) : V ℚ 3) = 0 := by simp [Q]
  have hp' : Q ℚ 3 ((0, e ℚ 3 0) : V ℚ 3) = 0 := by simp [Q]
  have hpp : pairing ℚ 3 ((f ℚ 3 0, 0) : V ℚ 3) (0, e ℚ 3 0) = 1 := by
    rw [s10_pairing_apply]
    simp [s10_f_e]
  have hpol := s10_polar_mod (s10_Nop φ) _ hN hp hp' hpp
  set P₀ := s10_Nop φ (f ℚ 3 0, 0) (0, e ℚ 3 0) + s10_Nop φ (0, e ℚ 3 0) (f ℚ 3 0, 0) with hP₀
  -- rational vectors `v, v'` with `v_K = a + σ a`, `v'_K = σ b + b`
  have ha' : σV 3 d a ∈ P.W₂ := s10_σV_W₁ P ha
  have hb' : σV 3 d b ∈ P.W₁ := s10_σV_W₂ P hb
  obtain ⟨v, hv⟩ := s10_rat_of_σV hd (a + σV 3 d a) (by rw [map_add, s10_σV_σV, add_comm])
  obtain ⟨v', hv'⟩ := s10_rat_of_σV hd (σV 3 d b + b) (by rw [map_add, s10_σV_σV, add_comm])
  set s := Kd.sqrtNeg d with hs
  have hσs : Kd.σ d s = -s := s10_σ_sqrtNeg d
  have hφ : ∀ y : V ℚ 3, bcV ℚ (Kd d) 3 (φ y) = P.ηK hW s (bcV ℚ (Kd d) 3 y) :=
    fun y => s10_bcV_η P hW s y
  have hφv : bcV ℚ (Kd d) 3 (φ v) = s • a - s • σV 3 d a := by
    rw [hφ, hv, s10_ηK_add P hW s ha ha', hσs, neg_smul, sub_eq_add_neg]
  have hφv' : bcV ℚ (Kd d) 3 (φ v') = s • σV 3 d b - s • b := by
    rw [hφ, hv', s10_ηK_add P hW s hb' hb, hσs, neg_smul, sub_eq_add_neg]
  have hφφv' : bcV ℚ (Kd d) 3 (φ (φ v')) = (s * s) • σV 3 d b + (s * s) • b := by
    rw [hφ, hφ, s10_ηK_mul, hv', s10_ηK_add P hW _ hb' hb, map_mul, hσs, neg_mul_neg]
  -- over `ℂ`
  set s' : ℂ := algebraMap (Kd d) ℂ s with hs'
  have hs'2 : s' ^ 2 = -(d : ℂ) := by
    rw [hs', ← map_pow, hs, s10_sqrtNeg_sq hd, map_neg, ← IsScalarTower.algebraMap_apply,
      eq_ratCast]
  set A := bcV (Kd d) ℂ 3 a with hA
  set A' := bcV (Kd d) ℂ 3 (σV 3 d a) with hA'
  set C := bcV (Kd d) ℂ 3 (σV 3 d b) with hC
  set C' := bcV (Kd d) ℂ 3 b with hC'
  have hbc : ∀ y : V ℚ 3, bcV ℚ ℂ 3 y = bcV (Kd d) ℂ 3 (bcV ℚ (Kd d) 3 y) :=
    fun y => (s10_bcV_bcV y).symm
  have hsm : ∀ (c : Kd d) (y : V (Kd d) 3),
      bcV (Kd d) ℂ 3 (c • y) = algebraMap (Kd d) ℂ c • bcV (Kd d) ℂ 3 y := fun c y => by
    rw [map_smul, algebraMap_smul]
  have e1 : bcV ℚ ℂ 3 v = A + A' := by rw [hbc, hv, map_add]
  have e2 : bcV ℚ ℂ 3 (φ v) = s' • A - s' • A' := by rw [hbc, hφv, map_sub, hsm, hsm]
  have e3 : bcV ℚ ℂ 3 v' = C + C' := by rw [hbc, hv', map_add]
  have e4 : bcV ℚ ℂ 3 (φ v') = s' • C - s' • C' := by rw [hbc, hφv', map_sub, hsm, hsm]
  have e5 : bcV ℚ ℂ 3 (φ (φ v')) = s' ^ 2 • C + s' ^ 2 • C' := by
    rw [hbc, hφφv', map_add, hsm, hsm, map_mul, sq]
  -- the operator identity `4d D_{A,C'} = P(v, φ v') - s' P(v, v')`
  have key : (-4 * s' ^ 2) • s10_D A C' = (s10_Nop φ v (φ v') + s10_Nop φ (φ v') v) -
      s' • (s10_Nop φ v v' + s10_Nop φ v' v) := by
    refine LinearMap.ext fun z => ?_
    simp only [s10_Nop_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      s10_D_apply, e1, e2, e3, e4, e5, map_add, map_sub, map_smul, smul_eq_mul]
    module
  -- the scalar identity: the `Q`-part vanishes
  have hAC : pairing ℂ 3 A C = 0 := by
    rw [hA, hC, s10_pairing_bcV', s10_pairing_W P.isPure.2.1 ha hb', map_zero]
  have hAC' : pairing ℂ 3 A C' = 0 := by rw [hA, hC', s10_pairing_bcV', hab, map_zero]
  have hA'C' : pairing ℂ 3 A' C' = 0 := by
    rw [hA', hC', s10_pairing_bcV', s10_pairing_W P.isPure₂.2.1 ha' hb, map_zero]
  have k1 : ((pairing ℚ 3 v (φ v') : ℚ) : ℂ) = pairing ℂ 3 (A + A') (s' • C - s' • C') := by
    rw [← e1, ← e4, s10_pairing_bcV', eq_ratCast]
  have k2 : ((pairing ℚ 3 v v' : ℚ) : ℂ) = pairing ℂ 3 (A + A') (C + C') := by
    rw [← e1, ← e3, s10_pairing_bcV', eq_ratCast]
  have hκ : ((pairing ℚ 3 v (φ v') : ℚ) : ℂ) - s' * ((pairing ℚ 3 v v' : ℚ) : ℂ) = 0 := by
    rw [k1, k2]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, smul_eq_mul, hAC, hAC', hA'C']
    ring
  have hmem : (s10_Nop φ v (φ v') + s10_Nop φ (φ v') v) -
      s' • (s10_Nop φ v v' + s10_Nop φ v' v) ∈ s10_stabEnd W := by
    have h1 : s10_Nop φ v (φ v') + s10_Nop φ (φ v') v - pairing ℚ 3 v (φ v') • P₀ ∈
        s10_stabEnd W := hpol v (φ v')
    have h2 : s10_Nop φ v v' + s10_Nop φ v' v - pairing ℚ 3 v v' • P₀ ∈ s10_stabEnd W :=
      hpol v v'
    have e : (s10_Nop φ v (φ v') + s10_Nop φ (φ v') v) -
        s' • (s10_Nop φ v v' + s10_Nop φ v' v) =
        (s10_Nop φ v (φ v') + s10_Nop φ (φ v') v - pairing ℚ 3 v (φ v') • P₀) -
          s' • (s10_Nop φ v v' + s10_Nop φ v' v - pairing ℚ 3 v v' • P₀) +
          (((pairing ℚ 3 v (φ v') : ℚ) : ℂ) - s' * ((pairing ℚ 3 v v' : ℚ) : ℂ)) • P₀ := by
      rw [← Rat.cast_smul_eq_qsmul ℂ (pairing ℚ 3 v (φ v')) P₀,
        ← Rat.cast_smul_eq_qsmul ℂ (pairing ℚ 3 v v') P₀]
      module
    rw [e, hκ, zero_smul, add_zero]
    exact (s10_stabEnd W).sub_mem h1 ((s10_stabEnd W).smul_mem s' h2)
  have hne : (-4 * s' ^ 2 : ℂ) ≠ 0 := by
    rw [hs'2]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    intro h
    exact this (by linear_combination h / 4)
  have h3 : (-4 * s' ^ 2) • s10_D A C' ∈ s10_stabEnd W := by rw [key]; exact hmem
  have h4 := (s10_stabEnd W).smul_mem (-4 * s' ^ 2)⁻¹ h3
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  exact h4 x hx

end S10Dense

section S10Frame

set_option linter.unusedSectionVars false

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']

theorem s10_rho_rho_inv (g : Spin F 3) (v : V F 3) : rho F 3 g (rho F 3 g⁻¹ v) = v := by
  have hρmul : ∀ a b : Spin F 3, rho F 3 (a * b) = rho F 3 a * rho F 3 b := fun a b =>
    CliffordAlgebra.spinVectorAction_mul _ a b
  rw [← LinearEquiv.mul_apply, ← hρmul, mul_inv_cancel]
  exact congrArg (fun e : V F 3 ≃ₗ[F] V F 3 => e v) (CliffordAlgebra.spinVectorAction_one _)

theorem s10_rho_inv_rho (g : Spin F 3) (v : V F 3) : rho F 3 g⁻¹ (rho F 3 g v) = v := by
  have := s10_rho_rho_inv g⁻¹ v
  rwa [inv_inv] at this

theorem s10_bcSubV_map_rho (g : Spin F 3) (A : Submodule F (V F 3)) :
    bcSubV F F' 3 (A.map (rho F 3 g).toLinearMap) =
      (bcSubV F F' 3 A).map (rho F' 3 (bcSpin F F' 3 g)).toLinearMap := by
  rw [bcSubV, bcSubV, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => s10_bcV_rho g x

theorem s10_bcSubV_bot_prod_top :
    bcSubV F F' 3 ((⊥ : Submodule F (Module.Dual F (H1 F 3))).prod ⊤) =
      (⊥ : Submodule F' (Module.Dual F' (H1 F' 3))).prod ⊤ := by
  apply le_antisymm
  · rw [bcSubV, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x.1 = 0 := by simpa using (Submodule.mem_prod.mp hx).1
    refine Submodule.mem_prod.mpr ⟨?_, Submodule.mem_top⟩
    rw [Submodule.mem_bot]
    show bcDual F F' 3 x.1 = 0
    rw [h1, map_zero]
  · intro y hy
    have h1 : y.1 = 0 := by simpa using (Submodule.mem_prod.mp hy).1
    have hy' : y = ∑ i : Fin 6, y.2 i • ((0, e F' 3 i) : V F' 3) := by
      refine Prod.ext ?_ ?_
      · simp [h1, Prod.fst_sum]
      · funext k
        simp [Prod.snd_sum, Finset.sum_apply, e, Pi.single_apply]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(0, e F 3 i), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, Submodule.mem_top⟩,
        s10_bcV_e i⟩)

theorem s10_bcSubV_top_prod_bot :
    bcSubV F F' 3 ((⊤ : Submodule F (Module.Dual F (H1 F 3))).prod ⊥) =
      (⊤ : Submodule F' (Module.Dual F' (H1 F' 3))).prod ⊥ := by
  apply le_antisymm
  · rw [bcSubV, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h2 : x.2 = 0 := by simpa using (Submodule.mem_prod.mp hx).2
    refine Submodule.mem_prod.mpr ⟨Submodule.mem_top, ?_⟩
    rw [Submodule.mem_bot]
    show bcH1 F F' 3 x.2 = 0
    rw [h2, map_zero]
  · intro y hy
    have h2 : y.2 = 0 := by simpa using (Submodule.mem_prod.mp hy).2
    have hy' : y = ∑ i : Fin 6, y.1 (e F' 3 i) • ((f F' 3 i, 0) : V F' 3) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sum, Prod.smul_fst]
        exact s10_dual_eq_sum y.1
      · simp [h2, Prod.snd_sum]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(f F 3 i, 0), Submodule.mem_prod.mpr ⟨Submodule.mem_top, Submodule.zero_mem _⟩,
        s10_bcV_f i⟩)

/-- The coordinatewise action of a field automorphism fixes the vectors defined over `ℚ`. -/
theorem s10_conjV_bcV (c : F ≃+* F) (x : V ℚ 3) : conjV c 3 (bcV ℚ F 3 x) = bcV ℚ F 3 x := by
  apply s10_V_ext
  · intro i
    rw [s10_conjV_fst]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, s10_f_e, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [s10_bcV_fst', eq_ratCast, map_ratCast]
  · intro i
    rw [s10_conjV_snd, Function.comp_apply, s10_bcV_snd', eq_ratCast, map_ratCast]

theorem s10_map_conjVL_bcSubV (c : F ≃+* F) (W₀ : Submodule ℚ (V ℚ 3)) :
    (bcSubV ℚ F 3 W₀).map (s10_conjVL c) = bcSubV ℚ F 3 W₀ := by
  rw [bcSubV, Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => s10_conjV_bcV c x

theorem s10_σS_σS {d : ℚ} (x : S (Kd d) 3) : σS 3 d (σS 3 d x) = x := by
  have := s10_conjS_symm_conjS (Kd.σ d) x
  rwa [show (Kd.σ d).symm = Kd.σ d from RingEquiv.ext fun z => rfl] at this

end S10Frame

/-! ## Lemma 10.2.1 -/

/-- **Lemma 10.2.1** (`lemma-imaginary-quadratic-field-is-centralizer-sixfold-case`), first
sentence. Let `w ∈ S⁺_ℚ` with `d := J(w) > 0`, and `K = ℚ(√-d)` (`Kd (J ℚ w)`). Then the two maximal
isotropic subspaces `W₁, W₂` of `V_ℂ` invariant under `Spin(V_ℚ)_w` (acting through
`Spin(V_ℚ) → Spin(V_ℂ)` and `ρ`) are defined over `K` — they are the base changes of subspaces
`W₁, W₂ ⊆ V_K` — but not over `ℚ`, and `σ(W₁) = W₂`.
Reading: "the two maximal isotropic subspaces of `V_ℂ` invariant under `Spin(V_ℚ)_w`" asserts that
there are exactly two such subspaces; this is stated as the equivalence below (it uses that
`Spin(V_ℚ)_w` is Zariski dense in `Spin(V_ℂ)_w ≅ SL(W₁)`, which the paper does not discuss). -/
theorem lemma10_2_1 (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ W₁ W₂ : Submodule (Kd (J ℚ w)) (V (Kd (J ℚ w)) 3),
      W₁ ≠ W₂ ∧
      (∀ W : Submodule ℂ (V ℂ 3),
        IsMaxIsotropic ℂ 3 W ∧ IsInvariantUnder ℚ ℂ 3 (spinStab ℚ 3 w) W ↔
          W = bcSubV (Kd (J ℚ w)) ℂ 3 W₁ ∨ W = bcSubV (Kd (J ℚ w)) ℂ 3 W₂) ∧
      ¬ IsDefinedOverV ℚ ℂ 3 (bcSubV (Kd (J ℚ w)) ℂ 3 W₁) ∧
      ¬ IsDefinedOverV ℚ ℂ 3 (bcSubV (Kd (J ℚ w)) ℂ 3 W₂) ∧
      σV 3 (J ℚ w) '' (W₁ : Set (V (Kd (J ℚ w)) 3)) = (W₂ : Set (V (Kd (J ℚ w)) 3)) := by
  obtain ⟨g, c, P, hc, hu₁, hu₂, hW, hwP, hT, hPK⟩ := s10_secant_data w hw hd
  have hstab := s10_spinStab_eq w hw hd P hW hwP
  set gc := bcSpin (Kd (J ℚ w)) ℂ 3 g with hgc
  have hinv : bcSpin (Kd (J ℚ w)) ℂ 3 g⁻¹ = gc⁻¹ := map_inv _ g
  have hptc : bcS (Kd (J ℚ w)) ℂ 3 (pt (Kd (J ℚ w)) 3) = pt ℂ 3 := s10_bcS_basisS _ _ _ _
  -- `W₁ = g⁻¹(H¹(X))`, `W₂ = g⁻¹(H¹(X̂))` and their base changes to `ℂ`
  have hW1 : P.W₁ =
      ((⊥ : Submodule (Kd (J ℚ w)) (Module.Dual (Kd (J ℚ w)) (H1 (Kd (J ℚ w)) 3))).prod ⊤).map
        (rho (Kd (J ℚ w)) 3 g⁻¹).toLinearMap := by
    show ann _ 3 P.u₁ = _
    rw [hu₁, ann_m_spin, ann_pt]
  have hW2 : P.W₂ =
      ((⊤ : Submodule (Kd (J ℚ w)) (Module.Dual (Kd (J ℚ w)) (H1 (Kd (J ℚ w)) 3))).prod ⊥).map
        (rho (Kd (J ℚ w)) 3 g⁻¹).toLinearMap := by
    show ann _ 3 P.u₂ = _
    rw [hu₂, s10_ann_smul hc, ann_m_spin, ann_one]
  have hW1c : bcSubV (Kd (J ℚ w)) ℂ 3 P.W₁ =
      ((⊥ : Submodule ℂ (Module.Dual ℂ (H1 ℂ 3))).prod ⊤).map (rho ℂ 3 gc⁻¹).toLinearMap := by
    rw [hW1, s10_bcSubV_map_rho, s10_bcSubV_bot_prod_top, hinv]
  have hW2c : bcSubV (Kd (J ℚ w)) ℂ 3 P.W₂ =
      ((⊤ : Submodule ℂ (Module.Dual ℂ (H1 ℂ 3))).prod ⊥).map (rho ℂ 3 gc⁻¹).toLinearMap := by
    rw [hW2, s10_bcSubV_map_rho, s10_bcSubV_top_prod_bot, hinv]
  have hA1 : bcSubV (Kd (J ℚ w)) ℂ 3 P.W₁ = ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) := by
    rw [hW1c, hu₁, s10_bcS_m_spin, hinv, hptc, ann_m_spin, ann_pt]
  have hA2 : bcSubV (Kd (J ℚ w)) ℂ 3 P.W₂ = ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) := by
    rw [hW2c, hu₂, map_smul, ← algebraMap_smul ℂ c, s10_ann_smul ((map_ne_zero_iff _
      (algebraMap (Kd (J ℚ w)) ℂ).injective).mpr hc), s10_bcS_m_spin, hinv, map_one, ann_m_spin,
      ann_one]
  -- `Spin(V_ℚ)_w` fixes the base changes of `u₁`, `u₂`
  have hfix : ∀ h ∈ spinStab ℚ 3 w, ∀ y ∈ bcSubS ℚ ℂ 3 P.Pℚ,
      m ℂ 3 (bcSpin ℚ ℂ 3 h : C ℂ 3) y = y := by
    intro h hh y hy
    rw [hstab] at hh
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      rw [← s10_bcS_m_spin, hh p hp]
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hu₁c : bcS (Kd (J ℚ w)) ℂ 3 P.u₁ ∈ bcSubS ℚ ℂ 3 P.Pℚ := by
    rw [← hPK]
    exact Submodule.subset_span ⟨P.u₁, Submodule.subset_span (by simp), rfl⟩
  have hu₂c : bcS (Kd (J ℚ w)) ℂ 3 P.u₂ ∈ bcSubS ℚ ℂ 3 P.Pℚ := by
    rw [← hPK]
    exact Submodule.subset_span ⟨P.u₂, Submodule.subset_span (by simp), rfl⟩
  have hinvA : ∀ u ∈ bcSubS ℚ ℂ 3 P.Pℚ, IsInvariantUnder ℚ ℂ 3 (spinStab ℚ 3 w) (ann ℂ 3 u) :=
    fun u hu h hh v hv => s10_rho_mem_ann_of_fix _ (hfix h hh u hu) v hv
  -- complex conjugation exchanges `(W₁)_ℂ` and `(W₂)_ℂ`
  have hconj1 : (ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₁)).map (s10_conjVL s10_cc) =
      ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) := by
    rw [← s10_ann_conjS, s10_cc_bcS]
    rfl
  have hconj2 : (ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₂)).map (s10_conjVL s10_cc) =
      ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) := by
    rw [← s10_ann_conjS, s10_cc_bcS, show σS 3 (J ℚ w) P.u₂ = P.u₁ from s10_σS_σS P.u₁]
  have hne : ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) ≠ ann ℂ 3 (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) := by
    intro h
    have h1 := hT.2.2.2.2.1
    rw [← h, inf_idem] at h1
    have h2 := hT.2.2.1.2.2
    rw [h1, finrank_bot] at h2
    norm_num at h2
  refine ⟨P.W₁, P.W₂, ?_, fun W => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `W₁ ≠ W₂` (they are transversal and nonzero)
    intro h
    have h1 : P.W₁ = ⊥ := by
      have := hW.inf_eq_bot
      rwa [← h, inf_idem] at this
    have h2 : Module.finrank (Kd (J ℚ w)) P.W₁ = 2 * 3 := P.isPure.2.2
    rw [h1, finrank_bot] at h2
    norm_num at h2
  · -- the invariant maximal isotropic subspaces are `(W₁)_ℂ` and `(W₂)_ℂ` (density of
    -- `Spin(V_ℚ)_w` in `SL(W₁)`, through the unitary transvections)
    rintro ⟨hmax, hinvW⟩
    have hinvP : IsInvariantUnder ℚ ℂ 3 P.spinPℚ W := by rw [← hstab]; exact hinvW
    set W' := W.map (rho ℂ 3 gc).toLinearMap with hW'
    have hfin : Module.finrank ℂ W' = 6 := by
      rw [hW', LinearEquiv.finrank_map_eq]
      exact hmax.2
    have hback : W'.map (rho ℂ 3 gc⁻¹).toLinearMap = W := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simp only [LinearEquiv.coe_coe]
        rw [s10_rho_inv_rho]
        exact hx
      · intro hy
        exact ⟨rho ℂ 3 gc y, ⟨y, hy, rfl⟩, s10_rho_inv_rho gc y⟩
    have hN : ∀ i j : Fin 6, i ≠ j → ∀ v ∈ W', s10_N i j v ∈ W' := by
      intro i j hij v hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
      have ha : rho (Kd (J ℚ w)) 3 g⁻¹ (0, e _ 3 j) ∈ P.W₁ := by
        rw [hW1]
        exact Submodule.mem_map_of_mem
          (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, Submodule.mem_top⟩)
      have hb : rho (Kd (J ℚ w)) 3 g⁻¹ (f _ 3 i, 0) ∈ P.W₂ := by
        rw [hW2]
        exact Submodule.mem_map_of_mem
          (Submodule.mem_prod.mpr ⟨Submodule.mem_top, Submodule.zero_mem _⟩)
      have hab : pairing (Kd (J ℚ w)) 3 (rho (Kd (J ℚ w)) 3 g⁻¹ (0, e _ 3 j))
          (rho (Kd (J ℚ w)) 3 g⁻¹ (f _ 3 i, 0)) = 0 := by
        rw [s10_rho_isometry, s10_pairing_apply]
        simp [s10_f_e, hij]
      have hD := s10_D_mem P hW hd W hinvP ha hb hab x hx
      rw [s10_bcV_rho, s10_bcV_rho, s10_bcV_e, s10_bcV_f, hinv] at hD
      have e1 : s10_N i j (rho ℂ 3 gc x) = rho ℂ 3 gc
          (-s10_D (rho ℂ 3 gc⁻¹ (0, e ℂ 3 j)) (rho ℂ 3 gc⁻¹ (f ℂ 3 i, 0)) x) := by
        rw [s10_N_eq_D, ← s10_D_swap, ← s10_rho_D, s10_rho_rho_inv, s10_rho_rho_inv]
      rw [LinearEquiv.coe_coe, e1]
      exact Submodule.mem_map_of_mem (W.neg_mem hD)
    rcases s10_eq_A_or_B W' hfin hN with h | h
    · right
      rw [hW2c, ← h, hback]
    · left
      rw [hW1c, ← h, hback]
  · -- `(W₁)_ℂ = ker m_{u₁}` and `(W₂)_ℂ = ker m_{u₂}` are maximal isotropic and invariant
    rintro (rfl | rfl)
    · rw [hA1]
      exact ⟨hT.2.2.1.2, hinvA _ hu₁c⟩
    · rw [hA2]
      exact ⟨hT.2.2.2.1.2, hinvA _ hu₂c⟩
  · -- not defined over `ℚ`: a rational subspace is stable under complex conjugation, which
    -- exchanges `(W₁)_ℂ` and `(W₂)_ℂ` (since `σ(ℓ̃₁) = ℓ̃₂`, by the paper's `J`-argument in
    -- `s10_not_fixed_lines`; see `s10_cm_secant`)
    rintro ⟨W₀, hW₀⟩
    rw [hA1] at hW₀
    have := hconj1
    rw [hW₀, s10_map_conjVL_bcSubV, ← hW₀] at this
    exact hne this
  · rintro ⟨W₀, hW₀⟩
    rw [hA2] at hW₀
    have := hconj2
    rw [hW₀, s10_map_conjVL_bcSubV, ← hW₀] at this
    exact hne this.symm
  · -- `σ(W₁) = W₂`
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact s10_σV_W₁ P hx
    · intro hy
      exact ⟨σV 3 _ y, s10_σV_W₂ P hy, s10_σV_σV y⟩

/-- **Lemma 10.2.1** (`lemma-imaginary-quadratic-field-is-centralizer-sixfold-case`), second
sentence. For `w ∈ S⁺_ℚ` with `d := J(w) > 0` and `K = ℚ(√-d)`, the centralizer of
`ρ(Spin(V_ℚ)_w)` in the group `Õ(V_ℚ)` of rational similarities with multiplier in `Nm(K^×)`
(2.2.3) is isomorphic to `K^×`. -/
theorem lemma10_2_1_centralizer (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    Nonempty (↥(Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓
      Otilde 3 (J ℚ w)) ≃* (Kd (J ℚ w))ˣ) := by
  -- the centralizer is `η(K^×)` (Lemma 2.2.4, with `Spin(V_ℚ)_w = Spin(V_ℚ)_P`)
  obtain ⟨P, hW, hwP, -, -⟩ := s10_secant w hw hd
  obtain ⟨hinj, hex, hiff⟩ := s10_eta_centralizer w hw hd P hW hwP
  set G := Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓ Otilde 3 (J ℚ w)
  have hη : ∀ x : G, ∃ l : (Kd (J ℚ w))ˣ, ((x : V ℚ 3 ≃ₗ[ℚ] V ℚ 3) : V ℚ 3 →ₗ[ℚ] V ℚ 3) =
      P.η hW l := fun x => (hiff x).mp x.2
  choose f hf using hη
  have hmem : ∀ l : (Kd (J ℚ w))ˣ, (Classical.choose (hex l)) ∈ G := by
    intro l
    exact (hiff _).mpr ⟨l, (Classical.choose_spec (hex l)).2⟩
  refine ⟨{ toFun := f
            invFun := fun l => ⟨Classical.choose (hex l), hmem l⟩
            left_inv := fun x => ?_
            right_inv := fun l => ?_
            map_mul' := fun x y => ?_ }⟩
  · apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    rw [(Classical.choose_spec (hex (f x))).2, ← hf x]
  · apply hinj
    rw [← hf, (Classical.choose_spec (hex l)).2]
  · apply hinj
    rw [← hf, Units.val_mul]
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun (hf x) ((y : V ℚ 3 ≃ₗ[ℚ] V ℚ 3) v)
    have h2 := LinearMap.congr_fun (hf y) v
    simp only [LinearEquiv.coe_coe] at h1 h2
    rw [← s10_η_mul P hW, ← h2, ← h1]
    rfl

/-- (Proof of Lemma 10.2.1, l. 9792–9796, with Lemma 10.1.1.) For `w ∈ S⁺_ℚ` with
`d := J(w) > 0`, the secant `P_w` through `w` is a rational `K`-secant in the sense of §2.2: there
is `P : KSecant 3 d` (an even pure spinor `u₁ ∈ S⁺_K` and `u₂ = σ(u₁)`) with `V_K = W₁ ⊕ W₂`, whose
rational plane `P ⊆ S⁺_ℚ` contains `w`, such that `P_K ⊗ ℂ` is the transversal secant through `w`
of Lemma 10.1.1, spanned by `u₁, u₂`, and is the base change of `P` ("`P_w` is defined over
`ℚ`"). -/
theorem lemma10_2_1_secant (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w) :
    ∃ P : KSecant 3 (J ℚ w), IsCompl P.W₁ P.W₂ ∧ w ∈ P.Pℚ ∧
      IsTransversalSecant ℂ 3 (bcSubS (Kd (J ℚ w)) ℂ 3 P.PK)
        (bcS (Kd (J ℚ w)) ℂ 3 P.u₁) (bcS (Kd (J ℚ w)) ℂ 3 P.u₂) ∧
      bcSubS (Kd (J ℚ w)) ℂ 3 P.PK = bcSubS ℚ ℂ 3 P.Pℚ := by
  exact s10_secant w hw hd

/-- (Proof of Lemma 10.2.1, l. 9798, by Remark 2.2.3 with `n = 3` odd.) For `w ∈ S⁺_ℚ` with
`J(w) > 0` and a `K`-secant `P` with `V_K = W₁ ⊕ W₂` whose rational plane contains `w`,
`Spin(V_ℚ)_w = Spin(V_ℚ)_P`. -/
theorem lemma10_2_1_spinStab_eq (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    spinStab ℚ 3 w = P.spinPℚ := by
  exact s10_spinStab_eq w hw hd P hW hwP

/-- (Text after Lemma 10.2.1, l. 9842.) Let `w ∈ S⁺_ℚ` with `d := J(w) > 0`, and orient the
secant `P` through `w` (the choice of `W₁`). The homomorphism `η : K^× → GL(V_ℚ)` of (2.2.4) is
injective, its image is contained in `Õ(V_ℚ)`, and it equals the centralizer of `ρ(Spin(V_ℚ)_w)` in
`Õ(V_ℚ)` (by Lemma 2.2.4). -/
theorem eta_centralizer_spinStab (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hd : 0 < J ℚ w)
    (P : KSecant 3 (J ℚ w)) (hW : IsCompl P.W₁ P.W₂) (hwP : w ∈ P.Pℚ) :
    (∀ l l' : (Kd (J ℚ w))ˣ, P.η hW l = P.η hW l' → l = l') ∧
      (∀ l : (Kd (J ℚ w))ˣ, ∃ h ∈ Otilde 3 (J ℚ w), (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l) ∧
      ∀ h : V ℚ 3 ≃ₗ[ℚ] V ℚ 3,
        h ∈ Subgroup.centralizer (rho ℚ 3 '' (spinStab ℚ 3 w : Set (Spin ℚ 3))) ⊓
            Otilde 3 (J ℚ w) ↔
          ∃ l : (Kd (J ℚ w))ˣ, (h : V ℚ 3 →ₗ[ℚ] V ℚ 3) = P.η hW l := by
  exact s10_eta_centralizer w hw hd P hW hwP

/-! ## Example 10.2.2 -/

section Example

variable (F : Type*) [Field F] [CharZero F]

/-- The class `e_i ∧ e_j ∈ H²(X, F)` (0-based indices). -/
noncomputable def wedge2 (i j : Fin 6) : S F 3 :=
  ExteriorAlgebra.ι F (e F 3 i) * ExteriorAlgebra.ι F (e F 3 j)

/-- The class `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` of Example 10.2.2, as printed (0-based indices).
In the coordinates of §10.1 (`∫_X e₁ ∧ ⋯ ∧ e₆ = 1`) it has `Θ³ = -6 [pt_X]` (`thetaEx_cube`). -/
noncomputable def thetaEx : S F 3 := wedge2 F 0 3 + wedge2 F 1 4 + wedge2 F 2 5

/-- The class `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, with `Θ'³ = 6 [pt_X]` (`thetaEx'_cube`), i.e.
`Θ'³/3! = [pt_X]` as for a principal polarization (§8.2). -/
noncomputable def thetaEx' : S F 3 := -wedge2 F 0 3 + wedge2 F 1 4 + wedge2 F 2 5

/-! Helpers (prefix `s10_`): the classes `e_i ∧ e_j` and their products in the basis `e_K`. -/

theorem s10_wedge2_eq {i j : Fin 6} (hij : i < j) : wedge2 F i j = basisS F 3 {i, j} := by
  have hne : i ∉ ({j} : Finset (Fin 6)) := by simpa using hij.ne
  have hf : (({j} : Finset (Fin 6)).filter (· < i)).card = 0 := by
    simp [Finset.filter_singleton, not_lt.mpr hij.le]
  rw [wedge2, ← s10_basisS_singleton (F := F) (n := 3) j, s10_ι_e_mul_basisS, ite_eq_right hne, hf,
    pow_zero, one_smul]

theorem s10_B_mul_disj (K L : Finset (Fin 6)) (h : Disjoint K L) :
    basisS F 3 K * basisS F 3 L = (-1 : F) ^ s10_inv (n := 3) K L • basisS F 3 (K ∪ L) := by
  rw [s10_basisS_mul_basisS, ite_eq_left h]

theorem s10_B_mul_not_disj (K L : Finset (Fin 6)) (h : ¬ Disjoint K L) :
    basisS F 3 K * basisS F 3 L = 0 := by
  rw [s10_basisS_mul_basisS, ite_eq_right h]

/-- The products of the three classes `e₁∧e₄`, `e₂∧e₅`, `e₃∧e₆` (0-based: `{0,3}`, `{1,4}`,
`{2,5}`). -/
theorem s10_theta_products :
    basisS F 3 {0, 3} * basisS F 3 {0, 3} = 0 ∧ basisS F 3 {1, 4} * basisS F 3 {1, 4} = 0 ∧
    basisS F 3 {2, 5} * basisS F 3 {2, 5} = 0 ∧
    basisS F 3 {0, 3} * basisS F 3 {1, 4} = -basisS F 3 {0, 1, 3, 4} ∧
    basisS F 3 {1, 4} * basisS F 3 {0, 3} = -basisS F 3 {0, 1, 3, 4} ∧
    basisS F 3 {0, 3} * basisS F 3 {2, 5} = -basisS F 3 {0, 2, 3, 5} ∧
    basisS F 3 {2, 5} * basisS F 3 {0, 3} = -basisS F 3 {0, 2, 3, 5} ∧
    basisS F 3 {1, 4} * basisS F 3 {2, 5} = -basisS F 3 {1, 2, 4, 5} ∧
    basisS F 3 {2, 5} * basisS F 3 {1, 4} = -basisS F 3 {1, 2, 4, 5} := by
  refine ⟨s10_B_mul_not_disj F _ _ (by decide), s10_B_mul_not_disj F _ _ (by decide),
    s10_B_mul_not_disj F _ _ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [s10_B_mul_disj F _ _ (by decide)]
    rw [show s10_inv (n := 3) _ _ = _ from rfl]
    first
    | (rw [show ({0, 3} ∪ {1, 4} : Finset (Fin 6)) = {0, 1, 3, 4} by decide,
        show s10_inv (n := 3) ({0, 3} : Finset (Fin 6)) {1, 4} = 1 by decide]; simp)
    | (rw [show ({1, 4} ∪ {0, 3} : Finset (Fin 6)) = {0, 1, 3, 4} by decide,
        show s10_inv (n := 3) ({1, 4} : Finset (Fin 6)) {0, 3} = 3 by decide]; norm_num)
    | (rw [show ({0, 3} ∪ {2, 5} : Finset (Fin 6)) = {0, 2, 3, 5} by decide,
        show s10_inv (n := 3) ({0, 3} : Finset (Fin 6)) {2, 5} = 1 by decide]; simp)
    | (rw [show ({2, 5} ∪ {0, 3} : Finset (Fin 6)) = {0, 2, 3, 5} by decide,
        show s10_inv (n := 3) ({2, 5} : Finset (Fin 6)) {0, 3} = 3 by decide]; norm_num)
    | (rw [show ({1, 4} ∪ {2, 5} : Finset (Fin 6)) = {1, 2, 4, 5} by decide,
        show s10_inv (n := 3) ({1, 4} : Finset (Fin 6)) {2, 5} = 1 by decide]; simp)
    | (rw [show ({2, 5} ∪ {1, 4} : Finset (Fin 6)) = {1, 2, 4, 5} by decide,
        show s10_inv (n := 3) ({2, 5} : Finset (Fin 6)) {1, 4} = 3 by decide]; norm_num)

/-- The products `e_{0134} ∧ e_{25}`, etc., are `[pt_X]`, and the other products vanish. -/
theorem s10_theta_cube_products :
    basisS F 3 {0, 1, 3, 4} * basisS F 3 {2, 5} = pt F 3 ∧
    basisS F 3 {0, 2, 3, 5} * basisS F 3 {1, 4} = pt F 3 ∧
    basisS F 3 {1, 2, 4, 5} * basisS F 3 {0, 3} = pt F 3 ∧
    basisS F 3 {0, 1, 3, 4} * basisS F 3 {0, 3} = 0 ∧
    basisS F 3 {0, 1, 3, 4} * basisS F 3 {1, 4} = 0 ∧
    basisS F 3 {0, 2, 3, 5} * basisS F 3 {0, 3} = 0 ∧
    basisS F 3 {0, 2, 3, 5} * basisS F 3 {2, 5} = 0 ∧
    basisS F 3 {1, 2, 4, 5} * basisS F 3 {1, 4} = 0 ∧
    basisS F 3 {1, 2, 4, 5} * basisS F 3 {2, 5} = 0 := by
  refine ⟨?_, ?_, ?_, s10_B_mul_not_disj F _ _ (by decide), s10_B_mul_not_disj F _ _ (by decide),
    s10_B_mul_not_disj F _ _ (by decide), s10_B_mul_not_disj F _ _ (by decide),
    s10_B_mul_not_disj F _ _ (by decide), s10_B_mul_not_disj F _ _ (by decide)⟩
  · rw [s10_B_mul_disj F _ _ (by decide), show ({0, 1, 3, 4} ∪ {2, 5} : Finset (Fin 6)) =
      Finset.univ by decide, show s10_inv (n := 3) ({0, 1, 3, 4} : Finset (Fin 6)) {2, 5} = 2 by
      decide]
    norm_num
    rfl
  · rw [s10_B_mul_disj F _ _ (by decide), show ({0, 2, 3, 5} ∪ {1, 4} : Finset (Fin 6)) =
      Finset.univ by decide, show s10_inv (n := 3) ({0, 2, 3, 5} : Finset (Fin 6)) {1, 4} = 4 by
      decide]
    norm_num
    rfl
  · rw [s10_B_mul_disj F _ _ (by decide), show ({1, 2, 4, 5} ∪ {0, 3} : Finset (Fin 6)) =
      Finset.univ by decide, show s10_inv (n := 3) ({1, 2, 4, 5} : Finset (Fin 6)) {0, 3} = 6 by
      decide]
    norm_num
    rfl

theorem s10_thetaEx_eq : thetaEx F = basisS F 3 {0, 3} + basisS F 3 {1, 4} + basisS F 3 {2, 5} := by
  rw [thetaEx, s10_wedge2_eq F (by decide), s10_wedge2_eq F (by decide),
    s10_wedge2_eq F (by decide)]

theorem s10_thetaEx'_eq :
    thetaEx' F = -basisS F 3 {0, 3} + basisS F 3 {1, 4} + basisS F 3 {2, 5} := by
  rw [thetaEx', s10_wedge2_eq F (by decide), s10_wedge2_eq F (by decide),
    s10_wedge2_eq F (by decide)]

omit [CharZero F] in
theorem s10_two_smul_one : (2 : F) • (1 : S F 3) = 2 := by
  rw [Algebra.smul_def, mul_one, map_ofNat]

theorem s10_eStar_25' : eStar F 2 5 = basisS F 3 {0, 1, 3, 4} := by
  rw [s10_eStar_25, show ({2, 5}ᶜ : Finset (Fin 6)) = {0, 1, 3, 4} by decide]

theorem s10_eStar_14' : eStar F 1 4 = basisS F 3 {0, 2, 3, 5} := by
  rw [s10_eStar_14, show ({1, 4}ᶜ : Finset (Fin 6)) = {0, 2, 3, 5} by decide]

theorem s10_eStar_03' : eStar F 0 3 = basisS F 3 {1, 2, 4, 5} := by
  rw [s10_eStar_03, show ({0, 3}ᶜ : Finset (Fin 6)) = {1, 2, 4, 5} by decide]

/-- `Θ² = -2 (e₃₆^* + e₂₅^* + e₁₄^*)`. -/
theorem s10_thetaEx_sq :
    thetaEx F ^ 2 = -(2 : F) • (basisS F 3 {0, 1, 3, 4} + basisS F 3 {0, 2, 3, 5} +
      basisS F 3 {1, 2, 4, 5}) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := s10_theta_products F
  rw [s10_thetaEx_eq, sq]
  simp only [add_mul, mul_add, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  module

/-- `Θ'² = 2 (e₃₆^* + e₂₅^* - e₁₄^*)`. -/
theorem s10_thetaEx'_sq :
    thetaEx' F ^ 2 = (2 : F) • (basisS F 3 {0, 1, 3, 4} + basisS F 3 {0, 2, 3, 5} -
      basisS F 3 {1, 2, 4, 5}) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := s10_theta_products F
  rw [s10_thetaEx'_eq, sq]
  simp only [add_mul, mul_add, neg_mul, mul_neg, neg_neg, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  module

/-- The slip in Example 10.2.2: with `∫_X e₁ ∧ ⋯ ∧ e₆ = 1`, the printed
`Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` has `Θ³ = -6 [pt_X]`, whereas a principal polarization has
`Θ³/3! = [pt_X]`. -/
theorem thetaEx_cube : thetaEx F ^ 3 = (-6 : F) • pt F 3 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := s10_theta_cube_products F
  rw [pow_succ, s10_thetaEx_sq, s10_thetaEx_eq]
  simp only [smul_mul_assoc, add_mul, mul_add, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  module

/-- `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` satisfies `Θ'³ = 6 [pt_X]`. -/
theorem thetaEx'_cube : thetaEx' F ^ 3 = (6 : F) • pt F 3 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := s10_theta_cube_products F
  rw [pow_succ, s10_thetaEx'_sq, s10_thetaEx'_eq]
  simp only [smul_mul_assoc, add_mul, mul_add, sub_mul, mul_neg, c1, c2, c3, c4, c5, c6, c7, c8,
    c9]
  module

/-- **Example 10.2.2** (`example-gulbrandsen`), the computation of `Θ²` (l. 9854–9860):
`Θ² = 2[e₁∧e₄∧e₂∧e₅ + e₁∧e₄∧e₃∧e₆ + e₂∧e₅∧e₃∧e₆] = (-2)(e₃₆^* + e₂₅^* + e₁₄^*)` for the printed
`Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. -/
theorem example10_2_2_theta_sq :
    thetaEx F ^ 2 = 2 * (wedge2 F 0 3 * wedge2 F 1 4 + wedge2 F 0 3 * wedge2 F 2 5 +
        wedge2 F 1 4 * wedge2 F 2 5) ∧
      thetaEx F ^ 2 = (-2 : F) • (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := s10_theta_products F
  refine ⟨?_, ?_⟩
  · rw [s10_thetaEx_sq, s10_wedge2_eq F (by decide), s10_wedge2_eq F (by decide),
      s10_wedge2_eq F (by decide), h4, h6, h8]
    simp only [two_mul]
    module
  · rw [s10_thetaEx_sq, s10_eStar_25', s10_eStar_14', s10_eStar_03']

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9861: `w := 2 - dΘ²` equals
`2 + 2d(e₃₆^* + e₂₅^* + e₁₄^*)`, for the printed `Θ`. -/
theorem example10_2_2_w (d : F) :
    (2 : S F 3) - d • thetaEx F ^ 2 =
      2 + (2 * d) • (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) := by
  rw [(example10_2_2_theta_sq F).2, smul_smul]
  module

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9861, the intermediate steps:
`J(w) = 2⁴ d³ J(1 + (e₃₆^* + e₂₅^* + e₁₄^*))` and `J(1 + (e₃₆^* + e₂₅^* + e₁₄^*)) = 1`
(Remark 10.1.2(1) with `d = 1`), for `w = 2 - dΘ²` with the printed `Θ`. -/
theorem example10_2_2_steps (d : F) :
    J F (2 - d • thetaEx F ^ 2) =
        2 ^ 4 * d ^ 3 * J F (1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3)) ∧
      J F (1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3)) = 1 := by
  have h1 : J F (1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3)) = 1 := by
    have h := s10_J_diag F 1 1 1 1
    rw [show (1 : F) • (1 : S F 3) + (1 : F) • eStar F 0 3 + (1 : F) • eStar F 1 4 +
      (1 : F) • eStar F 2 5 = 1 + (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) by
      simp only [one_smul]; abel] at h
    rw [h]; ring
  have h2 : J F (2 - d • thetaEx F ^ 2) = 16 * d ^ 3 := by
    rw [example10_2_2_w]
    have h := s10_J_diag F 2 (2 * d) (2 * d) (2 * d)
    rw [show (2 : F) • (1 : S F 3) + (2 * d) • eStar F 0 3 + (2 * d) • eStar F 1 4 +
      (2 * d) • eStar F 2 5 = 2 + (2 * d) • (eStar F 2 5 + eStar F 1 4 + eStar F 0 3) by
      rw [s10_two_smul_one, smul_add, smul_add]; abel] at h
    rw [h]; ring
  refine ⟨?_, h1⟩
  rw [h2, h1]
  ring

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9854 and l. 9861: the Igusa invariant of
`w = 2 - dΘ²` (the Chern character of a bundle in Gulbrandsen's `M(2, 0, dΘ²)`) is
`J(w) = 16 d³`, for the printed `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. The paper takes `d` a positive
integer; the identity holds for every `d ∈ F`.
Slip of the paper: it says that `H¹(X, ℤ)` has a basis with `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` for
the principal polarization `Θ`; with the normalization `∫_X e₁ ∧ ⋯ ∧ e₆ = 1` of §10.1 this class has
`Θ³ = -6 [pt_X]` (`thetaEx_cube`), while a principal polarization has `Θ³ = 6 [pt_X]`. The value is
the same for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`, `Θ'³ = 6 [pt_X]` (`example10_2_2_principal`); in
fact `J(2 - dΘ²) = 16 d³ (∫_X Θ³ / 6)²` for every `Θ ∈ H²(X)` (checked numerically). -/
theorem example10_2_2 (d : F) : J F (2 - d • thetaEx F ^ 2) = 16 * d ^ 3 := by
  rw [(example10_2_2_steps F d).1, (example10_2_2_steps F d).2]
  ring

/-- **Example 10.2.2** (`example-gulbrandsen`) with a class `Θ'` satisfying `Θ'³ = 6 [pt_X]` (as a
principal polarization does in the orientation of §10.1), correcting the slip of the printed basis:
`J(2 - dΘ'²) = 16 d³` for `Θ' = -e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆`. -/
theorem example10_2_2_principal (d : F) : J F (2 - d • thetaEx' F ^ 2) = 16 * d ^ 3 := by
  have h := s10_J_diag F 2 (2 * d) (-(2 * d)) (-(2 * d))
  rw [show (2 : F) • (1 : S F 3) + (2 * d) • eStar F 0 3 + (-(2 * d)) • eStar F 1 4 +
    (-(2 * d)) • eStar F 2 5 = 2 - d • thetaEx' F ^ 2 by
    rw [s10_thetaEx'_sq, s10_eStar_25', s10_eStar_14', s10_eStar_03', s10_two_smul_one, smul_smul]
    module] at h
  rw [h]; ring

/-- **Example 10.2.2** (`example-gulbrandsen`), last sentence (l. 9864): `w = 2α`, where
`α = 1 - (d/2)Θ²` is the class of Lemma 8.2.1 (there `Θ³/6 = [pt_X]`; we take `Θ'`); hence
`J(α) = d³`. -/
theorem example10_2_2_alpha (d : F) :
    (2 : S F 3) - d • thetaEx' F ^ 2 = 2 * (1 - (d / 2) • thetaEx' F ^ 2) ∧
      J F (1 - (d / 2) • thetaEx' F ^ 2) = d ^ 3 := by
  refine ⟨?_, ?_⟩
  · rw [mul_sub, mul_one, two_mul ((d / 2) • thetaEx' F ^ 2), ← add_smul, add_halves]
  · have h := s10_J_diag F 1 d (-d) (-d)
    rw [show (1 : F) • (1 : S F 3) + d • eStar F 0 3 + (-d) • eStar F 1 4 + (-d) • eStar F 2 5 =
      1 - (d / 2) • thetaEx' F ^ 2 by
      rw [s10_thetaEx'_sq, s10_eStar_25', s10_eStar_14', s10_eStar_03', one_smul, smul_smul]
      have : d / 2 * 2 = d := by field_simp
      rw [this]
      module] at h
    rw [h]; ring

/-- **Example 10.2.2** (`example-gulbrandsen`), l. 9854, "so that `K = ℚ(√-d)`": for `d > 0` the
field `ℚ(√-J(w))`, `w = 2 - dΘ²`, is `ℚ(√-d)`, for the printed `Θ` and for `Θ'`. -/
theorem example10_2_2_field (d : ℚ) (hd : 0 < d) :
    Kd (J ℚ (2 - d • thetaEx ℚ ^ 2)) = Kd d ∧ Kd (J ℚ (2 - d • thetaEx' ℚ ^ 2)) = Kd d := by
  -- `√-(16 d³) = 4d √-d`, so both generate the same field
  have hsq : sqrtNeg (16 * d ^ 3) = ((4 * d : ℚ) : ℂ) * sqrtNeg d := by
    have hd' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
    have h4 : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
    have hr : Real.sqrt ((16 * d ^ 3 : ℚ) : ℝ) = 4 * (d : ℝ) * Real.sqrt (d : ℝ) := by
      rw [show ((16 * d ^ 3 : ℚ) : ℝ) = (4 * (d : ℝ)) ^ 2 * (d : ℝ) by push_cast; ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h4]
    simp only [sqrtNeg, hr]
    push_cast
    ring
  have hK : Kd (16 * d ^ 3) = Kd d := by
    have hq : ((4 * d : ℚ) : ℂ) ≠ 0 := by
      have : (4 * d : ℚ) ≠ 0 := by positivity
      exact_mod_cast this
    apply le_antisymm
    · apply Subfield.closure_le.mpr
      rintro _ rfl
      rw [hsq]
      exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure rfl)
    · apply Subfield.closure_le.mpr
      rintro _ rfl
      have h1 : sqrtNeg (16 * d ^ 3) ∈ Kd (16 * d ^ 3) := Subfield.subset_closure rfl
      rw [hsq] at h1
      have h2 : sqrtNeg d = ((((4 * d : ℚ) : ℂ))⁻¹) * (((4 * d : ℚ) : ℂ) * sqrtNeg d) := by
        field_simp
      rw [h2]
      exact mul_mem (by rw [← Rat.cast_inv]; exact SubfieldClass.ratCast_mem _ _) h1
  exact ⟨by rw [example10_2_2, hK], by rw [example10_2_2_principal, hK]⟩

end Example

/-! ## Example 10.2.3 -/

/-- **Example 10.2.3** (no label). The Igusa invariant of `1 - m[pt_X]` (the Chern character of the
ideal sheaf of a zero-dimensional subscheme of length `m`; the paper's `n`) is
`J(1 - m[pt_X]) = -(1/4) m² = -(m/2)²`. -/
theorem example10_2_3 (F : Type*) [Field F] [CharZero F] (m : ℕ) :
    J F (1 - (m : F) • pt F 3) = -(1 / 4) * (m : F) ^ 2 ∧
      -(1 / 4) * (m : F) ^ 2 = -((m : F) / 2) ^ 2 := by
  refine ⟨?_, by ring⟩
  rw [sub_eq_add_neg, ← neg_smul, J_one_add_smul_pt]
  ring

/-- **Example 10.2.3** (no label), "and so `K = ℚ`": `-J(1 - m[pt_X])` is the square of a rational
number, so `ℚ(√-J(1 - m[pt_X])) = ℚ`. -/
theorem example10_2_3_field (m : ℕ) : IsSquare (-J ℚ (1 - (m : ℚ) • pt ℚ 3)) := by
  rw [(example10_2_3 ℚ m).1]
  exact ⟨(m : ℚ) / 2, by ring⟩

end WeilClasses
