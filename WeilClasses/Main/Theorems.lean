module

public import WeilClasses.Main.Compare
public import WeilClasses.Main.Intro
public import WeilClasses.AbelianVariety.Lemmas

/-!
# The main results in the model (Theorems 1.4.1 (3), (4), 1.5.1, Corollary 1.6.1)

The statements of record (`Challenge.lean`) in the library: Theorem 1.4.1 (3), (4) for the explicit
polarized abelian sixfold of Weil type `X × X̂` of `WeilClasses.Defs` (`fX`, `hX`, `JX`, `kappaX`),
Theorem 1.5.1 and Corollary 1.6.1 for a system of algebraic classes `Z` satisfying the hypotheses of
`WeilClasses.Defs`, and the compared theorems that check the definitions of the block.

* Theorem 1.4.1 (3), (4) follow from the paper's versions for the secant `P_Θ`
  (`WeilClasses.Main.Intro`) through the bridges of `WeilClasses.Main.Compare` (`f = η(√-d)`,
  `h = Ξ_P^♯`, the standard complex structure `-I_{V_ℝ}`, `coordV`).
* Theorem 1.5.1 follows the proof in §9.3: discriminant `-1` of `X × X̂` (Lemma 3.1.3 for `n = 3`),
  `κ₃(E)` algebraic near `X × X̂` (`SecantSheafDeformation`), its `η(K)`-translates algebraic
  (`PullbackClosed`), `h³` algebraic (`LefschetzOneOne`, `SubalgebraClosed`), hence `ĤW` algebraic
  near `X × X̂` (Theorem 1.4.1(4)), on the whole connected component (`VoisinLocus`), and on every
  polarized abelian sixfold of Weil type with discriminant `-1` (`VanGeemenModuli`,
  `PullbackClosed`).
  For `d ∈ {1, 2}` the proof uses `ℚ(√-4d) = ℚ(√-d)`.
* Corollary 1.6.1 follows its proof (§1.6), with Lefschetz (1,1) and hard Lefschetz in the degrees
  other than `4`.
-/

@[expose] public section

namespace WeilClasses

/-! ### A principally polarized abelian `n`-fold: the standard complex structure `J₀`

`ThetaStd = Σ e_{2i} ∧ e_{2i+1}` is ample for `J₀ e_{2i} = -e_{2i+1}`, `J₀ e_{2i+1} = e_{2i}` (the
torus `ℂⁿ/(ℤⁿ + iℤⁿ)`). The statements of Theorem 1.4.1(4) in the model and of the discriminant of
`X × X̂` involve no complex structure; the paper's versions are stated for an `X` on which `Θ` is
ample (the Jacobian of a genus-`3` curve in §8), and `J₀` provides one. -/

section StdComplex

variable (n : ℕ)

/-- The involution `2i ↔ 2i + 1` of `Fin (2n)`. -/
def main_swap (k : Fin (2 * n)) : Fin (2 * n) :=
  ⟨if k.val % 2 = 0 then k.val + 1 else k.val - 1, by split_ifs <;> omega⟩

/-- The sign `+1` on even, `-1` on odd indices. -/
def main_sgn (k : Fin (2 * n)) : ℝ := if k.val % 2 = 0 then 1 else -1

theorem main_swap_swap (k : Fin (2 * n)) : main_swap n (main_swap n k) = k := by
  ext; simp only [main_swap]; split_ifs <;> omega

theorem main_sgn_swap (k : Fin (2 * n)) : main_sgn n (main_swap n k) = -main_sgn n k := by
  simp only [main_sgn, main_swap]; split_ifs <;> (try norm_num) <;> omega

theorem main_swap_even (i : Fin n) :
    main_swap n ⟨2 * i, by omega⟩ = ⟨2 * i + 1, by omega⟩ := by
  ext; simp [main_swap]

theorem main_swap_odd (i : Fin n) :
    main_swap n ⟨2 * i + 1, by omega⟩ = ⟨2 * i, by omega⟩ := by
  ext; simp only [main_swap]; split_ifs <;> omega

theorem main_sgn_even (i : Fin n) : main_sgn n ⟨2 * i, by omega⟩ = 1 := by
  simp [main_sgn]

theorem main_sgn_odd (i : Fin n) : main_sgn n ⟨2 * i + 1, by omega⟩ = -1 := by
  simp only [main_sgn]; split_ifs <;> first | rfl | omega

theorem main_swap_eq_iff (k j : Fin (2 * n)) : main_swap n k = j ↔ k = main_swap n j := by
  constructor
  · rintro rfl; rw [main_swap_swap]
  · rintro rfl; rw [main_swap_swap]

/-- The matrix of the standard complex structure `J₀`. -/
noncomputable def main_M0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun k j => if j = main_swap n k then main_sgn n k else 0

/-- The standard complex structure `J₀` of `H¹(X, ℝ) = ℝ^{2n}`: `J₀ e_{2i} = -e_{2i+1}`,
`J₀ e_{2i+1} = e_{2i}`. -/
noncomputable def main_J0 : Module.End ℝ (H1 ℝ n) := Matrix.toLin' (main_M0 n)

theorem main_J0_apply (x : H1 ℝ n) (k : Fin (2 * n)) :
    main_J0 n x k = main_sgn n k * x (main_swap n k) := by
  simp [main_J0, main_M0, Matrix.mulVec, dotProduct]

theorem main_J0_isComplex : IsComplexStructure (main_J0 n) := by
  refine LinearMap.ext fun x => funext fun k => ?_
  simp only [Module.End.mul_apply, main_J0_apply, main_swap_swap, main_sgn_swap]
  simp only [LinearMap.neg_apply, Module.End.one_apply, Pi.neg_apply]
  have : main_sgn n k * main_sgn n k = 1 := by
    simp only [main_sgn]; split_ifs <;> norm_num
  linear_combination (-(x k)) * this

theorem main_complexify_J0_apply (v : H1 ℂ n) (k : Fin (2 * n)) :
    complexifyH1 n (main_J0 n) v k = (main_sgn n k : ℂ) * v (main_swap n k) := by
  simp only [complexifyH1, main_J0, LinearMap.toMatrix_eq_toMatrix', Matrix.toLin_eq_toLin',
    LinearMap.toMatrix'_toLin', Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    main_M0]
  simp [apply_ite (fun r : ℝ => (r : ℂ)), ite_mul, Finset.sum_ite_eq']

theorem main_J0_e_even (i : Fin n) :
    main_J0 n (e ℝ n ⟨2 * i, by omega⟩) = -e ℝ n ⟨2 * i + 1, by omega⟩ := by
  funext k
  rw [main_J0_apply]
  simp only [e, Pi.single_apply, main_swap_eq_iff, main_swap_even, Pi.neg_apply]
  split_ifs with h
  · subst h; rw [main_sgn_odd]; ring
  · ring

theorem main_J0_e_odd (i : Fin n) :
    main_J0 n (e ℝ n ⟨2 * i + 1, by omega⟩) = e ℝ n ⟨2 * i, by omega⟩ := by
  funext k
  rw [main_J0_apply]
  simp only [e, Pi.single_apply, main_swap_eq_iff, main_swap_odd]
  split_ifs with h
  · subst h; rw [main_sgn_even]; ring
  · ring

/-- `e_{2i} + i e_{2i+1} ∈ H^{1,0}` for `J₀`. -/
theorem main_mem_H10_J0 (i : Fin n) :
    e ℂ n ⟨2 * i, by omega⟩ + Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩ ∈ H10 n (main_J0 n) := by
  rw [H10, Module.End.mem_eigenspace_iff]
  funext k
  rw [main_complexify_J0_apply]
  simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, main_swap_eq_iff,
    main_swap_even, main_swap_odd]
  by_cases h1 : k = ⟨2 * i, by omega⟩
  · subst h1
    have : (⟨2 * i, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by simp
    simp [main_sgn_even, this]
  · by_cases h2 : k = ⟨2 * i + 1, by omega⟩
    · subst h2
      simp [main_sgn_odd, h1]
    · simp [h1, h2]

/-- `e_{2i} - i e_{2i+1} ∈ H^{0,1}` for `J₀`. -/
theorem main_mem_H01_J0 (i : Fin n) :
    e ℂ n ⟨2 * i, by omega⟩ - Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩ ∈ H01 n (main_J0 n) := by
  rw [H01, Module.End.mem_eigenspace_iff]
  funext k
  rw [main_complexify_J0_apply]
  simp only [e, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, main_swap_eq_iff,
    main_swap_even, main_swap_odd]
  by_cases h1 : k = ⟨2 * i, by omega⟩
  · subst h1
    have : (⟨2 * i, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by simp
    simp [main_sgn_even, this]
  · by_cases h2 : k = ⟨2 * i + 1, by omega⟩
    · subst h2
      simp [main_sgn_odd, h1]
    · simp [h1, h2]

/-- `ThetaStd` is ample for the standard complex structure `J₀`. -/
theorem main_ample_J0 : IsAmple n (main_J0 n) (ThetaStd ℚ n) := by
  refine ⟨(mem_hodgeClassesX_iff n _ 1 _).mpr ⟨ThetaStd_mem n, ?_⟩, fun a ha => ?_⟩
  · rw [main_bcS_ThetaStd]
    refine Submodule.sum_mem _ fun i _ => ?_
    set v := e ℂ n ⟨2 * i, by omega⟩ + Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩
    set w := e ℂ n ⟨2 * i, by omega⟩ - Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩
    have key : ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) *
        ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩) =
        (Complex.I / 2) • (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) := by
      have hc : ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩) *
          ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) =
          -(ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) *
            ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      simp only [v, w, map_add, map_sub, map_smul, add_mul, mul_sub,
        smul_mul_assoc, mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, hc]
      match_scalars
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨![v], ![w], ?_, ?_, ?_⟩)
    · intro j; fin_cases j; exact main_mem_H10_J0 n i
    · intro j; fin_cases j; exact main_mem_H01_J0 n i
    · simp [ExteriorAlgebra.ιMulti_apply]
  · have hsum : eval2 ℝ n (ThetaStd ℝ n) a (a ∘ₗ main_J0 n) =
        ∑ i : Fin n, ((a (e ℝ n ⟨2 * i, by omega⟩)) ^ 2 +
          (a (e ℝ n ⟨2 * i + 1, by omega⟩)) ^ 2) := by
      rw [main_eval2_eq, ThetaStd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← main_eval2_eq, main_eval2_ι_mul_ι]
      simp only [LinearMap.comp_apply, main_J0_e_even, main_J0_e_odd, map_neg]
      ring
    rw [main_bcS_ThetaStd, hsum]
    obtain ⟨k, hk⟩ : ∃ k, a (e ℝ n k) ≠ 0 := by
      by_contra! h
      exact ha ((Pi.basisFun ℝ (Fin (2 * n))).ext fun k => by simpa [e] using h k)
    refine Finset.sum_pos' (fun i _ => by positivity)
      ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k.val with h | h
    · have hk' : k = ⟨2 * (k.val / 2), by omega⟩ := Fin.ext (by simp; omega)
      rw [← hk']
      have := sq_pos_of_ne_zero hk
      positivity
    · have hk' : k = ⟨2 * (k.val / 2) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [← hk']
      have := sq_pos_of_ne_zero hk
      positivity

end StdComplex

/-! ### Helpers for Theorem 1.5.1: transport of Hodge–Weil classes -/

/-- The Hodge–Weil classes of an endomorphism `T` with eigenvalues `±s` over a subfield `K`. -/
noncomputable def main_hwOf (K : Subfield ℂ) (m : ℕ) (T : Module.End ℚ (H1 ℚ (2 * m))) (s : K) :
    Submodule ℚ (S ℚ (2 * m)) :=
  ⋀[ℚ]^(2 * m) (H1 ℚ (2 * m)) ⊓
    ((topWedge (Module.End.eigenspace (bcMap ℚ K T) s) (2 * m) ⊔
      topWedge (Module.End.eigenspace (bcMap ℚ K T) (-s)) (2 * m)).restrictScalars ℚ).comap
      (bcS ℚ K (2 * m)).toLinearMap

theorem main_HWof_eq {m : ℕ} {d : ℚ} (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * m))) :
    HWof η = main_hwOf (Kd d) m (η (Kd.sqrtNeg d)) (Kd.sqrtNeg d) := rfl

theorem main_hwOf_congr {K₁ K₂ : Subfield ℂ} (h : K₁ = K₂) (m : ℕ)
    (T : Module.End ℚ (H1 ℚ (2 * m))) (s₁ : K₁) (s₂ : K₂) (hs : (s₁ : ℂ) = s₂) :
    main_hwOf K₁ m T s₁ = main_hwOf K₂ m T s₂ := by
  subst h
  rw [Subtype.ext hs]

theorem main_hwOf_smul (K : Subfield ℂ) (m : ℕ) (T : Module.End ℚ (H1 ℚ (2 * m))) (s : K) (c : ℚ)
    (hc : c ≠ 0) : main_hwOf K m (c • T) (c • s) = main_hwOf K m T s := by
  have hc' : algebraMap ℚ K c ≠ 0 := by simpa using hc
  have h1 : c • s = algebraMap ℚ K c * s := Algebra.smul_def c s
  have h2 : -(c • s) = algebraMap ℚ K c * (-s) := by rw [h1, mul_neg]
  rw [main_hwOf, main_hwOf, main_bcMap_smul, h2, h1, main_eigenspace_smul _ _ _ hc',
    main_eigenspace_smul _ _ _ hc']

/-- Hodge–Weil classes are natural under `K`-linear maps: if `ψ η(√-d) = η'(√-d) ψ`, then
`ψ` maps `ĤW(η)` into `ĤW(η')`. -/
theorem main_map_mem_HWof {m : ℕ} {d : ℚ} (η η' : Kd d →+* Module.End ℚ (H1 ℚ (2 * m)))
    (ψ : Module.End ℚ (H1 ℚ (2 * m))) (hψ : ψ ∘ₗ η (Kd.sqrtNeg d) = η' (Kd.sqrtNeg d) ∘ₗ ψ)
    {α : S ℚ (2 * m)} (hα : α ∈ HWof η) : ExteriorAlgebra.map ψ α ∈ HWof η' := by
  rw [HWof, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem] at hα ⊢
  refine ⟨main_map_mem_exteriorPower ψ _ hα.1, ?_⟩
  rw [AlgHom.toLinearMap_apply] at hα ⊢
  rw [main_bcS_map]
  have hcomm : bcMap ℚ (Kd d) ψ ∘ₗ bcMap ℚ (Kd d) (η (Kd.sqrtNeg d)) =
      bcMap ℚ (Kd d) (η' (Kd.sqrtNeg d)) ∘ₗ bcMap ℚ (Kd d) ψ := by
    rw [← main_bcMap_comp, hψ, main_bcMap_comp]
  have heig : ∀ μ, ∀ v ∈ Module.End.eigenspace (bcMap ℚ (Kd d) (η (Kd.sqrtNeg d))) μ,
      bcMap ℚ (Kd d) ψ v ∈ Module.End.eigenspace (bcMap ℚ (Kd d) (η' (Kd.sqrtNeg d))) μ := by
    intro μ v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply, hv, map_smul]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hα.2
  rw [← hyz, map_add]
  exact Submodule.add_mem_sup (main_map_mem_topWedge _ _ _ (heig _) _ hy)
    (main_map_mem_topWedge _ _ _ (heig _) _ hz)

/-- `√-4d = 2√-d`. -/
theorem main_sqrtNeg_four_mul (d : ℚ) : sqrtNeg (4 * d) = 2 * sqrtNeg d := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  simp only [sqrtNeg]
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  push_cast; ring

/-- `ℚ(√-4d) = ℚ(√-d)` (footnote in §1.5). -/
theorem main_Kd_four_mul (d : ℚ) : Kd (4 * d) = Kd d := by
  have h2 : ∀ K : Subfield ℂ, (2 : ℂ) ∈ K := fun K => by
    simp
  apply le_antisymm
  · rw [Kd, Subfield.closure_le, Set.singleton_subset_iff, main_sqrtNeg_four_mul d]
    exact Subfield.mul_mem _ (h2 _) (Subfield.subset_closure rfl)
  · rw [Kd, Subfield.closure_le, Set.singleton_subset_iff]
    have : sqrtNeg d = (2 : ℂ)⁻¹ * sqrtNeg (4 * d) := by
      rw [main_sqrtNeg_four_mul d]; field_simp
    rw [this]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (h2 _)) (Subfield.subset_closure rfl)

theorem main_norm_congr {K₁ K₂ : Subfield ℂ} (h : K₁ = K₂) (x : K₁) (y : K₂)
    (hxy : (x : ℂ) = y) : Algebra.norm ℚ x = Algebra.norm ℚ y := by
  subst h; rw [Subtype.ext hxy]

theorem main_subfieldCongr_coe {s t : Subfield ℂ} (h : s = t) (x : s) :
    ((RingEquiv.subfieldCongr h x : t) : ℂ) = x := rfl

/-- **Transport from `d` to `4d`** (`ℚ(√-4d) = ℚ(√-d)`, `η(√-4d) = 2 η(√-d)`): a polarized abelian
variety of Weil type for `ℚ(√-d)` is one for `ℚ(√-4d)`, with the same Hodge–Weil classes and the
same discriminant class. -/
theorem main_exists_four_mul {m : ℕ} {A : AbVar (2 * m)} {d d' : ℚ} (hd : 0 < d)
    (hd' : d' = 4 * d) (X : PolarizedWeilType A d) (hdisc : X.DiscIs (-1)) :
    ∃ X' : PolarizedWeilType A d', X'.HW = X.HW ∧ X'.DiscIs (-1) := by
  have hK : Kd d' = Kd d := by rw [hd']; exact main_Kd_four_mul d
  set e : Kd d' ≃+* Kd d := RingEquiv.subfieldCongr hK with he_def
  have he : ∀ k : Kd d', ((e k : Kd d) : ℂ) = k := fun k => main_subfieldCongr_coe hK k
  have hs' : sqrtNeg d' = 2 * sqrtNeg d := by rw [hd', main_sqrtNeg_four_mul d]
  have hes : e (Kd.sqrtNeg d') = (2 : ℚ) • Kd.sqrtNeg d := by
    apply Subtype.ext
    rw [he]
    change sqrtNeg d' = ((2 : ℚ) • Kd.sqrtNeg d : Kd d)
    rw [hs', two_smul, Subfield.coe_add]
    simp only [Kd.sqrtNeg]
    ring
  set T := X.η (Kd.sqrtNeg d) with hT
  set η' : Kd d' →+* Module.End ℚ (H1 ℚ (2 * m)) := X.η.comp e.toRingHom with hη'_def
  have hη' : η' (Kd.sqrtNeg d') = (2 : ℚ) • T := by
    rw [hη'_def, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hes,
      two_smul, map_add, ← two_smul ℚ]
  have hweil₁ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η' (Kd.sqrtNeg d')))
      (sqrtNeg d') ⊓ H10 (2 * m) A.J) = m := by
    rw [hη', main_bcMap_smul, hs',
      show (2 : ℂ) * sqrtNeg d = algebraMap ℚ ℂ 2 * sqrtNeg d by norm_num,
      main_eigenspace_smul _ _ _ (by norm_num)]
    exact X.weil₁
  have hweil₂ : Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (η' (Kd.sqrtNeg d')))
      (-sqrtNeg d') ⊓ H10 (2 * m) A.J) = m := by
    rw [hη', main_bcMap_smul, hs',
      show -((2 : ℂ) * sqrtNeg d) = algebraMap ℚ ℂ 2 * (-sqrtNeg d) by rw [map_ofNat]; ring,
      main_eigenspace_smul _ _ _ (by norm_num)]
    exact X.weil₂
  have hnorm : ∀ k : Kd d', Kd.Nm d' k = Kd.Nm d (e k) := fun k =>
    main_norm_congr hK k (e k) (he k).symm
  let X' : PolarizedWeilType A d' :=
    { η := η', isHodge := fun k => X.isHodge (e k), weil₁ := hweil₁, weil₂ := hweil₂,
      h := X.h, ample := X.ample, norm := fun k => by rw [hnorm]; exact X.norm (e k) }
  have hfT : ∀ y, X'.fT y = (2 : ℚ) • X.fT y := by
    intro y
    simp only [PolarizedWeilType.fT, X', hη', LinearMap.dualMap_apply', LinearMap.comp_smul]
    rfl
  have hherm : ∀ x y, X'.herm x y = 2 * X.herm x y := by
    intro x y
    simp only [PolarizedWeilType.herm, PolarizedWeilType.E, hfT, main_eval2_smul_right, hs']
    simp only [X']
    push_cast
    ring
  refine ⟨X', ?_, ?_⟩
  · show HWof η' = HWof X.η
    rw [main_HWof_eq, main_HWof_eq,
      main_hwOf_congr hK m _ (Kd.sqrtNeg d') (e (Kd.sqrtNeg d')) (he _).symm, hes, hη',
      main_hwOf_smul _ _ _ _ _ two_ne_zero]
  · obtain ⟨b, hb, k, hk, hdet⟩ := hdisc
    refine ⟨b, ?_, e.symm (((2 : ℚ) ^ m) • k), ?_, ?_⟩
    · have : (Sum.elim b fun i => X'.fT (b i)) =
          (Sum.elim (fun _ : Fin (2 * m) => (1 : ℚˣ))
            (fun _ : Fin (2 * m) => Units.mk0 (2 : ℚ) two_ne_zero)) •
            (Sum.elim b fun i => X.fT (b i)) := by
        funext j; cases j <;> simp [hfT]
      rw [this]
      exact hb.units_smul _
    · simp [hk]
    · have hmat : (Matrix.of fun i j => X'.herm (b i) (b j)) =
          (2 : ℂ) • Matrix.of fun i j => X.herm (b i) (b j) := by
        ext i j; simp [hherm]
      rw [hmat, Matrix.det_smul, hdet, hnorm, RingEquiv.apply_symm_apply]
      have h1 := Kd.coe_Nm hd k
      have h2 := Kd.coe_Nm hd (((2 : ℚ) ^ m) • k)
      rw [h1, h2]
      simp only [Fintype.card_fin]
      push_cast
      simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
      ring

/-- `x ∈ ⊕_p H^{p,p}` has its degree-`2k` component in `H^{k,k}`. -/
theorem main_projDeg_mem_hodgeClassesV {n : ℕ} {I : Module.End ℝ (V ℝ n)} {x : ExtV ℚ n}
    (hx : x ∈ hodgeRingV n I) (k : ℕ) : projDeg ℚ n (2 * k) x ∈ hodgeClassesV n I k := by
  refine Submodule.iSup_induction _ (motive := fun x => projDeg ℚ n (2 * k) x ∈ hodgeClassesV n I k)
    hx (fun p y hy => ?_) ?_ (fun y z hy hz => ?_)
  · rw [projDeg, main_proj_of_mem ((mem_hodgeClassesV_iff n I p y).mp hy).1]
    split_ifs with h
    · rwa [show k = p by omega]
    · exact Submodule.zero_mem _
  · rw [map_zero]; exact Submodule.zero_mem _
  · rw [map_add]; exact Submodule.add_mem _ hy hz

theorem main_map_conj_map {n : ℕ} (T : Module.End ℚ (V ℚ n)) (y : ExtV ℚ n) :
    ExteriorAlgebra.map (↑(coordV ℚ n) ∘ₗ T ∘ₗ ↑(coordV ℚ n).symm)
        (ExteriorAlgebra.map (coordV ℚ n).toLinearMap y) =
      ExteriorAlgebra.map (coordV ℚ n).toLinearMap (ExteriorAlgebra.map T y) := by
  have hcomp : (↑(coordV ℚ n) ∘ₗ T ∘ₗ ↑(coordV ℚ n).symm) ∘ₗ (coordV ℚ n).toLinearMap =
      (coordV ℚ n).toLinearMap ∘ₗ T := by
    refine LinearMap.ext fun x => ?_; simp
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hcomp, ← ExteriorAlgebra.map_comp_map,
    AlgHom.comp_apply]

/-! ### Compared theorems -/

/-- `Nm(a + b√-d) = a² + d b²`. -/
theorem Kd_Nm (d : ℚ) (hd : 0 < d) (a b : ℚ) :
    Kd.Nm d ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d) = a ^ 2 + d * b ^ 2 := by
  have h := Kd.coe_Nm hd ((a : Kd d) + (b : Kd d) * Kd.sqrtNeg d)
  apply_fun ((↑) : ℚ → ℂ) using Rat.cast_injective
  rw [h]
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hd.le)]
    simp
  simp only [Kd.sqrtNeg, WeilClasses.sqrtNeg, Subfield.coe_add, Subfield.coe_mul, map_add, map_mul,
    SubfieldClass.coe_ratCast, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  linear_combination (b : ℂ) ^ 2 * hs -
    (b : ℂ) ^ 2 * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 * Complex.I_sq

/-- `f² = -d` on `H¹(X × X̂, ℚ)` in the model. -/
theorem fX_mul_self (n : ℕ) (d : ℚ) : fX n d * fX n d = -(d • 1) := by
  have h := fV_mul_self n d
  refine LinearMap.ext fun x => ?_
  simp only [fX, transportEnd, Module.End.mul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [← Module.End.mul_apply (fV n d), h]
  simp

/-- `X × X̂` with `(η, h)` is a polarized abelian `2n`-fold of Weil type (§2.4: Lemma 2.2.6,
Proposition 2.4.4; Lemma 3.2.1, Corollary 3.2.3): its complex structure lies in its Weil-type period
domain. -/
theorem JX_mem_weilDomain (n : ℕ) (d : ℚ) (hd : 0 < d)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hΘ : IsAmple n J (ThetaStd ℚ n))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n))) (hη : η (Kd.sqrtNeg d) = fX n d) :
    JX n J ∈ WeilDomain η (hX n d) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: the zero-dimensional abelian variety
    have hh0 : hX 0 d = 0 := by simp [hX, hV, ThetaV, ThetaHatV]
    have hsub : ∀ x y : H1 ℝ (2 * 0), x = y := fun x y => funext fun i => i.elim0
    have hfin : ∀ U : Submodule ℂ (H1 ℂ (2 * 0)), Module.finrank ℂ U = 0 := fun U =>
      Nat.le_zero.mp ((Submodule.finrank_le U).trans (by simp))
    refine ⟨?_, fun k => ?_, hfin _, hfin _, ⟨?_, fun a ha => ?_⟩, fun k => ?_⟩
    · exact LinearMap.ext fun x => hsub _ _
    · exact LinearMap.ext fun x => hsub _ _
    · rw [hh0]; exact Submodule.zero_mem _
    · exact absurd (LinearMap.ext fun x => by rw [hsub x 0, map_zero, map_zero]) ha
    · rw [hh0, map_zero, smul_zero]
  · -- the complex structure of `X × X̂` is `-I_{V_ℝ}`, with `I_{V_ℝ} ∈ Ω_P` (Lemma 4.0.1)
    rw [weilDomain_eq_image_OmegaP n d hd hn η hη]
    exact ⟨productStructure n J, productStructure_mem_OmegaP hd hn J hJ (ThetaStd ℚ n) hΘ,
      by simp only [JX, stdStructure_eq_neg]⟩

/-- The discriminant of `X × X̂` is `(-1)ⁿ` (Lemma 3.1.3, for van Geemen's Hermitian form): every
polarized abelian `2n`-fold of Weil type with the action and the polarization of `X × X̂` has
discriminant `(-1)ⁿ`. -/
theorem discIs_XXhat (n : ℕ) (d : ℚ) (hd : 0 < d) (A : AbVar (2 * n)) (X : PolarizedWeilType A d)
    (hη : X.η (Kd.sqrtNeg d) = fX n d) (hh : X.h = hX n d) : X.DiscIs ((-1) ^ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty (Fin (2 * 0)) := Fin.isEmpty'
    refine ⟨Fin.elim0, linearIndependent_empty_type, 1, one_ne_zero, ?_⟩
    simp [Kd.Nm]
  · -- Lemma 3.1.3 for `P_Θ`, `Θ = ThetaStd` (ample for `J₀`)
    obtain ⟨b, hb, q, ⟨z, hz, rfl⟩, hdet⟩ := lemma3_1_3 hd hn (main_J0 n) (main_J0_isComplex n)
      (ThetaStd ℚ n) (main_ample_J0 n)
    set P := PStd n d hd hn
    set hW := PStd_isCompl n d hd hn
    have hf : P.fη hW = fV n d := fη_PStd n d hd hn
    set ι : V ℚ n →ₗ[ℚ] Module.Dual ℚ (H1 ℚ (2 * n)) :=
      LinearMap.lcomp ℚ ℚ (coordV ℚ n).symm.toLinearMap ∘ₗ pairing ℚ n with hι
    have hιapp : ∀ x w, ι x w = pairing ℚ n x ((coordV ℚ n).symm w) := fun x w => rfl
    have hιφ : ∀ x, ι x ∘ₗ (coordV ℚ n).toLinearMap = pairing ℚ n x := fun x =>
      LinearMap.ext fun v => by simp [hιapp]
    have hE : ∀ x y, X.E (ι x) (ι y) = P.XiQ hW x y := by
      intro x y
      rw [PolarizedWeilType.E, hh, eval2, hX, D, main_contractLeft_map, main_contractLeft_map,
        hιφ, hιφ, main_coord_empty, AlgHom.toLinearMap_apply, main_algebraMapInv_map]
      exact hV_eq_XiQ n d hd hn x y
    have hfT : ∀ y, X.fT (ι y) = ι (-(P.fη hW y)) := by
      intro y
      refine LinearMap.ext fun w => ?_
      rw [PolarizedWeilType.fT, hη, LinearMap.dualMap_apply, hιapp, hιapp, map_neg,
        LinearMap.neg_apply, hf, fX, transportEnd]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply]
      rw [← hf, main_pairing_comm, P.pairing_fη_left hW, main_pairing_comm]
    have hherm : ∀ x y, X.herm (ι x) (ι y) = -((P.hermH hW y x : Kd d) : ℂ) := by
      intro x y
      rw [PolarizedWeilType.herm, hfT, hE, hE]
      simp only [KSecant.XiQ, KSecant.hermH, map_neg, Subfield.coe_add, Subfield.coe_mul,
        LinearMap.BilinForm.compLeft_apply, P.pairing_fη_fη hW, P.pairing_fη_left hW y x,
        main_pairing_comm ℚ n y (P.fη hW x), main_pairing_comm ℚ n y x,
        eq_ratCast (algebraMap ℚ (Kd d)), SubfieldClass.coe_ratCast]
      simp only [Kd.sqrtNeg]
      push_cast
      ring
    refine ⟨fun i => ι (b i), ?_, z, hz, ?_⟩
    · -- a `K`-basis of `V_ℚ` gives one of `H₁(A, ℚ)` (`ι` is injective)
      have hιinj : Function.Injective ι := by
        intro x y hxy
        refine sub_eq_zero.mp (main_pairing_eq_zero ℚ n _ fun v => ?_)
        have := congrArg (fun f => f (coordV ℚ n v)) hxy
        simp only [hιapp, LinearEquiv.symm_apply_apply] at this
        rw [map_sub, LinearMap.sub_apply, this, sub_self]
      have : (Sum.elim (fun i => ι (b i)) fun i => X.fT (ι (b i))) =
          ι ∘ ((Sum.elim (fun _ : Fin (2 * n) => (1 : ℚˣ)) (fun _ : Fin (2 * n) => -1)) •
            Sum.elim b fun i => P.fη hW (b i)) := by
        funext j; cases j <;> simp [hfT]
      rw [this]
      exact (hb.units_smul _).map' ι (LinearMap.ker_eq_bot.mpr hιinj)
    · -- the Gram matrix of van Geemen's form is `-ᵗH`, whose determinant is `det H`
      have hmat : (Matrix.of fun i j => X.herm (ι (b i)) (ι (b j))) =
          -((P.gramH hW b).transpose.map (Kd d).subtype) := by
        ext i j; simp [hherm, KSecant.gramH]
      rw [hmat, Matrix.det_neg,
        show ((P.gramH hW b).transpose.map (Kd d).subtype).det =
          (Kd d).subtype (P.gramH hW b).transpose.det from (RingHom.map_det _ _).symm,
        Matrix.det_transpose, hdet]
      simp only [Fintype.card_fin, Subfield.subtype_apply, eq_ratCast (algebraMap ℚ (Kd d)),
        SubfieldClass.coe_ratCast]
      push_cast
      rw [pow_mul]
      ring

/-- The sheaf `E` of Theorem 1.4.1(2) has rank `8d`. -/
theorem rank_chE (d : ℚ) : ExteriorAlgebra.algebraMapInv (chE d) = 8 * d := by
  rw [chE, tauExt, main_algebraMapInv_reverse]
  exact lemma8_3_1_rank_eq d

/-! ### Theorem 1.4.1 (3), (4) in the model -/

/-- **Theorem 1.4.1 (3)** (`main-theorem-introduction`), in the model: every graded summand of
`κ(E)` is a Hodge class on every deformation of `(X × X̂, η, h)` as a polarized abelian sixfold of
Weil type (the connected component of its Weil-type period domain). -/
theorem theorem1_4_1_3_model (d : ℕ) (hd : 3 ≤ d) (J : Module.End ℝ (H1 ℝ 3))
    (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3))) (hη : η (Kd.sqrtNeg d) = fX 3 d)
    (M : Matrix (Fin (2 * (2 * 3))) (Fin (2 * (2 * 3))) ℝ)
    (hM : M ∈ connectedComponentIn (WeilDomainMat η (hX 3 d)) (LinearMap.toMatrix' (JX 3 J)))
    (k : ℕ) : kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k := by
  have hd3 : (3 : ℚ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℚ) < d := by linarith
  -- the deformation `M` is `-I` (transported) for some `I ∈ Ω_P`
  obtain ⟨J', hJ', rfl⟩ := connectedComponentIn_subset _ _ hM
  rw [Matrix.toLin'_toMatrix']
  rw [weilDomain_eq_image_OmegaP 3 d hd0 (by norm_num) η hη] at hJ'
  obtain ⟨I, hI, rfl⟩ := hJ'
  rw [kappaX, map_mem_hodgeClassesX_iff 3 I hI.2.1]
  exact main_projDeg_mem_hodgeClassesV (theorem1_4_1_3 hJ hΘ hd3 I hI) k

/-- Corollary 1.3.2 for the sheaf `E`, in the model (the step of the paragraph before
Theorem 1.5.1, TeX 570): every graded summand of `κ(E)` is a Hodge class on every deformation of
`(X × X̂, η, h)` as a polarized abelian sixfold of Weil type (the connected component of its
Weil-type period domain). -/
theorem main_kappaX_mem_hodge (d : ℕ) (hd : 3 ≤ d) (J : Module.End ℝ (H1 ℝ 3))
    (hJ : IsComplexStructure J) (hΘ : IsAmple 3 J (ThetaStd ℚ 3))
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3))) (hη : η (Kd.sqrtNeg d) = fX 3 d)
    (M : Matrix (Fin (2 * (2 * 3))) (Fin (2 * (2 * 3))) ℝ)
    (hM : M ∈ connectedComponentIn (WeilDomainMat η (hX 3 d)) (LinearMap.toMatrix' (JX 3 J)))
    (k : ℕ) : kappaX k d ∈ hodgeClassesX (2 * 3) (Matrix.toLin' M) k := by
  have hd3 : (3 : ℚ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℚ) < d := by linarith
  -- the deformation `M` is `-I` (transported) for some `I ∈ Ω_P`
  obtain ⟨J', hJ', rfl⟩ := connectedComponentIn_subset _ _ hM
  rw [Matrix.toLin'_toMatrix']
  rw [weilDomain_eq_image_OmegaP 3 d hd0 (by norm_num) η hη] at hJ'
  obtain ⟨I, hI, rfl⟩ := hJ'
  rw [kappaX, map_mem_hodgeClassesX_iff 3 I hI.2.1]
  exact main_projDeg_mem_hodgeClassesV (main_kappa_chE_hodge hJ hΘ hd3 I hI) k

/-- **Theorem 1.4.1 (4)** (`main-theorem-introduction`), in the model: the `η(K)`-translates of
`κ₃(E)`, together with `h³`, span the `3`-dimensional subspace `ℚ h³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`. -/
theorem theorem1_4_1_4_model (d : ℕ) (hd : 3 ≤ d) (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * 3)))
    (hη : η (Kd.sqrtNeg d) = fX 3 d) :
    Submodule.span ℚ
        (insert (hX 3 d ^ 3) (Set.range fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d))) =
      (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η ∧
    Module.finrank ℚ ↥((ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η) = 3 := by
  have hd3 : (3 : ℚ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℚ) < d := by linarith
  -- Departure from the paper: the model statement fixes no complex structure on `X`, and the
  -- conclusion does not depend on one; we apply the paper's version (`theorem1_4_1_4`) to the
  -- standard principally polarized threefold `(ℝ⁶, J₀)`, for which `Θ = ThetaStd` is ample.
  have hJ₀ := main_J0_isComplex 3
  have hΘ := main_ample_J0 3
  set P := PJac (d : ℚ) hΘ hd0 with hP
  set hW := PJac_isCompl (d : ℚ) hΘ hd0
  set Φ := (ExteriorAlgebra.map (coordV ℚ 3).toLinearMap).toLinearMap with hΦ
  have hh3 : hX 3 d ^ 3 = Φ (P.hClass hW ^ 3) := by
    rw [hΦ, AlgHom.toLinearMap_apply, map_pow, hX, ← hClass_PStd 3 d hd0 (by norm_num)]
  have hHW : HWof η = P.hwPlane.map Φ := HWof_eq_map_hwPlane 3 d hd0 (by norm_num) η hη
  have hη' : η = etaX 3 d hd0 := eq_etaX 3 d hd0 η hη
  have hκ : (fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d)) =
      Φ ∘ fun k => ExteriorAlgebra.map (P.η hW k) (kappa3E d) := by
    funext k
    have h1 : P.η hW k = etaV 3 d hd0 k := by
      rw [← ηHom_PStd 3 d hd0 (by norm_num)]; rfl
    have h2 : etaX 3 d hd0 k = ↑(coordV ℚ 3) ∘ₗ etaV 3 d hd0 k ∘ₗ ↑(coordV ℚ 3).symm := rfl
    rw [Function.comp_apply, h1, hη', h2, hΦ, AlgHom.toLinearMap_apply, kappaX, kappa3E,
      main_map_conj_map]
  obtain ⟨h1, h2⟩ := And.intro (theorem1_4_1_4 hJ₀ hΘ hd3) (theorem1_4_1_4_finrank hJ₀ hΘ hd3)
  have hspan : Submodule.span ℚ
      (insert (hX 3 d ^ 3) (Set.range fun k : Kd d => ExteriorAlgebra.map (η k) (kappaX 3 d))) =
      ((ℚ ∙ (P.hClass hW ^ 3)) ⊔ P.hwPlane).map Φ := by
    rw [hκ, Set.range_comp, hh3, ← Set.image_insert_eq, ← Submodule.map_span, Set.insert_eq,
      Set.union_comm, h1]
  have hsup : (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η = ((ℚ ∙ (P.hClass hW ^ 3)) ⊔ P.hwPlane).map Φ := by
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, ← hh3, ← hHW]
  refine ⟨hspan.trans hsup.symm, ?_⟩
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have := congrArg (ExteriorAlgebra.map (coordV ℚ 3).symm.toLinearMap) hxy
    simpa [hΦ, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map] using this
  rw [hsup]
  exact (Submodule.equivMapOfInjective Φ hinj _).finrank_eq.symm.trans h2.2

/-! ### Theorem 1.5.1 and Corollary 1.6.1 -/

/-- Theorem 1.5.1 for `d ≥ 3`, following the proof in §9.3 (`d ≥ 3` is the range of the secant sheaf
construction of §§8–9, `SecantSheafDeformation`). -/
theorem main_theorem1_5_1_of_three_le (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [VanGeemenModuli] [SecantSheafDeformation Z]
    (d : ℕ) (hd : 3 ≤ d) (A : AbVar (2 * 3)) (X : PolarizedWeilType A d)
    (hdisc : X.DiscIs (-1)) : X.HW ≤ Z.alg (2 * 3) A.J := by
  have hd0 : (0 : ℚ) < d := by
    have : (3 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  -- The secant sheaf `E` on `X × X̂` of Theorem 1.4.1, for a principally polarized threefold `X`.
  obtain ⟨J, hJ, hΘ, hdef⟩ := SecantSheafDeformation.deform (Z := Z) d hd
  set η₀ := etaX 3 d hd0
  have hη₀ : η₀ (Kd.sqrtNeg d) = fX 3 d := etaX_sqrtNeg 3 d hd0
  have hJX : JX 3 J ∈ WeilDomain η₀ (hX 3 d) := JX_mem_weilDomain 3 d hd0 J hJ hΘ η₀ hη₀
  -- `X × X̂` is a polarized abelian sixfold of Weil type, of discriminant `-1` (Lemma 3.1.3).
  let A₀ : AbVar (2 * 3) := ⟨JX 3 J, hJX.1, ⟨hX 3 d, hJX.2.2.2.2.1⟩⟩
  let X₀ : PolarizedWeilType A₀ d :=
    { η := η₀, isHodge := hJX.2.1, weil₁ := hJX.2.2.1, weil₂ := hJX.2.2.2.1, h := hX 3 d,
      ample := hJX.2.2.2.2.1, norm := hJX.2.2.2.2.2 }
  have hdisc₀ : X₀.DiscIs (-1) := by
    have h := discIs_XXhat 3 d hd0 A₀ X₀ hη₀ rfl
    rwa [show ((-1 : ℚ)) ^ 3 = -1 by norm_num] at h
  -- `C`: the connected component of `X × X̂` in its Weil-type period domain (the irreducible
  -- component of moduli of deformations of `(X × X̂, η, h)`); its points are of Weil type.
  set C := connectedComponentIn (WeilDomainMat η₀ (hX 3 d)) (LinearMap.toMatrix' (JX 3 J))
  have hx₀C : LinearMap.toMatrix' (JX 3 J) ∈ C := mem_connectedComponentIn ⟨_, hJX, rfl⟩
  have hCW : ∀ J', LinearMap.toMatrix' J' ∈ C → J' ∈ WeilDomain η₀ (hX 3 d) := fun J' hJ' => by
    obtain ⟨J'', hJ'', hJ''eq⟩ := connectedComponentIn_subset _ _ hJ'
    rwa [LinearMap.toMatrix'.injective hJ''eq] at hJ''
  -- (1) `κ₃(E) = q^*κ₃(B)` is algebraic on a nonempty open subset `u ∩ C` of `C`: by the
  -- semiregularity of `B` (Lemma 9.3.11) and Conjecture 7.3.9, verified for families of abelian
  -- varieties (`SecantSheafDeformation`), `(X × X̂, q^*B)` deforms locally over the locus where
  -- `κ(E) = q^*κ(B)` remains of Hodge type, and `κ(E)` remains of Hodge type over the Weil-type
  -- deformations of `(X × X̂, η, h)` by Corollary 1.3.2 (the paragraph before Theorem 1.5.1).
  have hdef' : ∀ᶠ M in nhdsWithin (LinearMap.toMatrix' (JX 3 J)) C,
      kappaX 3 d ∈ Z.alg (2 * 3) (Matrix.toLin' M) := by
    filter_upwards [hdef η₀ hη₀, self_mem_nhdsWithin] with M hM hMC
    exact hM fun k => main_kappaX_mem_hodge d hd J hJ hΘ η₀ hη₀ M hMC k
  obtain ⟨u, hu_open, hu_mem, hu_sub⟩ := mem_nhdsWithin.mp hdef'
  -- (2) Hence the Hodge–Weil classes are algebraic at every point of `u ∩ C`: the `η(K)`-translates
  -- of `κ₃(E)` are algebraic (`η(K)` acts by algebraic correspondences), so is `h³` (Lefschetz
  -- (1,1) and products), and they span `ℚh³ ⊕ ĤW` (Theorem 1.4.1(4)).
  have hHWu : ∀ J', LinearMap.toMatrix' J' ∈ u ∩ C → HWof η₀ ≤ Z.alg (2 * 3) J' := by
    intro J' hJ'
    have hW := hCW J' hJ'.2
    let A' : AbVar (2 * 3) := ⟨J', hW.1, ⟨hX 3 d, hW.2.2.2.2.1⟩⟩
    have hκ : kappaX 3 d ∈ Z.alg (2 * 3) J' := by
      simpa [Matrix.toLin'_toMatrix'] using hu_sub hJ'
    have htrans : ∀ k, ExteriorAlgebra.map (η₀ k) (kappaX 3 d) ∈ Z.alg (2 * 3) J' := fun k =>
      PullbackClosed.map_mem A' A' (η₀ k) (hW.2.1 k) _ hκ
    have hh : hX 3 d ∈ Z.alg (2 * 3) J' := LefschetzOneOne.le A' hW.2.2.2.2.1.1
    have hh3 : hX 3 d ^ 3 ∈ Z.alg (2 * 3) J' := by
      rw [pow_three]
      exact SubalgebraClosed.mul_mem A' _ _ hh (SubalgebraClosed.mul_mem A' _ _ hh hh)
    calc HWof η₀ ≤ (ℚ ∙ (hX 3 d ^ 3)) ⊔ HWof η₀ := le_sup_right
      _ = Submodule.span ℚ (insert (hX 3 d ^ 3)
            (Set.range fun k : Kd d => ExteriorAlgebra.map (η₀ k) (kappaX 3 d))) :=
          (theorem1_4_1_4_model d hd η₀ hη₀).1.symm
      _ ≤ Z.alg (2 * 3) J' := by
          rw [Submodule.span_le]
          rintro _ (rfl | ⟨k, rfl⟩)
          exacts [hh3, htrans k]
  -- (3) The locus where a Hodge–Weil class `α` (a fixed rational class) is algebraic is a
  -- countable union of closed algebraic subsets [Voisin, §4.2]; it contains the open subset
  -- `u ∩ C`, hence the whole component `C`.
  have hopen : IsOpen ((↑) ⁻¹' (u ∩ C) : Set C) := by
    rw [Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ]
    exact hu_open.preimage continuous_subtype_val
  have hHWC : ∀ J', LinearMap.toMatrix' J' ∈ C → HWof η₀ ≤ Z.alg (2 * 3) J' :=
    fun J' hJ' α hα => VoisinLocus.spread (Z := Z) η₀ (hX 3 d) α (JX 3 J) (u ∩ C)
      Set.inter_subset_right ⟨_, hu_mem, hx₀C⟩ hopen (fun J'' hJ'' => hHWu J'' hJ'' hα) J' hJ'
  -- (4) [van Geemen, Th. 5.2(3)]: `A` is isogenous, by `ψ`, to the deformation
  -- `A' = (ψ A ψ⁻¹)` of `X × X̂` in `C`; transport the Hodge–Weil classes back along `ψ⁻¹`.
  obtain ⟨ψ, hψη, -, hψC⟩ := VanGeemenModuli.moduli hd0 A A₀ X X₀ (-1) hdisc hdisc₀
  set J' := bcMap ℚ ℝ ψ.toLinearMap ∘ₗ A.J ∘ₗ bcMap ℚ ℝ ψ.symm.toLinearMap with hJ'_def
  have hW := hCW J' hψC
  let A' : AbVar (2 * 3) := ⟨J', hW.1, ⟨hX 3 d, hW.2.2.2.2.1⟩⟩
  have hψA : IsHodgeMap A'.J A.J ψ.symm.toLinearMap := by
    show bcMap ℚ ℝ ψ.symm.toLinearMap ∘ₗ J' = A.J ∘ₗ bcMap ℚ ℝ ψ.symm.toLinearMap
    rw [hJ'_def, ← LinearMap.comp_assoc, ← main_bcMap_comp]
    simp [main_bcMap_id]
  intro α hα
  have h1 : ExteriorAlgebra.map ψ.toLinearMap α ∈ HWof η₀ :=
    main_map_mem_HWof X.η η₀ ψ.toLinearMap (hψη _) hα
  have h2 := PullbackClosed.map_mem A' A ψ.symm.toLinearMap hψA _ (hHWC J' hψC h1)
  rwa [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearEquiv.symm_comp,
    ExteriorAlgebra.map_id, AlgHom.id_apply] at h2

/-- **Theorem 1.5.1** (`thm-algebraicity`). Let `d` be a positive integer and `K = ℚ(√-d)`. The
Hodge–Weil classes of polarized abelian sixfolds of Weil type with complex multiplication by `K`
and with discriminant `-1` are algebraic. -/
theorem theorem1_5_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [VanGeemenModuli] [SecantSheafDeformation Z]
    (d : ℕ) (hd : 0 < d) (A : AbVar (2 * 3)) (X : PolarizedWeilType A d) (hdisc : X.DiscIs (-1)) :
    X.HW ≤ Z.alg (2 * 3) A.J := by
  by_cases hd3 : 3 ≤ d
  · exact main_theorem1_5_1_of_three_le Z d hd3 A X hdisc
  · -- Departure from the paper: the construction of §§8–9 needs `d ≥ 3` (Theorem 1.4.1); for
    -- `d ∈ {1, 2}` we use `ℚ(√-4d) = ℚ(√-d)` (the footnote in §1.5, used there for the parity of
    -- `d`) and replace `d` by `4d ≥ 3`: the same abelian variety is of Weil type for `4d`, with the
    -- same Hodge–Weil classes and discriminant (`main_exists_four_mul`).
    obtain ⟨X', hHW, hdisc'⟩ := main_exists_four_mul (d' := ((4 * d : ℕ) : ℚ))
      (by exact_mod_cast hd) (by push_cast; ring) X hdisc
    rw [← hHW]
    exact main_theorem1_5_1_of_three_le Z (4 * d) (by omega) A X' hdisc'

/-- The sum of two sub-Hodge structures is a sub-Hodge structure. -/
theorem main_isHodgeSub_sup {g : ℕ} (A : AbVar g) {U U' : Submodule ℚ (H1 ℚ g)}
    (hU : A.IsHodgeSub U) (hU' : A.IsHodgeSub U') : A.IsHodgeSub (U ⊔ U') := by
  intro x hx
  have hspan : Submodule.span ℝ (bcH1 ℚ ℝ g '' ↑(U ⊔ U')) =
      Submodule.span ℝ (bcH1 ℚ ℝ g '' U) ⊔ Submodule.span ℝ (bcH1 ℚ ℝ g '' U') := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩)
        (Submodule.subset_span ⟨u', hu', rfl⟩)
    · exact sup_le (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr le_sup_left)))
        (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr le_sup_right)))
  rw [hspan] at hx ⊢
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (hU y hy) (hU' z hz)

/-- **Corollary 1.6.1** (no label). The Hodge conjecture holds for abelian fourfolds: every Hodge
class is algebraic. -/
theorem corollary1_6_1 (Z : CycleClasses) [PullbackClosed Z] [SubalgebraClosed Z]
    [LefschetzOneOne Z] [VoisinLocus Z] [VanGeemenModuli] [SecantSheafDeformation Z]
    [SchoenDegeneration Z] [MoonenZarhinSimple] [RamonMariProducts Z] [MoonenZarhinLowDim]
    (A : AbVar (2 * 2)) (p : ℕ) : A.hodge p ≤ Z.alg (2 * 2) A.J := by
  -- An ample class `h`, algebraic by the Lefschetz (1,1) theorem.
  obtain ⟨h, hh⟩ := A.polarizable
  have hh1 : h ∈ Z.alg (2 * 2) A.J := LefschetzOneOne.le A hh.1
  -- Theorem 1.5.1 and [Schoen, Prop. 10]: the Hodge–Weil classes of every abelian fourfold of
  -- Weil type are algebraic, for all `K` and all discriminants.
  have hHW : ∀ (d : ℕ) (hd : 0 < d) (X : WeilType A d), X.HW ≤ Z.alg (2 * 2) A.J :=
    fun d hd X =>
      SchoenDegeneration.imp d hd (fun A' X' hdisc => theorem1_5_1 Z d hd A' X' hdisc) A X
  have hallHW : A.allHW ≤ Z.alg (2 * 2) A.J :=
    iSup_le fun d => iSup_le fun hd => iSup_le fun X => hHW d hd X
  -- Products of divisor classes are algebraic (Lefschetz (1,1), intersection products).
  have hdiv : A.divisorProducts ≤ Z.alg (2 * 2) A.J := by
    rw [AbVar.divisorProducts, Submodule.span_le]
    rintro _ ⟨α, hα, β, hβ, rfl⟩
    exact SubalgebraClosed.mul_mem A _ _ (LefschetzOneOne.le A hα) (LefschetzOneOne.le A hβ)
  have hfin : Module.finrank ℚ (H1 ℚ (2 * 2)) = 8 := by simp
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ 2 * 2 < p by omega) with
    rfl | rfl | rfl | rfl | rfl | hp
  · -- `H⁰(A, ℚ) = ℚ · [A]`
    intro α hα
    have hα0 : α ∈ ⋀[ℚ]^(2 * 0) (H1 ℚ (2 * 2)) := hα.1
    rw [ExteriorAlgebra.exteriorPower, Nat.mul_zero, pow_zero] at hα0
    obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hα0
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (SubalgebraClosed.one_mem A)
  · -- Lefschetz (1,1)
    exact LefschetzOneOne.le A
  · -- codimension two
    by_cases hs : A.IsSimple
    · -- [Moonen–Zarhin 1995, Th. 2.11]
      exact (MoonenZarhinSimple.span A hs).trans (sup_le hdiv hallHW)
    · -- `A` is not simple: by Poincaré reducibility it is isogenous to a product.
      obtain ⟨U, hU, hU0, hUT⟩ : ∃ U, A.IsHodgeSub U ∧ U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra! hc
        exact hs ⟨by norm_num, fun U hU => (eq_or_ne U ⊥).imp_right (hc U hU)⟩
      have hcompl : ∀ W, A.IsHodgeSub W → ∃ W', A.IsHodgeSub W' ∧ IsCompl W W' ∧
          Module.finrank ℚ W + Module.finrank ℚ W' = 8 := fun W hW => by
        obtain ⟨W', hW', hc⟩ := A.exists_isCompl_isHodgeSub W hW
        exact ⟨W', hW', hc, (Submodule.finrank_add_eq_of_isCompl hc).trans hfin⟩
      by_cases h4 : ∃ W, A.IsHodgeSub W ∧ Module.finrank ℚ W = 4
      · -- a product of two abelian surfaces: [Ramón-Marí, Th. 4.11]
        obtain ⟨W, hW, hW4⟩ := h4
        obtain ⟨W', hW', hc, hsum⟩ := hcompl W hW
        exact RamonMariProducts.hc A W W' ⟨hW, hW', hc, hW4, by omega⟩ 2
      · -- `A` is isogenous to `B × E`, `B` a simple threefold: [Moonen–Zarhin 1999]
        simp only [not_exists, not_and] at h4
        have hdim : ∀ W, A.IsHodgeSub W → W ≠ ⊥ → W ≠ ⊤ →
            Module.finrank ℚ W = 2 ∨ Module.finrank ℚ W = 6 := fun W hW hW0 hWT => by
          obtain ⟨k, hk⟩ := A.even_finrank_of_isHodgeSub W hW
          have h0 : Module.finrank ℚ W ≠ 0 := fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
          have h8 : Module.finrank ℚ W ≠ 8 := fun h8 =>
            hWT (Submodule.eq_top_of_finrank_eq (h8.trans hfin.symm))
          have hle : Module.finrank ℚ W ≤ 8 := hfin ▸ Submodule.finrank_le W
          have := h4 W hW
          omega
        obtain ⟨W6, W2, hW6, hW2, hc, h6, h2⟩ : ∃ W6 W2, A.IsHodgeSub W6 ∧ A.IsHodgeSub W2 ∧
            IsCompl W6 W2 ∧ Module.finrank ℚ W6 = 6 ∧ Module.finrank ℚ W2 = 2 := by
          obtain ⟨U', hU', hc, hsum⟩ := hcompl U hU
          rcases hdim U hU hU0 hUT with h | h
          · exact ⟨U', U, hU', hU, hc.symm, by omega, h⟩
          · exact ⟨U, U', hU, hU', hc, h, by omega⟩
        have hsimple : A.SimpleFactor W6 := by
          refine ⟨fun h0 => by rw [h0, finrank_bot] at h6; omega, fun U' hU'6 hU' => ?_⟩
          obtain ⟨k, hk⟩ := A.even_finrank_of_isHodgeSub U' hU'
          have hle : Module.finrank ℚ U' ≤ 6 := h6 ▸ Submodule.finrank_mono hU'6
          have hne4 := h4 U' hU'
          have hne2 : Module.finrank ℚ U' ≠ 2 := by
            intro h2'
            have hdisj : U' ⊓ W2 = ⊥ := eq_bot_iff.mpr fun x hx =>
              hc.disjoint.le_bot ⟨hU'6 hx.1, hx.2⟩
            have := Submodule.finrank_sup_add_finrank_inf_eq U' W2
            rw [hdisj, finrank_bot] at this
            exact h4 _ (main_isHodgeSub_sup A hU' hW2) (by omega)
          rcases (show Module.finrank ℚ U' = 0 ∨ Module.finrank ℚ U' = 6 by omega) with h0 | h6'
          · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
          · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hU'6 (h6'.trans h6.symm))
        exact (MoonenZarhinLowDim.span A W6 W2 ⟨hW6, hW2, hc, h6, h2⟩ hsimple).trans
          (sup_le hdiv hallHW)
  · -- hard Lefschetz: `h² ∪ : H² → H⁶` maps Hodge classes onto Hodge classes
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := Submodule.mem_map.mp (A.hodge_pred_le_map (by norm_num) h hh hα)
    have h2 : h ^ (2 * 2 - 2) ∈ Z.alg (2 * 2) A.J := by
      rw [show 2 * 2 - 2 = 2 from rfl, pow_two]
      exact SubalgebraClosed.mul_mem A _ _ hh1 hh1
    rw [LinearMap.mulLeft_apply]
    exact SubalgebraClosed.mul_mem A _ _ h2 (LefschetzOneOne.le A hβ)
  · -- the top degree `H⁸(A, ℚ) = ℚ h⁴`
    intro α hα
    have hα8 : α ∈ ⋀[ℚ]^(2 * (2 * 2)) (H1 ℚ (2 * 2)) := hα.1
    rw [A.top_eq_span_pow h hh, Submodule.mem_span_singleton] at hα8
    obtain ⟨c, rfl⟩ := hα8
    refine Submodule.smul_mem _ c ?_
    have h2 : h ^ 2 ∈ Z.alg (2 * 2) A.J := by
      rw [pow_two]; exact SubalgebraClosed.mul_mem A _ _ hh1 hh1
    have h4 : h ^ (2 * 2) = h ^ 2 * h ^ 2 := by rw [← pow_add]
    rw [h4]
    exact SubalgebraClosed.mul_mem A _ _ h2 h2
  · -- no Hodge classes above the top degree
    rw [A.hodge_eq_bot_of_lt p hp]
    exact bot_le

end WeilClasses
