module

public import WeilClasses.External.VanGeemen.Landherr
public import WeilClasses.Main.Compare
public import WeilClasses.AbelianVariety.Lemmas

/-!
# [van Geemen, Th. 5.2(3)] in the case used in Theorem 1.5.1

B. van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, Lecture Notes in
Math. 1594 (1994), Th. 5.2(3): polarized abelian `2n`-folds of Weil type for `K = ℚ(√-d)` with a
given discriminant form one connected family up to isogeny. Theorem 1.5.1 uses it once (TeX line
6847, step (4) of `main_theorem1_5_1_of_three_le`): for a sixfold `A` of discriminant `-1` against
the sixfold `X × X̂` of discriminant `-1` built from a principally polarized threefold. This file
proves that case for every `n > 0` (`vanGeemen_moduli_XXhat`), together with the connectedness of
the Weil-type period domain of `X × X̂` (`weilDomainMat_isPreconnected`); the main theorems use it
and assume no part of [van Geemen, Th. 5.2(3)].

## Proof (van Geemen's: Landherr's theorem and the connectedness of the period domain)

1. *The Hermitian form.* `H₁(A, ℚ) = H¹(A, ℚ)*` with `f = η(√-d)ᵀ` and the Riemann form
   `E(x, y) = ⟪h, x ∧ y⟫` is a nondegenerate Hermitian space over `K`
   (`PolarizedWeilType.vg_space`): `f² = -d` (`η` is a ring homomorphism),
   `E(f x, f y) = Nm(√-d) E(x, y) = d E(x, y)` (`X.norm`), `E` alternating, and nondegenerate
   (ampleness). Its Hermitian form is van Geemen's `H(x, y) = E(x, f y) + √-d E(x, y)`
   (`PolarizedWeilType.herm`).
2. *Signature `(n, n)`.* Over `ℝ`, `T = (J ∘ η(√-d))ᵀ = f ∘ Jᵀ` satisfies `T² = d`; on its
   eigenspaces for `∓√d`, `f = ±√d Jᵀ`, so `H(a, a) = E(a, f a) = ±√d E(a, a ∘ J)`, of sign `±` by
   ampleness (`vg_q_eigen`). The Weil conditions `weil₁`, `weil₂` give both eigenspaces dimension
   at least `2n` (`vg_finrank_P`, `vg_finrank_N`): the real parts of the `(±√-d, i)`-eigenspace of
   `(η(√-d), J)` in `H¹(A, ℂ)` (complex dimension `n`) form a real subspace of dimension `2n` of the
   `∓√d`-eigenspace of `J ∘ η(√-d)`, which has the dimension of that of its transpose. A rational
   family orthogonal for the trace form `E(x, f y)`, with values of one sign, spans a real
   subspace of its size meeting the eigenspace of the other sign only in `0`, so it has at most `2n`
   members (`vg_posBound`, `vg_negBound`).
3. *Landherr's theorem (split case)* (`vg_HermSpace.landherr_split`, in
   `WeilClasses.External.VanGeemen.Landherr`) makes `H` hyperbolic for `X` and for `X₀` (both of
   discriminant `(-1)ⁿ`), and their hyperbolic bases give a `K`-linear isometry
   `φ : H₁(A₀) → H₁(A)` (`vg_HermSpace.exists_isometry`).
4. *`ψ`* is the isomorphism of `H¹` with transpose `φ` (`vg_psi`: `x ∘ ψ = φ x`, the inverse
   transpose of `φ⁻¹`): it is `K`-linear (`vg_psi_eta`) and maps `h` to `h₀`, as
   `⟪ψ_* h, a ∧ b⟫ = E(φ a, φ b) = E₀(a, b)` (`vg_psi_h`; `c' = 1`).
5. *Transport.* `J' = ψ_ℝ ∘ J ∘ ψ_ℝ⁻¹` is a complex structure, `η₀(K)` acts on `H¹` by Hodge maps,
   the Weil dimensions and the ampleness of `h₀ = ψ_* h` transport along `ψ`, and
   `η₀(k)^* h₀ = Nm(k) h₀` is `X₀.norm`: `J'` is in the Weil-type period domain of `(η₀, h₀)`
   (`vg_transport_mem`).
6. *Connectedness.* The Weil-type period domain of `X × X̂` is the image of the path-connected
   period domain `Ω_P` of §4 (`weilDomain_eq_image_OmegaP`, `KSecant.s4_OmegaP_join`) under the
   continuous map `I ↦ -I` in the coordinates of the model, so it is preconnected and is the
   connected component of each of its points.

The discriminant of `X₀` is a hypothesis (`hdisc₀`); it holds for every polarized abelian variety
of Weil type with the action and the polarization of `X × X̂` (`discIs_XXhat`, Lemma 3.1.3, in
`WeilClasses.Main.Theorems`, which imports this file).
-/

@[expose] public section

namespace WeilClasses

open Module

/-! ### Helpers: `eval2`, base change, real parts, transposes -/

section Helpers

variable {F : Type*} [Field F] [CharZero F] {g : ℕ}

/-- `⟪ξ, a ∧ b⟫` as a bilinear form in `a, b ∈ H₁ = (H¹)*`. -/
noncomputable def vg_eval2L (ξ : S F g) : LinearMap.BilinForm F (Module.Dual F (H1 F g)) :=
  LinearMap.mk₂ F (eval2 F g ξ)
    (fun a a' b => by simp only [eval2, map_add, LinearMap.add_apply])
    (fun c a b => by simp only [eval2, map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun a b b' => by simp only [eval2, map_add, LinearMap.add_apply])
    (fun c a b => by simp only [eval2, map_smul, LinearMap.smul_apply, smul_eq_mul])

theorem vg_eval2L_apply (ξ : S F g) (a b : Module.Dual F (H1 F g)) :
    vg_eval2L ξ a b = eval2 F g ξ a b := rfl

/-- `⟪φ_* ξ, a ∧ b⟫ = ⟪ξ, (a ∘ φ) ∧ (b ∘ φ)⟫`. -/
theorem vg_eval2_map (T : Module.End F (H1 F g)) (ξ : S F g) (a b : Module.Dual F (H1 F g)) :
    eval2 F g (ExteriorAlgebra.map T ξ) a b = eval2 F g ξ (a ∘ₗ T) (b ∘ₗ T) := by
  simp only [eval2, main_coord_empty, AlgHom.toLinearMap_apply]
  exact main_dc_map T a b ξ

theorem vg_eval2_smul (c : F) (ξ : S F g) (a b : Module.Dual F (H1 F g)) :
    eval2 F g (c • ξ) a b = c * eval2 F g ξ a b := by
  simp only [eval2, map_smul, smul_eq_mul]

end Helpers

section BaseChange

variable {g : ℕ}

theorem vg_bcDual_comp (φ : Module.End ℚ (H1 ℚ g)) (x : Module.Dual ℚ (H1 ℚ g)) :
    bcDual ℚ ℝ g (x ∘ₗ φ) = bcDual ℚ ℝ g x ∘ₗ bcMap ℚ ℝ φ := by
  refine (Pi.basisFun ℝ (Fin (2 * g))).ext fun i => ?_
  have he : (Pi.basisFun ℝ (Fin (2 * g))) i = bcH1 ℚ ℝ g (e ℚ g i) := by
    rw [main_bcH1_e, Pi.basisFun_apply]
    rfl
  rw [he, LinearMap.comp_apply, main_bcMap_bcH1, s3_bcDual_bcH1, s3_bcDual_bcH1,
    LinearMap.comp_apply]

theorem vg_bcDual_injective : Function.Injective (bcDual ℚ ℝ g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [fnd_dual_eq_sum g ℚ x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := congrArg (fun a => a (e ℝ g i)) hx
  simp only [s3_bcDual_apply_e, LinearMap.zero_apply, map_eq_zero_iff _
    (algebraMap ℚ ℝ).injective] at h
  simp [h]

theorem vg_bcMap_bcMap (φ : Module.End ℚ (H1 ℚ g)) : bcMap ℝ ℂ (bcMap ℚ ℝ φ) = bcMap ℚ ℂ φ := by
  simp only [bcMap, LinearMap.toMatrix'_toLin', Matrix.map_map]
  congr 2

/-- `η(a + b√-d) = a + b η(√-d)` for a ring homomorphism `η : K → End(M)`. -/
theorem vg_eta_eq {d : ℚ} (hd : 0 < d) {M : Type*} [AddCommGroup M] [Module ℚ M]
    (η : Kd d →+* Module.End ℚ M) (k : Kd d) :
    η k = Kd.ratPart d k • 1 + Kd.sqrtNegCoeff d k • η (Kd.sqrtNeg d) := by
  conv_lhs => rw [Kd.eq_ratPart_add_sqrtNegCoeff hd k]
  rw [map_add, map_mul, RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The real part `H¹(ℂ) → H¹(ℝ)`, coordinatewise. -/
noncomputable def vg_re (g : ℕ) : H1 ℂ g →ₗ[ℝ] H1 ℝ g :=
  LinearMap.pi fun i => Complex.reLm ∘ₗ LinearMap.proj i

/-- The imaginary part `H¹(ℂ) → H¹(ℝ)`, coordinatewise. -/
noncomputable def vg_im (g : ℕ) : H1 ℂ g →ₗ[ℝ] H1 ℝ g :=
  LinearMap.pi fun i => Complex.imLm ∘ₗ LinearMap.proj i

theorem vg_re_apply (x : H1 ℂ g) (i : Fin (2 * g)) : vg_re g x i = (x i).re := rfl

theorem vg_im_apply (x : H1 ℂ g) (i : Fin (2 * g)) : vg_im g x i = (x i).im := rfl

theorem vg_re_bcMap (B : Module.End ℝ (H1 ℝ g)) (x : H1 ℂ g) :
    vg_re g (bcMap ℝ ℂ B x) = B (vg_re g x) := by
  funext i
  rw [vg_re_apply, ← LinearMap.toMatrix'_mulVec B]
  simp only [bcMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Complex.re_sum, vg_re_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem vg_re_I_smul (x : H1 ℂ g) : vg_re g (Complex.I • x) = -vg_im g x := by
  funext i
  simp [vg_re_apply, vg_im_apply]

theorem vg_re_real_smul (r : ℝ) (x : H1 ℂ g) : vg_re g ((r : ℂ) • x) = r • vg_re g x := by
  funext i
  simp [vg_re_apply]

theorem vg_eq_zero_of_re_im (x : H1 ℂ g) (h1 : vg_re g x = 0) (h2 : vg_im g x = 0) : x = 0 := by
  funext i
  exact Complex.ext (congrFun h1 i) (congrFun h2 i)

/-- A `ℂ`-subspace `W` of `H¹(ℂ)` on which `J_ℂ = i` and `B_ℂ = μ` (`μ` real) gives, by real parts,
a subspace of the `μ`-eigenspace of `B` of real dimension `2 dim W`. -/
theorem vg_finrank_eigenspace_ge (J B : Module.End ℝ (H1 ℝ g)) (W : Submodule ℂ (H1 ℂ g)) (μ : ℝ)
    (hJ : ∀ x ∈ W, bcMap ℝ ℂ J x = Complex.I • x) (hB : ∀ x ∈ W, bcMap ℝ ℂ B x = (μ : ℂ) • x) :
    2 * finrank ℂ W ≤ finrank ℝ (Module.End.eigenspace B μ) := by
  set L : W.restrictScalars ℝ →ₗ[ℝ] H1 ℝ g := (vg_re g).comp (W.restrictScalars ℝ).subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hre : vg_re g (x : H1 ℂ g) = 0 := hx
    have h1 := congrArg (vg_re g) (hJ x x.2)
    rw [vg_re_bcMap, hre, map_zero, vg_re_I_smul, eq_comm, neg_eq_zero] at h1
    exact Subtype.ext (vg_eq_zero_of_re_im _ hre h1)
  have hrange : LinearMap.range L ≤ Module.End.eigenspace B μ := by
    rintro _ ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    show B (vg_re g x) = μ • vg_re g x
    rw [← vg_re_bcMap, hB x x.2, vg_re_real_smul]
  have h2 : finrank ℝ (W.restrictScalars ℝ) = 2 * finrank ℂ W := by
    show finrank ℝ W = _
    rw [← Module.finrank_mul_finrank ℝ ℂ W, Complex.finrank_real_complex]
  rw [← h2, ← LinearMap.finrank_range_of_inj hinj]
  exact Submodule.finrank_mono hrange

/-- The eigenspaces of the transpose have the same dimensions. -/
theorem vg_finrank_eigenspace_dualMap {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (B : Module.End K M) (μ : K) :
    finrank K (Module.End.eigenspace B.dualMap μ) = finrank K (Module.End.eigenspace B μ) := by
  have h : B.dualMap - μ • 1 = (B - μ • 1).dualMap := by
    ext x v
    simp
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def, h]
  have h1 := LinearMap.finrank_range_add_finrank_ker (B - μ • 1).dualMap
  have h2 := LinearMap.finrank_range_add_finrank_ker (B - μ • 1)
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h1
  omega

end BaseChange

/-! ### The Hermitian space of a polarized abelian variety of Weil type -/

namespace PolarizedWeilType

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : PolarizedWeilType A d)

theorem vg_fT_apply (x : Module.Dual ℚ (H1 ℚ (2 * m))) : X.fT x = x ∘ₗ X.η (Kd.sqrtNeg d) := rfl

theorem vg_eta_sq (hd : 0 < d) :
    X.η (Kd.sqrtNeg d) * X.η (Kd.sqrtNeg d) = -(d • (1 : Module.End ℚ (H1 ℚ (2 * m)))) := by
  rw [← map_mul, s3_sqrtNeg_mul_self hd, map_neg, RingHom.map_rat_algebraMap,
    Algebra.algebraMap_eq_smul_one]

theorem vg_fT_fT (hd : 0 < d) (x : Module.Dual ℚ (H1 ℚ (2 * m))) : X.fT (X.fT x) = -(d • x) := by
  refine LinearMap.ext fun w => ?_
  have h := LinearMap.congr_fun (X.vg_eta_sq hd) w
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [fT, LinearMap.dualMap_apply, h, map_neg, map_smul, LinearMap.neg_apply,
    LinearMap.smul_apply]

theorem vg_E_fT_fT (hd : 0 < d) (x y : Module.Dual ℚ (H1 ℚ (2 * m))) :
    X.E (X.fT x) (X.fT y) = d * X.E x y := by
  have h := X.norm (Kd.sqrtNeg d)
  rw [s24a_Nm_sqrtNeg hd] at h
  simp only [E, X.vg_fT_apply]
  rw [← vg_eval2_map, h, vg_eval2_smul]

/-- The real Riemann form `⟪h, a ∧ b⟫` on `H₁(A, ℝ)`. -/
noncomputable abbrev vg_ER : LinearMap.BilinForm ℝ (Module.Dual ℝ (H1 ℝ (2 * m))) :=
  vg_eval2L (bcS ℚ ℝ (2 * m) X.h)

/-- `η(√-d)` on `H¹(A, ℝ)`. -/
noncomputable abbrev vg_FR : Module.End ℝ (H1 ℝ (2 * m)) := bcMap ℚ ℝ (X.η (Kd.sqrtNeg d))

theorem vg_ER_bcDual (x y : Module.Dual ℚ (H1 ℚ (2 * m))) :
    X.vg_ER (bcDual ℚ ℝ _ x) (bcDual ℚ ℝ _ y) = (X.E x y : ℝ) := by
  rw [vg_eval2L_apply, s24b_eval2_bcS]
  rfl

theorem vg_bcDual_fT (x : Module.Dual ℚ (H1 ℚ (2 * m))) :
    bcDual ℚ ℝ _ (X.fT x) = X.vg_FR.dualMap (bcDual ℚ ℝ _ x) := by
  rw [vg_fT_apply, vg_bcDual_comp, LinearMap.dualMap_apply']

/-- `E` is nondegenerate (the polarization is ample). -/
theorem vg_E_nondeg (x : Module.Dual ℚ (H1 ℚ (2 * m))) (hx : ∀ y, X.E x y = 0) : x = 0 := by
  set a := bcDual ℚ ℝ (2 * m) x with ha
  have h1 : ∀ b : Module.Dual ℝ (H1 ℝ (2 * m)), X.vg_ER a b = 0 := by
    intro b
    rw [fnd_dual_eq_sum (2 * m) ℝ b, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, ← s3_bcDual_f ℚ ℝ, ha, X.vg_ER_bcDual, hx, Rat.cast_zero, smul_zero]
  by_contra hne
  have ha0 : a ≠ 0 := fun h => hne (vg_bcDual_injective (by rw [← ha, h, map_zero]))
  have := X.ample.2 a ha0
  rw [← vg_eval2L_apply, h1] at this
  exact lt_irrefl _ this

/-- **The Hermitian space** `(H₁(A, ℚ), f = η(√-d)ᵀ, E)` of a polarized abelian variety of Weil
type; its Hermitian form is van Geemen's `H` (`PolarizedWeilType.herm`, `vg_space_herm`). -/
noncomputable def vg_space (hd : 0 < d) : vg_HermSpace d (Module.Dual ℚ (H1 ℚ (2 * m))) where
  f := X.fT
  E := vg_eval2L X.h
  d_pos := hd
  f_f := X.vg_fT_fT hd
  E_swap x y := s24b_eval2_swap ℚ (2 * m) X.h y x
  E_ff := X.vg_E_fT_fT hd
  nondeg := X.vg_E_nondeg

theorem vg_space_herm (hd : 0 < d) (x y : Module.Dual ℚ (H1 ℚ (2 * m))) :
    (X.vg_space hd).herm x y = X.herm x y := rfl

/-! ### The signature `(n, n)` -/

/-- On the `μ`-eigenspace of `(J ∘ f)ᵀ`, `E(a, f a) = -μ E(a, a ∘ J)`. -/
theorem vg_q_eigen (μ : ℝ) (a : Module.Dual ℝ (H1 ℝ (2 * m)))
    (ha : a ∈ Module.End.eigenspace (A.J ∘ₗ X.vg_FR).dualMap μ) :
    X.vg_ER a (X.vg_FR.dualMap a) = -μ * X.vg_ER a (a ∘ₗ A.J) := by
  rw [Module.End.mem_eigenspace_iff, LinearMap.dualMap_apply'] at ha
  have hcomm : X.vg_FR ∘ₗ A.J = A.J ∘ₗ X.vg_FR := X.isHodge (Kd.sqrtNeg d)
  have hJJ : ∀ w, A.J (A.J w) = -w := fun w => by
    have := LinearMap.congr_fun A.isComplex w
    simpa using this
  have hcommv : ∀ w, X.vg_FR (A.J w) = A.J (X.vg_FR w) := fun w => LinearMap.congr_fun hcomm w
  have hav : ∀ w, a (A.J (X.vg_FR w)) = μ * a w := fun w => by
    have := LinearMap.congr_fun ha w
    simpa using this
  have key : X.vg_FR.dualMap a = (-μ) • (a ∘ₗ A.J) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    have h1 : a (X.vg_FR v) = -a (A.J (A.J (X.vg_FR v))) := by rw [hJJ, map_neg, neg_neg]
    rw [h1, ← hcommv, hav]
    ring
  rw [key, map_smul, smul_eq_mul]

theorem vg_sqrtNeg_mul_I : sqrtNeg d * Complex.I = ((-Real.sqrt d : ℝ) : ℂ) := by
  simp only [sqrtNeg, Complex.ofReal_neg]
  linear_combination (Real.sqrt d : ℂ) * Complex.I_mul_I

/-- The Weil condition `weil₁` makes the `-√d`-eigenspace of `(J ∘ f)ᵀ` (where `E(a, f a) > 0`)
of dimension at least `2n`. -/
theorem vg_finrank_P :
    2 * m ≤ finrank ℝ (Module.End.eigenspace (A.J ∘ₗ X.vg_FR).dualMap (-Real.sqrt d)) := by
  rw [vg_finrank_eigenspace_dualMap]
  have h := vg_finrank_eigenspace_ge A.J (A.J ∘ₗ X.vg_FR)
    (Module.End.eigenspace (bcMap ℚ ℂ (X.η (Kd.sqrtNeg d))) (sqrtNeg d) ⊓ H10 (2 * m) A.J)
    (-Real.sqrt d) (fun x hx => by
      have := Module.End.mem_eigenspace_iff.mp hx.2
      rwa [main_lef_complexifyH1_eq] at this) (fun x hx => by
      have h1 := Module.End.mem_eigenspace_iff.mp hx.1
      have h2 := Module.End.mem_eigenspace_iff.mp hx.2
      rw [main_lef_complexifyH1_eq] at h2
      rw [main_bcMap_comp, LinearMap.comp_apply, vg_bcMap_bcMap, h1, map_smul, h2, smul_smul,
        vg_sqrtNeg_mul_I])
  rwa [X.weil₁] at h

/-- The Weil condition `weil₂` makes the `√d`-eigenspace of `(J ∘ f)ᵀ` (where `E(a, f a) < 0`)
of dimension at least `2n`. -/
theorem vg_finrank_N :
    2 * m ≤ finrank ℝ (Module.End.eigenspace (A.J ∘ₗ X.vg_FR).dualMap (Real.sqrt d)) := by
  rw [vg_finrank_eigenspace_dualMap]
  have h := vg_finrank_eigenspace_ge A.J (A.J ∘ₗ X.vg_FR)
    (Module.End.eigenspace (bcMap ℚ ℂ (X.η (Kd.sqrtNeg d))) (-sqrtNeg d) ⊓ H10 (2 * m) A.J)
    (Real.sqrt d) (fun x hx => by
      have := Module.End.mem_eigenspace_iff.mp hx.2
      rwa [main_lef_complexifyH1_eq] at this) (fun x hx => by
      have h1 := Module.End.mem_eigenspace_iff.mp hx.1
      have h2 := Module.End.mem_eigenspace_iff.mp hx.2
      rw [main_lef_complexifyH1_eq] at h2
      rw [main_bcMap_comp, LinearMap.comp_apply, vg_bcMap_bcMap, h1, map_smul, h2, smul_smul,
        neg_mul, vg_sqrtNeg_mul_I, Complex.ofReal_neg, neg_neg])
  rwa [X.weil₂] at h

/-- A rational family orthogonal for the trace form, with values of the sign of `σ`, spans over `ℝ`
a subspace of its size meeting a subspace `N` where the trace form has the opposite sign only in
`0`. -/
theorem vg_card_add_finrank_le (σ : ℝ) (N : Submodule ℝ (Module.Dual ℝ (H1 ℝ (2 * m))))
    (hN : ∀ a ∈ N, a ≠ 0 → σ * X.vg_ER a (X.vg_FR.dualMap a) < 0)
    {ι : Type} [Fintype ι] (t : ι → Module.Dual ℚ (H1 ℚ (2 * m)))
    (horth : ∀ i j, i ≠ j → X.E (t i) (X.fT (t j)) = 0)
    (hσ : ∀ i, 0 < σ * X.E (t i) (X.fT (t i))) :
    Fintype.card ι + finrank ℝ N ≤ 2 * (2 * m) := by
  set L := Fintype.linearCombination ℝ (fun i => bcDual ℚ ℝ (2 * m) (t i)) with hL
  have hq : ∀ c : ι → ℝ, σ * X.vg_ER (L c) (X.vg_FR.dualMap (L c)) =
      ∑ i, c i ^ 2 * (σ * X.E (t i) (X.fT (t i))) := by
    intro c
    simp only [hL, Fintype.linearCombination_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, ← X.vg_bcDual_fT, X.vg_ER_bcDual]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hji
      rw [horth j i hji]
      simp
    · simp
  have hnonneg : ∀ c : ι → ℝ, 0 ≤ σ * X.vg_ER (L c) (X.vg_FR.dualMap (L c)) := fun c => by
    rw [hq]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hσ i).le
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 := hq c
    rw [hc, map_zero, LinearMap.zero_apply, mul_zero] at h0
    have h' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (sq_nonneg (c i)) (hσ i).le)).mp h0.symm
    funext i
    rcases mul_eq_zero.mp (h' i (Finset.mem_univ i)) with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · exact absurd h (hσ i).ne'
  have hdisj : LinearMap.range L ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨c, rfl⟩, haN⟩
    by_contra ha
    exact absurd (hN _ haN ha) (not_lt.mpr (hnonneg c))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range L) N
  rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_le (LinearMap.range L ⊔ N)
  rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  omega

/-- The trace form of `H` has positive index at most `2n`. -/
theorem vg_posBound (hd : 0 < d) : (X.vg_space hd).PosBound (2 * m) := by
  intro ι _ t horth hpos
  have h := X.vg_card_add_finrank_le 1
    (Module.End.eigenspace (A.J ∘ₗ X.vg_FR).dualMap (Real.sqrt d)) (fun a ha ha0 => by
    rw [X.vg_q_eigen _ a ha, one_mul]
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have := X.ample.2 a ha0
    rw [← vg_eval2L_apply] at this
    nlinarith) t horth (fun i => by
      have := hpos i
      rw [one_mul]
      exact_mod_cast this)
  have := X.vg_finrank_N
  omega

/-- The trace form of `H` has negative index at most `2n`. -/
theorem vg_negBound (hd : 0 < d) : (X.vg_space hd).NegBound (2 * m) := by
  intro ι _ t horth hneg
  have h := X.vg_card_add_finrank_le (-1)
    (Module.End.eigenspace (A.J ∘ₗ X.vg_FR).dualMap (-Real.sqrt d)) (fun a ha ha0 => by
    rw [X.vg_q_eigen _ a ha]
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have := X.ample.2 a ha0
    rw [← vg_eval2L_apply] at this
    nlinarith) t horth (fun i => by
      have := hneg i
      have h' : (X.E (t i) (X.fT (t i)) : ℝ) < 0 := by exact_mod_cast this
      linarith)
  have := X.vg_finrank_P
  omega

theorem vg_finrank_dual : finrank ℚ (Module.Dual ℚ (H1 ℚ (2 * m))) = 2 * (2 * m) := by
  rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **Landherr's theorem (split case) for `X`**: if the discriminant is `(-1)ⁿ`, van Geemen's
Hermitian form of `X` is hyperbolic. -/
theorem vg_hypSys (hm : 0 < m) (hd : 0 < d) (hdisc : X.DiscIs ((-1) ^ m)) :
    Nonempty ((X.vg_space hd).HypSys m) := by
  obtain ⟨b, hb, k, -, hk⟩ := hdisc
  exact (X.vg_space hd).landherr_split hm vg_finrank_dual (X.vg_posBound hd) (X.vg_negBound hd)
    b hb k hk

end PolarizedWeilType

/-! ### The isomorphism `ψ` and the transported complex structure -/

/-- The isomorphism `ψ` of `H¹` with transpose `φ`: `x ∘ ψ = φ(x)` for `x ∈ H₁ = (H¹)*`. -/
noncomputable def vg_psi {g : ℕ} (φ : Module.Dual ℚ (H1 ℚ g) ≃ₗ[ℚ] Module.Dual ℚ (H1 ℚ g)) :
    H1 ℚ g ≃ₗ[ℚ] H1 ℚ g :=
  (Module.evalEquiv ℚ (H1 ℚ g)).trans (φ.dualMap.trans (Module.evalEquiv ℚ (H1 ℚ g)).symm)

theorem vg_psi_apply {g : ℕ} (φ : Module.Dual ℚ (H1 ℚ g) ≃ₗ[ℚ] Module.Dual ℚ (H1 ℚ g))
    (x : Module.Dual ℚ (H1 ℚ g)) (w : H1 ℚ g) : x (vg_psi φ w) = φ x w := by
  simp only [vg_psi, LinearEquiv.trans_apply, Module.apply_evalEquiv_symm_apply,
    LinearEquiv.dualMap_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]

theorem vg_comp_psi {g : ℕ} (φ : Module.Dual ℚ (H1 ℚ g) ≃ₗ[ℚ] Module.Dual ℚ (H1 ℚ g))
    (x : Module.Dual ℚ (H1 ℚ g)) : x ∘ₗ (vg_psi φ).toLinearMap = φ x :=
  LinearMap.ext fun w => vg_psi_apply φ x w

section Transport

variable {n : ℕ} {d : ℚ} {A A₀ : AbVar (2 * n)} (X : PolarizedWeilType A d)
  (X₀ : PolarizedWeilType A₀ d)
  (φ : Module.Dual ℚ (H1 ℚ (2 * n)) ≃ₗ[ℚ] Module.Dual ℚ (H1 ℚ (2 * n)))

/-- `ψ` is `K`-linear: `ψ ∘ η(k) = η₀(k) ∘ ψ`, since its transpose `φ` commutes with `f`. -/
theorem vg_psi_eta (hd : 0 < d) (hφf : ∀ x, φ (X₀.fT x) = X.fT (φ x)) (k : Kd d) :
    (vg_psi φ).toLinearMap ∘ₗ X.η k = X₀.η k ∘ₗ (vg_psi φ).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro x
  rw [map_sub, sub_eq_zero]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, vg_psi_apply]
  have h1 : x (X₀.η k (vg_psi φ w)) = (x ∘ₗ X₀.η k) (vg_psi φ w) := rfl
  have h2 : x ∘ₗ X₀.η k = Kd.ratPart d k • x + Kd.sqrtNegCoeff d k • X₀.fT x := by
    refine LinearMap.ext fun v => ?_
    rw [vg_eta_eq hd X₀.η k]
    simp [PolarizedWeilType.fT, LinearMap.dualMap_apply]
  rw [h1, vg_psi_apply, h2, map_add, map_smul, map_smul, hφf, vg_eta_eq hd X.η k]
  simp [PolarizedWeilType.fT, LinearMap.dualMap_apply]

/-- `ψ` maps the polarization of `X` to that of `X₀`: `⟪ψ_* h, a ∧ b⟫ = E(φ a, φ b) = E₀(a, b)`. -/
theorem vg_psi_h (hφE : ∀ x y, X.E (φ x) (φ y) = X₀.E x y) :
    ExteriorAlgebra.map (vg_psi φ).toLinearMap X.h = X₀.h := by
  apply main_eq_of_dc (main_map_mem_exteriorPower _ 2 X.ample.mem_exteriorPower_two)
    X₀.ample.mem_exteriorPower_two
  intro a b
  rw [main_dc_map, vg_comp_psi, vg_comp_psi]
  have h := hφE a b
  simp only [PolarizedWeilType.E, eval2, main_coord_empty, AlgHom.toLinearMap_apply, D] at h
  exact h

/-- **The transported complex structure** `J' = ψ_ℝ ∘ J ∘ ψ_ℝ⁻¹` lies in the Weil-type period
domain of `(η₀, h₀)`. -/
theorem vg_transport_mem (hd : 0 < d) (hφf : ∀ x, φ (X₀.fT x) = X.fT (φ x))
    (hφE : ∀ x y, X.E (φ x) (φ y) = X₀.E x y) :
    bcMap ℚ ℝ (vg_psi φ).toLinearMap ∘ₗ A.J ∘ₗ bcMap ℚ ℝ (vg_psi φ).symm.toLinearMap ∈
      WeilDomain X₀.η X₀.h := by
  set ψ := vg_psi φ with hψ
  have hψψ' : ψ.toLinearMap ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
    ext1 w; simp
  have hψ'ψ : ψ.symm.toLinearMap ∘ₗ ψ.toLinearMap = LinearMap.id := by
    ext1 w; simp
  have hη₀ : ∀ k, X₀.η k = ψ.toLinearMap ∘ₗ X.η k ∘ₗ ψ.symm.toLinearMap := fun k => by
    rw [← LinearMap.comp_assoc, vg_psi_eta X X₀ φ hd hφf k, LinearMap.comp_assoc, hψψ',
      LinearMap.comp_id]
  -- real base change
  set Ψ := bcMap ℚ ℝ ψ.toLinearMap with hΨ
  set Ψ' := bcMap ℚ ℝ ψ.symm.toLinearMap with hΨ'
  have hΨΨ' : ∀ w, Ψ (Ψ' w) = w := fun w => by
    rw [← LinearMap.comp_apply, hΨ, hΨ', ← main_bcMap_comp, hψψ', main_bcMap_id,
      LinearMap.id_apply]
  have hΨ'Ψ : ∀ w, Ψ' (Ψ w) = w := fun w => by
    rw [← LinearMap.comp_apply, hΨ, hΨ', ← main_bcMap_comp, hψ'ψ, main_bcMap_id,
      LinearMap.id_apply]
  set J' := Ψ ∘ₗ A.J ∘ₗ Ψ' with hJ'
  have hJ'Ψ : J' ∘ₗ Ψ = Ψ ∘ₗ A.J := by
    refine LinearMap.ext fun w => ?_
    simp only [hJ', LinearMap.comp_apply, hΨ'Ψ]
  have hJJ : ∀ w, A.J (A.J w) = -w := fun w => by
    have := LinearMap.congr_fun A.isComplex w
    simpa using this
  have hcs : IsComplexStructure J' := by
    refine LinearMap.ext fun w => ?_
    simp only [hJ', Module.End.mul_apply, LinearMap.comp_apply, hΨ'Ψ, hJJ, map_neg, hΨΨ']
    simp
  -- complex base change
  let ΨC : H1 ℂ (2 * n) ≃ₗ[ℂ] H1 ℂ (2 * n) :=
    LinearEquiv.ofLinearMap (bcMap ℚ ℂ ψ.toLinearMap) (bcMap ℚ ℂ ψ.symm.toLinearMap)
      (by rw [← main_bcMap_comp, hψψ', main_bcMap_id])
      (by rw [← main_bcMap_comp, hψ'ψ, main_bcMap_id])
  have hΨC : ∀ T : Module.End ℚ (H1 ℚ (2 * n)),
      bcMap ℚ ℂ (ψ.toLinearMap ∘ₗ T ∘ₗ ψ.symm.toLinearMap) =
        ΨC.toLinearMap ∘ₗ bcMap ℚ ℂ T ∘ₗ ΨC.symm.toLinearMap := fun T => by
    rw [main_bcMap_comp, main_bcMap_comp]
    rfl
  have hH10 : H10 (2 * n) J' = (H10 (2 * n) A.J).map ΨC.toLinearMap := by
    rw [H10, H10, main_lef_complexifyH1_eq, main_lef_complexifyH1_eq, hJ', main_bcMap_comp,
      main_bcMap_comp, hΨ, hΨ', vg_bcMap_bcMap, vg_bcMap_bcMap]
    exact s24b_eigenspace_conj ΨC _ _
  have hweil : ∀ μ : ℂ, Module.finrank ℂ ↥(Module.End.eigenspace (bcMap ℚ ℂ (X₀.η (Kd.sqrtNeg d)))
      μ ⊓ H10 (2 * n) J') = Module.finrank ℂ ↥(Module.End.eigenspace
        (bcMap ℚ ℂ (X.η (Kd.sqrtNeg d))) μ ⊓ H10 (2 * n) A.J) := fun μ => by
    rw [hη₀, hΨC, s24b_eigenspace_conj, hH10, ← Submodule.map_inf _ ΨC.injective]
    exact LinearEquiv.finrank_map_eq ΨC _
  -- the polarization
  have hh₀ : X₀.h = ExteriorAlgebra.map ψ.toLinearMap X.h := (vg_psi_h X X₀ φ hφE).symm
  have hbc : bcS ℚ ℝ (2 * n) X₀.h = ExteriorAlgebra.map Ψ (bcS ℚ ℝ (2 * n) X.h) := by
    rw [hh₀, main_bcS_map]
  refine ⟨hcs, fun k => ?_, by rw [hweil]; exact X.weil₁, by rw [hweil]; exact X.weil₂,
    ⟨?_, fun a ha => ?_⟩, X₀.norm⟩
  · -- `η₀(k)` are Hodge maps for `J'`
    have h := X.isHodge k
    refine LinearMap.ext fun w => ?_
    have hk := LinearMap.congr_fun h (Ψ' w)
    simp only [LinearMap.comp_apply] at hk
    rw [hη₀, main_bcMap_comp, main_bcMap_comp]
    simp only [LinearMap.comp_apply, hJ', ← hΨ, ← hΨ', hΨ'Ψ, hk]
  · -- `h₀` is of type `(1,1)` for `J'`
    rw [hh₀]
    refine main_lef_hodge_one_of_map hcs
      (main_map_mem_exteriorPower _ 2 X.ample.mem_exteriorPower_two) ?_
    rw [main_bcS_map, ← hΨ, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hJ'Ψ,
      ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply, main_lef_map_bcS_of_hodge X.ample.1]
  · -- positivity
    rw [hbc, vg_eval2_map]
    have h1 : (a ∘ₗ J') ∘ₗ Ψ = (a ∘ₗ Ψ) ∘ₗ A.J := by
      rw [LinearMap.comp_assoc, hJ'Ψ, LinearMap.comp_assoc]
    rw [h1]
    refine X.ample.2 _ fun h0 => ha ?_
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun h0 (Ψ' w)
    simpa [hΨΨ'] using this

end Transport

/-! ### Connectedness of the Weil-type period domain of `X × X̂` -/

/-- The Weil-type period domain of `X × X̂` (for `n > 0`) is preconnected: it is the image of the
path-connected period domain `Ω_P` of `P_Θ` (`weilDomain_eq_image_OmegaP`, `KSecant.s4_OmegaP_join`)
under the continuous map `I ↦ -I` in the coordinates of the model. -/
theorem weilDomainMat_isPreconnected {n : ℕ} (hn : 0 < n) {d : ℚ} (hd : 0 < d)
    (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n))) (hη : η (Kd.sqrtNeg d) = fX n d) :
    IsPreconnected (WeilDomainMat η (hX n d)) := by
  rw [WeilDomainMat, weilDomain_eq_image_OmegaP n d hd hn η hη, Set.image_image]
  let := endTopology n
  set P := PStd n d hd hn
  set hW := PStd_isCompl n d hd hn
  have hpre : IsPreconnected (P.OmegaP hW) := by
    refine isPreconnected_of_forall_pair fun x hx y hy => ?_
    obtain ⟨⟨γ, hγ, h0, h1, hmem⟩, -⟩ := P.s4_OmegaP_join hW x y hx hy
    refine ⟨γ '' Set.Icc 0 1, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩,
      isPreconnected_Icc.image γ hγ.continuousOn⟩
    rintro _ ⟨t, -, rfl⟩
    exact hmem t
  -- `I ↦ -I`, transported to the model and written as a matrix, is linear
  let B := LinearMap.toMatrix (basisV ℝ n) (basisV ℝ n)
  let T : Module.End ℝ (V ℝ n) →ₗ[ℝ] Matrix (Fin (2 * (2 * n))) (Fin (2 * (2 * n))) ℝ :=
    LinearMap.toMatrix'.toLinearMap ∘ₗ (coordV ℝ n).conj.toLinearMap ∘ₗ (-LinearMap.id)
  have hT : ∀ I, T I = LinearMap.toMatrix' (transportEnd n (-I)) := fun I => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.neg_apply,
      LinearMap.id_apply, LinearEquiv.conj_apply, transportEnd, LinearMap.comp_assoc]
  have hcont : Continuous
      (fun I : Module.End ℝ (V ℝ n) => LinearMap.toMatrix' (transportEnd n (-I))) := by
    have h1 : Continuous (T ∘ₗ B.symm.toLinearMap) := LinearMap.continuous_of_finiteDimensional _
    have h2 : Continuous B := continuous_induced_dom
    have h3 : (fun I : Module.End ℝ (V ℝ n) => LinearMap.toMatrix' (transportEnd n (-I))) =
        (T ∘ₗ B.symm.toLinearMap) ∘ B := by
      funext I
      simp [hT]
    rw [h3]
    exact h1.comp h2
  exact hpre.image _ hcont.continuousOn

/-! ### The theorem -/

/-- **[van Geemen, Th. 5.2(3)]**, the case used in Theorem 1.5.1: a polarized abelian `2n`-fold of
Weil type `X` (`n > 0`) for `K = ℚ(√-d)` with discriminant `(-1)ⁿ` and any polarized abelian
`2n`-fold of Weil type `X₀` with the action `η₀(√-d) = f` and the polarization `h` of `X × X̂`
(and discriminant `(-1)ⁿ`, which holds for every such `X₀` by Lemma 3.1.3, `discIs_XXhat`) lie in
one connected family up to isogeny: a `K`-linear isomorphism `ψ` of their `H¹` maps the
polarization of `X` to that of `X₀` (`c' = 1`) and carries the complex structure of `X` into the
Weil-type period domain of `(η₀, h)`, which is connected.

Proof: by Landherr's theorem (split case, `vg_HermSpace.landherr_split`) van Geemen's Hermitian
forms of `X` and `X₀`, of signature `(n, n)` (the Weil condition and the positivity of the
polarization) and discriminant `(-1)ⁿ`, are both hyperbolic, hence isometric by a `K`-linear `φ`
(`vg_HermSpace.exists_isometry`); `ψ` is the inverse transpose of `φ`. The period domain of
`X × X̂` is the image of the connected domain `Ω_P` of §4 (`weilDomainMat_isPreconnected`). -/
theorem vanGeemen_moduli_XXhat {n : ℕ} (hn : 0 < n) {d : ℚ} (hd : 0 < d) (A : AbVar (2 * n))
    (X : PolarizedWeilType A d) (hdisc : X.DiscIs ((-1) ^ n))
    (A₀ : AbVar (2 * n)) (X₀ : PolarizedWeilType A₀ d)
    (hη₀ : X₀.η (Kd.sqrtNeg d) = fX n d) (hh₀ : X₀.h = hX n d) (hdisc₀ : X₀.DiscIs ((-1) ^ n)) :
    ∃ ψ : H1 ℚ (2 * n) ≃ₗ[ℚ] H1 ℚ (2 * n), (∀ k, ψ.toLinearMap ∘ₗ X.η k = X₀.η k ∘ₗ ψ.toLinearMap) ∧
      (∃ c' : ℚ, 0 < c' ∧ ExteriorAlgebra.map ψ.toLinearMap X.h = c' • X₀.h) ∧
      LinearMap.toMatrix' (bcMap ℚ ℝ ψ.toLinearMap ∘ₗ A.J ∘ₗ bcMap ℚ ℝ ψ.symm.toLinearMap) ∈
        connectedComponentIn (WeilDomainMat X₀.η X₀.h) (LinearMap.toMatrix' A₀.J) := by
  obtain ⟨s⟩ := X.vg_hypSys hn hd hdisc
  obtain ⟨s₀⟩ := X₀.vg_hypSys hn hd hdisc₀
  obtain ⟨φ, hφf, hφE⟩ := (X₀.vg_space hd).exists_isometry PolarizedWeilType.vg_finrank_dual
    PolarizedWeilType.vg_finrank_dual s₀ s
  refine ⟨vg_psi φ, fun k => vg_psi_eta X X₀ φ hd hφf k,
    ⟨1, one_pos, by rw [one_smul]; exact vg_psi_h X X₀ φ hφE⟩, ?_⟩
  have hpre := weilDomainMat_isPreconnected hn hd X₀.η hη₀
  rw [← hh₀] at hpre
  have hA₀ : LinearMap.toMatrix' A₀.J ∈ WeilDomainMat X₀.η X₀.h :=
    ⟨A₀.J, ⟨A₀.isComplex, X₀.isHodge, X₀.weil₁, X₀.weil₂, X₀.ample, X₀.norm⟩, rfl⟩
  rw [hpre.connectedComponentIn hA₀]
  exact ⟨_, vg_transport_mem X X₀ φ hd hφf hφE, rfl⟩

end WeilClasses
