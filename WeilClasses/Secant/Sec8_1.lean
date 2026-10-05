module

public import WeilClasses.WeilType.Theta
public import WeilClasses.AbelianVariety.Defs
public import WeilClasses.Spinor.Integral
public import WeilClasses.Secant.Defs
public import WeilClasses.PureSpinor.Lemma2_2_1
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal

/-!
# §8.1: `K`-secants on a generic ppav

Statements of the paper's §8.1 (TeX lines 3634–3720). `(X, Θ)` is a principally polarized abelian
`n`-fold; `θ : H¹(X, ℚ)* → H¹(X, ℚ)` is the contraction with `Θ` ((2.4.3), `contractOne`), and the
paper's `f := (φ_Θ^*)⁻¹ : H¹(X) → H¹(X̂)` is `(-θ)⁻¹` (the footnote of §2.4 identifies `-θ` with
`φ_Θ^*`; `WeilClasses.fOfTheta`). All the identities below are insensitive to the sign of `f`.

## Definitions

* `WeilClasses.fOfTheta θ hθ = -θ⁻¹ : H¹(X, F) → H¹(X̂, F) = H¹(X, F)*` (for invertible `θ`).
* `WeilClasses.hdgMatrix θ hθ a`: the endomorphism of `V_F` with matrix
  `[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]` in the paper's order `(w, θ)` ((8.1.2)); in our order
  `(y, w)` it is `(y, w) ↦ (a₂₁ f(w) + a₂₂ y, a₁₁ w + a₁₂ f⁻¹(y))` (`a = !![a₁₁, a₁₂; a₂₁, a₂₂]`,
  `Fin 2` indices from `0`).
* `WeilClasses.SOplusHdg θ hθ`: the matrices with `a₁₁a₂₂ - a₂₁a₁₂ = 1` (the paper's
  `SO⁺_Hdg(V_F)`, *defined* in §8.1 as this group for `F = ℚ, K`).
* `WeilClasses.iotaTheta Θ c = Σ_j c_j Θ^{n-j}/(n-j)!`: the involution `ι` (interchanging the
  coefficients of `Θ^j/j!` and `Θ^{n-j}/(n-j)!`) applied to `Σ_j c_j Θ^j/j!`.
* `WeilClasses.alphaPP`, `WeilClasses.betaPP`: the classes `α`, `β` enumerating the non-rational pure
  spinors (closed forms of the paper).

## Statements

* (8.1.1) `equation8_1_1`; (8.1.2) `equation8_1_2` (corrected, see below); `SO⁺_Hdg`:
  `hdgMatrix_pairing`, `exists_rho_eq_hdgMatrix`.
* **Lemma 8.1.1** (`lemma8_1_1`), by the paper's case split and stabilizer step, with the points of
  the orbit `ℙ¹_K` given by coset representatives instead of the rational normal curve (departure,
  reason 2, see the docstring); and the Möbius form of the action on the pure spinors `exp(kΘ)`
  (`m_exp_mem_span_hdgMatrix`, used for `ι`).
* `ι`: `iotaTheta_exp` (`k^n exp(k⁻¹Θ) = ι(exp(kΘ))`) and the claim that the matrix
  `[[0, -f⁻¹], [f, 0]]` extends `ι`, corrected to `ι ∘ τ` (`iota_tau_extends`, see below).
* The enumeration `q^n exp(kΘ) = α + τ√-d β` (`enumeration8_1`), the displayed expansions
  (`alphaPP_expansion`, `betaPP_expansion` (misprint corrected)),
  `α, β ∈ H^{ev}(X, ℤ)` (`alphaPP_mem_SZ`, `betaPP_mem_SZ`), saturation for `q = 1`
  (`saturated_of_q_eq_one`), and the table of `∫_X (aα + bβ)^∨ (aα + bβ)` (`chi8_1_odd`, `chi8_1_two`,
  `chi8_1_four`, `chi8_1_even`), with `w^∨ = τ(w)` (Remark 5.2.3).

## Corrections of the paper (REPORT.md; checked numerically, exact arithmetic)

* (8.1.2) needs `End_ℚ(X) = ℚ`, which a cyclic Néron–Severi group does not imply (Jacobians of
  Picard curves): stated with that hypothesis, as agreed with the project owner (`equation8_1_2`).
* `[[0, -f⁻¹], [f, 0]]` acts on the pure spinors by `exp(kΘ) ↦ exp(-k⁻¹Θ)`, so it extends `ι ∘ τ`,
  not `ι` (`exp(kΘ) ↦ exp(k⁻¹Θ)` projectively): stated in that form, as agreed with the project
  owner (`iota_tau_extends`).
* The displayed expansion of `β`: the coefficient of `Θ⁴/4!` is `4 q^{n-4} ρ(ρ² - τ²d)`, not
  `q^{n-4} ρ(ρ² - τ²d)` (the closed form is right); an obvious misprint, corrected
  (`betaPP_expansion`).

## Left out (sheaf-theoretic)

The identification of `χ(F^∨ ⊗ F)` with `∫ ch(F^∨) ch(F)` (Hirzebruch–Riemann–Roch), the remark on the
minimum of `|χ(F^∨ ⊗ F)|` over Chern characters of objects and the lift of `ι` to `Aut(Dᵇ(X))`, and
the relation of `χ` to `Ext²(F, F)` and semiregularity for `n = 4`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## The matrices of (8.1.2) -/

section Matrices

variable {F : Type*} [Field F] {n : ℕ}

/-- `f = (φ_Θ^*)⁻¹ = (-θ)⁻¹ : H¹(X, F) → H¹(X̂, F) = H¹(X, F)*` (§8.1), for an invertible `θ`. -/
noncomputable def fOfTheta (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ) :
    H1 F n →ₗ[F] Module.Dual F (H1 F n) :=
  -((LinearEquiv.ofBijective θ hθ).symm : H1 F n →ₗ[F] Module.Dual F (H1 F n))

/-- The endomorphism of `V_F` with matrix `[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]` ((8.1.2), the
paper's order `(w, θ)`), `f⁻¹ = -θ`: in our order, `(y, w) ↦ (a₂₁ f(w) + a₂₂ y, a₁₁ w - a₁₂ θ(y))`,
with `a = !![a₁₁, a₁₂; a₂₁, a₂₂]`. -/
noncomputable def hdgMatrix (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (a : Matrix (Fin 2) (Fin 2) F) : V F n →ₗ[F] V F n :=
  LinearMap.prod
    (a 1 0 • (fOfTheta θ hθ ∘ₗ LinearMap.snd F _ _) + a 1 1 • LinearMap.fst F _ _)
    (a 0 0 • LinearMap.snd F _ _ + a 0 1 • ((-θ) ∘ₗ LinearMap.fst F _ _))

/-- **`SO⁺_Hdg(V_F)`** (§8.1): the matrices (8.1.2) with coefficients in `F` and
`a₁₁a₂₂ - a₂₁a₁₂ = 1` (the paper's definition for `F = ℚ` and, "allowing the coefficients to belong
to `K`", for `F = K`). -/
def SOplusHdg (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ) :
    Set (V F n →ₗ[F] V F n) :=
  {A | ∃ a : Matrix (Fin 2) (Fin 2) F, a.det = 1 ∧ A = hdgMatrix θ hθ a}

end Matrices

section MatricesCharZero

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-! ### Helpers (prefix `s8_`): `θ` is antisymmetric, the matrices (8.1.2) compose as matrices -/

omit [CharZero F] in
theorem s8_contractOne_smul (c : F) (ξ : S F n) :
    contractOne F n (c • ξ) = c • contractOne F n ξ := by
  ext y i
  simp [contractOne, map_smul]

/-- `θ` is antisymmetric: `a(θ b) = -b(θ a)` for `Θ ∈ ⋀² H¹(X)` (`θ(y) = y ⌋ Θ`). -/
theorem s8_theta_antisymm {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (a b : Module.Dual F (H1 F n)) :
    a (contractOne F n Θ b) = -b (contractOne F n Θ a) := by
  have key : ∀ a b : Module.Dual F (H1 F n), a (contractOne F n Θ b) =
      ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) a (contractLeft (Q := 0) b Θ)) := by
    intro a b
    change _ = ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) a (D F n b Θ))
    rw [← ι_contractOne F n Θ hΘ b]
    change _ = ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) a
      (CliffordAlgebra.ι 0 (contractOne F n Θ b)))
    rw [contractLeft_ι]
    simp [ExteriorAlgebra.algebraMapInv]
  rw [key, key, contractLeft_comm, map_neg]

/-- `θ⁻¹` is antisymmetric: `(θ⁻¹ w)(w') = -(θ⁻¹ w')(w)`. -/
theorem s8_thetaInv_antisymm {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (w w' : H1 F n) :
    (LinearEquiv.ofBijective _ hθ).symm w w' = -((LinearEquiv.ofBijective _ hθ).symm w' w) := by
  set y := (LinearEquiv.ofBijective _ hθ).symm w
  set y' := (LinearEquiv.ofBijective _ hθ).symm w'
  have hw : contractOne F n Θ y = w := (LinearEquiv.ofBijective _ hθ).apply_symm_apply w
  have hw' : contractOne F n Θ y' = w' := (LinearEquiv.ofBijective _ hθ).apply_symm_apply w'
  rw [← hw, ← hw', s8_theta_antisymm hΘ]

omit [CharZero F] in
theorem s8_fOfTheta_apply (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (w : H1 F n) : fOfTheta θ hθ w = -(LinearEquiv.ofBijective θ hθ).symm w := rfl

omit [CharZero F] in
/-- `f(θ y) = -y`. -/
theorem s8_fOfTheta_theta (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (y : Module.Dual F (H1 F n)) : fOfTheta θ hθ (θ y) = -y := by
  rw [s8_fOfTheta_apply, neg_inj]
  exact (LinearEquiv.ofBijective θ hθ).symm_apply_apply y

omit [CharZero F] in
/-- `θ(f w) = -w`. -/
theorem s8_theta_fOfTheta (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (w : H1 F n) : θ (fOfTheta θ hθ w) = -w := by
  rw [s8_fOfTheta_apply, map_neg, neg_inj]
  exact (LinearEquiv.ofBijective θ hθ).apply_symm_apply w

omit [CharZero F] in
theorem s8_hdgMatrix_apply (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (a : Matrix (Fin 2) (Fin 2) F) (v : V F n) :
    hdgMatrix θ hθ a v =
      (a 1 0 • fOfTheta θ hθ v.2 + a 1 1 • v.1, a 0 0 • v.2 - a 0 1 • θ v.1) := by
  simp [hdgMatrix, sub_eq_add_neg]

omit [CharZero F] in
/-- The matrices (8.1.2) compose as `2 × 2` matrices (`f⁻¹ f = id`, `f f⁻¹ = id`). -/
theorem s8_hdgMatrix_comp (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (a b : Matrix (Fin 2) (Fin 2) F) :
    hdgMatrix θ hθ a ∘ₗ hdgMatrix θ hθ b = hdgMatrix θ hθ (a * b) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, s8_hdgMatrix_apply, map_add, map_smul, map_sub,
    s8_fOfTheta_theta, s8_theta_fOfTheta, Matrix.mul_apply, Fin.sum_univ_two]
  ext1 <;> simp only <;> module

omit [CharZero F] in
theorem s8_hdgMatrix_one (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ) :
    hdgMatrix θ hθ 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp [s8_hdgMatrix_apply]

/-- **(8.1.1)** (`eq-identity-expressing-anti-symmetry-of-theta`): `f(w)(f⁻¹(θ')) = -θ'(w)` for
`w ∈ H¹(X)` and `θ' ∈ H¹(X̂) = H¹(X)*`, where `θ = contractOne Θ` for a class `Θ ∈ ⋀² H¹(X, F)`
with `θ` invertible, `f⁻¹ = -θ`. (Checked numerically for random non-degenerate `Θ`, `n ≤ 3`.) -/
theorem equation8_1_1 (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (w : H1 F n) (y : Module.Dual F (H1 F n)) :
    fOfTheta (contractOne F n Θ) hθ w ((-contractOne F n Θ) y) = -y w := by
  -- `f(w)(-θ y) = (θ⁻¹ w)(θ y) = -y(θ θ⁻¹ w)` (antisymmetry of `θ`)
  simp only [s8_fOfTheta_apply, LinearMap.neg_apply, map_neg, neg_neg]
  rw [s8_theta_antisymm hΘ]
  congr 1
  exact congrArg y ((LinearEquiv.ofBijective _ hθ).apply_symm_apply w)

/-- (§8.1, TeX lines 3653–3655) "The identity (8.1.1) implies that the group `SO⁺_Hdg(V_ℚ)` is the
subgroup of invertible elements of `End_Hdg(V_ℚ)` with `a₁₁a₂₂ - a₂₁a₁₂ = 1`": the matrix (8.1.2)
multiplies the pairing (1.2.2) by its determinant, `(A x, A y)_V = (a₁₁a₂₂ - a₂₁a₁₂)(x, y)_V`. -/
theorem hdgMatrix_pairing (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (a : Matrix (Fin 2) (Fin 2) F) (x y : V F n) :
    pairing F n (hdgMatrix (contractOne F n Θ) hθ a x) (hdgMatrix (contractOne F n Θ) hθ a y) =
      a.det * pairing F n x y := by
  -- the identities: `f(w)(w') + f(w')(w) = 0`, `f(w)(-θ y) = -y(w)`, `y(θ y') + y'(θ y) = 0`
  have I1 : ∀ w w' : H1 F n, fOfTheta (contractOne F n Θ) hθ w w' +
      fOfTheta (contractOne F n Θ) hθ w' w = 0 := by
    intro w w'
    rw [s8_fOfTheta_apply, s8_fOfTheta_apply, LinearMap.neg_apply, LinearMap.neg_apply,
      s8_thetaInv_antisymm hΘ hθ w w']
    ring
  have I2 : ∀ (w : H1 F n) (y : Module.Dual F (H1 F n)),
      fOfTheta (contractOne F n Θ) hθ w (contractOne F n Θ y) = y w := by
    intro w y
    have := equation8_1_1 Θ hΘ hθ w y
    rw [LinearMap.neg_apply, map_neg, neg_inj] at this
    exact this
  have I3 : ∀ y y' : Module.Dual F (H1 F n),
      y (contractOne F n Θ y') + y' (contractOne F n Θ y) = 0 := by
    intro y y'
    rw [s8_theta_antisymm hΘ y y']
    ring
  rw [s8_hdgMatrix_apply, s8_hdgMatrix_apply, s8_pairing_apply, s8_pairing_apply,
    Matrix.det_fin_two]
  simp only [map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (a 1 0 * a 0 0) * I1 x.2 y.2 - (a 1 1 * a 0 1) * I3 x.1 y.1 -
    (a 1 0 * a 0 1) * (I2 x.2 y.1 + I2 y.2 x.1)

/-! ### Helpers (prefix `s8_`): spin lifts of the unipotent matrices (Eichler transvections) -/

theorem s8_rho_mul (g h : Spin F n) :
    (rho F n (g * h) : V F n →ₗ[F] V F n) =
      (rho F n g : V F n →ₗ[F] V F n) ∘ₗ (rho F n h : V F n →ₗ[F] V F n) := by
  simp [rho]; rfl

theorem s8_rho_one : (rho F n 1 : V F n →ₗ[F] V F n) = LinearMap.id := by
  simp [rho]

omit [CharZero F] in
theorem s8_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

/-- The spin lift `1 + w u` of the Eichler transvection `E_{u,w}` (`u, w` isotropic and orthogonal)
acts by `v ↦ v + (v, u) w - (v, w) u`. -/
theorem s8_exists_rho_transvection {u w : V F n} (hu : Q F n u = 0) (hw : Q F n w = 0)
    (huw : QuadraticMap.polar (Q F n) u w = 0) :
    ∃ g : Spin F n, ∀ v, rho F n g v =
      v + QuadraticMap.polar (Q F n) v u • w - QuadraticMap.polar (Q F n) v w • u := by
  refine ⟨CliffordAlgebra.spinTransvection s8_Q_nondegenerate hu huw, fun v => ?_⟩
  have h := CliffordAlgebra.coe_spinToSpecialOrthogonal_apply (Q F n)
    (CliffordAlgebra.spinTransvection s8_Q_nondegenerate hu huw) v
  rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_spinTransvection,
    QuadraticMap.transvection_apply] at h
  rw [rho, ← h, hw, zero_mul, zero_smul, sub_zero]

/-- A product of spin lifts of `1 + Nᵢ` with `Nᵢ Nⱼ = 0` lifts `1 + Σ Nᵢ`. -/
theorem s8_exists_rho_id_add_sum {ι : Type*} (s : Finset ι) (N : ι → V F n →ₗ[F] V F n)
    (hN : ∀ i j, N i ∘ₗ N j = 0)
    (hlift : ∀ i, ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = LinearMap.id + N i) :
    ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = LinearMap.id + ∑ i ∈ s, N i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp [s8_rho_one]⟩
  | insert i s hi ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨gi, hgi⟩ := hlift i
    refine ⟨gi * g, ?_⟩
    have h0 : N i ∘ₗ ∑ j ∈ s, N j = 0 := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]
      exact Finset.sum_eq_zero fun j _ => by
        rw [← LinearMap.comp_apply, hN i j, LinearMap.zero_apply]
    rw [s8_rho_mul, hgi, hg, Finset.sum_insert hi, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.comp_add, LinearMap.id_comp, LinearMap.id_comp, h0]
    abel

omit [CharZero F] in
theorem s8_polar_Q (x y : V F n) : QuadraticMap.polar (Q F n) x y = x.1 y.2 + y.1 x.2 :=
  s8_pairing_apply F n x y

/-- The upper unipotent matrix `[[1, b], [0, 1]]`, `(y, w) ↦ (y, w - bθ(y))`, lies in `ρ(Spin(V_F))`:
a product of `2n` Eichler transvections with isotropic vectors in `H¹(X)`. -/
theorem s8_exists_rho_upper {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (b : F) :
    ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) =
      hdgMatrix (contractOne F n Θ) hθ !![1, b; 0, 1] := by
  let γ : Fin (2 * n) → H1 F n := fun i => (-(b / 2)) • contractOne F n Θ (f F n i)
  let N : Fin (2 * n) → V F n →ₗ[F] V F n := fun i =>
    LinearMap.inr F _ _ ∘ₗ ((Module.Dual.eval F (H1 F n) (e F n i)).smulRight (γ i) -
      (Module.Dual.eval F (H1 F n) (γ i)).smulRight (e F n i)) ∘ₗ LinearMap.fst F _ _
  have hNapp : ∀ i v, N i v = (0, v.1 (e F n i) • γ i - v.1 (γ i) • e F n i) := fun i v => rfl
  have hN : ∀ i j, N i ∘ₗ N j = 0 := fun i j => LinearMap.ext fun v => by
    simp [hNapp]
  have hlift : ∀ i, ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = LinearMap.id + N i := by
    intro i
    obtain ⟨g, hg⟩ := s8_exists_rho_transvection (u := (0, e F n i)) (w := (0, γ i))
      (by simp [Q]) (by simp [Q]) (by simp [])
    refine ⟨g, LinearMap.ext fun v => ?_⟩
    rw [LinearEquiv.coe_coe, hg, LinearMap.add_apply, LinearMap.id_apply, hNapp, s8_polar_Q,
      s8_polar_Q]
    ext1 <;> simp [sub_eq_add_neg, add_assoc]
  obtain ⟨g, hg⟩ := s8_exists_rho_id_add_sum Finset.univ N hN hlift
  refine ⟨g, hg.trans (LinearMap.ext fun v => ?_)⟩
  -- `Σᵢ (y(eᵢ) γᵢ - y(γᵢ) eᵢ) = -bθ(y)` (antisymmetry of `θ`)
  have h1 : ∑ i, v.1 (e F n i) • γ i = (-(b / 2)) • contractOne F n Θ v.1 := by
    simp only [γ, smul_comm (v.1 _), ← Finset.smul_sum, ← map_smul, ← map_sum]
    rw [← s8_dual_eq_sum]
  have h2 : ∑ i, v.1 (γ i) • e F n i = (b / 2) • contractOne F n Θ v.1 := by
    simp only [γ, map_smul, smul_eq_mul, s8_theta_antisymm hΘ v.1, mul_neg, neg_mul, neg_neg,
      mul_smul, ← Finset.smul_sum]
    congr 1
    exact (s8_H1_eq_sum F n (contractOne F n Θ v.1)).symm
  rw [LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, s8_hdgMatrix_apply]
  simp only [hNapp]
  ext1
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_add, Prod.snd_sum, Finset.sum_sub_distrib, h1, h2]
    simp
    module

/-- The lower unipotent matrix `[[1, 0], [c, 1]]`, `(y, w) ↦ (y + c f(w), w)`, lies in
`ρ(Spin(V_F))`: a product of `2n` Eichler transvections with isotropic vectors in `H¹(X̂)`. -/
theorem s8_exists_rho_lower {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (c : F) :
    ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) =
      hdgMatrix (contractOne F n Θ) hθ !![1, 0; c, 1] := by
  set θ := contractOne F n Θ
  set fθ := fOfTheta θ hθ
  let β : Fin (2 * n) → Module.Dual F (H1 F n) := fun i => (c / 2) • fθ (e F n i)
  let N : Fin (2 * n) → V F n →ₗ[F] V F n := fun i =>
    LinearMap.inl F _ _ ∘ₗ ((LinearMap.proj i).smulRight (β i) -
      (β i).smulRight (f F n i)) ∘ₗ LinearMap.snd F _ _
  have hNapp : ∀ i v, N i v = (v.2 i • β i - β i v.2 • f F n i, 0) := fun i v => rfl
  have hN : ∀ i j, N i ∘ₗ N j = 0 := fun i j => LinearMap.ext fun v => by
    simp [hNapp]
  have hlift : ∀ i, ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = LinearMap.id + N i := by
    intro i
    obtain ⟨g, hg⟩ := s8_exists_rho_transvection (u := (f F n i, 0)) (w := (β i, 0))
      (by simp [Q]) (by simp [Q]) (by simp [])
    refine ⟨g, LinearMap.ext fun v => ?_⟩
    rw [LinearEquiv.coe_coe, hg, LinearMap.add_apply, LinearMap.id_apply, hNapp, s8_polar_Q,
      s8_polar_Q]
    ext1 <;> simp [f, sub_eq_add_neg, add_assoc]
  obtain ⟨g, hg⟩ := s8_exists_rho_id_add_sum Finset.univ N hN hlift
  refine ⟨g, hg.trans (LinearMap.ext fun v => ?_)⟩
  -- `Σᵢ (wᵢ βᵢ - βᵢ(w) fᵢ) = c f(w)` (antisymmetry of `f = -θ⁻¹`)
  have hanti : ∀ w w' : H1 F n, fθ w w' = -(fθ w' w) := by
    intro w w'
    rw [s8_fOfTheta_apply, s8_fOfTheta_apply, LinearMap.neg_apply, LinearMap.neg_apply,
      s8_thetaInv_antisymm hΘ hθ w w', neg_neg]
  have h1 : ∑ i, v.2 i • β i = (c / 2) • fθ v.2 := by
    simp only [β, smul_comm (v.2 _), ← Finset.smul_sum, ← map_smul, ← map_sum]
    rw [← s8_H1_eq_sum]
  have h2 : ∑ i, β i v.2 • f F n i = (-(c / 2)) • fθ v.2 := by
    simp only [β, LinearMap.smul_apply, hanti _ v.2, smul_eq_mul, mul_neg, neg_smul, mul_smul,
      ← Finset.smul_sum, Finset.sum_neg_distrib]
    rw [← s8_dual_eq_sum]
  rw [LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, s8_hdgMatrix_apply]
  simp only [hNapp]
  ext1
  · simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_sub_distrib, h1, h2]
    simp
    module
  · simp [Prod.snd_sum]

/-- (§8.1) The matrices (8.1.2) of determinant `1` lie in `SO⁺(V_F) = ρ(Spin(V_F))` (they form
`SL₂(F)`, which has trivial spinor norm). -/
theorem exists_rho_eq_hdgMatrix (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (a : Matrix (Fin 2) (Fin 2) F) (ha : a.det = 1) :
    ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a := by
  -- `SL₂(F)` is generated by the unipotent matrices (Bruhat decomposition)
  have hprod : ∀ g₁ g₂ : Spin F n, ∀ a₁ a₂ : Matrix (Fin 2) (Fin 2) F,
      (rho F n g₁ : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a₁ →
      (rho F n g₂ : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a₂ →
      (rho F n (g₁ * g₂) : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ (a₁ * a₂) := by
    intro g₁ g₂ a₁ a₂ h₁ h₂
    rw [s8_rho_mul, h₁, h₂, s8_hdgMatrix_comp]
  -- `a₁₀ ≠ 0`: `a = [[1, x], [0, 1]] [[1, 0], [a₁₀, 1]] [[1, z], [0, 1]]`
  have hgen : ∀ a : Matrix (Fin 2) (Fin 2) F, a.det = 1 → a 1 0 ≠ 0 →
      ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a := by
    intro a ha h10
    obtain ⟨g₁, h₁⟩ := s8_exists_rho_upper hΘ hθ ((a 0 0 - 1) / a 1 0)
    obtain ⟨g₂, h₂⟩ := s8_exists_rho_lower hΘ hθ (a 1 0)
    obtain ⟨g₃, h₃⟩ := s8_exists_rho_upper hΘ hθ ((a 1 1 - 1) / a 1 0)
    refine ⟨g₁ * g₂ * g₃, ?_⟩
    rw [hprod _ _ _ _ (hprod _ _ _ _ h₁ h₂) h₃]
    congr 1
    rw [Matrix.det_fin_two] at ha
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination ha
  by_cases h10 : a 1 0 = 0
  · -- `a = [[1, 0], [1, 1]] a'` with `a'₁₀ = -a₀₀ ≠ 0`
    have h00 : a 0 0 ≠ 0 := by
      intro h; rw [Matrix.det_fin_two, h, h10] at ha; simp at ha
    obtain ⟨g₁, h₁⟩ := s8_exists_rho_lower hΘ hθ 1
    obtain ⟨g₂, h₂⟩ := hgen (!![1, 0; -1, 1] * a)
      (by rw [Matrix.det_mul, ha]; simp [Matrix.det_fin_two])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h00])
    refine ⟨g₁ * g₂, ?_⟩
    rw [hprod _ _ _ _ h₁ h₂, ← mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact hgen a ha h10

end MatricesCharZero

/-! ## (8.1.2) -/

section Equation812

variable {n : ℕ}

/-! ### Helpers (prefix `s8_`, private): real extensions of rational maps -/

private theorem s8_bcDual_f' (i : Fin (2 * n)) : bcDual ℚ ℝ n (f ℚ n i) = f ℝ n i := by
  change ∑ j, algebraMap ℚ ℝ (f ℚ n i (e ℚ n j)) • f ℝ n j = f ℝ n i
  simp [f, e, Pi.single_apply]

private theorem s8_ext_bcH1 {M : Type*} [AddCommGroup M] [Module ℝ M] {L L' : H1 ℝ n →ₗ[ℝ] M}
    (h : ∀ w, L (bcH1 ℚ ℝ n w) = L' (bcH1 ℚ ℝ n w)) : L = L' :=
  (Pi.basisFun ℝ (Fin (2 * n))).ext fun i => by
    have := h (e ℚ n i)
    rw [s8_bcH1_e] at this
    rw [Pi.basisFun_apply]
    exact this

private theorem s8_ext_bcDual {M : Type*} [AddCommGroup M] [Module ℝ M]
    {L L' : Module.Dual ℝ (H1 ℝ n) →ₗ[ℝ] M}
    (h : ∀ y, L (bcDual ℚ ℝ n y) = L' (bcDual ℚ ℝ n y)) : L = L' :=
  (Pi.basisFun ℝ (Fin (2 * n))).dualBasis.ext fun i => by
    have hi : (Pi.basisFun ℝ (Fin (2 * n))).dualBasis i = f ℝ n i := by
      ext v; simp [f]
    have := h (f ℚ n i)
    rwa [s8_bcDual_f', ← hi] at this

private theorem s8_ext_bcV {M : Type*} [AddCommGroup M] [Module ℝ M] {L L' : V ℝ n →ₗ[ℝ] M}
    (h : ∀ v, L (bcV ℚ ℝ n v) = L' (bcV ℚ ℝ n v)) : L = L' := by
  refine LinearMap.prod_ext (s8_ext_bcDual fun y => ?_) (s8_ext_bcH1 fun w => ?_)
  · have := h (y, 0)
    simpa [bcV] using this
  · have := h (0, w)
    simpa [bcV] using this

private theorem s8_bcMap_bcH1 {g g' : ℕ} (φ : H1 ℚ g →ₗ[ℚ] H1 ℚ g') (v : H1 ℚ g) :
    bcMap ℚ ℝ φ (bcH1 ℚ ℝ g v) = bcH1 ℚ ℝ g' (φ v) := by
  have h1 : ∀ i, φ v i = ∑ x, φ (Pi.single x 1) i * v x := by
    intro i
    have hv : v = ∑ x, v x • (Pi.single x 1 : H1 ℚ g) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, mul_comm]
  ext i
  simp [bcMap, bcH1, Matrix.mulVec, dotProduct, h1]

/-- The real extension `θ_ℝ` of an invertible `θ` is invertible. -/
private theorem s8_bijective_thetaExt {Θ : S ℚ n} (hθ : Function.Bijective (thetaMap n Θ)) :
    Function.Bijective (thetaExt n ℝ Θ) := by
  have hsurj : Function.Surjective (thetaExt n ℝ Θ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun ℝ (Fin (2 * n))).span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := hθ.2 (e ℚ n i)
    refine ⟨bcDual ℚ ℝ n y, ?_⟩
    rw [thetaExt_bcDual, hy, s8_bcH1_e, Pi.basisFun_apply]
    rfl
  refine ⟨?_, hsurj⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq)).mpr hsurj

/-- **(8.1.2)** (`eq-two-by-two-matrix`), corrected: for a principally polarized abelian `n`-fold
`(X, Θ)` with `End_ℚ(X) = ℚ`, `End_ℚ(X × X̂) ≅ End_Hdg(V_ℚ)` is the algebra of the matrices
`[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]`, `a_{ij} ∈ ℚ`.

Model: `X` is `H¹(X, ℝ)` with the complex structure `J`, `Θ` ample; `End_ℚ(X) = ℚ`: every rational
Hodge endomorphism of `H¹(X, ℚ)` is a scalar (`IsHodgeMap`); `End_Hdg(V_ℚ)` is the set of rational
endomorphisms of `V_ℚ` commuting with the complex structure `I_{V_ℝ}` of `X × X̂`
(`productStructure`; `End_ℚ(X × X̂) ≅ End_Hdg(V_ℚ)` is the definition of endomorphisms in the
model).

**Correction of the paper** (agreed with the project owner; REPORT.md). The paper assumes only that
the Néron–Severi group is `ℤΘ`, which does not suffice: the Jacobian `X` of a very general Picard
curve `y³ = x⁴ + a x² + b x + c` (genus `3`, automorphism `y ↦ ζ₃ y`) has `NS(X) = ℤΘ` (the
Rosati-symmetric part of `End_ℚ(X) = ℚ(ζ₃)` is `ℚ`) but `End_ℚ(X × X̂) ≅ M₂(ℚ(ζ₃))` has dimension
`8`; for `n = 1` CM elliptic curves are counterexamples. The hypothesis `End_ℚ(X) = ℚ` (which implies
`NS(X)_ℚ = ℚΘ`) holds for a very general principally polarized abelian variety, the setting of the
section title. The rest of §8.1 does not use (8.1.2): `SO⁺_Hdg(V_K)` is defined as the matrix group
(`SOplusHdg`). -/
theorem equation8_1_2 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : IsAmple n J Θ)
    (hEnd : ∀ B : H1 ℚ n →ₗ[ℚ] H1 ℚ n, IsHodgeMap J J B → ∃ c : ℚ, B = c • LinearMap.id) :
    {A : V ℚ n →ₗ[ℚ] V ℚ n |
        bcEndV ℝ n A * productStructure n J = productStructure n J * bcEndV ℝ n A} =
      Set.range (hdgMatrix (thetaMap n Θ) hΘ.bijective_thetaMap) := by
  -- (The paper states (8.1.2) without proof.) `I = (Jᵀ, -J)` is block-diagonal, so `A` commutes
  -- with `I` iff its four blocks are Hodge morphisms between `H¹(X̂) = H¹(X)*` and `H¹(X)`;
  -- composing with the Hodge isomorphism `θ` (`thetaExt_comp_neg_dualMap`) or its inverse turns each
  -- block into a rational Hodge endomorphism of `H¹(X)`, a scalar by `End_ℚ(X) = ℚ`. Conversely the
  -- matrices (8.1.2) commute with `I` because `θ` does.
  have hθ : Function.Bijective (thetaMap n Θ) := hΘ.bijective_thetaMap
  have hθR : Function.Bijective (thetaExt n ℝ Θ) := s8_bijective_thetaExt hθ
  set θ : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n := thetaMap n Θ with hθdef
  set θR : Module.Dual ℝ (H1 ℝ n) →ₗ[ℝ] H1 ℝ n := thetaExt n ℝ Θ with hθRdef
  set eθ := LinearEquiv.ofBijective θ hθ with heθ
  have hF1 : ∀ y, θR (bcDual ℚ ℝ n y) = bcH1 ℚ ℝ n (θ y) := thetaExt_bcDual n ℝ Θ
  have hF2 : ∀ y, θR (-(J.dualMap y)) = J (θR y) := fun y =>
    LinearMap.congr_fun (thetaExt_comp_neg_dualMap n J hJ Θ hΘ.1) y
  have hθθinv : ∀ w, θ (eθ.symm w) = w := eθ.apply_symm_apply
  have hθinvθ : ∀ y, eθ.symm (θ y) = y := eθ.symm_apply_apply
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hA
    set AR := bcEndV ℝ n A with hARdef
    have hAR : ∀ v, AR (bcV ℚ ℝ n v) = bcV ℚ ℝ n (A v) := bcEndV_bcV ℝ n A
    have hI : ∀ v, AR (productStructure n J v) = productStructure n J (AR v) := fun v =>
      LinearMap.congr_fun hA v
    -- the blocks of `A` and of its real extension
    obtain ⟨P, hP⟩ : ∃ P : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] Module.Dual ℚ (H1 ℚ n),
        ∀ y, P y = (A (y, 0)).1 := ⟨LinearMap.fst ℚ _ _ ∘ₗ A ∘ₗ LinearMap.inl ℚ _ _, fun _ => rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n,
        ∀ y, R y = (A (y, 0)).2 := ⟨LinearMap.snd ℚ _ _ ∘ₗ A ∘ₗ LinearMap.inl ℚ _ _, fun _ => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : H1 ℚ n →ₗ[ℚ] Module.Dual ℚ (H1 ℚ n),
        ∀ w, Q w = (A (0, w)).1 := ⟨LinearMap.fst ℚ _ _ ∘ₗ A ∘ₗ LinearMap.inr ℚ _ _, fun _ => rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : H1 ℚ n →ₗ[ℚ] H1 ℚ n,
        ∀ w, T w = (A (0, w)).2 := ⟨LinearMap.snd ℚ _ _ ∘ₗ A ∘ₗ LinearMap.inr ℚ _ _, fun _ => rfl⟩
    obtain ⟨PR, hPR⟩ : ∃ PR : Module.Dual ℝ (H1 ℝ n) →ₗ[ℝ] Module.Dual ℝ (H1 ℝ n),
        ∀ z, PR z = (AR (z, 0)).1 := ⟨LinearMap.fst ℝ _ _ ∘ₗ AR ∘ₗ LinearMap.inl ℝ _ _, fun _ => rfl⟩
    obtain ⟨RR, hRR⟩ : ∃ RR : Module.Dual ℝ (H1 ℝ n) →ₗ[ℝ] H1 ℝ n,
        ∀ z, RR z = (AR (z, 0)).2 := ⟨LinearMap.snd ℝ _ _ ∘ₗ AR ∘ₗ LinearMap.inl ℝ _ _, fun _ => rfl⟩
    obtain ⟨QR, hQR⟩ : ∃ QR : H1 ℝ n →ₗ[ℝ] Module.Dual ℝ (H1 ℝ n),
        ∀ x, QR x = (AR (0, x)).1 := ⟨LinearMap.fst ℝ _ _ ∘ₗ AR ∘ₗ LinearMap.inr ℝ _ _, fun _ => rfl⟩
    obtain ⟨TR, hTR⟩ : ∃ TR : H1 ℝ n →ₗ[ℝ] H1 ℝ n,
        ∀ x, TR x = (AR (0, x)).2 := ⟨LinearMap.snd ℝ _ _ ∘ₗ AR ∘ₗ LinearMap.inr ℝ _ _, fun _ => rfl⟩
    -- the real blocks extend the rational ones
    have eP : ∀ y, PR (bcDual ℚ ℝ n y) = bcDual ℚ ℝ n (P y) := fun y => by
      rw [hPR, hP]
      have := congrArg Prod.fst (hAR (y, 0))
      simpa [bcV] using this
    have eR : ∀ y, RR (bcDual ℚ ℝ n y) = bcH1 ℚ ℝ n (R y) := fun y => by
      rw [hRR, hR]
      have := congrArg Prod.snd (hAR (y, 0))
      simpa [bcV] using this
    have eQ : ∀ w, QR (bcH1 ℚ ℝ n w) = bcDual ℚ ℝ n (Q w) := fun w => by
      rw [hQR, hQ]
      have := congrArg Prod.fst (hAR (0, w))
      simpa [bcV] using this
    have eT : ∀ w, TR (bcH1 ℚ ℝ n w) = bcH1 ℚ ℝ n (T w) := fun w => by
      rw [hTR, hT]
      have := congrArg Prod.snd (hAR (0, w))
      simpa [bcV] using this
    -- commutation with `I = (Jᵀ, -J)`, blockwise
    have cP : ∀ z, PR (J.dualMap z) = J.dualMap (PR z) := fun z => by
      rw [hPR, hPR]
      have := congrArg Prod.fst (hI (z, 0))
      simpa only [productStructure, LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero,
        neg_zero] using this
    have cR : ∀ z, RR (J.dualMap z) = -(J (RR z)) := fun z => by
      rw [hRR, hRR]
      have := congrArg Prod.snd (hI (z, 0))
      simpa only [productStructure, LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero,
        neg_zero] using this
    have cQ : ∀ x, QR (-(J x)) = J.dualMap (QR x) := fun x => by
      rw [hQR, hQR]
      have := congrArg Prod.fst (hI (0, x))
      simpa only [productStructure, LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero,
        neg_zero] using this
    have cT : ∀ x, TR (-(J x)) = -(J (TR x)) := fun x => by
      rw [hTR, hTR]
      have := congrArg Prod.snd (hI (0, x))
      simpa only [productStructure, LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero,
        neg_zero] using this
    -- `T`, `R θ⁻¹`, `θ Q`, `θ P θ⁻¹` are rational Hodge endomorphisms of `H¹(X, ℚ)`
    have hTH : IsHodgeMap J J T := by
      have hbc : bcMap ℚ ℝ T = TR := s8_ext_bcH1 fun w => by rw [s8_bcMap_bcH1, eT]
      unfold IsHodgeMap
      rw [hbc]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      have := cT x
      rw [map_neg] at this
      exact neg_inj.mp this
    have hRH : IsHodgeMap J J (R ∘ₗ eθ.symm.toLinearMap) := by
      have hbc : bcMap ℚ ℝ (R ∘ₗ eθ.symm.toLinearMap) ∘ₗ θR = RR := s8_ext_bcDual fun y => by
        rw [LinearMap.comp_apply, hF1, s8_bcMap_bcH1, LinearMap.comp_apply,
          LinearEquiv.coe_toLinearMap, hθinvθ, eR]
      unfold IsHodgeMap
      refine s8_ext_bcH1 fun w => ?_
      obtain ⟨y, rfl⟩ : ∃ y, w = θ y := ⟨eθ.symm w, (hθθinv w).symm⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hF1, ← hF2,
        ← LinearMap.comp_apply (bcMap ℚ ℝ _) θR, ← LinearMap.comp_apply (bcMap ℚ ℝ _) θR, hbc,
        map_neg, cR, neg_neg]
    have hQH : IsHodgeMap J J (θ ∘ₗ Q) := by
      have hbc : bcMap ℚ ℝ (θ ∘ₗ Q) = θR ∘ₗ QR := s8_ext_bcH1 fun w => by
        rw [s8_bcMap_bcH1, LinearMap.comp_apply, LinearMap.comp_apply, eQ, hF1]
      unfold IsHodgeMap
      rw [hbc]
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply]
      have h1 : QR (J x) = -(J.dualMap (QR x)) := by
        rw [← cQ, map_neg, neg_neg]
      rw [h1, hF2]
    have hPH : IsHodgeMap J J (θ ∘ₗ P ∘ₗ eθ.symm.toLinearMap) := by
      have hbc : bcMap ℚ ℝ (θ ∘ₗ P ∘ₗ eθ.symm.toLinearMap) ∘ₗ θR = θR ∘ₗ PR :=
        s8_ext_bcDual fun y => by
          rw [LinearMap.comp_apply, hF1, s8_bcMap_bcH1]
          simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hθinvθ]
          rw [eP, hF1]
      unfold IsHodgeMap
      refine s8_ext_bcH1 fun w => ?_
      obtain ⟨y, rfl⟩ : ∃ y, w = θ y := ⟨eθ.symm w, (hθθinv w).symm⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hF1, ← hF2,
        ← LinearMap.comp_apply (bcMap ℚ ℝ _) θR, ← LinearMap.comp_apply (bcMap ℚ ℝ _) θR, hbc,
        LinearMap.comp_apply, LinearMap.comp_apply, map_neg, cP, hF2]
    -- `End_ℚ(X) = ℚ`: the four blocks are scalar multiples of `id, θ, θ⁻¹, id`
    obtain ⟨c₀, hc₀⟩ := hEnd T hTH
    obtain ⟨c₁, hc₁⟩ := hEnd _ hRH
    obtain ⟨c₂, hc₂⟩ := hEnd _ hQH
    obtain ⟨c₃, hc₃⟩ := hEnd _ hPH
    have hTv : ∀ w, T w = c₀ • w := fun w => by rw [hc₀]; rfl
    have hRv : ∀ y, R y = c₁ • θ y := fun y => by
      have := LinearMap.congr_fun hc₁ (θ y)
      simpa [hθinvθ] using this
    have hQv : ∀ w, Q w = c₂ • eθ.symm w := fun w => by
      apply hθ.1
      have := LinearMap.congr_fun hc₂ w
      rw [map_smul, hθθinv]
      simpa using this
    have hPv : ∀ y, P y = c₃ • y := fun y => by
      apply hθ.1
      have := LinearMap.congr_fun hc₃ (θ y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hθinvθ, LinearMap.smul_apply,
        LinearMap.id_apply] at this
      rw [map_smul]
      exact this
    refine ⟨!![c₀, -c₁; -c₂, c₃], ?_⟩
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, w⟩ := v
    have hv : A (y, w) = (P y + Q w, R y + T w) := by
      rw [hP, hQ, hR, hT, ← Prod.fst_add, ← Prod.snd_add, ← map_add, Prod.mk_add_mk, add_zero,
        zero_add]
    rw [s8_hdgMatrix_apply, s8_fOfTheta_apply, hv, hPv, hQv, hRv, hTv]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
      simp only [neg_smul, smul_neg, neg_neg]
      abel
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
      simp only [neg_smul, sub_neg_eq_add]
      abel
  · rintro ⟨a, rfl⟩
    have hfR : ∀ w, fOfTheta θR hθR (bcH1 ℚ ℝ n w) = bcDual ℚ ℝ n (fOfTheta θ hθ w) := fun w => by
      apply hθR.1
      rw [s8_theta_fOfTheta, hF1, s8_theta_fOfTheta, map_neg]
    have hθJ : ∀ y, θR (J.dualMap y) = -(J (θR y)) := fun y => by
      rw [← hF2, map_neg, neg_neg]
    have hfJ : ∀ w, fOfTheta θR hθR (J w) = -(J.dualMap (fOfTheta θR hθR w)) := fun w => by
      apply hθR.1
      rw [s8_theta_fOfTheta, map_neg, hθJ, s8_theta_fOfTheta, map_neg, neg_neg]
    have hext : bcEndV ℝ n (hdgMatrix θ hθ a) = hdgMatrix θR hθR (a.map (algebraMap ℚ ℝ)) := by
      refine s8_ext_bcV fun v => ?_
      obtain ⟨y, w⟩ := v
      rw [bcEndV_bcV, s8_hdgMatrix_apply, s8_hdgMatrix_apply]
      simp only [bcV, LinearMap.prodMap_apply, map_add, map_sub, map_smul, Matrix.map_apply,
        algebraMap_smul, hfR, hF1]
    rw [hext]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, w⟩ := v
    simp only [Module.End.mul_apply, productStructure, LinearMap.prodMap_apply, s8_hdgMatrix_apply,
      LinearMap.neg_apply, map_add, map_sub, map_smul, map_neg, hfJ, hθJ, smul_neg, neg_neg]

end Equation812

/-! ## Helpers (prefix `s8_`): spinors killed by `H¹(X̂)` or by `H¹(X)` -/

section S8Spinors

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s8_proj_mem (s : S F n) (k : ℕ) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k s ∈ ⋀[F]^k (H1 F n) := by
  rw [GradedAlgebra.proj_apply]
  exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (H1 F n)) s k).2

omit [CharZero F] in
theorem s8_proj_of_mem {j k : ℕ} {x : S F n} (hx : x ∈ ⋀[F]^j (H1 F n)) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k x = if j = k then x else 0 := by
  split_ifs with h
  · subst h
    rw [GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (H1 F n)) hx]
  · rw [GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (H1 F n)) hx h]

omit [CharZero F] in
/-- `s = Σ_{k ≤ 2n} s_k` (graded pieces). -/
theorem s8_eq_sum_proj (s : S F n) :
    s = ∑ k ∈ Finset.range (2 * n + 1), GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k s := by
  conv_lhs => rw [← (basisS F n).sum_repr s]
  conv_rhs => rw [← (basisS F n).sum_repr s]
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hK := s8_basisS_mem F n K
  have hcard : K.card < 2 * n + 1 := by
    have := K.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  rw [Finset.sum_eq_single K.card]
  · rw [s8_proj_of_mem hK, ite_eq_left rfl]
  · intro k _ hk
    rw [s8_proj_of_mem hK, ite_eq_right (Ne.symm hk), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hcard) h

omit [CharZero F] in
/-- The number operator on `S`: `Σᵢ eᵢ ∧ (fᵢ ⌋ s) = Σ_k k s_k`. -/
theorem s8_numberOp_S (s : S F n) :
    ∑ i, ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s =
      ∑ k ∈ Finset.range (2 * n + 1),
        (k : F) • GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k s := by
  conv_lhs => rw [s8_eq_sum_proj s]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := s8_numberOp (Pi.basisFun F (Fin (2 * n))) (s8_proj_mem s k)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
  simp only [Pi.basisFun_apply]
  rfl

/-- A spinor killed by every `D_y`, `y ∈ H¹(X̂)` (i.e. `H¹(X̂) × 0 ⊆ ker m_s`) is a scalar. -/
theorem s8_eq_algebraMap_of_contract {s : S F n} (h : ∀ y, D F n y s = 0) :
    s = algebraMap F (S F n) (ExteriorAlgebra.algebraMapInv s) := by
  have hN := s8_numberOp_S s
  simp only [h, mul_zero, Finset.sum_const_zero] at hN
  have hk : ∀ k, 0 < k → GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k s = 0 := by
    intro k hk
    by_cases hk2 : k < 2 * n + 1
    · have := congrArg (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k) hN
      rw [map_zero, map_sum, Finset.sum_eq_single k] at this
      · rw [map_smul, s8_proj_of_mem (s8_proj_mem s k), ite_eq_left rfl] at this
        exact (smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast hk.ne')
      · intro j _ hj
        rw [map_smul, s8_proj_of_mem (s8_proj_mem s j), ite_eq_right hj, smul_zero]
      · intro h'
        exact absurd (Finset.mem_range.mpr hk2) h'
    · exact s8_mem_bot_of_lt F n (by omega) (s8_proj_mem s k)
  have hs : s = GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) 0 s := by
    conv_lhs => rw [s8_eq_sum_proj s]
    rw [Finset.sum_eq_single 0]
    · intro k _ hk0
      exact hk k (Nat.pos_of_ne_zero hk0)
    · simp
  have h0 := s8_eq_algebraMap_of_mem_zero (s8_proj_mem s 0)
  rw [← hs] at h0
  exact h0

omit [CharZero F] in
/-- A class of top degree is a multiple of `[pt]`. -/
theorem s8_eq_smul_pt_of_mem {x : S F n} (hx : x ∈ ⋀[F]^(2 * n) (H1 F n)) :
    x = integral F n x • pt F n := by
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [Finset.sum_eq_single Finset.univ]
  · rfl
  · intro K _ hK
    rw [s8_repr_eq_zero_of_mem F n hx K (fun h => hK (Finset.eq_univ_of_card _ (by
      rw [h, Fintype.card_fin]))), zero_smul]
  · simp

/-- A spinor killed by every `L_w`, `w ∈ H¹(X)` (i.e. `0 × H¹(X) ⊆ ker m_s`) is a multiple of
`[pt]`. -/
theorem s8_eq_smul_pt_of_mul {s : S F n} (h : ∀ w, ExteriorAlgebra.ι F w * s = 0) :
    s = integral F n s • pt F n := by
  -- `Σᵢ fᵢ ⌋ (eᵢ ∧ s) = 2n s - Σᵢ eᵢ ∧ (fᵢ ⌋ s)`
  have hdual : ∑ i, D F n (f F n i) (ExteriorAlgebra.ι F (e F n i) * s) =
      ((2 * n : ℕ) : F) • s - ∑ i, ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s := by
    have hcl : ∀ i, D F n (f F n i) (ExteriorAlgebra.ι F (e F n i) * s) =
        s - ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s := by
      intro i
      change contractLeft (Q := 0) (f F n i) (CliffordAlgebra.ι 0 (e F n i) * s) = _
      rw [contractLeft_ι_mul]
      simp only [f, e, LinearMap.proj_apply, Pi.single_eq_same, one_smul]
      rfl
    simp only [hcl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul F]
  simp only [h, map_zero, Finset.sum_const_zero, s8_numberOp_S] at hdual
  have hk : ∀ k, k ≠ 2 * n → GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k s = 0 := by
    intro k hk
    by_cases hk2 : k < 2 * n + 1
    · have := congrArg (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k) hdual
      rw [map_zero, map_sub, map_smul, map_sum, Finset.sum_eq_single k] at this
      · rw [map_smul, s8_proj_of_mem (s8_proj_mem s k), ite_eq_left rfl, ← sub_smul] at this
        refine (smul_eq_zero.mp this.symm).resolve_left ?_
        exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hk))
      · intro j _ hj
        rw [map_smul, s8_proj_of_mem (s8_proj_mem s j), ite_eq_right hj, smul_zero]
      · intro h'
        exact absurd (Finset.mem_range.mpr hk2) h'
    · exact s8_mem_bot_of_lt F n (by omega) (s8_proj_mem s k)
  have hs : s = GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) (2 * n) s := by
    conv_lhs => rw [s8_eq_sum_proj s]
    rw [Finset.sum_eq_single (2 * n)]
    · intro k _ hk2n
      exact hk k hk2n
    · simp
  have hmem := s8_proj_mem s (2 * n)
  rw [← hs] at hmem
  exact s8_eq_smul_pt_of_mem hmem

omit [CharZero F] in
/-- A class of degree `2` commutes with `H¹(X)`. -/
theorem s8_commute_ι_of_mem_two {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (v : H1 F n) :
    ExteriorAlgebra.ι F v * Θ = Θ * ExteriorAlgebra.ι F v := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hΘ
  induction hΘ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one]
    have h1 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := F) v (w 0))
    have h2 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := F) v (w 1))
    rw [← mul_assoc, h1, neg_mul, mul_assoc, h2, mul_neg, neg_neg, ← mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]

omit [CharZero F] in
/-- Leibniz rule for a class of degree `2`: `y ⌋ (Θ x) = (y ⌋ Θ) x + Θ (y ⌋ x)`. -/
theorem s8_D_mul_of_mem_two {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (y : Module.Dual F (H1 F n)) (x : S F n) :
    D F n y (Θ * x) = D F n y Θ * x + Θ * D F n y x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hΘ
  induction hΘ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    change contractLeft (Q := 0) y (CliffordAlgebra.ι 0 (w 0) * CliffordAlgebra.ι 0 (w 1) * x) =
      contractLeft (Q := 0) y (CliffordAlgebra.ι 0 (w 0) * CliffordAlgebra.ι 0 (w 1)) * x +
        CliffordAlgebra.ι 0 (w 0) * CliffordAlgebra.ι 0 (w 1) * contractLeft (Q := 0) y x
    rw [mul_assoc, contractLeft_ι_mul, contractLeft_ι_mul, contractLeft_ι_mul, contractLeft_ι,
      ← Algebra.commutes, ← Algebra.smul_def]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel
  | zero => simp
  | add a b _ _ ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | smul c a _ ha => simp only [smul_mul_assoc, map_smul, ha, smul_add]

/-- `y ⌋ Θ^{m+1} = (m+1) θ(y) ∧ Θ^m` for `Θ ∈ H²`. -/
theorem s8_D_pow_succ {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (y : Module.Dual F (H1 F n))
    (m : ℕ) :
    D F n y (Θ ^ (m + 1)) =
      ((m + 1 : ℕ) : F) • (ExteriorAlgebra.ι F (contractOne F n Θ y) * Θ ^ m) := by
  induction m with
  | zero =>
    rw [zero_add, pow_one, pow_zero, mul_one, Nat.cast_one, one_smul, ι_contractOne F n Θ hΘ y]
  | succ m ih =>
    rw [pow_succ', s8_D_mul_of_mem_two hΘ, ih, ← ι_contractOne F n Θ hΘ y, mul_smul_comm,
      ← mul_assoc, ← s8_commute_ι_of_mem_two hΘ, mul_assoc, ← pow_succ']
    push_cast
    module

/-- If `θ` is invertible, `Θⁿ ≠ 0` (Pfaffian non-zero): if `Θ^{m+1} = 0` with `m < n` then
`θ(y) ∧ Θ^m = 0` for all `y`, so `Θ^m` is a multiple of `[pt]` of degree `2m < 2n`, i.e. zero. -/
theorem s8_pow_ne_zero_of_bijective {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) : Θ ^ n ≠ 0 := by
  have step : ∀ m, m < n → Θ ^ (m + 1) = 0 → Θ ^ m = 0 := by
    intro m hm h0
    have hw : ∀ w, ExteriorAlgebra.ι F w * Θ ^ m = 0 := by
      intro w
      obtain ⟨y, rfl⟩ := hθ.2 w
      have := s8_D_pow_succ hΘ y m
      rw [h0, map_zero] at this
      exact (smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast Nat.succ_ne_zero m)
    rw [s8_eq_smul_pt_of_mul hw]
    have hI : integral F n (Θ ^ m) = 0 :=
      s8_integral_eq_zero_of_mem F n (by omega : 2 * m ≠ 2 * n) (s8_pow_mem F n hΘ m)
    rw [hI, zero_smul]
  intro hn
  have : ∀ k, k ≤ n → Θ ^ (n - k) = 0 := by
    intro k hk
    induction k with
    | zero => simpa using hn
    | succ k ih =>
      have := step (n - (k + 1)) (by omega) (by rw [show n - (k + 1) + 1 = n - k by omega]; exact ih (by omega))
      exact this
  have h1 := this n le_rfl
  rw [Nat.sub_self, pow_zero] at h1
  exact one_ne_zero h1

end S8Spinors

/-! ## Helpers (prefix `s8_`): the elements `exp(j u)` of `Spin(V_F)` and the annihilators -/

section S8ExpSpin

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s8_isNilpotent_of_mem_two {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (c : F) :
    IsNilpotent (c • Θ) :=
  ⟨n + 1, s8_pow_eq_zero F n (Submodule.smul_mem _ c hΘ) (by omega)⟩

/-- `exp(j u) ∈ Spin(V_F)` for `u ∈ ⋀² H¹(X, F)` ([Chevalley, III.1.7]). -/
noncomputable def s8_expSpin (u : S F n) (hu : u ∈ ⋀[F]^2 (H1 F n)) : Spin F n :=
  ⟨IsNilpotent.exp (iotaX F n u), chevalley_III_1_7_mem F n u hu⟩

theorem s8_m_expSpin (u : S F n) (hu : u ∈ ⋀[F]^2 (H1 F n)) (s : S F n) :
    m F n (s8_expSpin u hu : C F n) s = IsNilpotent.exp u * s := by
  change m F n (IsNilpotent.exp (iotaX F n u)) s = _
  rw [m_exp_jH F n u hu, LinearMap.mulLeft_apply]

theorem s8_rho_expSpin (u : S F n) (hu : u ∈ ⋀[F]^2 (H1 F n)) (v : V F n) :
    rho F n (s8_expSpin u hu) v = (v.1, v.2 - contractOne F n u v.1) :=
  chevalley_III_1_7_rho F n u hu v

omit [CharZero F] in
theorem s8_mem_ann_iff (s : S F n) (v : V F n) :
    v ∈ ann F n s ↔ ExteriorAlgebra.ι F v.2 * s + D F n v.1 s = 0 := by
  simp only [ann, LinearMap.mem_ker, mOf,
    AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply, m, CliffordAlgebra.lift_ι_apply,
    cliffordOp, L, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.snd_apply,
    LinearMap.fst_apply, LinearMap.mul_apply']

omit [CharZero F] in
theorem s8_inl_mem_ann_one (y : Module.Dual F (H1 F n)) : ((y, 0) : V F n) ∈ ann F n 1 := by
  rw [s8_mem_ann_iff]
  simp [D]

omit [CharZero F] in
theorem s8_m_inv_m (g : Spin F n) (s : S F n) :
    m F n ((g⁻¹ : Spin F n) : C F n) (m F n (g : C F n) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    map_one, Module.End.one_apply]

omit [CharZero F] in
theorem s8_m_injective (g : Spin F n) : Function.Injective (m F n (g : C F n)) := by
  intro x y hxy
  rw [← s8_m_inv_m g x, ← s8_m_inv_m g y, hxy]

/-- `ρ_g(v) ∈ ker m_{g s}` for `v ∈ ker m_s` (`WeilClasses.ann_m_spin`). -/
theorem s8_rho_mem_ann (g : Spin F n) {s : S F n} {v : V F n} (hv : v ∈ ann F n s) :
    rho F n g v ∈ ann F n (m F n (g : C F n) s) := by
  rw [ann_m_spin]
  exact ⟨v, hv, rfl⟩

omit [CharZero F] in
theorem s8_bcS_mem {F' : Type*} [Field F'] [Algebra F F'] {k : ℕ} {x : S F n}
    (hx : x ∈ ⋀[F]^k (H1 F n)) : bcS F F' n x ∈ ⋀[F']^k (H1 F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [s8_bcS_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' k ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, ← algebraMap_smul F']
    exact Submodule.smul_mem _ _ hx

/-- `(y, -c θ(y)) ∈ ker m_{exp(cΘ)}`: `ker m_{exp(cΘ)} = exp(cΘ)(H¹(X̂) × 0)` ((2.4.4), (2.4.6)). -/
theorem s8_mem_ann_exp {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (c : F)
    (y : Module.Dual F (H1 F n)) :
    ((y, -(c • contractOne F n Θ y)) : V F n) ∈ ann F n (IsNilpotent.exp (c • Θ)) := by
  have hu : c • Θ ∈ ⋀[F]^2 (H1 F n) := Submodule.smul_mem _ c hΘ
  have h := s8_rho_mem_ann (s8_expSpin (c • Θ) hu) (s8_inl_mem_ann_one (n := n) y)
  rw [s8_m_expSpin, mul_one, s8_rho_expSpin, s8_contractOne_smul] at h
  simpa [sub_eq_add_neg] using h

/-- A spinor `s` with `(y, -c θ(y)) ∈ ker m_s` for all `y` is a multiple of `exp(cΘ)`
([Chevalley, III.1.4] in this case: `exp(-cΘ) s` is killed by `H¹(X̂)`, hence a scalar). -/
theorem s8_mem_span_exp_of_ann {Θ : S F n} (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (c : F) (s : S F n)
    (hs : ∀ y, ((y, -(c • contractOne F n Θ y)) : V F n) ∈ ann F n s) :
    s ∈ Submodule.span F {IsNilpotent.exp (c • Θ)} := by
  have hu : (-c) • Θ ∈ ⋀[F]^2 (H1 F n) := Submodule.smul_mem _ (-c) hΘ
  set t := IsNilpotent.exp ((-c) • Θ) * s
  have ht : ∀ y, D F n y t = 0 := by
    intro y
    have h := s8_rho_mem_ann (s8_expSpin ((-c) • Θ) hu) (hs y)
    rw [s8_m_expSpin, s8_rho_expSpin, s8_contractOne_smul] at h
    have h' : ((y, (0 : H1 F n)) : V F n) ∈ ann F n t := by
      have hv : ((y, -(c • contractOne F n Θ y) - ((-c) • contractOne F n Θ) y) : V F n) =
          (y, 0) := by
        rw [LinearMap.smul_apply, neg_smul, sub_neg_eq_add, neg_add_cancel]
      rw [← hv]
      exact h
    rw [s8_mem_ann_iff] at h'
    simpa using h'
  have hcomm : Commute (c • Θ) ((-c) • Θ) := (Commute.refl Θ).smul_left c |>.smul_right (-c)
  have hnil : IsNilpotent (c • Θ) := s8_isNilpotent_of_mem_two hΘ c
  have h1 : IsNilpotent.exp (c • Θ) * IsNilpotent.exp ((-c) • Θ) = 1 := by
    rw [← IsNilpotent.exp_add_of_commute hcomm hnil (s8_isNilpotent_of_mem_two hΘ (-c)),
      ← add_smul, add_neg_cancel, zero_smul, IsNilpotent.exp_zero]
  have hs' : s = IsNilpotent.exp (c • Θ) * t := by rw [← mul_assoc, h1, one_mul]
  rw [hs', s8_eq_algebraMap_of_contract ht, ← Algebra.commutes, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end S8ExpSpin

/-! ## Lemma 8.1.1 -/

section Lemma811

variable {n : ℕ} (d : ℚ)

/-- The Möbius form of the action of `SO⁺_Hdg(V_F)` on the pure spinors `exp(kΘ)` (the proof of
`m_exp_mem_span_hdgMatrix`; used for the action of `[[0, -f⁻¹], [f, 0]]` in `iota_tau_extends`, not
in the proof of Lemma 8.1.1): `ρ(g) = A` maps `ker m_{exp(kΘ)} = {(y, -kθ(y))}` onto
`{(y, -k'θ(y))} = ker m_{exp(k'Θ)}`, and the pure spinor is determined by its annihilator
(`s8_mem_span_exp_of_ann`). -/
theorem s8_m_exp_mem_span {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (hθ : Function.Bijective (contractOne F n Θ))
    (a : Matrix (Fin 2) (Fin 2) F) (g : Spin F n)
    (hg : (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a)
    (k : F) (hk : a 1 0 * k + a 1 1 ≠ 0) :
    m F n (g : C F n) (IsNilpotent.exp (k • Θ)) ∈
      Submodule.span F {IsNilpotent.exp (((a 0 0 * k + a 0 1) / (a 1 0 * k + a 1 1)) • Θ)} := by
  refine s8_mem_span_exp_of_ann hΘ _ _ fun y' => ?_
  set c := a 1 0 * k + a 1 1
  have h1 := s8_rho_mem_ann g (s8_mem_ann_exp hΘ k (c⁻¹ • y'))
  rw [← LinearEquiv.coe_coe, hg, s8_hdgMatrix_apply] at h1
  convert h1 using 2
  · simp only [map_neg, map_smul, s8_fOfTheta_theta, smul_neg, neg_neg, smul_smul]
    rw [← add_smul, show a 1 0 * (k * c⁻¹) + a 1 1 * c⁻¹ = c * c⁻¹ by ring,
      mul_inv_cancel₀ hk, one_smul]
  · simp only [map_smul, smul_smul, sub_eq_add_neg, ← neg_smul, ← add_smul]
    congr 1
    field_simp
    ring

/-- (Proof of Lemma 8.1.1, case `a₂₂ = 0`) `A(H¹(X̂, K)) = H¹(X, K)`, so `A` maps the pure spinor
`1` of `H¹(X̂, K)` to the pure spinor line `K[pt]` of `H¹(X, K)`: `m_g(1) ∈ K [pt]`, `m_g(1) ≠ 0`. -/
theorem s8_m_one_eq_smul_pt {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hθ : Function.Bijective (contractOne F n Θ)) (a : Matrix (Fin 2) (Fin 2) F) (ha : a.det = 1)
    (h11 : a 1 1 = 0) (g : Spin F n)
    (hg : (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a) :
    m F n (g : C F n) 1 = integral F n (m F n (g : C F n) 1) • pt F n ∧
      integral F n (m F n (g : C F n) 1) ≠ 0 := by
  have h01 : a 0 1 ≠ 0 := by
    intro h; rw [Matrix.det_fin_two, h11, h] at ha; simp at ha
  have hpt : m F n (g : C F n) 1 = integral F n (m F n (g : C F n) 1) • pt F n := by
    refine s8_eq_smul_pt_of_mul fun w => ?_
    obtain ⟨y, hy⟩ := hθ.2 ((-(a 0 1))⁻¹ • w)
    have h := s8_rho_mem_ann g (s8_inl_mem_ann_one (n := n) y)
    rw [← LinearEquiv.coe_coe, hg, s8_hdgMatrix_apply] at h
    simp only [h11, zero_smul, add_zero, map_zero, smul_zero, zero_sub, hy, smul_smul] at h
    have hsc : a 0 1 * (-(a 0 1))⁻¹ = -1 := by
      rw [inv_neg, mul_neg, mul_inv_cancel₀ h01]
    rw [hsc, neg_one_smul, neg_neg] at h
    rw [s8_mem_ann_iff] at h
    simpa [D] using h
  refine ⟨hpt, fun h0 => ?_⟩
  have hm : m F n (g : C F n) 1 = 0 := by rw [hpt, h0, zero_smul]
  exact one_ne_zero (s8_m_injective g (by rw [hm, map_zero]))

/-- (Proof of Lemma 8.1.1, TeX line 3672) "The subgroup of `SO⁺_Hdg(V_K)` leaving `H¹(X̂, K)`
invariant is the lower triangular subgroup with `a₁₂ = 0`": a lower triangular matrix (8.1.2)
(`a₁₂ = 0`) of determinant `1` maps `H¹(X̂) × 0 = ker m_1` onto itself, so its lifts
`g ∈ Spin(V_F)` fix the pure spinor line of `1`: `m_g(1) ∈ F·1` (a pure spinor line is determined by
its annihilator, `s8_mem_span_exp_of_ann` with `c = 0`). -/
theorem s8_m_one_mem_span_one {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (hθ : Function.Bijective (contractOne F n Θ))
    (b : Matrix (Fin 2) (Fin 2) F) (hb : b.det = 1) (h01 : b 0 1 = 0) (g : Spin F n)
    (hg : (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ b) :
    m F n (g : C F n) 1 ∈ Submodule.span F {1} := by
  have h11 : b 1 1 ≠ 0 := by
    intro h; rw [Matrix.det_fin_two, h, h01] at hb; simp at hb
  have hmem : m F n (g : C F n) 1 ∈ Submodule.span F {IsNilpotent.exp ((0 : F) • Θ)} := by
    refine s8_mem_span_exp_of_ann hΘ 0 _ fun y => ?_
    -- `ρ_g(b₂₂⁻¹ y, 0) = (y, 0)`: `ρ_g` maps `ker m_1 = H¹(X̂) × 0` into `ker m_{g 1}`
    have h := s8_rho_mem_ann g (s8_inl_mem_ann_one (n := n) ((b 1 1)⁻¹ • y))
    rw [← LinearEquiv.coe_coe, hg, s8_hdgMatrix_apply] at h
    convert h using 2
    · simp [smul_smul, h11]
    · simp [h01]
  rwa [zero_smul, IsNilpotent.exp_zero] at hmem

/-- (Proof of Lemma 8.1.1) The coset representative `[[1, k], [0, 1]]` of `k ∈ K ⊆ ℙ¹_K` lifts to
`exp(kΘ) ∈ Spin(V_F)` ([Chevalley, III.1.7], `s8_expSpin`), which maps `1` to `exp(kΘ)`. -/
theorem s8_rho_expSpin_eq_hdgMatrix {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (hθ : Function.Bijective (contractOne F n Θ)) (k : F) :
    (rho F n (s8_expSpin (k • Θ) (Submodule.smul_mem _ k hΘ)) : V F n →ₗ[F] V F n) =
      hdgMatrix (contractOne F n Θ) hθ !![1, k; 0, 1] := by
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, s8_rho_expSpin, s8_hdgMatrix_apply, s8_contractOne_smul]
  simp

/-- (Proof of Lemma 8.1.1, the cosets with `a₂₂ ≠ 0`) If `a₂₂ ≠ 0`, then `a = [[1, k], [0, 1]] b`
with `k = a₁₂/a₂₂` and `b = [[1, -k], [0, 1]] a` lower triangular: `a` lies in the coset of
`k ∈ ℙ¹_F`. The lift `exp(-kΘ) g` of `b` fixes the line of `1` (the stabilizer step,
`s8_m_one_mem_span_one`), so `m_g(1)` spans the image `exp(kΘ)` of `1` under the lift `exp(kΘ)` of
`[[1, k], [0, 1]]`. -/
theorem s8_m_one_eq_smul_exp {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (hθ : Function.Bijective (contractOne F n Θ))
    (a : Matrix (Fin 2) (Fin 2) F) (ha : a.det = 1) (h11 : a 1 1 ≠ 0) (g : Spin F n)
    (hg : (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a) :
    ∃ c : F, c ≠ 0 ∧ m F n (g : C F n) 1 = c • IsNilpotent.exp ((a 0 1 / a 1 1) • Θ) := by
  obtain ⟨k, hk⟩ : ∃ k : F, k = a 0 1 / a 1 1 := ⟨_, rfl⟩
  rw [← hk]
  have hb01 : (!![1, -k; 0, 1] * a) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hk, div_mul_cancel₀ _ h11]
  have hbdet : (!![1, -k; 0, 1] * a).det = 1 := by
    rw [Matrix.det_mul, ha]; simp [Matrix.det_fin_two]
  -- the lift `g₁ = exp(-kΘ)` of `[[1, -k], [0, 1]]`, with `m_{g₁}(exp(kΘ)) = 1`
  obtain ⟨g₁, hg₁ρ, hg₁m⟩ : ∃ g₁ : Spin F n,
      (rho F n g₁ : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ !![1, -k; 0, 1] ∧
      m F n (g₁ : C F n) (IsNilpotent.exp (k • Θ)) = 1 := by
    refine ⟨s8_expSpin _ (Submodule.smul_mem _ (-k) hΘ), s8_rho_expSpin_eq_hdgMatrix hΘ hθ (-k), ?_⟩
    have hcomm : Commute ((-k) • Θ) (k • Θ) := ((Commute.refl _).smul_left (-k)).smul_right k
    rw [s8_m_expSpin, ← IsNilpotent.exp_add_of_commute hcomm (s8_isNilpotent_of_mem_two hΘ (-k))
      (s8_isNilpotent_of_mem_two hΘ k), ← add_smul, neg_add_cancel, zero_smul, IsNilpotent.exp_zero]
  -- the stabilizer step: `g₁ g` lifts `b`, which fixes the line of `1`
  have hb : (rho F n (g₁ * g) : V F n →ₗ[F] V F n) =
      hdgMatrix (contractOne F n Θ) hθ (!![1, -k; 0, 1] * a) := by
    rw [s8_rho_mul, hg₁ρ, hg, s8_hdgMatrix_comp]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (s8_m_one_mem_span_one hΘ hθ _ hbdet hb01 (g₁ * g) hb)
  -- so `m_g(1) = m_{g₁⁻¹}(c 1) = c exp(kΘ)`
  have hinv : m F n ((g₁⁻¹ : Spin F n) : C F n) 1 = IsNilpotent.exp (k • Θ) := by
    rw [← hg₁m, s8_m_inv_m]
  have hm : m F n (g : C F n) 1 = c • IsNilpotent.exp (k • Θ) := by
    have hgg : g = g₁⁻¹ * (g₁ * g) := by rw [inv_mul_cancel_left]
    rw [hgg, Submonoid.coe_mul, map_mul, Module.End.mul_apply, ← hc, map_smul, hinv]
  refine ⟨c, ?_, hm⟩
  rintro rfl
  rw [zero_smul] at hm
  exact one_ne_zero (s8_m_injective g (by rw [hm, map_zero]))

/-- **Lemma 8.1.1** (`lemma-orbit-of-pure-spinors`). The `SO⁺_Hdg(V_K)`-orbit of the pure spinor
`span_K{1} ∈ ℙ(S⁺_K)` is `{span_K{Θⁿ}} ∪ {span_K{exp(kΘ)} : k ∈ K}`.

Model: `SO⁺_Hdg(V_K)` is the group of matrices (8.1.2) with coefficients in `K` and determinant `1`
(`SOplusHdg`, for the `K`-linear `θ`), acting on `ℙ(S⁺_K)` through `Spin(V_K)` (`ρ` is onto
`SO⁺(V_K)` with kernel `±1`, which acts trivially on `ℙ(S_K)`): the orbit is the set of lines
`K m_g(1)`, `g ∈ Spin(V_K)` with `ρ(g) ∈ SO⁺_Hdg(V_K)`. Reading: the lemma uses only this definition
of `SO⁺_Hdg(V_K)`; it holds for every `Θ ∈ ⋀² H¹(X, ℚ)` with `θ` invertible (the section's hypotheses
on `(X, Θ)` are not needed).

Proof as in the paper (TeX lines 3669–3676). If `a₂₂ = 0`, then `A(H¹(X̂, K)) = H¹(X, K)`, so `A`
maps the pure spinor `span_K{1}` of `H¹(X̂, K)` to the pure spinor `span_K{Θⁿ}` of `H¹(X, K)`
(`s8_m_one_eq_smul_pt`). The subgroup of `SO⁺_Hdg(V_K)` leaving `H¹(X̂, K)` invariant is the lower
triangular subgroup `B` (`a₁₂ = 0`); the proof uses that `B` leaves `H¹(X̂, K)` invariant, hence
fixes `span_K{1}` (`s8_m_one_mem_span_one`), so that the point `A span_K{1}` of the orbit depends
only on the coset `aB ∈ SL₂(K)/B = ℙ¹_K` (the reverse inclusion, which makes the orbit isomorphic to
`ℙ¹_K`, is not needed for the description of the orbit).

Departure from the paper (reason 2: no rational normal curves or Zariski closures in the library):
the paper identifies the orbit `ℙ¹_K` with the rational normal curve of degree `n` in
`ℙ(span_K{Θʲ : 0 ≤ j ≤ n})`, the Zariski closure of `{span_K{exp(kΘ)} : k ∈ K}`, to read off its
points. Here the points of `ℙ¹_K = SL₂(K)/B` are listed by coset representatives: `a ∈ [[1, k], [0, 1]] B`
with `k = a₁₂/a₂₂` if `a₂₂ ≠ 0`, and `a ∈ [[0, -1], [1, 0]] B` if `a₂₂ = 0`; the first maps
`span_K{1}` to `span_K{exp(kΘ)}` (its lift `exp(kΘ) ∈ Spin(V_K)`, [Chevalley, III.1.7],
`s8_rho_expSpin_eq_hdgMatrix`), the second to `span_K{Θⁿ}` (the case `a₂₂ = 0`). The lifts of the
matrices to `Spin(V_K)` by Eichler transvections (`exists_rho_eq_hdgMatrix`) are taken for granted in
the paper. -/
theorem lemma8_1_1 (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) :
    {L : Submodule (Kd d) (S (Kd d) n) | ∃ g : Spin (Kd d) n,
        (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∈ SOplusHdg (thetaExt n (Kd d) Θ) hθ ∧
        L = Submodule.span (Kd d) {m (Kd d) n (g : C (Kd d) n) 1}} =
      {Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n}} ∪
        Set.range fun k : Kd d => Submodule.span (Kd d) {IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)} := by
  have hΘK : bcS ℚ (Kd d) n Θ ∈ ⋀[Kd d]^2 (H1 (Kd d) n) := s8_bcS_mem hΘ
  -- `span{Θⁿ} = span{[pt]}` (`Θⁿ ≠ 0` as `θ` is invertible)
  have hpow : bcS ℚ (Kd d) n Θ ^ n ≠ 0 := s8_pow_ne_zero_of_bijective hΘK hθ
  have hΘn := s8_eq_smul_pt_of_mem (s8_pow_mem (Kd d) n hΘK n)
  have hI : integral (Kd d) n (bcS ℚ (Kd d) n Θ ^ n) ≠ 0 := fun h => hpow (by rw [hΘn, h, zero_smul])
  have hspan_pt : Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n} =
      Submodule.span (Kd d) {pt (Kd d) n} := by
    rw [hΘn, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hI)]
  -- the case `a₂₂ = 0`: the line of `Θⁿ`
  have hcase0 : ∀ (a : Matrix (Fin 2) (Fin 2) (Kd d)) (g : Spin (Kd d) n), a.det = 1 → a 1 1 = 0 →
      (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) = hdgMatrix (thetaExt n (Kd d) Θ) hθ a →
      Submodule.span (Kd d) {m (Kd d) n (g : C (Kd d) n) 1} =
        Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n} := by
    intro a g ha h11 hg
    obtain ⟨hpt, hI'⟩ := s8_m_one_eq_smul_pt hθ a ha h11 g hg
    rw [hpt, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hI'), hspan_pt]
  ext L
  constructor
  · rintro ⟨g, ⟨a, ha, hga⟩, rfl⟩
    by_cases h11 : a 1 1 = 0
    · exact Or.inl (hcase0 a g ha h11 hga)
    · -- `a₂₂ ≠ 0`: `a = [[1, k], [0, 1]] b`, `k = a₁₂/a₂₂`, `b` lower triangular (the coset of
      -- `k ∈ ℙ¹_K`), and `b` fixes the line of `1`: the line of `exp(kΘ)`
      obtain ⟨c, hc0, hm⟩ := s8_m_one_eq_smul_exp hΘK hθ a ha h11 g hga
      refine Or.inr ⟨a 0 1 / a 1 1, ?_⟩
      simp only
      rw [hm, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc0)]
  · rintro (h | ⟨k, rfl⟩)
    · -- the coset representative `[[0, -1], [1, 0]]` maps the line of `1` to that of `Θⁿ`
      have hdet : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (Kd d)).det = 1 := by
        simp [Matrix.det_fin_two]
      obtain ⟨g, hg⟩ := exists_rho_eq_hdgMatrix (bcS ℚ (Kd d) n Θ) hΘK hθ _ hdet
      refine ⟨g, ⟨_, hdet, hg⟩, ?_⟩
      rw [Set.mem_singleton_iff.mp h]
      exact (hcase0 _ g hdet (by simp) hg).symm
    · -- the coset representative `[[1, k], [0, 1]]`: its lift `exp(kΘ)` maps `1` to `exp(kΘ)`
      refine ⟨s8_expSpin _ (Submodule.smul_mem _ k hΘK),
        ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two], s8_rho_expSpin_eq_hdgMatrix hΘK hθ k⟩, ?_⟩
      rw [s8_m_expSpin, mul_one]

/-- The action of `SO⁺_Hdg(V_K)` on the pure spinors `exp(kΘ)` of Lemma 8.1.1 is the Möbius action on
`ℙ¹_K` (not stated in the paper; the proof of Lemma 8.1.1, `lemma8_1_1`, does not use it, and it
computes the action of `[[0, -f⁻¹], [f, 0]]` in `iota_tau_extends`): the matrix
`A = [[a₁₁, a₁₂ f⁻¹], [a₂₁ f, a₂₂]]` maps the maximal isotropic subspace
`ker m_{exp(kΘ)} = {(y, -kθ(y))}` to `ker m_{exp(k'Θ)}` with `k' = (a₁₁ k + a₁₂)/(a₂₁ k + a₂₂)`:
for `g ∈ Spin(V_K)` with `ρ(g) = A`, `m_g(exp(kΘ)) ∈ K exp(k'Θ)`. (If `a₂₁ k + a₂₂ = 0`, `A` maps
`ker m_{exp(kΘ)}` onto `H¹(X, K)`, the annihilator of the line of `Θⁿ`; that case is not part of
this statement.) (Checked numerically for `n ≤ 3`.) -/
theorem m_exp_mem_span_hdgMatrix (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) (a : Matrix (Fin 2) (Fin 2) (Kd d))
    (g : Spin (Kd d) n)
    (hg : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) = hdgMatrix (thetaExt n (Kd d) Θ) hθ a)
    (k : Kd d) (hk : a 1 0 * k + a 1 1 ≠ 0) :
    m (Kd d) n (g : C (Kd d) n) (IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)) ∈
      Submodule.span (Kd d)
        {IsNilpotent.exp (((a 0 0 * k + a 0 1) / (a 1 0 * k + a 1 1)) • bcS ℚ (Kd d) n Θ)} :=
  s8_m_exp_mem_span (s8_bcS_mem hΘ) hθ a g hg k hk

end Lemma811

/-! ## The involution `ι` -/

section Iota

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The involution `ι` of §8.1, interchanging the coefficients of `Θ^j/j!` and `Θ^{n-j}/(n-j)!`,
applied to `Σ_{j=0}^{n} c_j Θ^j/j!`: the class `Σ_j c_j Θ^{n-j}/(n-j)!`. -/
noncomputable def iotaTheta (Θ : S F n) (c : ℕ → F) : S F n :=
  ∑ j ∈ Finset.range (n + 1), (c j / ((n - j).factorial : F)) • Θ ^ (n - j)

/-- (§8.1, TeX lines 3679–3680) `ι` acts on the pure spinors `exp(kΘ) = Σ_j k^j Θ^j/j!` by
`ι(exp(kΘ)) = kⁿ exp(k⁻¹Θ)` (`k ≠ 0`). (Checked symbolically for `n ≤ 6`.) -/
theorem iotaTheta_exp (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (k : F) (hk : k ≠ 0) :
    iotaTheta Θ (fun j => k ^ j) = k ^ n • IsNilpotent.exp (k⁻¹ • Θ) := by
  -- `exp(k⁻¹Θ) = Σ_{i ≤ n} k⁻ⁱ Θⁱ/i!` (`Θ^{n+1} = 0`); reflect `j ↦ n - j`
  have hnil : (k⁻¹ • Θ) ^ (n + 1) = 0 :=
    s8_pow_eq_zero F n (Submodule.smul_mem _ _ hΘ) (by omega)
  have hq : ∀ (q : ℚ) (x : S F n), q • x = (q : F) • x := fun q x =>
    (Rat.cast_smul_eq_qsmul F q x).symm
  rw [IsNilpotent.exp_eq_sum hnil, iotaTheta, Finset.smul_sum]
  have hL : ∑ j ∈ Finset.range (n + 1), ((fun j : ℕ => k ^ j) j / ((n - j).factorial : F)) •
      Θ ^ (n - j) = ∑ j ∈ Finset.range (n + 1),
        (fun i : ℕ => (k ^ (n - i) / (i.factorial : F)) • Θ ^ i) (n + 1 - 1 - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [Nat.add_sub_cancel]
    rw [Nat.sub_sub_self hjn]
  rw [hL, Finset.sum_range_reflect (fun i : ℕ => (k ^ (n - i) / (i.factorial : F)) • Θ ^ i)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hq, smul_pow, smul_smul, smul_smul, pow_sub₀ k hk hin, inv_pow]
  congr 1
  push_cast
  ring

variable (d : ℚ)

/-- (§8.1, TeX lines 3680–3681) "The action of the element `[[0, -f⁻¹], [f, 0]]` on `ℙ(S_K)` extends
the action of `ι`", corrected: a lift `g ∈ Spin(V_K)` of `[[0, -f⁻¹], [f, 0]]` maps the line of
`exp(kΘ)` to the line of `exp(-k⁻¹Θ) ∝ ι(τ(exp(kΘ)))` (`k ∈ K^×`), the line of `1` to that of `Θⁿ`
and the line of `Θⁿ` to that of `1`; i.e. it extends `ι ∘ τ` (`τ(exp(kΘ)) = exp(-kΘ)`).

**Correction of the paper** (agreed with the project owner; REPORT.md). As printed ("extends `ι`") the
claim is false: the matrix acts on the pure spinors by the Möbius map `k ↦ -1/k`
(`m_exp_mem_span_hdgMatrix`), so it maps the line of `exp(kΘ)` to that of `exp(-k⁻¹Θ)`, not of
`ι(exp(kΘ)) ∝ exp(k⁻¹Θ)` (checked numerically for `n = 1, 2, 3`, `k = 2`). (An element
`[[0, c f⁻¹], [c f, 0]]` of `SO⁺_Hdg(V_K)` inducing `k ↦ 1/k` needs `-c² = 1`, so it exists only for
`K = ℚ(√-1)`.) The paper uses the claim only to lift `ι` to `Aut(Dᵇ(X))` and obtain an object of
non-zero rank, which `ι ∘ τ` also gives. -/
theorem iota_tau_extends (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) (g : Spin (Kd d) n)
    (hg : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) =
      hdgMatrix (thetaExt n (Kd d) Θ) hθ !![0, -1; 1, 0]) :
    (∀ k : Kd d, k ≠ 0 →
      m (Kd d) n (g : C (Kd d) n) (IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)) ∈
        Submodule.span (Kd d) {IsNilpotent.exp ((-k⁻¹) • bcS ℚ (Kd d) n Θ)}) ∧
      m (Kd d) n (g : C (Kd d) n) 1 ∈ Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n} ∧
      m (Kd d) n (g : C (Kd d) n) (bcS ℚ (Kd d) n Θ ^ n) ∈ Submodule.span (Kd d) {1} := by
  have hΘK : bcS ℚ (Kd d) n Θ ∈ ⋀[Kd d]^2 (H1 (Kd d) n) := s8_bcS_mem hΘ
  have hdet : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (Kd d)).det = 1 := by
    simp [Matrix.det_fin_two]
  -- `Θⁿ = I [pt]`, `I ≠ 0` (`θ` invertible)
  have hpow : bcS ℚ (Kd d) n Θ ^ n ≠ 0 := s8_pow_ne_zero_of_bijective hΘK hθ
  have hΘn := s8_eq_smul_pt_of_mem (s8_pow_mem (Kd d) n hΘK n)
  have hI : integral (Kd d) n (bcS ℚ (Kd d) n Θ ^ n) ≠ 0 := fun h => hpow (by rw [hΘn, h, zero_smul])
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · -- the Möbius map `k ↦ -1/k`
    have h := s8_m_exp_mem_span hΘK hθ _ g hg k (by simpa using hk)
    convert h using 4
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, zero_add, one_mul,
      add_zero, neg_div, one_div, neg_smul]
  · -- `A(H¹(X̂)) = H¹(X)`: the line of `1` goes to that of `[pt]`, i.e. of `Θⁿ`
    obtain ⟨hpt, -⟩ := s8_m_one_eq_smul_pt hθ _ hdet (by simp) g hg
    rw [hpt, hΘn, Submodule.mem_span_singleton]
    refine ⟨integral (Kd d) n (m (Kd d) n (g : C (Kd d) n) 1) *
      (integral (Kd d) n (bcS ℚ (Kd d) n Θ ^ n))⁻¹, ?_⟩
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  · -- `A(H¹(X)) = H¹(X̂)`: the line of `[pt]` goes to that of `1`
    have hD : ∀ y, D (Kd d) n y (m (Kd d) n (g : C (Kd d) n) (pt (Kd d) n)) = 0 := by
      intro y
      have h0 : ((0, -(thetaExt n (Kd d) Θ y)) : V (Kd d) n) ∈ ann (Kd d) n (pt (Kd d) n) := by
        rw [s8_mem_ann_iff]
        have : ExteriorAlgebra.ι (Kd d) (thetaExt n (Kd d) Θ y) * pt (Kd d) n = 0 :=
          s8_mem_bot_of_lt (Kd d) n (by omega : 2 * n < 1 + 2 * n)
            (SetLike.mul_mem_graded (by simp) (s8_pt_mem (Kd d) n))
        simp [this, D]
      have h := s8_rho_mem_ann g h0
      rw [← LinearEquiv.coe_coe, hg, s8_hdgMatrix_apply] at h
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, map_neg,
        s8_fOfTheta_theta, neg_neg, one_smul, zero_smul, add_zero, map_zero, smul_zero,
        sub_zero] at h
      rw [s8_mem_ann_iff] at h
      simpa using h
    rw [hΘn, map_smul, s8_eq_algebraMap_of_contract hD, Algebra.algebraMap_eq_smul_one, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Iota

/-! ## The enumeration of the non-rational pure spinors -/

section Enumeration

variable {n : ℕ}

/-- **`α`** (§8.1): `α = exp(ρΘ/q) Σ_{j=0}^{⌊n/2⌋} (-1)^j q^{n-2j} (τ²d)^j Θ^{2j}/(2j)!`, for
`k = (ρ + τ√-d)/q`. -/
noncomputable def alphaPP (Θ : S ℚ n) (d : ℚ) (ρ τ q : ℤ) : S ℚ n :=
  IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
    ∑ j ∈ Finset.range (n / 2 + 1),
      ((-1 : ℚ) ^ j * (q : ℚ) ^ (n - 2 * j) * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ)) •
        Θ ^ (2 * j)

/-- **`β`** (§8.1): `β = exp(ρΘ/q) Σ_{j=0}^{⌊(n-1)/2⌋} (-1)^j q^{n-1-2j} (τ²d)^j Θ^{2j+1}/(2j+1)!`. -/
noncomputable def betaPP (Θ : S ℚ n) (d : ℚ) (ρ τ q : ℤ) : S ℚ n :=
  IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
    ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
      ((-1 : ℚ) ^ j * (q : ℚ) ^ (n - 1 - 2 * j) * ((τ : ℚ) ^ 2 * d) ^ j /
          ((2 * j + 1).factorial : ℚ)) • Θ ^ (2 * j + 1)

/-! ### Helpers (prefix `s8_`): `α`, `β` as polynomials in `Θ` -/

/-- `Σ_{m < 2N} f m = Σ_{j < N} f(2j) + Σ_{j < N} f(2j+1)`. -/
theorem s8_sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m =
      ∑ j ∈ Finset.range N, f (2 * j) + ∑ j ∈ Finset.range N, f (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- Truncating a sum whose terms vanish beyond `M`. -/
theorem s8_sum_range_of_vanish {M' : Type*} [AddCommMonoid M'] (f : ℕ → M') {M N : ℕ}
    (hMN : M ≤ N) (h : ∀ j, M ≤ j → j < N → f j = 0) :
    ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range M, f j := by
  rw [← Finset.sum_range_add_sum_Ico _ hMN, Finset.sum_eq_zero (s := Finset.Ico M N)
    (fun j hj => h j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2), add_zero]

/-- `exp(cΘ) = Σ_{i < N} cⁱ Θⁱ/i!` for `N > n` (`Θ^{n+1} = 0`). -/
theorem s8_exp_smul_eq_sum {F : Type*} [Field F] [CharZero F] {Θ : S F n}
    (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (c : F) {N : ℕ} (hN : n < N) :
    IsNilpotent.exp (c • Θ) = ∑ i ∈ Finset.range N, (c ^ i / (i.factorial : F)) • Θ ^ i := by
  rw [IsNilpotent.exp_eq_sum (s8_pow_eq_zero F n (Submodule.smul_mem _ c hΘ) hN)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, ← Rat.cast_smul_eq_qsmul F, smul_smul]
  congr 1
  push_cast
  ring

/-- `α` with rational exponents: `α = exp(ρΘ/q) Σ_{j ≤ n} (-1)^j qⁿ q^{-2j} (τ²d)^j Θ^{2j}/(2j)!`. -/
theorem s8_alphaPP_eq (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (d : ℚ) (ρ τ q : ℤ)
    (hq : (q : ℚ) ≠ 0) :
    alphaPP Θ d ρ τ q = IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j))⁻¹ *
        ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ)) • Θ ^ (2 * j) := by
  rw [alphaPP]
  congr 1
  rw [s8_sum_range_of_vanish _ (by omega : n / 2 + 1 ≤ n + 1)
    (fun j hj _ => by rw [s8_pow_eq_zero ℚ n hΘ (by omega : n < 2 * j), smul_zero])]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj2 : 2 * j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [pow_sub₀ _ hq hj2]
  congr 1
  ring

/-- `β` with rational exponents: `β = exp(ρΘ/q) Σ_{j ≤ n} (-1)^j qⁿ q^{-2j-1} (τ²d)^j
Θ^{2j+1}/(2j+1)!`. -/
theorem s8_betaPP_eq (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (d : ℚ) (ρ τ q : ℤ)
    (hq : (q : ℚ) ≠ 0) :
    betaPP Θ d ρ τ q = IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j + 1))⁻¹ *
        ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j + 1).factorial : ℚ)) • Θ ^ (2 * j + 1) := by
  rw [betaPP]
  congr 1
  rw [s8_sum_range_of_vanish _ (by omega : (n - 1) / 2 + 1 ≤ n + 1)
    (fun j hj _ => by rw [s8_pow_eq_zero ℚ n hΘ (by omega : n < 2 * j + 1), smul_zero])]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hj2 : 2 * j + 1 ≤ n
  · rw [show n - 1 - 2 * j = n - (2 * j + 1) by omega, pow_sub₀ _ hq hj2]
    congr 1
    ring
  · rw [s8_pow_eq_zero ℚ n hΘ (by omega : n < 2 * j + 1), smul_zero, smul_zero]

/-- Splitting a double sum of multiples of powers of `Θ` into the part of degree `< 5` and a
multiple of `Θ⁵`. -/
theorem s8_double_sum_trunc (Θ : S ℚ n) (a c : ℕ → ℚ) (e : ℕ → ℕ → ℕ) (N M : ℕ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, (a i * c j) • Θ ^ e i j =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
          (if e i j < 5 then (a i * c j) • Θ ^ e i j else 0) +
        Θ ^ 5 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
          (if e i j < 5 then 0 else (a i * c j) • Θ ^ (e i j - 5)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [mul_zero, add_zero]
  · rw [zero_add, mul_smul_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]

/-- A multiple of `Θᵏ` only depends on the coefficient when `k ≤ n` (`Θᵏ = 0` for `k > n`). -/
theorem s8_smul_pow_congr {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (k : ℕ) {a b : ℚ}
    (h : k ≤ n → a = b) : a • Θ ^ k = b • Θ ^ k := by
  by_cases hk : k ≤ n
  · rw [h hk]
  · rw [s8_pow_eq_zero ℚ n hΘ (by omega), smul_zero, smul_zero]

/-- (§8.1, TeX lines 3683–3699) The non-rational pure spinors of Lemma 8.1.1: for
`k = (ρ + τ√-d)/q` (`ρ, τ, q ∈ ℤ`, `q > 0`), `qⁿ exp(kΘ) = α + τ√-d β`; so the line of `exp(kΘ)` is
that of `(α + τ√-d β)/qⁿ`. (Checked symbolically for `n ≤ 6`.) The conditions `gcd(ρ, τ, q) = 1`,
`τ ≠ 0` of the paper make the enumeration bijective onto the non-rational lines (`τ ≠ 0`) and are
not needed for the identity. -/
theorem enumeration8_1 (d : ℚ) (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ((q : Kd d) ^ n) • IsNilpotent.exp ((((ρ : Kd d) + (τ : Kd d) * Kd.sqrtNeg d) / (q : Kd d)) •
        bcS ℚ (Kd d) n Θ) =
      bcS ℚ (Kd d) n (alphaPP Θ d ρ τ q) +
        ((τ : Kd d) * Kd.sqrtNeg d) • bcS ℚ (Kd d) n (betaPP Θ d ρ τ q) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqK : (q : Kd d) ≠ 0 := by exact_mod_cast hq.ne'
  have hΘK : bcS ℚ (Kd d) n Θ ∈ ⋀[Kd d]^2 (H1 (Kd d) n) := s8_bcS_mem hΘ
  set s := Kd.sqrtNeg d
  have hs : s * s = -(d : Kd d) := by
    rw [s8_sqrtNeg_mul_self hd.le, map_neg]; rfl
  set ΘK := bcS ℚ (Kd d) n Θ
  -- `bcS` commutes with `exp` and the sums
  have hbcexp : bcS ℚ (Kd d) n (IsNilpotent.exp (((ρ : ℚ) / q) • Θ)) =
      IsNilpotent.exp ((((ρ : Kd d) / q)) • ΘK) := by
    rw [IsNilpotent.map_exp (s8_isNilpotent_of_mem_two hΘ _) (bcS ℚ (Kd d) n), map_smul,
      ← Rat.cast_smul_eq_qsmul (Kd d)]
    push_cast; rfl
  rw [s8_alphaPP_eq Θ hΘ d ρ τ q hq', s8_betaPP_eq Θ hΘ d ρ τ q hq', map_mul, map_mul, hbcexp,
    map_sum, map_sum]
  simp only [map_smul, map_pow]
  -- `exp(kΘ) = exp(ρΘ/q) exp(τ√-dΘ/q)`
  have hsplit : ((ρ : Kd d) + τ * s) / q = (ρ : Kd d) / q + τ * s / q := by ring
  rw [hsplit, add_smul, IsNilpotent.exp_add_of_commute ((Commute.refl ΘK).smul_left _ |>.smul_right _)
    (s8_isNilpotent_of_mem_two hΘK _) (s8_isNilpotent_of_mem_two hΘK _),
    s8_exp_smul_eq_sum hΘK ((τ : Kd d) * s / q) (by omega : n < 2 * (n + 1)),
    s8_sum_range_two_mul]
  -- even and odd powers of `τ√-d/q`
  have hev : ∀ j : ℕ, ((τ : Kd d) * s / q) ^ (2 * j) =
      ((-1) ^ j * ((τ : Kd d) ^ 2 * d) ^ j) * ((q : Kd d) ^ (2 * j))⁻¹ := by
    intro j
    rw [div_pow, pow_mul, mul_pow, mul_pow, sq s, hs, div_eq_mul_inv]
    ring
  have hod : ∀ j : ℕ, ((τ : Kd d) * s / q) ^ (2 * j + 1) =
      ((τ : Kd d) * s) * ((-1) ^ j * ((τ : Kd d) ^ 2 * d) ^ j) * ((q : Kd d) ^ (2 * j + 1))⁻¹ := by
    intro j
    have h1 : ((τ : Kd d) * s / q) ^ (2 * j + 1) =
        ((τ : Kd d) * s / q) ^ (2 * j) * ((τ : Kd d) * s / q) := pow_succ _ _
    rw [h1, hev]
    field_simp
    ring
  -- `qⁿ` times the even part is `α`'s sum, `qⁿ` times the odd part is `τ√-d` times `β`'s sum
  have hA : (q : Kd d) ^ n • ∑ j ∈ Finset.range (n + 1),
      (((τ : Kd d) * s / q) ^ (2 * j) / ((2 * j).factorial : Kd d)) • ΘK ^ (2 * j) =
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j))⁻¹ *
        ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ)) • ΘK ^ (2 * j) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hev, ← Rat.cast_smul_eq_qsmul (Kd d)]
    congr 1
    push_cast
    ring
  have hB : (q : Kd d) ^ n • ∑ j ∈ Finset.range (n + 1),
      (((τ : Kd d) * s / q) ^ (2 * j + 1) / ((2 * j + 1).factorial : Kd d)) • ΘK ^ (2 * j + 1) =
      ((τ : Kd d) * s) • ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (q : ℚ) ^ n *
        ((q : ℚ) ^ (2 * j + 1))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j + 1).factorial : ℚ)) •
          ΘK ^ (2 * j + 1) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hod, ← Rat.cast_smul_eq_qsmul (Kd d), smul_smul]
    congr 1
    push_cast
    ring
  rw [mul_add, smul_add, ← mul_smul_comm, ← mul_smul_comm, hA, hB, mul_smul_comm]

/-- (§8.1, TeX lines 3686–3688) The displayed expansion of `α`:
`α = qⁿ + ρqⁿ⁻¹Θ + qⁿ⁻²(ρ² - τ²d)Θ²/2 + qⁿ⁻³ρ(ρ² - 3τ²d)Θ³/3! + qⁿ⁻⁴(ρ⁴ - 6ρ²τ²d + τ⁴d²)Θ⁴/4! + ⋯`,
the dots being a multiple of `Θ⁵`. (Natural subtraction in the exponents is harmless: `Θ^j = 0` for
`j > n`.) -/
theorem alphaPP_expansion (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ∃ r : S ℚ n, alphaPP Θ d ρ τ q =
      ((q : ℚ) ^ n) • (1 : S ℚ n) + ((ρ : ℚ) * (q : ℚ) ^ (n - 1)) • Θ +
        ((q : ℚ) ^ (n - 2) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 2) • Θ ^ 2 +
        ((q : ℚ) ^ (n - 3) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - 3 * (τ : ℚ) ^ 2 * d) / 6) • Θ ^ 3 +
        ((q : ℚ) ^ (n - 4) * ((ρ : ℚ) ^ 4 - 6 * (ρ : ℚ) ^ 2 * (τ : ℚ) ^ 2 * d +
          (τ : ℚ) ^ 4 * d ^ 2) / 24) • Θ ^ 4 + Θ ^ 5 * r := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  -- `α = exp(ρΘ/q) C(Θ)` as a double sum `Σᵢ Σⱼ aᵢ cⱼ Θ^{i+2j}`
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℚ, ∀ i, a i = ((ρ : ℚ) / q) ^ i / (i.factorial : ℚ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℚ, ∀ j, c j = (-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j))⁻¹ *
      ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ) := ⟨_, fun _ => rfl⟩
  have hα : alphaPP Θ d ρ τ q = ∑ i ∈ Finset.range (n + 5), ∑ j ∈ Finset.range (n + 3),
      (a i * c j) • Θ ^ (i + 2 * j) := by
    rw [s8_alphaPP_eq Θ hΘ d ρ τ q hq', s8_exp_smul_eq_sum hΘ _ (by omega : n < n + 5)]
    simp only [← ha, ← hc]
    rw [← s8_sum_range_of_vanish (fun j => c j • Θ ^ (2 * j)) (by omega : n + 1 ≤ n + 3)
        (fun j hj _ => by
          show c j • Θ ^ (2 * j) = 0
          rw [s8_pow_eq_zero ℚ n hΘ (by omega), smul_zero]),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, ← pow_add]
  rw [hα, s8_double_sum_trunc]
  refine ⟨∑ i ∈ Finset.range (n + 5), ∑ j ∈ Finset.range (n + 3),
    (if i + 2 * j < 5 then 0 else (a i * c j) • Θ ^ (i + 2 * j - 5)), ?_⟩
  congr 1
  -- the part of degree `< 5`: the pairs `(i, j)` with `i + 2j < 5`
  rw [s8_sum_range_of_vanish _ (by omega : 5 ≤ n + 5) (fun i hi _ => Finset.sum_eq_zero
    fun j _ => ite_eq_right (by omega))]
  rw [Finset.sum_congr rfl fun i _ => s8_sum_range_of_vanish _ (by omega : 3 ≤ n + 3)
    (fun j hj _ => ite_eq_right (by omega))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  -- compare the coefficients of `Θᵏ`, `k ≤ 4`, when `k ≤ n` (else `Θᵏ = 0`)
  have h0 : (a 0 * c 0) • (1 : S ℚ n) = ((q : ℚ) ^ n) • (1 : S ℚ n) := by
    congr 1; rw [ha, hc]; norm_num
  have h1 : (a 1 * c 0) • Θ = ((ρ : ℚ) * (q : ℚ) ^ (n - 1)) • Θ := by
    have := s8_smul_pow_congr hΘ 1 (a := a 1 * c 0) (b := (ρ : ℚ) * (q : ℚ) ^ (n - 1))
      fun hk => by
        rw [ha, hc, pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp
    rwa [pow_one] at this
  have h2 : (a 2 * c 0 + a 0 * c 1) • Θ ^ 2 =
      ((q : ℚ) ^ (n - 2) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 2) • Θ ^ 2 :=
    s8_smul_pow_congr hΘ 2 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp; ring
  have h3 : (a 3 * c 0 + a 1 * c 1) • Θ ^ 3 =
      ((q : ℚ) ^ (n - 3) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - 3 * (τ : ℚ) ^ 2 * d) / 6) • Θ ^ 3 :=
    s8_smul_pow_congr hΘ 3 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp; ring
  have h4 : (a 4 * c 0 + a 2 * c 1 + a 0 * c 2) • Θ ^ 4 =
      ((q : ℚ) ^ (n - 4) * ((ρ : ℚ) ^ 4 - 6 * (ρ : ℚ) ^ 2 * (τ : ℚ) ^ 2 * d +
          (τ : ℚ) ^ 4 * d ^ 2) / 24) • Θ ^ 4 :=
    s8_smul_pow_congr hΘ 4 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp; ring
  rw [← h0, ← h1, ← h2, ← h3, ← h4]
  simp only [add_smul]
  abel

/-- (§8.1, TeX lines 3692–3694) The displayed expansion of `β`:
`β = qⁿ⁻¹Θ + ρqⁿ⁻²Θ² + qⁿ⁻³(3ρ² - dτ²)Θ³/3! + 4qⁿ⁻⁴ρ(ρ² - τ²d)Θ⁴/4! + ⋯`, the dots being a multiple
of `Θ⁵`.

**Misprint corrected** (REPORT.md): the paper prints the coefficient of `Θ⁴/4!` as `qⁿ⁻⁴ρ(ρ² - τ²d)`,
without the factor `4`; its closed form for `β`, which is the definition (`betaPP`), gives
`4qⁿ⁻⁴ρ(ρ² - τ²d)` (the imaginary part of `(ρ + τ√-d)⁴` is `4ρτ(ρ² - τ²d)√d`). -/
theorem betaPP_expansion (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ∃ r : S ℚ n, betaPP Θ d ρ τ q =
      ((q : ℚ) ^ (n - 1)) • Θ + ((ρ : ℚ) * (q : ℚ) ^ (n - 2)) • Θ ^ 2 +
        ((q : ℚ) ^ (n - 3) * (3 * (ρ : ℚ) ^ 2 - d * (τ : ℚ) ^ 2) / 6) • Θ ^ 3 +
        (4 * (q : ℚ) ^ (n - 4) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 24) • Θ ^ 4 +
        Θ ^ 5 * r := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  -- `β = exp(ρΘ/q) S(Θ)` as a double sum `Σᵢ Σⱼ aᵢ cⱼ Θ^{i+2j+1}`
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℚ, ∀ i, a i = ((ρ : ℚ) / q) ^ i / (i.factorial : ℚ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℚ, ∀ j, c j = (-1 : ℚ) ^ j * (q : ℚ) ^ n *
      ((q : ℚ) ^ (2 * j + 1))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j + 1).factorial : ℚ) :=
    ⟨_, fun _ => rfl⟩
  have hβ : betaPP Θ d ρ τ q = ∑ i ∈ Finset.range (n + 5), ∑ j ∈ Finset.range (n + 3),
      (a i * c j) • Θ ^ (i + (2 * j + 1)) := by
    rw [s8_betaPP_eq Θ hΘ d ρ τ q hq', s8_exp_smul_eq_sum hΘ _ (by omega : n < n + 5)]
    simp only [← ha, ← hc]
    rw [← s8_sum_range_of_vanish (fun j => c j • Θ ^ (2 * j + 1)) (by omega : n + 1 ≤ n + 3)
        (fun j hj _ => by
          show c j • Θ ^ (2 * j + 1) = 0
          rw [s8_pow_eq_zero ℚ n hΘ (by omega), smul_zero]),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, ← pow_add]
  rw [hβ, s8_double_sum_trunc]
  refine ⟨∑ i ∈ Finset.range (n + 5), ∑ j ∈ Finset.range (n + 3),
    (if i + (2 * j + 1) < 5 then 0 else (a i * c j) • Θ ^ (i + (2 * j + 1) - 5)), ?_⟩
  congr 1
  -- the part of degree `< 5`: the pairs `(i, j)` with `i + 2j + 1 < 5`
  rw [s8_sum_range_of_vanish _ (by omega : 4 ≤ n + 5) (fun i hi _ => Finset.sum_eq_zero
    fun j _ => ite_eq_right (by omega))]
  rw [Finset.sum_congr rfl fun i _ => s8_sum_range_of_vanish _ (by omega : 2 ≤ n + 3)
    (fun j hj _ => ite_eq_right (by omega))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  -- compare the coefficients of `Θᵏ`, `1 ≤ k ≤ 4`, when `k ≤ n` (else `Θᵏ = 0`)
  have h1 : (a 0 * c 0) • Θ = ((q : ℚ) ^ (n - 1)) • Θ := by
    have := s8_smul_pow_congr hΘ 1 (a := a 0 * c 0) (b := (q : ℚ) ^ (n - 1)) fun hk => by
      rw [ha, hc, pow_sub₀ _ hq' hk]; norm_num
    rwa [pow_one] at this
  have h2 : (a 1 * c 0) • Θ ^ 2 = ((ρ : ℚ) * (q : ℚ) ^ (n - 2)) • Θ ^ 2 :=
    s8_smul_pow_congr hΘ 2 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp
  have h3 : (a 2 * c 0 + a 0 * c 1) • Θ ^ 3 =
      ((q : ℚ) ^ (n - 3) * (3 * (ρ : ℚ) ^ 2 - d * (τ : ℚ) ^ 2) / 6) • Θ ^ 3 :=
    s8_smul_pow_congr hΘ 3 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp; ring
  have h4 : (a 3 * c 0 + a 1 * c 1) • Θ ^ 4 =
      (4 * (q : ℚ) ^ (n - 4) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 24) • Θ ^ 4 :=
    s8_smul_pow_congr hΘ 4 fun hk => by
      simp only [ha, hc]; rw [pow_sub₀ _ hq' hk]; norm_num [Nat.factorial]; field_simp; ring
  rw [← h1, ← h2, ← h3, ← h4]
  simp only [add_smul]
  abel

/-! ### Helpers (prefix `s8_`): integrality of `α`, `β` -/

/-- Elements of `⋀²` are central in the exterior algebra. -/
theorem s8_commute_of_mem_two {c : S ℚ n} (hc : c ∈ ⋀[ℚ]^2 (H1 ℚ n)) (z : S ℚ n) :
    Commute c z := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact s61_commute_ι_mul_ι _ _ z
  | zero => exact Commute.zero_left z
  | add x y _ _ hx hy => exact hx.add_left hy
  | smul a x _ hx => exact hx.smul_left a

theorem s8_basisS_mem_SZ (K : Finset (Fin (2 * n))) : basisS ℚ n K ∈ SZ n := by
  intro L
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s8_one_mem_SZ : (1 : S ℚ n) ∈ SZ n := by
  rw [← s8_basisS_empty ℚ n]
  exact s8_basisS_mem_SZ ∅

theorem s8_intSmul_mem_SZ (z : ℤ) {x : S ℚ n} (hx : x ∈ SZ n) : (z : ℚ) • x ∈ SZ n := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

/-- `H*(X, ℤ)` is a subring: `e_K ∧ e_L = ±e_{K ∪ L}` or `0`. -/
theorem s8_mul_mem_SZ {x y : S ℚ n} (hx : x ∈ SZ n) (hy : y ∈ SZ n) : x * y ∈ SZ n := by
  rw [← (basisS ℚ n).sum_repr x, ← (basisS ℚ n).sum_repr y, Finset.sum_mul_sum]
  refine AddSubgroup.sum_mem _ fun K _ => AddSubgroup.sum_mem _ fun L _ => ?_
  obtain ⟨z₁, hz₁⟩ := hx K
  obtain ⟨z₂, hz₂⟩ := hy L
  rw [smul_mul_smul_comm, s61_basisS_mul, smul_smul, hz₁, hz₂, s61_epsSign_eq]
  split_ifs
  · rw [show (z₁ : ℚ) * z₂ * (-1 : ℚ) ^ s61_inv K L =
        ((z₁ * z₂ * (-1) ^ s61_inv K L : ℤ) : ℚ) by push_cast; ring]
    exact s8_intSmul_mem_SZ _ (s8_basisS_mem_SZ _)
  · rw [mul_zero, zero_smul]; exact zero_mem _

/-- `(x + y)^{j+1} = y^{j+1} + (j+1) x y^j` when `x² = 0` and `x` commutes with `y`. -/
theorem s8_add_pow_succ_of_mul_self {A : Type*} [Ring A] {x y : A} (hx : x * x = 0)
    (hxy : Commute x y) (j : ℕ) :
    (x + y) ^ (j + 1) = y ^ (j + 1) + (j + 1) • (x * y ^ j) := by
  induction j with
  | zero => simp [add_comm]
  | succ j ih =>
    have h1 : y ^ (j + 1) * x = x * y ^ (j + 1) := ((hxy.pow_right (j + 1)).eq).symm
    have h2 : x * y ^ j * x = 0 := by
      rw [mul_assoc, ← (hxy.pow_right j).eq, ← mul_assoc, hx, zero_mul]
    have h3 : x * y ^ j * y = x * y ^ (j + 1) := by rw [mul_assoc, ← pow_succ]
    rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, h1, h2, h3,
      ← pow_succ, smul_zero, zero_add, succ_nsmul _ (j + 1)]
    abel

/-- Divided powers of a sum of central square-zero integral classes are integral. -/
theorem s8_divPow_sum_mem_SZ {ι : Type*} (s : Finset ι) (x : ι → S ℚ n)
    (hxZ : ∀ p, x p ∈ SZ n) (hx2 : ∀ p, x p * x p = 0) (hxc : ∀ p z, Commute (x p) z) (j : ℕ) :
    ((j.factorial : ℚ)⁻¹) • (∑ p ∈ s, x p) ^ j ∈ SZ n := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    cases j with
    | zero => simpa using (s8_one_mem_SZ (n := n))
    | succ j => simp
  | insert p s hp ih =>
    cases j with
    | zero => simpa using (s8_one_mem_SZ (n := n))
    | succ j =>
      rw [Finset.sum_insert hp, s8_add_pow_succ_of_mul_self (hx2 p) (hxc p _), smul_add]
      refine AddSubgroup.add_mem _ (ih _) ?_
      have h : ((((j + 1).factorial : ℕ) : ℚ)⁻¹) • ((j + 1) • (x p * (∑ q ∈ s, x q) ^ j)) =
          x p * (((j.factorial : ℚ)⁻¹) • (∑ q ∈ s, x q) ^ j) := by
        rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_smul_comm, Nat.factorial_succ]
        congr 1
        push_cast
        field_simp
      rw [h]
      exact s8_mul_mem_SZ (hxZ p) (ih j)

/-- (§8.1, TeX line 3700) `Θʲ/j!` is integral for an integral `Θ ∈ H²(X, ℤ)`. -/
theorem s8_divPow_mem_SZ {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘZ : Θ ∈ SZ n) (j : ℕ) :
    ((j.factorial : ℚ)⁻¹) • Θ ^ j ∈ SZ n := by
  have hsum : Θ = ∑ K, (basisS ℚ n).repr Θ K • basisS ℚ n K := ((basisS ℚ n).sum_repr Θ).symm
  rw [hsum]
  refine s8_divPow_sum_mem_SZ _ _ (fun K => ?_) (fun K => ?_) (fun K z => ?_) j
  · obtain ⟨z, hz⟩ := hΘZ K
    rw [hz]
    exact s8_intSmul_mem_SZ z (s8_basisS_mem_SZ K)
  · by_cases hK : K.card = 2
    · have hne : ¬Disjoint K K := by
        rw [Finset.disjoint_self_iff_empty]
        rintro rfl
        simp at hK
      rw [smul_mul_smul_comm, s8_basisS_mul_eq_zero ℚ n hne, smul_zero]
    · rw [s8_repr_eq_zero_of_mem ℚ n hΘ K hK, zero_smul, mul_zero]
  · by_cases hK : K.card = 2
    · have hmem : basisS ℚ n K ∈ ⋀[ℚ]^2 (H1 ℚ n) := by
        have h := s8_basisS_mem ℚ n K
        rwa [hK] at h
      exact (s8_commute_of_mem_two hmem z).smul_left _
    · rw [s8_repr_eq_zero_of_mem ℚ n hΘ K hK, zero_smul]
      exact Commute.zero_left z

/-- `α` as a double sum: `α = Σᵢ Σⱼ (ρ/q)ⁱ/i! · (-1)ʲ qⁿ⁻²ʲ (τ²d)ʲ/(2j)! · Θ^{i+2j}`. -/
theorem s8_alphaPP_double (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (d : ℚ) (ρ τ q : ℤ)
    (hq : (q : ℚ) ≠ 0) :
    alphaPP Θ d ρ τ q = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (((ρ : ℚ) / q) ^ i / (i.factorial : ℚ) * ((-1 : ℚ) ^ j * (q : ℚ) ^ n *
        ((q : ℚ) ^ (2 * j))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ))) •
          Θ ^ (i + 2 * j) := by
  rw [s8_alphaPP_eq Θ hΘ d ρ τ q hq, s8_exp_smul_eq_sum hΘ _ (by omega : n < n + 1),
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, ← pow_add]

/-- `β` as a double sum: `β = Σᵢ Σⱼ (ρ/q)ⁱ/i! · (-1)ʲ qⁿ⁻¹⁻²ʲ (τ²d)ʲ/(2j+1)! · Θ^{i+2j+1}`. -/
theorem s8_betaPP_double (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (d : ℚ) (ρ τ q : ℤ)
    (hq : (q : ℚ) ≠ 0) :
    betaPP Θ d ρ τ q = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (((ρ : ℚ) / q) ^ i / (i.factorial : ℚ) * ((-1 : ℚ) ^ j * (q : ℚ) ^ n *
        ((q : ℚ) ^ (2 * j + 1))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j + 1).factorial : ℚ))) •
          Θ ^ (i + (2 * j + 1)) := by
  rw [s8_betaPP_eq Θ hΘ d ρ τ q hq, s8_exp_smul_eq_sum hΘ _ (by omega : n < n + 1),
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, ← pow_add]

/-- The coefficient `(ρ/q)ⁱ/i! · (-1)ʲ qⁿ (q^m)⁻¹ (τ²d)ʲ/m!` of `Θ^{i+m}` (`m = 2j` or `2j+1`) is
`ρⁱ (-1)ʲ (τ²d)ʲ q^{n-i-m} binom(i+m, i) / (i+m)!`, an integer multiple of `1/(i+m)!` when
`i + m ≤ n` and `d ∈ ℤ`. -/
theorem s8_coef_eq (ρ τ q z : ℤ) (hq : (q : ℚ) ≠ 0) (i j m : ℕ) (hm : i + m ≤ n) :
    ((ρ : ℚ) / q) ^ i / (i.factorial : ℚ) * ((-1 : ℚ) ^ j * (q : ℚ) ^ n *
        ((q : ℚ) ^ m)⁻¹ * ((τ : ℚ) ^ 2 * (z : ℚ)) ^ j / (m.factorial : ℚ)) =
      ((ρ ^ i * (-1) ^ j * (τ ^ 2 * z) ^ j * q ^ (n - (i + m)) * ((i + m).choose i : ℤ) : ℤ) : ℚ) *
        (((i + m).factorial : ℚ))⁻¹ := by
  push_cast
  rw [div_pow, Nat.cast_choose ℚ (by omega : i ≤ i + m), Nat.add_sub_cancel_left,
    pow_sub₀ _ hq hm]
  have h0 : (q : ℚ) ^ i ≠ 0 := pow_ne_zero _ hq
  have h1 : ((i.factorial : ℚ)) ≠ 0 := by positivity
  have h2 : ((m.factorial : ℚ)) ≠ 0 := by positivity
  have h3 : (((i + m).factorial : ℚ)) ≠ 0 := by positivity
  field_simp
  ring

/-- The degree-`k` part of `e_L`. -/
theorem s8_proj_basisS (k : ℕ) (L : Finset (Fin (2 * n))) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) k (basisS ℚ n L) =
      if L.card = k then basisS ℚ n L else 0 := by
  rw [GradedAlgebra.proj_apply]
  split_ifs with hL
  · rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n))
      (by rw [← hL]; exact s8_basisS_mem ℚ n L)]
  · rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) (s8_basisS_mem ℚ n L) hL]

/-- The homogeneous parts of an integral class are integral. -/
theorem s8_proj_mem_SZ {x : S ℚ n} (hx : x ∈ SZ n) (k : ℕ) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) k x ∈ SZ n := by
  rw [← (basisS ℚ n).sum_repr x, map_sum]
  refine AddSubgroup.sum_mem _ fun L _ => ?_
  obtain ⟨z, hz⟩ := hx L
  rw [map_smul, s8_proj_basisS, hz]
  split_ifs
  · exact s8_intSmul_mem_SZ z (s8_basisS_mem_SZ L)
  · rw [smul_zero]; exact zero_mem _

/-- The degree-`k` part of `Θᵐ` (`Θ ∈ ⋀²`). -/
theorem s8_proj_pow {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (k m : ℕ) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) k (Θ ^ m) =
      if 2 * m = k then Θ ^ m else 0 := by
  rw [GradedAlgebra.proj_apply]
  split_ifs with h
  · rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n))
      (by rw [← h]; exact s8_pow_mem ℚ n hΘ m)]
  · rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) (s8_pow_mem ℚ n hΘ m) h]

/-- (§8.1, TeX line 3700) "`α, β ∈ H^{ev}(X, ℤ)`": for `Θ ∈ H²(X, ℤ)` and `d ∈ ℤ`, `α` is integral
(`α = Σ_j qⁿ⁻ʲ Re((ρ + τ√-d)^j) Θ^j/j!` and `Θ^j/j!` is integral). -/
theorem alphaPP_mem_SZ (d : ℚ) (hdZ : ∃ z : ℤ, d = z) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hΘZ : Θ ∈ SZ n) (ρ τ q : ℤ) (hq : 0 < q) : alphaPP Θ d ρ τ q ∈ SZ n := by
  obtain ⟨z, rfl⟩ := hdZ
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  -- termwise: `Θ^{i+2j}` vanishes for `i + 2j > n`, else its coefficient is an integer
  -- multiple of `1/(i+2j)!` and `Θ^{i+2j}/(i+2j)!` is integral
  rw [s8_alphaPP_double Θ hΘ _ ρ τ q hq']
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  by_cases hij : i + 2 * j ≤ n
  · rw [s8_coef_eq ρ τ q z hq' i j (2 * j) hij, mul_smul]
    exact s8_intSmul_mem_SZ _ (s8_divPow_mem_SZ hΘ hΘZ _)
  · rw [s8_pow_eq_zero ℚ n hΘ (by omega), smul_zero]
    exact zero_mem _

/-- (§8.1, TeX line 3700) "`α, β ∈ H^{ev}(X, ℤ)`": `β` is integral. -/
theorem betaPP_mem_SZ (d : ℚ) (hdZ : ∃ z : ℤ, d = z) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hΘZ : Θ ∈ SZ n) (ρ τ q : ℤ) (hq : 0 < q) : betaPP Θ d ρ τ q ∈ SZ n := by
  obtain ⟨z, rfl⟩ := hdZ
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [s8_betaPP_double Θ hΘ _ ρ τ q hq']
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  by_cases hij : i + (2 * j + 1) ≤ n
  · rw [s8_coef_eq ρ τ q z hq' i j (2 * j + 1) hij, mul_smul]
    exact s8_intSmul_mem_SZ _ (s8_divPow_mem_SZ hΘ hΘZ _)
  · rw [s8_pow_eq_zero ℚ n hΘ (by omega), smul_zero]
    exact zero_mem _

/-- (§8.1, TeX line 3700) "`span_ℤ{α, β}` is saturated in `H^{ev}(X, ℤ)` when `q = 1`": a rational
combination `aα + bβ` is integral only if `a, b ∈ ℤ`. Hypotheses: `Θ` integral and primitive in
`H²(X, ℤ)` (true for the generator `Θ` of `NS(X)`, which is saturated in `H²(X, ℤ)`), `d ∈ ℤ`,
`n ≥ 1`. -/
theorem saturated_of_q_eq_one (d : ℚ) (hn : 1 ≤ n) (Θ : S ℚ n)
    (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hprim : ∀ c : ℚ, c • Θ ∈ SZ n → ∃ z : ℤ, c = z) (ρ τ : ℤ) (a b : ℚ)
    (hab : a • alphaPP Θ d ρ τ 1 + b • betaPP Θ d ρ τ 1 ∈ SZ n) :
    (∃ z : ℤ, a = z) ∧ ∃ z : ℤ, b = z := by
  have hq1 : ((1 : ℤ) : ℚ) ≠ 0 := by norm_num
  -- the degree-`0` and degree-`2` parts of `α = 1 + ρΘ + ⋯` and `β = Θ + ⋯` (`q = 1`)
  have hP0α : GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) 0 (alphaPP Θ d ρ τ 1) = 1 := by
    rw [s8_alphaPP_double Θ hΘ d ρ τ 1 hq1]
    simp only [map_sum, map_smul, s8_proj_pow hΘ]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
      · simp
      · intro j _ hj; rw [ite_eq_right (by omega), smul_zero]
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (by omega), smul_zero]
  have hP0β : GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) 0 (betaPP Θ d ρ τ 1) = 0 := by
    rw [s8_betaPP_double Θ hΘ d ρ τ 1 hq1]
    simp only [map_sum, map_smul, s8_proj_pow hΘ]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [ite_eq_right (by omega), smul_zero]
  have hP2α : GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) 2 (alphaPP Θ d ρ τ 1) =
      (ρ : ℚ) • Θ := by
    rw [s8_alphaPP_double Θ hΘ d ρ τ 1 hq1]
    simp only [map_sum, map_smul, s8_proj_pow hΘ]
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
      · simp
      · intro j _ hj; rw [ite_eq_right (by omega), smul_zero]
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (by omega), smul_zero]
  have hP2β : GradedAlgebra.proj (fun i : ℕ => ⋀[ℚ]^i (H1 ℚ n)) 2 (betaPP Θ d ρ τ 1) = Θ := by
    rw [s8_betaPP_double Θ hΘ d ρ τ 1 hq1]
    simp only [map_sum, map_smul, s8_proj_pow hΘ]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
      · simp
      · intro j _ hj; rw [ite_eq_right (by omega), smul_zero]
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (by omega), smul_zero]
  -- degree `0`: `a ∈ ℤ`
  have h0 := s8_proj_mem_SZ hab 0
  rw [map_add, map_smul, map_smul, hP0α, hP0β, smul_zero, add_zero] at h0
  obtain ⟨za, hza⟩ := h0 ∅
  rw [map_smul, ← s8_basisS_empty ℚ n, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at hza
  refine ⟨⟨za, hza⟩, ?_⟩
  -- degree `2`: `(aρ + b) Θ` is integral, so `aρ + b ∈ ℤ` (`Θ` primitive)
  have h2 := s8_proj_mem_SZ hab 2
  rw [map_add, map_smul, map_smul, hP2α, hP2β, smul_smul, ← add_smul] at h2
  obtain ⟨zb, hzb⟩ := hprim _ h2
  exact ⟨zb - za * ρ, by push_cast; rw [← hzb, hza]; ring⟩

/-! ### Helpers (prefix `s8_`): the table of `χ(F^∨ ⊗ F)`

With `E = exp(ρΘ/q)`, `α = E A` and `β = E B` where `A` is even and `B` is odd in `Θ`; since
`τ(Θ) = -Θ`, `τ(aα + bβ)(aα + bβ) = (aA - bB) E⁻¹ E (aA + bB) = a²A² - b²B²`, and
`∫_X Θᵐ = n! δ_{m,n}`. For `n = 2m` the two double sums collapse to
`(-1)ᵐ qⁿ (τ²d)ᵐ Σⱼ binom(n, 2j)` and `(-1)ᵐ⁻¹ qⁿ (τ²d)ᵐ⁻¹ Σⱼ binom(n, 2j+1)`, both binomial sums
being `2ⁿ⁻¹`. -/

/-- `∫_X Θᵐ = n! δ_{m,n}` for a principal `Θ`. -/
theorem s8_integral_pow {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (m : ℕ) :
    integral ℚ n (Θ ^ m) = if m = n then (n.factorial : ℚ) else 0 := by
  split_ifs with h
  · rw [h, hpp, map_smul, s8_integral_pt, smul_eq_mul, mul_one]
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · exact s8_integral_eq_zero_of_mem ℚ n (by omega) (s8_pow_mem ℚ n hΘ m)
    · rw [s8_pow_eq_zero ℚ n hΘ hgt, map_zero]

/-- `∫_X (Σⱼ cⱼ Θ^{eⱼ})² = n! Σ_{eⱼ + eₖ = n} cⱼ cₖ`. -/
theorem s8_integral_sq_sum {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (c : ℕ → ℚ) (e : ℕ → ℕ) (N : ℕ) :
    integral ℚ n ((∑ j ∈ Finset.range N, c j • Θ ^ e j) * (∑ k ∈ Finset.range N, c k • Θ ^ e k)) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        c j * c k * (if e j + e k = n then (n.factorial : ℚ) else 0) := by
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_smul_comm, ← pow_add, map_smul, s8_integral_pow hΘ hpp, smul_eq_mul]

theorem s8_tau_even_sum {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (c : ℕ → ℚ) (N : ℕ) :
    tau ℚ n (∑ j ∈ Finset.range N, c j • Θ ^ (2 * j)) = ∑ j ∈ Finset.range N, c j • Θ ^ (2 * j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, s8_tau_pow ℚ n hΘ, Even.neg_pow (even_two_mul j)]

theorem s8_tau_odd_sum {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (c : ℕ → ℚ) (N : ℕ) :
    tau ℚ n (∑ j ∈ Finset.range N, c j • Θ ^ (2 * j + 1)) =
      -∑ j ∈ Finset.range N, c j • Θ ^ (2 * j + 1) := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, s8_tau_pow ℚ n hΘ, Odd.neg_pow (odd_two_mul_add_one j), smul_neg]

theorem s8_commute_sums (Θ : S ℚ n) (c c' : ℕ → ℚ) (e e' : ℕ → ℕ) (N N' : ℕ) :
    Commute (∑ j ∈ Finset.range N, c j • Θ ^ e j) (∑ k ∈ Finset.range N', c' k • Θ ^ e' k) :=
  Commute.sum_left _ _ _ fun _ _ => Commute.sum_right _ _ _ fun _ _ =>
    (((Commute.refl Θ).pow_pow _ _).smul_left _).smul_right _

theorem s8_tau_exp_mul_exp {Θ : S ℚ n} (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (c : ℚ) :
    tau ℚ n (IsNilpotent.exp (c • Θ)) * IsNilpotent.exp (c • Θ) = 1 := by
  rw [s8_tau_exp ℚ n (Submodule.smul_mem _ c hΘ), ← neg_smul,
    ← IsNilpotent.exp_add_of_commute (((Commute.refl Θ).smul_left _).smul_right _)
      (s8_isNilpotent_of_mem_two hΘ _) (s8_isNilpotent_of_mem_two hΘ _), ← add_smul,
    neg_add_cancel, zero_smul, IsNilpotent.exp_zero]

theorem s8_tau_mul_self_of {E A B : S ℚ n} (hE : tau ℚ n E * E = 1) (hA : tau ℚ n A = A)
    (hB : tau ℚ n B = -B) (hAB : Commute A B) (a b : ℚ) :
    tau ℚ n (a • (E * A) + b • (E * B)) * (a • (E * A) + b • (E * B)) =
      (a ^ 2) • (A * A) - (b ^ 2) • (B * B) := by
  have h1 : a • (E * A) + b • (E * B) = E * (a • A + b • B) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  rw [h1, s8_tau_mul, map_add, map_smul, map_smul, hA, hB, mul_assoc, ← mul_assoc (tau ℚ n E), hE,
    one_mul]
  simp only [add_mul, mul_add, smul_neg, neg_mul, smul_mul_smul_comm]
  rw [← hAB.eq, mul_comm b a, sq, sq]
  abel

theorem s8_double_sum_diag {M' : Type*} [AddCommMonoid M'] (g : ℕ → ℕ → M') {N M : ℕ}
    (hMN : M + 1 ≤ N) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, (if j + k = M then g j k else 0) =
      ∑ j ∈ Finset.range (M + 1), g j (M - j) := by
  rw [s8_sum_range_of_vanish _ hMN (fun j hj _ => Finset.sum_eq_zero fun k _ => ite_eq_right (by omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [Finset.sum_eq_single_of_mem (M - j) (Finset.mem_range.mpr (by omega))
    (fun k _ hk => ite_eq_right (by omega)), ite_eq_left (by omega)]

theorem s8_sum_choose_even_odd (m : ℕ) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ)) = 2 ^ (2 * m - 1) ∧
      (∑ j ∈ Finset.range m, ((2 * m).choose (2 * j + 1) : ℚ)) = 2 ^ (2 * m - 1) := by
  set E := ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ)
  set O := ∑ j ∈ Finset.range m, ((2 * m).choose (2 * j + 1) : ℚ)
  have hO : ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j + 1) : ℚ) = O := by
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : 2 * m < 2 * m + 1),
      Nat.cast_zero, add_zero]
  have hext : ∀ f : ℕ → ℚ, f (2 * m + 1) = 0 →
      ∑ i ∈ Finset.range (2 * (m + 1)), f i = ∑ i ∈ Finset.range (2 * m + 1), f i := by
    intro f hf
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, hf, add_zero]
  have hc : (2 * m).choose (2 * m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h1 : E + O = 2 ^ (2 * m) := by
    have := s8_sum_range_two_mul (fun i => ((2 * m).choose i : ℚ)) (m + 1)
    rw [hext _ (by simp), hO] at this
    rw [← this]
    exact_mod_cast Nat.sum_range_choose (2 * m)
  have h2 : E - O = 0 := by
    have := s8_sum_range_two_mul (fun i => (-1 : ℚ) ^ i * ((2 * m).choose i : ℚ)) (m + 1)
    rw [hext _ (by simp)] at this
    have he : ∀ j : ℕ, (-1 : ℚ) ^ (2 * j) = 1 := fun j => by rw [pow_mul, neg_one_sq, one_pow]
    have ho : ∀ j : ℕ, (-1 : ℚ) ^ (2 * j + 1) = -1 := fun j => by rw [pow_succ, he, one_mul]
    simp only [he, ho, one_mul, neg_one_mul, Finset.sum_neg_distrib] at this
    rw [hO, ← sub_eq_add_neg] at this
    rw [← this]
    exact_mod_cast Int.alternating_sum_range_choose_of_ne (by omega : 2 * m ≠ 0)
  have h4 : (2 : ℚ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']; congr 1; omega
  constructor <;> linarith

theorem s8_coefA_mul (q t : ℚ) (hq : q ≠ 0) {m j : ℕ} (hj : j ≤ m) :
    ((-1 : ℚ) ^ j * q ^ (2 * m) * (q ^ (2 * j))⁻¹ * t ^ j / ((2 * j).factorial : ℚ)) *
      ((-1 : ℚ) ^ (m - j) * q ^ (2 * m) * (q ^ (2 * (m - j)))⁻¹ * t ^ (m - j) /
        ((2 * (m - j)).factorial : ℚ)) * ((2 * m).factorial : ℚ) =
      (-1) ^ m * q ^ (2 * m) * t ^ m * ((2 * m).choose (2 * j) : ℚ) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left, Nat.cast_choose ℚ (by omega : 2 * j ≤ 2 * (j + l)),
    show 2 * (j + l) - 2 * j = 2 * l by omega]
  have h1 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * l).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem s8_coefB_mul (q t : ℚ) (hq : q ≠ 0) {m j : ℕ} (hm : 1 ≤ m) (hj : j ≤ m - 1) :
    ((-1 : ℚ) ^ j * q ^ (2 * m) * (q ^ (2 * j + 1))⁻¹ * t ^ j / ((2 * j + 1).factorial : ℚ)) *
      ((-1 : ℚ) ^ (m - 1 - j) * q ^ (2 * m) * (q ^ (2 * (m - 1 - j) + 1))⁻¹ * t ^ (m - 1 - j) /
        ((2 * (m - 1 - j) + 1).factorial : ℚ)) * ((2 * m).factorial : ℚ) =
      (-1) ^ (m - 1) * q ^ (2 * m) * t ^ (m - 1) * ((2 * m).choose (2 * j + 1) : ℚ) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (show j ≤ m' by omega)
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel_left,
    Nat.cast_choose ℚ (by omega : 2 * j + 1 ≤ 2 * (j + l + 1)),
    show 2 * (j + l + 1) - (2 * j + 1) = 2 * l + 1 by omega]
  have h1 : ((2 * j + 1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * l + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem s8_sum_if_two_mul (f : ℕ → ℕ → ℚ) (F : ℚ) (N m : ℕ) (hN : m + 1 ≤ N) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        f j k * (if 2 * j + 2 * k = 2 * m then F else 0) =
      ∑ j ∈ Finset.range (m + 1), f j (m - j) * F := by
  rw [← s8_double_sum_diag (fun j k => f j k * F) hN]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j + k = m
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]

theorem s8_sum_if_two_mul_add_one (f : ℕ → ℕ → ℚ) (F : ℚ) (N m : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        f j k * (if 2 * j + 1 + (2 * k + 1) = 2 * m then F else 0) =
      ∑ j ∈ Finset.range m, f j (m - 1 - j) * F := by
  have h := s8_double_sum_diag (fun j k => f j k * F) (M := m - 1) (N := N) (by omega)
  rw [show m - 1 + 1 = m by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j + k = m - 1
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]

/-- The integral `∫_X τ(aα + bβ)(aα + bβ) = a² ∫ A² - b² ∫ B²` as double sums. -/
theorem s8_chi_eq (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (ρ τ q : ℤ) (hq : (q : ℚ) ≠ 0) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      a ^ 2 * ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j /
          ((2 * j).factorial : ℚ)) *
        ((-1 : ℚ) ^ k * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * k))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ k /
          ((2 * k).factorial : ℚ)) *
        (if 2 * j + 2 * k = n then (n.factorial : ℚ) else 0) -
      b ^ 2 * ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ j * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * j + 1))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ j /
          ((2 * j + 1).factorial : ℚ)) *
        ((-1 : ℚ) ^ k * (q : ℚ) ^ n * ((q : ℚ) ^ (2 * k + 1))⁻¹ * ((τ : ℚ) ^ 2 * d) ^ k /
          ((2 * k + 1).factorial : ℚ)) *
        (if 2 * j + 1 + (2 * k + 1) = n then (n.factorial : ℚ) else 0) := by
  rw [s8_alphaPP_eq Θ hΘ d ρ τ q hq, s8_betaPP_eq Θ hΘ d ρ τ q hq,
    s8_tau_mul_self_of (s8_tau_exp_mul_exp hΘ _) (s8_tau_even_sum hΘ _ _) (s8_tau_odd_sum hΘ _ _)
      (s8_commute_sums Θ _ _ _ _ _ _), map_sub, map_smul, map_smul,
    s8_integral_sq_sum hΘ hpp, s8_integral_sq_sum hΘ hpp, smul_eq_mul, smul_eq_mul]

/-- The table for `n = 2m` even. -/
theorem s8_chi_even (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (hn : Even n) (hn2 : 2 ≤ n) (ρ τ q : ℤ)
    (hq : 0 < q) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      (-1 : ℚ) ^ (n / 2) * 2 ^ (n - 1) * d ^ (n / 2 - 1) * (q : ℚ) ^ n * (τ : ℚ) ^ (n - 2) *
        (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [s8_chi_eq d Θ hΘ hpp ρ τ q hq' a b]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨r, hr⟩ := hn; omega⟩
  have hm : 1 ≤ m := by omega
  rw [s8_sum_if_two_mul _ _ _ m (by omega), s8_sum_if_two_mul_add_one _ _ _ m hm (by omega),
    Finset.sum_congr rfl fun j hj => s8_coefA_mul (q : ℚ) ((τ : ℚ) ^ 2 * d) hq'
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)),
    Finset.sum_congr rfl fun j hj => s8_coefB_mul (q : ℚ) ((τ : ℚ) ^ 2 * d) hq' hm
      (by have := Finset.mem_range.mp hj; omega),
    ← Finset.mul_sum, ← Finset.mul_sum, (s8_sum_choose_even_odd m hm).1,
    (s8_sum_choose_even_odd m hm).2, Nat.mul_div_cancel_left m two_pos]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, show 2 * (m' + 1) - 2 = 2 * m' by omega]
  ring

/-- (§8.1, TeX lines 3703–3711) The table of `χ(F^∨ ⊗ F) = ∫_X (aα + bβ)^∨ (aα + bβ)`, `n` odd: it is
`0`. Model: `w^∨ = τ(w)` (Remark 5.2.3), `Θ` principal (`Θⁿ = n! [pt]`), `a, b ∈ ℚ`. (Checked
symbolically for `n ≤ 6`.) -/
theorem chi8_1_odd (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (hn : Odd n) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) = 0 := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [s8_chi_eq d Θ hΘ hpp ρ τ q hq' a b]
  obtain ⟨k, rfl⟩ := hn
  rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => by
      rw [ite_eq_right (by omega), mul_zero],
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => by
      rw [ite_eq_right (by omega), mul_zero]]
  ring

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n = 2`: `-2q²(a²τ²d + b²)`. -/
theorem chi8_1_two (d : ℚ) (Θ : S ℚ 2) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ 2))
    (hpp : Θ ^ 2 = (2 : ℚ) • pt ℚ 2) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ 2 (tau ℚ 2 (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      -2 * (q : ℚ) ^ 2 * (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  have hpp' : Θ ^ 2 = ((Nat.factorial 2 : ℕ) : ℚ) • pt ℚ 2 := by
    rw [hpp, Nat.factorial_two, Nat.cast_ofNat]
  rw [s8_chi_even d Θ hΘ hpp' ⟨1, rfl⟩ le_rfl ρ τ q hq a b]
  norm_num

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n = 4`: `8dq⁴τ²(a²τ²d + b²)`. -/
theorem chi8_1_four (d : ℚ) (Θ : S ℚ 4) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ 4))
    (hpp : Θ ^ 4 = (24 : ℚ) • pt ℚ 4) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ 4 (tau ℚ 4 (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      8 * d * (q : ℚ) ^ 4 * (τ : ℚ) ^ 2 * (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  have hpp' : Θ ^ 4 = ((Nat.factorial 4 : ℕ) : ℚ) • pt ℚ 4 := by
    rw [hpp]; norm_num [Nat.factorial]
  rw [s8_chi_even d Θ hΘ hpp' ⟨2, rfl⟩ (by norm_num) ρ τ q hq a b]
  norm_num

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n` even:
`(-1)^{n/2} 2^{n-1} d^{n/2-1} qⁿ τ^{n-2} (a²τ²d + b²)` (`n ≥ 2`). -/
theorem chi8_1_even (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (hn : Even n) (hn2 : 2 ≤ n) (ρ τ q : ℤ)
    (hq : 0 < q) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      (-1 : ℚ) ^ (n / 2) * 2 ^ (n - 1) * d ^ (n / 2 - 1) * (q : ℚ) ^ n * (τ : ℚ) ^ (n - 2) *
        (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) :=
  s8_chi_even d Θ hΘ hpp hn hn2 ρ τ q hq a b

end Enumeration

end WeilClasses
