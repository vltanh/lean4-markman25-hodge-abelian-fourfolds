module

public import WeilClasses.PureSpinor.Lemma2_2_1
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import WeilClasses.External.Chevalley.Sec3
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# Stabilizers of `K`-secants: `Spin(V_K)_{ℓ₁,ℓ₂}`, `Spin(V_K)_P`, Lemma 2.2.2 and Remark 2.2.3

Paper §2.2, from "Assume that `W₁ ∩ W₂` is the zero subspace" to Remark 2.2.3. Throughout, the
standing hypothesis of the paper `W₁ ∩ W₂ = 0` is an explicit hypothesis `hW`, and `0 < d` is the
paper's "`K` purely imaginary".

## Main definitions

* `WeilClasses.annRestrict F n u`: the action `Spin(V_F)_{[u]} → End(ker m_u)` of the stabilizer of
  the line `[u]` on `W = ker m_u`.
* `WeilClasses.pairRestrict F n u₁ u₂`: the homomorphism
  `Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`.
* `WeilClasses.specialLinearUnits F W`: `SL(W) ⊆ GL(W)`.
* `WeilClasses.KSecant.restrictW₁`: `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, and `KSecant.restrictW₁P`, its
  restriction to `Spin(V_K)_P`.
* `WeilClasses.KSecant.pairingW₂`: the identification `W₂ → W₁*` given by the pairing of `V_K`.

## Statements

* The claims attributed to [Igusa, Lemma 1] (`KSecant.restrictW₁_eq_one_iff`,
  `KSecant.range_restrictW₁` (corrected, see below),
  `KSecant.rho_eq_one_iff`, `KSecant.pairingW₂_bijective`, `KSecant.pairingW₂_rho`),
  `KSecant.det₂_eq_inv` (`det₂ = det₁⁻¹`), `KSecant.χ₁_sq`, `KSecant.χ₂_sq` (`ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`).
* **Lemma 2.2.2** with the misprint `SL_n(K)` corrected to `SL_{2n}(K)` (`lemma2_2_2`,
  `lemma2_2_2_restrict`).
* **Remark 2.2.3** ([Igusa, Lemma 2] and the remark after it): `remark2_2_3_not_pure`,
  `remark2_2_3_odd`, `remark2_2_3_even`, `remark2_2_3_determines`, `remark2_2_3_unique_secant`.

## A false claim of the paper

The paper says "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`". At the
level of `K`-points this contradicts the paper's own `ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁` (`χ₁² = det₁`): `det₁` only
takes square values, so the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)` is the subgroup of
endomorphisms with square determinant. For instance, if `x ∈ W₂`, `y ∈ W₁`, `(x, y)_V = 1`, the
element of `SO(V_K)` acting by `a ∉ K^{×2}` on `y`, by `a⁻¹` on `x` and trivially on the
orthogonal of `x, y` is not in `ρ(Spin(V_K))`: its two lifts `±(√a⁻¹ x y + √a y x)` to
`Spin(V_{K̄})` are not `K`-rational. The isomorphism holds for the algebraic groups (over `K̄`). We
state the corrected claim (`KSecant.range_restrictW₁`), as agreed with the project owner.
Lemma 2.2.2 is unaffected.

## Proofs

The cited results [Igusa, Lemmas 1 and 2] have statements of record in
`WeilClasses.External.Igusa.Sec2_2`, which imports this file, and [Chevalley, III.1.4, III.1.12,
III.2.4] in `WeilClasses.External.Chevalley.Sec2_2`, downstream too; the facts used are proved here
(sections `S22aKernel`, `S22aLift`, `S22aLineStab`, `S22aFix`, `S22aSwap`). [Chevalley, III.3.2 and
III.4.5] (`chevalley_III_3_2_III_4_5`, for `χᵢ² = detᵢ`) is imported and used by name.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prover P03, prefix `s22a_`) -/

section S22aKernel

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s22a_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

omit [CharZero F] in
theorem s22a_nontrivial_V (hn : 0 < n) : Nontrivial (V F n) :=
  ⟨⟨(0, 0), (0, e F n ⟨0, by omega⟩), by
    intro h
    have := congrFun (congrArg Prod.snd h) ⟨0, by omega⟩
    simp [e] at this⟩⟩

/-- The kernel of `ρ : Spin(V_F) → SO(V_F)` is `{±1}` (Tau Ceti). -/
theorem s22a_rho_eq_one_iff (hn : 0 < n) (g : Spin F n) :
    rho F n g = 1 ↔ (g : C F n) = 1 ∨ (g : C F n) = -1 := by
  have := s22a_nontrivial_V (F := F) hn
  have hker : rho F n g = 1 ↔ g ∈ MonoidHom.ker (spinToOrthogonal (Q F n)) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rw [coe_spinToOrthogonal_apply]
      exact LinearEquiv.congr_fun h v
    · intro h
      apply LinearEquiv.ext
      intro v
      have := congrArg
        (fun x : TauCeti.QuadraticMap.orthogonalGroup (Q F n) => (x : V F n ≃ₗ[F] V F n) v) h
      show spinVectorAction (Q F n) g v = v
      simpa using this
  rw [hker, mem_ker_spinToOrthogonal_iff (Q F n) s22a_Q_nondegenerate g]
  constructor
  · rintro (rfl | rfl)
    · left; rfl
    · right; exact spinGroup.coe_negOne _ _
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; apply Subtype.ext; rw [h, spinGroup.coe_negOne]

omit [CharZero F] in
/-- `ι v ι u ι v = ι((v, u)_V v - Q(v) u)`. -/
theorem s22a_ι_mul_ι_mul_ι (v u : V F n) :
    ι (Q F n) v * ι (Q F n) u * ι (Q F n) v =
      ι (Q F n) (QuadraticMap.polar (Q F n) v u • v - Q F n v • u) := by
  rw [CliffordAlgebra.ι_mul_ι_comm v u, sub_mul, mul_assoc, ι_sq_scalar, map_sub, map_smul,
    map_smul, Algebra.smul_def, Algebra.smul_def, Algebra.commutes (Q F n v)]

/-- For `Q(p) Q(q) = 1`, `ι p ι q ∈ Spin(V_F)` and `ρ(ι p ι q) = r_p ∘ r_q` with
`r_v(z) = (v, z)_V v - Q(v) z` (a product of two reflections). -/
private theorem s22a_rho_ι_mul_ι (p q : V F n) (hpq : Q F n p * Q F n q = 1) (z : V F n) :
    rho F n ⟨ι (Q F n) p * ι (Q F n) q,
        ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one p q hpq⟩ z =
      QuadraticMap.polar (Q F n) p (QuadraticMap.polar (Q F n) q z • q - Q F n q • z) • p -
        Q F n p • (QuadraticMap.polar (Q F n) q z • q - Q F n q • z) := by
  apply CliffordAlgebra.ι_injective (Q F n)
  rw [ι_rho]
  have hstar : star (ι (Q F n) p * ι (Q F n) q) = ι (Q F n) q * ι (Q F n) p := by
    rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι, neg_mul_neg]
  show ι (Q F n) p * ι (Q F n) q * ι (Q F n) z * star (ι (Q F n) p * ι (Q F n) q) = _
  rw [hstar, show ι (Q F n) p * ι (Q F n) q * ι (Q F n) z * (ι (Q F n) q * ι (Q F n) p) =
    ι (Q F n) p * (ι (Q F n) q * ι (Q F n) z * ι (Q F n) q) * ι (Q F n) p by noncomm_ring,
    s22a_ι_mul_ι_mul_ι q z, s22a_ι_mul_ι_mul_ι p]

/-- `ρ` of Tau Ceti's spin lift `1 + ι w ι u` of an Eichler transvection. -/
private theorem s22a_rho_spinTransvection {u w : V F n} (hu : Q F n u = 0)
    (huw : QuadraticMap.polar (Q F n) u w = 0) (z : V F n) :
    rho F n (spinTransvection s22a_Q_nondegenerate hu huw) z =
      z + QuadraticMap.polar (Q F n) z u • w - QuadraticMap.polar (Q F n) z w • u -
        (Q F n w * QuadraticMap.polar (Q F n) z u) • u := by
  rw [← QuadraticMap.transvection_apply hu huw,
    ← coe_spinToSpecialOrthogonal_spinTransvection s22a_Q_nondegenerate hu huw,
    coe_spinToSpecialOrthogonal_apply]
  rfl

end S22aKernel

/-! ## Helpers (prover P03): lifting `SL(W₁)` to `Spin(V)` ([Igusa, Lemma 1])

The paper uses [Igusa, Lemma 1] (`Spin(V_K)_{ℓ₁,ℓ₂}/{±1} ≅ GL(W₁)`, corrected to the subgroup of
square determinant). The statements of record (`WeilClasses.igusa_lemma1_*`) cannot be imported here:
`WeilClasses.External.Igusa.Sec2_2` imports this file. We prove the surjectivity part used: in dual
bases `xᵢ` of `W₁`, `yᵢ` of `W₂`, `SL(W₁)` is generated by the transvections `1 + a E_{ij}` and
`diag(c, c⁻¹)` (`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`); the former lift to
the spin transvections `1 + ι(a xᵢ) ι(yⱼ)` (Tau Ceti), the latter to products of four vectors
`ι(xᵢ + yᵢ) ι(xⱼ + yⱼ) ι(xᵢ + c yᵢ) ι(xⱼ + c⁻¹ yⱼ)` (two pairs of reflections). -/

section S22aLift

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
private theorem s22a_sum_transvection (x : Fin (2 * n) → V F n) {i j : Fin (2 * n)} (a : F)
    (k : Fin (2 * n)) :
    ∑ l, ((1 : Matrix (Fin (2 * n)) (Fin (2 * n)) F) + Matrix.single i j a) l k • x l =
      x k + (if k = j then a else 0) • x i := by
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
    Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  congr 1
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

omit [CharZero F] in
private theorem s22a_sum_diagonal (x : Fin (2 * n) → V F n) (D : Fin (2 * n) → F)
    (k : Fin (2 * n)) : ∑ l, (Matrix.diagonal D) l k • x l = D k • x k := by
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

set_option linter.unusedSimpArgs false in
/-- **Lifting `SL(W₁)` to `Spin(V)`** (the surjectivity in [Igusa, Lemma 1]): for dual bases `x` of
`W₁` and `y` of `W₂` (complementary isotropic subspaces), every `M ∈ SL_{2n}(F)` is the matrix of
`ρ(g)|_{W₁}` in the basis `x` for some `g ∈ Spin(V_F)` preserving `W₂`. -/
private theorem s22a_lift_SL (hn : 0 < n) {W₂ : Submodule F (V F n)}
    (i₂ : ∀ a ∈ W₂, ∀ b ∈ W₂, QuadraticMap.polar (Q F n) a b = 0)
    {x y : Fin (2 * n) → V F n} (hy : ∀ i, y i ∈ W₂)
    (ex₂ : ∀ w ∈ W₂, w = ∑ i, QuadraticMap.polar (Q F n) (x i) w • y i)
    (pxy : ∀ a b, QuadraticMap.polar (Q F n) (x a) (y b) = if a = b then 1 else 0)
    (pxx : ∀ a b, QuadraticMap.polar (Q F n) (x a) (x b) = 0)
    (Qx : ∀ a, Q F n (x a) = 0) (Qy : ∀ a, Q F n (y a) = 0)
    (M : Matrix.SpecialLinearGroup (Fin (2 * n)) F) :
    ∃ g : Spin F n, (∀ k, rho F n g (x k) = ∑ l, (M : Matrix _ _ F) l k • x l) ∧
      (∀ w ∈ W₂, rho F n g w ∈ W₂) := by
  have pyx : ∀ a b, QuadraticMap.polar (Q F n) (y a) (x b) = if b = a then 1 else 0 := by
    intro a b
    rw [QuadraticMap.polar_comm, pxy]
  have pyy : ∀ a b, QuadraticMap.polar (Q F n) (y a) (y b) = 0 := fun a b => i₂ _ (hy a) _ (hy b)
  have : Nontrivial (Fin (2 * n)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  -- `W₂` is preserved as soon as each `yₖ` goes to `W₂`.
  have hW₂ : ∀ g : Spin F n, (∀ k, rho F n g (y k) ∈ W₂) → ∀ w ∈ W₂, rho F n g w ∈ W₂ := by
    intro g hg w hw
    rw [ex₂ w hw, map_sum]
    exact Submodule.sum_mem _ fun i _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hg i)
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun M : Matrix.SpecialLinearGroup (Fin (2 * n)) F => ∃ g : Spin F n,
      (∀ k, rho F n g (x k) = ∑ l, (M : Matrix _ _ F) l k • x l) ∧
      (∀ w ∈ W₂, rho F n g w ∈ W₂)) M ?_ ?_ ?_
  · -- `diag(c, c⁻¹)` at `(i, j)`
    intro i j hij c hc
    have Qa : ∀ k, Q F n (x k + y k) = 1 := by
      intro k
      rw [QuadraticMap.map_add (Q F n), Qx, Qy, pxy, ite_eq_left rfl, zero_add, zero_add]
    have Qb : ∀ (k : Fin (2 * n)) (t : F), Q F n (x k + t • y k) = t := by
      intro k t
      rw [QuadraticMap.map_add (Q F n), Qx, QuadraticMap.map_smul, Qy,
        QuadraticMap.polar_smul_right, pxy, ite_eq_left rfl]
      simp
    have h₁ : Q F n (x i + y i) * Q F n (x j + y j) = 1 := by rw [Qa, Qa, one_mul]
    have h₂ : Q F n (x i + c • y i) * Q F n (x j + c⁻¹ • y j) = 1 := by
      rw [Qb, Qb, mul_inv_cancel₀ hc]
    set g₁ : Spin F n := ⟨ι (Q F n) (x i + y i) * ι (Q F n) (x j + y j),
      ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ h₁⟩ with hg₁
    set g₂ : Spin F n := ⟨ι (Q F n) (x i + c • y i) * ι (Q F n) (x j + c⁻¹ • y j),
      ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ h₂⟩ with hg₂
    have hji : j ≠ i := Ne.symm hij
    have r₁ : ∀ z, rho F n g₁ z = _ := fun z => s22a_rho_ι_mul_ι _ _ h₁ z
    have r₂ : ∀ z, rho F n g₂ z = _ := fun z => s22a_rho_ι_mul_ι _ _ h₂ z
    refine ⟨g₁ * g₂, fun k => ?_, hW₂ _ fun k => ?_⟩
    · rw [Matrix.SpecialLinearGroup.diag2n_coe, s22a_sum_diagonal, s22a_rho_mul, r₂, r₁]
      by_cases hki : k = i
      · subst hki
        simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji]
        simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
        match_scalars <;> field_simp <;> ring
      · by_cases hkj : k = j
        · subst hkj
          simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji, hki, Ne.symm hki]
          simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
          match_scalars <;> field_simp <;> ring
        · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji, hki, Ne.symm hki, hkj, Ne.symm hkj]
          simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
          match_scalars <;> field_simp <;> ring
    · have e : rho F n (g₁ * g₂) (y k) =
          (if k = i then c⁻¹ else if k = j then c else 1) • y k := by
        rw [s22a_rho_mul, r₂, r₁]
        by_cases hki : k = i
        · subst hki
          simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
            QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
            QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
            smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
            one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji]
          simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
          match_scalars <;> field_simp <;> ring
        · by_cases hkj : k = j
          · subst hkj
            simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
            QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
            QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
            smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
            one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji, hki, Ne.symm hki]
            simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
            match_scalars <;> field_simp <;> ring
          · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
            QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
            QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qa, Qb,
            smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
            one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hij, hji, hki, Ne.symm hki, hkj, Ne.symm hkj]
            simp only [smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
            match_scalars <;> field_simp <;> ring
      rw [e]
      exact Submodule.smul_mem _ _ (hy k)
  · -- transvection `1 + a E_{ij}`
    intro i j hij a
    have huw : QuadraticMap.polar (Q F n) (y j) (a • x i) = 0 := by
      rw [QuadraticMap.polar_smul_right, pyx, ite_eq_right hij, smul_zero]
    refine ⟨spinTransvection s22a_Q_nondegenerate (Qy j) huw, fun k => ?_, fun w hw => ?_⟩
    · rw [s22a_rho_spinTransvection, Matrix.SpecialLinearGroup.transvection_coe,
        s22a_sum_transvection, QuadraticMap.polar_smul_right, pxx, QuadraticMap.map_smul, Qx, pxy]
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    · rw [s22a_rho_spinTransvection, i₂ _ hw _ (hy j), QuadraticMap.map_smul, Qx]
      simp only [zero_smul, add_zero, mul_zero, zero_mul, sub_zero]
      exact Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (hy j))
  · -- products
    rintro A B ⟨g, hg, hg'⟩ ⟨g', hh, hh'⟩
    refine ⟨g * g', fun k => ?_, fun w hw => ?_⟩
    · rw [s22a_rho_mul, hh, map_sum]
      simp only [map_smul, hg, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      congr 1
      exact mul_comm _ _
    · rw [s22a_rho_mul]
      exact hg' _ (hh' w hw)

set_option linter.unusedSimpArgs false in
/-- **Lifting `GL(W₁)` with square determinant** ([Igusa, Lemma 1], corrected for `F`-points):
every `M` with `det M = b²`, `b ≠ 0`, is the matrix of `ρ(g)|_{W₁}` for some `g ∈ Spin(V_F)`
preserving `W₂`: `M = M' diag(b², 1, …, 1)` with `M' ∈ SL`, and `diag(b², 1, …, 1)` lifts to
`ι(b⁻¹(x₀ + y₀)) ι(x₀ + b² y₀)`. -/
private theorem s22a_lift_sq (hn : 0 < n) {W₂ : Submodule F (V F n)}
    (i₂ : ∀ a ∈ W₂, ∀ b ∈ W₂, QuadraticMap.polar (Q F n) a b = 0)
    {x y : Fin (2 * n) → V F n} (hy : ∀ i, y i ∈ W₂)
    (ex₂ : ∀ w ∈ W₂, w = ∑ i, QuadraticMap.polar (Q F n) (x i) w • y i)
    (pxy : ∀ a b, QuadraticMap.polar (Q F n) (x a) (y b) = if a = b then 1 else 0)
    (pxx : ∀ a b, QuadraticMap.polar (Q F n) (x a) (x b) = 0)
    (Qx : ∀ a, Q F n (x a) = 0) (Qy : ∀ a, Q F n (y a) = 0)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) F) {b : F} (hb : b ≠ 0) (hM : M.det = b * b) :
    ∃ g : Spin F n, (∀ k, rho F n g (x k) = ∑ l, M l k • x l) ∧
      (∀ w ∈ W₂, rho F n g w ∈ W₂) := by
  have pyx : ∀ a b, QuadraticMap.polar (Q F n) (y a) (x b) = if b = a then 1 else 0 := by
    intro a b
    rw [QuadraticMap.polar_comm, pxy]
  have pyy : ∀ a b, QuadraticMap.polar (Q F n) (y a) (y b) = 0 := fun a b => i₂ _ (hy a) _ (hy b)
  set k₀ : Fin (2 * n) := ⟨0, by omega⟩
  -- the torus element `t = ι(b⁻¹ (x₀ + y₀)) ι(x₀ + b² y₀)`
  have Qp : Q F n (b⁻¹ • (x k₀ + y k₀)) = b⁻¹ * b⁻¹ := by
    rw [QuadraticMap.map_smul, QuadraticMap.map_add (Q F n), Qx, Qy, pxy, ite_eq_left rfl]
    ring
  have Qq : Q F n (x k₀ + (b * b) • y k₀) = b * b := by
    rw [QuadraticMap.map_add (Q F n), Qx, QuadraticMap.map_smul, Qy,
      QuadraticMap.polar_smul_right, pxy, ite_eq_left rfl]
    ring
  have hpq : Q F n (b⁻¹ • (x k₀ + y k₀)) * Q F n (x k₀ + (b * b) • y k₀) = 1 := by
    rw [Qp, Qq]
    field_simp
  set t : Spin F n := ⟨ι (Q F n) (b⁻¹ • (x k₀ + y k₀)) * ι (Q F n) (x k₀ + (b * b) • y k₀),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ hpq⟩ with ht
  have rt : ∀ z, rho F n t z = _ := fun z => s22a_rho_ι_mul_ι _ _ hpq z
  have htx : ∀ k, rho F n t (x k) = (if k = k₀ then b * b else 1) • x k := by
    intro k
    rw [rt, Qp, Qq]
    by_cases hk : k = k₀
    · subst hk
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub]
      simp only [smul_smul]
      match_scalars <;> field_simp <;> ring
    · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hk, Ne.symm hk]
      simp only [smul_smul]
      match_scalars <;> field_simp <;> ring
  have hty : ∀ k, rho F n t (y k) = (if k = k₀ then (b * b)⁻¹ else 1) • y k := by
    intro k
    rw [rt, Qp, Qq]
    by_cases hk : k = k₀
    · subst hk
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub]
      simp only [smul_smul]
      match_scalars <;> field_simp <;> ring
    · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hk, Ne.symm hk]
      simp only [smul_smul]
      match_scalars <;> field_simp <;> ring
  -- `M = M' T` with `T = diag(b², 1, …, 1)` and `M' ∈ SL`.
  set D : Fin (2 * n) → F := fun k => if k = k₀ then b * b else 1 with hD
  set D' : Fin (2 * n) → F := fun k => if k = k₀ then (b * b)⁻¹ else 1 with hD'
  have hDD : Matrix.diagonal D' * Matrix.diagonal D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    simp only [hD, hD']
    split_ifs
    · field_simp
    · ring
  have hdetD' : (Matrix.diagonal D').det = (b * b)⁻¹ := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single k₀]
    · simp [hD']
    · intro k _ hk
      simp [hD', hk]
    · simp
  have hM' : (M * Matrix.diagonal D').det = 1 := by
    rw [Matrix.det_mul, hM, hdetD']
    field_simp
  obtain ⟨g', hg', hg''⟩ := s22a_lift_SL hn i₂ hy ex₂ pxy pxx Qx Qy ⟨M * Matrix.diagonal D', hM'⟩
  refine ⟨g' * t, fun k => ?_, fun w hw => ?_⟩
  · rw [s22a_rho_mul, htx, map_smul, hg']
    simp only [Matrix.mul_diagonal, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    simp only [hD, hD']
    split_ifs
    · field_simp
    · ring
  · rw [s22a_rho_mul]
    apply hg''
    rw [ex₂ w hw, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul, hty]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hy i))

end S22aLift

section S22aLineStab

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- An element of `Spin(V_F)` preserving `ker m_u` stabilizes the line `F u`, when `u` has a
transversal partner `u'` (uniqueness of the spinor with given annihilator, [Chevalley, III.1.4]). -/
theorem s22a_mem_lineStabilizer {u u' : S F n} (hu' : u' ≠ 0)
    (hsup : ann F n u ⊔ ann F n u' = ⊤) (hc : mukai F n u u' ≠ 0) (g : Spin F n)
    (hg : ∀ v ∈ ann F n u, rho F n g v ∈ ann F n u) : g ∈ lineStabilizer F n u := by
  have hmap : (ann F n u).map (rho F n g).toLinearMap = ann F n u := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      exact hg v hv
    · exact LinearEquiv.finrank_map_eq _ _
  have hann : ann F n (m F n (g : C F n) u) = ann F n u := by rw [ann_m_spin, hmap]
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp (s22a_mem_span_of_ann_le hu' hsup hc hann.ge)
  exact ⟨c, hc'.symm⟩

end S22aLineStab

/-! ## Helpers (prover P03): the infinitesimal stabilizer of `a u₁ + b u₂` ([Igusa, Lemma 2])

The paper's Remark 2.2.3 cites [Igusa, Lemma 2] (statements of record `WeilClasses.igusa_lemma2_*`,
not importable here). We prove the facts used through the infinitesimal stabilizer: let
`Λ = span {ι p ι q} ⊆ C(V)` (scalars and `so(V)`), stable under conjugation by `Spin(V)`. For a
transversal pair of even pure spinors and `w = a u₁ + b u₂`, `a, b ≠ 0`, `n ≥ 3`, the joint kernel of
`{ξ ∈ Λ : m_ξ w = 0}` is `F u₁ + F u₂` (`s22a_fix_iff`); it is preserved by the stabilizer of `w`
(`s22a_fix_m_spin`). (With the number operator `N`: `m_ξ uᵢ` decomposes into `N`-eigenvectors of
eigenvalues `2n, 2n - 2` (for `u₁`) and `0, 2` (for `u₂`), distinct for `n ≥ 3`.) -/

section S22aFix

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `Λ = span {ι p ι q} ⊆ C(V_F)`. -/
noncomputable def s22a_Λ (F : Type*) [Field F] [CharZero F] (n : ℕ) : Submodule F (C F n) :=
  Submodule.span F (Set.range fun pq : V F n × V F n => ι (Q F n) pq.1 * ι (Q F n) pq.2)

theorem s22a_ι_mul_ι_mem_Λ (p q : V F n) : ι (Q F n) p * ι (Q F n) q ∈ s22a_Λ F n :=
  Submodule.subset_span ⟨(p, q), rfl⟩

/-- `star g ι v g = ι(ρ(g⁻¹) v)`. -/
theorem s22a_star_ι_mul (g : Spin F n) (v : V F n) :
    star (g : C F n) * ι (Q F n) v * g = ι (Q F n) (rho F n g⁻¹ v) := by
  rw [ι_rho]
  have h1 : ((g⁻¹ : Spin F n) : C F n) = star (g : C F n) := rfl
  rw [h1, star_star]

/-- `Λ` is stable under conjugation by `Spin(V_F)`. -/
theorem s22a_conj_mem_Λ (g : Spin F n) {ξ : C F n} (hξ : ξ ∈ s22a_Λ F n) :
    star (g : C F n) * ξ * g ∈ s22a_Λ F n := by
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hx
    have hg : (g : C F n) * star (g : C F n) = 1 := spinGroup.mul_star_self_of_mem g.2
    have e : star (g : C F n) * (ι (Q F n) p * ι (Q F n) q) * g =
        (star (g : C F n) * ι (Q F n) p * g) * (star (g : C F n) * ι (Q F n) q * g) := by
      calc star (g : C F n) * (ι (Q F n) p * ι (Q F n) q) * g
          = star (g : C F n) * ι (Q F n) p * 1 * ι (Q F n) q * g := by noncomm_ring
        _ = star (g : C F n) * ι (Q F n) p * ((g : C F n) * star (g : C F n)) *
              ι (Q F n) q * g := by rw [hg]
        _ = _ := by noncomm_ring
    rw [e, s22a_star_ι_mul, s22a_star_ι_mul]
    exact s22a_ι_mul_ι_mem_Λ _ _
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- **Equivariance**: the joint kernel of the infinitesimal stabilizer of `w` is preserved by the
stabilizer of `w` in `Spin(V_F)`. -/
theorem s22a_fix_m_spin {w s : S F n}
    (hs : ∀ ξ ∈ s22a_Λ F n, m F n ξ w = 0 → m F n ξ s = 0)
    (g : Spin F n) (hg : m F n (g : C F n) w = w) :
    ∀ ξ ∈ s22a_Λ F n, m F n ξ w = 0 → m F n ξ (m F n (g : C F n) s) = 0 := by
  intro ξ hξ hξw
  have hgs : (g : C F n) * star (g : C F n) = 1 := spinGroup.mul_star_self_of_mem g.2
  have h1 : m F n (star (g : C F n) * ξ * g) w = 0 := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg, hξw, map_zero]
  have h2 := hs _ (s22a_conj_mem_Λ g hξ) h1
  have e : ξ * g = (g : C F n) * (star (g : C F n) * ξ * g) := by
    rw [← mul_assoc, ← mul_assoc, hgs, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h2, map_zero]

omit [CharZero F] in
/-- Separation of eigenvectors for four distinct eigenvalues. -/
theorem s22a_eigen_first {M : Type*} [AddCommGroup M] [Module F M] (N : M →ₗ[F] M)
    {z₁ z₂ z₃ z₄ : M} {l₁ l₂ l₃ l₄ : F} (h₁ : N z₁ = l₁ • z₁) (h₂ : N z₂ = l₂ • z₂)
    (h₃ : N z₃ = l₃ • z₃) (h₄ : N z₄ = l₄ • z₄) (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃) (h14 : l₁ ≠ l₄)
    (hs : z₁ + z₂ + z₃ + z₄ = 0) : z₁ = 0 := by
  -- apply `(N - l₄)`, then `(N - l₃)`, then `(N - l₂)`
  have e1 : (l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃ = 0 := by
    have := congrArg N hs
    rw [map_add, map_add, map_add, h₁, h₂, h₃, h₄, map_zero] at this
    calc (l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃
        = (l₁ • z₁ + l₂ • z₂ + l₃ • z₃ + l₄ • z₄) - l₄ • (z₁ + z₂ + z₃ + z₄) := by module
      _ = 0 := by rw [this, hs, smul_zero, sub_zero]
  have e2 : ((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂ = 0 := by
    have := congrArg N e1
    rw [map_add, map_add, map_smul, map_smul, map_smul, h₁, h₂, h₃, map_zero] at this
    calc ((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂
        = ((l₁ - l₄) • l₁ • z₁ + (l₂ - l₄) • l₂ • z₂ + (l₃ - l₄) • l₃ • z₃) -
          l₃ • ((l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃) := by module
      _ = 0 := by rw [this, e1, smul_zero, sub_zero]
  have e3 : ((l₁ - l₄) * (l₁ - l₃) * (l₁ - l₂)) • z₁ = 0 := by
    have := congrArg N e2
    rw [map_add, map_smul, map_smul, h₁, h₂, map_zero] at this
    calc ((l₁ - l₄) * (l₁ - l₃) * (l₁ - l₂)) • z₁
        = (((l₁ - l₄) * (l₁ - l₃)) • l₁ • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • l₂ • z₂) -
          l₂ • (((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂) := by module
      _ = 0 := by rw [this, e2, smul_zero, sub_zero]
  refine (smul_eq_zero.mp e3).resolve_left ?_
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h14) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h12)

/-- The number operator `N = Σ m_{xᵢ} m_{yᵢ}` of dual bases, as an endomorphism of `S`. -/
theorem s22a_numOp_apply (x y : Fin (2 * n) → V F n) (r : S F n) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r =
      ∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) r) := by
  rw [LinearMap.sum_apply]
  rfl

theorem s22a_numOp_u₁ {u₁ : S F n} {x y : Fin (2 * n) → V F n} (hx : ∀ i, x i ∈ ann F n u₁)
    (hxy : ∀ i j, pairing F n (x i) (y j) = if i = j then 1 else 0) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) u₁ = (2 * n : F) • u₁ := by
  have h1 : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₁) = u₁ := by
    intro i
    rw [s22a_m_swap (y i) (x i), show m F n (ι (Q F n) (x i)) u₁ = 0 from hx i, map_zero,
      sub_zero, s22a_pairing_comm, hxy]
    simp
  rw [s22a_numOp_apply]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul F]
  push_cast
  rfl

theorem s22a_numOp_u₂ {u₂ : S F n} {x y : Fin (2 * n) → V F n} (hy : ∀ i, y i ∈ ann F n u₂) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) u₂ = 0 := by
  rw [s22a_numOp_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show m F n (ι (Q F n) (y i)) u₂ = 0 from hy i, map_zero]

/-- For `ξ ∈ Λ`: `m_ξ u₁ = c₁ u₁ + r₁` with `N r₁ = (2n - 2) r₁`, and `m_ξ u₂ = c₂ u₂ + r₂` with
`N r₂ = 2 r₂` (`N` the number operator of dual bases of `W₁ = ker m_{u₁}`, `W₂ = ker m_{u₂}`). -/
theorem s22a_decomp {u₁ u₂ : S F n} {x y : Fin (2 * n) → V F n}
    (hx : ∀ i, x i ∈ ann F n u₁) (hy : ∀ i, y i ∈ ann F n u₂)
    (hxy : ∀ i j, pairing F n (x i) (y j) = if i = j then 1 else 0)
    (ex₁ : ∀ v ∈ ann F n u₁, v = ∑ i, pairing F n v (y i) • x i)
    (ex₂ : ∀ w ∈ ann F n u₂, w = ∑ i, pairing F n (x i) w • y i)
    (i₁ : ∀ a ∈ ann F n u₁, ∀ b ∈ ann F n u₁, pairing F n a b = 0)
    (i₂ : ∀ a ∈ ann F n u₂, ∀ b ∈ ann F n u₂, pairing F n a b = 0)
    (hsup : ann F n u₁ ⊔ ann F n u₂ = ⊤) {ξ : C F n} (hξ : ξ ∈ s22a_Λ F n) :
    ∃ (c₁ c₂ : F) (r₁ r₂ : S F n), m F n ξ u₁ = c₁ • u₁ + r₁ ∧
      (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r₁ = ((2 * n : F) - 2) • r₁ ∧
      m F n ξ u₂ = c₂ • u₂ + r₂ ∧
      (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r₂ = (2 : F) • r₂ := by
  set N : Module.End F (S F n) := ∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))
    with hN
  have hN₁ : ∀ {v : V F n}, v ∈ ann F n u₁ → ∀ r : S F n,
      N (m F n (ι (Q F n) v) r) = m F n (ι (Q F n) v) (N r) + m F n (ι (Q F n) v) r := by
    intro v hv r
    rw [hN, s22a_numOp_apply, s22a_numOp_apply]
    exact s22a_numOp_W₁ i₁ hx ex₁ hv r
  have hN₂ : ∀ {v : V F n}, v ∈ ann F n u₂ → ∀ r : S F n,
      N (m F n (ι (Q F n) v) r) = m F n (ι (Q F n) v) (N r) - m F n (ι (Q F n) v) r := by
    intro v hv r
    rw [hN, s22a_numOp_apply, s22a_numOp_apply]
    exact s22a_numOp_W₂ i₂ hy ex₂ hv r
  have hNu₁ : N u₁ = (2 * n : F) • u₁ := s22a_numOp_u₁ hx hxy
  have hNu₂ : N u₂ = 0 := s22a_numOp_u₂ hy
  induction hξ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hz
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := p))
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := q))
    have hq₁u : m F n (ι (Q F n) q₁) u₁ = 0 := hq₁
    have hq₂u : m F n (ι (Q F n) q₂) u₂ = 0 := hq₂
    have hp₁u : m F n (ι (Q F n) p₁) u₁ = 0 := hp₁
    have hp₂u : m F n (ι (Q F n) p₂) u₂ = 0 := hp₂
    refine ⟨pairing F n q₂ p₁, pairing F n q₁ p₂,
      m F n (ι (Q F n) p₂) (m F n (ι (Q F n) q₂) u₁),
      m F n (ι (Q F n) p₁) (m F n (ι (Q F n) q₁) u₂), ?_, ?_, ?_, ?_⟩
    · simp only [map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply, hq₁u, zero_add]
      rw [s22a_m_swap q₂ p₁, hp₁u, map_zero, sub_zero]
    · rw [hN₂ hp₂, hN₂ hq₂, hNu₁, map_sub, map_smul, map_smul]
      module
    · simp only [map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply, hq₂u, add_zero]
      rw [s22a_m_swap q₁ p₂, hp₂u, map_zero, sub_zero, add_comm]
    · rw [hN₁ hp₁, hN₁ hq₁, hNu₂, map_zero, zero_add]
      module
  | zero =>
    exact ⟨0, 0, 0, 0, by simp, by simp, by simp, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := hz
    obtain ⟨c₁', c₂', r₁', r₂', e₁', f₁', e₂', f₂'⟩ := hz'
    refine ⟨c₁ + c₁', c₂ + c₂', r₁ + r₁', r₂ + r₂', ?_, ?_, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, e₁, e₁', add_smul]; abel
    · rw [map_add, f₁, f₁', smul_add]
    · rw [map_add, LinearMap.add_apply, e₂, e₂', add_smul]; abel
    · rw [map_add, f₂, f₂', smul_add]
  | smul c z _ hz =>
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := hz
    refine ⟨c * c₁, c * c₂, c • r₁, c • r₂, ?_, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, e₁, smul_add, smul_smul]
    · rw [map_smul, f₁, smul_comm]
    · rw [map_smul, LinearMap.smul_apply, e₂, smul_add, smul_smul]
    · rw [map_smul, f₂, smul_comm]

theorem s22a_m_swap0 {v w : V F n} (h : pairing F n v w = 0) (s : S F n) :
    m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) = -m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) := by
  rw [s22a_m_swap, h, zero_smul, zero_sub]

theorem s22a_m_sq (v : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) v) s) = Q F n v • s := by
  rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]

/-- **The joint kernel of the infinitesimal stabilizer of `w = a u₁ + b u₂`** (`n ≥ 3`, `a, b ≠ 0`,
`u₁, u₂` a transversal pair of even pure spinors) is `F u₁ + F u₂`. -/
theorem s22a_fix_iff (hn : 3 ≤ n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (s : S F n) :
    (∀ ξ ∈ s22a_Λ F n, m F n ξ (a • u₁ + b • u₂) = 0 → m F n ξ s = 0) ↔
      s ∈ Submodule.span F {u₁, u₂} := by
  have hn0 : 0 < n := by omega
  have hu₁ : u₁ ≠ 0 := IsEvenPureSpinor.ne_zero hn0 h₁
  have hu₂ : u₂ ≠ 0 := IsEvenPureSpinor.ne_zero hn0 h₂
  have i₁ : ∀ a ∈ ann F n u₁, ∀ b ∈ ann F n u₁, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₁ ha hb
  have i₂ : ∀ a ∈ ann F n u₂, ∀ b ∈ ann F n u₂, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₂ ha hb
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (ann F n u₁) (ann F n u₂)
  rw [hW, finrank_bot, h₁.2.2, h₂.2.2, add_zero] at h3
  have hsup : ann F n u₁ ⊔ ann F n u₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h3, s22a_finrank_V]
  have hC : IsCompl (ann F n u₁) (ann F n u₂) := ⟨disjoint_iff.mpr hW, codisjoint_iff.mpr hsup⟩
  obtain ⟨x, y, hx, hy, hxy, ex₁, ex₂⟩ := s22a_dual_bases i₂ h₁.2.2 h₂.2.2 hC
  have hc₁₂ : mukai F n u₁ u₂ ≠ 0 := s22a_mukai_ne_zero_of_sup_eq_top hu₁ hu₂ hsup
  have hc₂₁ : mukai F n u₂ u₁ ≠ 0 :=
    s22a_mukai_ne_zero_of_sup_eq_top hu₂ hu₁ (by rw [sup_comm]; exact hsup)
  set N : Module.End F (S F n) := ∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i)) with hN
  have hNu₁ : N u₁ = (2 * n : F) • u₁ := s22a_numOp_u₁ hx hxy
  have hNu₂ : N u₂ = 0 := s22a_numOp_u₂ hy
  have hn1 : (n : F) ≠ 1 := by exact_mod_cast (show n ≠ 1 by omega)
  have hn2 : (n : F) ≠ 2 := by exact_mod_cast (show n ≠ 2 by omega)
  have hn0' : (n : F) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  -- Elements of the infinitesimal stabilizer of `w` kill `u₁` and `u₂`.
  have hkill : ∀ ξ ∈ s22a_Λ F n, m F n ξ (a • u₁ + b • u₂) = 0 →
      m F n ξ u₁ = 0 ∧ m F n ξ u₂ = 0 := by
    intro ξ hξ hw
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := s22a_decomp hx hy hxy ex₁ ex₂ i₁ i₂ hsup hξ
    rw [map_add, map_smul, map_smul, e₁, e₂] at hw
    have hs4 : (a * c₁) • u₁ + a • r₁ + (b * c₂) • u₂ + b • r₂ = 0 := by
      rw [← hw]
      module
    have g₁ : N ((a * c₁) • u₁) = (2 * n : F) • ((a * c₁) • u₁) := by
      rw [map_smul, hNu₁, smul_comm]
    have g₂ : N (a • r₁) = ((2 * n : F) - 2) • (a • r₁) := by
      rw [map_smul, f₁, smul_comm]
    have g₃ : N ((b * c₂) • u₂) = (0 : F) • ((b * c₂) • u₂) := by
      rw [map_smul, hNu₂, smul_zero, zero_smul]
    have g₄ : N (b • r₂) = (2 : F) • (b • r₂) := by
      rw [map_smul, f₂, smul_comm]
    have d12 : (2 * n : F) ≠ 2 * n - 2 := by
      intro h
      exact two_ne_zero (by linear_combination h : (2 : F) = 0)
    have d13 : (2 * n : F) ≠ 0 := mul_ne_zero two_ne_zero hn0'
    have d14 : (2 * n : F) ≠ 2 := fun h => hn1 (by linear_combination h / 2)
    have d23 : (2 * n : F) - 2 ≠ 0 := fun h => hn1 (by linear_combination h / 2)
    have d24 : (2 * n : F) - 2 ≠ 2 := fun h => hn2 (by linear_combination h / 2)
    have d34 : (0 : F) ≠ 2 := two_ne_zero.symm
    have z₁ := s22a_eigen_first N g₁ g₂ g₃ g₄ d12 d13 d14 hs4
    have z₂ := s22a_eigen_first N g₂ g₁ g₃ g₄ d12.symm d23 d24 (by rw [← hs4]; abel)
    have z₃ := s22a_eigen_first N g₃ g₁ g₂ g₄ d13.symm d23.symm d34 (by rw [← hs4]; abel)
    have z₄ := s22a_eigen_first N g₄ g₁ g₂ g₃ d14.symm d24.symm d34.symm (by rw [← hs4]; abel)
    have hc₁ : c₁ = 0 := by
      rcases smul_eq_zero.mp z₁ with h | h
      · exact (mul_eq_zero.mp h).resolve_left ha
      · exact absurd h hu₁
    have hc₂ : c₂ = 0 := by
      rcases smul_eq_zero.mp z₃ with h | h
      · exact (mul_eq_zero.mp h).resolve_left hb
      · exact absurd h hu₂
    have hr₁ : r₁ = 0 := (smul_eq_zero.mp z₂).resolve_left ha
    have hr₂ : r₂ = 0 := (smul_eq_zero.mp z₄).resolve_left hb
    exact ⟨by rw [e₁, hc₁, hr₁, zero_smul, add_zero], by rw [e₂, hc₂, hr₂, zero_smul, add_zero]⟩
  constructor
  · intro hs
    have hQx : ∀ i, Q F n (x i) = 0 := fun i => s22a_Q_of_mem_ann hu₁ (hx i)
    have hQy : ∀ i, Q F n (y i) = 0 := fun i => s22a_Q_of_mem_ann hu₂ (hy i)
    -- `nᵢ = m_{xᵢ} m_{yᵢ}`: commuting idempotents, `nᵢ u₁ = u₁`, `nᵢ u₂ = 0`.
    have hn_u₁ : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₁) = u₁ := by
      intro i
      rw [s22a_m_swap (y i) (x i), show m F n (ι (Q F n) (x i)) u₁ = 0 from hx i, map_zero,
        sub_zero, s22a_pairing_comm, hxy]
      simp
    have hn_u₂ : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₂) = 0 := by
      intro i
      rw [show m F n (ι (Q F n) (y i)) u₂ = 0 from hy i, map_zero]
    have hyfix : ∀ i z, m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z)) = m F n (ι (Q F n) (y i)) z := by
      intro i z
      rw [s22a_m_swap (x i) (y i), hxy, ite_eq_left rfl, one_smul, s22a_m_sq, hQy, zero_smul,
        map_zero, sub_zero]
    have hxkill : ∀ i z, m F n (ι (Q F n) (x i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z)) = 0 := by
      intro i z
      rw [s22a_m_sq, hQx, zero_smul]
    have hidem : ∀ i z, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z))) =
          m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z) := by
      intro i z
      rw [hyfix]
    have hcomm : ∀ i j z, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j)) z))) =
          m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j))
            (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z))) := by
      intro i j z
      by_cases hij : i = j
      · subst hij; rfl
      have p1 : pairing F n (x j) (y i) = 0 := by rw [hxy, ite_eq_right (Ne.symm hij)]
      have p2 : pairing F n (x j) (x i) = 0 := i₁ _ (hx j) _ (hx i)
      have p3 : pairing F n (y j) (y i) = 0 := i₂ _ (hy j) _ (hy i)
      have p4 : pairing F n (y j) (x i) = 0 := by rw [s22a_pairing_comm, hxy, ite_eq_right hij]
      rw [s22a_m_swap0 p1, map_neg, s22a_m_swap0 p2, neg_neg, s22a_m_swap0 p3, map_neg, map_neg,
        s22a_m_swap0 p4, map_neg, neg_neg]
    -- `s ∈ Fix` forces `nᵢ s = nⱼ s`.
    have heq : ∀ i j, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s) =
        m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j)) s) := by
      intro i j
      have hξ : ι (Q F n) (x i) * ι (Q F n) (y i) - ι (Q F n) (x j) * ι (Q F n) (y j) ∈
          s22a_Λ F n := Submodule.sub_mem _ (s22a_ι_mul_ι_mem_Λ _ _) (s22a_ι_mul_ι_mem_Λ _ _)
      have hw : m F n (ι (Q F n) (x i) * ι (Q F n) (y i) - ι (Q F n) (x j) * ι (Q F n) (y j))
          (a • u₁ + b • u₂) = 0 := by
        simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, map_add,
          map_smul, hn_u₁, hn_u₂, smul_zero, add_zero, sub_self]
      have := hs _ hξ hw
      simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply] at this
      exact sub_eq_zero.mp this
    set k₀ : Fin (2 * n) := ⟨0, by omega⟩
    set t := m F n (ι (Q F n) (x k₀)) (m F n (ι (Q F n) (y k₀)) s) with ht_def
    have ht : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) t) = t := by
      intro i
      rw [ht_def, hcomm, heq i k₀, hidem]
    have hst : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (s - t)) = 0 := by
      intro i
      rw [map_sub, map_sub, ht, heq i k₀, ← ht_def, sub_self]
    have ht₁ : t ∈ F ∙ u₁ := by
      refine s22a_mem_span_of_ann_le hu₂ hsup hc₁₂ fun v hv => ?_
      rw [s22a_mem_ann, ex₁ v hv, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, ← ht i, hxkill, smul_zero]
    have ht₂ : s - t ∈ F ∙ u₂ := by
      refine s22a_mem_span_of_ann_le hu₁ (by rw [sup_comm]; exact hsup) hc₂₁ fun w hw => ?_
      rw [s22a_mem_ann, ex₂ w hw, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, ← hyfix, hst, map_zero, smul_zero]
    have hle₁ : (F ∙ u₁) ≤ Submodule.span F {u₁, u₂} :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    have hle₂ : (F ∙ u₂) ≤ Submodule.span F {u₁, u₂} :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have h12 := Submodule.add_mem _ (hle₁ ht₁) (hle₂ ht₂)
    rwa [add_sub_cancel] at h12
  · intro hs ξ hξ hw
    obtain ⟨k₁, k₂, rfl⟩ := Submodule.mem_span_pair.mp hs
    obtain ⟨h1, h2⟩ := hkill ξ hξ hw
    rw [map_add, map_smul, map_smul, h1, h2, smul_zero, smul_zero, add_zero]

/-- Even elements of `C(V_F)` preserve `S⁺`. -/
theorem s22a_m_even_mem_Splus {g : C F n} (hg : g ∈ evenOdd (Q F n) 0) {s : S F n}
    (hs : s ∈ Splus F n) : m F n g s ∈ Splus F n := by
  induction g, hg using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_zero, pow_zero] at hv
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hv
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ r hs
  | add x y hx hy ihx ihy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact m_mem_Splus_of_odd F n _ (CliffordAlgebra.ι_mem_evenOdd_one _ _) _
      (m_mem_Sminus_of_odd F n _ (CliffordAlgebra.ι_mem_evenOdd_one _ _) _ ih)

/-- `Spin(V_F)` maps even pure spinors to even pure spinors. -/
theorem s22a_pure_m_spin {u : S F n} (hu : IsEvenPureSpinor F n u) (g : Spin F n) :
    IsEvenPureSpinor F n (m F n (g : C F n) u) := by
  refine ⟨s22a_m_even_mem_Splus ?_ hu.1, ?_, ?_⟩
  · rw [← CliffordAlgebra.even_toSubmodule]
    exact spinGroup.mem_even g.2
  · intro v hv
    rw [ann_m_spin] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    show Q F n (rho F n g v') = 0
    rw [show rho F n g v' = spinVectorAction (Q F n) g v' from rfl, spinVectorAction_map_app]
    exact hu.2.1 v' hv'
  · rw [ann_m_spin, LinearEquiv.finrank_map_eq]
    exact hu.2.2

end S22aFix

/-! ## Helpers (prover P03): an element of `Spin(V)` exchanging `W₁` and `W₂`

For dual bases `x` of `W₁`, `y` of `W₂`, the element `ι(x_p + y_p) ι(x_q + y_q)` (two reflections)
maps `x_p ↦ -y_p`, `x_q ↦ -y_q`, `y_p ↦ -x_p`, `y_q ↦ -x_q` and fixes the other basis vectors; the
product over the pairs `(2k, 2k+1)` exchanges `W₁` and `W₂`. -/

section S22aSwap

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

set_option linter.unusedSimpArgs false in
private theorem s22a_rho_pair {x y : Fin (2 * n) → V F n}
    (pxy : ∀ a b, QuadraticMap.polar (Q F n) (x a) (y b) = if a = b then 1 else 0)
    (pxx : ∀ a b, QuadraticMap.polar (Q F n) (x a) (x b) = 0)
    (pyy : ∀ a b, QuadraticMap.polar (Q F n) (y a) (y b) = 0)
    (Qx : ∀ a, Q F n (x a) = 0) (Qy : ∀ a, Q F n (y a) = 0) {p q : Fin (2 * n)} (hpq : p ≠ q) :
    ∃ E : Spin F n,
      (∀ l, rho F n E (x l) = if l = p then -y p else if l = q then -y q else x l) ∧
      (∀ l, rho F n E (y l) = if l = p then -x p else if l = q then -x q else y l) := by
  have pyx : ∀ a b, QuadraticMap.polar (Q F n) (y a) (x b) = if b = a then 1 else 0 := by
    intro a b
    rw [QuadraticMap.polar_comm, pxy]
  have Qa : ∀ k, Q F n (x k + y k) = 1 := by
    intro k
    rw [QuadraticMap.map_add (Q F n), Qx, Qy, pxy, ite_eq_left rfl, zero_add, zero_add]
  have h₁ : Q F n (x p + y p) * Q F n (x q + y q) = 1 := by rw [Qa, Qa, one_mul]
  have hqp : q ≠ p := Ne.symm hpq
  refine ⟨⟨ι (Q F n) (x p + y p) * ι (Q F n) (x q + y q),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ h₁⟩, fun l => ?_, fun l => ?_⟩
  · rw [s22a_rho_ι_mul_ι _ _ h₁, Qa, Qa]
    by_cases hlp : l = p
    · subst hlp
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp]
      module
    · by_cases hlq : l = q
      · subst hlq
        simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp, hlp, Ne.symm hlp]
        module
      · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp, hlp, Ne.symm hlp, hlq, Ne.symm hlq]
        module
  · rw [s22a_rho_ι_mul_ι _ _ h₁, Qa, Qa]
    by_cases hlp : l = p
    · subst hlp
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp]
      module
    · by_cases hlq : l = q
      · subst hlq
        simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp, hlp, Ne.symm hlp]
        module
      · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, pxy, pyx, pxx, pyy, Qx, Qy,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, sub_zero, ↓reduceIte, zero_mul,
          one_mul, zero_sub, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, smul_add, smul_sub, hpq, hqp, hlp, Ne.symm hlp, hlq, Ne.symm hlq]
        module

/-- The product of the first `k` pair elements maps `x_l ↦ -y_l`, `y_l ↦ -x_l` for `l < 2k` and
fixes the other basis vectors. -/
private theorem s22a_swap_aux {x y : Fin (2 * n) → V F n}
    (pxy : ∀ a b, QuadraticMap.polar (Q F n) (x a) (y b) = if a = b then 1 else 0)
    (pxx : ∀ a b, QuadraticMap.polar (Q F n) (x a) (x b) = 0)
    (pyy : ∀ a b, QuadraticMap.polar (Q F n) (y a) (y b) = 0)
    (Qx : ∀ a, Q F n (x a) = 0) (Qy : ∀ a, Q F n (y a) = 0) :
    ∀ k ≤ n, ∃ g : Spin F n,
      (∀ l : Fin (2 * n), rho F n g (x l) = if (l : ℕ) < 2 * k then -y l else x l) ∧
      (∀ l : Fin (2 * n), rho F n g (y l) = if (l : ℕ) < 2 * k then -x l else y l) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, fun l => by simp [s22a_rho_one], fun l => by simp [s22a_rho_one]⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, hgx, hgy⟩ := ih (by omega)
    set p : Fin (2 * n) := ⟨2 * k, by omega⟩ with hp
    set q : Fin (2 * n) := ⟨2 * k + 1, by omega⟩ with hq
    have hpq : p ≠ q := by
      intro h
      have := congrArg Fin.val h
      simp [hp, hq] at this
    obtain ⟨E, hEx, hEy⟩ := s22a_rho_pair pxy pxx pyy Qx Qy hpq
    refine ⟨g * E, fun l => ?_, fun l => ?_⟩
    · rw [s22a_rho_mul, hEx]
      by_cases hlp : l = p
      · subst hlp
        rw [ite_eq_left rfl, map_neg, hgy]
        have h1 : ¬ ((p : ℕ) < 2 * k) := by rw [hp]; show ¬ (2 * k < 2 * k); omega
        have h2 : (p : ℕ) < 2 * (k + 1) := by rw [hp]; show 2 * k < 2 * (k + 1); omega
        rw [ite_eq_right h1, ite_eq_left h2]
      · by_cases hlq : l = q
        · subst hlq
          rw [ite_eq_right (Ne.symm hpq), ite_eq_left rfl, map_neg, hgy]
          have h1 : ¬ ((q : ℕ) < 2 * k) := by rw [hq]; show ¬ (2 * k + 1 < 2 * k); omega
          have h2 : (q : ℕ) < 2 * (k + 1) := by rw [hq]; show 2 * k + 1 < 2 * (k + 1); omega
          rw [ite_eq_right h1, ite_eq_left h2]
        · rw [ite_eq_right hlp, ite_eq_right hlq, hgx]
          have h1 : (l : ℕ) ≠ 2 * k := fun h => hlp (Fin.ext (by simp [hp, h]))
          have h2 : (l : ℕ) ≠ 2 * k + 1 := fun h => hlq (Fin.ext (by simp [hq, h]))
          have h3 : ((l : ℕ) < 2 * k ↔ (l : ℕ) < 2 * (k + 1)) := by omega
          by_cases h4 : (l : ℕ) < 2 * k
          · rw [ite_eq_left h4, ite_eq_left (h3.mp h4)]
          · rw [ite_eq_right h4, ite_eq_right (fun h => h4 (h3.mpr h))]
    · rw [s22a_rho_mul, hEy]
      by_cases hlp : l = p
      · subst hlp
        rw [ite_eq_left rfl, map_neg, hgx]
        have h1 : ¬ ((p : ℕ) < 2 * k) := by rw [hp]; show ¬ (2 * k < 2 * k); omega
        have h2 : (p : ℕ) < 2 * (k + 1) := by rw [hp]; show 2 * k < 2 * (k + 1); omega
        rw [ite_eq_right h1, ite_eq_left h2]
      · by_cases hlq : l = q
        · subst hlq
          rw [ite_eq_right (Ne.symm hpq), ite_eq_left rfl, map_neg, hgx]
          have h1 : ¬ ((q : ℕ) < 2 * k) := by rw [hq]; show ¬ (2 * k + 1 < 2 * k); omega
          have h2 : (q : ℕ) < 2 * (k + 1) := by rw [hq]; show 2 * k + 1 < 2 * (k + 1); omega
          rw [ite_eq_right h1, ite_eq_left h2]
        · rw [ite_eq_right hlp, ite_eq_right hlq, hgy]
          have h1 : (l : ℕ) ≠ 2 * k := fun h => hlp (Fin.ext (by simp [hp, h]))
          have h2 : (l : ℕ) ≠ 2 * k + 1 := fun h => hlq (Fin.ext (by simp [hq, h]))
          have h3 : ((l : ℕ) < 2 * k ↔ (l : ℕ) < 2 * (k + 1)) := by omega
          by_cases h4 : (l : ℕ) < 2 * k
          · rw [ite_eq_left h4, ite_eq_left (h3.mp h4)]
          · rw [ite_eq_right h4, ite_eq_right (fun h => h4 (h3.mpr h))]

/-- An element of `Spin(V_F)` exchanging `x_l ↔ -y_l` for all `l`. -/
theorem s22a_exists_exchange {x y : Fin (2 * n) → V F n}
    (pxy : ∀ a b, QuadraticMap.polar (Q F n) (x a) (y b) = if a = b then 1 else 0)
    (pxx : ∀ a b, QuadraticMap.polar (Q F n) (x a) (x b) = 0)
    (pyy : ∀ a b, QuadraticMap.polar (Q F n) (y a) (y b) = 0)
    (Qx : ∀ a, Q F n (x a) = 0) (Qy : ∀ a, Q F n (y a) = 0) :
    ∃ g : Spin F n, (∀ l, rho F n g (x l) = -y l) ∧ (∀ l, rho F n g (y l) = -x l) := by
  obtain ⟨g, hgx, hgy⟩ := s22a_swap_aux pxy pxx pyy Qx Qy n le_rfl
  exact ⟨g, fun l => by rw [hgx, ite_eq_left l.2], fun l => by rw [hgy, ite_eq_left l.2]⟩

/-- The torus element `ι(t⁻¹(x₀ + y₀)) ι(x₀ + t² y₀)` acts on `u₁` by `t` and on `u₂` by `t⁻¹`. -/
theorem s22a_exists_torus {u₁ u₂ : S F n} {x₀ y₀ : V F n} (hx₀ : x₀ ∈ ann F n u₁)
    (hy₀ : y₀ ∈ ann F n u₂) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hxy : pairing F n x₀ y₀ = 1)
    {t : F} (ht : t ≠ 0) :
    ∃ h : Spin F n, m F n (h : C F n) u₁ = t • u₁ ∧ m F n (h : C F n) u₂ = t⁻¹ • u₂ := by
  have Qx : Q F n x₀ = 0 := s22a_Q_of_mem_ann hu₁ hx₀
  have Qy : Q F n y₀ = 0 := s22a_Q_of_mem_ann hu₂ hy₀
  have pxy : QuadraticMap.polar (Q F n) x₀ y₀ = 1 := by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact hxy
  have Qp : Q F n (t⁻¹ • (x₀ + y₀)) = t⁻¹ * t⁻¹ := by
    rw [QuadraticMap.map_smul, QuadraticMap.map_add (Q F n), Qx, Qy, pxy]
    ring
  have Qq : Q F n (x₀ + (t * t) • y₀) = t * t := by
    rw [QuadraticMap.map_add (Q F n), Qx, QuadraticMap.map_smul, Qy, QuadraticMap.polar_smul_right,
      pxy]
    ring
  have hpq : Q F n (t⁻¹ • (x₀ + y₀)) * Q F n (x₀ + (t * t) • y₀) = 1 := by
    rw [Qp, Qq]
    field_simp
  have hx₀u : m F n (ι (Q F n) x₀) u₁ = 0 := hx₀
  have hy₀u : m F n (ι (Q F n) y₀) u₂ = 0 := hy₀
  have e1 : m F n (ι (Q F n) x₀) (m F n (ι (Q F n) y₀) u₁) = u₁ := by
    rw [s22a_m_swap y₀ x₀, hx₀u, map_zero, sub_zero, s22a_pairing_comm, hxy, one_smul]
  have e2 : m F n (ι (Q F n) y₀) (m F n (ι (Q F n) x₀) u₂) = u₂ := by
    rw [s22a_m_swap x₀ y₀, hy₀u, map_zero, sub_zero, hxy, one_smul]
  have sqx : ∀ z, m F n (ι (Q F n) x₀) (m F n (ι (Q F n) x₀) z) = 0 := by
    intro z
    rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, Qx, map_zero, map_zero, LinearMap.zero_apply]
  have sqy : ∀ z, m F n (ι (Q F n) y₀) (m F n (ι (Q F n) y₀) z) = 0 := by
    intro z
    rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, Qy, map_zero, map_zero, LinearMap.zero_apply]
  refine ⟨⟨ι (Q F n) (t⁻¹ • (x₀ + y₀)) * ι (Q F n) (x₀ + (t * t) • y₀),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ hpq⟩, ?_, ?_⟩
  · show m F n (ι (Q F n) (t⁻¹ • (x₀ + y₀)) * ι (Q F n) (x₀ + (t * t) • y₀)) u₁ = t • u₁
    simp only [map_mul, map_add, map_smul, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, hx₀u, smul_add, zero_add, e1, sqy, smul_zero, add_zero, smul_smul]
    congr 1
    field_simp
  · show m F n (ι (Q F n) (t⁻¹ • (x₀ + y₀)) * ι (Q F n) (x₀ + (t * t) • y₀)) u₂ = t⁻¹ • u₂
    simp only [map_mul, map_add, map_smul, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, hy₀u, smul_zero, add_zero, e2, sqx, zero_add, smul_add]

end S22aSwap

section General

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The stabilizer of the line `[u]` preserves `ker m_u` (by `WeilClasses.ann_m_spin`). -/
theorem rho_mem_ann_of_mem_lineStabilizer (u : S F n) (g : Spin F n)
    (hg : g ∈ lineStabilizer F n u) (v : V F n) (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n u := by
  obtain ⟨c, hc⟩ := (lineStabilizer F n u).inv_mem hg
  simp only [ann, LinearMap.mem_ker, mOf, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply] at hv ⊢
  rw [ι_rho, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hs : star (g : C F n) = ((g⁻¹ : Spin F n) : C F n) := rfl
  rw [hs, hc, map_smul, hv, smul_zero, map_zero]

/-- The action `Spin(V_F)_{[u]} → End(ker m_u)` of the stabilizer of the line `[u]` on the isotropic
subspace `W = ker m_u`, by restriction of `ρ`. -/
noncomputable def annRestrict (u : S F n) : lineStabilizer F n u →* Module.End F (ann F n u) where
  toFun g := (rho F n (g : Spin F n)).toLinearMap.restrict
    (rho_mem_ann_of_mem_lineStabilizer F n u g g.2)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, OneMemClass.coe_one, LinearEquiv.coe_coe, s22a_rho_one,
      Module.End.one_apply]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Subgroup.coe_mul, LinearEquiv.coe_coe, s22a_rho_mul,
      Module.End.mul_apply]

/-- The homomorphism `Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def pairRestrict (u₁ u₂ : S F n) :
    (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)) →*
      (Module.End F (ann F n u₁))ˣ :=
  ((annRestrict F n u₁).comp (Subgroup.inclusion inf_le_left)).toHomUnits

/-- `SL(W)`: the automorphisms of determinant one, as a subgroup of `GL(W) = (End W)ˣ`. -/
noncomputable def specialLinearUnits (W : Type*) [AddCommGroup W] [Module F W] :
    Subgroup (Module.End F W)ˣ :=
  (Units.map (LinearMap.det : Module.End F W →* F)).ker

end General

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- The homomorphism `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}` (§2.2). -/
noncomputable def restrictW₁ : P.spinL₁L₂ →* (Module.End (Kd d) P.W₁)ˣ :=
  pairRestrict (Kd d) n P.u₁ P.u₂

/-- `det₁` is the determinant of `restrictW₁`. -/
theorem det_restrictW₁ (g : P.spinL₁L₂) :
    LinearMap.det ((P.restrictW₁ g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) =
      P.det₁ g :=
  rfl

/-- The pairing of `V_K` identifies `W₂` with `W₁*`: `y ↦ (x ↦ (x, y)_V)` (§2.2). -/
noncomputable def pairingW₂ : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁ :=
  ((pairing (Kd d) n).compl₁₂ P.W₁.subtype P.W₂.subtype).flip

theorem s22a_restrictW₁_apply (g : P.spinL₁L₂) (x : P.W₁) :
    (((P.restrictW₁ g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) x : V (Kd d) n) =
      rho (Kd d) n g x := rfl

theorem s22a_restrictW₁_inv_apply (g : P.spinL₁L₂) (x : P.W₁) :
    ((((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) x :
        V (Kd d) n) = rho (Kd d) n ((g : Spin (Kd d) n)⁻¹) x := by
  rw [← map_inv]
  rfl

theorem s22a_pairingW₂_apply (y : P.W₂) (x : P.W₁) :
    P.pairingW₂ y x = pairing (Kd d) n (x : V (Kd d) n) (y : V (Kd d) n) := rfl

/-- `W₁`, `W₂` are isotropic for `(·,·)_V`. -/
theorem s22a_pairing_W₁ {x x' : V (Kd d) n} (hx : x ∈ P.W₁) (hx' : x' ∈ P.W₁) :
    pairing (Kd d) n x x' = 0 :=
  s22a_pairing_of_mem_ann P.u₁_ne_zero hx hx'

theorem s22a_pairing_W₂ {y y' : V (Kd d) n} (hy : y ∈ P.W₂) (hy' : y' ∈ P.W₂) :
    pairing (Kd d) n y y' = 0 :=
  s22a_pairing_of_mem_ann P.s22a_u₂_ne_zero hy hy'

/-- A vector of `W₂` orthogonal to `W₁` is zero (when `V_K = W₁ ⊕ W₂`). -/
theorem s22a_eq_zero_of_W₂ (hW : P.W₁ ⊓ P.W₂ = ⊥) {y : V (Kd d) n} (hy : y ∈ P.W₂)
    (h : ∀ x ∈ P.W₁, pairing (Kd d) n x y = 0) : y = 0 := by
  have hC := P.isCompl_of_inf_eq_bot hW
  apply s22a_pairing_sepLeft
  intro v
  obtain ⟨x, hx, w, hw, rfl⟩ :=
    Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, s22a_pairing_comm, h x hx, P.s22a_pairing_W₂ hy hw, zero_add]

/-- **[Igusa, Lemma 1]** as used in §2.2 (kernel): the kernel of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)` is
`{±1}`, so that `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` embeds in `GL(W₁)`.

Departure from the paper: the statements of record of [Igusa, Lemma 1]
(`WeilClasses.igusa_lemma1_*`) live in `WeilClasses.External.Igusa.Sec2_2`, which imports this file,
so they cannot be used here; the facts used are proved in this file (see the helper sections). Here: an element acting
trivially on `W₁` acts trivially on `W₂ ≅ W₁*` (isometry), hence on `V_K = W₁ ⊕ W₂`, and the kernel
of `ρ` is `{±1}` (Tau Ceti, `mem_ker_spinToOrthogonal_iff`). -/
theorem restrictW₁_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.restrictW₁ g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 := by
  rw [← s22a_rho_eq_one_iff (s22a_n_pos P)]
  have hC := P.isCompl_of_inf_eq_bot hW
  constructor
  · intro h
    -- `ρ(g) = 1` on `W₁`, hence on `W₂ ≅ W₁*` (isometry), hence on `V_K = W₁ ⊕ W₂`.
    have h1 : ∀ x ∈ P.W₁, rho (Kd d) n g x = x := by
      intro x hx
      have := congrArg (fun u : (Module.End (Kd d) P.W₁)ˣ =>
        (((u : Module.End (Kd d) P.W₁) ⟨x, hx⟩ : P.W₁) : V (Kd d) n)) h
      simpa only [P.s22a_restrictW₁_apply, Units.val_one, Module.End.one_apply] using this
    have h2 : ∀ y ∈ P.W₂, rho (Kd d) n g y = y := by
      intro y hy
      rw [← sub_eq_zero]
      apply P.s22a_eq_zero_of_W₂ hW (Submodule.sub_mem _ (P.rho_mem_W₂ g y hy) hy)
      intro x hx
      rw [map_sub, ← s22a_pairing_rho (g : Spin (Kd d) n) x y, h1 x hx, sub_self]
    apply LinearEquiv.ext
    intro v
    obtain ⟨x, hx, w, hw, rfl⟩ :=
      Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, h1 x hx, h2 w hw]
    rfl
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [P.s22a_restrictW₁_apply, h]
    rfl

theorem s22a_mukai_u₁_u₂_ne_zero (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    mukai (Kd d) n P.u₁ P.u₂ ≠ 0 := fun h => (P.s22a_mukai_u₁_u₂_eq_zero_iff.mp h) hW

theorem s22a_mukai_u₂_u₁_ne_zero (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    mukai (Kd d) n P.u₂ P.u₁ ≠ 0 := by
  rw [s22a_mukai_swap]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (P.s22a_mukai_u₁_u₂_ne_zero hW)

theorem s22a_sup (hW : P.W₁ ⊓ P.W₂ = ⊥) : P.W₁ ⊔ P.W₂ = ⊤ :=
  (P.isCompl_of_inf_eq_bot hW).sup_eq_top

/-- An element of `Spin(V_K)` preserving `W₁` and `W₂` lies in `Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem s22a_mem_spinL₁L₂ (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : Spin (Kd d) n)
    (h₁ : ∀ v ∈ P.W₁, rho (Kd d) n g v ∈ P.W₁) (h₂ : ∀ w ∈ P.W₂, rho (Kd d) n g w ∈ P.W₂) :
    g ∈ P.spinL₁L₂ :=
  Subgroup.mem_inf.mpr ⟨s22a_mem_lineStabilizer P.s22a_u₂_ne_zero (P.s22a_sup hW)
      (P.s22a_mukai_u₁_u₂_ne_zero hW) g h₁,
    s22a_mem_lineStabilizer P.u₁_ne_zero (by rw [sup_comm]; exact P.s22a_sup hW)
      (P.s22a_mukai_u₂_u₁_ne_zero hW) g h₂⟩

theorem s22a_χ₁_spec (g : P.spinL₁L₂) :
    m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.χ₁ g • P.u₁ :=
  Classical.choose_spec ((Subgroup.mem_inf.mp g.2).1)

theorem s22a_χ₂_spec (g : P.spinL₁L₂) :
    m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₂ = P.χ₂ g • P.u₂ :=
  Classical.choose_spec ((Subgroup.mem_inf.mp g.2).2)

/-- `χ₁ χ₂ = 1`: `g` is an isometry of `(·,·)_S` and `(λ₁, λ₂)_S ≠ 0`. -/
theorem s22a_χ₁_mul_χ₂ (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) : P.χ₁ g * P.χ₂ g = 1 := by
  have h := s22a_mukai_spin (g : Spin (Kd d) n) P.u₁ P.u₂
  rw [P.s22a_χ₁_spec, P.s22a_χ₂_spec] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [mul_comm (P.χ₂ g)] at h
  have hc := P.s22a_mukai_u₁_u₂_ne_zero hW
  calc P.χ₁ g * P.χ₂ g = P.χ₁ g * P.χ₂ g * mukai (Kd d) n P.u₁ P.u₂ / mukai (Kd d) n P.u₁ P.u₂ := by
        field_simp
    _ = 1 := by rw [h, div_self hc]

/-- Dual bases of `W₁` and `W₂` (when `W₁ ∩ W₂ = 0`). -/
theorem s22a_dual (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    ∃ x y : Fin (2 * n) → V (Kd d) n, (∀ i, x i ∈ P.W₁) ∧ (∀ i, y i ∈ P.W₂) ∧
      (∀ i j, pairing (Kd d) n (x i) (y j) = if i = j then 1 else 0) ∧
      (∀ v ∈ P.W₁, v = ∑ i, pairing (Kd d) n v (y i) • x i) ∧
      (∀ w ∈ P.W₂, w = ∑ i, pairing (Kd d) n (x i) w • y i) :=
  s22a_dual_bases (fun _ ha _ hb => P.s22a_pairing_W₂ ha hb) P.isPure.2.2 P.isPure₂.2.2
    (P.isCompl_of_inf_eq_bot hW)

/-- **[Igusa, Lemma 1]** (surjectivity, corrected for `K`-points): every endomorphism `A` of `W₁`
with determinant `b²`, `b ≠ 0`, is `ρ(g)|_{W₁}` for some `g ∈ Spin(V_K)` preserving `W₂`. -/
theorem s22a_exists_spin_of_det (hW : P.W₁ ⊓ P.W₂ = ⊥) (A : Module.End (Kd d) P.W₁)
    {b : Kd d} (hb : b ≠ 0) (hA : LinearMap.det A = b * b) :
    ∃ g : Spin (Kd d) n, (∀ v : P.W₁, rho (Kd d) n g v = A v) ∧
      (∀ w ∈ P.W₂, rho (Kd d) n g w ∈ P.W₂) := by
  obtain ⟨x, y, hx, hy, hxy, -, ex₂⟩ := P.s22a_dual hW
  have pxy : ∀ a b, QuadraticMap.polar (Q (Kd d) n) (x a) (y b) = if a = b then 1 else 0 :=
    fun a b => by rw [← QuadraticMap.polarBilin_apply_apply]; exact hxy a b
  have pxx : ∀ a b, QuadraticMap.polar (Q (Kd d) n) (x a) (x b) = 0 :=
    fun a b => by rw [← QuadraticMap.polarBilin_apply_apply]; exact P.s22a_pairing_W₁ (hx a) (hx b)
  have i₂ : ∀ a ∈ P.W₂, ∀ b ∈ P.W₂, QuadraticMap.polar (Q (Kd d) n) a b = 0 :=
    fun a ha b hb => by rw [← QuadraticMap.polarBilin_apply_apply]; exact P.s22a_pairing_W₂ ha hb
  have Qx : ∀ a, Q (Kd d) n (x a) = 0 := fun a => s22a_Q_of_mem_ann P.u₁_ne_zero (hx a)
  have Qy : ∀ a, Q (Kd d) n (y a) = 0 := fun a => s22a_Q_of_mem_ann P.s22a_u₂_ne_zero (hy a)
  have ex₂' : ∀ w ∈ P.W₂, w = ∑ i, QuadraticMap.polar (Q (Kd d) n) (x i) w • y i := by
    intro w hw
    simpa only [QuadraticMap.polarBilin_apply_apply] using ex₂ w hw
  have hli : LinearIndependent (Kd d) (fun i => (⟨x i, hx i⟩ : P.W₁)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (fun v : P.W₁ => pairing (Kd d) n (v : V (Kd d) n) (y j)) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, hxy, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply] at h
    exact h
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, by have := s22a_n_pos P; omega⟩⟩
  let B₁ : Module.Basis (Fin (2 * n)) (Kd d) P.W₁ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; exact P.isPure.2.2.symm)
  have hB₁ : ∀ i, (B₁ i : V (Kd d) n) = x i := fun i => by
    simp [B₁]
  have hM : (LinearMap.toMatrix B₁ B₁ A).det = b * b := by rw [LinearMap.det_toMatrix, hA]
  obtain ⟨g, hg, hg'⟩ := s22a_lift_sq (s22a_n_pos P) i₂ hy ex₂' pxy pxx Qx Qy
    (LinearMap.toMatrix B₁ B₁ A) hb hM
  refine ⟨g, fun v => ?_, hg'⟩
  have hAB : ∀ k, (A (B₁ k) : V (Kd d) n) = ∑ l, LinearMap.toMatrix B₁ B₁ A l k • x l := by
    intro k
    conv_lhs => rw [← B₁.sum_repr (A (B₁ k))]
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.toMatrix_apply, hB₁]
  conv_lhs => rw [← B₁.sum_repr v]
  conv_rhs => rw [← B₁.sum_repr v]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hB₁, hg, hAB]

/-- `χ₁² = det₁` ([Chevalley, III.3.2 and III.4.5], `WeilClasses.chevalley_III_3_2_III_4_5`). -/
theorem s22a_χ₁_sq (g : P.spinL₁L₂) : P.χ₁ g ^ 2 = P.det₁ g := by
  obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 (Kd d) n P.u₁ P.isPure (g : Spin (Kd d) n)
    (fun v hv => P.rho_mem_W₁ g v hv)
  have : P.χ₁ g = c := smul_left_injective (Kd d) P.u₁_ne_zero ((P.s22a_χ₁_spec g).symm.trans hc)
  rw [this, hc2]
  rfl

/-- `χ₂² = det₂` ([Chevalley, III.3.2 and III.4.5]). -/
theorem s22a_χ₂_sq (g : P.spinL₁L₂) : P.χ₂ g ^ 2 = P.det₂ g := by
  obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 (Kd d) n P.u₂ P.isPure₂ (g : Spin (Kd d) n)
    (fun v hv => P.rho_mem_W₂ g v hv)
  have : P.χ₂ g = c :=
    smul_left_injective (Kd d) P.s22a_u₂_ne_zero ((P.s22a_χ₂_spec g).symm.trans hc)
  rw [this, hc2]
  rfl

/-- The claim "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`" (§2.2,
[Igusa, Lemma 1]), on `K`-points: the image of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`,
consists of the automorphisms whose determinant is a square in `K` (it contains `SL(W₁)`, and
`det₁ = χ₁²`); with `restrictW₁_eq_one_iff`, `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to that subgroup.

Correction of the paper (agreed with the project owner; REPORT.md): the paper says the quotient is
isomorphic to `GL(W₁)`. That holds for the algebraic groups (over `K̄`, as in Igusa's lemma) but not
for `K`-points: `diag(a, 1, …, 1)` with `a ∉ K^{×2}` is not in the image (its lifts
`±(√a⁻¹ x y + √a y x)` are not `K`-rational). Lemma 2.2.2 and the rest of the paper are unaffected.

Departure from the paper: the statements of record of [Igusa, Lemma 1]
(`WeilClasses.igusa_lemma1_*`) live in `WeilClasses.External.Igusa.Sec2_2`, which imports this file,
so they cannot be used here; the facts used are proved in this file (see the helper sections). Here: `⊆` by `det₁ = χ₁²`
([Chevalley, III.3.2, III.4.5], `chevalley_III_3_2_III_4_5`); `⊇` because `SL(W₁)` is generated by
transvections and `diag(c, c⁻¹)` (`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`), which
lift to `Spin(V_K)` (Tau Ceti's `spinTransvection`, products of reflections), and
`diag(b², 1, …, 1)` lifts to `ι(b⁻¹(x₀ + y₀)) ι(x₀ + b² y₀)` (`s22a_exists_spin_of_det`). -/
theorem range_restrictW₁ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) =
      {A : (Module.End (Kd d) P.W₁)ˣ |
        IsSquare (LinearMap.det (A : Module.End (Kd d) P.W₁))} := by
  ext A
  constructor
  · -- `det₁ = χ₁²` (`χ₁_sq`)
    rintro ⟨g, rfl⟩
    exact ⟨P.χ₁ g, by rw [P.det_restrictW₁, ← P.s22a_χ₁_sq g, sq]⟩
  · rintro ⟨b, hb⟩
    have hdet : LinearMap.det (A : Module.End (Kd d) P.W₁) ≠ 0 :=
      (Units.map (LinearMap.det : Module.End (Kd d) P.W₁ →* Kd d) A).ne_zero
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact hdet hb
    obtain ⟨g, hg, hg'⟩ := P.s22a_exists_spin_of_det hW A hb0 hb
    have hg₁ : ∀ v ∈ P.W₁, rho (Kd d) n g v ∈ P.W₁ := fun v hv => by
      rw [hg ⟨v, hv⟩]
      exact Subtype.mem _
    refine ⟨⟨g, P.s22a_mem_spinL₁L₂ hW g hg₁ hg'⟩, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [P.s22a_restrictW₁_apply]
    exact hg v

/-- "**The quotient maps injectively into `SO⁺(V_K)`**" (§2.2, [Igusa, Lemma 1]): an element of
`Spin(V_K)_{ℓ₁,ℓ₂}` acting trivially on `V_K` is `±1`.

Departure from the paper: the statements of record of [Igusa, Lemma 1]
(`WeilClasses.igusa_lemma1_*`) live in `WeilClasses.External.Igusa.Sec2_2`, which imports this file,
so they cannot be used here; the facts used are proved in this file (see the helper sections). Here: the kernel of
`ρ : Spin(V_K) → SO(V_K)` is `{±1}` (Tau Ceti, `mem_ker_spinToOrthogonal_iff`). -/
theorem rho_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    rho (Kd d) n g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 :=
  s22a_rho_eq_one_iff (s22a_n_pos P) _

/-- "**`W₂` is identified with `W₁*` via the bilinear pairing of `V_K`**" (§2.2): when
`W₁ ∩ W₂ = 0`, `y ↦ (·, y)_V|_{W₁}` is an isomorphism `W₂ ≅ W₁*`. -/
theorem pairingW₂_bijective (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Bijective P.pairingW₂ := by
  have hinj : Function.Injective P.pairingW₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    apply P.s22a_eq_zero_of_W₂ hW y.2
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    rwa [P.s22a_pairingW₂_apply] at this
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Subspace.dual_finrank_eq]
  exact P.isPure₂.2.2.trans P.isPure.2.2.symm

/-- "**The element of `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` corresponding to `g ∈ GL(W₁)` acts on `W₂` via
`(g*)⁻¹`**, where `W₂` is identified with `W₁*` via the bilinear pairing of `V_K`" (§2.2,
[Igusa, Lemma 1]): under `pairingW₂`, `ρ(g)|_{W₂}` is the inverse transpose of `ρ(g)|_{W₁}`.

The cited fact is the isometry property of `ρ(g)` (`igusa_lemma1_dual`, which cannot be imported
here); it is proved directly (`s22a_pairing_rho`). -/
theorem pairingW₂_rho (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) (y : V (Kd d) n)
    (hy : y ∈ P.W₂) :
    P.pairingW₂ ⟨rho (Kd d) n g y, P.rho_mem_W₂ g y hy⟩ =
      LinearMap.dualMap
        (((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁)
        (P.pairingW₂ ⟨y, hy⟩) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.dualMap_apply, P.s22a_pairingW₂_apply, P.s22a_pairingW₂_apply,
    P.s22a_restrictW₁_inv_apply]
  conv_lhs => rw [← s22a_pairing_rho ((g : Spin (Kd d) n)⁻¹) (x : V (Kd d) n)]
  rw [s22a_rho_inv_rho]

/-- "**`det₂(s) = det₁(s)⁻¹`**" (§2.2), for `s ∈ Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem det₂_eq_inv (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.det₂ g = (P.det₁ g)⁻¹ := by
  set e := LinearEquiv.ofBijective P.pairingW₂ (P.pairingW₂_bijective hd hW) with he
  set B : Module.End (Kd d) P.W₁ :=
    (((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) with hB
  have hconj : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
      (fun v hv => P.rho_mem_W₂ g v hv) =
      (e.symm : Module.Dual (Kd d) P.W₁ →ₗ[Kd d] P.W₂) ∘ₗ B.dualMap ∘ₗ
        (e.symm.symm : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁) := by
    apply LinearMap.ext
    intro y
    apply e.injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    rw [he, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hB]
    exact P.pairingW₂_rho hd hW g y y.2
  have hdet : P.det₂ g = LinearMap.det B := by
    show LinearMap.det ((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
      (fun v hv => P.rho_mem_W₂ g v hv)) = _
    rw [hconj, LinearMap.det_conj, LinearMap.det_dualMap]
  rw [hdet, hB, ← P.det_restrictW₁ g]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

/-- "**`ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁`**" (§2.2, by the proof of [Igusa, Lemma 1] and [Chevalley, III.3.2]): the
character `χ₁` of `Spin(V_K)_{ℓ₁,ℓ₂}` on `ℓ̃₁` satisfies `χ₁² = det₁`. Used again in §6.4
("`ℓ̃ᵢ²` is the character `⋀^{2n} Wᵢ ≅ detᵢ`"). -/
theorem χ₁_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₁ g ^ 2 = P.det₁ g :=
  P.s22a_χ₁_sq g

/-- "**`ℓ̃₂ ⊗ ℓ̃₂ ≅ det₂`**" (§2.2): `χ₂² = det₂`. -/
theorem χ₂_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₂ g ^ 2 = P.det₂ g :=
  P.s22a_χ₂_sq g

/-! ## Lemma 2.2.2 -/

/-- `Spin(V_K)_P ⊆ Spin(V_K)_{ℓ₁,ℓ₂}`: an element fixing `P_K` pointwise fixes `u₁` and `u₂`. -/
theorem spinPK_le_spinL₁L₂ : P.spinPK ≤ P.spinL₁L₂ := by
  intro g hg
  refine Subgroup.mem_inf.mpr ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
  · rw [one_smul]
    exact hg P.u₁ (Submodule.subset_span (Set.mem_insert _ _))
  · rw [one_smul]
    exact hg P.u₂ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

/-- An element fixing `u₁` and `u₂` fixes `P_K` pointwise. -/
theorem s22a_mem_spinPK {g : Spin (Kd d) n}
    (h₁ : m (Kd d) n (g : C (Kd d) n) P.u₁ = P.u₁) (h₂ : m (Kd d) n (g : C (Kd d) n) P.u₂ = P.u₂) :
    g ∈ P.spinPK := by
  intro p hp
  have hle : P.PK ≤ LinearMap.eqLocus (m (Kd d) n (g : C (Kd d) n)) LinearMap.id := by
    rw [PK, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  exact hle hp

/-- The scalar `-1 ∈ Spin(V_K)`. -/
noncomputable def s22a_negOne : Spin (Kd d) n :=
  ⟨-1, by
    have := s22a_nontrivial_V (F := Kd d) (s22a_n_pos P)
    exact neg_one_mem_spinGroup (Q (Kd d) n) s22a_Q_nondegenerate.ne_zero⟩

theorem s22a_coe_negOne : ((P.s22a_negOne : Spin (Kd d) n) : C (Kd d) n) = -1 := rfl

theorem s22a_rho_negOne_mul (g : Spin (Kd d) n) (v : V (Kd d) n) :
    rho (Kd d) n (P.s22a_negOne * g) v = rho (Kd d) n g v := by
  rw [s22a_rho_mul]
  have h1 : rho (Kd d) n P.s22a_negOne = 1 :=
    (s22a_rho_eq_one_iff (s22a_n_pos P) _).mpr (Or.inr P.s22a_coe_negOne)
  rw [h1]
  rfl

theorem s22a_m_negOne_mul (g : Spin (Kd d) n) (s : S (Kd d) n) :
    m (Kd d) n ((P.s22a_negOne * g : Spin (Kd d) n) : C (Kd d) n) s =
      -m (Kd d) n (g : C (Kd d) n) s := by
  rw [Submonoid.coe_mul, P.s22a_coe_negOne, neg_one_mul, map_neg, LinearMap.neg_apply]

/-- The homomorphism `Spin(V_K)_P → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def restrictW₁P : P.spinPK →* (Module.End (Kd d) P.W₁)ˣ :=
  P.restrictW₁.comp (Subgroup.inclusion P.spinPK_le_spinL₁L₂)

/-- Every `A ∈ SL(W₁)` is `ρ(g)|_{W₁}` for some `g ∈ Spin(V_K)_P` ([Igusa, Lemma 1]; `det₁ = χ₁²`,
`χ₁ χ₂ = 1`, and `-1 ∈ Spin(V_K)` to fix the sign). -/
theorem s22a_exists_spinPK (hW : P.W₁ ⊓ P.W₂ = ⊥) (A : Module.End (Kd d) P.W₁)
    (hA : LinearMap.det A = 1) :
    ∃ g : P.spinPK, ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) = A := by
  obtain ⟨g, hg, hg'⟩ := P.s22a_exists_spin_of_det hW A one_ne_zero (by rw [hA, one_mul])
  have hg₁ : ∀ v ∈ P.W₁, rho (Kd d) n g v ∈ P.W₁ := fun v hv => by
    rw [hg ⟨v, hv⟩]
    exact Subtype.mem _
  set g₀ : P.spinL₁L₂ := ⟨g, P.s22a_mem_spinL₁L₂ hW g hg₁ hg'⟩
  have hdet₁ : P.det₁ g₀ = 1 := by
    have : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
        (fun v hv => P.rho_mem_W₁ g₀ v hv) = A := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact hg v
    show LinearMap.det _ = 1
    rw [this, hA]
  have hsq : P.χ₁ g₀ ^ 2 = 1 := by rw [P.s22a_χ₁_sq, hdet₁]
  have hχχ := P.s22a_χ₁_mul_χ₂ hW g₀
  have hres : ∀ g' : Spin (Kd d) n, (∀ v, rho (Kd d) n g' v = rho (Kd d) n g v) →
      (m (Kd d) n (g' : C (Kd d) n) P.u₁ = P.u₁) → (m (Kd d) n (g' : C (Kd d) n) P.u₂ = P.u₂) →
      ∃ g : P.spinPK, ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁) = A := by
    intro g' hρ h₁ h₂
    refine ⟨⟨g', P.s22a_mem_spinPK h₁ h₂⟩, ?_⟩
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show rho (Kd d) n g' v = _
    rw [hρ, hg v]
  rw [sq] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · have h' : P.χ₂ g₀ = 1 := by rw [h, one_mul] at hχχ; exact hχχ
    refine hres g (fun v => rfl) ?_ ?_
    · rw [show (g : C (Kd d) n) = ((g₀ : Spin (Kd d) n) : C (Kd d) n) from rfl,
        P.s22a_χ₁_spec, h, one_smul]
    · rw [show (g : C (Kd d) n) = ((g₀ : Spin (Kd d) n) : C (Kd d) n) from rfl,
        P.s22a_χ₂_spec, h', one_smul]
  · have h' : P.χ₂ g₀ = -1 := by
      rw [h, neg_one_mul, neg_eq_iff_eq_neg] at hχχ
      exact hχχ
    refine hres (P.s22a_negOne * g) (fun v => P.s22a_rho_negOne_mul g v) ?_ ?_
    · rw [P.s22a_m_negOne_mul,
        show (g : C (Kd d) n) = ((g₀ : Spin (Kd d) n) : C (Kd d) n) from rfl,
        P.s22a_χ₁_spec, h, neg_one_smul, neg_neg]
    · rw [P.s22a_m_negOne_mul,
        show (g : C (Kd d) n) = ((g₀ : Spin (Kd d) n) : C (Kd d) n) from rfl,
        P.s22a_χ₂_spec, h', neg_one_smul, neg_neg]

/-- The proof of Lemma 2.2.2 (see `WeilClasses.lemma2_2_2_restrict`). -/
theorem s22a_restrict_aux (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Injective P.restrictW₁P ∧
      P.restrictW₁P.range = specialLinearUnits (Kd d) P.W₁ := by
  -- The proof of the paper: `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is identified with a subgroup of `GL(W₁)`
  -- containing `SL(W₁)` ([Igusa, Lemma 1], `restrictW₁_eq_one_iff`, `s22a_exists_spin_of_det`),
  -- `det₁ = χ₁²` and `χ₁ χ₂ = 1`; so `Spin(V_K)_P` maps onto `SL(W₁)`, injectively since
  -- `-1 ∉ Spin(V_K)_P`.
  have hu₁ := P.u₁_ne_zero
  have hfix₁ : ∀ g : P.spinPK, m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.u₁ :=
    fun g => g.2 P.u₁ (Submodule.subset_span (Set.mem_insert _ _))
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    rcases (P.restrictW₁_eq_one_iff hd hW (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g)).mp hg
      with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exfalso
      have h1 := hfix₁ g
      have h2 : ((g : Spin (Kd d) n) : C (Kd d) n) = -1 := h
      rw [h2, map_neg, map_one, LinearMap.neg_apply, Module.End.one_apply] at h1
      have : (2 : Kd d) • P.u₁ = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        exact neg_add_cancel _
      exact hu₁ ((smul_eq_zero.mp this).resolve_left two_ne_zero)
  · ext A
    constructor
    · rintro ⟨g, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      have hχ : P.χ₁ (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g) = 1 :=
        smul_left_injective (Kd d) hu₁
          ((P.s22a_χ₁_spec _).symm.trans ((hfix₁ g).trans (one_smul _ _).symm))
      have h := P.s22a_χ₁_sq (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g)
      rw [hχ, one_pow] at h
      simp only [Units.coe_map, Units.val_one]
      exact h.symm
    · intro hA
      have hdetA : LinearMap.det (A : Module.End (Kd d) P.W₁) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.mp hA)
        simpa using this
      obtain ⟨g, hg⟩ := P.s22a_exists_spinPK hW (A : Module.End (Kd d) P.W₁) hdetA
      exact ⟨g, Units.ext hg⟩

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint corrected: the group `Spin(V_K)_P` is
isomorphic to `SL_{2n}(K)`. The paper prints `SL_n(K)`; this is an obvious misprint, since `W₁` has
dimension `2n` and the text just before says `GL(W₁) ≅ GL_{2n}(K)`. Standing hypothesis:
`W₁ ∩ W₂ = 0`. See `lemma2_2_2_restrict` for the isomorphism itself.

Departure from the paper: [Igusa, Lemma 1] is proved locally (see `lemma2_2_2_restrict`). -/
theorem _root_.WeilClasses.lemma2_2_2 (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Nonempty (P.spinPK ≃* Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d)) := by
  obtain ⟨hinj, hrange⟩ := P.s22a_restrict_aux hd hW
  obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (2 * n)) (Kd d) P.W₁) :=
    ⟨Module.finBasisOfFinrankEq (Kd d) P.W₁ P.isPure.2.2⟩
  have hdet : ∀ g : P.spinPK, LinearMap.det ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
      Module.End (Kd d) P.W₁) = 1 := by
    intro g
    have hmem : P.restrictW₁P g ∈ specialLinearUnits (Kd d) P.W₁ := hrange ▸ ⟨g, rfl⟩
    have := congrArg Units.val (MonoidHom.mem_ker.mp hmem)
    simpa using this
  let φ : P.spinPK →* Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d) :=
    { toFun := fun g => ⟨LinearMap.toMatrix B B
          ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁),
        by rw [LinearMap.det_toMatrix, hdet]⟩
      map_one' := by
        apply Subtype.ext
        show LinearMap.toMatrix B B ((P.restrictW₁P 1 : (Module.End (Kd d) P.W₁)ˣ) :
            Module.End (Kd d) P.W₁) = 1
        rw [MonoidHom.map_one, Units.val_one, LinearMap.toMatrix_one]
      map_mul' := by
        intro g h
        apply Subtype.ext
        show LinearMap.toMatrix B B ((P.restrictW₁P (g * h) : (Module.End (Kd d) P.W₁)ˣ) :
            Module.End (Kd d) P.W₁) =
          LinearMap.toMatrix B B ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
            Module.End (Kd d) P.W₁) *
          LinearMap.toMatrix B B ((P.restrictW₁P h : (Module.End (Kd d) P.W₁)ˣ) :
            Module.End (Kd d) P.W₁)
        rw [MonoidHom.map_mul, Units.val_mul, LinearMap.toMatrix_mul] }
  have hφ : ∀ g, ((φ g : Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d)) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d)) = LinearMap.toMatrix B B
        ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) := fun g => rfl
  refine ⟨MulEquiv.ofBijective φ ⟨fun g h hgh => hinj ?_, fun M => ?_⟩⟩
  · apply Units.ext
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d) =>
      (A : Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d))) hgh
    simp only [hφ] at h1
    exact (LinearMap.toMatrix B B).injective h1
  · -- `M ∈ SL_{2n}(K)` is the matrix of an endomorphism of `W₁` of determinant `1`
    have hA : LinearMap.det (Matrix.toLin B B (M : Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d))) = 1 := by
      rw [LinearMap.det_toLin]
      exact M.2
    obtain ⟨g, hg⟩ := P.s22a_exists_spinPK hW _ hA
    refine ⟨g, Subtype.ext ?_⟩
    rw [hφ, hg]
    exact LinearMap.toMatrix_toLin B B _

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint `SL_n(K)` corrected to `SL_{2n}(K)`,
in the form of its proof: `g ↦ ρ(g)|_{W₁}` maps `Spin(V_K)_P` isomorphically onto `SL(W₁)`.
(The proof's "`Spin(V_K)_P` is the kernel of `det₁` in `Spin(V_K)_{ℓ₁,ℓ₂}`" should read: the kernel
of `det₁` is `{±1} · Spin(V_K)_P`; `Spin(V_K)_P` is the kernel of `χ₁`, and `-1 ∉ Spin(V_K)_P`.)

Departure from the paper: the proof uses [Igusa, Lemma 1] (`restrictW₁_eq_one_iff`, and that the
image of `Spin(V_K)_{ℓ₁,ℓ₂}` contains `SL(W₁)`: `s22a_exists_spin_of_det`), proved in this file because
the statements of record (`WeilClasses.igusa_lemma1_*`) live in a module importing it; together with
`det₁ = χ₁²` (`χ₁_sq`) and `χ₁ χ₂ = 1` (`s22a_χ₁_mul_χ₂`). -/
theorem _root_.WeilClasses.lemma2_2_2_restrict (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Injective P.restrictW₁P ∧
      P.restrictW₁P.range = specialLinearUnits (Kd d) P.W₁ :=
  P.s22a_restrict_aux hd hW

/-! ## Remark 2.2.3 -/

theorem s22a_linIndep₁₂ {s t : Kd d} (h : s • P.u₁ + t • P.u₂ = 0) : s = 0 ∧ t = 0 :=
  (LinearIndependent.pair_iff.mp P.linIndep) s t h

/-- A vector of `P_K` on neither line is `a u₁ + b u₂` with `a, b ≠ 0`. -/
theorem s22a_coeffs {w : S (Kd d) n} (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    ∃ a b : Kd d, a ≠ 0 ∧ b ≠ 0 ∧ w = a • P.u₁ + b • P.u₂ := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hwP
  refine ⟨a, b, ?_, ?_, rfl⟩
  · rintro rfl
    apply hw₂
    rw [zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro rfl
    apply hw₁
    rw [zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The stabilizer of `w = a u₁ + b u₂`** (`n ≥ 3`, `a, b ≠ 0`, [Igusa, Lemma 2]): an element of
`Spin(V_K)` fixing `w` either fixes `u₁` and `u₂`, or exchanges the lines:
`g u₁ = (b/a) u₂`, `g u₂ = (a/b) u₁`. It preserves the joint kernel `P_K` of the infinitesimal
stabilizer of `w` (`s22a_fix_iff`, `s22a_fix_m_spin`), and pure spinors of `P_K` lie on the two lines
([Chevalley, III.1.12]). -/
theorem s22a_stab_cases (hn : 3 ≤ n) (hW : P.W₁ ⊓ P.W₂ = ⊥) {a b : Kd d} (ha : a ≠ 0)
    (hb : b ≠ 0) (g : Spin (Kd d) n)
    (hg : m (Kd d) n (g : C (Kd d) n) (a • P.u₁ + b • P.u₂) = a • P.u₁ + b • P.u₂) :
    (m (Kd d) n (g : C (Kd d) n) P.u₁ = P.u₁ ∧ m (Kd d) n (g : C (Kd d) n) P.u₂ = P.u₂) ∨
      (m (Kd d) n (g : C (Kd d) n) P.u₁ = (b / a) • P.u₂ ∧
        m (Kd d) n (g : C (Kd d) n) P.u₂ = (a / b) • P.u₁) := by
  have hfix := s22a_fix_iff hn P.isPure P.isPure₂ hW ha hb
  have hmem : ∀ u ∈ Submodule.span (Kd d) {P.u₁, P.u₂},
      m (Kd d) n (g : C (Kd d) n) u ∈ Submodule.span (Kd d) {P.u₁, P.u₂} := by
    intro u hu
    exact (hfix _).mp (s22a_fix_m_spin ((hfix u).mpr hu) g hg)
  have hu₁ : P.u₁ ∈ Submodule.span (Kd d) {P.u₁, P.u₂} := Submodule.subset_span (Set.mem_insert _ _)
  have hu₂ : P.u₂ ∈ Submodule.span (Kd d) {P.u₁, P.u₂} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨α, β, e₁⟩ := Submodule.mem_span_pair.mp (hmem _ hu₁)
  obtain ⟨γ, δ, e₂⟩ := Submodule.mem_span_pair.mp (hmem _ hu₂)
  have hp₁ := s22a_pure_m_spin P.isPure g
  have hp₂ := s22a_pure_m_spin P.isPure₂ g
  rw [← e₁] at hp₁
  rw [← e₂] at hp₂
  have c₁ := s22a_chevalley_III_1_12 (by omega) _ _ P.isPure P.isPure₂ hW α β hp₁
  have c₂ := s22a_chevalley_III_1_12 (by omega) _ _ P.isPure P.isPure₂ hW γ δ hp₂
  -- coefficients of `g w = w`
  have hw : (a * α + b * γ - a) • P.u₁ + (a * β + b * δ - b) • P.u₂ = 0 := by
    have := hg
    rw [map_add, map_smul, map_smul, ← e₁, ← e₂] at this
    rw [← sub_eq_zero] at this
    rw [← this]
    module
  obtain ⟨k₁, k₂⟩ := P.s22a_linIndep₁₂ hw
  rcases c₁ with rfl | rfl <;> rcases c₂ with rfl | rfl
  · -- `α = 0`, `γ = 0`: then `a = 0`
    exfalso
    apply ha
    linear_combination -k₁
  · -- `α = 0`, `δ = 0`: exchange
    right
    have hβ : β = b / a := by field_simp; linear_combination k₂
    have hγ : γ = a / b := by field_simp; linear_combination k₁
    refine ⟨?_, ?_⟩
    · rw [← e₁, zero_smul, zero_add, hβ]
    · rw [← e₂, zero_smul, add_zero, hγ]
  · -- `β = 0`, `γ = 0`: fixes both
    left
    have hα : α = 1 := by
      have : a * (α - 1) = 0 := by linear_combination k₁
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
    have hδ : δ = 1 := by
      have : b * (δ - 1) = 0 := by linear_combination k₂
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)
    refine ⟨?_, ?_⟩
    · rw [← e₁, zero_smul, add_zero, hα, one_smul]
    · rw [← e₂, zero_smul, zero_add, hδ, one_smul]
  · -- `β = 0`, `δ = 0`: then `b = 0`
    exfalso
    apply hb
    linear_combination -k₂

/-- **An element of `Spin(V_K)` exchanging the two lines** (`n` even): `s u₁ = (b/a) u₂`,
`s u₂ = (a/b) u₁`, so `s` fixes `a u₁ + b u₂`. (A product of reflections maps `W₁` onto `W₂`, hence
`u₁ ↦ β u₂`, `u₂ ↦ γ u₁` with `βγ = 1` since `(·,·)_S` is symmetric and invariant; a torus element of
`Spin(V_K)_{ℓ₁,ℓ₂}` adjusts the scalars.) -/
theorem s22a_exists_swap (heven : Even n) (hW : P.W₁ ⊓ P.W₂ = ⊥) {a b : Kd d} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ∃ s : Spin (Kd d) n, m (Kd d) n (s : C (Kd d) n) P.u₁ = (b / a) • P.u₂ ∧
      m (Kd d) n (s : C (Kd d) n) P.u₂ = (a / b) • P.u₁ := by
  have hn := s22a_n_pos P
  obtain ⟨x, y, hx, hy, hxy, ex₁, ex₂⟩ := P.s22a_dual hW
  have pxy : ∀ a b, QuadraticMap.polar (Q (Kd d) n) (x a) (y b) = if a = b then 1 else 0 :=
    fun a b => by rw [← QuadraticMap.polarBilin_apply_apply]; exact hxy a b
  have pxx : ∀ a b, QuadraticMap.polar (Q (Kd d) n) (x a) (x b) = 0 :=
    fun a b => by rw [← QuadraticMap.polarBilin_apply_apply]; exact P.s22a_pairing_W₁ (hx a) (hx b)
  have pyy : ∀ a b, QuadraticMap.polar (Q (Kd d) n) (y a) (y b) = 0 :=
    fun a b => by rw [← QuadraticMap.polarBilin_apply_apply]; exact P.s22a_pairing_W₂ (hy a) (hy b)
  have Qx : ∀ a, Q (Kd d) n (x a) = 0 := fun a => s22a_Q_of_mem_ann P.u₁_ne_zero (hx a)
  have Qy : ∀ a, Q (Kd d) n (y a) = 0 := fun a => s22a_Q_of_mem_ann P.s22a_u₂_ne_zero (hy a)
  obtain ⟨G, hGx, hGy⟩ := s22a_exists_exchange pxy pxx pyy Qx Qy
  have hG₁ : ∀ v ∈ P.W₁, rho (Kd d) n G v ∈ P.W₂ := by
    intro v hv
    rw [ex₁ v hv, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul, hGx]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (hy i))
  have hG₂ : ∀ v ∈ P.W₂, rho (Kd d) n G v ∈ P.W₁ := by
    intro v hv
    rw [ex₂ v hv, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul, hGy]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (hx i))
  have hann₁ : ann (Kd d) n (m (Kd d) n (G : C (Kd d) n) P.u₁) = P.W₂ := by
    rw [ann_m_spin]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      exact hG₁ v hv
    · rw [LinearEquiv.finrank_map_eq]
      exact P.isPure.2.2.trans P.isPure₂.2.2.symm
  have hann₂ : ann (Kd d) n (m (Kd d) n (G : C (Kd d) n) P.u₂) = P.W₁ := by
    rw [ann_m_spin]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      exact hG₂ v hv
    · rw [LinearEquiv.finrank_map_eq]
      exact P.isPure₂.2.2.trans P.isPure.2.2.symm
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp
    (s22a_mem_span_of_ann_le (u := P.u₂) (u' := P.u₁) P.u₁_ne_zero
      (by rw [sup_comm]; exact P.s22a_sup hW) (P.s22a_mukai_u₂_u₁_ne_zero hW) hann₁.ge)
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp
    (s22a_mem_span_of_ann_le (u := P.u₁) (u' := P.u₂) P.s22a_u₂_ne_zero
      (P.s22a_sup hW) (P.s22a_mukai_u₁_u₂_ne_zero hW) hann₂.ge)
  have hβγ : β * γ = 1 := by
    have h := s22a_mukai_spin G P.u₁ P.u₂
    rw [← hβ, ← hγ] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [s22a_mukai_swap P.u₁ P.u₂, heven.neg_one_pow, one_mul] at h
    have hc := P.s22a_mukai_u₁_u₂_ne_zero hW
    have : (β * γ - 1) * mukai (Kd d) n P.u₁ P.u₂ = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc)
  have hβ0 : β ≠ 0 := left_ne_zero_of_mul_eq_one hβγ
  have ht : b / (a * β) ≠ 0 := div_ne_zero hb (mul_ne_zero ha hβ0)
  set k₀ : Fin (2 * n) := ⟨0, by omega⟩
  obtain ⟨h, hh₁, hh₂⟩ := s22a_exists_torus (hx k₀) (hy k₀) P.u₁_ne_zero P.s22a_u₂_ne_zero
    (by rw [hxy, ite_eq_left rfl]) ht
  refine ⟨G * h, ?_, ?_⟩
  · rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hh₁, map_smul, ← hβ, smul_smul]
    congr 1
    field_simp
  · rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hh₂, map_smul, ← hγ, smul_smul]
    congr 1
    field_simp
    linear_combination hβγ

/-- An element of `Spin(V_K)_P` fixes every vector of `P_K`, hence the line of `w ∈ P_K`. -/
theorem s22a_spinPK_le_fixing {w : S (Kd d) n} (hwP : w ∈ P.PK) :
    P.spinPK ≤ fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) := by
  intro g hg p hp
  exact hg p ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwP)) hp)



/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), first claim
([Igusa, Lemma 2]): for `n ≥ 3`, a vector `w ∈ P_K` on neither `ℓ̃₁` nor `ℓ̃₂` is not a pure spinor
("as commented above", i.e. by [Chevalley, III.1.12]). Reading: `w` is a `K`-point of the plane
(`w ∈ P_K`); this includes the nonzero rational points of `P`.

Departure from the paper: [Chevalley, III.1.12] is proved locally (`s22a_chevalley_III_1_12`), its
statement of record living in a module that imports this file. -/
theorem _root_.WeilClasses.remark2_2_3_not_pure (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    ¬ IsEvenPureSpinor (Kd d) n w := by
  -- [Chevalley, III.1.12] (local version `s22a_chevalley_III_1_12`).
  intro hpure
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hwP
  rcases s22a_chevalley_III_1_12 (by omega) _ _ P.isPure P.isPure₂ hW a b hpure with rfl | rfl
  · apply hw₂
    rw [zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply hw₁
    rw [zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` odd
([Igusa, Lemma 2] and the remark after it): for `n ≥ 3` odd and `w ∈ P_K` on neither `ℓ̃₁` nor
`ℓ̃₂`, the stabilizer of `w` in `Spin(V_K)` is `Spin(V_K)_P`.

Departure from the paper: the remark cites [Igusa, Lemma 2] and [Chevalley, III.1.12], whose
statements of record live in modules importing this file; their content is proved here. The
stabilizer is analysed through the infinitesimal stabilizer `{ξ ∈ span(ι p ι q) : m_ξ w = 0}`, whose
joint kernel is `P_K` (`s22a_fix_iff`, by a number-operator argument for `n ≥ 3`) and is preserved
by the stabilizer of `w` (`s22a_fix_m_spin`); so the stabilizer fixes `u₁, u₂` or exchanges the two
lines (`s22a_stab_cases`). For odd `n` an exchange is impossible:
`(·,·)_S` is invariant and alternating on `S⁺`, and `(u₁, u₂)_S ≠ 0`. -/
theorem _root_.WeilClasses.remark2_2_3_odd (hd : 0 < d) (hn : 3 ≤ n) (hodd : Odd n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) = P.spinPK := by
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  refine le_antisymm (fun g hg => ?_) (P.s22a_spinPK_le_fixing hwP)
  have hgw := hg _ (Submodule.mem_span_singleton_self _)
  rcases P.s22a_stab_cases hn hW ha hb g hgw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact P.s22a_mem_spinPK h₁ h₂
  · -- for odd `n` the pairing is alternating, which excludes an exchange of the two lines
    exfalso
    have h := s22a_mukai_spin g P.u₁ P.u₂
    rw [h₁, h₂] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [s22a_mukai_swap P.u₁ P.u₂, hodd.neg_one_pow] at h
    have hc := P.s22a_mukai_u₁_u₂_ne_zero hW
    apply hc
    have e : b / a * (a / b) = 1 := by field_simp
    have : (2 : Kd d) * mukai (Kd d) n P.u₁ P.u₂ = 0 := by
      linear_combination (-1 : Kd d) * h - (mukai (Kd d) n P.u₁ P.u₂) * e
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` even
([Igusa, Lemma 2] and the remark after it): "the stabilizer has two connected components and the
identity component is `Spin(V_K)_P`". Reading for the group of `K`-points: `Spin(V_K)_P` is a normal
subgroup of index `2` of the stabilizer of `w` in `Spin(V_K)` (the non-identity component, the
elements exchanging `ℓ₁` and `ℓ₂`, has `K`-points).

Departure from the paper: the remark cites [Igusa, Lemma 2] and [Chevalley, III.1.12], whose
statements of record live in modules importing this file; their content is proved here. The
stabilizer is analysed through the infinitesimal stabilizer `{ξ ∈ span(ι p ι q) : m_ξ w = 0}`, whose
joint kernel is `P_K` (`s22a_fix_iff`, by a number-operator argument for `n ≥ 3`) and is preserved
by the stabilizer of `w` (`s22a_fix_m_spin`); so the stabilizer fixes `u₁, u₂` or exchanges the two
lines (`s22a_stab_cases`). For even `n` an exchange exists: a product of
reflections maps `W₁` onto `W₂`, and a torus element of `Spin(V_K)_{ℓ₁,ℓ₂}` adjusts the scalars
(`s22a_exists_swap`). -/
theorem _root_.WeilClasses.remark2_2_3_even (hd : 0 < d) (hn : 3 ≤ n) (heven : Even n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    P.spinPK ≤ fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) ∧
      (P.spinPK.subgroupOf (fixingSpin (Kd d) n (Submodule.span (Kd d) {w}))).Normal ∧
      P.spinPK.relIndex (fixingSpin (Kd d) n (Submodule.span (Kd d) {w})) = 2 := by
  -- The stabilizer of `w` consists of the elements fixing `u₁, u₂` (`Spin(V_K)_P`) and of the
  -- elements exchanging the two lines (`s22a_stab_cases`); for `n` even the latter exist
  -- (`s22a_exists_swap`), so `Spin(V_K)_P` has index `2`.
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  have hle := P.s22a_spinPK_le_fixing hwP
  obtain ⟨s, hs₁, hs₂⟩ := P.s22a_exists_swap heven hW ha hb
  have hsw : m (Kd d) n (s : C (Kd d) n) (a • P.u₁ + b • P.u₂) = a • P.u₁ + b • P.u₂ := by
    rw [map_add, map_smul, map_smul, hs₁, hs₂, smul_smul, smul_smul,
      mul_div_cancel₀ _ ha, mul_div_cancel₀ _ hb, add_comm]
  have hsG : s ∈ fixingSpin (Kd d) n (Submodule.span (Kd d) {a • P.u₁ + b • P.u₂}) := by
    intro p hp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    rw [map_smul, hsw]
  have hnot : ∀ g : Spin (Kd d) n, m (Kd d) n (g : C (Kd d) n) P.u₁ = (b / a) • P.u₂ →
      g ∉ P.spinPK := by
    intro g hg hgP
    have h1 : m (Kd d) n (g : C (Kd d) n) P.u₁ = P.u₁ :=
      hgP P.u₁ (Submodule.subset_span (Set.mem_insert _ _))
    rw [hg] at h1
    have := P.s22a_linIndep₁₂ (s := 1) (t := -(b / a))
      (by rw [one_smul, neg_smul, ← h1, add_neg_cancel])
    exact one_ne_zero this.1
  have hidx : (P.spinPK.subgroupOf
      (fixingSpin (Kd d) n (Submodule.span (Kd d) {a • P.u₁ + b • P.u₂}))).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsG⟩, fun g => ?_⟩
    have hgw : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) (a • P.u₁ + b • P.u₂) =
        a • P.u₁ + b • P.u₂ := g.2 _ (Submodule.mem_span_singleton_self _)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases P.s22a_stab_cases hn hW ha hb g hgw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine Or.inr ⟨P.s22a_mem_spinPK h₁ h₂, hnot _ ?_⟩
      rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hs₁, map_smul, h₂]
    · refine Or.inl ⟨P.s22a_mem_spinPK ?_ ?_, hnot g h₁⟩
      · have e : b / a * (a / b) = 1 := by field_simp
        rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hs₁, map_smul, h₂, smul_smul, e,
          one_smul]
      · have e : a / b * (b / a) = 1 := by field_simp
        rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hs₂, map_smul, h₁, smul_smul, e,
          one_smul]
  exact ⟨hle, Subgroup.normal_of_index_eq_two hidx, hidx⟩

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "in particular,
`w` determines `P`": any `K`-secant `P'` with `W₁' ∩ W₂' = 0` whose plane contains `w` has the same
plane `P'_K = P_K` (hence the same rational plane).

Departure from the paper: the paper derives this from the description of the stabilizer of `w`
([Igusa, Lemma 2]: its identity component is `Spin(V_K)_P`). For `K`-points we use instead that
`P_K` is the joint kernel of the infinitesimal stabilizer of `w` (`s22a_fix_iff`), which depends only
on `w`. -/
theorem _root_.WeilClasses.remark2_2_3_determines (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (P' : KSecant n d) (hW' : P'.W₁ ⊓ P'.W₂ = ⊥) (hwP' : w ∈ P'.PK) :
    P'.PK = P.PK := by
  -- `P_K` is the joint kernel of the infinitesimal stabilizer of `w` (`s22a_fix_iff`), which
  -- depends only on `w`.
  have hnp := remark2_2_3_not_pure P hd hn hW w hwP hw₁ hw₂
  have hw0 : w ≠ 0 := fun h => hw₁ (h ▸ Submodule.zero_mem _)
  have hline : ∀ {u : S (Kd d) n}, IsEvenPureSpinor (Kd d) n u →
      w ∉ Submodule.span (Kd d) {u} := by
    intro u hu h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw0 hc.symm
    apply hnp
    rw [← hc]
    exact s22a_isEvenPureSpinor_smul hu hc0
  obtain ⟨a, b, ha, hb, hab⟩ := P.s22a_coeffs hwP hw₁ hw₂
  obtain ⟨a', b', ha', hb', hab'⟩ := P'.s22a_coeffs hwP' (hline P'.isPure) (hline P'.isPure₂)
  ext s
  show s ∈ Submodule.span (Kd d) {P'.u₁, P'.u₂} ↔ s ∈ Submodule.span (Kd d) {P.u₁, P.u₂}
  rw [← s22a_fix_iff hn P'.isPure P'.isPure₂ hW' ha' hb', ← hab', hab,
    s22a_fix_iff hn P.isPure P.isPure₂ hW ha hb]

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "`ℙ(P)` is the
unique secant to the spinor variety through `w`": if `w` lies on the line through two distinct
points `[x], [y]` of the (complex) even spinor variety, then that line is `ℙ(P_ℂ)`.

Departure from the paper: as for `remark2_2_3_determines`, over `ℂ`: `ker m_w = 0`
([Chevalley, III.1.12], `s22a_ann_combo_eq_bot`) forces `x, y` to be transversal with nonzero
coefficients, and both `P_ℂ` and `ℂx + ℂy` are the joint kernel of the infinitesimal stabilizer of
`w` (`s22a_fix_iff`). -/
theorem _root_.WeilClasses.remark2_2_3_unique_secant (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (x y : S ℂ n) (hx : IsEvenPureSpinor ℂ n x) (hy : IsEvenPureSpinor ℂ n y)
    (hxy : LinearIndependent ℂ ![x, y]) (hw : bcS (Kd d) ℂ n w ∈ Submodule.span ℂ {x, y}) :
    Submodule.span ℂ {x, y} =
      Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁, bcS (Kd d) ℂ n P.u₂} := by
  -- Over `ℂ`, `w` lies on the secant `ℙ(P_ℂ)` only, since the joint kernel of its infinitesimal
  -- stabilizer is `P_ℂ` and also the plane of any secant through `w` (`s22a_fix_iff`).
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  obtain ⟨p₁, p₂, hW'⟩ := s22a_bc_pure_pair (Kd d) ℂ (by omega) P.isPure P.isPure₂ hW
  have ha' : algebraMap (Kd d) ℂ a ≠ 0 := (map_ne_zero _).mpr ha
  have hb' : algebraMap (Kd d) ℂ b ≠ 0 := (map_ne_zero _).mpr hb
  have hwC : bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂) =
      algebraMap (Kd d) ℂ a • bcS (Kd d) ℂ n P.u₁ + algebraMap (Kd d) ℂ b • bcS (Kd d) ℂ n P.u₂ := by
    rw [map_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]
  have hann : ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) = ⊥ := by
    rw [hwC]
    exact s22a_ann_combo_eq_bot (by omega) p₁ p₂ hW' ha' hb'
  have hw0 : bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂) ≠ 0 := by
    intro h0
    have : ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) = ⊤ := by
      rw [h0]
      ext v
      simp only [Submodule.mem_top, iff_true]
      exact s22a_mem_ann.mpr (map_zero _)
    rw [hann] at this
    have hV : Module.finrank ℂ (⊥ : Submodule ℂ (V ℂ n)) = Module.finrank ℂ (V ℂ n) := by
      rw [this, finrank_top]
    rw [finrank_bot, s22a_finrank_V] at hV
    omega
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw
  have hnotpure : ¬ IsEvenPureSpinor ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) := by
    intro hp
    have := hp.2.2
    rw [hann, finrank_bot] at this
    omega
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hαβ
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hαβ
      exact hw0 hαβ.symm
    exact hnotpure (hαβ ▸ s22a_isEvenPureSpinor_smul hy hβ0)
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hαβ
    exact hnotpure (hαβ ▸ s22a_isEvenPureSpinor_smul hx hα)
  have hinf : ann ℂ n x ⊓ ann ℂ n y = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvx, hvy⟩
    have : v ∈ ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) := by
      rw [← hαβ, s22a_mem_ann, map_add, map_smul, map_smul, s22a_mem_ann.mp hvx,
        s22a_mem_ann.mp hvy, smul_zero, smul_zero, add_zero]
    rw [hann] at this
    exact this
  ext s
  rw [← s22a_fix_iff hn hx hy hinf hα hβ, hαβ, hwC, s22a_fix_iff hn p₁ p₂ hW' ha' hb']

end KSecant

end WeilClasses
