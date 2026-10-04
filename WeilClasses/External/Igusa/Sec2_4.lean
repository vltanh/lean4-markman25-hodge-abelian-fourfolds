module

public import WeilClasses.Spinor.Defs
public import Mathlib.Algebra.Algebra.Rat
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action

/-!
# Igusa, *A classification of spinors up to dimension twelve*, §2 (as used in §2.4 of the paper)

J.-I. Igusa, *A classification of spinors up to dimension twelve*, Amer. J. Math. 92 (1970),
997–1028, §2: for a hyperbolic pair `e_k, e_{k+2n}` (isotropic, `(e_k, e_{k+2n}) = 1`), the
element `s_k(λ) = λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n}` of the even Clifford algebra lies in the spin group,
and its vector action multiplies `e_k` by `λ²`, `e_{k+2n}` by `λ⁻²` and fixes the orthogonal
complement of the pair (the second displayed formula of §2).

The paper uses this in Remark 2.4.3 (TeX lines 1300–1308): the product
`ϖ̃(λ) = ∏_k (λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n})` over a basis of two complementary maximal isotropic
subspaces is an element of `Spin(V_F)` mapping to `ϖ(λ)` ("apply the second displayed formula in
[Igusa, Sec. 2]"); and in §2.2 for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`. We state the one-factor case over a field `F`
of characteristic `0` (the relation of `C(V_F)` is `v² = Q(v) = ½ (v, v)_V`, i.e. the paper's
(2.1.1)).

## Proof

For a hyperbolic pair `a, b` (`Q(a) = Q(b) = 0`, `(a, b)_V = 1`) one has
`s(λ) = λ⁻¹ + (λ - λ⁻¹) a b = (a + b)(λ⁻¹ a + λ b)` in `C(V_F)` (using `a² = b² = 0`,
`ab + ba = 1`), a product of two vectors of norm `Q = 1`; so `s(λ) ∈ Spin(V_F)`
(`CliffordAlgebra.ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one`), and its vector action is the
product of the reflections in `a + b` and in `λ⁻¹ a + λ b`
(`CliffordAlgebra.spinToOrthogonal_spinReflectionPair`), which is computed directly.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- Igusa's element `s(λ) = λ⁻¹ + (λ - λ⁻¹) a b ∈ C(V_F)` for vectors `a, b ∈ V_F` and `λ ∈ F^×`. -/
noncomputable def igusaFactor (a b : V F n) (l : Fˣ) : C F n :=
  algebraMap F (C F n) ((l⁻¹ : Fˣ) : F) +
    ((l : F) - ((l⁻¹ : Fˣ) : F)) • (CliffordAlgebra.ι (Q F n) a * CliffordAlgebra.ι (Q F n) b)

/-! ## Helpers (prover SC, prefix `sc_`) -/

omit [CharZero F] in
/-- `(v, v)_V = 2 Q(v)`. -/
theorem sc_pairing_self (v : V F n) : pairing F n v v = 2 * Q F n v := by
  show QuadraticMap.polar (Q F n) v v = 2 * Q F n v
  rw [QuadraticMap.polar_self, two_nsmul]
  ring

/-- A vector isotropic for the pairing is isotropic for `Q`. -/
theorem sc_Q_eq_zero_of_pairing_self {v : V F n} (h : pairing F n v v = 0) : Q F n v = 0 := by
  rw [sc_pairing_self] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

omit [CharZero F] in
/-- `s(λ) = (a + b)(λ⁻¹ a + λ b)` for a hyperbolic pair `a, b`. -/
theorem sc_igusaFactor_eq (a b : V F n) (ha : Q F n a = 0) (hb : Q F n b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) :
    igusaFactor a b l = ι (Q F n) (a + b) * ι (Q F n) (((l⁻¹ : Fˣ) : F) • a + (l : F) • b) := by
  have hAA : ι (Q F n) a * ι (Q F n) a = 0 := by rw [ι_sq_scalar, ha, map_zero]
  have hBB : ι (Q F n) b * ι (Q F n) b = 0 := by rw [ι_sq_scalar, hb, map_zero]
  have hBA : ι (Q F n) b * ι (Q F n) a = 1 - ι (Q F n) a * ι (Q F n) b := by
    have h := ι_mul_ι_add_swap (Q := Q F n) a b
    have hab' : QuadraticMap.polar (Q F n) a b = 1 := hab
    rw [hab', map_one] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  simp only [igusaFactor, map_add, map_smul, add_mul, mul_add, mul_smul_comm, hAA, hBB, hBA,
    zero_add, add_zero, smul_sub, Algebra.algebraMap_eq_smul_one, sub_smul]
  abel

omit [CharZero F] in
theorem sc_Q_add_of_hyperbolic (a b : V F n) (ha : Q F n a = 0) (hb : Q F n b = 0)
    (hab : pairing F n a b = 1) : Q F n (a + b) = 1 := by
  have hab' : QuadraticMap.polar (Q F n) a b = 1 := hab
  rw [QuadraticMap.polar, ha, hb, sub_zero, sub_zero] at hab'
  exact hab'

omit [CharZero F] in
theorem sc_Q_smul_add_of_hyperbolic (a b : V F n) (ha : Q F n a = 0) (hb : Q F n b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) :
    Q F n (((l⁻¹ : Fˣ) : F) • a + (l : F) • b) = 1 := by
  have hab' : QuadraticMap.polar (Q F n) a b = 1 := hab
  rw [QuadraticMap.map_add (Q F n), QuadraticMap.map_smul, QuadraticMap.map_smul, ha, hb,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hab']
  simp

/-- **[Igusa 1970, §2]** (special case used in Remark 2.4.3): for a hyperbolic pair `a, b`
(`(a, a)_V = (b, b)_V = 0`, `(a, b)_V = 1`) and `λ ∈ F^×`, `s(λ) = λ⁻¹ + (λ - λ⁻¹) a b` lies in
`Spin(V_F)`. -/
theorem igusa_sec2_mem (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) : igusaFactor a b l ∈ spinGroup (Q F n) := by
  have ha' := sc_Q_eq_zero_of_pairing_self ha
  have hb' := sc_Q_eq_zero_of_pairing_self hb
  rw [sc_igusaFactor_eq a b ha' hb' hab l]
  exact ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ (by
    rw [sc_Q_add_of_hyperbolic a b ha' hb' hab, sc_Q_smul_add_of_hyperbolic a b ha' hb' hab l,
      one_mul])

/-- The vector action of `s(λ)`: the product of the reflections in `p = a + b` and in
`q = λ⁻¹ a + λ b` (both of norm `1`): `v ↦ r_p(r_q(v))` with `r_u(y) = y - (u, y)_V u`. -/
theorem sc_rho_igusaFactor (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) (v : V F n) :
    rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ v =
      (v - QuadraticMap.polar (Q F n) (((l⁻¹ : Fˣ) : F) • a + (l : F) • b) v •
          (((l⁻¹ : Fˣ) : F) • a + (l : F) • b)) -
        QuadraticMap.polar (Q F n) (a + b) (v - QuadraticMap.polar (Q F n)
          (((l⁻¹ : Fˣ) : F) • a + (l : F) • b) v • (((l⁻¹ : Fˣ) : F) • a + (l : F) • b)) •
          (a + b) := by
  have ha' := sc_Q_eq_zero_of_pairing_self ha
  have hb' := sc_Q_eq_zero_of_pairing_self hb
  have hp := sc_Q_add_of_hyperbolic a b ha' hb' hab
  have hq := sc_Q_smul_add_of_hyperbolic a b ha' hb' hab l
  have : Invertible (Q F n (a + b)) := invertibleOfNonzero (by rw [hp]; exact one_ne_zero)
  have : Invertible (Q F n (((l⁻¹ : Fˣ) : F) • a + (l : F) • b)) :=
    invertibleOfNonzero (by rw [hq]; exact one_ne_zero)
  have hg := spinToOrthogonal_eq_reflection_mul_reflection_of_coe_eq (Q := Q F n)
    (⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ : Spin F n) (a + b)
    (((l⁻¹ : Fˣ) : F) • a + (l : F) • b) (sc_igusaFactor_eq a b ha' hb' hab l)
  rw [rho, ← coe_spinToOrthogonal_apply, hg]
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply,
    TauCeti.QuadraticMap.coe_reflectionOrthogonal, TauCeti.QuadraticMap.reflection_apply,
    invOf_eq_inv, hp, hq, inv_one, one_mul]

/-- The vector action of `s(λ)` in closed form:
`ρ(s(λ)) v = v + (λ² - 1) (b, v)_V a + (λ⁻² - 1) (a, v)_V b`. -/
theorem sc_rho_igusaFactor_eq (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) (v : V F n) :
    rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ v =
      v + (((l : F) ^ 2 - 1) * pairing F n b v) • a +
        ((((l⁻¹ : Fˣ) : F) ^ 2 - 1) * pairing F n a v) • b := by
  have paa : QuadraticMap.polar (Q F n) a a = 0 := ha
  have pbb : QuadraticMap.polar (Q F n) b b = 0 := hb
  have pab : QuadraticMap.polar (Q F n) a b = 1 := hab
  have pba : QuadraticMap.polar (Q F n) b a = 1 := by rw [QuadraticMap.polar_comm]; exact pab
  have hl : ((l⁻¹ : Fˣ) : F) * (l : F) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hl' : (l : F) * ((l⁻¹ : Fˣ) : F) = 1 := by rw [mul_comm, hl]
  rw [sc_rho_igusaFactor a b ha hb hab l]
  have e1 : pairing F n b v = QuadraticMap.polar (Q F n) b v := rfl
  have e2 : pairing F n a v = QuadraticMap.polar (Q F n) a v := rfl
  rw [e1, e2]
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    paa, pbb, pab, pba, smul_eq_mul]
  linear_combination (norm := module)
    hl' • (QuadraticMap.polar (Q F n) a v • a + QuadraticMap.polar (Q F n) b v • b)

/-- **[Igusa 1970, §2, second displayed formula]** (special case used in Remark 2.4.3): the vector
action of `s(λ)` multiplies `a` by `λ²`, `b` by `λ⁻²`, and fixes every vector orthogonal to `a`
and `b`. -/
theorem igusa_sec2_rho (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) :
    rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ a = ((l : F) ^ 2) • a ∧
      rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ b =
        (((l⁻¹ : Fˣ) : F) ^ 2) • b ∧
      ∀ v : V F n, pairing F n a v = 0 → pairing F n b v = 0 →
        rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ v = v := by
  have paa : QuadraticMap.polar (Q F n) a a = 0 := ha
  have pbb : QuadraticMap.polar (Q F n) b b = 0 := hb
  have pab : QuadraticMap.polar (Q F n) a b = 1 := hab
  have pba : QuadraticMap.polar (Q F n) b a = 1 := by rw [QuadraticMap.polar_comm]; exact pab
  have hl : ((l⁻¹ : Fˣ) : F) * (l : F) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hl' : (l : F) * ((l⁻¹ : Fˣ) : F) = 1 := by rw [mul_comm, hl]
  refine ⟨?_, ?_, ?_⟩
  · rw [sc_rho_igusaFactor a b ha hb hab l]
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      paa, pbb, pab, pba, smul_eq_mul]
    linear_combination (norm := module) hl' • b
  · rw [sc_rho_igusaFactor a b ha hb hab l]
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      paa, pbb, pab, pba, smul_eq_mul]
    linear_combination (norm := module) hl' • a
  · intro v hav hbv
    have pav : QuadraticMap.polar (Q F n) a v = 0 := hav
    have pbv : QuadraticMap.polar (Q F n) b v = 0 := hbv
    rw [sc_rho_igusaFactor a b ha hb hab l]
    simp [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, pav, pbv]

end WeilClasses
