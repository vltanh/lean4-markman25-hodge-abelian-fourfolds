module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The imaginary quadratic field `K = ℚ(√-d)` inside `ℂ`

The paper fixes a positive rational (later integer) `d`, sets `K := ℚ(√-d)`, and chooses the square
root `√-d := √d · e^{iπ/2}` of argument `π/2` (§2.4, before (2.4.1)). We realize `K` as the subfield
of `ℂ` of the numbers `a + b √-d` with `a, b ∈ ℚ`; its embedding into `ℂ` is the inclusion, so the
paper's choice of square root is built in. The Galois involution `σ` of `K/ℚ` (§2.2) is complex
conjugation, and the norm is `Nm(λ) = λ σ(λ)`.

## Main definitions

* `WeilClasses.sqrtNeg d`: the complex number `√-d = i √d`.
* `WeilClasses.Kd d`: the subfield `ℚ(√-d)` of `ℂ`.
* `WeilClasses.Kd.σ`: the Galois involution of `K/ℚ`, the restriction of complex conjugation.
* `WeilClasses.Kd.Nm`: the norm `K → ℚ`.
-/

@[expose] public section

namespace WeilClasses

open Complex

/-- The square root `√-d := √d · e^{iπ/2} = i√d` of `-d`, with argument `π/2` (paper, §2.4). -/
noncomputable def sqrtNeg (d : ℚ) : ℂ := I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)

theorem sqrtNeg_sq {d : ℚ} (hd : 0 ≤ d) : sqrtNeg d ^ 2 = -(d : ℂ) := by
  sorry

/-- The subfield `K = ℚ(√-d)` of `ℂ`: the numbers `a + b √-d` with `a, b ∈ ℚ`. For `d ≤ 0` the
chosen square root is `0` and the set is `ℚ`; the paper always takes `d > 0`. -/
noncomputable def Kd (d : ℚ) : Subfield ℂ where
  carrier := {z | ∃ a b : ℚ, z = a + b * sqrtNeg d}
  mul_mem' := by sorry
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by sorry
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by sorry
  inv_mem' := by sorry

namespace Kd

variable (d : ℚ)

theorem mem_iff {z : ℂ} : z ∈ Kd d ↔ ∃ a b : ℚ, z = a + b * WeilClasses.sqrtNeg d := Iff.rfl

/-- The generator `√-d` as an element of `K`. -/
noncomputable def sqrtNeg : Kd d := ⟨WeilClasses.sqrtNeg d, ⟨0, 1, by simp⟩⟩

theorem conj_mem {z : ℂ} (hz : z ∈ Kd d) : (starRingEnd ℂ) z ∈ Kd d := by
  sorry

/-- The Galois involution `σ` of `K/ℚ`: the restriction of complex conjugation (paper, §2.2). -/
noncomputable def σ : Kd d ≃+* Kd d where
  toFun z := ⟨(starRingEnd ℂ) z, conj_mem d z.2⟩
  invFun z := ⟨(starRingEnd ℂ) z, conj_mem d z.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
theorem coe_σ (z : Kd d) : ((σ d z : Kd d) : ℂ) = (starRingEnd ℂ) z := rfl

theorem normSq_rat (z : Kd d) : ∃ q : ℚ, ((q : ℝ) : ℂ) = (z : ℂ) * (starRingEnd ℂ) z := by
  sorry

/-- The norm `Nm : K → ℚ`, `Nm(λ) = λ σ(λ)` (paper, §2.2). -/
noncomputable def Nm (z : Kd d) : ℚ := Classical.choose (normSq_rat d z)

theorem coe_Nm (z : Kd d) : (((Nm d z : ℚ) : ℝ) : ℂ) = (z : ℂ) * (starRingEnd ℂ) z :=
  Classical.choose_spec (normSq_rat d z)

/-- The norm group `Nm(K^×) ⊆ ℚ^×` (paper, §1.1 and (2.2.3)). -/
def normGroup : Set ℚ := {q | ∃ z : Kd d, z ≠ 0 ∧ Nm d z = q}

end Kd

noncomputable example (d : ℚ) : Algebra (Kd d) ℂ := inferInstance
noncomputable example (d : ℚ) : Algebra ℚ (Kd d) := inferInstance
example (d : ℚ) : IsScalarTower ℚ (Kd d) ℂ := inferInstance
example : IsScalarTower ℚ ℝ ℂ := inferInstance

end WeilClasses
