module

public import WeilClasses.Hodge.Defs

/-!
# Ample classes (Kähler positivity)

A class `Θ ∈ H²(X, ℚ) = ⋀² H¹(X, ℚ)` is evaluated on `a ∧ b` with `a, b ∈ H₁(X, ℝ) = H¹(X, ℝ)*`
by `⟪Θ, a ∧ b⟫ = b ⌋ (a ⌋ Θ)` (`WeilClasses.eval2`; for `Θ = x ∧ y` this is
`a(x) b(y) - a(y) b(x)`).

`Θ` is *ample* for the complex structure `J` of `H¹(X, ℝ)` (whose `i`-eigenspace is `H^{1,0}`) if it
is of type `(1,1)` and `⟪Θ, a ∧ J_T a⟫ > 0` for all `a ≠ 0`, where `J_T = Jᵀ : a ↦ a ∘ J` is the
complex structure of the tangent space `H₁(X, ℝ)`. This is Kähler positivity in the convention of
[Huybrechts, *Complex geometry*, Def. 1.2.13 and Lemma 1.2.15] (`ω(v, J v) > 0`), which the paper
cites for its sign convention (proof of Proposition 2.4.4). For the elliptic curve `ℂ/(ℤ + iℤ)`
with `H^{1,0} = ℂ (x₁ + i x₂)`, i.e. `J x₁ = -x₂`, `J x₂ = x₁`, the class `x₁ ∧ x₂ = [pt]` is
ample: `⟪x₁ ∧ x₂, λ₁ ∧ λ₁ ∘ J⟫ = ⟪x₁ ∧ x₂, λ₁ ∧ λ₂⟫ = 1`.
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-0 coefficient), for `ξ ∈ S_F` and `a, b ∈ H¹(X, F)*`. On
`⋀² H¹` this is the pairing with `⋀² H₁`: `⟪x ∧ y, a ∧ b⟫ = a(x) b(y) - a(y) b(x)`. -/
noncomputable def eval2 (ξ : S F n) (a b : Module.Dual F (H1 F n)) : F :=
  (basisS F n).coord ∅ (D F n b (D F n a ξ))

/-- `Θ ∈ H²(X, ℚ)` is ample for the complex structure `J` of `H¹(X, ℝ)`: of type `(1,1)` and
`⟪Θ, a ∧ (a ∘ J)⟫ > 0` for every nonzero `a ∈ H₁(X, ℝ) = H¹(X, ℝ)*`. -/
def IsAmple (J : Module.End ℝ (H1 ℝ n)) (Θ : S ℚ n) : Prop :=
  Θ ∈ hodgeClassesX n J 1 ∧
    ∀ a : Module.Dual ℝ (H1 ℝ n), a ≠ 0 → 0 < eval2 ℝ n (bcS ℚ ℝ n Θ) a (a ∘ₗ J)

end WeilClasses
