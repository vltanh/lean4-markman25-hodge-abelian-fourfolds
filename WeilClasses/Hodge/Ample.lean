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

-- The definitions `WeilClasses.eval2` and `WeilClasses.IsAmple` are in `WeilClasses.Defs`.
