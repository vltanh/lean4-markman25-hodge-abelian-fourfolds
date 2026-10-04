module

public import WeilClasses.Orlov.Defs

/-!
# Huybrechts, *Fourier–Mukai transforms*, Exercise 9.41, as used in §6.1

[Hu] D. Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Oxford, 2006, Exercise 9.41:
the line bundles `N_g` of [Orlov, Th. 2.10] (see `WeilClasses.External.Orlov.Sec6_1`) satisfy the
cocycle identity `c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`. Used in §6.1 for (6.1.9).

In the model, `c₁(N_g)` is a class `c ∈ ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g` (6.1.8) (it is unique:
`exp(c) = ρ'_g(1)`). The other results of [Hu] cited in §5–§6.1 (Rem. 7.7, Cor. 9.37, Prop. 9.39)
concern derived categories and are left out (Prop. 9.39 is (6.1.8), see
`WeilClasses.External.Orlov.Sec6_1`).
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Huybrechts, Ex. 9.41]** (used for (6.1.9)): if `c₁, c₂, c₁₂ ∈ ⋀²V` satisfy (6.1.8) for
`g₁, g₂, g₁g₂`, then `c₁₂ = c₁ + ρ_{g₁}(c₂)`. -/
theorem huybrechts_ex9_41 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ := by
  sorry

end WeilClasses
