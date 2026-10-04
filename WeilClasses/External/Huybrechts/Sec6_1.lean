module

public import WeilClasses.Orlov.Defs
import WeilClasses.Orlov.Basis

/-!
# Huybrechts, *Fourier–Mukai transforms*, Exercise 9.41, as used in §6.1

[Hu] D. Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Oxford, 2006, Exercise 9.41:
the line bundles `N_g` of [Orlov, Th. 2.10] (see `WeilClasses.External.Orlov.Sec6_1`) satisfy the
cocycle identity `c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`. Used in §6.1 for (6.1.9).

In the model, `c₁(N_g)` is a class `c ∈ ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g` (6.1.8) (it is unique:
`exp(c) = ρ'_g(1)`). The other results of [Hu] cited in §5–§6.1 (Rem. 7.7, Cor. 9.37, Prop. 9.39)
concern derived categories and are left out (Prop. 9.39 is (6.1.8), see
`WeilClasses.External.Orlov.Sec6_1`).

**Proof** (Stage 2, prover SD; the argument of the exercise): `ρ'` is a representation
(`rhoPrimeRep`, (6.1.7)), so `ρ'_{g₁g₂}(1) = ρ'_{g₁}(ρ'_{g₂}(1))`, i.e.
`exp(c₁₂) = exp(c₁) ∪ ρ_{g₁}(exp(c₂)) = exp(c₁ + ρ_{g₁}(c₂))` (`ρ_{g₁}` is an algebra automorphism
and classes of degree `2` commute); the degree-`2` parts give `c₁₂ = c₁ + ρ_{g₁}(c₂)`
(`s61_projDeg_two_exp`). This uses neither Proposition 6.1.2 nor [Orlov, Th. 2.10].
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Huybrechts, Ex. 9.41]** (used for (6.1.9)): if `c₁, c₂, c₁₂ ∈ ⋀²V` satisfy (6.1.8) for
`g₁, g₂, g₁g₂`, then `c₁₂ = c₁ + ρ_{g₁}(c₂)`.
Proof: evaluate `ρ'_{g₁g₂} = ρ'_{g₁} ρ'_{g₂}` (`ρ'` is a representation) at `1` and compare the
degree-`2` parts of `exp(c₁₂) = exp(c₁ + ρ_{g₁}(c₂))`. -/
theorem huybrechts_ex9_41 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ := by
  -- `ρ'` is a representation: `ρ'_{g₁g₂} = ρ'_{g₁} ρ'_{g₂}`; evaluate at `1`
  have hrep : rhoPrime F n (g₁ * g₂) 1 = rhoPrime F n g₁ (rhoPrime F n g₂ 1) := by
    have h := (rhoPrimeRep F n).map_mul g₁ g₂
    have h' : rhoPrime F n (g₁ * g₂) = rhoPrime F n g₁ * rhoPrime F n g₂ := h
    rw [h', Module.End.mul_apply]
  have hρc₂ := s61_rhoExt_mem F n g₁ hc₂
  have hcomm : Commute c₁ (rhoExt F n g₁ c₂) := by
    have := s61_mul_comm_of_mem hc₁ hρc₂
    show c₁ * _ = _ * c₁
    rw [this, show (2 * 2 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  have e1 : rhoPrime F n (g₁ * g₂) 1 = IsNilpotent.exp c₁₂ := by
    rw [h₁₂, map_one, mul_one]
  have e2 : rhoPrime F n g₂ 1 = IsNilpotent.exp c₂ := by
    rw [h₂, map_one, mul_one]
  have e3 : rhoPrime F n g₁ (IsNilpotent.exp c₂) = IsNilpotent.exp (c₁ + rhoExt F n g₁ c₂) := by
    rw [h₁, IsNilpotent.map_exp (s61_isNilpotent_of_mem_two F n hc₂) (rhoExt F n g₁),
      IsNilpotent.exp_add_of_commute hcomm (s61_isNilpotent_of_mem_two F n hc₁)
        (s61_isNilpotent_of_mem_two F n hρc₂)]
  rw [e1, e2, e3] at hrep
  have := congrArg (projDeg F n 2) hrep
  rwa [s61_projDeg_two_exp F n hc₁₂, s61_projDeg_two_exp F n (add_mem hc₁ hρc₂)] at this

end WeilClasses
