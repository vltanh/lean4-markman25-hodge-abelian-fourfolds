module

public import WeilClasses.Orlov.Defs

/-!
# §1.3: Orlov's equivalence and the representations `ρ`, `ρ'` (introduction)

Statements of the introduction's §1.3 (TeX lines 403–452): Proposition 1.3.1, the commutativity of
Diagram (1.3.1) and the `Spin(V)`-equivariance of `φ̃` (1.3.2) (`phiTildeIntro`). In the
introduction `ρ'_g` is *defined* by the explicit formula `exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`
(`rhoPrimeFormula`); §6.1 defines it as `φ (m_g ⊗ m†_g) φ⁻¹` (6.1.4) and proves the formula
(Prop. 6.1.2).

**Correction of a misprint** (agreed with the project owner; REPORT.md). As printed, the
introduction makes `φ ∘ (id ⊗ τ)` equivariant from `m ⊗ m†` (Prop. 1.3.1, the lower square of
(1.3.1)) and `φ̃` (1.3.2) equivariant from `m ⊗ m†`. This is false (`n = 1`, `g = 1 + e₁e₂`,
`y = 1 ⊗ 1`). What holds, and what §6.1 ((6.1.4) with Prop. 6.1.2), §6.4 and the proof of
Corollary 1.3.2 use, is that `φ` is equivariant from `m ⊗ m†`, i.e. `φ ∘ (id ⊗ τ)` and `φ̃` are
equivariant from `m ⊗ m`; these are the statements below.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **Proposition 1.3.1** (no label; = Lemma 6.1.1 + Proposition 6.1.2), first claim: the
isomorphism `φ` given in (1.2.5), `φ = (φ_𝒫 ⊗ φ_𝒫⁻¹) ∘ φ̃ ∘ (id ⊗ τ)`, is equal to the isomorphism
induced by Orlov's equivalence `Φ`.

Reading: in the model the isomorphism induced by `Φ` is `phiOrlov = (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*`, and
(1.2.5) is read as in Lemma 6.1.1: `φ̃` lands in `H*(X̂ × X)` (as in §6.3), `φ_𝒫 : H*(X̂) → H*(X)`
acts
on the `X̂`-factor and `φ_𝒫⁻¹ = ψ_{𝒫⁻¹[n]} : H*(X) → H*(X̂)` on the `X`-factor. (Reading `φ̃` as
landing in `H*(X × X̂)` with `φ_𝒫 : H*(X) → H*(X̂)` on its `X`-factor and the inverse on the other
gives `(-1)^d` times this map on `H^d(X × X̂)` — checked numerically for `n = 1, 2`; the sign is
irrelevant for the equivariance claims below, `ρ'_g` preserving parity.) So this is
`lemma6_1_1`. -/
theorem proposition1_3_1_eq : phiOrlov F n = PiMap F n ∘ₗ varphiTilde F n ∘ₗ tauTensor F n := by
  sorry

/-- **Proposition 1.3.1** (no label), second claim: `φ ∘ (id ⊗ τ)` is `Spin(V)`-equivariant, where
the domain is the representation `m ⊗ m` and the codomain is `ρ'`
(`ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`, the introduction's definition); equivalently, `φ` is
equivariant from `m ⊗ m†`. This is also the commutativity of the lower square of Diagram (1.3.1).

Correction of a misprint (REPORT.md): the paper prints the domain representation `m ⊗ m†` for
`φ ∘ (id ⊗ τ)`, which is false (`n = 1`, `g = 1 + e₁e₂`, `y = 1 ⊗ 1`); `m ⊗ m` agrees with (6.1.4),
§6.4 and the proof of Corollary 1.3.2. -/
theorem proposition1_3_1_equivariant (g : Spin F n) (y : S F n ⊗[F] S F n) :
    phiPrime F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y) =
      rhoPrimeFormula F n g (phiPrime F n y) := by
  sorry

/-- **Diagram (1.3.1)** (`eq-diagram-of-rho-and-rho-prime`), upper square: cup product with
`exp(-½c₁(𝒫))` intertwines `ρ'_g` with `ρ_g` on `H*(X × X̂, ℚ)`; hence `ρ` and `ρ'` are isomorphic
after tensoring with `ℚ`. (The lower square is `proposition1_3_1_equivariant`.) -/
theorem diagram1_3_1_upper (g : Spin F n) (x : ExtV F n) :
    IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * rhoPrimeFormula F n g x =
      rhoExt F n g (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x) := by
  sorry

/-- **(1.3.2)** (`eq-tilde-phi`): `φ̃ = exp(-c₁(𝒫)/2) ∪ φ ∘ (id ⊗ τ)` is `Spin(V)`-equivariant, where
the domain is the representation `m ⊗ m` and the codomain is `ρ` (the outer square of Diagram
(1.3.1)). Correction of a misprint: the paper prints `m ⊗ m†` (see `proposition1_3_1_equivariant`). -/
theorem equation1_3_2_equivariant (g : Spin F n) (y : S F n ⊗[F] S F n) :
    phiTildeIntro F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y) =
      rhoExt F n g (phiTildeIntro F n y) := by
  sorry

end Field

end WeilClasses
