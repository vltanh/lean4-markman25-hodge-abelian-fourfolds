module

public import WeilClasses.Chevalley.Defs

/-!
# Trautman, Theorem 1(i), as used in Remark 2.3.1 of the paper

[TT] A. Trautman, K. Trautman, *Generalized pure spinors*, J. Geom. Phys. 15 (1994), 1–22,
Theorem 1(i) (the paper's reference `trautman`, where `φ̃` is denoted by `E`): over a field of
characteristic zero, the isomorphism `E : S ⊗ S → ⋀•V` obtained from Chevalley's
`φ : S ⊗ S → C(V)` (2.2.5) by composing with the symmetric identification `C(V) ≅ ⋀•V` (the change
of form by `-½(·,·)_V`, Mathlib's `CliffordAlgebra.equivExterior`) is `Spin(V)`-equivariant, for
`m ⊗ m` on `S ⊗ S` and the grading-preserving action `⋀ρ` on `⋀•V`.

Used in Remark 2.3.1 ("In that case the resulting isomorphism `S_ℚ ⊗ S_ℚ → ⋀•V_ℚ` is
`Spin(V)`-equivariant ... (see [Trautman, Th. 1(i)])"), and, through the authorized algebraic proof
of Proposition 6.1.2, in §6.1.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Trautman, Th. 1(i)]**, the special case used in Remark 2.3.1: `E = equivExterior ∘ φ`
(`varphiTildeSym`) satisfies `E((m_g ⊗ m_g)(y)) = ρ_g(E(y))` for `g ∈ Spin(V_F)`. -/
theorem trautman_theorem1_i (g : Spin F n) (y : S F n ⊗[F] S F n) :
    varphiTildeSym F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y) =
      rhoExt F n g (varphiTildeSym F n y) := by
  sorry

end WeilClasses
