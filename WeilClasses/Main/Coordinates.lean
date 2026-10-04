module

public import WeilClasses.AbelianVariety.Defs

/-!
# `X × X̂` as an abelian `2n`-fold of the model

`V_F = H¹(X̂, F) ⊕ H¹(X, F) = H¹(X × X̂, F)` has dimension `4n`, so `X × X̂` and its deformations as
abelian varieties of Weil type are abelian `2n`-folds whose `H¹` is `V_ℚ`. The coordinate isomorphism
`coordV : V_F ≃ F^{4n} = H1 F (2n)` sends the basis `basisV` (`f₁, …, f_{2n}, e₁, …, e_{2n}`) to the
standard basis, so that complex structures, classes and endomorphisms of `V` become those of the
model (`WeilClasses.AbVar (2 * n)`).

Also: the class `Θ = e₁ ∧ e₂ + e₃ ∧ e₄ + ⋯ + e_{2n-1} ∧ e_{2n}` of a principal polarization in
symplectic coordinates (`WeilClasses.ThetaStd`), with `Θⁿ/n! = [pt]` for the orientation
`∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1`.
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `Θⁿ = n! [pt]` for `ThetaStd`: the orientation `∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1` is the one for which `Θ`
has degree `Θⁿ/n! = 1`. -/
theorem ThetaStd_pow : ThetaStd F n ^ n = (n.factorial : F) • pt F n := by
  sorry

end WeilClasses
