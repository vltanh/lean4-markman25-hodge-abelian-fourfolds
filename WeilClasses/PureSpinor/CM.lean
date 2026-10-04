module

public import WeilClasses.PureSpinor.Defs

/-!
# The action of `K` on `V_ℚ` attached to a `K`-secant (paper (2.2.3)–(2.2.4))

When `W₁ ∩ W₂ = 0`, `V_K = W₁ ⊕ W₂`, and `η_λ` acts on `W₁` by `λ` and on `W₂` by `σ(λ)`. It commutes
with `σ`, so it preserves `V_ℚ`; this gives `η : K → End(V_ℚ)` (2.2.4), whose restriction to `K^×`
is the paper's homomorphism `K^× → GL(V_ℚ)`. The rational similarity group `Õ(V_ℚ)` is (2.2.3).

To descend a `σ`-equivariant endomorphism of `V_K` to `V_ℚ` we take rational parts of coordinates
(`WeilClasses.Kd.ratPart`, the coefficient `a` of `a + b√-d`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (n : ℕ) (d : ℚ)

namespace Kd

theorem exists_ratPart (z : Kd d) : ∃ a : ℚ, (a : ℝ) = (z : ℂ).re := by
  sorry

/-- The rational part `a` of `z = a + b√-d ∈ K` (the real part of `z`). -/
noncomputable def ratPartFun (z : Kd d) : ℚ := Classical.choose (exists_ratPart d z)

/-- The rational part `a` of `z = a + b√-d ∈ K`, as a `ℚ`-linear map. -/
noncomputable def ratPart : Kd d →ₗ[ℚ] ℚ where
  toFun := ratPartFun d
  map_add' := by sorry
  map_smul' := by sorry

end Kd

/-- Rational parts of the coordinates of a vector of `V_K`. -/
noncomputable def ratPartV : V (Kd d) n →ₗ[ℚ] V ℚ n where
  toFun v := (∑ i, Kd.ratPart d (v.1 (e (Kd d) n i)) • f ℚ n i, fun i => Kd.ratPart d (v.2 i))
  map_add' v w := by sorry
  map_smul' c v := by sorry

/-- The rational endomorphism of `V_ℚ` induced by an endomorphism of `V_K` (meaningful when the
endomorphism commutes with `σ`, `WeilClasses.bcV_descend`). -/
noncomputable def descend (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n) : V ℚ n →ₗ[ℚ] V ℚ n :=
  ratPartV n d ∘ₗ (A.restrictScalars ℚ) ∘ₗ bcV ℚ (Kd d) n

theorem bcV_descend (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n)
    (hA : ∀ v, σV n d (A v) = A (σV n d v)) (v : V ℚ n) :
    bcV ℚ (Kd d) n (descend n d A v) = A (bcV ℚ (Kd d) n v) := by
  sorry

/-- The group `Õ(V_ℚ)` of rational similarities of `V_ℚ` with multiplier in `Nm(K^×)` (2.2.3). -/
def Otilde : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | ∃ c ∈ Kd.normGroup d, ∀ x y, pairing ℚ n (g x) (g y) = c * pairing ℚ n x y}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

namespace KSecant

variable {n d} (P : KSecant n d)

/-- The `K`-linear endomorphism `η_λ` of `V_K = W₁ ⊕ W₂`: multiplication by `λ` on `W₁` and by
`σ(λ)` on `W₂` (2.2.4); here `hW : V_K = W₁ ⊕ W₂`. -/
noncomputable def ηK (hW : IsCompl P.W₁ P.W₂) (l : Kd d) : V (Kd d) n →ₗ[Kd d] V (Kd d) n :=
  l • (P.W₁.subtype ∘ₗ Submodule.projectionOnto P.W₁ P.W₂ hW) +
    Kd.σ d l • (P.W₂.subtype ∘ₗ Submodule.projectionOnto P.W₂ P.W₁ hW.symm)

/-- The rational endomorphism `η_λ` of `V_ℚ` (2.2.4): the descent of `ηK`. -/
noncomputable def η (hW : IsCompl P.W₁ P.W₂) (l : Kd d) : V ℚ n →ₗ[ℚ] V ℚ n :=
  descend n d (P.ηK hW l)

/-- `f = η_{√-d}` (2.4.1). -/
noncomputable def fη (hW : IsCompl P.W₁ P.W₂) : V ℚ n →ₗ[ℚ] V ℚ n := P.η hW (Kd.sqrtNeg d)

end KSecant

end WeilClasses
