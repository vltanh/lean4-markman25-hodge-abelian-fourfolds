module

public import WeilClasses.Orlov.Defs

/-!
# Orlov, *Derived categories of coherent sheaves on abelian varieties ...*, Theorem 2.10, as used in
§6.1

[Or] D. Orlov, *Derived categories of coherent sheaves on abelian varieties and equivalences between
them*, Izv. Math. 66 (2002), Theorem 2.10 (see also [Huybrechts, FM transforms, Prop. 9.39]): the
autoequivalences of `Dᵇ(X)` act on `Dᵇ(X × X̂)` (through Orlov's equivalence) by push-forward along
an automorphism of `X × X̂` followed by tensorization with a line bundle `N_g`. Cohomologically, for
`g ∈ Spin(V)`: `ρ'_g = ch(N_g) ∪ ρ_g` (6.1.8).

In the model, `ρ'_g` is (6.1.4) (`rhoPrime`) and `ch(N_g) = exp(c)` for a class `c = c₁(N_g)` in
`H²(X × X̂) = ⋀²V`. The existence of the line bundles themselves is left out. In the paper's route
this is used for (6.1.8) and in the proof of Lemma 6.2.3; in the model it is also a consequence of
Proposition 6.1.2.
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Orlov, Th. 2.10]** (cohomological form, (6.1.8)): for every `g ∈ Spin(V)` there is
`c ∈ H²(X × X̂) = ⋀²V` (the first Chern class of a line bundle `N_g`) with `ρ'_g = exp(c) ∪ ρ_g`. -/
theorem orlov_theorem2_10 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x := by
  sorry

end WeilClasses
