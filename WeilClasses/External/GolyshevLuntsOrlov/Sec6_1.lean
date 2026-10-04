module

public import WeilClasses.Orlov.Defs

/-!
# Golyshev–Lunts–Orlov, Proposition 4.3.7 and Corollary 4.3.8, as used in §6.1 of the paper

[GLO] V. Golyshev, V. Lunts, D. Orlov, *Mirror symmetry for abelian varieties*, J. Algebraic Geom.
10 (2001), 433–496, Proposition 4.3.7 and Corollary 4.3.8: the cohomological action of an
autoequivalence of `Dᵇ(X)` is an element of `Spin(V)` (the exact sequence (5.1.2)), and its action
on `H*(X × X̂)` through Orlov's equivalence preserves the decreasing filtration
`F_k = ⊕_{i ≥ k} H^i(X × X̂)`, with associated graded action the one induced from
`ρ : Spin(V) → SO(V)`. The paper uses the second part in §6.1 (TeX lines 2228–2235; "and more
directly by Lemma 6.1.1"). The exact sequence (5.1.2) is sheaf-theoretic and is left out.
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[GLO, Prop. 4.3.7, Cor. 4.3.8]** (as used in §6.1): `ρ'_g` (6.1.4) preserves the decreasing
filtration `F_k(⋀•V)` (6.1.5) and acts on `F_k / F_{k+1} = ⋀^k V` by `⋀^k ρ_g`. -/
theorem glo_prop4_3_7 (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    rhoPrime F n g x ∈ extFiltGE F n k ∧
      projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  sorry

end WeilClasses
