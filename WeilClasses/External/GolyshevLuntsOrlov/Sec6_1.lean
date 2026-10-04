module

public import WeilClasses.Orlov.Defs
import WeilClasses.Orlov.Basis
import WeilClasses.External.Orlov.Sec6_1

/-!
# Golyshev–Lunts–Orlov, Proposition 4.3.7 and Corollary 4.3.8, as used in §6.1 of the paper

[GLO] V. Golyshev, V. Lunts, D. Orlov, *Mirror symmetry for abelian varieties*, J. Algebraic Geom.
10 (2001), 433–496, Proposition 4.3.7 and Corollary 4.3.8: the cohomological action of an
autoequivalence of `Dᵇ(X)` is an element of `Spin(V)` (the exact sequence (5.1.2)), and its action
on `H*(X × X̂)` through Orlov's equivalence preserves the decreasing filtration
`F_k = ⊕_{i ≥ k} H^i(X × X̂)`, with associated graded action the one induced from
`ρ : Spin(V) → SO(V)`. The paper uses the second part in §6.1 (TeX lines 2228–2235; "and more
directly by Lemma 6.1.1"). The exact sequence (5.1.2) is sheaf-theoretic and is left out.

**Proof** (Stage 2, prover SD). In the model the filtration statement follows from the cohomological
form of [Orlov, Th. 2.10] (`orlov_theorem2_10`, proved in the model from the computation of `ρ'_g`
behind Proposition 6.1.2, which does not use [GLO]): `ρ'_g = exp(c) ∪ ρ_g` with `c ∈ ⋀²V`, so
`ρ'_g(x) - ρ_g(x) = (exp(c) - 1) ∪ ρ_g(x) ∈ F_{k+2}` for `x ∈ F_k`, and `ρ_g` preserves the grading.
(§6.1 itself proves these claims through Lemma 6.1.1, the paper's "more direct" route, and does not
cite this theorem.)
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[GLO, Prop. 4.3.7, Cor. 4.3.8]** (as used in §6.1): `ρ'_g` (6.1.4) preserves the decreasing
filtration `F_k(⋀•V)` (6.1.5) and acts on `F_k / F_{k+1} = ⋀^k V` by `⋀^k ρ_g`.
Proof in the model: `ρ'_g = exp(c) ∪ ρ_g` with `c ∈ ⋀²V` ([Orlov, Th. 2.10], `orlov_theorem2_10`),
and `exp(c) - 1 ∈ F_2`. -/
theorem glo_prop4_3_7 (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    rhoPrime F n g x ∈ extFiltGE F n k ∧
      projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  obtain ⟨c, hc, h⟩ := orlov_theorem2_10 F n g
  have h1 := s61_exp_sub_one_mem F n hc
  have h2 := s61_rhoExt_mem_extFiltGE F n g hx
  -- `(exp(c) - 1) ∪ ρ_g(x) ∈ F_{k+2} ⊆ F_{k+1}`
  have h3 : (IsNilpotent.exp c - 1) * rhoExt F n g x ∈ extFiltGE F n (k + 1) :=
    s61_extFiltGE_mono F n (by omega) (s61_mul_mem_extFiltGE F n h1 h2)
  rw [h, ← sub_add_cancel (IsNilpotent.exp c) 1, add_mul, one_mul]
  refine ⟨add_mem (s61_extFiltGE_mono F n (by omega) h3) h2, ?_⟩
  rw [map_add, s61_projDeg_eq_zero_of_mem_extFiltGE F n h3, zero_add, s61_projDeg_rhoExt]

end WeilClasses
