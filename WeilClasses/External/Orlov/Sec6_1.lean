module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Spinor.Integral
import WeilClasses.Orlov.Sec6_3

/-!
# Orlov, *Derived categories of coherent sheaves on abelian varieties ...*, Theorem 2.10, as used in
§6.1

[Or] D. Orlov, *Derived categories of coherent sheaves on abelian varieties and equivalences between
them*, Izv. Math. 66 (2002), Theorem 2.10 (see also [Huybrechts, FM transforms, Prop. 9.39]): the
autoequivalences of `Dᵇ(X)` act on `Dᵇ(X × X̂)` (through Orlov's equivalence) by push-forward along
an automorphism of `X × X̂` followed by tensorization with a line bundle `N_g`. Cohomologically, for
`g ∈ Spin(V)`: `ρ'_g = ch(N_g) ∪ ρ_g` (6.1.8).

In the model, `ρ'_g` is (6.1.4) (`rhoPrime`) and `ch(N_g) = exp(c)` for a class `c = c₁(N_g)` in
`H²(X × X̂) = ⋀²V`. The existence of the line bundles themselves is left out; that `N_g` is a line
bundle is kept as the integrality of `c₁(N_g)` for `g` in the integral group `Spin(V)`
(`SpinZ`), the case the paper uses (TeX lines 2244–2249 for (6.1.8); TeX lines 2451–2456 in the
proof of Lemma 6.2.3). The identity itself is also stated over every field `F` of characteristic
`0`, the reading under which §6.1 states (6.1.8) (`equation6_1_8`).

**Proof** (Stage 2, prover SD). In the model the statement follows from the computation of `ρ'_g`
that proves Proposition 6.1.2: `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`
(`sd_rhoPrime_of_lemma6_1_1`, `WeilClasses.Orlov.Sec6_3`), whose proof (the authorized algebraic
argument through Chevalley's isomorphism, Remark 2.3.1 and Lemma 6.3.2) does not use
[Orlov, Th. 2.10]. That computation takes the identity of Lemma 6.1.1 as a hypothesis, supplied by
`lemma6_1_1` (`WeilClasses.Orlov.Sec6_3`, where the paper proves it). For integral `g` the class
`½[c₁(𝒫) - ρ_g(c₁(𝒫))]` is integral by the remark after Proposition 6.1.2 (TeX lines 2277–2279:
`c₁(𝒫)` and `(·,·)_V` agree modulo `2`; `half_c1P_sub_rho_mem_ExtZ`, `WeilClasses.Orlov.Sec6_3`).
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Orlov, Th. 2.10]** (cohomological form, (6.1.8)): for every `g ∈ Spin(V)` there is a line
bundle `N_g` on `X × X̂` with `ρ'_g = ch(N_g) ∪ ρ_g`. In the model: a class
`c = c₁(N_g) ∈ H²(X × X̂) = ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g`, for `g ∈ Spin(V_F)` over every field
`F` of characteristic `0` (first conjunct); and for `g` in the integral group `Spin(V)` the class
`c₁(N_g)` is integral, `N_g` being a line bundle (second conjunct; the case the paper uses, TeX
lines 2244–2249 and 2451–2456).
Proof in the model: `c = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]`, by the algebraic computation of `ρ'_g` behind
Proposition 6.1.2 (`sd_rhoPrime_of_lemma6_1_1`, applied to Lemma 6.1.1), which does not use this
theorem; for integral `g` this class is integral (`half_c1P_sub_rho_mem_ExtZ`). -/
theorem orlov_theorem2_10 :
    (∀ g : Spin F n, ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x) ∧
    ∀ g ∈ SpinZ n, ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧ ∀ x : ExtV ℚ n,
      rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x :=
  ⟨fun g => ⟨_, s61_beta_mem F n g, sd_rhoPrime_of_lemma6_1_1 F n (lemma6_1_1 F n) g⟩,
    fun g hg => ⟨_, s61_beta_mem ℚ n g, half_c1P_sub_rho_mem_ExtZ n g hg,
      sd_rhoPrime_of_lemma6_1_1 ℚ n (lemma6_1_1 ℚ n) g⟩⟩

end WeilClasses
