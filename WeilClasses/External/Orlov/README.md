# Orlov, *Derived categories of coherent sheaves on abelian varieties ...* (2002)

[Or] D. Orlov, *Derived categories of coherent sheaves on abelian varieties and equivalences between
them*, Izv. Math. 66 (2002), 569–594 (the paper's reference `orlov-abelian-varieties`), Theorem 2.10
(see also [Huybrechts, Prop. 9.39]).

## `Sec6_1.lean`: Theorem 2.10, cohomological form (prover SD)

Used in §6.1 for (6.1.8) (`equation6_1_8`, `equation6_1_8_integral`, TeX line 2249: "there exists a
topological complex line-bundle `N_g` on `X × X̂` such that `ρ'_g = ch(N_g) ∪ ρ_g`, by
[Orlov, Theorem 2.10]"), and through (6.1.8) in the proof of Lemma 6.2.3 ((6.2.4), TeX lines
2451–2456). Proved; not a hypothesis.

* `orlov_theorem2_10`, a conjunction:
  1. for every `g ∈ Spin(V_F)` (any field `F` of characteristic `0`) there is `c ∈ ⋀²V = H²(X × X̂)`
     with `ρ'_g = exp(c) ∪ ρ_g`, where `ρ'_g = φ (m_g ⊗ m†_g) φ⁻¹` is (6.1.4) (`rhoPrime`) and
     `ρ_g = ⋀ρ(g)` (`rhoExt`) — the reading under which §6.1 states (6.1.8);
  2. for every `g` in the integral group `Spin(V)` (`SpinZ n`) there is such a class `c` that is
     moreover integral (`c ∈ ExtZ n`): `N_g` is a line bundle, so `c₁(N_g) ∈ H²(X × X̂, ℤ)`. This is
     the case the paper uses (integral `g`, TeX lines 2244–2249 and 2451–2456).

  The line bundle `N_g` itself (the autoequivalence of `Dᵇ(X × X̂)`) is sheaf-theoretic and left
  out; only `c = c₁(N_g)`, its integrality and `ch(N_g) = exp(c)` appear.

Proof. In the model the statement is a consequence of the computation of `ρ'_g` behind
Proposition 6.1.2: `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g` (`sd_rhoPrime_of_lemma6_1_1`,
`WeilClasses.Orlov.Sec6_3`). That computation is the authorized algebraic proof of
Proposition 6.1.2 (through Chevalley's isomorphism, Remark 2.3.1 and the `Spin(V)`-equivariance of
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD`, Lemma 6.3.2); it does not use [Or], so citing [Or] for (6.1.8) is not
circular. It takes the identity of Lemma 6.1.1 as a hypothesis, supplied by `lemma6_1_1` (stated in
`WeilClasses.Orlov.Sec6_3`, next to Lemma 6.3.1, as the paper proves it in §6.3). For integral `g`
the class `c = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]` is integral by the remark after Proposition 6.1.2 (TeX lines
2277–2279: `c₁(𝒫)` and `(·,·)_V` agree modulo `2`; `half_c1P_sub_rho_mem_ExtZ`, also in
`WeilClasses.Orlov.Sec6_3`). §6.1 derives `equation6_1_8` from the first conjunct and
`equation6_1_8_integral` from the second.
