# Orlov, *Derived categories of coherent sheaves on abelian varieties ...* (2002)

[Or] D. Orlov, *Derived categories of coherent sheaves on abelian varieties and equivalences between
them*, Izv. Math. 66 (2002), 569–594 (the paper's reference `orlov-abelian-varieties`), Theorem 2.10
(see also [Huybrechts, Prop. 9.39]).

## `Sec6_1.lean`: Theorem 2.10, cohomological form (prover SD)

Used in §6.1 for (6.1.8) (`equation6_1_8`, TeX line 2249: "there exists a topological complex
line-bundle `N_g` on `X × X̂` such that `ρ'_g = ch(N_g) ∪ ρ_g`, by [Orlov, Theorem 2.10]"). Proved;
not a hypothesis.

* `orlov_theorem2_10`: for every `g ∈ Spin(V_F)` (any field `F` of characteristic `0`) there is
  `c ∈ ⋀²V = H²(X × X̂)` with `ρ'_g = exp(c) ∪ ρ_g`, where `ρ'_g = φ (m_g ⊗ m†_g) φ⁻¹` is (6.1.4)
  (`rhoPrime`) and `ρ_g = ⋀ρ(g)` (`rhoExt`). The line bundle `N_g` itself (the autoequivalence of
  `Dᵇ(X × X̂)`) is sheaf-theoretic and left out; only `c = c₁(N_g)` and `ch(N_g) = exp(c)` appear.

Proof. In the model the statement is a consequence of the computation of `ρ'_g` behind
Proposition 6.1.2: `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g` (`sd_rhoPrime_of_lemma6_1_1`,
`WeilClasses.Orlov.Sec6_3`). That computation is the authorized algebraic proof of
Proposition 6.1.2 (through Chevalley's isomorphism, Remark 2.3.1 and the `Spin(V)`-equivariance of
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD`, Lemma 6.3.2); it does not use [Or], so citing [Or] for (6.1.8) is not
circular. It takes the identity of Lemma 6.1.1 as a hypothesis, which this file re-derives from
Lemma 6.3.1 exactly as in the paper's proof of Lemma 6.1.1 (`lemma6_1_1` itself lives in
`WeilClasses.Orlov.Sec6_1`, which imports this file). The integrality of `c₁(N_g)` for `g` in the
integral group (`equation6_1_8_integral`) is not part of this statement; §6.1 proves it from
Proposition 6.1.2 and the integrality of `½[c₁(𝒫) - ρ_g(c₁(𝒫))]`.
