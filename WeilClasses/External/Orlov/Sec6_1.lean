module

public import WeilClasses.Orlov.Defs
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
`H²(X × X̂) = ⋀²V`. The existence of the line bundles themselves is left out. In the paper's route
this is used for (6.1.8) and in the proof of Lemma 6.2.3; in the model it is also a consequence of
Proposition 6.1.2.

**Proof** (Stage 2, prover SD). In the model the statement follows from the computation of `ρ'_g`
that proves Proposition 6.1.2: `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`
(`sd_rhoPrime_of_lemma6_1_1`, `WeilClasses.Orlov.Sec6_3`), whose proof (the authorized algebraic
argument through Chevalley's isomorphism, Remark 2.3.1 and Lemma 6.3.2) does not use
[Orlov, Th. 2.10]. That computation takes the identity of Lemma 6.1.1 as a hypothesis; it is
re-derived here from Lemma 6.3.1 and `φ = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ ν` exactly as in the paper's proof of
Lemma 6.1.1 (`lemma6_1_1` itself is stated in `WeilClasses.Orlov.Sec6_1`, which imports this file to
cite the theorem for (6.1.8)).
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Orlov, Th. 2.10]** (cohomological form, (6.1.8)): for every `g ∈ Spin(V)` there is
`c ∈ H²(X × X̂) = ⋀²V` (the first Chern class of a line bundle `N_g`) with `ρ'_g = exp(c) ∪ ρ_g`.
Proof in the model: `c = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]`, by the algebraic computation of `ρ'_g` behind
Proposition 6.1.2 (`sd_rhoPrime_of_lemma6_1_1`), which does not use this theorem. -/
theorem orlov_theorem2_10 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x := by
  -- the identity of Lemma 6.1.1, by its proof in the paper (Lemma 6.3.1 and `φ = Π ∘ ν`)
  have hφ : phiOrlov F n = PiMap F n ∘ₗ varphiTilde F n ∘ₗ tauTensor F n := by
    rw [← lemma6_3_1, LinearMap.comp_assoc, tauTensor_comp_tauTensor, LinearMap.comp_id,
      phiOrlov_eq_PiMap_comp_nuOrlov]
  exact ⟨_, s61_beta_mem F n g, sd_rhoPrime_of_lemma6_1_1 F n hφ g⟩

end WeilClasses
