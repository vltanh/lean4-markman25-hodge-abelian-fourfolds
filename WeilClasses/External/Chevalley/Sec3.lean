module

public import WeilClasses.PureSpinor.Defs

/-!
# Chevalley, *The algebraic theory of spinors*, III.3.2 and III.4.5 (as used in §3.1 of the paper)

C. Chevalley, *The algebraic theory of spinors*, Columbia University Press (1954), III.3.2 and
III.4.5: there is a `Spin(V)`-equivariant homomorphism `⋀^{2n}_+ V → Sym²(S⁺)`, defined on the
span of the lines `⋀^{2n} W` of the maximal isotropic subspaces `W` (of the family of `S⁺`), which
maps `⋀^{2n} W` onto the line spanned by `u²`, `u` the even pure spinor with `ker m_u = W`.

The paper uses it in the proof of Lemma 3.1.1 (TeX lines 1481–1486) in the following form: if
`g ∈ Spin(V)` preserves `W = ker m_u`, then `g` acts on the line of `u²` as `⋀^{2n} ρ(g)` acts on
`⋀^{2n} W`, i.e. by `det(ρ(g)|_W)`; so `g u = c u` with `c² = det(ρ(g)|_W)` (in particular
`c = ±1` when `det(ρ(g)|_W) = 1`). This is also the relation `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` of §2.2. We state
this consequence over a field `F` of characteristic `0`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, *The algebraic theory of spinors*, III.3.2 and III.4.5]**, in the form used in
the proof of Lemma 3.1.1: for an even pure spinor `u ∈ S⁺_F` with maximal isotropic
`W = ker m_u`, and `g ∈ Spin(V_F)` with `ρ(g)(W) ⊆ W`, we have `m(g) u = c u` for a scalar `c` with
`c² = det(ρ(g)|_W)`. -/
theorem chevalley_III_3_2_III_4_5 (u : S F n) (hu : IsEvenPureSpinor F n u) (g : Spin F n)
    (hg : ∀ v ∈ ann F n u, rho F n g v ∈ ann F n u) :
    ∃ c : F, m F n (g : C F n) u = c • u ∧
      c ^ 2 = LinearMap.det ((rho F n g : V F n →ₗ[F] V F n).restrict hg) := by
  sorry

end WeilClasses
