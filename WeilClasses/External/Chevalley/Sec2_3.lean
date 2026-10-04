module

public import WeilClasses.Chevalley.Defs

/-!
# Chevalley, *The algebraic theory of spinors*, results used in §2.3 (and §6.1–6.3) of the paper

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954.
The quadratic space is `V_F = H¹(X̂, F) ⊕ H¹(X, F)` with `Q(θ, w) = θ(w)`, over a field `F` of
characteristic zero (the paper uses these results over `ℚ`, deducing the integral statements).

* [II.1.6] For a bilinear form `B` on `V` with `B(u, u) = Q(u)`, the map
  `ψ_B = changeForm(-B) : C(V) → ⋀•V` (`ψ_B(v x) = v ∧ ψ_B(x) + B(v, ·) ⌋ ψ_B(x)`, `ψ_B(1) = 1`;
  Chevalley's `λ`, [Bourbaki, §9]) maps `C(V)_k` into `F^k(⋀•V)` and induces isomorphisms
  `C(V)_k / C(V)_{k-1} ≅ ⋀^k V` (`chevalley_II_1_6_*`). Used in §2.3 for `B = B₀`.
* [Sec. 3.3] These graded isomorphisms are `Spin(V)`-equivariant, for the conjugation action on
  `C(V)` and `⋀^k ρ` on `⋀^k V` (`chevalley_sec3_3_*`). Used in §2.3.
* [p. 85, discussion after III.3.1] The `Spin(V)`-action on `⋀•V` transported by
  `ψ_B ∘ φ : S ⊗ S → ⋀•V` preserves `F^k(⋀•V)`, with associated graded action `⋀ρ`, independent of
  `B` (`chevalley_p85_transport_graded`). Used in §2.3 (and, through Lemma 6.1.1, in §6.1).
* [III.3.1] `φ : S ⊗ S → C(V)` (2.2.5) is an isomorphism of `Spin(V)`-representations: stated in
  `WeilClasses.External.Chevalley.Sec2_2` (`chevalley_III_3_1_bijective`,
  `chevalley_III_3_1_equivariant`), where §2.2 first uses it; §2.3 uses it as well.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, II.1.6]** (filtration): for a bilinear form `B` on `V` with `B(u, u) = Q(u)`,
`ψ_B = changeForm(-B)` maps `C(V)_k` into `F^k(⋀•V)`. Special case `B = B₀`: §2.3, TeX line 1064. -/
theorem chevalley_II_1_6_filtration (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {x : C F n}
    (hx : x ∈ CFilt F n k) : CliffordAlgebra.changeForm hB x ∈ extFiltLE F n k := by
  sorry

/-- **[Chevalley, II.1.6]** (surjectivity of the graded map): `C(V)_k / C(V)_{k-1} → ⋀^k V`,
`x ↦ degree-k component of ψ_B(x)`, is surjective. Special case `B = B₀`: §2.3, TeX line 1067. -/
theorem chevalley_II_1_6_surjective (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {y : ExtV F n}
    (hy : y ∈ ⋀[F]^k (V F n)) :
    ∃ x ∈ CFilt F n k, projDeg F n k (CliffordAlgebra.changeForm hB x) = y := by
  sorry

/-- **[Chevalley, II.1.6]** (injectivity of the graded map): for `x ∈ C(V)_k`, the degree-`k`
component of `ψ_B(x)` vanishes iff `x ∈ C(V)_{k-1}`. Special case `B = B₀`: §2.3, TeX line 1068
("it induces an isomorphism once we tensor with `ℚ`"). -/
theorem chevalley_II_1_6_injective (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {x : C F n}
    (hx : x ∈ CFilt F n k) :
    projDeg F n k (CliffordAlgebra.changeForm hB x) = 0 ↔ x ∈ CFiltLT F n k := by
  sorry

/-- **[Chevalley, Sec. 3.3]**: conjugation by `Spin(V)` preserves the filtration `C(V)_k`.
Used in §2.3, TeX line 1069. -/
theorem chevalley_sec3_3_conj_mem (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    conjSpin F n g x ∈ CFilt F n k := by
  sorry

/-- **[Chevalley, Sec. 3.3]**: the graded isomorphism `C(V)_k / C(V)_{k-1} ≅ ⋀^k V` induced by
`ψ_B` is `Spin(V)`-equivariant (conjugation on `C(V)`, `⋀^k ρ` on `⋀^k V`). Special case `B = B₀`:
§2.3, TeX line 1069. -/
theorem chevalley_sec3_3_equivariant (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (g : Spin F n) (k : ℕ)
    {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (CliffordAlgebra.changeForm hB (conjSpin F n g x)) =
      rhoExt F n g (projDeg F n k (CliffordAlgebra.changeForm hB x)) := by
  sorry

/-- **[Chevalley, p. 85]** (discussion following the proof of III.3.1): the `Spin(V)`-action on
`⋀•V` obtained from `m ⊗ m` by conjugating with `ψ_B ∘ φ` preserves `F^k(⋀•V)`, and its associated
graded action is `⋀ρ`, whatever `B` is. Special case `B = B₀`: §2.3, TeX lines 1074–1077. -/
theorem chevalley_p85_transport_graded (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (g : Spin F n) (k : ℕ)
    (y : S F n ⊗[F] S F n) (hy : CliffordAlgebra.changeForm hB (varphi F n y) ∈ extFiltLE F n k) :
    CliffordAlgebra.changeForm hB
        (varphi F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y)) ∈
        extFiltLE F n k ∧
      projDeg F n k (CliffordAlgebra.changeForm hB
          (varphi F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y))) =
        rhoExt F n g (projDeg F n k (CliffordAlgebra.changeForm hB (varphi F n y))) := by
  sorry

end WeilClasses
