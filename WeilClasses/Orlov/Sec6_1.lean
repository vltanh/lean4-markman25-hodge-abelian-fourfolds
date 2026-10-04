module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Spinor.Integral
public import WeilClasses.Chevalley.Sec2_3

/-!
# §6.1: `Spin(V)`-equivariance properties of Orlov's equivalence

Statements of the paper's §6.1 (TeX lines 2139–2348), in the model where Orlov's cohomological
isomorphism `φ` (6.1.3) is the composite `(id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*` (`phiOrlov`, see
`WeilClasses.Orlov.Defs`):

* `φ` is an isomorphism (`phiOrlov_bijective`), integrally (`phiOrlov_image_SZZ`); (6.1.4) as
  printed (`rhoPrime_eq_phiOrlov_conj`);
* Lemma 6.1.1 (`lemma6_1_1`);
* `ρ'_g` preserves the decreasing filtration (6.1.5) with associated graded action `ρ`
  (`rhoPrime_mem_extFiltGE`, `rhoPrime_projDeg`; [GLO, Prop. 4.3.7, Cor. 4.3.8]);
* (6.1.8) (`equation6_1_8`, `equation6_1_8_integral`; [Orlov, Th. 2.10]) and the cocycle identity
  (6.1.9) (`equation6_1_9`; [Huybrechts, Ex. 9.41]);
* Proposition 6.1.2 = (6.1.10) (`proposition6_1_2`) and the integrality of
  `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` (`c1P_pairing_mod_two`, `half_c1P_sub_rho_mem_ExtZ`).

**Reading (coefficients).** The paper states Proposition 6.1.2, (6.1.8) and (6.1.9) for `g` in the
integral group `Spin(V)`, but applies them to `K`-points (Lemma 6.2.6 uses `Spin(V_K)_{ℓ₁,ℓ₂}`);
the identities are algebraic, and we state them for `g : Spin F n` over every field `F` of
characteristic `0`, the integrality claims separately for the integral group `SpinZ n`.

**Left out (sheaf-theoretic).** The derived equivalences (6.1.1), (6.1.2) themselves, the
intertwining of the actions of `Aut(Dᵇ(X))` ([Huybrechts, Cor. 9.37]), the identification of `φ`
with the Chern character of Orlov's kernel (GRR), the existence of the line bundles `N_g` (only
their classes `c₁(N_g) ∈ H²(X × X̂)` appear), the identity `φ_{𝒢^∨[n]} = τ φ_𝒢 τ`, the group
cohomology interpretation of (6.1.9), and the reduction of Proposition 6.1.2 to abelian surfaces
(its proof; replaced by an algebraic proof, see `notes/design.md`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- (6.1.3) Orlov's cohomological map `φ : S ⊗ S → ⋀•V` is an isomorphism. -/
theorem phiOrlov_bijective : Function.Bijective (phiOrlov F n) := by
  sorry

/-- (6.1.3) over the integers: `φ` maps `H*(X × X, ℤ) = S_ℤ ⊗ S_ℤ` onto `H*(X × X̂, ℤ) = ⋀•V_ℤ` (the
paper's `φ` is the correspondence isomorphism of an equivalence of derived categories, between
integral cohomology groups; checked numerically for `n = 1, 2`). -/
theorem phiOrlov_image_SZZ (n : ℕ) :
    phiOrlov ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  sorry

/-- **(6.1.4)** (`rho-prime-g`) as printed: `ρ'_g = φ (m_g × m†_g) φ⁻¹`. -/
theorem rhoPrime_eq_phiOrlov_conj (g : Spin F n) :
    rhoPrime F n g =
      phiOrlov F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (mDagger F n (g : C F n)) ∘ₗ
        phiOrlovInv F n := by
  sorry

/-- **Lemma 6.1.1** (`lemma-orlov-isomorphism-is-chevalley`).
`φ = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ φ̃ ∘ (id ⊗ τ)`, where `φ̃ : H*(X × X) → H*(X̂ × X)` is Chevalley's
isomorphism (2.3.2) and `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)`. (Checked numerically for
`n = 1, 2` with the sign convention of `c1P`.) -/
theorem lemma6_1_1 : phiOrlov F n = PiMap F n ∘ₗ varphiTilde F n ∘ₗ tauTensor F n := by
  sorry

/-- (§6.1, TeX lines 2228–2235; [GLO, Prop. 4.3.7, Cor. 4.3.8], "more directly by Lemma 6.1.1")
`ρ'_g` preserves the decreasing filtration `F_k(⋀•V) = ⊕_{i ≥ k} ⋀^i V` (6.1.5). -/
theorem rhoPrime_mem_extFiltGE (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    rhoPrime F n g x ∈ extFiltGE F n k := by
  sorry

/-- (§6.1, TeX lines 2228–2235; [GLO, Prop. 4.3.7, Cor. 4.3.8]) The graded action induced by `ρ'_g`
on `F_k / F_{k+1} = ⋀^k V` is `⋀^k ρ_g`, induced from `ρ : Spin(V) → SO(V)`. -/
theorem rhoPrime_projDeg (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  sorry

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10], [Huybrechts, Prop. 9.39]) For every `g ∈ Spin(V)`
there is a (topological) line bundle `N_g` on `X × X̂` with `ρ'_g = ch(N_g) ∪ ρ_g`. In the model:
there is a class `c = c₁(N_g) ∈ H²(X × X̂) = ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g`.
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0` (the integral version, `c` integral for
`g` integral, is `equation6_1_8_integral`). -/
theorem equation6_1_8 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x := by
  sorry

/-- **(6.1.9)** (`eq-1-cocycle-identity`; [Huybrechts, Ex. 9.41]) The cocycle identity
`c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`, for all `g₁, g₂ ∈ Spin(V)`, where `c₁(N_g)` is
any class satisfying (6.1.8) for `g` (it is unique: `exp(c) = ρ'_g(1)`).
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`. -/
theorem equation6_1_9 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ := by
  sorry

/-- **Proposition 6.1.2**
(`prop-extension-class-of-decreasing-filtration-of-spin-V-representations`),
equation **(6.1.10)** (`eq-relating-rho-and-rho-prime`):
`ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`.
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`. (Checked numerically for `n = 1, 2`
with the sign convention of `c1P`;
it fails for the opposite sign.) -/
theorem proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x := by
  sorry

end Field

section Integral

variable (n : ℕ)

/-- (§6.1, TeX lines 2273–2274) The integral alternating bilinear form `c₁(𝒫)` (the class
`c₁(𝒫) ∈ ⋀²V` paired with `x ∧ y` by the determinant pairing of `(·,·)_V`) and the symmetric
pairing `(·,·)_V` agree modulo `2` on the lattice `V`. -/
theorem c1P_pairing_mod_two (x y : V ℚ n) (hx : x ∈ VZ n) (hy : y ∈ VZ n) :
    ∃ k : ℤ, extPairing ℚ n (c1P ℚ n) (ExteriorAlgebra.ι ℚ x * ExteriorAlgebra.ι ℚ y) -
      pairing ℚ n x y = 2 * k := by
  sorry

/-- (§6.1, TeX lines 2273–2275) The class `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` is integral for every `g` in the
integral group `Spin(V)`. -/
theorem half_c1P_sub_rho_mem_ExtZ (g : Spin ℚ n) (hg : g ∈ SpinZ n) :
    (2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)) ∈ ExtZ n := by
  sorry

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10]) for the integral group: for `g ∈ Spin(V)` the class
`c₁(N_g)` of the line bundle `N_g` is integral. -/
theorem equation6_1_8_integral (g : Spin ℚ n) (hg : g ∈ SpinZ n) :
    ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧ ∀ x : ExtV ℚ n,
      rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x := by
  sorry

end Integral

end WeilClasses
