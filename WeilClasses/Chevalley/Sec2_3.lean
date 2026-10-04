module

public import WeilClasses.Chevalley.Defs
public import WeilClasses.Correspondence.FourierMukai
public import WeilClasses.Spinor.Integral

/-!
# §2.3: the isomorphism `φ̃ : S ⊗ S → ⋀•V`

Statements of the paper's §2.3 (TeX lines 1042–1222):

* the unnumbered claims about `ψ` (2.3.1): `(L'_x)² = ½(x, x)_V · 1` (`Lprime_sq`); `ψ(x) = ψ'(x)·1`
  (`psi_apply_eq_psiPrime`); `ψ` is a homomorphism (`psi_mul`) and an isomorphism (`psi_bijective`)
  of left `C(V)`-modules; `ψ(C(V)_k) ⊆ F^k(⋀•V)` (`psi_mem_extFiltLE`); the graded map
  `ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V` is an isomorphism (`psiBar_surjective`, `psiBar_injective`,
  [Chevalley, II.1.6]) and `Spin(V)`-equivariant (`conjSpin_mem_CFilt`, `psiBar_equivariant`,
  [Chevalley, Sec. 3.3]); the integral versions (`psi_image_CZ`);
* `φ̃ = ψ ∘ φ` (2.3.2) is an isomorphism (`varphiTilde_bijective`, integrally
  `varphiTilde_image_SZZ`);
  the `Spin(V)`-action transported by `φ̃` preserves `F^k(⋀•V)` with associated graded action `⋀ρ`,
  independent of `B₀` (`varphiTilde_transport_graded`, [Chevalley, p. 85]);
* Remark 2.3.1 (`remark2_3_1_*`);
* Lemma 2.3.2 (`lemma2_3_2_1`, `lemma2_3_2_2`).

The quotient `C(V)_k / C(V)_{k-1}` is not formed: `ψ̄_k(x mod C(V)_{k-1})` is the degree-`k`
component `projDeg k (ψ x)` of `ψ(x)` for `x ∈ C(V)_k`, and the bijectivity of `ψ̄_k` is stated as
surjectivity onto `⋀^k V` plus "kernel = `C(V)_{k-1}`".
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## The map `ψ` (2.3.1) -/

/-- (§2.3, TeX line 1052) `(L'_x)² = ½(x, x)_V · 1`, where `1` is the identity of `End(⋀•V)`. -/
theorem Lprime_sq (x : V F n) :
    Lprime F n x * Lprime F n x =
      ((2 : F)⁻¹ * pairing F n x x) • (1 : Module.End F (ExtV F n)) := by
  sorry

/-- (2.3.1) The paper's definition of `ψ`: `ψ(x) = ψ'(x) · 1`, with `1 ∈ ⋀⁰V` the unit
(our `psi` is defined as `CliffordAlgebra.changeForm`, see `WeilClasses.Chevalley.Defs`). -/
theorem psi_apply_eq_psiPrime (x : C F n) : psi F n x = psiPrime F n x 1 := by
  sorry

/-- (§2.3, TeX line 1062) `ψ` is a homomorphism of left `C(V)`-modules, `C(V)` acting on `⋀•V`
through `ψ'`: `ψ(x y) = ψ'(x)(ψ(y))`. -/
theorem psi_mul (x y : C F n) : psi F n (x * y) = psiPrime F n x (psi F n y) := by
  sorry

/-- (§2.3, TeX line 1064) `ψ(C(V)_k) ⊆ F^k(⋀•V) = ⊕_{i ≤ k} ⋀^i V`. -/
theorem psi_mem_extFiltLE (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    psi F n x ∈ extFiltLE F n k := by
  sorry

/-- (§2.3, TeX lines 1065–1069; [Chevalley, II.1.6]) The induced map
`ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V`, `x ↦ (degree-k component of ψ(x))`, is surjective. -/
theorem psiBar_surjective (k : ℕ) {y : ExtV F n} (hy : y ∈ ⋀[F]^k (V F n)) :
    ∃ x ∈ CFilt F n k, projDeg F n k (psi F n x) = y := by
  sorry

/-- (§2.3, TeX lines 1065–1069; [Chevalley, II.1.6]) `ψ̄_k` is injective: for `x ∈ C(V)_k`, the
degree-`k` component of `ψ(x)` vanishes iff `x ∈ C(V)_{k-1}`. -/
theorem psiBar_injective (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (psi F n x) = 0 ↔ x ∈ CFiltLT F n k := by
  sorry

/-- (§2.3, TeX line 1069) `ψ : C(V) → ⋀•V` is an isomorphism (of left `C(V)`-modules, by
`psi_mul`). -/
theorem psi_bijective : Function.Bijective (psi F n) := by
  sorry

/-- (§2.3, TeX line 1069; [Chevalley, Sec. 3.3]) The conjugation action of `Spin(V)` on `C(V)`
preserves the filtration `C(V)_k`. -/
theorem conjSpin_mem_CFilt (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    conjSpin F n g x ∈ CFilt F n k := by
  sorry

/-- (§2.3, TeX line 1069; [Chevalley, Sec. 3.3]) `ψ̄_k : C(V)_k / C(V)_{k-1} → ⋀^k V` is
`Spin(V)`-equivariant, for the conjugation action on `C(V)` and the action `⋀^k ρ` on `⋀^k V`
induced from `V`. -/
theorem psiBar_equivariant (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (psi F n (conjSpin F n g x)) = rhoExt F n g (projDeg F n k (psi F n x)) := by
  sorry

/-! ## The isomorphism `φ̃ = ψ ∘ φ` (2.3.2) -/

/-- (2.3.2) `φ̃ = ψ ∘ φ : S ⊗ S → ⋀•V` is an isomorphism ("the composite isomorphism"). -/
theorem varphiTilde_bijective : Function.Bijective (varphiTilde F n) := by
  sorry

/-- (§2.3, TeX lines 1074–1077; [Chevalley, p. 85]) The `Spin(V)`-action on `⋀•V` obtained by
conjugating `m ⊗ m` with `φ̃` preserves the increasing filtration `F^k(⋀•V)`, and its associated
graded action is the action `⋀ρ` induced from `V`; in particular it does not depend on `B₀`. -/
theorem varphiTilde_transport_graded (g : Spin F n) (k : ℕ) (y : S F n ⊗[F] S F n)
    (hy : varphiTilde F n y ∈ extFiltLE F n k) :
    varphiTilde F n (TensorProduct.map (m F n g) (m F n g) y) ∈ extFiltLE F n k ∧
      projDeg F n k (varphiTilde F n (TensorProduct.map (m F n g) (m F n g) y)) =
        rhoExt F n g (projDeg F n k (varphiTilde F n y)) := by
  sorry

/-! ## Remark 2.3.1 -/

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`), first claim: the projection `B̄₀`
of `B₀` to `∧²V* = V* ⊗ V* / Sym²(V*)` (realized as the alternating part `½(B₀ - B₀ᵀ)`) is
`B̄₀((w₁, θ₁), (w₂, θ₂)) = ½(θ₂(w₁) - θ₁(w₂))` (our order: `vᵢ = (θᵢ, wᵢ)`). -/
theorem remark2_3_1_B0bar_apply (v₁ v₂ : V F n) :
    B0bar F n v₁ v₂ = (2 : F)⁻¹ * (v₂.1 v₁.2 - v₁.1 v₂.2) := by
  sorry

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`): the projection of `B₀` to
`∧²V*` equals that of `B₀ + (·,·)_V` (the pairing is symmetric). -/
theorem remark2_3_1_altPart_add_pairing : altPart F n (B0 F n + pairing F n) = B0bar F n := by
  sorry

/-- The decomposition `B₀ = ½(·,·)_V + B̄₀` into symmetric and alternating parts (Remark 2.3.1). -/
theorem B0_eq_half_pairing_add_B0bar : B0 F n = (2 : F)⁻¹ • pairing F n + B0bar F n := by
  sorry

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`): `B̄₀ = ½ c₁(𝒫)`.

Reading: the remark identifies the alternating form `B̄₀ ∈ ∧²V*` with the class
`½c₁(𝒫) ∈ H²(X × X̂) = ∧²V` ([BL, Th. 2.5.1 and 2.6(2b)]); the identification of `∧²V*` with `∧²V`
is the one by which the remark is used (it motivates Prop. 6.1.2 through Lemma 6.1.1): under the
isomorphism `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)` (Poincaré duality up to sign, Lemma 6.3.2),
the change of form by `B̄₀` on `⋀•V` (the exponential of contraction with `B̄₀`; `changeB0bar`)
becomes cup product with `exp(½c₁(𝒫))`. (Checked numerically for `n = 1, 2`.) With the
identification through the determinant pairing induced by `(·,·)_V`, `B̄₀` corresponds to
`-½c₁(𝒫)` instead (`B0bar_eq_neg_half_extPairing_c1P`); the sign of `c₁(𝒫)` is fixed by
Lemma 6.3.1 and Prop. 6.1.2 (see `WeilClasses.Correspondence.FourierMukai`). -/
theorem remark2_3_1_B0bar_eq_half_c1P (x : ExtV F n) :
    PiMap F n (changeB0bar F n x) =
      IsNilpotent.exp ((2 : F)⁻¹ • c1P F n) * PiMap F n x := by
  sorry

/-- Sign bridge for Remark 2.3.1: through the determinant pairing `⟨a ∧ b, x ∧ y⟩ =
(a, x)_V (b, y)_V - (a, y)_V (b, x)_V`, the class `c₁(𝒫) = Σ eᵢ ∧ fᵢ` is the alternating form
`(v₁, v₂) ↦ θ₁(w₂) - θ₂(w₁) = -2 B̄₀(v₁, v₂)`. -/
theorem B0bar_eq_neg_half_extPairing_c1P (v₁ v₂ : V F n) :
    B0bar F n v₁ v₂ = -((2 : F)⁻¹ * extPairing F n (c1P F n)
        (ExteriorAlgebra.ι F v₁ * ExteriorAlgebra.ι F v₂)) := by
  sorry

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`; [Trautman, Th. 1(i)]): with `B₀`
replaced by `½(·,·)_V` (over a field of characteristic zero), the resulting isomorphism
`S ⊗ S → ⋀•V` (`varphiTildeSym = equivExterior ∘ φ`) is `Spin(V)`-equivariant, for `m ⊗ m` on
`S ⊗ S` and the grading-preserving action `⋀ρ` on `⋀•V` induced by `V`.

Reading: the action of `Spin(V)` on `S ⊗ S = S_X ⊗ S_X` is `m ⊗ m`, the one for which `φ`
(2.2.5) is equivariant ([Chevalley, III.3.1]: `φ(m_g u ⊗ m_g v) = g φ(u ⊗ v) g⁻¹`). -/
theorem remark2_3_1_sym_equivariant (g : Spin F n) (y : S F n ⊗[F] S F n) :
    varphiTildeSym F n (TensorProduct.map (m F n g) (m F n g) y) =
      rhoExt F n g (varphiTildeSym F n y) := by
  sorry

/-- **Remark 2.3.1** (`remark-non-equivariance-of-varphi-tilde`): the symmetric variant
`S ⊗ S → ⋀•V` is an isomorphism. -/
theorem remark2_3_1_sym_bijective : Function.Bijective (varphiTildeSym F n) := by
  sorry

/-- (Remark 2.3.1; used for Prop. 6.1.2) Since `B₀ = ½(·,·)_V + B̄₀`, `ψ` is the symmetric `ψ`
followed by the change of form by `B̄₀` ([Bourbaki, §9 Lemma 3], Mathlib's
`CliffordAlgebra.changeForm_changeForm`): `ψ = changeB0bar ∘ psiSym`. -/
theorem psi_eq_changeB0bar_comp_psiSym : psi F n = changeB0bar F n ∘ₗ psiSym F n := by
  sorry

/-! ## Lemma 2.3.2 -/

/-- **Lemma 2.3.2(1)** (`lemma-symmetric-or-alternating-product-of-two-pure-spinors-has-weight-2`).
`φ̃([pt_X] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt_X])` belongs to `F^{4n-2}(⋀•V)` but not to `F^{4n-3}(⋀•V)`.

The hypothesis `1 ≤ n` (implied by the paper's standing assumption `n ≥ 2`) is needed: for `n = 0`
the element is `0`. -/
theorem lemma2_3_2_1 (hn : 1 ≤ n) :
    varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∈
        extFiltLE F n (4 * n - 2) ∧
      varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∉
        extFiltLE F n (4 * n - 3) := by
  sorry

/-- **Lemma 2.3.2(2)** (`lemma-symmetric-or-alternating-product-of-two-pure-spinors-has-weight-2`).
`φ̃([pt_X] ⊗ 1 + (-1)ⁿ 1 ⊗ [pt_X])` does not belong to `F^{4n-1}(⋀•V)`.

The hypothesis `1 ≤ n` (implied by the paper's standing assumption `n ≥ 2`) is needed: for `n = 0`
the element is `2 ∈ ⋀⁰V`. -/
theorem lemma2_3_2_2 (hn : 1 ≤ n) :
    varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) + (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)) ∉
      extFiltLE F n (4 * n - 1) := by
  sorry

end Field

/-! ## Integrality (§2.3 works over `ℤ`) -/

section Integral

variable (n : ℕ)

/-- `H*(X × X, ℤ) = S ⊗_ℤ S` inside `S_ℚ ⊗_ℚ S_ℚ`: the additive subgroup generated by the `s ⊗ t`
with `s, t ∈ H*(X, ℤ)`. -/
noncomputable def SZZ : AddSubgroup (S ℚ n ⊗[ℚ] S ℚ n) :=
  AddSubgroup.closure {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = s ⊗ₜ[ℚ] t}

/-- (§2.3, TeX lines 1065–1069) `ψ` is an isomorphism over `ℤ`: it maps the integral Clifford
algebra `C(V)` onto `⋀•V` (the integral lattice). -/
theorem psi_image_CZ : psi ℚ n '' (CZ n : Set (C ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  sorry

/-- (2.3.2) `φ̃ = ψ ∘ φ : S ⊗_ℤ S → ⋀•V` is an isomorphism over `ℤ` ("the choice of `B₀` is done so
that the construction is over the integers", Remark 2.3.1). -/
theorem varphiTilde_image_SZZ :
    varphiTilde ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  sorry

end Integral

end WeilClasses
