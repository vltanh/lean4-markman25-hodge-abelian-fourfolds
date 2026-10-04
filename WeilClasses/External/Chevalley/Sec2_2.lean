module

public import WeilClasses.PureSpinor.Lemma2_2_6

/-!
# Chevalley, *The algebraic theory of spinors*, results used in §2.2 of the paper

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954, Chapter III.
The quadratic space is `V_F = H¹(X̂, F) ⊕ H¹(X, F)` (maximal Witt index), its spin representation is
`S_F = ⋀• H¹(X, F)` with `m_{(θ,w)} = L_w + D_θ`, and Chevalley's bilinear form on spinors is the
Mukai pairing `(·,·)_S`. All statements are over a field `F` of characteristic zero; the paper uses
them over `ℂ` and over `K = ℚ(√-d)`.

Results stated, with the places where the paper uses them:

* [III.1.4] every maximal isotropic subspace is `ker m_w` for an even or an odd pure spinor `w`, and
  `w` is unique up to a scalar (`chevalley_III_1_4_exists`, `chevalley_III_1_4_unique`): §2.2, first
  paragraph (definition of pure spinors, the spinor variety);
* [III.1.5] the two families (`chevalley_III_1_5_families`): §2.2, first paragraph ("`IGr(2n, V_ℂ)`
  has two connected components"; only the algebraic content, the disjointness of the two families,
  is stated: the isotropic Grassmannian and its topology are not modeled);
* [III.1.12] (`chevalley_III_1_12`): §2.2 after Lemma 2.2.1 (the line through `ℓ₁, ℓ₂` meets the
  spinor variety only in `ℓ₁, ℓ₂`, for `n > 1`) and Remark 2.2.3 ("`w` is not a pure spinor");
* [III.2.4] (`chevalley_III_2_4`, `chevalley_III_2_4_self`): proof of Lemma 2.2.1;
* [III.3.1] (`chevalley_III_3_1_bijective`, `chevalley_III_3_1_equivariant`): proof of Lemma 2.2.6
  (`φ ⊗ ℚ` is an isomorphism of `Spin(V_ℚ)`-representations);
* [III.3.2] (`chevalley_III_3_2`): proof of Lemma 2.2.6 (`φ(ℓ̃ᵢ ⊗ ℓ̃ᵢ) = ⋀^{2n} W_{i,ℂ}`) and the
  relation `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` of §2.2;
* [§3.3, Lemma 1] (`chevalley_sec3_3_lemma1`): transitivity of `Spin(V_F)` on ordered pairs of
  complementary maximal isotropic subspaces (used in §6.4; natural tool for the statements of §2.2).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, III.1.4]** (existence), as used in §2.2: every maximal isotropic subspace `W` of
`V_F` is `ker m_w` for a nonzero even or odd pure spinor `w`. -/
theorem chevalley_III_1_4_exists (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) :
    ∃ w : S F n, w ≠ 0 ∧ (IsEvenPureSpinor F n w ∨ IsOddPureSpinor F n w) ∧ ann F n w = W := by
  sorry

/-- **[Chevalley, III.1.4]** (uniqueness), as used in §2.2: a nonzero spinor `w` with `ker m_w`
maximal isotropic is determined up to a scalar by `ker m_w`; so the map from `IGr₊(2n, V)` to
`ℙ(S⁺)`, `W ↦ [w]`, is well defined and injective. -/
theorem chevalley_III_1_4_unique (w w' : S F n) (hw : w ≠ 0)
    (hmax : IsMaxIsotropic F n (ann F n w)) (h : ann F n w' = ann F n w) :
    w' ∈ Submodule.span F {w} := by
  sorry

/-- **[Chevalley, III.1.5]** (the two families), as used in §2.2: no maximal isotropic subspace is
the annihilator of both a nonzero even and a nonzero odd pure spinor, so the maximal isotropic
subspaces split into the two families `IGr₊` (even pure spinors) and `IGr₋` (odd pure spinors). -/
theorem chevalley_III_1_5_families (w w' : S F n) (hw : IsEvenPureSpinor F n w)
    (hw' : IsOddPureSpinor F n w') (hw0 : w ≠ 0) (hw0' : w' ≠ 0) :
    ann F n w ≠ ann F n w' := by
  sorry

/-- **[Chevalley, III.1.12]**, as used in §2.2 (after Lemma 2.2.1, and in Remark 2.2.3): if `u₁, u₂`
are even pure spinors with `ker m_{u₁} ∩ ker m_{u₂} = 0` and `n > 1`, then a combination
`a u₁ + b u₂` is a pure spinor only if `a = 0` or `b = 0`. -/
theorem chevalley_III_1_12 (hn : 1 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F)
    (hab : IsEvenPureSpinor F n (a • u₁ + b • u₂)) :
    a = 0 ∨ b = 0 := by
  sorry

/-- **[Chevalley, III.2.4]**, as used in the proof of Lemma 2.2.1: for even pure spinors `λ₁, λ₂`
(with `n ≥ 1`), `(λ₁, λ₂)_S = 0` if and only if `ker m_{λ₁} ∩ ker m_{λ₂} ≠ 0`. -/
theorem chevalley_III_2_4 (hn : 0 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) :
    mukai F n u₁ u₂ = 0 ↔ ann F n u₁ ⊓ ann F n u₂ ≠ ⊥ := by
  sorry

/-- **[Chevalley, III.2.4]**, the special case `λ₁ = λ₂` used in the proof of Lemma 2.2.1: a pure
spinor is isotropic, `(λ, λ)_S = 0` (for `n ≥ 1`). -/
theorem chevalley_III_2_4_self (hn : 0 < n) (u : S F n) (hu : IsEvenPureSpinor F n u) :
    mukai F n u u = 0 := by
  sorry

/-- **[Chevalley, III.3.1]**, as used in the proof of Lemma 2.2.6: Chevalley's map
`φ : S_F ⊗ S_F → C(V_F)`, `φ(u ⊗ v) = u [pt_X̂] τ(v)` (2.2.5), is bijective. -/
theorem chevalley_III_3_1_bijective : Function.Bijective (varphi F n) := by
  sorry

/-- **[Chevalley, III.3.1]**, as used in the proof of Lemma 2.2.6: `φ` is an isomorphism of
`Spin(V_F)`-representations, `Spin(V_F)` acting on `S ⊗ S` by `m_g ⊗ m_g` and on `C(V_F)` by
conjugation `x ↦ g x g⁻¹ = g x g*`. -/
theorem chevalley_III_3_1_equivariant (g : Spin F n) (s t : S F n) :
    varphi F n (m F n (g : C F n) s ⊗ₜ m F n (g : C F n) t) =
      (g : C F n) * varphi F n (s ⊗ₜ t) * star (g : C F n) := by
  sorry

/-- **[Chevalley, III.3.2]**, as used in the proof of Lemma 2.2.6 (and for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` in
§2.2): for a nonzero even pure spinor `u` with `W = ker m_u`, `φ(u ⊗ u)` is nonzero and spans the
line `⋀^{2n} W ⊆ C(V_F)`. -/
theorem chevalley_III_3_2 (u : S F n) (hu : IsEvenPureSpinor F n u) (hu0 : u ≠ 0) :
    varphi F n (u ⊗ₜ u) ≠ 0 ∧
      Submodule.span F {varphi F n (u ⊗ₜ u)} = cliffordTopPiece F n (ann F n u) := by
  sorry

/-- **[Chevalley, §3.3, Lemma 1]**, in the form used in the paper (§6.4: "`Spin(V_K)` acts
transitively on the set of ordered pairs of complementary maximally isotropic subspaces of `V_K`"),
restricted to pairs from the even family: given even pure spinors `u₁, u₂, u₁', u₂'` with
`ker m_{u₁} ∩ ker m_{u₂} = 0 = ker m_{u₁'} ∩ ker m_{u₂'}`, some `g ∈ Spin(V_F)` maps the pair
`(ker m_{u₁}, ker m_{u₂})` to `(ker m_{u₁'}, ker m_{u₂'})`. (`Spin(V_F)` preserves the two families,
so transitivity on all complementary pairs, as literally phrased in §6.4, fails; the pairs used
there come from even pure spinors.) -/
theorem chevalley_sec3_3_lemma1 (u₁ u₂ u₁' u₂' : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (h₁' : IsEvenPureSpinor F n u₁')
    (h₂' : IsEvenPureSpinor F n u₂') (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥)
    (hW' : ann F n u₁' ⊓ ann F n u₂' = ⊥) :
    ∃ g : Spin F n, (ann F n u₁).map (rho F n g).toLinearMap = ann F n u₁' ∧
      (ann F n u₂).map (rho F n g).toLinearMap = ann F n u₂' := by
  sorry

end WeilClasses
