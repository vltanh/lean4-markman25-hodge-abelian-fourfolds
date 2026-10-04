module

public import WeilClasses.Orlov.Defs

/-!
# §6.3: Orlov's equivalence induces Chevalley's isomorphism `S ⊗ S ≅ ⋀•V`

Statements of the paper's §6.3 (TeX lines 2660–2855): Lemma 6.3.1 with the displayed equations
(6.3.1), (6.3.2) and the unnumbered formulas of its proof, the proof of Lemma 6.1.1
(`phiOrlov_eq_PiMap_comp_nuOrlov`), Lemma 6.3.2 and Remark 6.3.3.

Notation (proof of Lemma 6.3.1): `e_K = basisS F n K`, `f_K = basisSHat F n K` (increasing wedge
products), `π_X^*`, `π_X̂^*` (`pullX`, `pullXHat`), `ε_{K,L}` (`epsSign`), `Σ(K)` (`sumIdx`, indices
from `1`), `σ_K = (-1)^{k(k+3)/2}` for `k = |K|`, `I' = K \ I`, `I^c` the complement in
`{1, …, 2n}`. `H*(X × X) = S ⊗ S` with `π₁^*e_K ∧ π₂^*e_L = e_K ⊗ e_L`, and
`H*(X̂ × X) = H*(X × X̂) = ⋀•V` (see `WeilClasses.Correspondence.Defs`).

**Correction** (agreed with the project owner; REPORT.md): Lemma 6.3.2 as printed, with the sign
`(-1)^{d(d+1)/2}`, is false in odd degrees `d` for the sign of `c₁(𝒫)` under which Lemma 6.3.1 and
Proposition 6.1.2 hold; `lemma6_3_2` states it with the correct sign `(-1)^{d(d-1)/2}`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## Combinatorics of the proof of Lemma 6.3.1 -/

/-- (§6.3, TeX line 2693) `ε_{K,K^c} = (-1)^{Σ(K) - k(k+1)/2}` (`Σ(K) ≥ k(k+1)/2`, so the natural
subtraction is the integer one). -/
theorem epsSign_compl (K : Finset (Fin (2 * n))) :
    epsSign F n K Kᶜ = (-1 : F) ^ (sumIdx n K - K.card * (K.card + 1) / 2) := by
  sorry

/-- (§6.3, TeX line 2694) `ε_{K^c,K} = (-1)^k ε_{K,K^c} = (-1)^{Σ(K) - k(k-1)/2}`. -/
theorem epsSign_compl_swap (K : Finset (Fin (2 * n))) :
    epsSign F n Kᶜ K = (-1 : F) ^ K.card * epsSign F n K Kᶜ ∧
      epsSign F n Kᶜ K = (-1 : F) ^ (sumIdx n K - K.card * (K.card - 1) / 2) := by
  sorry

/-- (§6.3, TeX line 2695) Poincaré duality `PD_X` sends `e_K` to `∫_X e_K ∧ (•) = ε_{K,K^c}
f_{K^c}`:
`PD_X(s)` pairs with `t` to `∫_X s ∧ t` (under `H^k(X̂) = H^k(X)*`, `⟨f_A, e_B⟩ = δ_{AB}`). -/
theorem PDX_spec (s t : S F n) : pairSHatS F n (PDX F n s) t = integral F n (s * t) := by
  sorry

/-- (§6.3, TeX lines 2697–2703) `μ^*(π₁^*e_K ∧ π₂^*e_L) = Σ_{I ⊆ K} ε_{I,I'} ε_{I',L} π₁^*e_I ∧
π₂^*(e_{I' ∪ L})`, `I' = K \ I`. -/
theorem muStar_basis (K L : Finset (Fin (2 * n))) :
    muStar F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n I (K \ I) * epsSign F n (K \ I) L) •
        (basisS F n I ⊗ₜ[F] basisS F n ((K \ I) ∪ L)) := by
  sorry

/-- (§6.3, TeX lines 2705–2716 and footnote) The cohomological action of `Ψ_{𝒫⁻¹[n]}` is
`Ψ_{𝒫⁻¹[n]}(e_K) = σ_K PD(e_K) = σ_K ε_{K,K^c} f_{K^c}`, `σ_K = (-1)^{k(k+3)/2}`. -/
theorem psiPinvShift_basis (K : Finset (Fin (2 * n))) :
    psiPinvShift F n (basisS F n K) =
      ((-1 : F) ^ (K.card * (K.card + 3) / 2) * epsSign F n K Kᶜ) • basisSHat F n Kᶜ := by
  sorry

/-- (footnote in §6.3) The cohomological action of `Ψ_{𝒫⁻¹}[n]` restricts to `H^k(X)` as
`(-1)^{k+n} φ_𝒫`, where `φ_𝒫 : H*(X) → H*(X̂)`. -/
theorem psiPinvShift_eq_phiPX (k : ℕ) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    psiPinvShift F n s = (-1 : F) ^ (k + n) • phiPX F n s := by
  sorry

/-- **(6.3.1)** (`eq-phi-of-e-K-e-L`), both lines:
`ν(π₁^*e_K ∧ π₂^*e_L) = Σ_{I ⊆ K} ε_{I',I} ε_{I,L} σ_{I'} ε_{I',(I')^c} π_X̂^*f_{(I')^c} ∧
π_X^*(e_{I∪L})
= Σ_{I ⊆ K} ε_{I',I} ε_{I,L} (-1)^{Σ(I') - |I'|} π_X̂^*f_{(I')^c} ∧ π_X^*(e_{I∪L})`, `I' = K \ I`.
(Checked numerically for `n = 1, 2`.) -/
theorem equation6_3_1 (K L : Finset (Fin (2 * n))) :
    nuOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
        ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * epsSign F n I L *
              (-1 : F) ^ ((K \ I).card * ((K \ I).card + 3) / 2) *
              epsSign F n (K \ I) (K \ I)ᶜ) •
            (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) ∧
      nuOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
        ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * epsSign F n I L *
              (-1 : F) ^ (sumIdx n (K \ I) - (K \ I).card)) •
            (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) := by
  sorry

/-- (§6.3, TeX line 2785) `δ_K(f₁ ∧ ⋯ ∧ f_{2n}) = (-1)^{Σ(K) - |K|} f_{K^c}`, where
`δ_K = δ_{e_{i₁}} ⋯ δ_{e_{i_k}}` (`i₁ < ⋯ < i_k`) and `δ_{e_i}` is contraction with
`B₀(e_i, ·) = (e_i, ·)_V`. -/
theorem delta_prod_ptHat (K : Finset (Fin (2 * n))) :
    (List.map (fun i => delta F n (0, e F n i)) K.sort).prod (pullXHat F n (ptHat F n)) =
      (-1 : F) ^ (sumIdx n K - K.card) • pullXHat F n (basisSHat F n Kᶜ) := by
  sorry

/-- (§6.3, TeX lines 2767–2786) `φ̃(e_K ⊗ e_L) = Σ_{I ⊆ K} ε_{I',I} (-1)^{ℓ(ℓ-1)/2}
(-1)^{Σ(I') - |I'|} ε_{I,L} f_{(I')^c} ∧ e_{I∪L}`, `ℓ = |L|`, `I' = K \ I`. -/
theorem varphiTilde_basis (K L : Finset (Fin (2 * n))) :
    varphiTilde F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n (K \ I) I * (-1 : F) ^ (L.card * (L.card - 1) / 2) *
            (-1 : F) ^ (sumIdx n (K \ I) - (K \ I).card) * epsSign F n I L) •
          (pullXHat F n (basisSHat F n (K \ I)ᶜ) * pullX F n (basisS F n (I ∪ L))) := by
  sorry

/-- **(6.3.2)** (`eq-orlov-isomorphism-categorifies-chevalley`)
`ν(π₁^*(e_K) ∧ π₂^*τ(e_L)) = φ̃(e_K ⊗ e_L)`. -/
theorem equation6_3_2 (K L : Finset (Fin (2 * n))) :
    nuOrlov F n (basisS F n K ⊗ₜ[F] tau F n (basisS F n L)) =
      varphiTilde F n (basisS F n K ⊗ₜ[F] basisS F n L) := by
  sorry

/-- **Lemma 6.3.1** (`lemma-nu-equal-tilde-varphi`). `ν ∘ (id ⊗ τ) = φ̃`, where
`ν : H*(X × X) → H*(X̂ × X)` is induced by `(Ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^*` and `φ̃` is (2.3.2).
(Checked numerically for `n = 1, 2`; this fixes the sign of `c₁(𝒫)`, see `c1P`.) -/
theorem lemma6_3_1 : nuOrlov F n ∘ₗ tauTensor F n = varphiTilde F n := by
  sorry

/-- (Proof of Lemma 6.1.1, §6.3, TeX line 2799) `φ = (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^* =
(φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ ν` (because `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`). -/
theorem phiOrlov_eq_PiMap_comp_nuOrlov : phiOrlov F n = PiMap F n ∘ₗ nuOrlov F n := by
  sorry

/-! ## Lemma 6.3.2 and Remark 6.3.3 -/

/-- **Lemma 6.3.2** (`lemma-phi-P-psi-P-inverse-is-PD-up-to-sign`):
`φ_𝒫 ⊗ ψ_{𝒫⁻¹} : H^d(X̂ × X) → H^{4n-d}(X × X̂)` equals `(-1)^{d(d-1)/2} PD_{X̂ × X}`, where
`(PD_{X̂×X}(α), •) = ∫_{X̂ × X} α ∧ •`, the pairing `( , )` of `H*(X × X̂)` with `H*(X̂ × X)` being
the one induced by `(·,·)_V` (`extPairing`).

Correction of the paper (REPORT.md): the paper prints the sign `(-1)^{d(d+1)/2}`, which differs from
the correct one in every odd degree. With `c₁(𝒫) = Σ eᵢ ∧ fᵢ`, the sign for which Lemma 6.3.1 and
Proposition 6.1.2 hold, `φ_𝒫(f_L) = (-1)^{n + ℓ(ℓ+1)/2 + ℓ} ε_{L,L^c} e_{L^c}`, while the proof uses
the footnote's `(-1)^{ℓ(ℓ+1)/2 + n} ε_{L,L^c} e_{L^c}`; they differ by `(-1)^ℓ`. Counterexample to the
printed sign: `n = 1`, `α = f₁`, `β = f₂ ∧ e₁ ∧ e₂`: the left side is `1`, the printed right side
`-1`. The paper only uses that the map reverses degrees (Proposition 6.4.1), which is unaffected.

Reading: `ψ_{𝒫⁻¹}` without shift, as printed (the proof says `φ_𝒫⁻¹ = ψ_{𝒫⁻¹}`, while
`φ_𝒫⁻¹ = ψ_{𝒫⁻¹[n]} = (-1)ⁿ ψ_{𝒫⁻¹}`; the two `(-1)ⁿ` in the proof's first display cancel). -/
theorem lemma6_3_2 (d : ℕ) {α : ExtV F n} (hα : α ∈ ⋀[F]^d (V F n)) (β : ExtV F n) :
    extPairing F n (PiMap0 F n α) β = (-1 : F) ^ (d * (d - 1) / 2) * integralExt F n (α * β) := by
  sorry

/-- **Remark 6.3.3** (no label). Let `ς : X × X̂ → X̂ × X` be the transposition. The isomorphism
`ς_* : V = H¹(X × X̂) → H¹(X̂ × X) = V*` is the one induced by `(·,·)_V` (in the model both
`H*(X × X̂)` and `H*(X̂ × X)` are `⋀•V`, `ς_*` is the identity and `V*` is identified with `V` by
`(·,·)_V`, as in `extPairing`). Hence `(φ_𝒫 ⊗ ψ_{𝒫⁻¹}) ∘ ς_* : ⋀•V → ⋀•V` is an analogue of the
Hodge `*` operator [Huybrechts, Complex geometry, Sec. 1.2].

Reading: "analogue of the Hodge `*` operator" is formalized as: on each `⋀^d V` it is, up to a sign
`±1`, the Hodge star of the pairing `(·,·)_V` and the volume form `∫_{X̂ × X}`, i.e. it satisfies
`(⋆α, β) = ∫ α ∧ β` up to sign (cf. Mathlib's `exteriorPower.hodgeStar`). -/
theorem remark6_3_3 (d : ℕ) :
    ∃ s : F, (s = 1 ∨ s = -1) ∧ ∀ α ∈ ⋀[F]^d (V F n), ∀ β : ExtV F n,
      extPairing F n (PiMap0 F n α) β = s * integralExt F n (α * β) := by
  sorry

end Field

end WeilClasses
