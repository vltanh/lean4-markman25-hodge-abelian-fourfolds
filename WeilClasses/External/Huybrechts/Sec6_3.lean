module

public import WeilClasses.Correspondence.FourierMukai

/-!
# Huybrechts, *Fourier–Mukai transforms*, Lemma 9.23 and Corollary 9.24, as used in §6.3

[Hu] D. Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Oxford, 2006, Lemma 9.23
(the cohomological Fourier–Mukai transform of the Poincaré bundle is Poincaré duality up to sign)
and Corollary 9.24 (its square). The paper uses them in the footnote of the proof of Lemma 6.3.1 to
compute `ψ_{𝒫⁻¹[n]}`, and in the proof of Lemma 6.3.2.

In the model (`WeilClasses.Correspondence.FourierMukai`) the transforms are the correspondences
`φ_𝒫 = ch(𝒫)_*` with `c₁(𝒫) = Σᵢ π_X^*eᵢ ∪ π_X̂^*fᵢ`, and Poincaré duality is
`PD_X(e_K) = ∫_X e_K ∧ (•) = ε_{K,K^c} f_{K^c}` (`PDX`, the paper's convention in §6.3).

**Reading of `PD_k : H^k(X̂) → H^{2n-k}(X)`** ("the Poincaré duality isomorphism"): it is the
inverse
of `PD_X : H^{2n-k}(X) → H^k(X̂) = H^{2n-k}(X)*` (`PDXinv`, `f_L ↦ ε_{L^c,L} e_{L^c}`); with this
reading both directions of Lemma 9.23 hold with the same sign `(-1)^{k(k+1)/2+n}`. With
`PD_X̂(f_L) = ∫_X̂ f_L ∧ (•) = ε_{L,L^c} e_{L^c}` (the convention used in the proof of Lemma 6.3.2)
the formula for `H^k(X̂) → H^{2n-k}(X)` fails by the sign `(-1)^k` (exact computation for `n = 1, 2`
and in general: `φ_𝒫(f_L) = (-1)^{n + ℓ(ℓ+1)/2 + ℓ} ε_{L,L^c} e_{L^c}`); this is the source of the
sign error in Lemma 6.3.2 (see `WeilClasses.Orlov.Sec6_3`).
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Huybrechts, Lemma 9.23]** for `X → X̂` (footnote in the proof of Lemma 6.3.1):
`φ_𝒫 : H^k(X) → H^{2n-k}(X̂)` equals `(-1)^{k(k+1)/2+n} PD_k`, `PD_X(e_K) = ε_{K,K^c} f_{K^c}`. -/
theorem huybrechts_lemma9_23_X (k : ℕ) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    phiPX F n s = (-1 : F) ^ (k * (k + 1) / 2 + n) • PDX F n s := by
  sorry

/-- **[Huybrechts, Lemma 9.23]** for `X̂ → X` (footnote in the proof of Lemma 6.3.1):
`φ_𝒫 : H^k(X̂) → H^{2n-k}(X)` equals `(-1)^{k(k+1)/2+n} PD_k`, where `PD_k` is read as the inverse
of `PD_X : H^{2n-k}(X) → H^k(X̂)` (see the module docstring; the paper's wording is ambiguous, and
this is the reading compatible with the sign of `c₁(𝒫)` fixed by Lemma 6.3.1 and Proposition 6.1.2,
`WeilClasses.Correspondence.FourierMukai`). -/
theorem huybrechts_lemma9_23_Xhat (k : ℕ) {t : SHat F n}
    (ht : t ∈ ⋀[F]^k (Module.Dual F (H1 F n))) :
    phiP F n t = (-1 : F) ^ (k * (k + 1) / 2 + n) • PDXinv F n t := by
  sorry

/-- **[Huybrechts, Cor. 9.24]** (footnote in the proof of Lemma 6.3.1): the composition
`H^k(X̂) → H^{2n-k}(X) → H^k(X̂)` of the two transforms `φ_𝒫` is `(-1)^{k+n}`. -/
theorem huybrechts_cor9_24 (k : ℕ) {t : SHat F n} (ht : t ∈ ⋀[F]^k (Module.Dual F (H1 F n))) :
    phiPX F n (phiP F n t) = (-1 : F) ^ (k + n) • t := by
  sorry

end WeilClasses
