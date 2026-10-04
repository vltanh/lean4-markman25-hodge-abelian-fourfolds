module

public import WeilClasses.Correspondence.FourierMukai
import WeilClasses.Orlov.Basis

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

**Proofs** (Stage 2, prover SD): by computation on the bases `e_K`, `f_L`. The kernel
`ch(𝒫) = exp(c₁(𝒫)) = Σ_K (-1)^{|K|(|K|-1)/2} π_X^*e_K ∪ π_X̂^*f_K` gives
`φ_𝒫(e_L) = (-1)^{m(m-1)/2} ε_{L,L^c} f_{L^c}` and
`φ_𝒫(f_L) = (-1)^{m(m-1)/2 + m²} ε_{L,L^c} e_{L^c}` with `m = |L^c| = 2n - |L|`
(`s61_phiPX_basisS`, `s61_phiP_basisSHat`, `WeilClasses.Orlov.Defs`), and the signs agree by
`m(m-1)/2 ≡ n + k(k+1)/2 (mod 2)` for `k + m = 2n` (`sd_tri_compl_mod_two`) and
`ε_{L,L^c} ε_{L^c,L} = (-1)^{km}`.
-/

@[expose] public section

namespace WeilClasses

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The parity identity behind the signs of Lemma 9.23: if `k + m = 2p`, then
`m(m-1)/2 ≡ p + k(k+1)/2 (mod 2)`. -/
theorem sd_tri_compl_mod_two {k m p : ℕ} (h : k + m = 2 * p) :
    m * (m - 1) / 2 % 2 = (k * (k + 1) / 2 + p) % 2 := by
  have h3 := s61_tri_add k m
  rw [h] at h3
  have h4 := s61_tri_two_mul p
  have h5 := s61_mul_self_mod_two k
  have h6 := s61_tri_succ k
  rw [mul_comm (k + 1) k] at h6
  have h7 : k * m + k * k = 2 * (p * k) := by
    rw [← mul_add, add_comm m k, h]; ring
  omega

omit [CharZero F] in
/-- `PD_X(e_K) = ε_{K,K^c} f_{K^c}`. -/
theorem sd_PDX_basisS (K : Finset (Fin (2 * n))) :
    PDX F n (basisS F n K) = epsSign F n K Kᶜ • basisSHat F n Kᶜ := by
  rw [PDX, Module.Basis.constr_basis]

omit [CharZero F] in
/-- `PD_X⁻¹(f_L) = ε_{L^c,L} e_{L^c}`. -/
theorem sd_PDXinv_basisSHat (L : Finset (Fin (2 * n))) :
    PDXinv F n (basisSHat F n L) = epsSign F n Lᶜ L • basisS F n Lᶜ := by
  rw [PDXinv, Module.Basis.constr_basis]

/-- **[Huybrechts, Lemma 9.23]** for `X → X̂` (footnote in the proof of Lemma 6.3.1):
`φ_𝒫 : H^k(X) → H^{2n-k}(X̂)` equals `(-1)^{k(k+1)/2+n} PD_k`, `PD_X(e_K) = ε_{K,K^c} f_{K^c}`.
Proof: on the basis `e_K` (`|K| = k`), `φ_𝒫(e_K) = (-1)^{m(m-1)/2} ε_{K,K^c} f_{K^c}`, `m = 2n - k`
(`s61_phiPX_basisS`), and `m(m-1)/2 ≡ n + k(k+1)/2`. -/
theorem huybrechts_lemma9_23_X (k : ℕ) {s : S F n} (hs : s ∈ ⋀[F]^k (H1 F n)) :
    phiPX F n s = (-1 : F) ^ (k * (k + 1) / 2 + n) • PDX F n s := by
  rw [← (basisS F n).sum_repr s]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : K.card = k
  · subst hK
    have hsgn : (-1 : F) ^ (Kᶜ.card * (Kᶜ.card - 1) / 2) =
        (-1 : F) ^ (K.card * (K.card + 1) / 2 + n) :=
      s61_neg_one_pow_congr (sd_tri_compl_mod_two (s61_card_add_card_compl n K))
    rw [s61_phiPX_basisS, sd_PDX_basisS, s61_epsSign_eq, ite_eq_left disjoint_compl_right]
    simp only [smul_smul]
    congr 1
    linear_combination (basisS F n).repr s K * (-1 : F) ^ s61_inv K Kᶜ * hsgn
  · have h0 : (basisS F n).repr s K = 0 := s61_repr_eq_zero_of_mem _ hs hK
    rw [h0, zero_smul, zero_smul, smul_zero]

/-- **[Huybrechts, Lemma 9.23]** for `X̂ → X` (footnote in the proof of Lemma 6.3.1):
`φ_𝒫 : H^k(X̂) → H^{2n-k}(X)` equals `(-1)^{k(k+1)/2+n} PD_k`, where `PD_k` is read as the inverse
of `PD_X : H^{2n-k}(X) → H^k(X̂)` (see the module docstring; the paper's wording is ambiguous, and
this is the reading compatible with the sign of `c₁(𝒫)` fixed by Lemma 6.3.1 and Proposition 6.1.2,
`WeilClasses.Correspondence.FourierMukai`).
Proof: on the basis `f_L` (`|L| = k`), `φ_𝒫(f_L) = (-1)^{m(m-1)/2 + m²} ε_{L,L^c} e_{L^c}`,
`m = 2n - k` (`s61_phiP_basisSHat`), `ε_{L,L^c} = (-1)^{km} ε_{L^c,L}`, `m² + km = 2nm` and
`m(m-1)/2 ≡ n + k(k+1)/2`. -/
theorem huybrechts_lemma9_23_Xhat (k : ℕ) {t : SHat F n}
    (ht : t ∈ ⋀[F]^k (Module.Dual F (H1 F n))) :
    phiP F n t = (-1 : F) ^ (k * (k + 1) / 2 + n) • PDXinv F n t := by
  rw [← (basisSHat F n).sum_repr t]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  by_cases hL : L.card = k
  · subst hL
    have h1 := s61_inv_add_inv (disjoint_compl_right : Disjoint L Lᶜ)
    have h2 := s61_card_add_card_compl n L
    have h3 := sd_tri_compl_mod_two h2
    have h4 : Lᶜ.card * Lᶜ.card + L.card * Lᶜ.card = 2 * (n * Lᶜ.card) := by
      rw [← add_mul, add_comm, h2, mul_assoc]
    have hsgn : (-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2) * (-1 : F) ^ (Lᶜ.card * Lᶜ.card) *
        (-1 : F) ^ s61_inv L Lᶜ =
        (-1 : F) ^ (L.card * (L.card + 1) / 2 + n) * (-1 : F) ^ s61_inv Lᶜ L := by
      simp only [← pow_add]
      exact s61_neg_one_pow_congr (by omega)
    rw [s61_phiP_basisSHat, sd_PDXinv_basisSHat, s61_epsSign_eq, ite_eq_left disjoint_compl_left]
    simp only [smul_smul]
    congr 1
    linear_combination (basisSHat F n).repr t L * hsgn
  · have h0 : (basisSHat F n).repr t L = 0 := s61_repr_eq_zero_of_mem _ ht hL
    rw [h0, zero_smul, zero_smul, smul_zero]

/-- **[Huybrechts, Cor. 9.24]** (footnote in the proof of Lemma 6.3.1): the composition
`H^k(X̂) → H^{2n-k}(X) → H^k(X̂)` of the two transforms `φ_𝒫` is `(-1)^{k+n}`.
Proof: on the basis `f_L` (`|L| = k`), with the formulas for `φ_𝒫(f_L)` and `φ_𝒫(e_{L^c})`
(`s61_phiP_basisSHat`, `s61_phiPX_basisS`) the sign is
`(-1)^{m(m-1)/2 + m² + km + k(k-1)/2} = (-1)^{n + k²}`, `m = 2n - k`. -/
theorem huybrechts_cor9_24 (k : ℕ) {t : SHat F n} (ht : t ∈ ⋀[F]^k (Module.Dual F (H1 F n))) :
    phiPX F n (phiP F n t) = (-1 : F) ^ (k + n) • t := by
  rw [← (basisSHat F n).sum_repr t]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  by_cases hL : L.card = k
  · subst hL
    have h1 := s61_inv_add_inv (disjoint_compl_right : Disjoint L Lᶜ)
    have h2 := s61_card_add_card_compl n L
    have h3 := sd_tri_compl_mod_two h2
    have h4 : Lᶜ.card * Lᶜ.card + L.card * Lᶜ.card = 2 * (n * Lᶜ.card) := by
      rw [← add_mul, add_comm, h2, mul_assoc]
    have h5 := s61_tri_succ L.card
    rw [mul_comm (L.card + 1) L.card] at h5
    have hsgn : (-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2) * (-1 : F) ^ (Lᶜ.card * Lᶜ.card) *
        (-1 : F) ^ s61_inv L Lᶜ *
        ((-1 : F) ^ (L.card * (L.card - 1) / 2) * (-1 : F) ^ s61_inv Lᶜ L) =
        (-1 : F) ^ (L.card + n) := by
      simp only [← pow_add]
      exact s61_neg_one_pow_congr (by omega)
    rw [s61_phiP_basisSHat, map_smul, s61_phiPX_basisS, compl_compl]
    simp only [smul_smul]
    congr 1
    linear_combination (basisSHat F n).repr t L * hsgn
  · have h0 : (basisSHat F n).repr t L = 0 := s61_repr_eq_zero_of_mem _ ht hL
    rw [h0, zero_smul, zero_smul, smul_zero]

end WeilClasses
