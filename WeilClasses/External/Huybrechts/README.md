# Huybrechts, *Fourier–Mukai transforms in algebraic geometry* (2006)

[Hu] D. Huybrechts, *Fourier–Mukai transforms in algebraic geometry*, Oxford University Press, 2006
(the paper's reference `huybrechts-derived-categories-book`, [H2]). The model:
`H*(X) = ⋀•H¹(X)`, `H*(X̂) = ⋀•H¹(X)*`, `H*(X × X̂) = ⋀•V` with the bases `e_K`, `f_L` (`basisS`,
`basisSHat`, `basisExt`); the cohomological Fourier–Mukai transforms are the correspondences
`φ_𝒫 = ch(𝒫)_*` with `c₁(𝒫) = Σᵢ π_X^*eᵢ ∪ π_X̂^*fᵢ` (`WeilClasses.Correspondence.FourierMukai`).
The results of [Hu] about derived categories that the paper cites in §5–§6.1 (Rem. 7.7, Cor. 9.37,
Prop. 9.39) are left out; Prop. 9.39 is the cohomological statement (6.1.8),
`WeilClasses.External.Orlov.Sec6_1`.

## `Sec6_3.lean`: Lemma 9.23 and Corollary 9.24 (prover SD)

Used in the footnote of the proof of Lemma 6.3.1 (TeX lines 2703–2710) and in the proof of
Lemma 6.3.2. All three statements are proved; none is a hypothesis.

* `huybrechts_lemma9_23_X`: `φ_𝒫 : H^k(X) → H^{2n-k}(X̂)` is `(-1)^{k(k+1)/2+n} PD_X`, with
  `PD_X(e_K) = ∫_X e_K ∧ (•) = ε_{K,K^c} f_{K^c}` (`PDX`).
* `huybrechts_lemma9_23_Xhat`: `φ_𝒫 : H^k(X̂) → H^{2n-k}(X)` is `(-1)^{k(k+1)/2+n} PD_k`, where
  `PD_k` is read as the inverse of `PD_X : H^{2n-k}(X) → H^k(X̂)` (`PDXinv`,
  `f_L ↦ ε_{L^c,L} e_{L^c}`). **Reading**: with `PD_X̂(f_L) = ε_{L,L^c} e_{L^c}` the formula fails
  by `(-1)^k`; this is the sign slip behind the corrected Lemma 6.3.2 (`WeilClasses.Orlov.Sec6_3`).
* `huybrechts_cor9_24`: the composition `H^k(X̂) → H^{2n-k}(X) → H^k(X̂)` of the two `φ_𝒫` is
  `(-1)^{k+n}`.

Proofs: on the bases. The kernel `ch(𝒫) = exp(c₁(𝒫)) = Σ_K (-1)^{|K|(|K|-1)/2} π_X^*e_K ∪ π_X̂^*f_K`
gives `φ_𝒫(e_L) = (-1)^{m(m-1)/2} ε_{L,L^c} f_{L^c}` and
`φ_𝒫(f_L) = (-1)^{m(m-1)/2 + m²} ε_{L,L^c} e_{L^c}`, `m = 2n - |L|` (`s61_phiPX_basisS`,
`s61_phiP_basisSHat` in `WeilClasses.Orlov.Defs`); the signs agree because
`m(m-1)/2 ≡ n + k(k+1)/2 (mod 2)` when `k + m = 2n` (`sd_tri_compl_mod_two`) and
`ε_{L,L^c} ε_{L^c,L} = (-1)^{km}`. Public helpers: `sd_tri_compl_mod_two`, `sd_PDX_basisS`,
`sd_PDXinv_basisSHat`.

Where §6.3 uses them: `psiPinvShift_eq_phiPX` (the footnote: `Ψ_{𝒫⁻¹}[n]` is the inverse of
`Φ_𝒫`, `ψ_{𝒫⁻¹[n]}(e_K)` has degree `2n - k` by Lemma 9.23 for `X̂ → X`, and Cor. 9.24 gives
`ψ_{𝒫⁻¹[n]} = (-1)^{k+n} φ_𝒫` on `H^k(X)`), `psiPinvShift_basis` (with Lemma 9.23 for `X → X̂`:
`ψ_{𝒫⁻¹[n]}(e_K) = (-1)^{k(k+3)/2} ε_{K,K^c} f_{K^c}`), and `sd_PiMap0_beta` (the computation of
`φ_𝒫 ⊗ ψ_{𝒫⁻¹}` on `f_L ∧ e_K` in the proof of Lemma 6.3.2, with Lemma 9.23 for `X̂ → X`).

## `Sec6_1.lean`: Exercise 9.41 (prover SD)

Used in §6.1 for the cocycle identity (6.1.9) (`equation6_1_9`, TeX line 2256). Proved; not a
hypothesis.

* `huybrechts_ex9_41`: if `c₁, c₂, c₁₂ ∈ ⋀²V` satisfy (6.1.8) for `g₁, g₂, g₁g₂` (i.e.
  `ρ'_g = exp(c) ∪ ρ_g`, the model of `ρ'_g = ch(N_g) ∪ ρ_g`), then `c₁₂ = c₁ + ρ_{g₁}(c₂)`.

Proof (the argument of the exercise): `ρ'` is a representation (`rhoPrimeRep`, (6.1.7)); evaluating
`ρ'_{g₁g₂} = ρ'_{g₁} ρ'_{g₂}` at `1` gives `exp(c₁₂) = exp(c₁ + ρ_{g₁}(c₂))` (degree-2 classes
commute and `ρ_{g₁}` is an algebra automorphism), and the degree-2 parts agree
(`s61_projDeg_two_exp`). It uses neither Proposition 6.1.2 nor [Orlov, Th. 2.10].
