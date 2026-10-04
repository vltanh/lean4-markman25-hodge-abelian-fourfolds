module

public import WeilClasses.Correspondence.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Algebra.Rat

/-!
# The Poincaré bundle and its cohomological Fourier–Mukai transforms (paper §1.2, §6.1, §6.3)

In the model (see `WeilClasses.Correspondence.Defs`), the geometric objects are replaced by their
cohomology classes:

* `c1P = c₁(𝒫) = Σᵢ π_X^*eᵢ ∪ π_X̂^*fᵢ ∈ H²(X × X̂) = ⋀²V`, the first Chern class of the
  (normalized) Poincaré line bundle. **Sign convention.** The class of `𝒫` in
  `H¹(X) ⊗ H¹(X̂) = End(H¹(X))` is `±id`, the sign depending on the identification
  `H¹(X̂) = H¹(X)*` ([BL, Th. 2.5.1, 2.6(2b)]). We fix the sign `+`: it is the one for which the
  footnote formula `ψ_{𝒫⁻¹[n]}(e_K) = (-1)^{k(k+3)/2} ε_{K,K^c} f_{K^c}` (proof of Lemma 6.3.1),
  Lemma 6.3.1 and Proposition 6.1.2 hold (checked numerically for `n = 1, 2`; with the opposite sign
  all three fail). No sign makes all of the paper's sign formulas hold: with this sign, Lemma 6.3.2
  fails in odd degrees (`WeilClasses.Orlov.Sec6_3`), the footnote's [Huybrechts, Lemma 9.23] for
  `H^k(X̂) → H^{2n-k}(X)` holds only with `PD_k` read as the inverse of `PD_X` (it fails by `(-1)^k`
  with `PD(f_L) = ε_{L,L^c} e_{L^c}`, `WeilClasses.External.Huybrechts.Sec6_3`), and Remark 2.3.1's
  `B̄₀ = ½c₁(𝒫)` holds through the isomorphism `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` but is `B̄₀ = -½c₁(𝒫)` through
  the determinant pairing (`WeilClasses.Chevalley.Sec2_3`).
* `chP = ch(𝒫) = exp(c₁(𝒫))` and `chPinvShift = ch(𝒫⁻¹[n]) = (-1)ⁿ exp(-c₁(𝒫))` (the shift `[n]`
  multiplies the Chern character by `(-1)ⁿ`), in `H*(X × X̂) = H*(X̂ × X) = ⋀•V`.
* `phiP = φ_𝒫 : H*(X̂) → H*(X)`, the cohomological transform `ch(𝒫)_*` of `Φ_𝒫 : Dᵇ(X̂) → Dᵇ(X)`
  (𝒫 on `X̂ × X`; §6.1); `phiPX = φ_𝒫 : H*(X) → H*(X̂)` (𝒫 on `X × X̂`; §1.2 and the footnote of
  §6.3); `psiPinvShift = ψ_{𝒫⁻¹[n]} : H*(X) → H*(X̂)`, the cohomological transform of
  `Ψ_{𝒫⁻¹[n]}`, the inverse of `Φ_𝒫`; `psiPinv = ψ_{𝒫⁻¹}` (no shift; Lemma 6.3.2).
* `PiMap = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)` (Lemma 6.1.1) and
  `PiMap0 = φ_𝒫 ⊗ ψ_{𝒫⁻¹}` (Lemma 6.3.2).
* Coordinates of the proof of Lemma 6.3.1: the signs `ε_{K,L}` (`e_K ∧ e_L = ε_{K,L} e_{K∪L}`),
  `Σ(K)`, Poincaré duality `PD_X(e_K) = ∫_X e_K ∧ (•) = ε_{K,K^c} f_{K^c}` (`PDX`; note the order
  of the factors, opposite to §5.2's `PD`), its inverse `PDXinv`, the pairing
  `H*(X̂) × H*(X) → F` (`⟨f_A, e_B⟩ = δ_{AB}`), `∫_{X̂ × X}` (`integralExt`, coefficient of
  `f₁ ∧ ⋯ ∧ f_{2n} ∧ e₁ ∧ ⋯ ∧ e_{2n}`) and the pairing of `H*(X × X̂)` with `H*(X̂ × X)` induced by
  `(·,·)_V` (`extPairing`, `⟨x₁ ∧ ⋯ ∧ x_k, y₁ ∧ ⋯ ∧ y_k⟩ = det((xᵢ, yⱼ)_V)`; proof of Lemma 6.3.2,
  Remark 6.3.3).

That `φ_𝒫`, `ψ_{𝒫⁻¹[n]}` are the cohomological actions of the Fourier–Mukai functors is the
Grothendieck–Riemann–Roch theorem (trivial Todd classes); in the model they are *defined* as these
correspondences.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## The Poincaré bundle -/

/-- `c₁(𝒫) = Σᵢ π_X^*eᵢ ∪ π_X̂^*fᵢ ∈ H²(X × X̂, ℤ) = ⋀²V` (sign convention in the module
docstring). -/
noncomputable def c1P : ExtV F n :=
  ∑ i : Fin (2 * n), pullX F n (ExteriorAlgebra.ι F (e F n i)) *
    pullXHat F n (ExteriorAlgebra.ι F (f F n i))

/-- `ch(𝒫) = exp(c₁(𝒫))` (𝒫 is a line bundle). -/
noncomputable def chP : ExtV F n := IsNilpotent.exp (c1P F n)

/-- `ch(𝒫⁻¹[n]) = (-1)ⁿ exp(-c₁(𝒫))`. -/
noncomputable def chPinvShift : ExtV F n := (-1 : F) ^ n • IsNilpotent.exp (-c1P F n)

/-- `φ_𝒫 = ch(𝒫)_* : H*(X̂) → H*(X)`, the cohomological action of `Φ_𝒫 : Dᵇ(X̂) → Dᵇ(X)` (𝒫 on
`X̂ × X`; §6.1, footnote in §6.3). -/
noncomputable def phiP : SHat F n →ₗ[F] S F n :=
  corr (integralHat F n) ((kunnethHatX F n).symm (chP F n))

/-- `φ_𝒫 = ch(𝒫)_* : H*(X) → H*(X̂)` (𝒫 on `X × X̂`; (1.2.5), footnote in §6.3). -/
noncomputable def phiPX : S F n →ₗ[F] SHat F n :=
  corr (integral F n) ((kunnethXHat F n).symm (chP F n))

/-- `ψ_{𝒫⁻¹[n]} = ch(𝒫⁻¹[n])_* : H*(X) → H*(X̂)`, the cohomological action of
`Ψ_{𝒫⁻¹[n]} : Dᵇ(X) → Dᵇ(X̂)`, the inverse of `Φ_𝒫` (§6.1). -/
noncomputable def psiPinvShift : S F n →ₗ[F] SHat F n :=
  corr (integral F n) ((kunnethXHat F n).symm (chPinvShift F n))

/-- `ψ_{𝒫⁻¹} = ch(𝒫⁻¹)_* : H*(X) → H*(X̂)` (no shift; Lemma 6.3.2): `(-1)ⁿ ψ_{𝒫⁻¹[n]}`. -/
noncomputable def psiPinv : S F n →ₗ[F] SHat F n :=
  corr (integral F n) ((kunnethXHat F n).symm (IsNilpotent.exp (-c1P F n)))

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} : H*(X̂ × X) → H*(X × X̂)` (Lemma 6.1.1):
`π_X̂^*a ∪ π_X^*b ↦ π_X^*φ_𝒫(a) ∪ π_X̂^*ψ_{𝒫⁻¹[n]}(b)`. -/
noncomputable def PiMap : ExtV F n →ₗ[F] ExtV F n :=
  (kunnethXHat F n).toLinearMap ∘ₗ TensorProduct.map (phiP F n) (psiPinvShift F n) ∘ₗ
    (kunnethHatX F n).symm.toLinearMap

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹} : H*(X̂ × X) → H*(X × X̂)` (Lemma 6.3.2; no shift). -/
noncomputable def PiMap0 : ExtV F n →ₗ[F] ExtV F n :=
  (kunnethXHat F n).toLinearMap ∘ₗ TensorProduct.map (phiP F n) (psiPinv F n) ∘ₗ
    (kunnethHatX F n).symm.toLinearMap

/-! ## Coordinates (proof of Lemma 6.3.1) -/

/-- `ε_{K,L} ∈ {-1, 0, 1}`, defined by `e_K ∧ e_L = ε_{K,L} e_{K ∪ L}` (proof of Lemma 6.3.1):
the coefficient of `e_{K ∪ L}` in `e_K ∧ e_L`. -/
noncomputable def epsSign (K L : Finset (Fin (2 * n))) : F :=
  (basisS F n).repr (basisS F n K * basisS F n L) (K ∪ L)

/-- `Σ(K) = Σ_{t} i_t` for `K = {i₁ < ⋯ < i_k} ⊆ [1, 2n]` (indices counted from `1`; our `Fin (2n)`
counts from `0`). -/
def sumIdx (K : Finset (Fin (2 * n))) : ℕ := ∑ i ∈ K, ((i : ℕ) + 1)

/-- Poincaré duality of the proof of Lemma 6.3.1, `PD_X : H^k(X) → H^{2n-k}(X̂) = H^{2n-k}(X)*`,
`PD_X(e_K) = ∫_X e_K ∧ (•) = ε_{K,K^c} f_{K^c}` (`PDX_spec`). -/
noncomputable def PDX : S F n →ₗ[F] SHat F n :=
  (basisS F n).constr F fun K => epsSign F n K Kᶜ • basisSHat F n Kᶜ

/-- The inverse `H^k(X̂) → H^{2n-k}(X)` of `PD_X`: `f_L ↦ ε_{L^c,L} e_{L^c}`. -/
noncomputable def PDXinv : SHat F n →ₗ[F] S F n :=
  (basisSHat F n).constr F fun L => epsSign F n Lᶜ L • basisS F n Lᶜ

/-- The pairing `H*(X̂) × H*(X) → F` identifying `H^k(X̂) = ⋀^k H¹(X)*` with `H^k(X)*`
(determinant pairing): `⟨f_A, e_B⟩ = δ_{AB}`. -/
noncomputable def pairSHatS : SHat F n →ₗ[F] S F n →ₗ[F] F :=
  (basisSHat F n).constr F fun A => (basisS F n).coord A

/-- `∫_{X̂ × X} : H*(X̂ × X) → F`, the coefficient of
`[pt_{X̂ × X}] = π_X̂^*[pt_X̂] ∪ π_X^*[pt_X] = f₁ ∧ ⋯ ∧ f_{2n} ∧ e₁ ∧ ⋯ ∧ e_{2n}` (the top vector of
`basisExt`; it is also `[pt_{X × X̂}]`). -/
noncomputable def integralExt : ExtV F n →ₗ[F] F := (basisExt F n).coord Finset.univ

/-- The degree-`k` component `⋀•V → ⋀^k V`, as an element of the submodule `⋀^k V`. -/
noncomputable def projDegSub (k : ℕ) : ExtV F n →ₗ[F] ⋀[F]^k (V F n) :=
  (DirectSum.component F ℕ (fun i : ℕ => ⋀[F]^i (V F n)) k) ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[F]^i (V F n))).toLinearMap

/-- The pairing between `H*(X × X̂) = ⋀•V` and `H*(X̂ × X) = ⋀•V` induced by `(·,·)_V` (which
identifies `V = H¹(X × X̂)` with `V* = H¹(X̂ × X)`, Remark 6.3.3): the sum over the degrees of the
determinant pairings `⟨x₁ ∧ ⋯ ∧ x_k, y₁ ∧ ⋯ ∧ y_k⟩ = det((xᵢ, yⱼ)_V)`
(`LinearMap.BilinForm.exteriorPower`). Used in the proof of Lemma 6.3.2. -/
noncomputable def extPairing : LinearMap.BilinForm F (ExtV F n) :=
  ∑ k ∈ Finset.range (4 * n + 1),
    ((pairing F n).exteriorPower k).compl₁₂ (projDegSub F n k) (projDegSub F n k)

end Defs

end WeilClasses
