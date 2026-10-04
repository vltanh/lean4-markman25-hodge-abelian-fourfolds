module

public import WeilClasses.Chevalley.Defs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product

/-!
# Cohomology of products, Künneth isomorphisms and correspondences (paper §5.2, §6.1, §6.3)

**The model (a representation choice, documented here once).** The cohomology ring of a product
of two abelian varieties `Y × Z` is `⋀•(H¹(Y) ⊕ H¹(Z))`, with cup product the exterior product; the
pullbacks `π_Y^*`, `π_Z^*` are `ExteriorAlgebra.map` of the two inclusions, and the Künneth
isomorphism `H*(Y) ⊗ H*(Z) ≅ H*(Y × Z)` is `u ⊗ v ↦ π_Y^*u ∪ π_Z^*v` (Mathlib's
`ExteriorAlgebra.prodEquivTensor`, whose target is the graded tensor product). Concretely:

* `H*(X̂ × X, F)` and `H*(X × X̂, F)` are both `⋀•V` (`V = H¹(X̂) ⊕ H¹(X)`, dual summand first, the
  same ring); `kunnethHatX : H*(X̂) ⊗ H*(X) ≅ ⋀•V` is `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b` (the Künneth order
  used for `φ̃ : H*(X × X) → H*(X̂ × X)` in §6.3) and `kunnethXHat : H*(X) ⊗ H*(X̂) ≅ ⋀•V` is
  `u ⊗ v ↦ π_X^*u ∪ π_X̂^*v` (the order used for `H*(X × X̂)`, the target of Orlov's `φ`).
* `H*(X × X, F)` is `S ⊗ S` (as in the paper's (2.3.2) and (6.1.3)), `u ⊗ v` standing for
  `π₁^*u ∪ π₂^*v`; the ring `⋀•(H¹(X) ⊕ H¹(X))` is `SXX`, identified with `S ⊗ S` by `kunnethXX`.
* `[pt_{X×Y}] = π_X^*[pt_X] ∪ π_Y^*[pt_Y]` (even degrees, so the order is irrelevant), so that the
  push-forward along `π_Y` is `π_{Y*}(π_X^*a ∪ π_Y^*b) = (∫_X a) b`.
* **Correspondences.** For `γ ∈ H*(X × Y) = H*(X) ⊗ H*(Y)` the paper sets
  `γ_*(s) = π_{Y*}(π_X^*s ∪ γ)`; for `γ = Σ uᵢ ⊗ vᵢ` this is `γ_*(s) = Σ (∫_X s ∪ uᵢ) vᵢ` (proof of
  Lemma 5.2.1), which we take as the definition (`corr`). The cohomological action of an integral
  functor with kernel `𝒢` is `ch(𝒢)_*` (Todd classes of abelian varieties are trivial).
* **The map `μ(x, y) = (x + y, y)`** of `X × X` (§1.3, §6.1, §6.3) acts on `H¹(X × X) = H¹(X) ⊕
  H¹(X)`
  by `μ^*(a, b) = (a, a + b)`, i.e. `μ^*(π₁^*e) = π₁^*e + π₂^*e`, `μ^*(π₂^*e) = π₂^*e`; `μ^*` on
  `H*(X × X)` is the induced ring homomorphism (`muStarXX`, and `muStar` on `S ⊗ S`).
* `PD(s) = ∫_X (• ∪ s)` (§5.2), and `id ⊗ τ` (`tauTensor`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Correspondences (generic) -/

section Generic

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [AddCommGroup B] [Module F B]

theorem pdOf_apply (intA : A →ₗ[F] F) (u s : A) : pdOf intA u s = intA (s * u) := rfl

theorem corr_tmul (intA : A →ₗ[F] F) (u : A) (v : B) (s : A) :
    corr intA (u ⊗ₜ v) s = intA (s * u) • v := by
  simp [corr, pdOf_apply]

end Generic

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- Poincaré duality (§5.2) `PD : H*(X, F) → H*(X, F)*`, `PD(s) = ∫_X (• ∪ s)`. -/
noncomputable def PD : S F n →ₗ[F] Module.Dual F (S F n) := pdOf (integral F n)

/-! ## `X̂ × X` and `X × X̂` -/

/-- Künneth for `X̂ × X`: `H*(X̂) ⊗ H*(X) ≅ ⋀•V`, `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b`. -/
noncomputable def kunnethHatX : SHat F n ⊗[F] S F n ≃ₗ[F] ExtV F n :=
  (GradedTensorProduct.of F (fun i : ℕ => ⋀[F]^i (Module.Dual F (H1 F n)))
      (fun i : ℕ => ⋀[F]^i (H1 F n))).trans
    (ExteriorAlgebra.prodEquivTensor F (Module.Dual F (H1 F n)) (H1 F n)).symm.toLinearEquiv

omit [CharZero F] in
theorem kunnethHatX_tmul (a : SHat F n) (b : S F n) :
    kunnethHatX F n (a ⊗ₜ b) = pullXHat F n a * pullX F n b := rfl

theorem kunnethXHat_tmul (u : S F n) (v : SHat F n) :
    kunnethXHat F n (u ⊗ₜ v) = pullX F n u * pullXHat F n v := by
  sorry

/-! ## `X × X` -/

/-- `π₁^* : H*(X) → H*(X × X)`. -/
noncomputable def pull1 : S F n →ₐ[F] SXX F n :=
  ExteriorAlgebra.map (LinearMap.inl F (H1 F n) (H1 F n))

/-- `π₂^* : H*(X) → H*(X × X)`. -/
noncomputable def pull2 : S F n →ₐ[F] SXX F n :=
  ExteriorAlgebra.map (LinearMap.inr F (H1 F n) (H1 F n))

omit [CharZero F] in
theorem kunnethXX_tmul (u v : S F n) : kunnethXX F n (u ⊗ₜ v) = pull1 F n u * pull2 F n v := rfl

/-- `(μ^{-1})^*` on `H¹(X × X)`: `(a, b) ↦ (a, b - a)`. -/
noncomputable def mu1Inv : (H1 F n × H1 F n) →ₗ[F] (H1 F n × H1 F n) :=
  (LinearMap.fst F (H1 F n) (H1 F n)).prod
    (LinearMap.snd F (H1 F n) (H1 F n) - LinearMap.fst F (H1 F n) (H1 F n))

/-- `μ^* : H*(X × X) → H*(X × X)`, the ring homomorphism induced by `mu1`. -/
noncomputable def muStarXX : SXX F n →ₐ[F] SXX F n := ExteriorAlgebra.map (mu1 F n)

/-- `(μ^*)^{-1} = (μ^{-1})^*` on `H*(X × X) = S ⊗ S`. -/
noncomputable def muStarInv : S F n ⊗[F] S F n →ₗ[F] S F n ⊗[F] S F n :=
  (kunnethXX F n).symm.toLinearMap ∘ₗ (ExteriorAlgebra.map (mu1Inv F n)).toLinearMap ∘ₗ
    (kunnethXX F n).toLinearMap

/-- `id ⊗ τ` on `H*(X × X) = S ⊗ S`. -/
noncomputable def tauTensor : S F n ⊗[F] S F n →ₗ[F] S F n ⊗[F] S F n :=
  TensorProduct.map LinearMap.id (tau F n)

/-! ## Basic API -/

omit [CharZero F] in
/-- `μ^*(π₁^*e) = π₁^*e + π₂^*e` (§6.3). -/
theorem muStarXX_pull1_ι (w : H1 F n) :
    muStarXX F n (pull1 F n (ExteriorAlgebra.ι F w)) =
      pull1 F n (ExteriorAlgebra.ι F w) + pull2 F n (ExteriorAlgebra.ι F w) := by
  simp [muStarXX, pull1, pull2, mu1, ← map_add]

omit [CharZero F] in
/-- `μ^*(π₂^*e) = π₂^*e` (§6.3). -/
theorem muStarXX_pull2_ι (w : H1 F n) :
    muStarXX F n (pull2 F n (ExteriorAlgebra.ι F w)) = pull2 F n (ExteriorAlgebra.ι F w) := by
  simp [muStarXX, pull2, mu1]

theorem muStar_comp_muStarInv : muStar F n ∘ₗ muStarInv F n = LinearMap.id := by
  sorry

theorem muStarInv_comp_muStar : muStarInv F n ∘ₗ muStar F n = LinearMap.id := by
  sorry

omit [CharZero F] in
theorem tau_tau (s : S F n) : tau F n (tau F n s) = s :=
  CliffordAlgebra.reverse_reverse s

omit [CharZero F] in
theorem tauTensor_comp_tauTensor : tauTensor F n ∘ₗ tauTensor F n = LinearMap.id := by
  ext u v
  simp [tauTensor, tau_tau]

end Defs

end WeilClasses
