module

public import WeilClasses.Correspondence.FourierMukai
public import Mathlib.RepresentationTheory.Basic

/-!
# The cohomological action of Orlov's equivalence (paper §1.3, §6.1, §6.3)

Orlov's equivalence `Φ = (id × Ψ_{𝒫⁻¹[n]}) ∘ μ^* : Dᵇ(X × X) → Dᵇ(X × X̂)` (6.1.2) induces the
correspondence isomorphism `φ : S ⊗ S → ⋀•V` (6.1.3) on cohomology. **In the model, `φ` is defined
as the composite of the cohomological transforms**, `φ := (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*` (`phiOrlov`);
that this is the Chern character of Orlov's kernel acting by correspondence is geometric
(Grothendieck–Riemann–Roch with trivial Todd classes) and is not stated.

* `phiOrlov = φ` (6.1.3): `H*(X × X) = S ⊗ S → H*(X × X̂) = ⋀•V`;
* `nuOrlov = ν = (ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^* : H*(X × X) → H*(X̂ × X)` (§6.3);
* `phiPrime = φ ∘ (id ⊗ τ)` (Prop. 1.3.1, (1.3.1)), with explicit inverses `phiOrlovInv`,
  `phiPrimeInv` (`φ⁻¹ = (μ^*)⁻¹ ∘ (id ⊗ φ_𝒫)`, since `φ_𝒫 = ψ_{𝒫⁻¹[n]}⁻¹`);
* `rhoPrime g = ρ'_g = φ' (m_g ⊗ m_g) φ'⁻¹ = φ (m_g ⊗ m†_g) φ⁻¹` (6.1.4) and the explicit
  `rhoPrimeFormula g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g` (the right side of (6.1.10), and the
  intro's definition of `ρ'`);
* the representations `ρ` (6.1.6, `rhoRep`) and `ρ'` (6.1.7, `rhoPrimeRep`) of `Spin(V)` on `⋀•V`;
* `phiTildeIntro = exp(-c₁(𝒫)/2) ∪ φ ∘ (id ⊗ τ)` (1.3.2) (`φ̃` of the introduction, not to be
  confused with Chevalley's `φ̃` (2.3.2), `varphiTilde`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `ν = (ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^* : H*(X × X) → H*(X̂ × X)` (§6.3), the cohomological action of
`(Ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^*`; `H*(X̂ × X) = ⋀•V` by `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b`. -/
noncomputable def nuOrlov : S F n ⊗[F] S F n →ₗ[F] ExtV F n :=
  (kunnethHatX F n).toLinearMap ∘ₗ TensorProduct.map (psiPinvShift F n) LinearMap.id ∘ₗ
    muStar F n

/-- `φ' = φ ∘ (id ⊗ τ)`. -/
noncomputable def phiPrime : S F n ⊗[F] S F n →ₗ[F] ExtV F n := phiOrlov F n ∘ₗ tauTensor F n

/-- The inverse `φ⁻¹ = (μ^*)⁻¹ ∘ (id ⊗ φ_𝒫)` of `φ` (`φ_𝒫 = ψ_{𝒫⁻¹[n]}⁻¹`, footnote in §6.3);
see `phiOrlov_comp_phiOrlovInv`. -/
noncomputable def phiOrlovInv : ExtV F n →ₗ[F] S F n ⊗[F] S F n :=
  muStarInv F n ∘ₗ TensorProduct.map LinearMap.id (phiP F n) ∘ₗ (kunnethXHat F n).symm.toLinearMap

/-- The inverse `φ'⁻¹ = (id ⊗ τ) ∘ φ⁻¹` of `φ'`. -/
noncomputable def phiPrimeInv : ExtV F n →ₗ[F] S F n ⊗[F] S F n :=
  tauTensor F n ∘ₗ phiOrlovInv F n

/-! ## Invertibility -/

/-- `Ψ_{𝒫⁻¹[n]}` is the inverse of `Φ_𝒫` (footnote in §6.3): `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`. -/
theorem phiP_comp_psiPinvShift : phiP F n ∘ₗ psiPinvShift F n = LinearMap.id := by
  sorry

/-- `ψ_{𝒫⁻¹[n]} ∘ φ_𝒫 = id`. -/
theorem psiPinvShift_comp_phiP : psiPinvShift F n ∘ₗ phiP F n = LinearMap.id := by
  sorry

theorem phiOrlov_comp_phiOrlovInv : phiOrlov F n ∘ₗ phiOrlovInv F n = LinearMap.id := by
  sorry

theorem phiOrlovInv_comp_phiOrlov : phiOrlovInv F n ∘ₗ phiOrlov F n = LinearMap.id := by
  sorry

/-- `φ'` is invertible, with inverse `phiPrimeInv` (needed for (6.1.4)). -/
theorem phiPrime_comp_phiPrimeInv : phiPrime F n ∘ₗ phiPrimeInv F n = LinearMap.id := by
  sorry

theorem phiPrimeInv_comp_phiPrime : phiPrimeInv F n ∘ₗ phiPrime F n = LinearMap.id := by
  sorry

/-! ## The representations `ρ` and `ρ'` -/

/-- **(6.1.4)** (`rho-prime-g`) `ρ'_g = φ' (m_g ⊗ m_g) φ'⁻¹ : ⋀•V → ⋀•V`, `φ' = φ ∘ (id ⊗ τ)`;
equivalently `ρ'_g = φ (m_g ⊗ m†_g) φ⁻¹` as printed (`rhoPrime_eq_phiOrlov_conj`). -/
noncomputable def rhoPrime (g : Spin F n) : Module.End F (ExtV F n) :=
  phiPrime F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) ∘ₗ phiPrimeInv F n

/-- The right side of (6.1.10) (and the introduction's definition of `ρ'_g`):
`x ↦ exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g(x)`. -/
noncomputable def rhoPrimeFormula (g : Spin F n) : Module.End F (ExtV F n) :=
  LinearMap.mulLeft F (IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n)))) ∘ₗ
    (rhoExt F n g).toLinearMap

/-- **(6.1.6)** (`eq-rho-extended-to-exterior-algebra`) `ρ : Spin(V) → GL(⋀•V)`, acting on `⋀^k V`
by `⋀^k ρ_g`. -/
noncomputable def rhoRep : Representation F (Spin F n) (ExtV F n) where
  toFun g := (rhoExt F n g).toLinearMap
  map_one' := by
    have h : (rho F n 1 : V F n →ₗ[F] V F n) = LinearMap.id := by
      simp [rho]
    simp only [rhoExt, h, ExteriorAlgebra.map_id]
    rfl
  map_mul' g h := by
    have hh : (rho F n (g * h) : V F n →ₗ[F] V F n) =
        (rho F n g : V F n →ₗ[F] V F n) ∘ₗ (rho F n h : V F n →ₗ[F] V F n) := by
      simp [rho]; rfl
    simp only [rhoExt, hh, ← ExteriorAlgebra.map_comp_map]
    rfl

/-- **(6.1.7)** (`eq-rho-prime`) `ρ' : Spin(V) → GL(⋀•V)`, `g ↦ ρ'_g` (6.1.4). -/
noncomputable def rhoPrimeRep : Representation F (Spin F n) (ExtV F n) where
  toFun g := rhoPrime F n g
  map_one' := by
    have h1 : m F n ((1 : Spin F n) : C F n) = LinearMap.id := by
      rw [OneMemClass.coe_one, map_one]; rfl
    show rhoPrime F n 1 = 1
    simp only [rhoPrime, h1, TensorProduct.map_id, LinearMap.id_comp]
    exact phiPrime_comp_phiPrimeInv F n
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    have hinv : ∀ y, phiPrimeInv F n (phiPrime F n y) = y := fun y => by
      rw [← LinearMap.comp_apply (phiPrimeInv F n) (phiPrime F n) y, phiPrimeInv_comp_phiPrime,
        LinearMap.id_apply]
    have hm : m F n ((g * h : Spin F n) : C F n) = m F n (g : C F n) * m F n (h : C F n) := by
      rw [Submonoid.coe_mul, map_mul]
    rw [Module.End.mul_apply]
    simp only [rhoPrime, LinearMap.comp_apply]
    rw [hinv, hm, TensorProduct.map_mul, Module.End.mul_apply]

/-! ## The introduction's `φ̃` (1.3.2) -/

/-- **(1.3.2)** (`eq-tilde-phi`) `φ̃ = exp(-c₁(𝒫)/2) ∪ φ ∘ (id ⊗ τ) : H*(X × X, ℚ) → H*(X × X̂, ℚ)`
(the
introduction's `\tilde{\phi}`; Chevalley's `\tilde{\varphi}` (2.3.2) is `varphiTilde`). -/
noncomputable def phiTildeIntro : S F n ⊗[F] S F n →ₗ[F] ExtV F n :=
  LinearMap.mulLeft F (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n))) ∘ₗ phiPrime F n

end Defs

end WeilClasses
