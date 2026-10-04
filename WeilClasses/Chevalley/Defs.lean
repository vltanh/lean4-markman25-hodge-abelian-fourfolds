module

public import WeilClasses.Spinor.Embeddings
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Chevalley's isomorphisms `φ : S ⊗ S → C(V)` (2.2.5) and `φ̃ = ψ ∘ φ : S ⊗ S → ⋀•V` (2.3.2)

Definitions for the paper's §2.3 ("The isomorphism `φ̃ : S ⊗ S → ∧*V`") and for the map `φ` of
(2.2.5) (defined in the proof of Lemma 2.2.6).

(`H*(X̂) = SHat`, `⋀•V = ExtV` and `[pt_X̂]` are in `WeilClasses.Defs` and
`WeilClasses.Spinor.Embeddings`.)

* `B0`: the paper's bilinear form `B₀(v₁, v₂) = θ₂(w₁)` for `vᵢ = (wᵢ, θᵢ)` (in our order
  `vᵢ = (θᵢ, wᵢ)`), with `B₀(u, u) = ½(u, u)_V = Q(u)`; its alternating part `B0bar`.
* `Lprime x = L_x + δ_x` on `⋀•V` (`δ_x` = contraction with `B₀(x, ·)`), the algebra homomorphism
  `psiPrime : C(V) → End(⋀•V)` it induces, and `psi : C(V) → ⋀•V` (2.3.1),
  `ψ(x) = ψ'(x) · 1`. We define `ψ` as Mathlib's `CliffordAlgebra.changeForm` into
  `CliffordAlgebra 0 = ExteriorAlgebra` for the bilinear form `-B₀`; `psi_apply_eq_psiPrime`
  (in `WeilClasses.Chevalley.Sec2_3`) is the bridge to the paper's definition.
* The filtrations `C(V)_k` (`CFilt`, and `CFiltLT k = C(V)_{k-1}`), `F^k(⋀•V) = ⊕_{i ≤ k} ⋀^i V`
  (`extFiltLE`), `F_k(⋀•V) = ⊕_{i ≥ k} ⋀^i V` (`extFiltGE`, (6.1.5)); the projection `projDeg k`
  to `⋀^k V` is in `WeilClasses.Defs`.
* Chevalley's `φ(u ⊗ v) = u [pt_X̂] τ(v)` (`varphi`, (2.2.5), in `WeilClasses.Spinor.Embeddings`,
  with the embeddings `iotaX`, `iotaXHat` and `ptHatC`) and `φ̃ = ψ ∘ φ` (`varphiTilde`, (2.3.2)).
* The symmetric variant of Remark 2.3.1 (`B₀` replaced by `½(·,·)_V`): `psiSym` (Mathlib's
  `CliffordAlgebra.equivExterior`) and `varphiTildeSym`; `changeB0bar`, the change of form by the
  alternating part `B̄₀` (so that `ψ = changeB0bar ∘ psiSym`).
* `conjSpin g x = g x g⁻¹`, the conjugation action of `Spin(V)` on `C(V)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## The bilinear form `B₀` -/

/-- The paper's bilinear form `B₀` on `V` (§2.3): for `vᵢ = (wᵢ, θᵢ)` in the paper's order,
`B₀(v₁, v₂) = θ₂(w₁)`. In our order `vᵢ = (θᵢ, wᵢ)`: `B0 v₁ v₂ = v₂.1 v₁.2`. It is not symmetric
and satisfies `B₀(u, u) = θ(w) = ½(u, u)_V = Q(u)`. (Chevalley [Sec. 3.3] uses `θ₁(w₂)` instead.) -/
noncomputable def B0 : LinearMap.BilinForm F (V F n) :=
  ((LinearMap.applyₗ (R := F) (M := H1 F n) (M₂ := F)).compl₂
      (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n))) ∘ₗ
    LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n)

omit [CharZero F] in
theorem B0_apply (v₁ v₂ : V F n) : B0 F n v₁ v₂ = v₂.1 v₁.2 := rfl

omit [CharZero F] in
/-- `B₀(u, u) = Q(u)`, i.e. the quadratic form of `-B₀` is `0 - Q`; this is the hypothesis of
Mathlib's `CliffordAlgebra.changeForm` from `C(V)` to `CliffordAlgebra 0 = ⋀•V`. -/
theorem neg_B0_toQuadraticMap :
    (-B0 F n).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n := by
  ext v
  simp [B0_apply]

/-- The alternating part `½(B - Bᵀ)` of a bilinear form on `V`, i.e. its projection to
`∧²V* = V* ⊗ V* / Sym²(V*)` (Remark 2.3.1). -/
noncomputable def altPart (B : LinearMap.BilinForm F (V F n)) : LinearMap.BilinForm F (V F n) :=
  (2 : F)⁻¹ • (B - B.flip)

/-- `B̄₀`, the alternating part of `B₀` (Remark 2.3.1). -/
noncomputable def B0bar : LinearMap.BilinForm F (V F n) := altPart F n (B0 F n)

omit [CharZero F] in
theorem B0bar_apply (v₁ v₂ : V F n) :
    B0bar F n v₁ v₂ = (2 : F)⁻¹ * (B0 F n v₁ v₂ - B0 F n v₂ v₁) := by
  simp [B0bar, altPart]

omit [CharZero F] in
/-- `B̄₀` is alternating, so the quadratic form of `-B̄₀` is `0 = 0 - 0`. -/
theorem neg_B0bar_toQuadraticMap :
    (-B0bar F n).toQuadraticMap =
      (0 : QuadraticForm F (V F n)) - (0 : QuadraticForm F (V F n)) := by
  ext v
  simp [B0bar_apply]

/-! ## `ψ' : C(V) → End(⋀•V)` and `ψ : C(V) → ⋀•V` (2.3.1) -/

/-- `L_x : ⋀•V → ⋀•V`, `L_x(u) = x ∧ u`. -/
noncomputable def Lext : V F n →ₗ[F] Module.End F (ExtV F n) :=
  (LinearMap.mul F (ExtV F n)) ∘ₗ ExteriorAlgebra.ι F

/-- `δ_x : ⋀•V → ⋀•V`, contraction with the functional `B₀(x, ·)`. -/
noncomputable def delta : V F n →ₗ[F] Module.End F (ExtV F n) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (V F n)))) ∘ₗ B0 F n

/-- `L'_x = L_x + δ_x` (§2.3). -/
noncomputable def Lprime : V F n →ₗ[F] Module.End F (ExtV F n) := Lext F n + delta F n

omit [CharZero F] in
/-- `(L'_x)² = Q(x) · 1`, the relation needed to extend `x ↦ L'_x` to `C(V)`
(see `Lprime_sq` for the paper's form `½(x, x)_V · 1`). -/
theorem Lprime_mul_self (x : V F n) :
    Lprime F n x * Lprime F n x = algebraMap F (Module.End F (ExtV F n)) (Q F n x) := by
  refine LinearMap.ext fun y => ?_
  have h1 : ExteriorAlgebra.ι F x * (ExteriorAlgebra.ι F x * y) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have h2 := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm F (V F n))) (B0 F n x) x y
  have h3 := CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm F (V F n)))
    (B0 F n x) y
  simp only [Lprime, Lext, delta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    Module.End.mul_apply, LinearMap.mul_apply', map_add, Module.algebraMap_end_apply]
  rw [h1]
  erw [h2, h3]
  rw [B0_apply]
  simp only [QuadraticForm.dualProd_apply, zero_add, add_zero]
  erw [sub_add_cancel]

/-- `ψ' : C(V) → End(⋀•V)`, the algebra homomorphism extending `x ↦ L'_x` (universal property of
`C(V)`, [Chevalley, II.1.1]). -/
noncomputable def psiPrime : C F n →ₐ[F] Module.End F (ExtV F n) :=
  CliffordAlgebra.lift (Q F n) ⟨Lprime F n, Lprime_mul_self F n⟩

/-- **(2.3.1)** (`eq-psi`) `ψ : C(V) → ⋀•V`, `ψ(x) = ψ'(x) · 1`. Defined as Mathlib's
`CliffordAlgebra.changeForm` for the bilinear form `-B₀` (from `Q` to the zero form):
`changeForm (ι v * x) = v ∧ changeForm x + B₀(v, ·) ⌋ changeForm x` and `changeForm 1 = 1`, which is
`ψ(v x) = L'_v ψ(x)`, `ψ(1) = 1`. The bridge to `ψ'(·) 1` is `psi_apply_eq_psiPrime`. -/
noncomputable def psi : C F n →ₗ[F] ExtV F n :=
  CliffordAlgebra.changeForm (neg_B0_toQuadraticMap F n)

/-! ## Filtrations -/

/-- `C(V)_k`: the span of the products of `j ≤ k` elements of `V` (§2.3), an increasing filtration
`C(V)_0 ⊆ C(V)_1 ⊆ ⋯ ⊆ C(V)_{4n} = C(V)`. -/
noncomputable def CFilt (k : ℕ) : Submodule F (C F n) :=
  ⨆ (i : ℕ) (_ : i ≤ k), LinearMap.range (CliffordAlgebra.ι (Q F n)) ^ i

/-- `C(V)_{k-1}`, the span of the products of `j < k` elements of `V` (with `C(V)_{-1} = 0`). -/
noncomputable def CFiltLT (k : ℕ) : Submodule F (C F n) :=
  ⨆ (i : ℕ) (_ : i < k), LinearMap.range (CliffordAlgebra.ι (Q F n)) ^ i

/-- The increasing filtration `F^k(⋀•V) = ⊕_{i ≤ k} ⋀^i V` (§2.3). -/
noncomputable def extFiltLE (k : ℕ) : Submodule F (ExtV F n) :=
  ⨆ (i : ℕ) (_ : i ≤ k), ⋀[F]^i (V F n)

/-- **(6.1.5)** (`eq-decreasing-weight-filtration`) The decreasing filtration `F_k(⋀•V) = ⊕_{i ≥ k}
⋀^i V`. -/
noncomputable def extFiltGE (k : ℕ) : Submodule F (ExtV F n) :=
  ⨆ (i : ℕ) (_ : k ≤ i), ⋀[F]^i (V F n)

/-! ## Chevalley's `φ : S ⊗ S → C(V)` (2.2.5) -/

/-- **(2.3.2)** (`eq-tilde-varphi`) `φ̃ = ψ ∘ φ : S ⊗ S → ⋀•V`. Via the Künneth theorem this is an
isomorphism `H*(X × X) → H*(X × X̂)` (§2.3; in the Künneth order of §6.3, `H*(X̂ × X)`). -/
noncomputable def varphiTilde : S F n ⊗[F] S F n →ₗ[F] ExtV F n := psi F n ∘ₗ varphi F n

/-! ## The symmetric variant (Remark 2.3.1) -/

/-- `ψ` for `B₀` replaced by `½(·,·)_V` (Remark 2.3.1): Mathlib's `CliffordAlgebra.equivExterior`
(the change of form by `-½(·,·)_V`). -/
noncomputable def psiSym : C F n →ₗ[F] ExtV F n :=
  (CliffordAlgebra.equivExterior (Q F n)).toLinearMap

/-- `φ̃` for `B₀` replaced by `½(·,·)_V` (Remark 2.3.1; Trautman's `E`). -/
noncomputable def varphiTildeSym : S F n ⊗[F] S F n →ₗ[F] ExtV F n := psiSym F n ∘ₗ varphi F n

/-- The change of form `⋀•V → ⋀•V` by the alternating form `-B̄₀` (Mathlib's `changeForm` from the
zero form to itself): `changeB0bar (v ∧ x) = v ∧ changeB0bar x + B̄₀(v, ·) ⌋ changeB0bar x`. Since
`B₀ = ½(·,·)_V + B̄₀`, `ψ = changeB0bar ∘ psiSym` (`changeForm_changeForm`). -/
noncomputable def changeB0bar : ExtV F n →ₗ[F] ExtV F n :=
  CliffordAlgebra.changeForm (neg_B0bar_toQuadraticMap F n)

/-! ## The conjugation action of `Spin(V)` on `C(V)` -/

/-- The conjugation action `x ↦ g x g⁻¹` of `g ∈ Spin(V)` on `C(V)` (§2.3). -/
noncomputable def conjSpin (g : Spin F n) (x : C F n) : C F n :=
  (g : C F n) * x * ((g⁻¹ : Spin F n) : C F n)

end Defs

end WeilClasses
