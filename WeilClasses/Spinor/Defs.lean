module

public import WeilClasses.Defs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action
public import TauCeti.LinearAlgebra.QuadraticForm.Dual

/-!
# The spin representation of `V = H¹(X × X̂)` on `S = H*(X)` (paper §1.2 and §2.1)

Let `X` be an abelian `n`-fold. We fix a basis `e₁, …, e_{2n}` of `H¹(X, ℤ)` with
`∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1` and work with coefficients in a field `F` of characteristic zero
(`ℚ`, `K = ℚ(√-d)`, `ℝ` or `ℂ`), in these coordinates:

* `H¹(X, F) = F^{2n}` (`WeilClasses.H1`);
* `V_F = H¹(X̂, F) ⊕ H¹(X, F) = H¹(X, F)* × H¹(X, F)` (`WeilClasses.V`, (1.2.1)). The paper writes
  `(w, θ)`; we use Mathlib's order `(θ, w)` of `QuadraticForm.dualProd`;
* the pairing (1.2.2) `((w₁,θ₁),(w₂,θ₂))_V = θ₁(w₂) + θ₂(w₁)` is the polar form of
  `Q (θ, w) = θ w` (`WeilClasses.Q`, `WeilClasses.pairing`), so the Clifford relation (2.1.1)
  `v₁v₂ + v₂v₁ = (v₁,v₂)_V` is Mathlib's `ι v * ι v = Q v`;
* `S_F = H*(X, F) = ⋀• H¹(X, F)` (`WeilClasses.S`), with `[pt_X] = e₁ ∧ ⋯ ∧ e_{2n}` and `∫_X`
  the coefficient of `[pt_X]`;
* the main anti-automorphism `τ` (reversal, `(-1)^{i(i-1)/2}` on `H^i`) and the Mukai pairing
  (1.2.3) `(s, t)_S = ∫_X τ(s) ∪ t`;
* the spin representation (2.1.2)–(2.1.3) `m : C(V_F) → End(S_F)`, `m_{(θ,w)} = L_w + D_θ`
  (`WeilClasses.m`);
* `Spin(V_F)`, Mathlib's `spinGroup`, which over a field is the paper's
  `{x ∈ C(V)^even : x x* = 1, x V x* ⊆ V}`, and its standard representation
  `ρ(x)(v) = x v x⁻¹` (`WeilClasses.rho`).

The integral structures (`H¹(X, ℤ)`, `V`, `S`, the integral spin group) are in
`WeilClasses.Spinor.Integral`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-- `2` is invertible in a field of characteristic zero; the base-change and vector-action
constructions of Mathlib and Tau Ceti ask for this instance. -/
noncomputable instance invertibleTwoOfCharZero (F : Type*) [Field F] [CharZero F] :
    Invertible (2 : F) :=
  invertibleOfNonzero two_ne_zero

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The quadratic form `Q (θ, w) = θ(w)` on `V`. Its polar form is the pairing (1.2.2), and
`CliffordAlgebra (Q F n)` is the paper's Clifford algebra `C(V_F)` with relation (2.1.1). -/
abbrev Q : QuadraticForm F (V F n) := QuadraticForm.dualProd F (H1 F n)

/-- The pairing (1.2.2): `((w₁,θ₁),(w₂,θ₂))_V = θ₁(w₂) + θ₂(w₁)`. -/
noncomputable abbrev pairing : LinearMap.BilinForm F (V F n) := QuadraticMap.polarBilin (Q F n)

/-- The Clifford algebra `C(V_F)` of §2.1. -/
abbrev C : Type _ := CliffordAlgebra (Q F n)

/-- The basis of `⋀• V_F` induced by `basisV`, indexed by subsets of `Fin (2n + 2n)`. -/
noncomputable def basisExt : Module.Basis (Finset (Fin (2 * n + 2 * n))) F (ExteriorAlgebra F (V F n)) :=
  (basisV F n).ExteriorAlgebra

/-- The main anti-automorphism `τ` of `S` (and of `C(V)`): reversal of products, acting on `H^i`
by `(-1)^{i(i-1)/2}`. -/
noncomputable def tau : S F n →ₗ[F] S F n :=
  CliffordAlgebra.reverse (Q := (0 : QuadraticForm F (H1 F n)))

/-- The Mukai pairing (1.2.3): `(s, t)_S = ∫_X τ(s) ∪ t`. -/
noncomputable def mukai : LinearMap.BilinForm F (S F n) :=
  ((LinearMap.mul F (S F n)) ∘ₗ tau F n).compr₂ (integral F n)

/-- The even part `S⁺ = H^ev(X, F)` (a half-spin representation). -/
noncomputable def Splus : Submodule F (S F n) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)) 0

/-- The odd part `S⁻ = H^odd(X, F)`. -/
noncomputable def Sminus : Submodule F (S F n) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)) 1

/-- `L_w`: exterior multiplication by `w ∈ H¹(X, F)` on `S` (§2.1). -/
noncomputable def L : H1 F n →ₗ[F] Module.End F (S F n) :=
  (LinearMap.mul F (S F n)) ∘ₗ ExteriorAlgebra.ι F

/-- The embedding (2.1.2) `V → End(S)`, `m_{(θ, w)} = L_w + D_θ`. -/
noncomputable def cliffordOp : V F n →ₗ[F] Module.End F (S F n) :=
  L F n ∘ₗ LinearMap.snd F _ _ + D F n ∘ₗ LinearMap.fst F _ _

theorem cliffordOp_mul_self (v : V F n) :
    cliffordOp F n v * cliffordOp F n v = algebraMap F _ (Q F n v) := by
  obtain ⟨θ, w⟩ := v
  refine LinearMap.ext fun s => ?_
  simp only [cliffordOp, L, D, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.snd_apply,
    LinearMap.fst_apply, Module.End.mul_apply, LinearMap.mul_apply', Module.algebraMap_end_apply,
    QuadraticForm.dualProd_apply, map_add]
  -- `L_w² = 0`, `D_θ² = 0` and `D_θ L_w + L_w D_θ = θ(w)` (Leibniz rule for the contraction).
  have h1 : ExteriorAlgebra.ι F w * (ExteriorAlgebra.ι F w * s) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have h2 : contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ (ExteriorAlgebra.ι F w * s) =
      θ w • s - ExteriorAlgebra.ι F w * contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ s :=
    contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w s
  have h3 := contractLeft_contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ s
  rw [h1, h2, h3]
  abel

/-- The spin representation (2.1.3) `m : C(V_F) → End(S_F)`, the algebra homomorphism extending
`m_{(θ, w)} = L_w + D_θ`. -/
noncomputable def m : C F n →ₐ[F] Module.End F (S F n) :=
  CliffordAlgebra.lift (Q F n) ⟨cliffordOp F n, cliffordOp_mul_self F n⟩

/-- For a spinor `s ∈ S`, the map `m_s : V → S`, `v ↦ m_v(s)` (§2.1). -/
noncomputable def mOf (s : S F n) : V F n →ₗ[F] S F n :=
  (LinearMap.applyₗ s) ∘ₗ (m F n).toLinearMap ∘ₗ CliffordAlgebra.ι (Q F n)

/-- The conjugate representation `m†_g = τ m_g τ` of (5.2.1), on all of `C(V)`. -/
noncomputable def mDagger (x : C F n) : Module.End F (S F n) :=
  tau F n ∘ₗ m F n x ∘ₗ tau F n

/-- The spin group `Spin(V_F)`: Mathlib's `spinGroup`. Over a field it is the paper's
`{x ∈ C(V_F)^even : x x* = 1, x V x* ⊆ V}` (`WeilClasses.mem_spin_iff`). -/
abbrev Spin : Type _ := spinGroup (Q F n)

/-- The standard representation `ρ : Spin(V_F) → SO(V_F)`, `ρ(x)(v) = x v x⁻¹` (§2.1). On `Spin`,
`x⁻¹ = x*`, and Tau Ceti's twisted action agrees with it. -/
noncomputable def rho (g : Spin F n) : V F n ≃ₗ[F] V F n := spinVectorAction (Q F n) g

theorem ι_rho (g : Spin F n) (v : V F n) :
    CliffordAlgebra.ι (Q F n) (rho F n g v) = (g : C F n) * CliffordAlgebra.ι (Q F n) v * star (g : C F n) :=
  ι_spinVectorAction_apply (Q F n) g v

/-- The action `ρ_g = ⋀• ρ(g)` of `g ∈ Spin(V_F)` on `⋀• V_F = H*(X × X̂, F)`, preserving the
grading ((6.1.6)). -/
noncomputable def rhoExt (g : Spin F n) : ExteriorAlgebra F (V F n) →ₐ[F] ExteriorAlgebra F (V F n) :=
  ExteriorAlgebra.map (rho F n g : V F n →ₗ[F] V F n)

end Defs

end WeilClasses
