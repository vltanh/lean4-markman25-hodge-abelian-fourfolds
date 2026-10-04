module

public import WeilClasses.Chevalley.Defs
public import WeilClasses.External.Chevalley.Sec2_3

/-!
# Trautman, Theorem 1(i), as used in Remark 2.3.1 of the paper

[TT] A. Trautman, K. Trautman, *Generalized pure spinors*, J. Geom. Phys. 15 (1994), 1–22,
Theorem 1(i) (the paper's reference `trautman`, where `φ̃` is denoted by `E`): over a field of
characteristic zero, the isomorphism `E : S ⊗ S → ⋀•V` obtained from Chevalley's
`φ : S ⊗ S → C(V)` (2.2.5) by composing with the symmetric identification `C(V) ≅ ⋀•V` (the change
of form by `-½(·,·)_V`, Mathlib's `CliffordAlgebra.equivExterior`) is `Spin(V)`-equivariant, for
`m ⊗ m` on `S ⊗ S` and the grading-preserving action `⋀ρ` on `⋀•V`.

Used in Remark 2.3.1 ("In that case the resulting isomorphism `S_ℚ ⊗ S_ℚ → ⋀•V_ℚ` is
`Spin(V)`-equivariant ... (see [Trautman, Th. 1(i)])"), and, through the authorized algebraic proof
of Proposition 6.1.2, in §6.1.

## Proof

By naturality. Conjugation by `g ∈ Spin(V)` on `C(V)` is `CliffordAlgebra.map` of the isometry `ρ_g`
(`sb_conjSpin_eq_map`), and `ρ_g` preserves the symmetric form `-½(·,·)_V` by which `equivExterior`
changes the form (`sb_associated_rho`). A change of form by a bilinear form invariant under a linear
map `f` commutes with the algebra maps induced by `f` (`sb_changeForm_natural`, proved by induction
from `changeForm_ι_mul` and the naturality of contraction, `sb_contractLeft_natural`). Hence
`equivExterior(g x g⁻¹) = ⋀ρ_g(equivExterior x)`; composing with `φ(m_g u ⊗ m_g v) = g φ(u ⊗ v) g⁻¹`
([Chevalley, III.3.1], `chevalley_III_3_1_equivariant`, through `sb_varphi_map`) gives the theorem.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## Helpers: naturality of contraction and of the change of form -/

/-- Contraction is natural: if an algebra homomorphism `φ : C(Q) → C(Q')` maps `ι m` to `ι (f m)`,
then `d ⌋ φ(x) = φ((d ∘ f) ⌋ x)`. -/
theorem sb_contractLeft_natural {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q Q' : QuadraticForm R M} (φ : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q') (f : M →ₗ[R] M)
    (hφ : ∀ m, φ (ι Q m) = ι Q' (f m)) (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractLeft d (φ x) = φ (contractLeft (d ∘ₗ f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, contractLeft_algebraMap, contractLeft_algebraMap, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | ι_mul x m hx =>
    rw [map_mul, hφ, contractLeft_ι_mul, contractLeft_ι_mul, hx, map_sub, map_smul, map_mul, hφ,
      LinearMap.comp_apply]

/-- The change of form is natural: if `f : M → M` preserves the bilinear form `B` and the algebra
homomorphisms `φ : C(Q) → C(Q)`, `φ' : C(Q') → C(Q')` map `ι m` to `ι (f m)`, then
`changeForm h ∘ φ = φ' ∘ changeForm h`. -/
theorem sb_changeForm_natural {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M} (h : B.toQuadraticMap = Q' - Q)
    (φ : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q)
    (φ' : CliffordAlgebra Q' →ₐ[R] CliffordAlgebra Q') (f : M →ₗ[R] M)
    (hφ : ∀ m, φ (ι Q m) = ι Q (f m)) (hφ' : ∀ m, φ' (ι Q' m) = ι Q' (f m))
    (hB : ∀ u v, B (f u) (f v) = B u v) (x : CliffordAlgebra Q) :
    changeForm h (φ x) = φ' (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, changeForm_algebraMap, AlgHom.commutes]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | ι_mul x m hx =>
    have hd : B (f m) ∘ₗ f = B m := LinearMap.ext fun v => hB m v
    rw [map_mul, hφ, changeForm_ι_mul, changeForm_ι_mul, hx, sb_contractLeft_natural φ' f hφ', hd,
      map_sub, map_mul, hφ']

/-- `ρ_g` preserves the symmetric bilinear form `associated (-Q) = -½(·,·)_V` of `equivExterior`. -/
theorem sb_associated_rho (g : Spin F n) (u v : V F n) :
    QuadraticMap.associated (R := F) (-(Q F n)) (rho F n g u) (rho F n g v) =
      QuadraticMap.associated (R := F) (-(Q F n)) u v := by
  have hQ : ∀ w : V F n, Q F n (rho F n g w) = Q F n w := fun w =>
    spinVectorAction_map_app (Q F n) g w
  simp only [QuadraticMap.associated_apply, neg_apply, ← map_add, hQ]

/-- **[Trautman, Th. 1(i)]**, the special case used in Remark 2.3.1: `E = equivExterior ∘ φ`
(`varphiTildeSym`) satisfies `E((m_g ⊗ m_g)(y)) = ρ_g(E(y))` for `g ∈ Spin(V_F)`. -/
theorem trautman_theorem1_i (g : Spin F n) (y : S F n ⊗[F] S F n) :
    varphiTildeSym F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y) =
      rhoExt F n g (varphiTildeSym F n y) := by
  simp only [varphiTildeSym, psiSym, LinearMap.comp_apply, LinearEquiv.coe_coe]
  -- `φ((m_g ⊗ m_g) y) = g φ(y) g⁻¹ = map ρ_g (φ(y))` ([Chevalley, III.3.1])
  rw [sb_varphi_map, sb_conjSpin_eq_map, CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv_apply, CliffordAlgebra.changeFormEquiv_apply]
  -- `equivExterior` is the change of form by the `ρ_g`-invariant form `associated (-Q)`
  exact sb_changeForm_natural _ (CliffordAlgebra.map (sb_rhoIsometry F n g)) (rhoExt F n g)
    (rho F n g).toLinearMap (fun v => CliffordAlgebra.map_apply_ι _ v)
    (fun v => ExteriorAlgebra.map_apply_ι _ v) (sb_associated_rho F n g) _

end WeilClasses
