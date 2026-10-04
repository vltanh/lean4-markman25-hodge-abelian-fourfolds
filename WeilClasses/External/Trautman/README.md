# Trautman–Trautman, *Generalized pure spinors* (1994), Theorem 1(i)

[TT] A. Trautman, K. Trautman, *Generalized pure spinors*, J. Geom. Phys. 15 (1994), 1–22,
Theorem 1(i) (the paper's reference `trautman`; there `φ̃` is denoted by `E`).

## `Sec2_3.lean`: Theorem 1(i) (prover SB)

Used in Remark 2.3.1 ("the resulting isomorphism `S_ℚ ⊗ S_ℚ → ⋀•V_ℚ` is `Spin(V)`-equivariant") and,
through the authorized algebraic proof of Proposition 6.1.2, in §6.1. Proved; not a hypothesis.

Statement. `trautman_theorem1_i`: over a field `F` of characteristic zero, for `g ∈ Spin(V_F)` and
`y ∈ S ⊗ S`, `E((m_g ⊗ m_g) y) = ⋀ρ_g(E(y))`, where `E = varphiTildeSym = equivExterior ∘ φ`.

How the Lean form relates to [TT] and to the paper:

* `φ : S ⊗ S → C(V)` is Chevalley's map (2.2.5), `φ(u ⊗ v) = u [pt_X̂] τ(v)` (`varphi`).
* The identification `C(V) ≅ ⋀•V` is Mathlib's `CliffordAlgebra.equivExterior`, the change of form
  by the symmetric form `-½(·,·)_V` (`QuadraticMap.associated (-Q)`), i.e. the paper's `ψ` with `B₀`
  replaced by `½(·,·)_V` as in Remark 2.3.1 (`psiSym`). It depends only on `(·,·)_V`, which
  `Spin(V)` preserves, whereas `ψ` for `B₀` depends on the splitting `V = H¹(X̂) ⊕ H¹(X)`, which
  `Spin(V)` does not preserve.
* `Spin(V)` acts on `S ⊗ S` by `m_g ⊗ m_g` and on `⋀•V` by `⋀ρ_g` (`rhoExt`), `ρ_g(v) = g v g⁻¹`.

Proof (naturality). Conjugation by `g` on `C(V)` is `CliffordAlgebra.map` of the isometry `ρ_g`
(`sb_conjSpin_eq_map`, in `WeilClasses.External.Chevalley.Sec2_3`), and `ρ_g` preserves the
symmetric form of `equivExterior` (`sb_associated_rho`). A change of form by a bilinear form that is
invariant under a linear map `f` commutes with the algebra maps induced by `f`
(`sb_changeForm_natural`, by induction from `changeForm_ι_mul` and the naturality of contraction
`sb_contractLeft_natural`), so `equivExterior(g x g⁻¹) = ⋀ρ_g(equivExterior(x))`. Composing with
[Chevalley, III.3.1] (`chevalley_III_3_1_equivariant`, cited in
`WeilClasses.External.Chevalley.Sec2_2`; `sb_varphi_map`) gives the theorem. The proof depends on
that cited statement and on nothing else that is cited. Public helpers: `sb_contractLeft_natural`,
`sb_changeForm_natural`, `sb_associated_rho`.
