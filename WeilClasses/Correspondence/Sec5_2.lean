module

public import WeilClasses.Correspondence.Defs

/-!
# §5.2: `Spin(V)`-equivariance of convolutions

Statements of the paper's §5.2 (TeX lines 1994–2123): the conjugate representation `m†` (5.2.1),
the invariance (5.2.2), (5.2.3) of the Poincaré pairing `∫_X s ∪ t` under `m† ⊗ m` and `m ⊗ m†`,
the behaviour of `PD` under `m`, Lemma 5.2.1 (with (5.2.4)), Corollary 5.2.2 and Remark 5.2.3.

**Model.** `H*(X × Y) = H*(X) ⊗ H*(Y)` and `γ_*` is `corr` (see
`WeilClasses.Correspondence.Defs`). The paper takes `X`, `Y`, `Z` to be abelian varieties of the
same
dimension `n` (§5.1); the statements and proofs of §5.2 do not use this, and we allow dimensions
`nX`, `nY`, `nZ`. Coefficients: a field `F` of characteristic `0` (the paper: `ℚ`).

**Left out (sheaf-theoretic, §5.1).** The integral functors `Φ_F`, `Ψ_F`, convolution of kernels,
Grothendieck–Verdier duality (5.1.1), the exact sequence (5.1.2) of [GLO, Prop. 4.3.7, Cor. 4.3.8],
the cohomological identity (5.1.3) `φ_{G_R} = τ φ_G τ`, the GRR formula for `ch(F ∗ G)`, and in
Remark 5.2.3 the fact `ch(F^∨) = τ(ch(F))`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section OneVariety

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **(5.2.1)** (`eq-m-dagger`) `m†_g = τ m_g τ` (the foundation's `mDagger`, defined on all of
`C(V)`). -/
theorem equation5_2_1 (g : Spin F n) :
    mDagger F n (g : C F n) = tau F n ∘ₗ m F n (g : C F n) ∘ₗ tau F n := rfl

/-- (5.2.1) `m† : Spin(V) → GL(S)` is a homomorphism (`τ² = 1`). -/
theorem mDagger_mul (x y : C F n) : mDagger F n (x * y) = mDagger F n x ∘ₗ mDagger F n y := by
  sorry

theorem mDagger_one : mDagger F n 1 = LinearMap.id := by
  sorry

/-- **(5.2.2)** (`eq-invariance-of-Poincare-pairing`)
`∫_X m†_g(s) ∪ m_g(t) = (m_g(τ(s)), m_g(t))_S = (τ(s), t)_S = ∫_X s ∪ t`
for all `s, t ∈ S` and `g ∈ Spin(V)` (the second equality is the `Spin(V)`-invariance of the Mukai
pairing (1.2.3)). -/
theorem equation5_2_2 (g : Spin F n) (s t : S F n) :
    integral F n (mDagger F n (g : C F n) s * m F n (g : C F n) t) =
        mukai F n (m F n (g : C F n) (tau F n s)) (m F n (g : C F n) t) ∧
      mukai F n (m F n (g : C F n) (tau F n s)) (m F n (g : C F n) t) = mukai F n (tau F n s) t ∧
      mukai F n (tau F n s) t = integral F n (s * t) := by
  sorry

/-- **(5.2.3)** (`eq-second-invariance-of-Poincare-pairing`)
`∫_X m_g(s) ∪ m†_g(t) = ∫_X s ∪ t` for all `s, t ∈ H*(X)` and `g ∈ Spin(V)`. -/
theorem equation5_2_3 (g : Spin F n) (s t : S F n) :
    integral F n (m F n (g : C F n) s * mDagger F n (g : C F n) t) = integral F n (s * t) := by
  sorry

/-- (§5.2, TeX line 2049) `PD(m_h(s)) = PD(s) ∘ m†_{h⁻¹}` for all `h ∈ Spin(V)`, where
`PD(s) = ∫_X (• ∪ s)`. -/
theorem PD_m (h : Spin F n) (s : S F n) :
    PD F n (m F n (h : C F n) s) = PD F n s ∘ₗ mDagger F n ((h⁻¹ : Spin F n) : C F n) := by
  sorry

/-- **Remark 5.2.3** (`rem-invariance-of-w-vee`), the cohomological claim: for `w ∈ S⁺`, the class
`w^∨ = τ(w)` is `Spin(V)_w`-invariant with respect to the `m†`-action. (The geometric input, that
`τ(ch(F)) = ch(F^∨)` for an object `F` of `Dᵇ(X)`, is left out.) -/
theorem remark5_2_3 (w : S F n) (hw : w ∈ Splus F n) (g : Spin F n) (hg : m F n (g : C F n) w = w) :
    mDagger F n (g : C F n) (tau F n w) = tau F n w := by
  sorry

end OneVariety

section Correspondences

variable (F : Type*) [Field F] [CharZero F] (nX nY nZ : ℕ)

/-- **Lemma 5.2.1** (`lemma-action-of-m-h-tensor-1`), first equality: for `γ ∈ H*(X × Y)`,
`h ∈ Spin(V_X)` and `g ∈ Spin(V_Y)`, `[(m_h ⊗ m†_g)(γ)]_* = m†_g ∘ γ_* ∘ m†_{h⁻¹}`. -/
theorem lemma5_2_1_1 (h : Spin F nX) (g : Spin F nY) (γ : S F nX ⊗[F] S F nY) :
    corr (integral F nX) (TensorProduct.map (m F nX (h : C F nX)) (mDagger F nY (g : C F nY)) γ) =
      mDagger F nY (g : C F nY) ∘ₗ corr (integral F nX) γ ∘ₗ
        mDagger F nX ((h⁻¹ : Spin F nX) : C F nX) := by
  sorry

/-- **Lemma 5.2.1** (`lemma-action-of-m-h-tensor-1`), second equality **(5.2.4)**
(`eq-equivariance-of-mapping-correspondence-to-homomorphism`): for `γ ∈ H*(X × Y)`,
`h ∈ Spin(V_X)` and `g ∈ Spin(V_Y)`, `[(m†_h ⊗ m_g)(γ)]_* = m_g ∘ γ_* ∘ m_{h⁻¹}`. -/
theorem lemma5_2_1_2 (h : Spin F nX) (g : Spin F nY) (γ : S F nX ⊗[F] S F nY) :
    corr (integral F nX) (TensorProduct.map (mDagger F nX (h : C F nX)) (m F nY (g : C F nY)) γ) =
      m F nY (g : C F nY) ∘ₗ corr (integral F nX) γ ∘ₗ m F nX ((h⁻¹ : Spin F nX) : C F nX) := by
  sorry

/-- **Corollary 5.2.2** (`cor-Spin-V-Y-invariance`), first equality: for `γ ∈ H*(X × Y)`,
`δ ∈ H*(Y × Z)` and `h ∈ Spin(V_Y)`, `[(m_h ⊗ 1)(δ)]_* ∘ [(1 ⊗ m†_h)(γ)]_* = δ_* ∘ γ_*`. -/
theorem corollary5_2_2_1 (h : Spin F nY) (γ : S F nX ⊗[F] S F nY) (δ : S F nY ⊗[F] S F nZ) :
    corr (integral F nY) (TensorProduct.map (m F nY (h : C F nY)) LinearMap.id δ) ∘ₗ
        corr (integral F nX) (TensorProduct.map LinearMap.id (mDagger F nY (h : C F nY)) γ) =
      corr (integral F nY) δ ∘ₗ corr (integral F nX) γ := by
  sorry

/-- **Corollary 5.2.2** (`cor-Spin-V-Y-invariance`), second equality: for `γ ∈ H*(X × Y)`,
`δ ∈ H*(Y × Z)` and `h ∈ Spin(V_Y)`, `[(m†_h ⊗ 1)(δ)]_* ∘ [(1 ⊗ m_h)(γ)]_* = δ_* ∘ γ_*`. -/
theorem corollary5_2_2_2 (h : Spin F nY) (γ : S F nX ⊗[F] S F nY) (δ : S F nY ⊗[F] S F nZ) :
    corr (integral F nY) (TensorProduct.map (mDagger F nY (h : C F nY)) LinearMap.id δ) ∘ₗ
        corr (integral F nX) (TensorProduct.map LinearMap.id (m F nY (h : C F nY)) γ) =
      corr (integral F nY) δ ∘ₗ corr (integral F nX) γ := by
  sorry

end Correspondences

end WeilClasses
