module

public import WeilClasses.PureSpinor.Defs
public import WeilClasses.PureSpinor.Sec2_1

/-!
# Pure spinors, rational `K`-secants, and Lemma 2.2.1 (paper §2.2, first part)

The definitions of pure spinors, of rational `K`-secants (`WeilClasses.KSecant`), of `W₁`, `W₂`,
`P_K` and `P` are in `WeilClasses.PureSpinor.Defs`. This file states the claims of §2.2 up to and
including the paragraph following Lemma 2.2.1:

* `ann_m_spin`: `ker m_{g s} = ρ(g)(ker m_s)`, so `W ↦ [s]` is a `Spin(V)`-equivariant embedding
  `IGr₊(2n, V_ℂ) → ℙ(S⁺_ℂ)` (together with [Chevalley, III.1.4–1.5], stated in
  `WeilClasses.External.Chevalley.Sec2_2`); `finrank_Splus`: `ℙ(S⁺_ℂ) ≅ ℙ^{2^{2n-1}-1}`. The
  isotropic Grassmannian `IGr(2n, V_ℂ)` itself (its dimension `2n² - n` and its two connected
  components) is not modeled;
* basic facts on a `K`-secant `P`: `u₁ ≠ 0`, `u₂` is pure, `W₂ = σ(W₁)` ("`W₂` is the complex
  conjugate of `W₁`"), `P_K` is defined over `ℚ` and `P ⊆ S⁺_ℚ` is a plane;
* `mukai_swap_of_mem_Splus`: `(t, s)_S = (-1)^n (s, t)_S` on `S⁺` (§1.2 says the Mukai pairing is
  symmetric for even `n` and antisymmetric for odd `n`);
* **Lemma 2.2.1**, corrected as decided with the project owner (`lemma2_2_1`, `lemma2_2_1_even`,
  `lemma2_2_1_odd`), and its consequence `KSecant.isCompl_of_not_isIsotropic`
  (`V_K = W₁ ⊕ W₂` when `P` is non-isotropic);
* `KSecant.isEvenPureSpinor_iff_of_mem_span`: when `W₁ ∩ W₂ = 0` and `n > 1`, the line `ℙ(P_ℂ)`
  meets the spinor variety exactly in `{ℓ₁, ℓ₂}` [Chevalley, III.1.12].

## Representation choices

`K = ℚ(√-d) = Kd d ⊆ ℂ`. A `K`-point of `S` or `V` is a vector of `S (Kd d) n` or `V (Kd d) n`
(coordinates in `K`), a complex point one of `S ℂ n`, `V ℂ n`; the change of coefficients is
`bcS`/`bcV` (coordinatewise). The paper's `√-1` in the proof of Lemma 2.2.1 stands for `√-d`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section General

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **`Spin(V)`-equivariance of the pure spinor embedding** (§2.2): for `g ∈ Spin(V_F)` and a spinor
`s`, `ker m_{g s} = ρ(g)(ker m_s)`. Hence `W = ker m_s ↦ [s]` is a `Spin(V)`-equivariant map
`IGr₊(2n, V) → ℙ(S⁺)`; it is injective by [Chevalley, III.1.4]
(`WeilClasses.chevalley_III_1_4_unique`). -/
theorem ann_m_spin (g : Spin F n) (s : S F n) :
    ann F n (m F n (g : C F n) s) = (ann F n s).map (rho F n g).toLinearMap := by
  sorry

/-- `dim S⁺ = 2^{2n-1}`, so that `ℙ(S⁺_ℂ) ≅ ℙ^{2^{2n-1}-1}` (§2.2, first paragraph). (With the
truncated subtraction of `ℕ` the formula also holds for `n = 0`.) -/
theorem finrank_Splus : Module.finrank F (Splus F n) = 2 ^ (2 * n - 1) := by
  sorry

/-- A pure spinor is nonzero when `n ≥ 1` (`ker m_0 = V` has dimension `4n ≠ 2n`). -/
theorem IsEvenPureSpinor.ne_zero {F : Type*} [Field F] [CharZero F] {n : ℕ} (hn : 0 < n)
    {w : S F n} (hw : IsEvenPureSpinor F n w) : w ≠ 0 := by
  sorry

/-- **The Mukai pairing on `S⁺` is `(-1)^n`-symmetric**: `(t, s)_S = (-1)^n (s, t)_S` for
`s, t ∈ S⁺` (in fact for all `s, t ∈ S`). For odd `n` it is alternating on `S⁺`. This is the reason
for the correction of the second sentence of Lemma 2.2.1 (see `lemma2_2_1_odd`). -/
theorem mukai_swap_of_mem_Splus (s t : S F n) (hs : s ∈ Splus F n) (ht : t ∈ Splus F n) :
    mukai F n t s = (-1) ^ n * mukai F n s t := by
  sorry

end General

/-! ## Definite and nondegenerate restrictions of a rational bilinear form -/

section Forms

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- The restriction of a rational bilinear form `B` to a subspace `P` is *definite*:
`B(a, a) > 0` for all nonzero `a ∈ P`, or `B(a, a) < 0` for all nonzero `a ∈ P`. -/
def BilinDefiniteOn (B : LinearMap.BilinForm ℚ M) (P : Submodule ℚ M) : Prop :=
  (∀ a ∈ P, a ≠ 0 → 0 < B a a) ∨ (∀ a ∈ P, a ≠ 0 → B a a < 0)

/-- The restriction of a bilinear form `B` to a subspace `P` is *nondegenerate*: the only `a ∈ P`
with `B(a, b) = 0` for all `b ∈ P` is `a = 0`. -/
def BilinNondegOn (B : LinearMap.BilinForm ℚ M) (P : Submodule ℚ M) : Prop :=
  ∀ a ∈ P, (∀ b ∈ P, B a b = 0) → a = 0

end Forms

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-! ## Basic facts on a rational `K`-secant -/

/-- The pure spinor `u₁` spanning `ℓ̃₁` is nonzero. -/
theorem u₁_ne_zero : P.u₁ ≠ 0 := by
  sorry

/-- The conjugate `u₂ = σ(u₁)` is an even pure spinor (§2.2: `ℓ₁, ℓ₂` are conjugate points of the
spinor variety). -/
theorem isPure₂ : IsEvenPureSpinor (Kd d) n P.u₂ := by
  sorry

/-- "**`W₂` is the complex conjugate of `W₁`**" (§2.2): `σ(v) ∈ W₂ ↔ v ∈ W₁`. -/
theorem σV_mem_W₂_iff (v : V (Kd d) n) : σV n d v ∈ P.W₂ ↔ v ∈ P.W₁ := by
  sorry

/-- "**`P_K` is defined over `ℚ`**" (§2.2): `P_K` is spanned over `K` by the rational plane `P`. -/
theorem span_bcS_Pℚ :
    Submodule.span (Kd d) (bcS ℚ (Kd d) n '' (P.Pℚ : Set (S ℚ n))) = P.PK := by
  sorry

/-- The rational points `P` of `P_K` form a plane (§2.2). -/
theorem finrank_Pℚ : Module.finrank ℚ P.Pℚ = 2 := by
  sorry

/-- The rational plane `P` lies in `S⁺_ℚ` (§2.2). -/
theorem Pℚ_le_Splus : P.Pℚ ≤ Splus ℚ n := by
  sorry

/-- When `W₁ ∩ W₂ = 0`, `V_K = W₁ ⊕ W₂` (both have dimension `2n`, and `dim V_K = 4n`). -/
theorem isCompl_of_inf_eq_bot (hW : P.W₁ ⊓ P.W₂ = ⊥) : IsCompl P.W₁ P.W₂ := by
  sorry

/-! ## Lemma 2.2.1 -/

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), first sentence,
as printed (true for all `n`): `P` is isotropic with respect to the Mukai pairing (1.2.3) (the
pairing vanishes identically on `P`) if and only if `W₁ ∩ W₂ ≠ 0`. The hypothesis `0 < d` is the paper's "`K` purely imaginary" (it is implied
by the existence of `P`). -/
theorem _root_.WeilClasses.lemma2_2_1 (hd : 0 < d) : P.IsIsotropic ↔ P.W₁ ⊓ P.W₂ ≠ ⊥ := by
  sorry

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), second sentence,
for even `n` (as printed): the restriction of `(·,·)_S` to `P` is definite if and only if
`W₁ ∩ W₂ = 0`.

Correction of the paper: the second sentence is false for odd n because (·,·)_S is alternating on
S⁺ ((t,s) = (−1)ⁿ(s,t)); see REPORT.md. For odd `n` see `lemma2_2_1_odd`. -/
theorem _root_.WeilClasses.lemma2_2_1_even (hd : 0 < d) (hn : Even n) :
    BilinDefiniteOn (mukai ℚ n) P.Pℚ ↔ P.W₁ ⊓ P.W₂ = ⊥ := by
  sorry

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), second sentence,
corrected for odd `n` (decided with the project owner): `(·,·)_S` is alternating on `S⁺`, and its
restriction to `P` is nondegenerate if and only if `W₁ ∩ W₂ = 0`.

Correction of the paper: the second sentence is false for odd n because (·,·)_S is alternating on
S⁺ ((t,s) = (−1)ⁿ(s,t)); see REPORT.md. (The paper's proof writes `λ₁ = a + ib` and uses the
symmetry of the pairing; for odd `n`, `(λ₁, λ₂) = -2√-d (a, b)_S` instead.) -/
theorem _root_.WeilClasses.lemma2_2_1_odd (hd : 0 < d) (hn : Odd n) :
    (∀ s ∈ Splus ℚ n, mukai ℚ n s s = 0) ∧
      (BilinNondegOn (mukai ℚ n) P.Pℚ ↔ P.W₁ ⊓ P.W₂ = ⊥) := by
  sorry

/-- If `P` is non-isotropic, then `V_K = W₁ ⊕ W₂` (§2.2, before Lemma 2.2.4: "The vanishing
`W₁ ∩ W₂ = (0)` holds, by Lemma 2.2.1"). -/
theorem isCompl_of_not_isIsotropic (hd : 0 < d) (hP : ¬ P.IsIsotropic) : IsCompl P.W₁ P.W₂ := by
  sorry

/-! ## The secant line meets the spinor variety in two points -/

/-- **The line `ℙ(P)` meets the spinor variety in `{ℓ₁, ℓ₂}`** (§2.2, after Lemma 2.2.1, by
[Chevalley, III.1.12]): if `W₁ ∩ W₂ = 0` and `n > 1`, then a vector `w` of the complex plane
`P_ℂ = ℂ u₁ + ℂ u₂` is an even pure spinor if and only if it is a nonzero multiple of `u₁` or of
`u₂`; that is, the set-theoretic intersection of `IGr₊(2n, V_ℂ)` (the spinor variety in
`ℙ(S⁺_ℂ)`) with the line through `ℓ₁` and `ℓ₂` is `{ℓ₁, ℓ₂}`. -/
theorem isEvenPureSpinor_iff_of_mem_span (hd : 0 < d) (hn : 1 < n) (hW : P.W₁ ⊓ P.W₂ = ⊥)
    (w : S ℂ n) (hw : w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁, bcS (Kd d) ℂ n P.u₂}) :
    IsEvenPureSpinor ℂ n w ↔
      w ≠ 0 ∧ (w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁} ∨
        w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₂}) := by
  sorry

end KSecant

end WeilClasses
