module

public import WeilClasses.PureSpinor.Lemma2_2_6
import WeilClasses.External.Chevalley.Sec3
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.RepresentationTheory.Spin.Structure
import TauCeti.RepresentationTheory.Spin.Polarization.Hyperbolic

/-!
# Chevalley, *The algebraic theory of spinors*, results used in §2.2 of the paper

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954, Chapter III.
The quadratic space is `V_F = H¹(X̂, F) ⊕ H¹(X, F)` (maximal Witt index), its spin representation is
`S_F = ⋀• H¹(X, F)` with `m_{(θ,w)} = L_w + D_θ`, and Chevalley's bilinear form on spinors is the
Mukai pairing `(·,·)_S`. All statements are over a field `F` of characteristic zero; the paper uses
them over `ℂ` and over `K = ℚ(√-d)`.

Results stated, with the places where the paper uses them:

* [III.1.4] every maximal isotropic subspace is `ker m_w` for an even or an odd pure spinor `w`, and
  `w` is unique up to a scalar (`chevalley_III_1_4_exists`, `chevalley_III_1_4_unique`): §2.2, first
  paragraph (definition of pure spinors, the spinor variety);
* [III.1.5] the two families (`chevalley_III_1_5_families`): §2.2, first paragraph ("`IGr(2n, V_ℂ)`
  has two connected components"; only the algebraic content, the disjointness of the two families,
  is stated: the isotropic Grassmannian and its topology are not modeled);
* [III.1.12] (`chevalley_III_1_12`): §2.2 after Lemma 2.2.1 (the line through `ℓ₁, ℓ₂` meets the
  spinor variety only in `ℓ₁, ℓ₂`, for `n > 1`) and Remark 2.2.3 ("`w` is not a pure spinor");
* [III.2.4] (`chevalley_III_2_4`, `chevalley_III_2_4_self`): proof of Lemma 2.2.1;
* [III.3.1] (`chevalley_III_3_1_bijective`, `chevalley_III_3_1_equivariant`): proof of Lemma 2.2.6
  (`φ ⊗ ℚ` is an isomorphism of `Spin(V_ℚ)`-representations);
* [III.3.2] (`chevalley_III_3_2`): proof of Lemma 2.2.6 (`φ(ℓ̃ᵢ ⊗ ℓ̃ᵢ) = ⋀^{2n} W_{i,ℂ}`) and the
  relation `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` of §2.2;
* [§3.3, Lemma 1] (`chevalley_sec3_3_lemma1`): transitivity of `Spin(V_F)` on ordered pairs of
  complementary maximal isotropic subspaces (used in §6.4; natural tool for the statements of §2.2).

## Proofs

All statements are proved, by arguments in the model, from the theory of pure spinors developed in
`WeilClasses.External.Chevalley.Sec3` (helpers prefixed `sa_`):

* [III.1.4], [III.1.5]: the normal form `W = σ_y(H* × 0)` (`sa_normal_form`) shows that the spinors
  killed by a maximal isotropic `W` form a line `F·(y·1)` spanned by a homogeneous spinor with
  `ker = W` (`sa_exists_pure`, `sa_unique`); an even and an odd spinor are never proportional.
* [III.2.4]: if `v ∈ ker m_{u₁} ∩ ker m_{u₂}` is nonzero and `(v, w)_V = 1`, then
  `(u₁, u₂)_S = ((m_v m_w + m_w m_v) u₁, u₂)_S = 0` by [III.2.2]. Conversely, for complementary
  kernels some `g ∈ Spin(V)` maps `(H* × 0, 0 × H) = (ker m_1, ker m_{[pt]})` to the pair
  (`sa_pair`), so `u₁ = c₁ g·1`, `u₂ = c₂ g·[pt]` and `(u₁, u₂)_S = c₁ c₂ (1, [pt])_S = c₁ c₂ ≠ 0`.
* [III.1.12]: with `g` as above, `a u₁ + b u₂ = g·(a c₁ + b c₂ [pt])`, and for `a, b ≠ 0`, `n > 1`,
  `m_{(θ, w)}(α + β [pt]) = α w + β D_θ[pt]` vanishes only for `(θ, w) = 0` (the number operator
  `Σ eᵢ ∧ D_{fᵢ}` separates the degrees `1` and `2n - 1`), so the kernel is `0`, not of dimension
  `2n`.
* [III.3.1]: `y · s[pt_X̂] = (m_y s)[pt_X̂]` gives the equivariance, and shows that the image of `φ` is
  a two-sided ideal; it contains `φ(1 ⊗ 1) = [pt_X̂] ≠ 0` and `C(V)` is simple (Tau Ceti's structure
  theorem for the hyperbolic polarization), so `φ` is onto, hence bijective
  (`dim S ⊗ S = 2^{4n} = dim C(V)`).
* [III.3.2]: `φ(u ⊗ u) = c² g [pt_X̂] g*` is a nonzero product of a basis of `W = ker m_u`, and every
  product of `2n` vectors of `W` is a multiple of it.
* [§3.3, Lemma 1]: `g₂ g₁⁻¹`, with `gᵢ` given by `sa_pair` for both pairs.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct


/-! ### Helpers (prefix `sa_`)

The pure-spinor theory used below (normal form of maximal isotropic subspaces, pairs, the left
ideal `C(V)·[pt_X̂]`, top products) is in `WeilClasses.External.Chevalley.Sec3`. -/

section Helpers

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
private theorem sa_finrank_V : Module.finrank F (V F n) = 2 * n + 2 * n := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq, sa_finrank_H1]

/-- A pure spinor is nonzero when `n > 0`. -/
private theorem sa_ne_zero_of_isMax (hn : 0 < n) {u : S F n} (hu : IsMaxIsotropic F n (ann F n u)) :
    u ≠ 0 := by
  rintro rfl
  have h := hu.2
  have htop : ann F n 0 = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [sa_mem_ann, map_zero]
  rw [htop, finrank_top, sa_finrank_V] at h
  omega

/-- The spinors killed by `ρ(g)(H* × 0)` and by `ρ(g)(0 × H)`. -/
private theorem sa_mem_span_of_pair (g : Spin F n) {u : S F n}
    (hu : (sa_W0 F n).map (rho F n g : V F n →ₗ[F] V F n) ≤ ann F n u) :
    u ∈ Submodule.span F {m F n (g : C F n) 1} := by
  have h := (sa_mem_kill_iff _ u).mpr hu
  rwa [show (rho F n g : V F n →ₗ[F] V F n) = ((sa_Inter.ofSpin g).σ : V F n →ₗ[F] V F n)
    from rfl, sa_kill_map_W0] at h

private theorem sa_mem_span_of_pair' (g : Spin F n) {u : S F n}
    (hu : (sa_W0' F n).map (rho F n g : V F n →ₗ[F] V F n) ≤ ann F n u) :
    u ∈ Submodule.span F {m F n (g : C F n) (pt F n)} := by
  have h := (sa_mem_kill_iff _ u).mpr hu
  rwa [show (rho F n g : V F n →ₗ[F] V F n) = ((sa_Inter.ofSpin g).σ : V F n →ₗ[F] V F n)
    from rfl, sa_kill_map_W0'] at h

/-- The number operator `N = Σᵢ eᵢ ∧ D_{fᵢ}` on `S` (it multiplies `⋀ᵏ H` by `k`). -/
private noncomputable def sa_num : S F n →ₗ[F] S F n :=
  ∑ i, LinearMap.mulLeft F (ExteriorAlgebra.ι F (e F n i)) ∘ₗ D F n (f F n i)

omit [CharZero F] in
private theorem sa_num_apply (s : S F n) :
    sa_num s = ∑ i, ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s := by
  simp [sa_num]

omit [CharZero F] in
private theorem sa_num_ι (w : H1 F n) : sa_num (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F w := by
  rw [sa_num_apply]
  have h : ∀ i, ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) (ExteriorAlgebra.ι F w) =
      ExteriorAlgebra.ι F (f F n i w • e F n i) := by
    intro i
    rw [show D F n (f F n i) (ExteriorAlgebra.ι F w) = algebraMap F (S F n) (f F n i w) from
      contractLeft_ι (Q := (0 : QuadraticForm F (H1 F n))) _ _, ← Algebra.commutes,
      ← Algebra.smul_def, ← map_smul]
  simp only [h]
  rw [← map_sum, sa_sum_smul_e]

omit [CharZero F] in
private theorem sa_num_D (θ : Module.Dual F (H1 F n)) (s : S F n) :
    sa_num (D F n θ s) = D F n θ (sa_num s) - D F n θ s := by
  rw [sa_num_apply, sa_num_apply, map_sum]
  have h : ∀ i, D F n θ (ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s) =
      θ (e F n i) • D F n (f F n i) s +
        ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) (D F n θ s) := by
    intro i
    rw [show D F n θ (ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s) =
        θ (e F n i) • D F n (f F n i) s -
          ExteriorAlgebra.ι F (e F n i) * D F n θ (D F n (f F n i) s) from
        contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) _ _ _]
    rw [show D F n θ (D F n (f F n i) s) = -D F n (f F n i) (D F n θ s) from
      contractLeft_comm (Q := (0 : QuadraticForm F (H1 F n))) θ (f F n i) s, mul_neg,
      sub_neg_eq_add]
  simp only [h, Finset.sum_add_distrib]
  have h2 : ∑ i, θ (e F n i) • D F n (f F n i) s = D F n θ s := by
    conv_rhs => rw [← sa_sum_coord_smul θ]
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply]
  rw [h2]
  abel

omit [CharZero F] in
private theorem sa_num_pt : sa_num (pt F n) = ((2 * n : ℕ) : F) • pt F n := by
  apply (basisS F n).repr.injective
  ext K
  rw [sa_num_apply, map_sum, Finsupp.finsetSum_apply]
  simp only [sa_repr_proj]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, map_smul, Finsupp.smul_apply, pt,
    Module.Basis.repr_self, Finsupp.single_apply, nsmul_eq_mul, smul_eq_mul]
  split_ifs with hK
  · subst hK
    simp
  · simp

/-- `ker m_{α + β [pt]} = 0` for `α, β ≠ 0` and `n > 1`: the components of degree `1` and `2n - 1`
of `m_{(θ, w)}(α + β [pt]) = α w + β D_θ [pt]` cannot cancel. -/
private theorem sa_ann_one_add_pt (hn : 1 < n) {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    ann F n (α • 1 + β • pt F n) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨θ, w⟩ hv
  rw [sa_mem_ann, map_add, map_smul, map_smul, sa_m_ι_one, sa_m_ι_apply,
    sa_ι_mul_pt, zero_add] at hv
  simp only at hv
  have h1 := congrArg sa_num hv
  rw [map_add, map_smul, map_smul, sa_num_ι, sa_num_D, sa_num_pt, map_smul, map_zero] at h1
  set X := D F n θ (pt F n)
  set Y := ExteriorAlgebra.ι F w
  have key : (β * (((2 * n : ℕ) : F) - 2)) • X =
      (α • Y + β • (((2 * n : ℕ) : F) • X - X)) - (α • Y + β • X) - (α • Y + β • X) +
        (α • Y + β • X) := by
    module
  rw [h1, hv, sub_zero, sub_zero, add_zero] at key
  have h2 : ((2 * n : ℕ) : F) - 2 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (show 2 * n ≠ 2 by omega)
  rcases smul_eq_zero.mp key with h | hX
  · exact absurd h (mul_ne_zero hβ h2)
  · have hθ : θ = 0 := (sa_D_pt_eq_zero_iff θ).mp hX
    rw [hX, smul_zero, add_zero, smul_eq_zero] at hv
    rcases hv with h | hw
    · exact absurd h hα
    · rw [← map_zero (ExteriorAlgebra.ι F), ExteriorAlgebra.ι_inj] at hw
      rw [hθ, hw, Submodule.mem_bot]
      rfl

omit [CharZero F] in
/-- Nondegeneracy of `(·,·)_V`: for `v ≠ 0` some `w` has `(v, w)_V = 1`. -/
private theorem sa_exists_polar_eq_one {v : V F n} (hv : v ≠ 0) :
    ∃ w : V F n, QuadraticMap.polar (Q F n) v w = 1 := by
  obtain ⟨θ, x⟩ := v
  by_cases hx : x = 0
  · subst hx
    have hθ : θ ≠ 0 := fun h => hv (by rw [h]; rfl)
    obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hθ
    rw [LinearMap.zero_apply] at hy
    refine ⟨(0, (θ y)⁻¹ • y), ?_⟩
    rw [sa_polar_apply]
    simp [hy]
  · obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hx
    refine ⟨(φ, 0), ?_⟩
    rw [sa_polar_apply]
    simp [hφ]

/-- **[III.2.4], first half**: if `ker m_{u₁} ∩ ker m_{u₂} ≠ 0` then `(u₁, u₂)_S = 0`, by
`u₁ = (m_v m_w + m_w m_v) u₁` for `v` in the intersection and `(v, w)_V = 1`, and III.2.2. -/
private theorem sa_mukai_eq_zero_of_inf {u₁ u₂ : S F n} (h : ann F n u₁ ⊓ ann F n u₂ ≠ ⊥) :
    mukai F n u₁ u₂ = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨w, hw⟩ := sa_exists_polar_eq_one hv0
  have h1 : m F n (ι (Q F n) v) u₁ = 0 := hv.1
  have h2 : m F n (ι (Q F n) v) u₂ = 0 := hv.2
  have hsum : m F n (ι (Q F n) v) (m F n (ι (Q F n) w) u₁) +
      m F n (ι (Q F n) w) (m F n (ι (Q F n) v) u₁) = u₁ := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.add_apply,
      ← map_mul (m F n), ← map_mul (m F n), ← map_add (m F n), ι_mul_ι_add_swap, hw, map_one,
      map_one, Module.End.one_apply]
  rw [← hsum, map_add, LinearMap.add_apply, sa_mukai_m_ι, h2, h1, map_zero, map_zero, map_zero,
    LinearMap.zero_apply, add_zero]

omit [CharZero F] in
private theorem sa_mukai_one_pt : mukai F n 1 (pt F n) = 1 := by
  show integral F n (tau F n 1 * pt F n) = 1
  rw [tau, reverse.map_one, one_mul, integral, pt, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

omit [CharZero F] in
private theorem sa_reverse_mul_self (g : Spin F n) : reverse (g : C F n) * (g : C F n) = 1 := by
  have h : reverse (g : C F n) = star (g : C F n) := by
    rw [star_def, involute_eq_of_mem_even (sa_spin_mem_evenOdd g)]
  rw [h, spinGroup.star_mul_self_of_mem g.2]

end Helpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, III.1.4]** (existence), as used in §2.2: every maximal isotropic subspace `W` of
`V_F` is `ker m_w` for a nonzero even or odd pure spinor `w`. -/
theorem chevalley_III_1_4_exists (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) :
    ∃ w : S F n, w ≠ 0 ∧ (IsEvenPureSpinor F n w ∨ IsOddPureSpinor F n w) ∧ ann F n w = W := by
  obtain ⟨w, hw0, hpar, hann, -⟩ := sa_exists_pure W hW
  refine ⟨w, hw0, ?_, hann⟩
  rcases hpar with h | h
  · exact Or.inl ⟨h, hann ▸ hW⟩
  · exact Or.inr ⟨h, hann ▸ hW⟩

/-- **[Chevalley, III.1.4]** (uniqueness), as used in §2.2: a nonzero spinor `w` with `ker m_w`
maximal isotropic is determined up to a scalar by `ker m_w`; so the map from `IGr₊(2n, V)` to
`ℙ(S⁺)`, `W ↦ [w]`, is well defined and injective. -/
theorem chevalley_III_1_4_unique (w w' : S F n) (hw : w ≠ 0)
    (hmax : IsMaxIsotropic F n (ann F n w)) (h : ann F n w' = ann F n w) :
    w' ∈ Submodule.span F {w} := by
  exact sa_unique w w' hw hmax h

/-- **[Chevalley, III.1.5]** (the two families), as used in §2.2: no maximal isotropic subspace is
the annihilator of both a nonzero even and a nonzero odd pure spinor, so the maximal isotropic
subspaces split into the two families `IGr₊` (even pure spinors) and `IGr₋` (odd pure spinors). -/
theorem chevalley_III_1_5_families (w w' : S F n) (hw : IsEvenPureSpinor F n w)
    (hw' : IsOddPureSpinor F n w') (hw0 : w ≠ 0) (hw0' : w' ≠ 0) :
    ann F n w ≠ ann F n w' := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sa_unique w w' hw0 hw.2 h.symm)
  have hmem : w' ∈ Splus F n ⊓ Sminus F n := ⟨hc ▸ Submodule.smul_mem _ c hw.1, hw'.1⟩
  rw [sa_Splus_inf_Sminus, Submodule.mem_bot] at hmem
  exact hw0' hmem

/-- **[Chevalley, III.1.12]**, as used in §2.2 (after Lemma 2.2.1, and in Remark 2.2.3): if `u₁, u₂`
are even pure spinors with `ker m_{u₁} ∩ ker m_{u₂} = 0` and `n > 1`, then a combination
`a u₁ + b u₂` is a pure spinor only if `a = 0` or `b = 0`. -/
theorem chevalley_III_1_12 (hn : 1 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F)
    (hab : IsEvenPureSpinor F n (a • u₁ + b • u₂)) :
    a = 0 ∨ b = 0 := by
  by_contra hcon
  obtain ⟨ha, hb⟩ := not_or.mp hcon
  have hn0 : 0 < n := by omega
  have hu₁0 := sa_ne_zero_of_isMax hn0 h₁.2
  have hu₂0 := sa_ne_zero_of_isMax hn0 h₂.2
  obtain ⟨g, hg1, hg2⟩ := sa_pair _ _ h₁.2 h₂.2 hW u₁ h₁.1 hu₁0 le_rfl
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (sa_mem_span_of_pair g hg1.le)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (sa_mem_span_of_pair' g hg2.le)
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    exact hu₁0 hc₁.symm
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₂
    exact hu₂0 hc₂.symm
  have heq : a • u₁ + b • u₂ = m F n (g : C F n) ((a * c₁) • 1 + (b * c₂) • pt F n) := by
    rw [← hc₁, ← hc₂, map_add, map_smul, map_smul, smul_smul, smul_smul]
  have hann : ann F n (a • u₁ + b • u₂) = ⊥ := by
    rw [heq, show m F n (g : C F n) = m F n (sa_Inter.ofSpin g).y from rfl, sa_ann_m,
      sa_ann_one_add_pt hn (mul_ne_zero ha hc₁0) (mul_ne_zero hb hc₂0), Submodule.map_bot]
  have h2 := hab.2.2
  rw [hann, finrank_bot] at h2
  omega

/-- **[Chevalley, III.2.4]**, as used in the proof of Lemma 2.2.1: for even pure spinors `λ₁, λ₂`
(with `n ≥ 1`), `(λ₁, λ₂)_S = 0` if and only if `ker m_{λ₁} ∩ ker m_{λ₂} ≠ 0`. -/
theorem chevalley_III_2_4 (hn : 0 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) :
    mukai F n u₁ u₂ = 0 ↔ ann F n u₁ ⊓ ann F n u₂ ≠ ⊥ := by
  refine ⟨fun h0 hbot => ?_, sa_mukai_eq_zero_of_inf⟩
  have hu₁0 := sa_ne_zero_of_isMax hn h₁.2
  have hu₂0 := sa_ne_zero_of_isMax hn h₂.2
  obtain ⟨g, hg1, hg2⟩ := sa_pair _ _ h₁.2 h₂.2 hbot u₁ h₁.1 hu₁0 le_rfl
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (sa_mem_span_of_pair g hg1.le)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (sa_mem_span_of_pair' g hg2.le)
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    exact hu₁0 hc₁.symm
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₂
    exact hu₂0 hc₂.symm
  rw [← hc₁, ← hc₂] at h0
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h0
  rw [sa_mukai_m_reverse, ← Module.End.mul_apply, ← map_mul (m F n), sa_reverse_mul_self,
    map_one (m F n), Module.End.one_apply, sa_mukai_one_pt] at h0
  simp [hc₁0, hc₂0] at h0

/-- **[Chevalley, III.2.4]**, the special case `λ₁ = λ₂` used in the proof of Lemma 2.2.1: a pure
spinor is isotropic, `(λ, λ)_S = 0` (for `n ≥ 1`). -/
theorem chevalley_III_2_4_self (hn : 0 < n) (u : S F n) (hu : IsEvenPureSpinor F n u) :
    mukai F n u u = 0 := by
  refine sa_mukai_eq_zero_of_inf ?_
  rw [inf_idem]
  intro hbot
  have h := hu.2.2
  rw [hbot, finrank_bot] at h
  omega

/-- **[Chevalley, III.3.1]**, as used in the proof of Lemma 2.2.6: Chevalley's map
`φ : S_F ⊗ S_F → C(V_F)`, `φ(u ⊗ v) = u [pt_X̂] τ(v)` (2.2.5), is bijective. -/
theorem chevalley_III_3_1_bijective : Function.Bijective (varphi F n) := by
  have hleft : ∀ (x : C F n) (z : S F n ⊗[F] S F n),
      x * varphi F n z = varphi F n (TensorProduct.map (m F n x) LinearMap.id z) := by
    intro x z
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, sa_varphi_tmul, sa_varphi_tmul,
        ← mul_assoc, ← mul_assoc, sa_mul_iotaX_mul_ptHatC]
    | add z₁ z₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, map_add, map_add]
  have hright : ∀ (x : C F n) (z : S F n ⊗[F] S F n),
      varphi F n z * x = varphi F n (TensorProduct.map LinearMap.id (m F n (reverse x)) z) := by
    intro x z
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, sa_varphi_tmul, sa_varphi_tmul,
        mul_assoc (iotaX F n s), mul_assoc (iotaX F n s), sa_ptHatC_mul_iotaX_mul]
      simp only [mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, map_add, map_add]
  let I : TwoSidedIdeal (C F n) := TwoSidedIdeal.mk' (Set.range (varphi F n)) ⟨0, map_zero _⟩
    (by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩)
    (by rintro _ ⟨a, rfl⟩; exact ⟨-a, map_neg _ _⟩)
    (by rintro x _ ⟨a, rfl⟩; exact ⟨_, (hleft x a).symm⟩)
    (by rintro _ y ⟨a, rfl⟩; exact ⟨_, (hright y a).symm⟩)
  have hmem : ∀ x, x ∈ I ↔ x ∈ Set.range (varphi F n) :=
    fun x => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x
  have hsimple : IsSimpleRing (C F n) :=
    TauCeti.SpinPolarizationData.isSimpleRing_cliffordAlgebra
      (TauCeti.SpinPolarizationData.hyperbolic (Module.eval_apply_injective F (V := H1 F n)))
      (by rw [sa_finrank_V]; exact ⟨2 * n, rfl⟩)
  have hI : I = ⊤ := by
    rcases hsimple.simple.eq_bot_or_eq_top I with h | h
    · exfalso
      have hP : ptHatC F n ∈ I := by
        rw [hmem]
        exact ⟨1 ⊗ₜ 1, sa_varphi_one⟩
      rw [h, TwoSidedIdeal.mem_bot] at hP
      exact sa_ptHatC_ne_zero hP
    · exact h
  have hsurj : Function.Surjective (varphi F n) := by
    intro x
    have hx : x ∈ I := by
      rw [hI]
      exact TwoSidedIdeal.mem_top _
    rwa [hmem] at hx
  have hdim : Module.finrank F (S F n ⊗[F] S F n) = Module.finrank F (C F n) := by
    have hS : Module.finrank F (S F n) = 2 ^ (2 * n) := by
      rw [CliffordAlgebra.finrank_eq_two_pow, sa_finrank_H1]
    have hC : Module.finrank F (C F n) = 2 ^ (2 * n + 2 * n) := by
      rw [CliffordAlgebra.finrank_eq_two_pow, sa_finrank_V]
    rw [Module.finrank_tensorProduct, hS, hC, ← pow_add]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- **[Chevalley, III.3.1]**, as used in the proof of Lemma 2.2.6: `φ` is an isomorphism of
`Spin(V_F)`-representations, `Spin(V_F)` acting on `S ⊗ S` by `m_g ⊗ m_g` and on `C(V_F)` by
conjugation `x ↦ g x g⁻¹ = g x g*`. -/
theorem chevalley_III_3_1_equivariant (g : Spin F n) (s t : S F n) :
    varphi F n (m F n (g : C F n) s ⊗ₜ m F n (g : C F n) t) =
      (g : C F n) * varphi F n (s ⊗ₜ t) * star (g : C F n) := by
  exact sa_varphi_equivariant g s t

/-- **[Chevalley, III.3.2]**, as used in the proof of Lemma 2.2.6 (and for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` in
§2.2): for a nonzero even pure spinor `u` with `W = ker m_u`, `φ(u ⊗ u)` is nonzero and spans the
line `⋀^{2n} W ⊆ C(V_F)`. -/
theorem chevalley_III_3_2 (u : S F n) (hu : IsEvenPureSpinor F n u) (hu0 : u ≠ 0) :
    varphi F n (u ⊗ₜ u) ≠ 0 ∧
      Submodule.span F {varphi F n (u ⊗ₜ u)} = cliffordTopPiece F n (ann F n u) := by
  obtain ⟨c, z, hφ, hφ0⟩ := sa_varphi_self u hu hu0
  refine ⟨hφ0, ?_⟩
  have hW := hu.2
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (2 * n)) F (ann F n u),
      b = Module.finBasisOfFinrankEq F (ann F n u) hW.2 := ⟨_, rfl⟩
  have key : ∀ y : Fin (2 * n) → ann F n u,
      sa_topMap (ann F n u) hW.1 (2 * n) y = b.det y • sa_topMap (ann F n u) hW.1 (2 * n) b := by
    intro y
    rw [hb]
    exact sa_topMap_eq_det_smul (ann F n u) hW.1 hW.2 y
  have hgen : ∀ w : Fin (2 * n) → V F n, (∀ i, w i ∈ ann F n u) →
      (List.ofFn fun i => ι (Q F n) (w i)).prod ∈
        Submodule.span F {sa_topMap (ann F n u) hW.1 (2 * n) b} := by
    intro w hw
    have hx : (List.ofFn fun i => ι (Q F n) (w i)).prod =
        sa_topMap (ann F n u) hW.1 (2 * n) (fun i => ⟨w i, hw i⟩) := by
      rw [sa_topMap_apply, List.map_ofFn]
      rfl
    have h2 := key (fun i => ⟨w i, hw i⟩)
    rw [hx, h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have htop : cliffordTopPiece F n (ann F n u) =
      Submodule.span F {sa_topMap (ann F n u) hW.1 (2 * n) b} := by
    apply le_antisymm
    · rw [cliffordTopPiece, Submodule.span_le]
      rintro x ⟨w, hw, rfl⟩
      exact hgen w hw
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      have hb' : sa_topMap (ann F n u) hW.1 (2 * n) b =
          (List.ofFn fun i => ι (Q F n) ((b i : ann F n u) : V F n)).prod := by
        rw [sa_topMap_apply, List.map_ofFn]
        rfl
      rw [hb']
      exact Submodule.subset_span ⟨fun i => (b i : V F n), fun i => (b i).2, rfl⟩
  have hk : c * b.det z ≠ 0 := by
    intro h0
    apply hφ0
    rw [hφ, key z, smul_smul, h0, zero_smul]
  rw [htop, hφ, key z, smul_smul]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hk) _

/-- **[Chevalley, §3.3, Lemma 1]**, in the form used in the paper (§6.4: "`Spin(V_K)` acts
transitively on the set of ordered pairs of complementary maximally isotropic subspaces of `V_K`"),
restricted to pairs from the even family: given even pure spinors `u₁, u₂, u₁', u₂'` with
`ker m_{u₁} ∩ ker m_{u₂} = 0 = ker m_{u₁'} ∩ ker m_{u₂'}`, some `g ∈ Spin(V_F)` maps the pair
`(ker m_{u₁}, ker m_{u₂})` to `(ker m_{u₁'}, ker m_{u₂'})`. (`Spin(V_F)` preserves the two families,
so transitivity on all complementary pairs, as literally phrased in §6.4, fails; the pairs used
there come from even pure spinors.) -/
theorem chevalley_sec3_3_lemma1 (u₁ u₂ u₁' u₂' : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (h₁' : IsEvenPureSpinor F n u₁')
    (h₂' : IsEvenPureSpinor F n u₂') (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥)
    (hW' : ann F n u₁' ⊓ ann F n u₂' = ⊥) :
    ∃ g : Spin F n, (ann F n u₁).map (rho F n g).toLinearMap = ann F n u₁' ∧
      (ann F n u₂).map (rho F n g).toLinearMap = ann F n u₂' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `V_F = 0`: all subspaces coincide.
    have hH : ∀ w : H1 F 0, w = 0 := fun w => funext fun i => absurd i.2 (by simp)
    have hV : ∀ v : V F 0, v = 0 := by
      rintro ⟨θ, w⟩
      refine Prod.ext ?_ (hH w)
      exact LinearMap.ext fun x => by rw [hH x, map_zero]; rfl
    have hsub : ∀ A B : Submodule F (V F 0), A = B := by
      intro A B
      ext v
      rw [hV v]
      exact ⟨fun _ => B.zero_mem, fun _ => A.zero_mem⟩
    exact ⟨1, hsub _ _, hsub _ _⟩
  · have hu₁0 := sa_ne_zero_of_isMax hn h₁.2
    have hu₁'0 := sa_ne_zero_of_isMax hn h₁'.2
    obtain ⟨g₁, hg₁, hg₁'⟩ := sa_pair _ _ h₁.2 h₂.2 hW u₁ h₁.1 hu₁0 le_rfl
    obtain ⟨g₂, hg₂, hg₂'⟩ := sa_pair _ _ h₁'.2 h₂'.2 hW' u₁' h₁'.1 hu₁'0 le_rfl
    have hcomp : (rho F n (g₂ * g₁⁻¹) : V F n →ₗ[F] V F n).comp (rho F n g₁ : V F n →ₗ[F] V F n) =
        (rho F n g₂ : V F n →ₗ[F] V F n) := by
      refine LinearMap.ext fun x => ?_
      have h1 : rho F n g₁⁻¹ (rho F n g₁ x) = x := by
        have := congrArg (fun e : V F n ≃ₗ[F] V F n => e x) (spinVectorAction_mul (Q F n) g₁⁻¹ g₁)
        simp only [inv_mul_cancel, spinVectorAction_one, LinearEquiv.refl_apply] at this
        exact this.symm
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show rho F n (g₂ * g₁⁻¹) = rho F n g₂ * rho F n g₁⁻¹ from spinVectorAction_mul _ _ _,
        LinearEquiv.mul_apply, h1]
    refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
    · rw [← hg₁, ← hg₂, ← Submodule.map_comp, hcomp]
    · rw [← hg₁', ← hg₂', ← Submodule.map_comp, hcomp]

end WeilClasses
