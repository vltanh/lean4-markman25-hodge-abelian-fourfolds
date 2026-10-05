module

public import WeilClasses.WeilType.Basic
public import WeilClasses.External.HasseMinkowski.Main

/-!
# Landherr's theorem (split case) for Hermitian forms over `K = ℚ(√-d)`

W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*, Abh.
Math. Sem. Univ. Hamburg 11 (1936), 245–248: Hermitian forms over a quadratic extension `K/k` of
number fields are classified by their rank, their discriminant in `k^×/Nm(K^×)` and their
signatures at the real places of `k` that do not split in `K`. This file proves the case that [van Geemen,
Th. 5.2(3)] uses, for `K = ℚ(√-d)`, `d > 0`: a Hermitian form of `K`-rank `2n` with signature
`(n, n)` and discriminant `(-1)ⁿ` is hyperbolic (`vg_HermSpace.landherr_split`), so any two such
forms are isometric (`vg_HermSpace.exists_isometry`).

## The rational model

`K` acts on a `ℚ`-vector space `V` through `f = η(√-d)` (`f² = -d`; `a + b√-d` acts by `a + b f`,
`vg_HermSpace.smulK`); no `K`-module structure is put on `V`. The Hermitian form is van Geemen's
`H(x, y) = E(x, f y) + √-d E(x, y)` (`vg_HermSpace.herm`) for an alternating form `E` with
`E(f x, f y) = d E(x, y)` (`vg_HermSpace`; for a polarized abelian variety of Weil type, `E` is the
Riemann form on `H₁` and `f` the transpose of `η(√-d)`, `PolarizedWeilType.herm`). `H` is
`K`-linear in the second and `K`-antilinear in the first variable, Hermitian, and
`H(x, x) = E(x, f x)` is rational.

The signature `(n, n)` enters through the trace form `(x, y) ↦ E(x, f y)`, the real part of `H`,
of signature `(2n, 2n)`: its positive and negative indices are at most `2n` (`PosBound`,
`NegBound`: a family orthogonal for the trace form, with values `E(tᵢ, f tᵢ)` of one sign, has at
most `2n` members). The discriminant is `det H(bᵢ, bⱼ) ∈ (-1)ⁿ Nm(K)` for one `K`-basis `b`
(`bᵢ, f bᵢ` a `ℚ`-basis), as in `PolarizedWeilType.DiscIs`.

## Proof

A hyperbolic system `u₁, v₁, …, u_m, v_m` (`H(uᵢ, uⱼ) = H(vᵢ, vⱼ) = 0`, `H(uᵢ, vⱼ) = δᵢⱼ`,
`vg_HermSpace.HypSys`) is extended by a hyperbolic pair of its orthogonal complement `U`, which is
`f`-stable, nondegenerate and of dimension at least `4(n - m)`; the pair is built from an isotropic
vector of `U` (`exists_hypPartner`). The isotropic vector comes:
* for `m + 2 ≤ n`, from Meyer's theorem (`HasseMinkowski.meyer`, vendored from
  jayyswan/hasse-minkowski): `dim U ≥ 8`, and the trace form is indefinite on `U`, since otherwise
  `U` together with the vectors `uᵢ ∓ vᵢ, f(uᵢ ∓ vᵢ)` would be a definite orthogonal family with
  more than `2n` members;
* for `m + 1 = n`, from the discriminant: `U` has `K`-rank `2`; for an `H`-orthogonal pair
  `w₁, w₂` of `U` with `a = H(w₁, w₁) ≠ 0`, `c = H(w₂, w₂) ≠ 0`, the family `uᵢ ± vᵢ, w₁, w₂` has
  Gram determinant `(-4)^m a c`, which is `Nm(z) (-1)ⁿ Nm(k)` by the change-of-basis formula
  (`det_herm_change`); so `a c = -Nm(λ)` and `(λ/a) w₁ + w₂` is isotropic.
-/

@[expose] public section

namespace WeilClasses

open Module

/-- A nondegenerate Hermitian space over `K = ℚ(√-d)` in rational terms: a `ℚ`-vector space `V`
with `f = η(√-d)` (`f² = -d`) and an alternating form `E` with `E(f x, f y) = d E(x, y)`,
nondegenerate. The `K`-valued Hermitian form is `H(x, y) = E(x, f y) + √-d E(x, y)`
(`vg_HermSpace.herm`). -/
structure vg_HermSpace (d : ℚ) (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The action of `√-d`. -/
  f : V →ₗ[ℚ] V
  /-- The alternating form (the imaginary part of `H`, up to `√d`). -/
  E : LinearMap.BilinForm ℚ V
  /-- `d > 0`: `K` is imaginary quadratic. -/
  d_pos : 0 < d
  /-- `f² = -d`. -/
  f_f : ∀ x, f (f x) = -(d • x)
  /-- `E` is alternating. -/
  E_swap : ∀ x y, E y x = -E x y
  /-- `E(f x, f y) = Nm(√-d) E(x, y)`. -/
  E_ff : ∀ x y, E (f x) (f y) = d * E x y
  /-- `E` is nondegenerate. -/
  nondeg : ∀ x, (∀ y, E x y = 0) → x = 0

theorem vg_coe_algebraMap {d : ℚ} (q : ℚ) : ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := by
  simp

/-- `k = a + b √-d` in `ℂ`, with `a = Kd.ratPart d k`, `b = Kd.sqrtNegCoeff d k`. -/
theorem vg_coe_Kd {d : ℚ} (hd : 0 < d) (k : Kd d) :
    (k : ℂ) = (Kd.ratPart d k : ℂ) + (Kd.sqrtNegCoeff d k : ℂ) * sqrtNeg d := by
  conv_lhs => rw [Kd.eq_ratPart_add_sqrtNegCoeff hd k]
  simp only [Subfield.coe_add, Subfield.coe_mul]
  rw [vg_coe_algebraMap, vg_coe_algebraMap]
  rfl

namespace vg_HermSpace

variable {d : ℚ} {V : Type*} [AddCommGroup V] [Module ℚ V] (W : vg_HermSpace d V)

/-! ### The identities of `E` and `f` -/

theorem E_self (x : V) : W.E x x = 0 := by
  have h := W.E_swap x x
  linarith

/-- `E(f x, y) = -E(x, f y)`. -/
theorem E_f_left (x y : V) : W.E (W.f x) y = -W.E x (W.f y) := by
  have h := W.E_ff (W.f x) y
  rw [W.f_f, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at h
  have h' : d * (W.E (W.f x) y + W.E x (W.f y)) = 0 := by linarith
  have := (mul_eq_zero.mp h').resolve_left W.d_pos.ne'
  linarith

/-- `E(x, f y) = E(y, f x)`: the trace form is symmetric. -/
theorem S_symm (x y : V) : W.E x (W.f y) = W.E y (W.f x) := by
  rw [W.E_swap (W.f x) y, W.E_f_left, neg_neg]

theorem E_f_f_right (x y : V) : W.E x (W.f (W.f y)) = -(d * W.E x y) := by
  rw [W.f_f, map_neg, map_smul, smul_eq_mul]

/-! ### The Hermitian form -/

/-- Van Geemen's Hermitian form `H(x, y) = E(x, f y) + √-d E(x, y)`, as a complex number. -/
noncomputable def herm (x y : V) : ℂ := (W.E x (W.f y) : ℂ) + sqrtNeg d * (W.E x y : ℂ)

theorem herm_add_left (x x' y : V) : W.herm (x + x') y = W.herm x y + W.herm x' y := by
  simp only [herm, map_add, LinearMap.add_apply, Rat.cast_add]; ring

theorem herm_add_right (x y y' : V) : W.herm x (y + y') = W.herm x y + W.herm x y' := by
  simp only [herm, map_add, Rat.cast_add]; ring

theorem herm_smul_left (a : ℚ) (x y : V) : W.herm (a • x) y = (a : ℂ) * W.herm x y := by
  simp only [herm, map_smul, LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul]; ring

theorem herm_smul_right (a : ℚ) (x y : V) : W.herm x (a • y) = (a : ℂ) * W.herm x y := by
  simp only [herm, map_smul, smul_eq_mul, Rat.cast_mul]; ring

/-- `H` as a `ℚ`-bilinear map. -/
noncomputable def hermL : V →ₗ[ℚ] V →ₗ[ℚ] ℂ :=
  LinearMap.mk₂ ℚ W.herm W.herm_add_left
    (fun a x y => by rw [W.herm_smul_left, Algebra.smul_def, eq_ratCast]) W.herm_add_right
    (fun a x y => by rw [W.herm_smul_right, Algebra.smul_def, eq_ratCast])

theorem hermL_apply (x y : V) : W.hermL x y = W.herm x y := rfl

theorem herm_neg_right (x y : V) : W.herm x (-y) = -W.herm x y := by
  rw [← W.hermL_apply, map_neg, W.hermL_apply]

theorem herm_f_right (x y : V) : W.herm x (W.f y) = sqrtNeg d * W.herm x y := by
  have hs : sqrtNeg d ^ 2 = -(d : ℂ) := sqrtNeg_sq W.d_pos.le
  simp only [herm, E_f_f_right]
  push_cast
  linear_combination (-(W.E x y : ℂ)) * hs

theorem herm_f_left (x y : V) : W.herm (W.f x) y = -sqrtNeg d * W.herm x y := by
  have hs : sqrtNeg d ^ 2 = -(d : ℂ) := sqrtNeg_sq W.d_pos.le
  simp only [herm, E_f_left, W.E_ff]
  push_cast
  linear_combination ((W.E x y : ℂ)) * hs

theorem herm_swap (x y : V) : W.herm y x = (starRingEnd ℂ) (W.herm x y) := by
  simp only [herm, map_add, map_mul, map_ratCast, fnd_conj_sqrtNeg]
  rw [W.S_symm y x, W.E_swap x y]
  push_cast
  ring

theorem herm_self (x : V) : W.herm x x = (W.E x (W.f x) : ℂ) := by
  simp [herm, W.E_self]

theorem herm_eq_zero_iff (x y : V) : W.herm x y = 0 ↔ W.E x (W.f y) = 0 ∧ W.E x y = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast W.d_pos)
    simp [herm, sqrtNeg] at hre him
    refine ⟨by exact_mod_cast hre, ?_⟩
    rcases him with h' | h'
    · exact absurd h' hs.ne'
    · exact_mod_cast h'
  · rintro ⟨h1, h2⟩
    simp [herm, h1, h2]

/-! ### The action of `K` -/

/-- `k • x = a x + b f(x)` for `k = a + b√-d ∈ K`. -/
noncomputable def smulK (k : Kd d) (x : V) : V :=
  Kd.ratPart d k • x + Kd.sqrtNegCoeff d k • W.f x

theorem herm_smulK_right (k : Kd d) (x y : V) : W.herm x (W.smulK k y) = (k : ℂ) * W.herm x y := by
  rw [smulK, W.herm_add_right, W.herm_smul_right, W.herm_smul_right, W.herm_f_right,
    vg_coe_Kd W.d_pos k]
  ring

theorem herm_smulK_left (k : Kd d) (x y : V) :
    W.herm (W.smulK k x) y = (starRingEnd ℂ) (k : ℂ) * W.herm x y := by
  rw [smulK, W.herm_add_left, W.herm_smul_left, W.herm_smul_left, W.herm_f_left,
    vg_coe_Kd W.d_pos k]
  simp only [map_add, map_mul, map_ratCast, fnd_conj_sqrtNeg]
  ring

/-! ### Change of `K`-basis: the discriminant up to norms -/

section Change

variable {ι : Type*}

/-- The `K`-coordinates of `y` in a `K`-basis `b` (the `ℚ`-basis `b, f b`). -/
noncomputable def coordK (qB : Module.Basis (ι ⊕ ι) ℚ V) (y : V) (i : ι) : Kd d :=
  algebraMap ℚ (Kd d) (qB.repr y (Sum.inl i)) +
    algebraMap ℚ (Kd d) (qB.repr y (Sum.inr i)) * Kd.sqrtNeg d

theorem coe_coordK (qB : Module.Basis (ι ⊕ ι) ℚ V) (y : V) (i : ι) :
    ((coordK (d := d) qB y i : Kd d) : ℂ) =
      (qB.repr y (Sum.inl i) : ℂ) + (qB.repr y (Sum.inr i) : ℂ) * sqrtNeg d := by
  simp only [coordK, Subfield.coe_add, Subfield.coe_mul, vg_coe_algebraMap]
  rfl

variable [Fintype ι]

theorem herm_expand_right (b : ι → V) (qB : Module.Basis (ι ⊕ ι) ℚ V)
    (hqB : ∀ s, qB s = Sum.elim b (fun i => W.f (b i)) s) (x y : V) :
    W.herm x y = ∑ i, ((coordK qB y i : Kd d) : ℂ) * W.herm x (b i) := by
  conv_lhs => rw [← qB.sum_repr y]
  rw [← W.hermL_apply, map_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, hqB, hqB]
  simp only [Sum.elim_inl, Sum.elim_inr, W.hermL_apply, W.herm_f_right, coe_coordK,
    Algebra.smul_def, eq_ratCast]
  ring

theorem herm_expand_left (b : ι → V) (qB : Module.Basis (ι ⊕ ι) ℚ V)
    (hqB : ∀ s, qB s = Sum.elim b (fun i => W.f (b i)) s) (x y : V) :
    W.herm y x = ∑ i, (starRingEnd ℂ) ((coordK qB y i : Kd d) : ℂ) * W.herm (b i) x := by
  rw [W.herm_swap, W.herm_expand_right b qB hqB, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← W.herm_swap]

variable [DecidableEq ι]

/-- **The discriminant up to norms.** If `b` is a `K`-basis (the vectors `bᵢ, f(bᵢ)` form a
`ℚ`-basis), then for every family `c` indexed by the same set,
`det H(cᵢ, cⱼ) = Nm(z) det H(bᵢ, bⱼ)` for some `z ∈ K` (`z` the determinant of the coordinates of
`c` in `b`). -/
theorem det_herm_change (b : ι → V) (qB : Module.Basis (ι ⊕ ι) ℚ V)
    (hqB : ∀ s, qB s = Sum.elim b (fun i => W.f (b i)) s) (c : ι → V) :
    ∃ z : Kd d, (Matrix.of fun i j => W.herm (c i) (c j)).det =
      (Kd.Nm d z : ℂ) * (Matrix.of fun i j => W.herm (b i) (b j)).det := by
  set MK : Matrix ι ι (Kd d) := Matrix.of fun i j => coordK qB (c j) i with hMK
  set M : Matrix ι ι ℂ := (Kd d).subtype.mapMatrix MK with hM
  have hgram : (Matrix.of fun i j => W.herm (c i) (c j)) =
      M.conjTranspose * (Matrix.of fun i j => W.herm (b i) (b j)) * M := by
    ext j l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hM,
      RingHom.mapMatrix_apply, Matrix.map_apply, hMK, Subfield.subtype_apply]
    rw [W.herm_expand_left b qB hqB]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [W.herm_expand_right b qB hqB (b i) (c l), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  refine ⟨MK.det, ?_⟩
  have hdet : M.det = ((MK.det : Kd d) : ℂ) := (RingHom.map_det (Kd d).subtype MK).symm
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet, Kd.coe_Nm W.d_pos,
    Complex.star_def]
  ring

end Change

/-! ### Definiteness bounds -/

/-- The trace form `(x, y) ↦ E(x, f y)` has positive index at most `N`: a trace-orthogonal family
with positive values `E(tᵢ, f tᵢ)` has at most `N` members. -/
def PosBound (N : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (t : ι → V), (∀ i j, i ≠ j → W.E (t i) (W.f (t j)) = 0) →
    (∀ i, 0 < W.E (t i) (W.f (t i))) → Fintype.card ι ≤ N

/-- The trace form has negative index at most `N`. -/
def NegBound (N : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (t : ι → V), (∀ i j, i ≠ j → W.E (t i) (W.f (t j)) = 0) →
    (∀ i, W.E (t i) (W.f (t i)) < 0) → Fintype.card ι ≤ N

/-! ### Hyperbolic pairs -/

/-- In an `f`-stable subspace `U` on which `E` is nondegenerate, an isotropic vector `u ≠ 0`
(`H(u, u) = E(u, f u) = 0`) has a partner `v ∈ U` with `H(v, v) = 0` and `H(u, v) = 1`. -/
theorem exists_hypPartner {U : Submodule ℚ V} (hU : ∀ x ∈ U, W.f x ∈ U)
    (hUnd : ∀ x ∈ U, (∀ y ∈ U, W.E x y = 0) → x = 0) {u : V} (hu : u ∈ U) (hu0 : u ≠ 0)
    (huu : W.E u (W.f u) = 0) :
    ∃ v ∈ U, W.E v (W.f v) = 0 ∧ W.E u v = 0 ∧ W.E u (W.f v) = 1 := by
  obtain ⟨w, hwU, hw⟩ : ∃ w ∈ U, W.E u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hUnd u hu h)
  obtain ⟨w₁, hw₁U, h1⟩ : ∃ w₁ ∈ U, W.E u w₁ = 1 :=
    ⟨(W.E u w)⁻¹ • w, U.smul_mem _ hwU, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  obtain ⟨w₀, hw₀U, h2, h3⟩ : ∃ w₀ ∈ U, W.E u w₀ = 0 ∧ W.E u (W.f w₀) = 1 := by
    have hff : W.E u (W.f (W.f w₁)) = -d := by rw [W.E_f_f_right, h1, mul_one]
    generalize ht : W.E u (W.f w₁) = t
    have hD : 0 < t ^ 2 + d := by have := W.d_pos; positivity
    refine ⟨(t / (t ^ 2 + d)) • w₁ + (-1 / (t ^ 2 + d)) • W.f w₁,
      U.add_mem (U.smul_mem _ hw₁U) (U.smul_mem _ (hU _ hw₁U)), ?_, ?_⟩
    · simp only [map_add, map_smul, smul_eq_mul, h1, ht]
      field_simp
      ring
    · simp only [map_add, map_smul, smul_eq_mul, hff, ht]
      field_simp
  have h4 : W.E w₀ (W.f u) = 1 := by rw [W.S_symm]; exact h3
  refine ⟨w₀ - (W.E w₀ (W.f w₀) / 2) • u, U.sub_mem hw₀U (U.smul_mem _ hu), ?_, ?_, ?_⟩
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h4, h3,
      huu]
    ring
  · simp only [map_sub, map_smul, smul_eq_mul, h2, W.E_self]
    ring
  · simp only [map_sub, map_smul, smul_eq_mul, h3, huu]
    ring

/-! ### Hyperbolic systems -/

/-- **A hyperbolic system** `u₁, v₁, …, u_m, v_m`: `H(uᵢ, uⱼ) = H(vᵢ, vⱼ) = 0` and
`H(uᵢ, vⱼ) = δᵢⱼ`, written with `E` (`H(x, y) = E(x, f y) + √-d E(x, y)`). -/
structure HypSys (m : ℕ) where
  /-- The first vectors of the hyperbolic planes. -/
  u : Fin m → V
  /-- The second vectors of the hyperbolic planes. -/
  v : Fin m → V
  uu : ∀ i j, W.E (u i) (u j) = 0
  vv : ∀ i j, W.E (v i) (v j) = 0
  uv : ∀ i j, W.E (u i) (v j) = 0
  ufu : ∀ i j, W.E (u i) (W.f (u j)) = 0
  vfv : ∀ i j, W.E (v i) (W.f (v j)) = 0
  ufv : ∀ i j, W.E (u i) (W.f (v j)) = if i = j then 1 else 0

/-- The empty hyperbolic system. -/
def HypSys.empty : W.HypSys 0 where
  u := Fin.elim0
  v := Fin.elim0
  uu i := i.elim0
  vv i := i.elim0
  uv i := i.elim0
  ufu i := i.elim0
  vfv i := i.elim0
  ufv i := i.elim0

namespace HypSys

variable {W} {m : ℕ} (s : W.HypSys m)

theorem vu (i j : Fin m) : W.E (s.v i) (s.u j) = 0 := by
  rw [W.E_swap, s.uv, neg_zero]

theorem vfu (i j : Fin m) : W.E (s.v i) (W.f (s.u j)) = if i = j then 1 else 0 := by
  rw [← W.S_symm, s.ufv]
  simp only [eq_comm]

/-- `u₁, …, u_m, v₁, …, v_m`. -/
def base : Fin m ⊕ Fin m → V := Sum.elim s.u s.v

theorem E_base_base (a b : Fin m ⊕ Fin m) : W.E (s.base a) (s.base b) = 0 := by
  rcases a with i | i <;> rcases b with j | j
  exacts [s.uu i j, s.uv i j, s.vu i j, s.vv i j]

theorem E_base_fbase (a b : Fin m ⊕ Fin m) :
    W.E (s.base a) (W.f (s.base b)) = if a = b.swap then 1 else 0 := by
  rcases a with i | i <;> rcases b with j | j
  · simp [base, s.ufu]
  · simp [base, s.ufv]
  · simp [base, s.vfu]
  · simp [base, s.vfv]

/-- The `4m` vectors `base, f(base)`. -/
def fam : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → V := Sum.elim s.base (fun a => W.f (s.base a))

/-- The values of `E` on the family `fam` (the same for every hyperbolic system). -/
def stdE : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → ℚ
  | Sum.inl a, Sum.inr b => if a = b.swap then 1 else 0
  | Sum.inr a, Sum.inl b => -(if a = b.swap then 1 else 0)
  | _, _ => 0

theorem E_fam_fam (α β : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) :
    W.E (s.fam α) (s.fam β) = stdE α β := by
  rcases α with a | a <;> rcases β with b | b
  · simp [fam, stdE, s.E_base_base]
  · simp [fam, stdE, s.E_base_fbase]
  · simp [fam, stdE, W.E_f_left, s.E_base_fbase]
  · simp [fam, stdE, W.E_ff, s.E_base_base]

/-- The dual family: `E(fam α, dual β) = δ_{αβ}`. -/
def dual : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → V :=
  Sum.elim (fun b => W.f (s.base b.swap)) (fun b => -s.base b.swap)

theorem E_fam_dual (α β : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) :
    W.E (s.fam α) (s.dual β) = if α = β then 1 else 0 := by
  rcases α with a | a <;> rcases β with b | b
  · simp [fam, dual, s.E_base_fbase]
  · simp [fam, dual, s.E_base_base]
  · simp [fam, dual, W.E_ff, s.E_base_base]
  · simp [fam, dual, W.E_f_left, s.E_base_fbase]

theorem fam_linearIndependent : LinearIndependent ℚ s.fam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg β
  have h : W.E (∑ α, g α • s.fam α) (s.dual β) = W.E 0 (s.dual β) := by rw [hg]
  rw [map_sum, LinearMap.sum_apply, map_zero, LinearMap.zero_apply] at h
  simp only [map_smul, LinearMap.smul_apply, s.E_fam_dual, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

theorem f_fam_inl (a : Fin m ⊕ Fin m) : W.f (s.fam (Sum.inl a)) = s.fam (Sum.inr a) := rfl

theorem f_fam_inr (a : Fin m ⊕ Fin m) :
    W.f (s.fam (Sum.inr a)) = -(d • s.fam (Sum.inl a)) := W.f_f _

/-! ### The orthogonal complement of a hyperbolic system -/

/-- The `E`-orthogonal complement of the span of `fam`. -/
def compl : Submodule ℚ V := LinearMap.ker (LinearMap.pi fun α => W.E (s.fam α))

theorem mem_compl {x : V} : x ∈ s.compl ↔ ∀ α, W.E (s.fam α) x = 0 := by
  simp only [compl, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Pi.zero_apply]

theorem f_mem_compl {x : V} (hx : x ∈ s.compl) : W.f x ∈ s.compl := by
  rw [mem_compl] at hx ⊢
  intro α
  have key : W.E (s.fam α) (W.f x) = -W.E (W.f (s.fam α)) x := by rw [W.E_f_left, neg_neg]
  rw [key]
  rcases α with a | a
  · rw [s.f_fam_inl, hx, neg_zero]
  · rw [s.f_fam_inr, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, hx,
      smul_zero, neg_zero, neg_zero]

theorem E_compl_fam {x : V} (hx : x ∈ s.compl) (α) : W.E x (s.fam α) = 0 := by
  rw [W.E_swap, (s.mem_compl.mp hx) α, neg_zero]

theorem E_compl_dual {x : V} (hx : x ∈ s.compl) (α) : W.E x (s.dual α) = 0 := by
  rcases α with b | b
  · exact s.E_compl_fam hx (Sum.inr b.swap)
  · show W.E x (-s.fam (Sum.inl b.swap)) = 0
    rw [map_neg, s.E_compl_fam hx, neg_zero]

/-- The projection of `z` to the span of `fam` along the complement. -/
def proj (z : V) : V := ∑ α, W.E (s.fam α) z • s.dual α

theorem sub_proj_mem (z : V) : z - s.proj z ∈ s.compl := by
  rw [mem_compl]
  intro β
  simp only [proj, map_sub, map_sum, map_smul, smul_eq_mul, s.E_fam_dual]
  simp

theorem compl_nondeg {x : V} (hx : x ∈ s.compl) (h : ∀ y ∈ s.compl, W.E x y = 0) : x = 0 := by
  refine W.nondeg x fun z => ?_
  have h1 := h _ (s.sub_proj_mem z)
  have h2 : W.E x (s.proj z) = 0 := by
    simp only [proj, map_sum, map_smul, smul_eq_mul, s.E_compl_dual hx, mul_zero,
      Finset.sum_const_zero]
  rw [map_sub, h2, sub_zero] at h1
  exact h1

theorem finrank_compl [FiniteDimensional ℚ V] :
    finrank ℚ V ≤ finrank ℚ s.compl + 4 * m := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun α => W.E (s.fam α))
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.pi fun α => W.E (s.fam α)))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
  rw [compl]
  omega

theorem E_u_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (s.u i) x = 0 :=
  (s.mem_compl.mp hx) (Sum.inl (Sum.inl i))

theorem E_v_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (s.v i) x = 0 :=
  (s.mem_compl.mp hx) (Sum.inl (Sum.inr i))

theorem E_fu_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (W.f (s.u i)) x = 0 :=
  (s.mem_compl.mp hx) (Sum.inr (Sum.inl i))

theorem E_fv_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (W.f (s.v i)) x = 0 :=
  (s.mem_compl.mp hx) (Sum.inr (Sum.inr i))

theorem E_compl_u {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E x (s.u i) = 0 := by
  rw [W.E_swap, s.E_u_compl hx, neg_zero]

theorem E_compl_v {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E x (s.v i) = 0 := by
  rw [W.E_swap, s.E_v_compl hx, neg_zero]

theorem E_compl_fu {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E x (W.f (s.u i)) = 0 :=
  s.E_compl_fam hx (Sum.inr (Sum.inl i))

theorem E_compl_fv {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E x (W.f (s.v i)) = 0 :=
  s.E_compl_fam hx (Sum.inr (Sum.inr i))

theorem E_u_f_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (s.u i) (W.f x) = 0 := by
  rw [← neg_neg (W.E (s.u i) (W.f x)), ← W.E_f_left, s.E_fu_compl hx, neg_zero]

theorem E_v_f_compl {x : V} (hx : x ∈ s.compl) (i : Fin m) : W.E (s.v i) (W.f x) = 0 := by
  rw [← neg_neg (W.E (s.v i) (W.f x)), ← W.E_f_left, s.E_fv_compl hx, neg_zero]

/-- Extend a hyperbolic system by a hyperbolic pair in its complement. -/
def extend {u' v' : V} (hu' : u' ∈ s.compl) (hv' : v' ∈ s.compl) (h1 : W.E u' (W.f u') = 0)
    (h2 : W.E v' (W.f v') = 0) (h3 : W.E u' v' = 0) (h4 : W.E u' (W.f v') = 1) :
    W.HypSys (m + 1) where
  u := Fin.snoc s.u u'
  v := Fin.snoc s.v v'
  uu i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [W.E_self]
      | cast j => simp [s.E_compl_u hu']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_u_compl hu']
      | cast j => simp [s.uu]
  vv i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [W.E_self]
      | cast j => simp [s.E_compl_v hv']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_v_compl hv']
      | cast j => simp [s.vv]
  uv i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using h3
      | cast j => simp [s.E_compl_v hu']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_u_compl hv']
      | cast j => simp [s.uv]
  ufu i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using h1
      | cast j => simp [W.S_symm u', s.E_u_f_compl hu']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_u_f_compl hu']
      | cast j => simp [s.ufu]
  vfv i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using h2
      | cast j => simp [W.S_symm v', s.E_v_f_compl hv']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_v_f_compl hv']
      | cast j => simp [s.vfv]
  ufv i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using h4
      | cast j =>
        simp [W.S_symm u', s.E_v_f_compl hu', (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [s.E_u_f_compl hv', (Fin.castSucc_lt_last i).ne]
      | cast j => simp [s.ufv]

/-- An isotropic vector of the complement extends the system. -/
theorem extend_of_isotropic {x : V} (hx : x ∈ s.compl) (hx0 : x ≠ 0)
    (hxx : W.E x (W.f x) = 0) : Nonempty (W.HypSys (m + 1)) := by
  obtain ⟨y, hy, h2, h3, h4⟩ :=
    W.exists_hypPartner (fun z hz => s.f_mem_compl hz) (fun z hz h => s.compl_nondeg hz h) hx
      hx0 hxx
  exact ⟨s.extend hx hy hxx h2 h3 h4⟩

/-! ### Isotropic vectors in the complement -/

/-- The complement has a basis orthogonal for the trace form, with nonzero values
`E(bᵢ, f bᵢ)` (Gram–Schmidt and nondegeneracy). -/
theorem exists_orthBasis_compl [FiniteDimensional ℚ V] :
    ∃ b : Fin (finrank ℚ s.compl) → V, (∀ i, b i ∈ s.compl) ∧
      (∀ i j, i ≠ j → W.E (b i) (W.f (b j)) = 0) ∧ ∀ i, W.E (b i) (W.f (b i)) ≠ 0 := by
  let B : LinearMap.BilinForm ℚ s.compl := LinearMap.BilinForm.restrict (W.E.compl₂ W.f) s.compl
  have hBapp : ∀ x y : s.compl, B x y = W.E x (W.f y) := fun x y => rfl
  have hB : LinearMap.IsSymm B := ⟨fun x y => by
    rw [RingHom.id_apply, hBapp, hBapp, W.S_symm]⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  refine ⟨fun i => (v i : V), fun i => (v i).2, fun i j hij => ?_, fun i h0 => ?_⟩
  · have h : B (v i) (v j) = 0 := hv hij
    rw [hBapp] at h
    exact h
  · have hBi : B (v i) = 0 := v.ext fun j => by
      by_cases hij : i = j
      · subst hij
        rw [hBapp, LinearMap.zero_apply]
        exact h0
      · rw [LinearMap.zero_apply]
        exact hv hij
    apply v.ne_zero i
    apply Subtype.ext
    refine s.compl_nondeg (v i).2 fun y hy => ?_
    have hy' : y = W.f (-(d⁻¹) • W.f y) := by
      rw [map_smul, W.f_f, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ W.d_pos.ne', neg_smul,
        one_smul, neg_neg]
    have h1 := LinearMap.congr_fun hBi ⟨-(d⁻¹) • W.f y, s.compl.smul_mem _ (s.f_mem_compl hy)⟩
    rw [hBapp, LinearMap.zero_apply] at h1
    rw [hy']
    exact h1

theorem E_z_fz (ε ε' : ℚ) (i j : Fin m) :
    W.E (s.u i + ε • s.v i) (W.f (s.u j + ε' • s.v j)) = if i = j then ε + ε' else 0 := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, s.ufu,
    s.ufv, s.vfu, s.vfv]
  split_ifs <;> ring

theorem E_z_z (ε ε' : ℚ) (i j : Fin m) : W.E (s.u i + ε • s.v i) (s.u j + ε' • s.v j) = 0 := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, s.uu,
    s.uv, s.vu, s.vv]
  ring

theorem herm_z_compl (ε : ℚ) (i : Fin m) {w : V} (hw : w ∈ s.compl) :
    W.herm (s.u i + ε • s.v i) w = 0 ∧ W.herm w (s.u i + ε • s.v i) = 0 := by
  have h1 : W.herm (s.u i + ε • s.v i) w = 0 := by
    rw [herm_eq_zero_iff]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      s.E_u_f_compl hw, s.E_v_f_compl hw, s.E_u_compl hw, s.E_v_compl hw]
    constructor <;> ring
  refine ⟨h1, ?_⟩
  rw [W.herm_swap, h1, map_zero]

/-- The vectors `zᵢ = uᵢ + ε vᵢ` and `f zᵢ` added to a trace-orthogonal family of the complement
keep it orthogonal; `E(zᵢ, f zᵢ) = 2ε` and `E(f zᵢ, f(f zᵢ)) = 2εd`. -/
theorem orth_aux {ι : Type*} (b : ι → V) (hbU : ∀ i, b i ∈ s.compl)
    (hb : ∀ i j, i ≠ j → W.E (b i) (W.f (b j)) = 0) (ε : ℚ) :
    (∀ a c, a ≠ c → W.E (Sum.elim b (Sum.elim (fun i => s.u i + ε • s.v i)
        (fun i => W.f (s.u i + ε • s.v i))) a) (W.f (Sum.elim b (Sum.elim
        (fun i => s.u i + ε • s.v i) (fun i => W.f (s.u i + ε • s.v i))) c)) = 0) ∧
      (∀ i, W.E (s.u i + ε • s.v i) (W.f (s.u i + ε • s.v i)) = 2 * ε) ∧
      (∀ i, W.E (W.f (s.u i + ε • s.v i)) (W.f (W.f (s.u i + ε • s.v i))) = 2 * ε * d) := by
  have hzz : ∀ i j, W.E (s.u i + ε • s.v i) (W.f (s.u j + ε • s.v j)) =
      if i = j then 2 * ε else 0 := by
    intro i j
    rw [s.E_z_fz]
    split_ifs <;> ring
  have hz0 : ∀ i j, W.E (s.u i + ε • s.v i) (s.u j + ε • s.v j) = 0 := s.E_z_z ε ε
  have hbz : ∀ i j, W.E (b i) (W.f (s.u j + ε • s.v j)) = 0 := by
    intro i j
    simp only [map_add, map_smul, smul_eq_mul, s.E_compl_fu (hbU i), s.E_compl_fv (hbU i)]
    ring
  have hbz' : ∀ i j, W.E (b i) (s.u j + ε • s.v j) = 0 := by
    intro i j
    simp only [map_add, map_smul, smul_eq_mul, s.E_compl_u (hbU i), s.E_compl_v (hbU i)]
    ring
  refine ⟨?_, fun i => by simpa using hzz i i, fun i => ?_⟩
  · rintro (i | i | i) (j | j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hb i j fun h => hij (by rw [h])
    · exact hbz i j
    · rw [W.E_f_f_right, hbz' i j, mul_zero, neg_zero]
    · rw [W.S_symm, hbz j i]
    · rw [hzz, ite_eq_right fun h => hij (by rw [h])]
    · rw [W.E_f_f_right, hz0, mul_zero, neg_zero]
    · rw [W.E_ff, W.E_swap, hbz' j i, neg_zero, mul_zero]
    · rw [W.E_ff, hz0, mul_zero]
    · rw [W.E_f_f_right, W.E_f_left, hzz, ite_eq_right fun h => hij (by rw [h])]
      ring
  · rw [W.E_f_f_right, W.E_f_left, hzz, ite_eq_left rfl]
    ring

/-- If the trace form has negative index at most `2n` and `m < n`, the complement of a hyperbolic
system of size `m` contains a vector with `E(x, f x) > 0`. -/
theorem exists_pos_compl [FiniteDimensional ℚ V] {n : ℕ} (hdim : finrank ℚ V = 2 * (2 * n))
    (hneg : W.NegBound (2 * n)) (hm : m < n) : ∃ x ∈ s.compl, 0 < W.E x (W.f x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbU, hborth, hb0⟩ := s.exists_orthBasis_compl
  obtain ⟨horth, hz, hfz⟩ := s.orth_aux b hbU hborth (-1)
  have h := hneg _ _ horth ?_
  · simp only [Fintype.card_sum, Fintype.card_fin] at h
    have := s.finrank_compl
    omega
  · rintro (i | i | i)
    · exact lt_of_le_of_ne (hcon _ (hbU i)) (hb0 i)
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hz]
      norm_num
    · simp only [Sum.elim_inr]
      rw [hfz]
      have := W.d_pos
      linarith

/-- If the trace form has positive index at most `2n` and `m < n`, the complement of a hyperbolic
system of size `m` contains a vector with `E(x, f x) < 0`. -/
theorem exists_neg_compl [FiniteDimensional ℚ V] {n : ℕ} (hdim : finrank ℚ V = 2 * (2 * n))
    (hpos : W.PosBound (2 * n)) (hm : m < n) : ∃ x ∈ s.compl, W.E x (W.f x) < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbU, hborth, hb0⟩ := s.exists_orthBasis_compl
  obtain ⟨horth, hz, hfz⟩ := s.orth_aux b hbU hborth 1
  have h := hpos _ _ horth ?_
  · simp only [Fintype.card_sum, Fintype.card_fin] at h
    have := s.finrank_compl
    omega
  · rintro (i | i | i)
    · exact lt_of_le_of_ne (hcon _ (hbU i)) (hb0 i).symm
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hz]
      norm_num
    · simp only [Sum.elim_inr]
      rw [hfz]
      have := W.d_pos
      linarith

/-- **Meyer's theorem** gives an isotropic vector in the complement when it has dimension at
least `8` (`m + 2 ≤ n`): the trace form is indefinite on it. -/
theorem exists_isotropic_of_le [FiniteDimensional ℚ V] {n : ℕ} (hdim : finrank ℚ V = 2 * (2 * n))
    (hpos : W.PosBound (2 * n)) (hneg : W.NegBound (2 * n)) (hm : m + 2 ≤ n) :
    ∃ x ∈ s.compl, x ≠ 0 ∧ W.E x (W.f x) = 0 := by
  obtain ⟨x₁, hx₁U, hx₁⟩ := s.exists_pos_compl hdim hneg (by omega)
  obtain ⟨x₂, hx₂U, hx₂⟩ := s.exists_neg_compl hdim hpos (by omega)
  let B : LinearMap.BilinForm ℚ s.compl := LinearMap.BilinForm.restrict (W.E.compl₂ W.f) s.compl
  let Q : QuadraticForm ℚ s.compl := LinearMap.BilinMap.toQuadraticMap B
  have hQ : ∀ x : s.compl, Q x = W.E x (W.f x) := fun x => rfl
  have hrank : 5 ≤ finrank ℚ s.compl := by
    have := s.finrank_compl
    omega
  have hind : HasseMinkowski.Indefinite (QuadraticForm.baseChange ℝ Q) := by
    constructor
    · refine ⟨(1 : ℝ) ⊗ₜ[ℚ] (⟨x₂, hx₂U⟩ : s.compl), ?_⟩
      rw [QuadraticForm.baseChange_tmul, hQ, mul_one, Rat.smul_one_eq_cast]
      exact_mod_cast hx₂
    · refine ⟨(1 : ℝ) ⊗ₜ[ℚ] (⟨x₁, hx₁U⟩ : s.compl), ?_⟩
      rw [QuadraticForm.baseChange_tmul, hQ, mul_one, Rat.smul_one_eq_cast]
      exact_mod_cast hx₁
  obtain ⟨x, hx0, hxQ⟩ := HasseMinkowski.meyer Q hrank hind
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hxQ⟩

/-- **The last hyperbolic plane.** If `m + 1 = n` and `det H(bᵢ, bⱼ) ∈ (-1)ⁿ Nm(K)` for a `K`-basis
`b`, the complement of a hyperbolic system of size `m` (of `K`-rank `2`) contains an isotropic
vector: with `w₁`, `w₂` an `H`-orthogonal pair in it, `H(w₁, w₁) H(w₂, w₂) = -Nm(λ)` (the
discriminant), and `λ/H(w₁, w₁) • w₁ + w₂` is isotropic. -/
theorem exists_isotropic_last [FiniteDimensional ℚ V] {n : ℕ} (hdim : finrank ℚ V = 2 * (2 * n))
    (hmn : m + 1 = n) (b : Fin (2 * n) → V)
    (hb : LinearIndependent ℚ (Sum.elim b (fun i => W.f (b i)))) (k : Kd d)
    (hk : (Matrix.of fun i j => W.herm (b i) (b j)).det =
      (((-1) ^ n : ℚ) : ℂ) * (Kd.Nm d k : ℂ)) :
    ∃ x ∈ s.compl, x ≠ 0 ∧ W.E x (W.f x) = 0 := by
  have hU := s.finrank_compl
  -- a first vector `w₁` of the complement
  have hUpos : s.compl ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hU
    omega
  obtain ⟨w₁, hw₁U, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUpos
  by_cases ha : W.E w₁ (W.f w₁) = 0
  · exact ⟨w₁, hw₁U, hw₁0, ha⟩
  -- a second vector `w₂` of the complement, `H`-orthogonal to `w₁`
  let Ψ : s.compl →ₗ[ℚ] (Fin 2 → ℚ) :=
    LinearMap.pi ![(W.E w₁).comp s.compl.subtype, (W.E w₁).comp (W.f.comp s.compl.subtype)]
  have hker : LinearMap.ker Ψ ≠ ⊥ := by
    intro h0
    have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
    have h2 := Submodule.finrank_le (LinearMap.range Ψ)
    rw [h0, finrank_bot] at h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hy1 : W.E w₁ y = 0 := congrFun (LinearMap.mem_ker.mp hy) 0
  have hy2 : W.E w₁ (W.f y) = 0 := congrFun (LinearMap.mem_ker.mp hy) 1
  set w₂ : V := (y : V) with hw₂
  have hw₂U : w₂ ∈ s.compl := y.2
  have hw₂0 : w₂ ≠ 0 := fun h => hy0 (Subtype.ext h)
  by_cases hc : W.E w₂ (W.f w₂) = 0
  · exact ⟨w₂, hw₂U, hw₂0, hc⟩
  have h12 : W.herm w₁ w₂ = 0 := (W.herm_eq_zero_iff _ _).mpr ⟨hy2, hy1⟩
  have h21 : W.herm w₂ w₁ = 0 := by rw [W.herm_swap, h12, map_zero]
  -- the discriminant in the `K`-basis `(uᵢ + vᵢ, uᵢ - vᵢ, w₁, w₂)`: `(-4)^m a c`
  have hcard : Fintype.card (Fin (2 * n) ⊕ Fin (2 * n)) = finrank ℚ V := by
    rw [hdim, Fintype.card_sum, Fintype.card_fin]
    ring
  let qB := basisOfLinearIndependentOfCardEqFinrank' _ hb hcard
  have hqB : ∀ t, qB t = Sum.elim b (fun i => W.f (b i)) t := fun t =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hb hcard) t
  let c₀ : (Fin m ⊕ Fin m) ⊕ Fin 2 → V :=
    Sum.elim (Sum.elim (fun i => s.u i + (1 : ℚ) • s.v i) (fun i => s.u i + (-1 : ℚ) • s.v i))
      ![w₁, w₂]
  have he : Fintype.card (Fin (2 * n)) = Fintype.card ((Fin m ⊕ Fin m) ⊕ Fin 2) := by
    simp only [Fintype.card_fin, Fintype.card_sum]
    omega
  let e := Fintype.equivOfCardEq he
  obtain ⟨z, hz⟩ := W.det_herm_change b qB hqB (c₀ ∘ e)
  have hwU : ∀ q, (![w₁, w₂] : Fin 2 → V) q ∈ s.compl := fun q => by
    fin_cases q
    · exact hw₁U
    · exact hw₂U
  have hdiag : (Matrix.of fun α β => W.herm (c₀ α) (c₀ β)) =
      Matrix.diagonal (fun α => W.herm (c₀ α) (c₀ α)) := by
    ext α β
    rw [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hαβ
    · rw [hαβ]
    · rcases α with (i | i) | p <;> rcases β with (j | j) | q <;>
        simp only [c₀, Sum.elim_inl, Sum.elim_inr]
      · rw [herm_eq_zero_iff]
        refine ⟨?_, s.E_z_z _ _ _ _⟩
        rw [s.E_z_fz, ite_eq_right fun h => hαβ (by rw [h])]
      · rw [herm_eq_zero_iff]
        refine ⟨?_, s.E_z_z _ _ _ _⟩
        rw [s.E_z_fz]
        split_ifs <;> norm_num
      · exact (s.herm_z_compl _ i (hwU q)).1
      · rw [herm_eq_zero_iff]
        refine ⟨?_, s.E_z_z _ _ _ _⟩
        rw [s.E_z_fz]
        split_ifs <;> norm_num
      · rw [herm_eq_zero_iff]
        refine ⟨?_, s.E_z_z _ _ _ _⟩
        rw [s.E_z_fz, ite_eq_right fun h => hαβ (by rw [h])]
      · exact (s.herm_z_compl _ i (hwU q)).1
      · exact (s.herm_z_compl _ j (hwU p)).2
      · exact (s.herm_z_compl _ j (hwU p)).2
      · fin_cases p <;> fin_cases q
        · exact absurd rfl hαβ
        · exact h12
        · exact h21
        · exact absurd rfl hαβ
  have hdetc : (Matrix.of fun i j => W.herm ((c₀ ∘ e) i) ((c₀ ∘ e) j)).det =
      (Matrix.of fun α β => W.herm (c₀ α) (c₀ β)).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  rw [hdetc, hdiag, Matrix.det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type,
    Fin.prod_univ_two, hk] at hz
  simp only [c₀, Sum.elim_inl, Sum.elim_inr, W.herm_self, s.E_z_fz, ite_true,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hz
  have hzQ : (1 + 1 : ℚ) ^ m * (-1 + -1) ^ m * (W.E w₁ (W.f w₁) * W.E w₂ (W.f w₂)) =
      Kd.Nm d z * ((-1) ^ n * Kd.Nm d k) := by
    exact_mod_cast hz
  set a := W.E w₁ (W.f w₁)
  set c := W.E w₂ (W.f w₂)
  set σ : ℚ := (-1) ^ m with hσdef
  have hσ : σ * σ = 1 := by rw [hσdef, ← mul_pow]; norm_num
  have hkey : (2 : ℚ) ^ m * 2 ^ m * (a * c) = -(Kd.Nm d z * Kd.Nm d k) := by
    have e1 : (-1 + -1 : ℚ) ^ m = σ * 2 ^ m := by
      rw [hσdef, ← mul_pow]; norm_num
    have e2 : (-1 : ℚ) ^ n = σ * (-1) := by rw [← hmn, pow_succ]
    rw [e1, e2, show (1 + 1 : ℚ) = 2 by norm_num] at hzQ
    linear_combination σ * hzQ - (2 ^ m * 2 ^ m * (a * c) + Kd.Nm d z * Kd.Nm d k) * hσ
  -- the isotropic vector `λ • w₁ + w₂`, `λ = z k / (2^m a)`
  set l : Kd d := z * k * algebraMap ℚ (Kd d) (2 ^ m * a)⁻¹ with hl
  refine ⟨W.smulK l w₁ + w₂, ?_, ?_, ?_⟩
  · exact s.compl.add_mem (s.compl.add_mem (s.compl.smul_mem _ hw₁U)
      (s.compl.smul_mem _ (s.f_mem_compl hw₁U))) hw₂U
  · intro h0
    have hw : w₂ = -W.smulK l w₁ := eq_neg_of_add_eq_zero_right h0
    apply hc
    have h := W.herm_self w₂
    rw [hw, W.herm_neg_right, ← hw, W.herm_smulK_right, h21, mul_zero, neg_zero] at h
    exact_mod_cast h.symm
  · have hx : W.herm (W.smulK l w₁ + w₂) (W.smulK l w₁ + w₂) =
        (starRingEnd ℂ) (l : ℂ) * (l : ℂ) * (a : ℂ) + (c : ℂ) := by
      rw [W.herm_add_left, W.herm_add_right, W.herm_add_right, W.herm_smulK_left,
        W.herm_smulK_left, W.herm_smulK_right, W.herm_smulK_right, h12, h21, W.herm_self,
        W.herm_self]
      ring
    have hl' : (starRingEnd ℂ) (l : ℂ) * (l : ℂ) =
        ((Kd.Nm d z * Kd.Nm d k * ((2 ^ m * a)⁻¹) ^ 2 : ℚ) : ℂ) := by
      rw [hl, Subfield.coe_mul, Subfield.coe_mul, vg_coe_algebraMap]
      simp only [map_mul, map_ratCast]
      push_cast
      rw [Kd.coe_Nm W.d_pos, Kd.coe_Nm W.d_pos]
      ring
    rw [hl'] at hx
    have hxQ : W.E (W.smulK l w₁ + w₂) (W.f (W.smulK l w₁ + w₂)) =
        Kd.Nm d z * Kd.Nm d k * ((2 ^ m * a)⁻¹) ^ 2 * a + c := by
      have h := W.herm_self (W.smulK l w₁ + w₂)
      rw [hx] at h
      exact_mod_cast h.symm
    rw [hxQ, show Kd.Nm d z * Kd.Nm d k = -(2 ^ m * 2 ^ m * (a * c)) by linarith]
    have h2 : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    ring

end HypSys

/-! ### Landherr's theorem -/

/-- **Landherr's theorem (split case)**, in the form used for abelian varieties of Weil type: a
nondegenerate Hermitian space over `K = ℚ(√-d)` of `K`-rank `2n` whose trace form
`E(x, f y)` has positive and negative indices at most `2n` (signature `(n, n)` of `H`) and whose
discriminant is `(-1)ⁿ` up to norms (`det H(bᵢ, bⱼ) ∈ (-1)ⁿ Nm(K)` for a `K`-basis `b`) is
hyperbolic: it has a hyperbolic basis `u₁, v₁, …, u_n, v_n`. The isotropic vectors come from
Meyer's theorem (`HasseMinkowski.meyer`) while the complement has `K`-rank at least `4`, and from
the discriminant for the last plane. -/
theorem landherr_split [FiniteDimensional ℚ V] {n : ℕ} (hn : 0 < n)
    (hdim : finrank ℚ V = 2 * (2 * n)) (hpos : W.PosBound (2 * n)) (hneg : W.NegBound (2 * n))
    (b : Fin (2 * n) → V) (hb : LinearIndependent ℚ (Sum.elim b (fun i => W.f (b i))))
    (k : Kd d)
    (hk : (Matrix.of fun i j => W.herm (b i) (b j)).det =
      (((-1) ^ n : ℚ) : ℂ) * (Kd.Nm d k : ℂ)) :
    Nonempty (W.HypSys n) := by
  have key : ∀ m, m + 1 ≤ n → Nonempty (W.HypSys m) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨HypSys.empty W⟩
    | succ m ih =>
      intro hm
      obtain ⟨s⟩ := ih (by omega)
      obtain ⟨x, hx, hx0, hxx⟩ := s.exists_isotropic_of_le hdim hpos hneg (by omega)
      exact s.extend_of_isotropic hx hx0 hxx
  obtain ⟨s⟩ := key (n - 1) (by omega)
  obtain ⟨x, hx, hx0, hxx⟩ := s.exists_isotropic_last hdim (by omega) b hb k hk
  have h := s.extend_of_isotropic hx hx0 hxx
  rwa [show n - 1 + 1 = n by omega] at h

/-- Two Hermitian spaces with hyperbolic bases of the same size are isometric: there is a
`ℚ`-linear isomorphism commuting with `f` and carrying `E` to `E₀`. -/
theorem exists_isometry {V₀ : Type*} [AddCommGroup V₀] [Module ℚ V₀] {W₀ : vg_HermSpace d V₀}
    [FiniteDimensional ℚ V] [FiniteDimensional ℚ V₀] {n : ℕ} (hdim : finrank ℚ V = 2 * (2 * n))
    (hdim₀ : finrank ℚ V₀ = 2 * (2 * n)) (s : W.HypSys n) (s₀ : W₀.HypSys n) :
    ∃ φ : V ≃ₗ[ℚ] V₀, (∀ x, φ (W.f x) = W₀.f (φ x)) ∧ ∀ x y, W₀.E (φ x) (φ y) = W.E x y := by
  have hcard : Fintype.card ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) = finrank ℚ V := by
    rw [hdim]
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  have hcard₀ : Fintype.card ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) = finrank ℚ V₀ := by
    rw [hdim₀]
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  let B := basisOfLinearIndependentOfCardEqFinrank' _ s.fam_linearIndependent hcard
  let B₀ := basisOfLinearIndependentOfCardEqFinrank' _ s₀.fam_linearIndependent hcard₀
  have hB : ∀ α, B α = s.fam α := fun α =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ s.fam_linearIndependent hcard) α
  have hB₀ : ∀ α, B₀ α = s₀.fam α := fun α =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ s₀.fam_linearIndependent hcard₀) α
  let φ := B.equiv B₀ (Equiv.refl _)
  have hφ : ∀ α, φ (s.fam α) = s₀.fam α := fun α => by
    rw [← hB, ← hB₀]
    exact B.equiv_apply α B₀ (Equiv.refl _)
  refine ⟨φ, fun x => ?_, fun x y => ?_⟩
  · have h : φ.toLinearMap ∘ₗ W.f = W₀.f ∘ₗ φ.toLinearMap := B.ext fun α => by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hB]
      rcases α with a | a
      · rw [s.f_fam_inl, hφ, hφ, s₀.f_fam_inl]
      · rw [s.f_fam_inr, map_neg, map_smul, hφ, hφ, s₀.f_fam_inr]
    exact LinearMap.congr_fun h x
  · have h : W₀.E.compl₁₂ φ.toLinearMap φ.toLinearMap = W.E :=
      LinearMap.BilinForm.ext_basis B fun α β => by
        rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hB, hB, hφ, hφ, s.E_fam_fam,
          s₀.E_fam_fam]
    have := LinearMap.congr_fun₂ h x y
    rwa [LinearMap.compl₁₂_apply] at this

end vg_HermSpace

end WeilClasses
