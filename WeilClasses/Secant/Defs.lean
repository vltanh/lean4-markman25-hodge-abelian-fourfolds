module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Main.Coordinates
public import WeilClasses.WeilType.Theta

/-!
# Characteristic classes of secant objects (paper §1.3, §6.2, §8.2–8.3): definitions

The cohomological objects attached to secant sheaves, in the model `H*(X × X̂, F) = ⋀• V_F`
(`ExtV F n`) and `H*(X, F) = S_F`.

## `κ` (§1.3)

For a class `ch ∈ H^{ev}(X × X̂, ℚ)` with graded summands `ch_i ∈ H^{2i}` and `ch₀ = r ≠ 0`,
`κ(ch) = exp(-ch₁/r) ch` (`WeilClasses.kappa`); `κ_k` is its summand in `H^{2k}`
(`WeilClasses.kappaDeg`). Here `r = ch₀` is the degree-`0` coefficient (`WeilClasses.rankExt`,
Mathlib's `ExteriorAlgebra.algebraMapInv`) and `ch₁` the degree-`2` component (`projDeg F n 2`).

## Secant classes (§1.3, Definition 6.2.2)

* `WeilClasses.tauExt`: the main anti-automorphism `τ` of `H*(X × X̂) = ⋀• V` (reversal,
  `(-1)^{k(k-1)/2}` on `⋀^k V`). For an object `G` of `Dᵇ(X × X̂)`, `ch(G^∨) = τ(ch G)` (geometric,
  the analogue of Remark 5.2.3; not formalized).
* `WeilClasses.secantSqClass F n w₁ w₂ = φ(w₁ ⊗ τ(w₂))`, `φ = phiOrlov` (6.1.3): for objects `F₁`,
  `F₂` of `Dᵇ(X)` with `ch(Fᵢ) = wᵢ`, this is `ch(Φ(F₁ ⊠ F₂^∨))`, since `ch(F₂^∨) = τ(ch F₂)` and the
  cohomological action of Orlov's equivalence is `φ` (both geometric: Remark 5.2.3 and GRR, not
  formalized). When `w₁, w₂ ∈ P`, `Φ(F₁ ⊠ F₂^∨)` is a *`P`-secant`^{⊠2}`-object* (§1.3,
  Definition 6.2.2, where the roles of `F₁`, `F₂` are exchanged: `Φ(F₂ ⊠ F₁^∨)` has class
  `secantSqClass F n w₂ w₁`). `secantSqClass F n w₁ w₂ = φ'(w₁ ⊗ w₂)`, `φ' = φ ∘ (id ⊗ τ)`
  (`secantSqClass_eq_phiPrime`).

## The class `h` of `Ξ_P` and `H²(X × X̂, ℚ)_P` (§1.3, §6.2, §8.3)

* `WeilClasses.formToExt2 F n B ∈ ⋀² V_F`: the class of a bilinear form `B` on `V_F` under the
  isomorphism `V_F ≅ V_F*`, `x ↦ (x, ·)_V`; for alternating `B` it is characterized by
  `⟪B^♯, (x, ·)_V ∧ (y, ·)_V⟫ = B(x, y)` (`formToExt2_spec`). In the basis `f_i, e_i` of `V`
  (`vecF`, `vecE`; `(f_i, e_j)_V = δ_{ij}`) it is
  `½ Σ B(f_i, f_j) e_i ∧ e_j + Σ B(f_i, e_j) e_i ∧ f_j + ½ Σ B(e_i, e_j) f_i ∧ f_j`.
* `WeilClasses.KSecant.hClass P hW = Ξ_P^♯`, the class in `H²(X × X̂, ℚ) = ⋀² V_ℚ` of the `2`-form
  `Ξ_P` (2.4.2). This is how the paper regards `Ξ_P` as an element of `H²(X × X̂, ℚ)` (§6.2:
  "`H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P + ℚ Ξ_P`"); the identification is `Spin(V)`-equivariant. The
  paper's ample class `h` spanning `H²(X × X̂, ℚ)^{Spin(V)_P}` (§1.3, §8.3) is a positive multiple of
  it; we take `h = Ξ_P^♯`. For `P = P_Θ` with `Θ = e₁ ∧ e₂ + ⋯` (`ThetaStd`) it is
  `d Θ + Θ̂`, `Θ̂ = f₁ ∧ f₂ + ⋯` (computed numerically for `n ≤ 3`; this is `WeilClasses.hV` of
  `WeilClasses.Main.Jacobian`).
* `WeilClasses.KSecant.H2P P`: `H²(X × X̂, ℚ)_P`, "the direct sum of all non-trivial irreducible
  `Spin(V)_P`-subrepresentations of `H²(X × X̂, ℚ)`" (§6.2). **Definition used:** the span of the
  vectors `ρ_g(x) - x`, `g ∈ Spin(V)_P` (the integral group `P.spinPZ`), `x ∈ ⋀² V_ℚ`. For a
  completely reducible representation `U` this is the sum of the non-trivial isotypic components
  (each non-trivial irreducible `U'` satisfies `U' = span{ρ_g x - x : x ∈ U'}`, and `ρ_g x - x` has no
  component in the invariants). `⋀² V_ℚ` is completely reducible under `Spin(V)_P` (over `K` it is
  `⋀²W₁ ⊕ ⋀²W₂ ⊕ sl(W₁) ⊕ K`, irreducible summands of `SL(W₁) ≅ Spin(V_K)_P`, in which `Spin(V)_P` is
  Zariski dense; see `WeilClasses.PureSpinor.Lemma2_2_7`), so the two definitions agree.

## The classes of §8.2 (`n = 3`)

`X` is the Jacobian of a non-hyperelliptic genus-`3` curve with theta divisor `Θ`; in the model
`Θ = ThetaStd ℚ 3` (`Θ³/6 = [pt]`, `ThetaStd_pow`), for a complex structure `J` of `H¹(X, ℝ)` for
which `Θ` is ample.

* `WeilClasses.alphaJac d = 1 - (d/2) Θ²`, `WeilClasses.betaJac d = Θ - d [pt]` (§8.2), with
  `exp(√-d Θ) = α + √-d β`.
* `WeilClasses.chF1 d = 1 + Θ - (d/2) Θ² - d [pt]` (Lemma 8.2.1): the Chern character of
  `F₁ = I_{∪_{i=1}^{d+1} Cᵢ}(Θ)` (and of `F₂ = I_{∪ Σᵢ}(Θ)` of Theorem 1.4.1, the `Σᵢ` translates of
  `-AJ(C)`, which have the same class `Θ²/2`). The value of the Chern character is geometric
  (Poincaré's formula `[C_t] = Θ²/2`, `χ(𝒪_C) = -2`, Riemann–Roch); in the model `chF1 d` is the
  input class.
* `WeilClasses.chE d = τ(φ(w ⊗ w))`, `w = chF1 d`: the Chern character of the sheaf `E` of
  Theorem 1.4.1(2). There `Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]` (equivalently `𝒢 = Φ(F₂ ⊠ F₁)[-3]`,
  `E = 𝒢^∨[-1]`, §9.2), so `ch(E) = ch(Φ(F₂ ⊠ F₁)^∨)` (an even shift does not change `ch`)
  `= τ(ch Φ(F₂ ⊠ F₁)) = τ(φ(ch F₂ ⊗ ch F₁))`. Since `τ` acts on `H^{2i}` by `(-1)^i` and is a ring
  automorphism of `H^{ev}`, `κ(τ x) = τ(κ x)`; so `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))` and the rank of `E` is that
  of `Φ(F₂ ⊠ F₁)` (it is `8d`, `WeilClasses.Main.Intro`).
* `WeilClasses.kappa3E d = κ₃(E)`.
* `WeilClasses.PJac hΘ d hd`: the oriented `K`-secant `P_Θ` of §2.4 for `Θ = ThetaStd ℚ 3`
  (`P = span{α, β}`, §8.2–8.3), and `PJac_isCompl` (`V_K = W₁ ⊕ W₂`).

## A complex structure for which `Θ` is ample

`WeilClasses.s8_J0` (`J₀ e_{2i} = -e_{2i+1}`, `J₀ e_{2i+1} = e_{2i}`), with `s8_J0_isComplex` and
`s8_ample_J0` (`ThetaStd` is ample for `J₀`): the one copy of `J₀` used throughout the library.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prefix `s8_`): `2`-vectors of an exterior algebra -/

section S8General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem s8_ι_mul_ι_mem (a b : M) :
    ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b ∈ ⋀[R]^2 M := by
  have ha : ExteriorAlgebra.ι R a ∈ ⋀[R]^1 M := by simp
  have hb : ExteriorAlgebra.ι R b ∈ ⋀[R]^1 M := by simp
  exact SetLike.mul_mem_graded ha hb

/-- `d ⌋ (a ∧ b) = d(a) b - d(b) a`. -/
theorem s8_contractLeft_ι_mul_ι (d : Module.Dual R M) (a b : M) :
    contractLeft (Q := 0) d (ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b) =
      d a • ExteriorAlgebra.ι R b - d b • ExteriorAlgebra.ι R a := by
  change contractLeft (Q := 0) d (CliffordAlgebra.ι 0 a * CliffordAlgebra.ι 0 b) = _
  rw [contractLeft_ι_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- `⟪a ∧ b, d ∧ d'⟫ = d' ⌋ (d ⌋ (a ∧ b)) = d(a) d'(b) - d(b) d'(a)`. -/
theorem s8_algebraMapInv_contractLeft_contractLeft_ι_mul_ι (d d' : Module.Dual R M) (a b : M) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) d'
        (contractLeft (Q := 0) d (ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b))) =
      d a * d' b - d b * d' a := by
  rw [s8_contractLeft_ι_mul_ι, map_sub, map_smul, map_smul]
  change ExteriorAlgebra.algebraMapInv (d a • contractLeft (Q := 0) d' (CliffordAlgebra.ι 0 b) -
    d b • contractLeft (Q := 0) d' (CliffordAlgebra.ι 0 a)) = _
  rw [contractLeft_ι, contractLeft_ι, map_sub, map_smul, map_smul]
  simp [ExteriorAlgebra.algebraMapInv]

/-- An element of positive degree has zero degree-`0` part. -/
theorem s8_algebraMapInv_eq_zero_of_mem {k : ℕ} (hk : 0 < k) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) : ExteriorAlgebra.algebraMapInv x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- `ExteriorAlgebra.map` preserves the degree-`0` part. -/
theorem s8_algebraMapInv_map {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map g x) = ExteriorAlgebra.algebraMapInv x := by
  have h : (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R N →ₐ[R] R).comp
      (ExteriorAlgebra.map g) = ExteriorAlgebra.algebraMapInv := by
    ext w
    simp [ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun h x


theorem s8_contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (φ : Module.Dual R N) (ξ : ExteriorAlgebra R M) :
    contractLeft (Q := 0) φ (ExteriorAlgebra.map f ξ) =
      ExteriorAlgebra.map f (contractLeft (Q := 0) (φ ∘ₗ f) ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    change contractLeft (Q := 0) φ (ExteriorAlgebra.map f (ExteriorAlgebra.ι R m * x)) =
      ExteriorAlgebra.map f (contractLeft (Q := 0) (φ ∘ₗ f) (ExteriorAlgebra.ι R m * x))
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    change contractLeft (Q := 0) φ (CliffordAlgebra.ι 0 (f m) * ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (contractLeft (Q := 0) (φ ∘ₗ f) (CliffordAlgebra.ι 0 m * x))
    rw [contractLeft_ι_mul, contractLeft_ι_mul, hx, map_sub, map_smul, map_mul,
      LinearMap.comp_apply]
    congr 2
    exact (ExteriorAlgebra.map_apply_ι f m).symm

theorem s8_numberOp_ιMulti {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (k : ℕ)
    (v : Fin k → M) :
    ∑ i, ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := 0) (b.coord i) (ExteriorAlgebra.ιMulti R k v) =
      (k : R) • ExteriorAlgebra.ιMulti R k v := by
  induction k with
  | zero =>
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    set y := ExteriorAlgebra.ιMulti R k (Matrix.vecTail v)
    have hcl : ∀ i, contractLeft (Q := 0) (b.coord i) (ExteriorAlgebra.ι R (v 0) * y) =
        b.coord i (v 0) • y - ExteriorAlgebra.ι R (v 0) * contractLeft (Q := 0) (b.coord i) y :=
      fun i => contractLeft_ι_mul (Q := 0) _ _ _
    simp only [hcl, mul_sub, mul_smul_comm, Finset.sum_sub_distrib]
    have h1 : ∑ i, b.coord i (v 0) • (ExteriorAlgebra.ι R (b i) * y) =
        ExteriorAlgebra.ι R (v 0) * y := by
      simp only [← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum,
        Module.Basis.coord_apply, b.sum_repr]
    have h2 : ∑ i, ExteriorAlgebra.ι R (b i) * (ExteriorAlgebra.ι R (v 0) *
        contractLeft (Q := 0) (b.coord i) y) =
        -(ExteriorAlgebra.ι R (v 0) * ∑ i, ExteriorAlgebra.ι R (b i) *
          contractLeft (Q := 0) (b.coord i) y) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← neg_mul]
      congr 1
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [h1, h2, ih, sub_neg_eq_add, mul_smul_comm, Nat.cast_succ, add_smul, one_smul, add_comm]

/-- The number operator `Σᵢ bᵢ ∧ (bᵢ* ⌋ ·)` acts on `⋀ᵏ M` by `k`. -/
theorem s8_numberOp {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) {k : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    ∑ i, ExteriorAlgebra.ι R (b i) * contractLeft (Q := 0) (b.coord i) x = (k : R) • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact s8_numberOp_ιMulti b k v
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, mul_add, Finset.sum_add_distrib, hx, hy, smul_add]
  | smul c x _ hx =>
    simp only [map_smul, mul_smul_comm, ← Finset.smul_sum, hx, smul_comm c]

/-- Contraction lowers the degree by one. -/
theorem s8_contractLeft_mem (φ : Module.Dual R M) {k : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^(k + 1) M) : contractLeft (Q := 0) φ x ∈ ⋀[R]^k M := by
  induction k generalizing x with
  | zero =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      change contractLeft (Q := 0) φ (CliffordAlgebra.ι 0 (v 0)) ∈ _
      rw [contractLeft_ι]
      exact SetLike.algebraMap_mem_graded _ _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  | succ k ih =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      change contractLeft (Q := 0) φ (CliffordAlgebra.ι 0 (v 0) * _) ∈ _
      rw [contractLeft_ι_mul]
      have hy : ExteriorAlgebra.ιMulti R (k + 1) (Matrix.vecTail v) ∈ ⋀[R]^(k + 1) M :=
        ExteriorAlgebra.ιMulti_range R (k + 1) ⟨_, rfl⟩
      refine sub_mem (Submodule.smul_mem _ _ hy) ?_
      have h1 : ExteriorAlgebra.ι R (v 0) ∈ ⋀[R]^1 M := by simp
      have := SetLike.mul_mem_graded h1 (ih hy)
      rwa [add_comm] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- A degree-`0` element is a scalar. -/
theorem s8_eq_algebraMap_of_mem_zero {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    x = algebraMap R _ (ExteriorAlgebra.algebraMapInv x) := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one] at hx
  obtain ⟨r, rfl⟩ := hx
  rw [ExteriorAlgebra.algebraMap_leftInverse]

end S8General

section S8Field
variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]

/-- An element of positive degree all of whose contractions vanish is zero. -/
theorem s8_eq_zero_of_contractLeft {ι : Type*} [Fintype ι] (b : Module.Basis ι K M) {k : ℕ}
    (hk : 0 < k) {x : ExteriorAlgebra K M} (hx : x ∈ ⋀[K]^k M)
    (h : ∀ φ : Module.Dual K M, contractLeft (Q := 0) φ x = 0) : x = 0 := by
  have := s8_numberOp b hx
  simp only [h, mul_zero, Finset.sum_const_zero] at this
  exact (smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast hk.ne')

end S8Field

/-! ## Helpers (prefix `s8_`): degrees, `τ`, `exp`, base change, `K`, `Re`/`Im` -/

section S8Ext
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s8_exteriorPower_eq_bot {k : ℕ} (hk : 2 * n < k) : ⋀[F]^k (H1 F n) = ⊥ := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_eq_bot]
  rintro _ ⟨v, rfl⟩
  apply AlternatingMap.map_linearDependent
  intro hv
  have := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
  omega

omit [CharZero F] in
theorem s8_mem_bot_of_lt {k : ℕ} (hk : 2 * n < k) {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n)) :
    x = 0 := by
  rw [s8_exteriorPower_eq_bot F n hk] at hx
  exact (Submodule.mem_bot F).mp hx

omit [CharZero F] in
theorem s8_pow_mem {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) (k : ℕ) :
    u ^ k ∈ ⋀[F]^(2 * k) (H1 F n) := by
  rw [show 2 * k = k • 2 by rw [smul_eq_mul, mul_comm]]
  exact SetLike.pow_mem_graded k hu

omit [CharZero F] in
theorem s8_pow_eq_zero {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) {k : ℕ} (hk : n < k) :
    u ^ k = 0 :=
  s8_mem_bot_of_lt F n (by omega) (s8_pow_mem F n hu k)

omit [CharZero F] in
theorem s8_basisS_mem (K : Finset (Fin (2 * n))) : basisS F n K ∈ ⋀[F]^K.card (H1 F n) := by
  rw [basisS, ExteriorAlgebra.basis_apply_ofCard _ (rfl : K.card = K.card)]
  exact (exteriorPower.ιMulti_family F K.card _ _).2

omit [CharZero F] in
theorem s8_pt_mem : pt F n ∈ ⋀[F]^(2 * n) (H1 F n) := by
  have h := s8_basisS_mem F n Finset.univ
  rwa [Finset.card_univ, Fintype.card_fin] at h

omit [CharZero F] in
/-- The coefficients of a homogeneous class of degree `k` vanish off the subsets of size `k`. -/
theorem s8_repr_eq_zero_of_mem {k : ℕ} {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n))
    (K : Finset (Fin (2 * n))) (hK : K.card ≠ k) : (basisS F n).repr x K = 0 := by
  have hproj : ∀ y : S F n, GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k y =
      ∑ L ∈ Finset.univ.filter (fun L : Finset (Fin (2 * n)) => L.card = k),
        (basisS F n).repr y L • basisS F n L := by
    intro y
    conv_lhs => rw [← (basisS F n).sum_repr y]
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [map_smul, GradedAlgebra.proj_apply]
    split_ifs with hL
    · rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (H1 F n))
        (hL ▸ s8_basisS_mem F n L)]
    · rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (H1 F n)) (s8_basisS_mem F n L) hL,
        smul_zero]
  have hx' : GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k x = x := by
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (H1 F n)) hx]
  have := congrArg (fun y => (basisS F n).repr y K) hx'
  simp only [hproj, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply] at this
  rw [← this]
  refine Finset.sum_eq_zero fun L hL => ?_
  have hLk : L.card = k := (Finset.mem_filter.mp hL).2
  have : L ≠ K := fun h => hK (h ▸ hLk)
  simp [this]

omit [CharZero F] in
theorem s8_integral_eq_zero_of_mem {k : ℕ} (hk : k ≠ 2 * n) {x : S F n}
    (hx : x ∈ ⋀[F]^k (H1 F n)) : integral F n x = 0 :=
  s8_repr_eq_zero_of_mem F n hx Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; exact hk.symm)

omit [CharZero F] in
theorem s8_integral_pt : integral F n (pt F n) = 1 := by
  simp [integral, pt]

omit [CharZero F] in
theorem s8_tau_ι_mul_ι (a b : H1 F n) :
    tau F n (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) =
      -(ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) := by
  change reverse (CliffordAlgebra.ι 0 a * CliffordAlgebra.ι 0 b) = _
  rw [reverse.map_mul, reverse_ι, reverse_ι]
  have h := ExteriorAlgebra.ι_add_mul_swap (R := F) a b
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

end S8Ext


section S8Tau
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s8_tau_mul (x y : S F n) : tau F n (x * y) = tau F n y * tau F n x :=
  reverse.map_mul x y

omit [CharZero F] in
theorem s8_tau_one : tau F n 1 = 1 := reverse.map_one

omit [CharZero F] in
theorem s8_tau_of_mem_two {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) : tau F n u = -u := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact s8_tau_ι_mul_ι F n (v 0) (v 1)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul c x _ hx => rw [map_smul, hx, smul_neg]

omit [CharZero F] in
theorem s8_tau_pow {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) (k : ℕ) :
    tau F n (u ^ k) = (-u) ^ k := by
  induction k with
  | zero => simp [s8_tau_one]
  | succ k ih => rw [pow_succ, s8_tau_mul, ih, s8_tau_of_mem_two F n hu, pow_succ']

theorem s8_tau_exp {u : S F n} (hu : u ∈ ⋀[F]^2 (H1 F n)) :
    tau F n (IsNilpotent.exp u) = IsNilpotent.exp (-u) := by
  have h1 : u ^ (n + 1) = 0 := s8_pow_eq_zero F n hu (by omega)
  have h2 : (-u) ^ (n + 1) = 0 := s8_pow_eq_zero F n (neg_mem hu) (by omega)
  rw [IsNilpotent.exp_eq_sum h1, IsNilpotent.exp_eq_sum h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, s8_tau_pow F n hu]

/-- For `n = 3`: `exp(u) = 1 + u + u²/2 + u³/6`. -/
theorem s8_exp_three {u : S F 3} (hu : u ∈ ⋀[F]^2 (H1 F 3)) :
    IsNilpotent.exp u = 1 + u + (2 : F)⁻¹ • u ^ 2 + (6 : F)⁻¹ • u ^ 3 := by
  have hq : ∀ (q : ℚ) (x : S F 3), q • x = (q : F) • x := fun q x =>
    (Rat.cast_smul_eq_qsmul F q x).symm
  rw [IsNilpotent.exp_eq_sum (s8_pow_eq_zero F 3 hu (by norm_num : 3 < 4))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hq]
  norm_num

end S8Tau

section S8BC
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] [CharZero F'] in
theorem s8_bcH1_e (i : Fin (2 * n)) : bcH1 F F' n (e F n i) = e F' n i := by
  funext k
  simp [bcH1, e, Pi.single_apply]

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) := by
  exact ExteriorAlgebra.lift_ι_apply F _ _ w

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_ιMulti (k : ℕ) (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp [s8_bcS_ι]

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_basisS (K : Finset (Fin (2 * n))) : bcS F F' n (basisS F n K) = basisS F' n K := by
  rw [basisS, basisS, ExteriorAlgebra.basis_apply_ofCard _ (rfl : K.card = K.card),
    ExteriorAlgebra.basis_apply_ofCard _ (rfl : K.card = K.card)]
  simp only [ExteriorAlgebra.ιMulti_family, s8_bcS_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.basisFun_apply]
  exact s8_bcH1_e F F' n _

omit [CharZero F] [CharZero F'] in
theorem s8_repr_bcS (x : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n x) K = algebraMap F F' ((basisS F n).repr x K) := by
  have h : bcS F F' n x = ∑ L, algebraMap F F' ((basisS F n).repr x L) • basisS F' n L := by
    conv_lhs => rw [← (basisS F n).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [map_smul, s8_bcS_basisS, algebraMap_smul]
  rw [h, Module.Basis.repr_sum_self]

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_injective : Function.Injective (bcS F F' n) := by
  intro x y h
  apply (basisS F n).repr.injective
  ext K
  have := congrArg (fun s => (basisS F' n).repr s K) h
  simpa [s8_repr_bcS] using this

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_ThetaStd : bcS F F' n (ThetaStd F n) = ThetaStd F' n := by
  simp [ThetaStd, map_sum, map_mul, s8_bcS_ι, s8_bcH1_e]

omit [CharZero F] [CharZero F'] in
theorem s8_bcS_pt : bcS F F' n (pt F n) = pt F' n := s8_bcS_basisS F F' n _

omit [CharZero F] [CharZero F'] in
theorem s8_integral_bcS (x : S F n) :
    integral F' n (bcS F F' n x) = algebraMap F F' (integral F n x) :=
  s8_repr_bcS F F' n x Finset.univ

end S8BC

section S8Kd
variable (d : ℚ)

theorem s8_coe_algebraMap (q : ℚ) : ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := by
  simp

theorem s8_ratPart_spec (z : Kd d) : ((Kd.ratPart d z : ℚ) : ℝ) = (z : ℂ).re :=
  Classical.choose_spec (Kd.exists_ratPart d z)

theorem s8_ratPart_eq (z : Kd d) (a : ℚ) (h : (z : ℂ).re = a) : Kd.ratPart d z = a := by
  have := s8_ratPart_spec d z
  rw [h] at this
  exact_mod_cast this

theorem s8_ratPart_algebraMap (q : ℚ) : Kd.ratPart d (algebraMap ℚ (Kd d) q) = q :=
  s8_ratPart_eq d _ q (by rw [s8_coe_algebraMap]; simp)

theorem s8_ratPart_sqrtNeg : Kd.ratPart d (Kd.sqrtNeg d) = 0 :=
  s8_ratPart_eq d _ 0 (by simp [Kd.sqrtNeg, sqrtNeg])

theorem s8_sqrtNeg_mul_self {d : ℚ} (hd : 0 ≤ d) :
    Kd.sqrtNeg d * Kd.sqrtNeg d = algebraMap ℚ (Kd d) (-d) := by
  apply Subtype.ext
  change sqrtNeg d * sqrtNeg d = ((algebraMap ℚ (Kd d) (-d) : Kd d) : ℂ)
  rw [s8_coe_algebraMap, ← sq, sqrtNeg_sq hd]
  push_cast; ring

theorem s8_sqrtNeg_ne_zero {d : ℚ} (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have h2 := s8_sqrtNeg_mul_self hd.le
  rw [h, zero_mul] at h2
  have : (-d : ℚ) = 0 := by
    have := congrArg (fun z : Kd d => ((z : ℂ))) h2
    simp only [ZeroMemClass.coe_zero] at this
    rw [s8_coe_algebraMap] at this
    exact_mod_cast this.symm
  linarith

theorem s8_sqrtNegCoeff_sqrtNeg {d : ℚ} (hd : 0 < d) : Kd.sqrtNegCoeff d (Kd.sqrtNeg d) = 1 := by
  simp only [Kd.sqrtNegCoeff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, s8_sqrtNeg_mul_self hd.le, s8_ratPart_algebraMap, smul_eq_mul]
  field_simp

theorem s8_sqrtNegCoeff_algebraMap (q : ℚ) : Kd.sqrtNegCoeff d (algebraMap ℚ (Kd d) q) = 0 := by
  simp only [Kd.sqrtNegCoeff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, s8_ratPart_sqrtNeg, smul_zero, mul_zero]

end S8Kd

section S8ReIm
variable (n : ℕ) (d : ℚ)

theorem s8_repr_coeffMapS (φ : Kd d →ₗ[ℚ] ℚ) (s : S (Kd d) n) (K : Finset (Fin (2 * n))) :
    (basisS ℚ n).repr (coeffMapS n d φ s) K = φ ((basisS (Kd d) n).repr s K) := by
  rw [coeffMapS, LinearMap.comp_apply, LinearEquiv.coe_coe, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  rfl

theorem s8_coeffMapS_smul_bcS (φ : Kd d →ₗ[ℚ] ℚ) (c : Kd d) (x : S ℚ n) :
    coeffMapS n d φ (c • bcS ℚ (Kd d) n x) = φ c • x := by
  apply (basisS ℚ n).repr.injective
  ext K
  rw [s8_repr_coeffMapS, LinearEquiv.map_smul, Finsupp.smul_apply, s8_repr_bcS,
    LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← Algebra.commutes,
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem s8_reS_smul_bcS (c : Kd d) (x : S ℚ n) :
    reS n d (c • bcS ℚ (Kd d) n x) = Kd.ratPart d c • x :=
  s8_coeffMapS_smul_bcS n d _ c x

theorem s8_imS_smul_bcS (c : Kd d) (x : S ℚ n) :
    imS n d (c • bcS ℚ (Kd d) n x) = Kd.sqrtNegCoeff d c • x :=
  s8_coeffMapS_smul_bcS n d _ c x

theorem s8_reS_bcS (x : S ℚ n) : reS n d (bcS ℚ (Kd d) n x) = x := by
  have := s8_reS_smul_bcS n d 1 x
  rwa [one_smul, ← map_one (algebraMap ℚ (Kd d)), s8_ratPart_algebraMap, one_smul] at this

theorem s8_imS_bcS (x : S ℚ n) : imS n d (bcS ℚ (Kd d) n x) = 0 := by
  have := s8_imS_smul_bcS n d 1 x
  rwa [one_smul, ← map_one (algebraMap ℚ (Kd d)), s8_sqrtNegCoeff_algebraMap, zero_smul] at this

end S8ReIm

section S8Theta

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- `Θ = Σ e_{2i} ∧ e_{2i+1}` has degree `2`. -/
theorem s8_ThetaStd_mem : ThetaStd F n ∈ ⋀[F]^2 (H1 F n) :=
  Submodule.sum_mem _ fun _ _ => s8_ι_mul_ι_mem _ _

/-- `Θ³ = 6 [pt]` (`n = 3`, `ThetaStd_pow`). -/
theorem s8_Theta_cube : ThetaStd F 3 ^ 3 = (6 : F) • pt F 3 := by
  rw [ThetaStd_pow]
  norm_num [Nat.factorial]

/-- `[pt] = Θ³/6` (`n = 3`). -/
theorem s8_pt_three : pt F 3 = (6 : F)⁻¹ • ThetaStd F 3 ^ 3 := by
  rw [s8_Theta_cube, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

omit [CharZero F] in
/-- `Θᵏ = 0` for `k ≥ 4` (`n = 3`). -/
theorem s8_Theta_pow_eq_zero {k : ℕ} (hk : 3 < k) : ThetaStd F 3 ^ k = 0 :=
  s8_pow_eq_zero F 3 (s8_ThetaStd_mem F 3) hk

end S8Theta

section S8Basis

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s8_basisS_empty : basisS F n ∅ = 1 := by
  rw [basisS, ExteriorAlgebra.basis_apply_ofCard _ (rfl : (∅ : Finset (Fin (2 * n))).card = 0)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

omit [CharZero F] in
theorem s8_basisSHat_empty : basisSHat F n ∅ = 1 := by
  rw [basisSHat, ExteriorAlgebra.basis_apply_ofCard _ (rfl : (∅ : Finset (Fin (2 * n))).card = 0)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

omit [CharZero F] in
theorem s8_algebraMapInv_basisS (K : Finset (Fin (2 * n))) :
    ExteriorAlgebra.algebraMapInv (basisS F n K) = if K = ∅ then 1 else 0 := by
  split_ifs with hK
  · rw [hK, s8_basisS_empty, map_one]
  · exact s8_algebraMapInv_eq_zero_of_mem
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hK)) (s8_basisS_mem F n K)

omit [CharZero F] in
theorem s8_algebraMapInv_basisSHat (K : Finset (Fin (2 * n))) :
    ExteriorAlgebra.algebraMapInv (basisSHat F n K) = if K = ∅ then 1 else 0 := by
  split_ifs with hK
  · rw [hK, s8_basisSHat_empty, map_one]
  · refine s8_algebraMapInv_eq_zero_of_mem
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hK)) ?_
    rw [basisSHat, ExteriorAlgebra.basis_apply_ofCard _ (rfl : K.card = K.card)]
    exact (exteriorPower.ιMulti_family F K.card _ _).2

omit [CharZero F] in
theorem s8_epsSign_empty_left (K : Finset (Fin (2 * n))) : epsSign F n ∅ K = 1 := by
  simp [epsSign, s8_basisS_empty]

omit [CharZero F] in
theorem s8_epsSign_empty_right (K : Finset (Fin (2 * n))) : epsSign F n K ∅ = 1 := by
  simp [epsSign, s8_basisS_empty]

omit [CharZero F] in
theorem s8_neg_one_pow_top : (-1 : F) ^ ((2 * n) * ((2 * n) + 3) / 2) = (-1 : F) ^ n := by
  have h : (2 * n) * ((2 * n) + 3) / 2 = 2 * (n * n + n) + n := by
    rw [show (2 * n) * ((2 * n) + 3) = 2 * (2 * (n * n + n) + n) by ring,
      Nat.mul_div_cancel_left _ two_pos]
  rw [h, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

omit [CharZero F] in
theorem s8_basisS_mul_eq_zero {K L : Finset (Fin (2 * n))} (h : ¬Disjoint K L) :
    basisS F n K * basisS F n L = 0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun F (Fin (2 * n)))
    (Set.powersetCard.ofCard (rfl : K.card = K.card))
    (Set.powersetCard.ofCard (rfl : L.card = L.card)) h

omit [CharZero F] in
/-- `∫_X e_K ∧ e_L = ε_{K,L}` if `K ∪ L = [2n]`, and `0` otherwise. -/
theorem s8_integral_basisS_mul (K L : Finset (Fin (2 * n))) :
    integral F n (basisS F n K * basisS F n L) =
      if K ∪ L = Finset.univ then epsSign F n K L else 0 := by
  split_ifs with h
  · rw [epsSign, h]; rfl
  · by_cases hd : Disjoint K L
    · have hmem : basisS F n K * basisS F n L ∈ ⋀[F]^(K.card + L.card) (H1 F n) :=
        SetLike.mul_mem_graded (s8_basisS_mem F n K) (s8_basisS_mem F n L)
      refine s8_repr_eq_zero_of_mem F n hmem Finset.univ ?_
      rw [Finset.card_univ, Fintype.card_fin, ← Finset.card_union_of_disjoint hd]
      intro hc
      exact h (Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact hc.symm))
    · rw [s8_basisS_mul_eq_zero F n hd, map_zero]

end S8Basis

/-! ## `κ` and the rank -/

section Kappa

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The class `φ(w₁ ⊗ τ(w₂))` (`φ = phiOrlov`, (6.1.3)): for objects `F₁, F₂` of `Dᵇ(X)` with
`ch(Fᵢ) = wᵢ` it is `ch(Φ(F₁ ⊠ F₂^∨))` (geometric: `ch(F₂^∨) = τ(ch F₂)` and GRR for Orlov's kernel;
not formalized). For `w₁, w₂` in a `K`-secant plane `P` this is the class of a
`P`-secant`^{⊠2}`-object (§1.3, Definition 6.2.2). -/
noncomputable def secantSqClass (w₁ w₂ : S F n) : ExtV F n :=
  phiOrlov F n (w₁ ⊗ₜ[F] tau F n w₂)

/-- `φ(w₁ ⊗ τ w₂) = φ'(w₁ ⊗ w₂)` with `φ' = φ ∘ (id ⊗ τ)` (`phiPrime`). -/
theorem secantSqClass_eq_phiPrime (w₁ w₂ : S F n) :
    secantSqClass F n w₁ w₂ = phiPrime F n (w₁ ⊗ₜ[F] w₂) := by
  simp [secantSqClass, phiPrime, tauTensor]

end Kappa

/-! ## The class of a bilinear form, `h = Ξ_P^♯`, and `H²(X × X̂, ℚ)_P` -/

section Sharp

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The vector `e_i = (0, e_i) ∈ V_F` (the summand `H¹(X, F)`). -/
noncomputable def vecE (i : Fin (2 * n)) : V F n := (0, e F n i)

/-- The vector `f_i = (f_i, 0) ∈ V_F` (the summand `H¹(X̂, F) = H¹(X, F)*`); `(f_i, e_j)_V = δ_{ij}`. -/
noncomputable def vecF (i : Fin (2 * n)) : V F n := (f F n i, 0)

/-- The class `B^♯ ∈ ⋀² V_F` of a bilinear form `B` on `V_F` under `V_F ≅ V_F*`, `x ↦ (x, ·)_V`:
`½ Σ B(f_i, f_j) e_i ∧ e_j + Σ B(f_i, e_j) e_i ∧ f_j + ½ Σ B(e_i, e_j) f_i ∧ f_j` (the dual basis of
`f_i, e_i` for `(·,·)_V` is `e_i, f_i`). For alternating `B`, `⟪B^♯, (x,·)_V ∧ (y,·)_V⟫ = B(x, y)`
(`formToExt2_spec`). -/
noncomputable def formToExt2 (B : LinearMap.BilinForm F (V F n)) : ExtV F n :=
  (∑ i, ∑ j, ((2 : F)⁻¹ * B (vecF F n i) (vecF F n j)) •
      (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecE F n j))) +
    (∑ i, ∑ j, B (vecF F n i) (vecE F n j) •
      (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecF F n j))) +
    ∑ i, ∑ j, ((2 : F)⁻¹ * B (vecE F n i) (vecE F n j)) •
      (ExteriorAlgebra.ι F (vecF F n i) * ExteriorAlgebra.ι F (vecF F n j))

/-! ### Helpers (prefix `s8_`): contractions of `2`-vectors, coordinates of `V_F` -/

omit [CharZero F] in
theorem s8_pairing_apply (x z : V F n) : pairing F n x z = x.1 z.2 + z.1 x.2 := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q,
    QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

omit [CharZero F] in
/-- `(x, e_i)_V = x.1(e_i)`. -/
theorem s8_pairing_vecE (x : V F n) (i : Fin (2 * n)) :
    pairing F n x (vecE F n i) = x.1 (e F n i) := by
  simp [vecE]

omit [CharZero F] in
/-- `(x, f_i)_V = x.2(i)`. -/
theorem s8_pairing_vecF (x : V F n) (i : Fin (2 * n)) :
    pairing F n x (vecF F n i) = x.2 i := by
  simp [vecF, f]

omit [CharZero F] in
theorem s8_dual_eq_sum (y : Module.Dual F (H1 F n)) : y = ∑ i, y (e F n i) • f F n i := by
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  simp [f, e, Pi.single_apply]

omit [CharZero F] in
theorem s8_H1_eq_sum (w : H1 F n) : w = ∑ i, w i • e F n i := by
  funext k
  simp [e, Pi.single_apply]

omit [CharZero F] in
/-- `x = Σ x.1(e_i) f_i + Σ x.2(i) e_i` in `V_F`. -/
theorem s8_V_eq_sum (x : V F n) :
    x = ∑ i, x.1 (e F n i) • vecF F n i + ∑ i, x.2 i • vecE F n i := by
  ext1
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, vecF, vecE, smul_zero,
      Finset.sum_const_zero, add_zero]
    exact s8_dual_eq_sum F n x.1
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, vecF, vecE, smul_zero,
      Finset.sum_const_zero, zero_add]
    exact s8_H1_eq_sum F n x.2

theorem s8_sum_skew {ι : Type*} [Fintype ι] (a c : ι → F) (G : ι → ι → F)
    (hG : ∀ i j, G j i = -G i j) :
    ∑ i, ∑ j, (2⁻¹ * G i j) * (a i * c j - a j * c i) = ∑ i, ∑ j, a i * c j * G i j := by
  have h : ∑ i, ∑ j, (2⁻¹ * G i j) * (a j * c i) = ∑ i, ∑ j, -(2⁻¹ * (a i * c j * G i j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hG]; ring
  have h2 : ∑ i, ∑ j, (2⁻¹ * G i j) * (a i * c j - a j * c i) =
      ∑ i, ∑ j, 2⁻¹ * (a i * c j * G i j) - ∑ i, ∑ j, (2⁻¹ * G i j) * (a j * c i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h]
  simp only [Finset.sum_neg_distrib, sub_neg_eq_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [CharZero F] in
theorem s8_sum_cross {ι : Type*} [Fintype ι] (a b c d : ι → F) (FE EF : ι → ι → F)
    (hEF : ∀ i j, EF i j = -FE j i) :
    ∑ i, ∑ j, FE i j * (a i * d j - b j * c i) =
      ∑ i, ∑ j, a i * d j * FE i j + ∑ i, ∑ j, b i * c j * EF i j := by
  have h : ∑ i, ∑ j, FE i j * (b j * c i) = ∑ i, ∑ j, -(b i * c j * EF i j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hEF]; ring
  have h2 : ∑ i, ∑ j, FE i j * (a i * d j - b j * c i) =
      ∑ i, ∑ j, a i * d j * FE i j - ∑ i, ∑ j, FE i j * (b j * c i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h]
  simp only [Finset.sum_neg_distrib, sub_neg_eq_add]

omit [CharZero F] in
theorem s8_sum_swap {ι : Type*} [Fintype ι] (a c : ι → F) (G : ι → ι → F) :
    ∑ j, ∑ i, c j * (a i * G i j) = ∑ i, ∑ j, a i * c j * G i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `B^♯` has degree `2`. -/
theorem formToExt2_mem (B : LinearMap.BilinForm F (V F n)) :
    formToExt2 F n B ∈ ⋀[F]^2 (V F n) := by
  unfold formToExt2
  refine add_mem (add_mem ?_ ?_) ?_ <;>
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (s8_ι_mul_ι_mem _ _)

/-- The characterization of `B^♯` for alternating `B`: `⟪B^♯, (x, ·)_V ∧ (y, ·)_V⟫ = B(x, y)`, where
`⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-`0` part), as in `WeilClasses.eval2`. Equivalently
`extPairing (x ∧ y) B^♯ = B(x, y)`. -/
theorem formToExt2_spec (B : LinearMap.BilinForm F (V F n)) (hB : B.IsAlt) (x y : V F n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing F n y) (contractLeft (Q := 0) (pairing F n x)
          (formToExt2 F n B))) = B x y := by
  have hE : ∀ a b : V F n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b))) =
      pairing F n x a * pairing F n y b - pairing F n x b * pairing F n y a :=
    fun a b => s8_algebraMapInv_contractLeft_contractLeft_ι_mul_ι _ _ a b
  -- the left side, term by term (`⟪a ∧ b, x ∧ y⟫ = (x, a)(y, b) - (x, b)(y, a)`)
  have hL : ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) (formToExt2 F n B))) =
      (∑ i, ∑ j, (2⁻¹ * B (vecF F n i) (vecF F n j)) *
          (x.1 (e F n i) * y.1 (e F n j) - x.1 (e F n j) * y.1 (e F n i))) +
        (∑ i, ∑ j, B (vecF F n i) (vecE F n j) * (x.1 (e F n i) * y.2 j - x.2 j * y.1 (e F n i))) +
        ∑ i, ∑ j, (2⁻¹ * B (vecE F n i) (vecE F n j)) * (x.2 i * y.2 j - x.2 j * y.2 i) := by
    simp only [formToExt2, map_add, map_sum, map_smul, hE, smul_eq_mul, s8_pairing_vecE,
      s8_pairing_vecF]
  -- the right side, expanding `x` and `y` in the basis `f_i, e_i`
  have hR : B x y = (∑ i, ∑ j, x.1 (e F n i) * y.1 (e F n j) * B (vecF F n i) (vecF F n j)) +
      (∑ i, ∑ j, x.1 (e F n i) * y.2 j * B (vecF F n i) (vecE F n j)) +
      (∑ i, ∑ j, x.2 i * y.1 (e F n j) * B (vecE F n i) (vecF F n j)) +
      ∑ i, ∑ j, x.2 i * y.2 j * B (vecE F n i) (vecE F n j) := by
    conv_lhs => rw [s8_V_eq_sum F n x, s8_V_eq_sum F n y]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, s8_sum_swap]
    ring
  -- `B` is alternating
  rw [hL, hR, s8_sum_skew F _ _ _ (fun i j => (hB.neg_eq _ _).symm),
    s8_sum_skew F _ _ _ (fun i j => (hB.neg_eq _ _).symm),
    s8_sum_cross F _ _ _ _ _ _ (fun i j => (hB.neg_eq _ _).symm)]
  ring

end Sharp

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- **The class `h = Ξ_P^♯ ∈ H²(X × X̂, ℚ)`** of the `2`-form `Ξ_P(x, y) = (f x, y)_V` (2.4.2) under
`V_ℚ ≅ V_ℚ*` (§1.3, §6.2, §8.3). It spans `H²(X × X̂, ℚ)^{Spin(V)_P}` and is ample for `P = P_Θ`
(`WeilClasses.Main.Intro`). -/
noncomputable def hClass (hW : IsCompl P.W₁ P.W₂) : ExtV ℚ n := formToExt2 ℚ n (P.XiQ hW)

/-- `⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`: `h` is the class of `Ξ_P`. -/
theorem hClass_spec (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing ℚ n y) (contractLeft (Q := 0) (pairing ℚ n x)
          (P.hClass hW))) = P.XiQ hW x y :=
  formToExt2_spec ℚ n (P.XiQ hW) (P.XiQ_isAlt hW) x y

/-- **`H²(X × X̂, ℚ)_P`** (§6.2): the sum of the non-trivial irreducible `Spin(V)_P`-subrepresentations
of `H²(X × X̂, ℚ) = ⋀² V_ℚ`, defined as the span of the vectors `ρ_g(x) - x`, `g ∈ Spin(V)_P` (the
integral group, `P.spinPZ`), `x ∈ ⋀² V_ℚ` (equivalent definition for the completely reducible
representation `⋀² V_ℚ`; see the module docstring). -/
noncomputable def H2P : Submodule ℚ (ExtV ℚ n) :=
  Submodule.span ℚ {y | ∃ g ∈ P.spinPZ, ∃ x ∈ ⋀[ℚ]^2 (V ℚ n), y = rhoExt ℚ n g x - x}

end KSecant

/-! ## Helpers (prefix `s8_`): a complex structure `J₀` for which `Θ` is ample

`ThetaStd = Σ e_{2i} ∧ e_{2i+1}` is ample for `J₀ e_{2i} = -e_{2i+1}`, `J₀ e_{2i+1} = e_{2i}` (the torus
`ℂⁿ/(ℤⁿ + iℤⁿ)`). The single copy of `J₀` in the library: statements that fix no complex structure on
`X` but use results stated under Assumption 2.4.1 for some complex structure (§8.3, the bridges of
`WeilClasses.Main.Compare`, Theorem 1.4.1(4) and the discriminant of `X × X̂` in the model, the
instances of `WeilClasses.Main.Instances`) take `J₀`. -/

section S8J0

variable (n : ℕ)

/-- The involution `2i ↔ 2i + 1` of `Fin (2n)`. -/
def s8_swap (k : Fin (2 * n)) : Fin (2 * n) :=
  ⟨if k.val % 2 = 0 then k.val + 1 else k.val - 1, by split_ifs <;> omega⟩

/-- The sign `+1` on even, `-1` on odd indices. -/
def s8_sgn (k : Fin (2 * n)) : ℝ := if k.val % 2 = 0 then 1 else -1

theorem s8_swap_swap (k : Fin (2 * n)) : s8_swap n (s8_swap n k) = k := by
  ext; simp only [s8_swap]; split_ifs <;> omega

theorem s8_sgn_swap (k : Fin (2 * n)) : s8_sgn n (s8_swap n k) = -s8_sgn n k := by
  simp only [s8_sgn, s8_swap]; split_ifs <;> (try norm_num) <;> omega

theorem s8_swap_even (i : Fin n) : s8_swap n ⟨2 * i, by omega⟩ = ⟨2 * i + 1, by omega⟩ := by
  ext; simp [s8_swap]

theorem s8_swap_odd (i : Fin n) : s8_swap n ⟨2 * i + 1, by omega⟩ = ⟨2 * i, by omega⟩ := by
  ext; simp only [s8_swap]; split_ifs <;> omega

theorem s8_sgn_even (i : Fin n) : s8_sgn n ⟨2 * i, by omega⟩ = 1 := by
  simp [s8_sgn]

theorem s8_sgn_odd (i : Fin n) : s8_sgn n ⟨2 * i + 1, by omega⟩ = -1 := by
  simp only [s8_sgn]; split_ifs <;> first | rfl | omega

theorem s8_swap_eq_iff (k j : Fin (2 * n)) : s8_swap n k = j ↔ k = s8_swap n j := by
  constructor
  · rintro rfl; rw [s8_swap_swap]
  · rintro rfl; rw [s8_swap_swap]

/-- The matrix of the standard complex structure `J₀`. -/
noncomputable def s8_M0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun k j => if j = s8_swap n k then s8_sgn n k else 0

/-- A complex structure `J₀` of `H¹(X, ℝ) = ℝ^{2n}` for which `Θ = ThetaStd` is ample:
`J₀ e_{2i} = -e_{2i+1}`, `J₀ e_{2i+1} = e_{2i}` (the torus `ℂⁿ/(ℤⁿ + iℤⁿ)`). -/
noncomputable def s8_J0 : Module.End ℝ (H1 ℝ n) := Matrix.toLin' (s8_M0 n)

theorem s8_J0_apply (x : H1 ℝ n) (k : Fin (2 * n)) :
    s8_J0 n x k = s8_sgn n k * x (s8_swap n k) := by
  simp [s8_J0, s8_M0, Matrix.mulVec, dotProduct]

/-- `J₀² = -1`. -/
theorem s8_J0_isComplex : IsComplexStructure (s8_J0 n) := by
  refine LinearMap.ext fun x => funext fun k => ?_
  simp only [Module.End.mul_apply, s8_J0_apply, s8_swap_swap, s8_sgn_swap]
  simp only [LinearMap.neg_apply, Module.End.one_apply, Pi.neg_apply]
  have : s8_sgn n k * s8_sgn n k = 1 := by
    simp only [s8_sgn]; split_ifs <;> norm_num
  linear_combination (-(x k)) * this

theorem s8_complexify_J0_apply (v : H1 ℂ n) (k : Fin (2 * n)) :
    complexifyH1 n (s8_J0 n) v k = (s8_sgn n k : ℂ) * v (s8_swap n k) := by
  simp only [complexifyH1, s8_J0, LinearMap.toMatrix_eq_toMatrix', Matrix.toLin_eq_toLin',
    LinearMap.toMatrix'_toLin', Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    s8_M0]
  simp [apply_ite (fun r : ℝ => (r : ℂ)), ite_mul, Finset.sum_ite_eq']

theorem s8_J0_e_even (i : Fin n) :
    s8_J0 n (e ℝ n ⟨2 * i, by omega⟩) = -e ℝ n ⟨2 * i + 1, by omega⟩ := by
  funext k
  rw [s8_J0_apply]
  simp only [e, Pi.single_apply, s8_swap_eq_iff, s8_swap_even, Pi.neg_apply]
  split_ifs with h
  · subst h; rw [s8_sgn_odd]; ring
  · ring

theorem s8_J0_e_odd (i : Fin n) :
    s8_J0 n (e ℝ n ⟨2 * i + 1, by omega⟩) = e ℝ n ⟨2 * i, by omega⟩ := by
  funext k
  rw [s8_J0_apply]
  simp only [e, Pi.single_apply, s8_swap_eq_iff, s8_swap_odd]
  split_ifs with h
  · subst h; rw [s8_sgn_even]; ring
  · ring

/-- `e_{2i} + i e_{2i+1} ∈ H^{1,0}` for `J₀`. -/
theorem s8_mem_H10_J0 (i : Fin n) :
    e ℂ n ⟨2 * i, by omega⟩ + Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩ ∈ H10 n (s8_J0 n) := by
  rw [H10, Module.End.mem_eigenspace_iff]
  funext k
  rw [s8_complexify_J0_apply]
  simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, s8_swap_eq_iff,
    s8_swap_even, s8_swap_odd]
  by_cases h1 : k = ⟨2 * i, by omega⟩
  · subst h1
    have : (⟨2 * i, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by simp
    simp [s8_sgn_even, this]
  · by_cases h2 : k = ⟨2 * i + 1, by omega⟩
    · subst h2
      simp [s8_sgn_odd, h1]
    · simp [h1, h2]

/-- `e_{2i} - i e_{2i+1} ∈ H^{0,1}` for `J₀`. -/
theorem s8_mem_H01_J0 (i : Fin n) :
    e ℂ n ⟨2 * i, by omega⟩ - Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩ ∈ H01 n (s8_J0 n) := by
  rw [H01, Module.End.mem_eigenspace_iff]
  funext k
  rw [s8_complexify_J0_apply]
  simp only [e, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, s8_swap_eq_iff,
    s8_swap_even, s8_swap_odd]
  by_cases h1 : k = ⟨2 * i, by omega⟩
  · subst h1
    have : (⟨2 * i, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * i + 1, by omega⟩ := by simp
    simp [s8_sgn_even, this]
  · by_cases h2 : k = ⟨2 * i + 1, by omega⟩
    · subst h2
      simp [s8_sgn_odd, h1]
    · simp [h1, h2]

theorem s8_eval2_ι_mul_ι (a b : Module.Dual ℝ (H1 ℝ n)) (x y : H1 ℝ n) :
    eval2 ℝ n (ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y) a b = a x * b y - a y * b x := by
  have h := s8_algebraMapInv_contractLeft_contractLeft_ι_mul_ι a b x y
  have hD : D ℝ n b (D ℝ n a (ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y)) =
      algebraMap ℝ (S ℝ n) (a x * b y - a y * b x) := by
    rw [← h]
    exact s8_eq_algebraMap_of_mem_zero (s8_contractLeft_mem _ (s8_contractLeft_mem _
      (s8_ι_mul_ι_mem x y)))
  rw [eval2, hD, Algebra.algebraMap_eq_smul_one, map_smul, ← s8_basisS_empty,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- `Θ = ThetaStd` is ample for `J₀`. -/
theorem s8_ample_J0 : IsAmple n (s8_J0 n) (ThetaStd ℚ n) := by
  refine ⟨(mem_hodgeClassesX_iff n _ 1 _).mpr ⟨s8_ThetaStd_mem ℚ n, ?_⟩, fun a ha => ?_⟩
  · rw [s8_bcS_ThetaStd]
    refine Submodule.sum_mem _ fun i _ => ?_
    set v := e ℂ n ⟨2 * i, by omega⟩ + Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩
    set w := e ℂ n ⟨2 * i, by omega⟩ - Complex.I • e ℂ n ⟨2 * i + 1, by omega⟩
    have key : ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) *
        ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩) =
        (Complex.I / 2) • (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) := by
      have hc : ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩) *
          ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) =
          -(ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i, by omega⟩) *
            ExteriorAlgebra.ι ℂ (e ℂ n ⟨2 * i + 1, by omega⟩)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      simp only [v, w, map_add, map_sub, map_smul, add_mul, mul_sub,
        smul_mul_assoc, mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, hc]
      match_scalars
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨![v], ![w], ?_, ?_, ?_⟩)
    · intro j; fin_cases j; exact s8_mem_H10_J0 n i
    · intro j; fin_cases j; exact s8_mem_H01_J0 n i
    · simp [ExteriorAlgebra.ιMulti_apply]
  · have hsum : eval2 ℝ n (ThetaStd ℝ n) a (a ∘ₗ s8_J0 n) =
        ∑ i : Fin n, ((a (e ℝ n ⟨2 * i, by omega⟩)) ^ 2 +
          (a (e ℝ n ⟨2 * i + 1, by omega⟩)) ^ 2) := by
      have hlin : ∀ ξ : S ℝ n, eval2 ℝ n ξ a (a ∘ₗ s8_J0 n) =
          ((basisS ℝ n).coord ∅ ∘ₗ D ℝ n (a ∘ₗ s8_J0 n) ∘ₗ D ℝ n a) ξ := fun ξ => rfl
      rw [hlin, ThetaStd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlin, s8_eval2_ι_mul_ι]
      simp only [LinearMap.comp_apply, s8_J0_e_even, s8_J0_e_odd, map_neg]
      ring
    rw [s8_bcS_ThetaStd, hsum]
    obtain ⟨k, hk⟩ : ∃ k, a (e ℝ n k) ≠ 0 := by
      by_contra! h
      exact ha ((Pi.basisFun ℝ (Fin (2 * n))).ext fun k => by simpa [e] using h k)
    refine Finset.sum_pos' (fun i _ => by positivity)
      ⟨⟨k.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one k.val with h | h
    · have hk' : k = ⟨2 * (k.val / 2), by omega⟩ := Fin.ext (by simp; omega)
      rw [← hk']
      have := sq_pos_of_ne_zero hk
      positivity
    · have hk' : k = ⟨2 * (k.val / 2) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [← hk']
      have := sq_pos_of_ne_zero hk
      positivity

end S8J0

/-! ## The classes of §8.2 (`n = 3`) -/

section Jacobian

variable (d : ℚ)

/-- `α = 1 - (d/2) Θ² ∈ H^{ev}(X, ℚ)` (§8.2), `Θ = ThetaStd ℚ 3`: `exp(√-d Θ) = α + √-d β`. -/
noncomputable def alphaJac : S ℚ 3 := 1 - (d / 2) • ThetaStd ℚ 3 ^ 2

/-- `β = Θ - d [pt] ∈ H^{ev}(X, ℚ)` (§8.2), `Θ = ThetaStd ℚ 3`. -/
noncomputable def betaJac : S ℚ 3 := ThetaStd ℚ 3 - d • pt ℚ 3

/-- **`κ₃(E)`** (Theorem 1.4.1(4)): the summand in `H⁶(X × X̂, ℚ)` of `κ(E) = exp(-c₁(E)/r) ch(E)`. -/
noncomputable def kappa3E : ExtV ℚ 3 := kappaDeg ℚ 3 3 (chE d)

/-- The oriented `K`-secant `P_Θ` of §2.4 for `Θ = ThetaStd ℚ 3` ample for a complex structure `J`
of `H¹(X, ℝ)` (§8.2–8.3: `P = span{α, β}`, the secant through `exp(±√-d Θ)`). -/
noncomputable abbrev PJac {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    KSecant 3 d :=
  PTheta 3 d hd (ThetaStd ℚ 3) hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos (by norm_num))

/-- `V_K = W₁ ⊕ W₂` for `P_Θ` (§2.4: `θ` is an isomorphism). -/
theorem PJac_isCompl {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    IsCompl (PJac d hΘ hd).W₁ (PJac d hΘ hd).W₂ :=
  PTheta_isCompl 3 d hd _ _ _ hΘ.bijective_thetaMap

end Jacobian

end WeilClasses
