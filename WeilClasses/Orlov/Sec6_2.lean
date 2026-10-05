module

public import WeilClasses.Secant.Defs
public import WeilClasses.Orlov.Sec6_1
public import WeilClasses.PureSpinor.Lemma2_2_7
public import WeilClasses.Hermitian.ComplexStructures
public import WeilClasses.Correspondence.Sec5_2
public import WeilClasses.PeriodDomain.SemiHodge

/-!
# §6.2: Objects in `Dᵇ(X × X̂)` with `Spin(V)_P`-invariant Chern classes

Statements of the paper's §6.2 (TeX lines 2349–2659), in the model where `H*(X × X̂, ℚ) = ⋀• V_ℚ`
and the Chern character of `Φ(F₂ ⊠ F₁^∨)` is the class `φ(w₂ ⊗ τ w₁)` (`secantSqClass ℚ n w₂ w₁`)
of the Chern characters `wᵢ = ch(Fᵢ)` (see `WeilClasses.Secant.Defs`).

* The decomposition `H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P + ℚ Ξ_P` (`KSecant.exteriorPower_two_eq`) and
  `H²_P ∩ H²^{Spin(V)_P} = 0` (`KSecant.H2P_inf_invQ`), with `H²_P = KSecant.H2P` and `Ξ_P` regarded
  as the class `KSecant.hClass ∈ ⋀² V_ℚ`.
* **Lemma 6.2.3** (`lemma6_2_3`, `lemma6_2_3_unique` (`ℓ` does not depend on the `Fᵢ`)) with
  **(6.2.4)** (`equation6_2_4_exists`, as printed; `equation6_2_4`, for the class `c₁(N_g)` of
  (6.1.8)) and the claims of its proof (`lemma6_2_3_rhoPrime_invariant`, `lemma6_2_3_lowest`,
  `lemma6_2_3_injective`, `s62_coset_inv` (TeX lines 2462–2464), `lemma6_2_3_c1N`).
* **Remark 6.2.4** (`remark6_2_4`, `remark6_2_4_ell`).
* **Lemma 6.2.5** (`lemma6_2_5`: Proposition 6.1.2 for abelian surfaces) with **(6.2.5)**
  (`equation6_2_5`) and the claim of its proof that `ℓ` is the `H²_P`-component of `-c₁(𝒫)/2`
  (`ell_eq_proj_c1P`, in the model for every `n`).
* **Lemma 6.2.6** (`lemma6_2_6_1`, `lemma6_2_6_2`).

## Setting and readings

* §6.2 fixes a `K`-secant `P` satisfying Assumption 2.4.1 (`Assumption2_4_1 P J`) and objects
  `F₁, F₂` with `ch(Fᵢ) = wᵢ ∈ P` "such that the `2`-form `Ξ_P` in Corollary 3.2.3 is ample". In the
  model "`Ξ_P` is ample" is the hypothesis of Corollary 3.2.3 for the complex structure
  `I = I_{V_ℝ}` (`productStructure n J`) of `X × X̂`: `g_I(x, x) = Ξ_P(x, I x) > 0` for `x ≠ 0`
  (`hample`), which is the Kähler condition for `Ξ_P` (Corollary 3.2.3, `corollary3_2_3_kahler`).
* `Spin(V)_P` is the integral group of (2.2.2) (`P.spinPZ`), acting on `⋀• V_ℚ` by `ρ`
  (`rhoExt`) or `ρ'` (`rhoPrime`, (6.1.4)); `Spin(V)_P`-invariance by `ρ` is membership in
  `invariantsExt ℚ n P.spinPZ`.
* "of type `(1,1)`" refers to the complex structure of `X × X̂` (`hodgeClassesV n I 1`; Hodge classes
  are the same for `I_{V_ℝ}` and the standard structure `-I_{V_ℝ}`).
* `k` is "the minimal non-negative integer such that `ch_k(Φ(F₂ ⊠ F₁^∨)) ≠ 0`", i.e. the least `j`
  with `projDeg (2j) β ≠ 0` (`IsLeast`).
* `Ξ_P` is `Spin(V)_P`-invariant because `ρ(Spin(V_ℚ)_P)` commutes with `f` (Lemma 2.2.4, TeX lines
  862 and 1240; `s62_rhoExt_hClass`).

## Departures

In the proof of Lemma 6.2.3 (reason 2; see its docstring): the complete reducibility of the
representation of the arithmetic group `Spin(V)_P` on `H^{2k+2}` (TeX lines 2462–2464) is replaced
by a `Spin(V)_P`-invariant pairing nondegenerate on `β_k ∪ H²` (`s62_coset_inv`), as the
decomposition `H² = H²_P + ℚ Ξ_P` uses an invariant pairing of `H²`
(`KSecant.exteriorPower_two_eq`); hard Lefschetz for `Ξ_P` is replaced by the algebraic Lefschetz
property of the nondegenerate `2`-form `Ξ_P` (`lemma6_2_3_injective`). The `(1,1)`-type of `ℓ`,
which the paper does not prove, is obtained from Proposition 6.1.2 (gap filled). Lemma 6.2.5 and
(6.2.5) are the case `n = 2` of Proposition 6.1.2 (authorized departure, `notes/design.md`).

## Left out (sheaf-theoretic)

Lemma 6.2.1 (the isomorphism `Φ(F₂ ⊠ F₁^∨) ≅ Rπ_{23,*}(π₁^*F₁^∨ ⊗ 𝓕₂)[n]`), the sheaves (6.2.1),
the morphism `ι_F` (6.2.2) and the moduli discussion before it, Definition 6.2.2 (secant`^{⊠2}`-objects;
their classes are `secantSqClass`), the line bundles `N_g` themselves (only `c₁(N_g)` appears), and in
the proof of Lemma 6.2.5 the Chern character of `Rπ_{23,*}(π₁^*F₁^∨ ⊗ 𝓕₂)` for ideal sheaves of points
([Markman, generalized Kummers, Prop. 11.2]) and the Zariski-density argument ([Verbitsky, Th. 2.1]);
Lemma 6.2.5 is proved instead from Proposition 6.1.2 (authorized departure, `notes/design.md`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prefix `s62_`): the grading of `⋀• V`, `exp` of classes of degree `2`, `ρ_g`

Generic facts about `H*(X × X̂, F) = ⋀• V_F` used in the proofs of §6.2 and §6.4: the projections
`projDeg k` to the graded pieces, the exponential of a class of degree `2` (central and nilpotent),
and the grading-preserving action `ρ_g = ⋀• ρ(g)`. -/

section Helpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `ρ_g` preserves the degree: it maps `⋀^k V` into `⋀^k V`. -/
theorem s62_rhoExt_mem (g : Spin F n) {k : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^k (V F n)) :
    rhoExt F n g x ∈ ⋀[F]^k (V F n) := by
  have h := (exteriorPower.map k (rho F n g : V F n →ₗ[F] V F n) ⟨x, hx⟩).2
  rwa [exteriorPower.coe_map] at h

omit [CharZero F] in
theorem s62_projDeg_mem (k : ℕ) (x : ExtV F n) : projDeg F n k x ∈ ⋀[F]^k (V F n) := by
  simp only [projDeg, GradedAlgebra.proj_apply]
  exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x k).2

omit [CharZero F] in
theorem s62_projDeg_of_mem {i : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^i (V F n)) (k : ℕ) :
    projDeg F n k x = if i = k then x else 0 := by
  simp only [projDeg, GradedAlgebra.proj_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx h

omit [CharZero F] in
theorem s62_projDeg_self {i : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^i (V F n)) :
    projDeg F n i x = x := by
  rw [s62_projDeg_of_mem F n hx, ite_eq_left rfl]

omit [CharZero F] in
theorem s62_projDeg_ne {i k : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^i (V F n)) (h : i ≠ k) :
    projDeg F n k x = 0 := by
  rw [s62_projDeg_of_mem F n hx, ite_eq_right h]

omit [CharZero F] in
theorem s62_projDeg_mul_left {i : ℕ} {a : ExtV F n} (ha : a ∈ ⋀[F]^i (V F n)) (y : ExtV F n)
    (m : ℕ) :
    projDeg F n m (a * y) = if i ≤ m then a * projDeg F n (m - i) y else 0 := by
  simp only [projDeg, GradedAlgebra.proj_apply]
  exact DirectSum.coe_decompose_mul_of_left_mem _ m ha

omit [CharZero F] in
theorem s62_pow_mem {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (j : ℕ) :
    c ^ j ∈ ⋀[F]^(2 * j) (V F n) := by
  have := SetLike.pow_mem_graded (A := fun i : ℕ => ⋀[F]^i (V F n)) j hc
  simpa [smul_eq_mul, mul_comm] using this

omit [CharZero F] in
theorem s62_finrank_V : Module.finrank F (V F n) = 4 * n := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_fin_fun]; ring

omit [CharZero F] in
theorem s62_exteriorPower_eq_bot {k : ℕ} (hk : 4 * n < k) : ⋀[F]^k (V F n) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [exteriorPower.finrank_eq, s62_finrank_V]
  exact Nat.choose_eq_zero_of_lt hk

omit [CharZero F] in
theorem s62_pow_eq_zero {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) {j : ℕ} (hj : 2 * n < j) :
    c ^ j = 0 := by
  have h := s62_pow_mem F n hc j
  rw [s62_exteriorPower_eq_bot F n (by omega)] at h
  exact (Submodule.mem_bot F).mp h

omit [CharZero F] in
theorem s62_isNilpotent {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) : IsNilpotent c :=
  ⟨2 * n + 1, s62_pow_eq_zero F n hc (by omega)⟩

theorem s62_exp_eq_sum {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp c = ∑ j ∈ Finset.range (2 * n + 3), (j.factorial : ℚ)⁻¹ • c ^ j :=
  IsNilpotent.exp_eq_sum (s62_pow_eq_zero F n hc (by omega))

/-- The graded components of `exp(c) x` for `c ∈ ⋀² V`, below the lowest degree of `x`: if
`x_{2j} = 0` for `j < k`, then `(exp(c) x)_{2k} = x_{2k}` and
`(exp(c) x)_{2k+2} = x_{2k+2} + c x_{2k}`. -/
theorem s62_projDeg_exp_mul {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) (x : ExtV F n) (k : ℕ)
    (hx : ∀ j < k, projDeg F n (2 * j) x = 0) :
    projDeg F n (2 * k) (IsNilpotent.exp c * x) = projDeg F n (2 * k) x ∧
      projDeg F n (2 * k + 2) (IsNilpotent.exp c * x) =
        projDeg F n (2 * k + 2) x + c * projDeg F n (2 * k) x := by
  rw [s62_exp_eq_sum F n hc, Finset.sum_mul]
  simp only [smul_mul_assoc, map_sum, map_rat_smul]
  constructor
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [s62_projDeg_mul_left F n (s62_pow_mem F n hc j)]
      split_ifs with h
      · rw [show 2 * k - 2 * j = 2 * (k - j) by omega, hx (k - j) (by omega), mul_zero, smul_zero]
      · rw [smul_zero]
    · intro h; simp at h
  · rw [Finset.sum_eq_add 0 1 (by omega)]
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, one_smul,
        Nat.factorial_one, pow_one]
      rw [s62_projDeg_mul_left F n hc, ite_eq_left (by omega), show 2 * k + 2 - 2 = 2 * k by omega]
    · intro j _ hj
      rw [s62_projDeg_mul_left F n (s62_pow_mem F n hc j)]
      split_ifs with h
      · rw [show 2 * k + 2 - 2 * j = 2 * (k + 1 - j) by omega, hx (k + 1 - j) (by omega),
          mul_zero, smul_zero]
      · rw [smul_zero]
    · intro h; simp at h
    · intro h; simp at h


omit [CharZero F] in
/-- Elements of `⋀² V` are central in `⋀• V`. -/
theorem s62_commute_of_mem_two {a : ExtV F n} (ha : a ∈ ⋀[F]^2 (V F n)) (x : ExtV F n) :
    Commute a x := by
  have hι : ∀ w : V F n, Commute a (ExteriorAlgebra.ι F w) := by
    intro w
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      have := ExteriorAlgebra.ι_mul_ιMulti_anticomm F w v
      simp only [show ((-1 : ℤˣ) ^ 2) = 1 by norm_num, one_smul] at this
      exact this.symm
    | zero => exact Commute.zero_left _
    | add y z _ _ hy hz => exact hy.add_left hz
    | smul c y _ hy => exact hy.smul_left c
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r a |>.symm
  | ι w => exact hι w
  | mul y z hy hz => exact hy.mul_right hz
  | add y z hy hz => exact hy.add_right hz

/-- `exp(a + b) = exp(a) exp(b)` for `a, b ∈ ⋀² V`. -/
theorem s62_exp_add {a b : ExtV F n} (ha : a ∈ ⋀[F]^2 (V F n)) (hb : b ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp (a + b) = IsNilpotent.exp a * IsNilpotent.exp b :=
  IsNilpotent.exp_add_of_commute (s62_commute_of_mem_two F n ha b) (s62_isNilpotent F n ha)
    (s62_isNilpotent F n hb)

theorem s62_exp_neg_mul {a : ExtV F n} (ha : a ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp (-a) * IsNilpotent.exp a = 1 := by
  rw [← s62_exp_add F n (neg_mem ha) ha, neg_add_cancel, IsNilpotent.exp_zero]

theorem s62_exp_mul_neg {a : ExtV F n} (ha : a ∈ ⋀[F]^2 (V F n)) :
    IsNilpotent.exp a * IsNilpotent.exp (-a) = 1 := by
  rw [← s62_exp_add F n ha (neg_mem ha), add_neg_cancel, IsNilpotent.exp_zero]

omit [CharZero F] in
/-- A map preserving the degrees commutes with the projections to the graded pieces. -/
theorem s62_projDeg_comm {F' : Type*} [Field F'] [CharZero F'] (φ : ExtV F n →+ ExtV F' n)
    (hφ : ∀ i x, x ∈ ⋀[F]^i (V F n) → φ x ∈ ⋀[F']^i (V F' n)) (k : ℕ) (x : ExtV F n) :
    projDeg F' n k (φ x) = φ (projDeg F n k x) := by
  induction x using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[F]^i (V F n)) with
  | zero => simp
  | homogeneous y =>
    obtain ⟨y, hy⟩ := y
    rw [s62_projDeg_of_mem F' n (hφ _ y hy), s62_projDeg_of_mem F n hy]
    split_ifs <;> simp
  | add y z hy hz => simp only [map_add, hy, hz]

theorem s62_projDeg_rhoExt (g : Spin F n) (k : ℕ) (x : ExtV F n) :
    projDeg F n k (rhoExt F n g x) = rhoExt F n g (projDeg F n k x) :=
  s62_projDeg_comm F n (rhoExt F n g).toRingHom.toAddMonoidHom
    (fun _ _ hx => s62_rhoExt_mem F n g hx) k x

theorem s62_rhoExt_exp (g : Spin F n) {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    rhoExt F n g (IsNilpotent.exp c) = IsNilpotent.exp (rhoExt F n g c) :=
  IsNilpotent.map_exp (s62_isNilpotent F n hc) (rhoExt F n g)

omit [CharZero F] in
/-- The rank (degree-`0` coefficient) vanishes in positive degrees. -/
theorem s62_rankExt_of_mem_succ {i : ℕ} {y : ExtV F n} (hy : y ∈ ⋀[F]^(i + 1) (V F n)) :
    rankExt F n y = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [rankExt, ExteriorAlgebra.algebraMapInv]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

omit [CharZero F] in
theorem s62_projDeg_zero (x : ExtV F n) :
    projDeg F n 0 x = algebraMap F (ExtV F n) (rankExt F n x) := by
  induction x using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[F]^i (V F n)) with
  | zero => simp
  | @homogeneous i y =>
    obtain ⟨y, hy⟩ := y
    rw [s62_projDeg_of_mem F n hy]
    split_ifs with h
    · subst h
      obtain ⟨r, rfl⟩ : ∃ r, algebraMap F (ExtV F n) r = y := by
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
        have h1 : Set.range (ExteriorAlgebra.ιMulti F 0 : (Fin 0 → V F n) → ExtV F n) = {1} := by
          ext z; simp [ExteriorAlgebra.ιMulti_zero_apply, eq_comm]
        rw [h1, Submodule.mem_span_singleton] at hy
        obtain ⟨r, rfl⟩ := hy
        exact ⟨r, Algebra.algebraMap_eq_smul_one r⟩
      simp [rankExt]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp [s62_rankExt_of_mem_succ F n hy]
  | add y z hy hz => simp only [map_add, hy, hz]


theorem s62_rankExt_rhoExt (g : Spin F n) (x : ExtV F n) :
    rankExt F n (rhoExt F n g x) = rankExt F n x := by
  have : (rankExt F n).comp (rhoExt F n g) = rankExt F n :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by
      simp [rankExt, rhoExt, ExteriorAlgebra.algebraMapInv])
  exact congrArg (fun φ : ExtV F n →ₐ[F] F => φ x) this

omit [CharZero F] in
theorem s62_ι_mul_ι_mem (a b : V F n) :
    ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b ∈ ⋀[F]^2 (V F n) := by
  have h1 : ∀ v : V F n, ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (V F n) := fun v => by
    rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ v
  exact SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[F]^i (V F n)) (h1 a) (h1 b)

omit [CharZero F] in
theorem s62_c1P_mem : c1P F n ∈ ⋀[F]^2 (V F n) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  simp only [pullX, pullXHat, ExteriorAlgebra.map_apply_ι]
  exact s62_ι_mul_ι_mem F n _ _

theorem s62_rankExt_exp {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    rankExt F n (IsNilpotent.exp c) = 1 := by
  rw [IsNilpotent.map_exp (s62_isNilpotent F n hc) (rankExt F n)]
  rw [show rankExt F n c = 0 from s62_rankExt_of_mem_succ F n (i := 1) hc, IsNilpotent.exp_zero]

theorem s62_projDeg_two_exp {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    projDeg F n 2 (IsNilpotent.exp c) = c := by
  have h := (s62_projDeg_exp_mul F n hc 1 0 (fun j hj => absurd hj (Nat.not_lt_zero _))).2
  rw [mul_one] at h
  rw [h, s62_projDeg_zero, s62_projDeg_ne F n (i := 0) (by simp) (by norm_num), zero_add]
  simp [rankExt]

omit [CharZero F] in
theorem s62_projDeg_two_mem (x : ExtV F n) : projDeg F n 2 x ∈ ⋀[F]^2 (V F n) :=
  s62_projDeg_mem F n 2 x

/-- `ρ'_g x = x` iff `ρ_g (exp(-c₁(𝒫)/2) x) = exp(-c₁(𝒫)/2) x` (Proposition 6.1.2). -/
theorem s62_rhoPrime_fixed_iff (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x = x ↔
      rhoExt F n g (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x) =
        IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x := by
  have hc := s62_c1P_mem F n
  have hc' : (2 : F)⁻¹ • c1P F n ∈ ⋀[F]^2 (V F n) := Submodule.smul_mem _ _ hc
  have hρc : (2 : F)⁻¹ • rhoExt F n g (c1P F n) ∈ ⋀[F]^2 (V F n) :=
    Submodule.smul_mem _ _ (s62_rhoExt_mem F n g hc)
  rw [proposition6_1_2, map_mul, s62_rhoExt_exp F n g (neg_mem hc'), map_neg, map_smul]
  have hsplit : (2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n)) =
      (2 : F)⁻¹ • c1P F n + -((2 : F)⁻¹ • rhoExt F n g (c1P F n)) := by
    rw [smul_sub, sub_eq_add_neg]
  rw [hsplit, s62_exp_add F n hc' (neg_mem hρc), mul_assoc]
  constructor
  · intro h
    conv_rhs => rw [← h]
    rw [← mul_assoc, s62_exp_neg_mul F n hc', one_mul]
  · intro h
    rw [h, ← mul_assoc, s62_exp_mul_neg F n hc', one_mul]

omit [CharZero F] in
/-- Contraction is natural for the maps of exterior algebras. -/
theorem s62_contractLeft_map (A : V F n →ₗ[F] V F n) (φ : Module.Dual F (V F n))
    (ξ : ExtV F n) :
    contractLeft (Q := 0) φ (ExteriorAlgebra.map A ξ) =
      ExteriorAlgebra.map A (contractLeft (Q := 0) (φ ∘ₗ A) ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, contractLeft_algebraMap, contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    have h1 : ExteriorAlgebra.map A (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) m) =
        CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) (A m) := ExteriorAlgebra.map_apply_ι A m
    rw [map_mul, h1, contractLeft_ι_mul, contractLeft_ι_mul, hx, map_sub, map_smul, map_mul, h1,
      LinearMap.comp_apply]

omit [CharZero F] in
theorem s62_algebraMapInv_map (A : V F n →ₗ[F] V F n) (ξ : ExtV F n) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map A ξ) = ExteriorAlgebra.algebraMapInv ξ := by
  have : (ExteriorAlgebra.algebraMapInv : ExtV F n →ₐ[F] F).comp (ExteriorAlgebra.map A) =
      ExteriorAlgebra.algebraMapInv :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp [ExteriorAlgebra.algebraMapInv])
  exact congrArg (fun φ : ExtV F n →ₐ[F] F => φ ξ) this

theorem s62_rho_pairing (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  have heq : ((spinToOrthogonal (Q F n) g : TauCeti.QuadraticMap.orthogonalGroup (Q F n)) :
      V F n ≃ₗ[F] V F n) = rho F n g :=
    LinearEquiv.ext fun v => coe_spinToOrthogonal_apply _ _ _
  have hmem : (rho F n g) ∈ TauCeti.QuadraticMap.orthogonalGroup (Q F n) :=
    heq ▸ (spinToOrthogonal (Q F n) g).2
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmem x y


omit [CharZero F] in
theorem s62_pairing_apply (x y : V F n) : pairing F n x y = x.1 y.2 + y.1 x.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticForm.dualProd_apply,
    Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
  ring

omit [CharZero F] in
theorem s62_pairing_injective : Function.Injective (pairing F n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : ∀ w : H1 F n, x.1 w = 0 := fun w => by
    have := LinearMap.congr_fun hx (0, w); simpa [s62_pairing_apply] using this
  have h2 : ∀ θ : Module.Dual F (H1 F n), θ x.2 = 0 := fun θ => by
    have := LinearMap.congr_fun hx (θ, 0); simpa [s62_pairing_apply] using this
  exact Prod.ext (LinearMap.ext h1) ((Module.forall_dual_apply_eq_zero_iff F x.2).mp h2)

omit [CharZero F] in
theorem s62_pairing_surjective (φ : Module.Dual F (V F n)) : ∃ x, pairing F n x = φ := by
  have hfr : Module.finrank F (V F n) = Module.finrank F (Module.Dual F (V F n)) :=
    (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp
    (s62_pairing_injective F n) φ

/-- `⟪ρ_g ξ, (x,·)∧(y,·)⟫ = ⟪ξ, (ρ_g⁻¹x,·)∧(ρ_g⁻¹y,·)⟫`. -/
theorem s62_eval_rhoExt (g : Spin F n) (ξ : ExtV F n) (x y : V F n) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) (rhoExt F n g ξ))) =
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n ((rho F n g).symm y))
      (contractLeft (Q := 0) (pairing F n ((rho F n g).symm x)) ξ)) := by
  have hcomp : ∀ z : V F n, (pairing F n z) ∘ₗ (rho F n g : V F n →ₗ[F] V F n) =
      pairing F n ((rho F n g).symm z) := by
    intro z; refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← (rho F n g).apply_symm_apply z]
    exact s62_rho_pairing F n g _ v
  simp only [rhoExt]
  rw [s62_contractLeft_map, hcomp, s62_contractLeft_map, hcomp, s62_algebraMapInv_map]

omit [CharZero F] in
/-- The pairing of `ξ ∈ ⋀² V` with two functionals is Mathlib's `pairingDual`. -/
theorem s62_eval_eq_pairingDual (φ₁ φ₂ : Module.Dual F (V F n)) (ξ : ⋀[F]^2 (V F n)) :
    ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) φ₂ (contractLeft (Q := 0) φ₁
      (ξ : ExtV F n))) =
    exteriorPower.pairingDual F (V F n) 2 (exteriorPower.ιMulti F 2 ![φ₁, φ₂]) ξ := by
  let L : ⋀[F]^2 (V F n) →ₗ[F] F :=
    (ExteriorAlgebra.algebraMapInv : ExtV F n →ₐ[F] F).toLinearMap ∘ₗ
      contractLeft (Q := 0) φ₂ ∘ₗ contractLeft (Q := 0) φ₁ ∘ₗ (⋀[F]^2 (V F n)).subtype
  have : L = exteriorPower.pairingDual F (V F n) 2 (exteriorPower.ιMulti F 2 ![φ₁, φ₂]) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [L, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, exteriorPower.pairingDual_ιMulti_ιMulti]
    rw [ExteriorAlgebra.ιMulti_apply]
    simp [List.ofFn_succ, contractLeft_ι_mul, contractLeft_ι, Matrix.det_fin_two,
      ExteriorAlgebra.algebraMapInv]
  exact LinearMap.congr_fun this ξ


omit [CharZero F] in
/-- A class of degree `2` is determined by its pairings `⟪ξ, (x,·)∧(y,·)⟫`. -/
theorem s62_eq_zero_of_eval {ξ : ExtV F n} (hξ : ξ ∈ ⋀[F]^2 (V F n))
    (h : ∀ x y : V F n, ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
      (contractLeft (Q := 0) (pairing F n x) ξ)) = 0) : ξ = 0 := by
  have h1 : ∀ φ₁ φ₂ : Module.Dual F (V F n),
      exteriorPower.pairingDual F (V F n) 2 (exteriorPower.ιMulti F 2 ![φ₁, φ₂]) ⟨ξ, hξ⟩ = 0 := by
    intro φ₁ φ₂
    obtain ⟨x, rfl⟩ := s62_pairing_surjective F n φ₁
    obtain ⟨y, rfl⟩ := s62_pairing_surjective F n φ₂
    rw [← s62_eval_eq_pairingDual]; exact h x y
  have h2 : ∀ ω : ⋀[F]^2 (Module.Dual F (V F n)),
      exteriorPower.pairingDual F (V F n) 2 ω ⟨ξ, hξ⟩ = 0 := by
    intro ω
    have hω : ω ∈ Submodule.span F (Set.range (exteriorPower.ιMulti F 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hω using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      rw [hv]; exact h1 _ _
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have h3 : ∀ ℓ : Module.Dual F (⋀[F]^2 (V F n)), ℓ ⟨ξ, hξ⟩ = 0 := by
    intro ℓ
    obtain ⟨ω, rfl⟩ := (exteriorPower.bijective_pairingDual F (V F n) (n := 2)).2 ℓ
    exact h2 ω
  have := (Module.forall_dual_apply_eq_zero_iff F (⟨ξ, hξ⟩ : ⋀[F]^2 (V F n))).mp h3
  simpa using congrArg Subtype.val this

theorem s62_rho_symm_pairing (g : Spin F n) (x y : V F n) :
    pairing F n ((rho F n g).symm x) ((rho F n g).symm y) = pairing F n x y := by
  conv_rhs => rw [← (rho F n g).apply_symm_apply x, ← (rho F n g).apply_symm_apply y]
  exact (s62_rho_pairing F n g _ _).symm

/-! ### The `sl₂`-triple of a nondegenerate class of degree `2` (Lefschetz) -/

omit [CharZero F] in
theorem s62_ι_mem_one (v : V F n) : ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (V F n) := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ v

omit [CharZero F] in
theorem s62_algebraMap_mem_zero (r : F) : algebraMap F (ExtV F n) r ∈ ⋀[F]^0 (V F n) := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero]
  exact Submodule.mem_one.mpr ⟨r, rfl⟩

omit [CharZero F] in
/-- Contraction lowers the degree by one. -/
theorem s62_contractLeft_mem (φ : Module.Dual F (V F n)) {k : ℕ} {x : ExtV F n}
    (hx : x ∈ ⋀[F]^(k + 1) (V F n)) : contractLeft (Q := 0) φ x ∈ ⋀[F]^k (V F n) := by
  induction k generalizing x with
  | zero =>
    rw [ExteriorAlgebra.exteriorPower, pow_one] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [contractLeft_ι]; exact s62_algebraMap_mem_zero F n _
  | succ k ih =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul]
      have h1 : ExteriorAlgebra.ιMulti F (k + 1) (Matrix.vecTail v) ∈ ⋀[F]^(k + 1) (V F n) :=
        ExteriorAlgebra.ιMulti_range F (k + 1) ⟨_, rfl⟩
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ h1) ?_
      have := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[F]^i (V F n))
        (s62_ι_mem_one F n (v 0)) (ih h1)
      simpa [add_comm] using this
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

omit [CharZero F] in
theorem s62_contractLeft_ι_mul (φ : Module.Dual F (V F n)) (a : V F n) (y : ExtV F n) :
    contractLeft (Q := 0) φ (ExteriorAlgebra.ι F a * y) =
      φ a • y - ExteriorAlgebra.ι F a * contractLeft (Q := 0) φ y :=
  contractLeft_ι_mul (Q := (0 : QuadraticForm F (V F n))) φ a y

omit [CharZero F] in
theorem s62_contractLeft_ι (φ : Module.Dual F (V F n)) (a : V F n) :
    contractLeft (Q := 0) φ (ExteriorAlgebra.ι F a) = algebraMap F (ExtV F n) (φ a) :=
  contractLeft_ι (Q := (0 : QuadraticForm F (V F n))) φ a

omit [CharZero F] in
theorem s62_contractLeft_ι_mul_ι_mul (φ : Module.Dual F (V F n)) (a b : V F n) (y : ExtV F n) :
    contractLeft (Q := 0) φ (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b * y) =
      contractLeft (Q := 0) φ (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) * y +
        ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b * contractLeft (Q := 0) φ y := by
  have e5 : ExteriorAlgebra.ι F a * algebraMap F (ExtV F n) (φ b) =
      φ b • ExteriorAlgebra.ι F a := by
    rw [← Algebra.commutes, ← Algebra.smul_def]
  rw [mul_assoc (ExteriorAlgebra.ι F a), s62_contractLeft_ι_mul, s62_contractLeft_ι_mul,
    s62_contractLeft_ι_mul, s62_contractLeft_ι, e5]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  abel

omit [CharZero F] in
/-- Contraction is a derivation with respect to multiplication by a class of degree `2`. -/
theorem s62_contractLeft_mul_two (φ : Module.Dual F (V F n)) {ω : ExtV F n}
    (hω : ω ∈ ⋀[F]^2 (V F n)) (y : ExtV F n) :
    contractLeft (Q := 0) φ (ω * y) =
      contractLeft (Q := 0) φ ω * y + ω * contractLeft (Q := 0) φ y := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hω
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    have hv : ExteriorAlgebra.ιMulti F 2 v = ExteriorAlgebra.ι F (v 0) * ExteriorAlgebra.ι F (v 1) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [hv]
    exact s62_contractLeft_ι_mul_ι_mul F n φ (v 0) (v 1) y
  | zero => simp
  | add a b _ _ ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | smul c a _ ha => simp only [smul_mul_assoc, map_smul, ha, smul_add]

/-- The Euler identity: if `Σ_j α_j(u) a_j = c u` for all `u`, then
`Σ_j a_j ∧ (α_j ⌋ y) = c p y` on `⋀^p V`. -/
theorem s62_euler {J : Type*} [Fintype J] (a : J → V F n) (α : J → Module.Dual F (V F n))
    (c : F) (hac : ∀ u, ∑ j, α j u • a j = c • u) {p : ℕ} {y : ExtV F n}
    (hy : y ∈ ⋀[F]^p (V F n)) :
    ∑ j, ExteriorAlgebra.ι F (a j) * contractLeft (Q := 0) (α j) y = (c * p) • y := by
  induction p generalizing y with
  | zero =>
    rw [ExteriorAlgebra.exteriorPower, pow_zero] at hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
    simp [contractLeft_algebraMap]
  | succ p ih =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have h1 : ExteriorAlgebra.ιMulti F p (Matrix.vecTail v) ∈ ⋀[F]^p (V F n) :=
        ExteriorAlgebra.ιMulti_range F p ⟨_, rfl⟩
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [contractLeft_ι_mul, mul_sub, mul_smul_comm]
      rw [Finset.sum_sub_distrib]
      have h2 : ∀ j, ExteriorAlgebra.ι F (a j) * (ExteriorAlgebra.ι F (v 0) *
          contractLeft (Q := 0) (α j) (ExteriorAlgebra.ιMulti F p (Matrix.vecTail v))) =
          -(ExteriorAlgebra.ι F (v 0) * (ExteriorAlgebra.ι F (a j) *
          contractLeft (Q := 0) (α j) (ExteriorAlgebra.ιMulti F p (Matrix.vecTail v)))) := by
        intro j
        rw [← mul_assoc, ← mul_assoc, ← neg_mul]
        congr 1
        exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      have h3 : ∑ j, α j (v 0) • (ExteriorAlgebra.ι F (a j) *
          ExteriorAlgebra.ιMulti F p (Matrix.vecTail v)) =
          c • (ExteriorAlgebra.ι F (v 0) * ExteriorAlgebra.ιMulti F p (Matrix.vecTail v)) := by
        simp only [← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum, hac]
      rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_neg_distrib, ← Finset.mul_sum, ih h1,
        h3, mul_smul_comm, sub_neg_eq_add, ← add_smul]
      congr 1
      push_cast; ring
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, mul_add, Finset.sum_add_distrib, hy, hz, smul_add]
    | smul r y _ hy => simp only [map_smul, mul_smul_comm, ← Finset.smul_sum, hy, smul_comm r]


omit [CharZero F] in
/-- The commutator relation `[Λ, L_ω] = (2p - 4n)` on `⋀^p V`, iterated:
`Λ(ω^{m+1} y) = ω^{m+1} Λ(y) + (m+1)(2p + 2m - 4n) ω^m y`. -/
theorem s62_sl2_pow (Λ : ExtV F n →ₗ[F] ExtV F n) {ω : ExtV F n} (hω : ω ∈ ⋀[F]^2 (V F n))
    (hΛ : ∀ (p : ℕ) (y : ExtV F n), y ∈ ⋀[F]^p (V F n) →
      Λ (ω * y) = ω * Λ y + (2 * (p : F) - 4 * n) • y)
    {p : ℕ} {y : ExtV F n} (hy : y ∈ ⋀[F]^p (V F n)) (m : ℕ) :
    Λ (ω ^ (m + 1) * y) =
      ω ^ (m + 1) * Λ y + (((m : F) + 1) * (2 * p + 2 * m - 4 * n)) • (ω ^ m * y) := by
  induction m with
  | zero =>
    rw [zero_add, pow_one, hΛ p y hy, pow_zero, one_mul]
    congr 2; push_cast; ring
  | succ m ih =>
    have hmem : ω ^ (m + 1) * y ∈ ⋀[F]^(p + 2 * (m + 1)) (V F n) := by
      have := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[F]^i (V F n))
        (s62_pow_mem F n hω (m + 1)) hy
      rwa [add_comm] at this
    rw [pow_succ' ω (m + 1), mul_assoc, hΛ _ _ hmem, ih, mul_add, ← mul_assoc, ← pow_succ',
      mul_smul_comm, ← mul_assoc, ← pow_succ', add_assoc, ← add_smul]
    congr 2
    push_cast; ring

omit [CharZero F] in
theorem s62_one_mem_zero : (1 : ExtV F n) ∈ ⋀[F]^0 (V F n) := by
  have := s62_algebraMap_mem_zero F n 1; rwa [map_one] at this

/-- `ω^j ≠ 0` for `j ≤ 2n` (from the `sl₂`-relation and `Λ(1) = 0`). -/
theorem s62_sl2_pow_ne_zero (Λ : ExtV F n →ₗ[F] ExtV F n) {ω : ExtV F n}
    (hω : ω ∈ ⋀[F]^2 (V F n))
    (hΛ : ∀ (p : ℕ) (y : ExtV F n), y ∈ ⋀[F]^p (V F n) →
      Λ (ω * y) = ω * Λ y + (2 * (p : F) - 4 * n) • y)
    (hΛ1 : Λ 1 = 0) {j : ℕ} (hj : j ≤ 2 * n) : ω ^ j ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    intro h0
    have h1 := s62_sl2_pow F n Λ hω hΛ (s62_one_mem_zero F n) j
    rw [mul_one, h0, map_zero, hΛ1, mul_zero, zero_add, mul_one] at h1
    have hcoef : ((j : F) + 1) * (2 * ((0 : ℕ) : F) + 2 * j - 4 * n) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero j) ?_
      rw [Nat.cast_zero, mul_zero, zero_add, sub_ne_zero]
      exact_mod_cast (by omega : 2 * j ≠ 4 * n)
    exact ih (by omega) ((smul_eq_zero.mp h1.symm).resolve_left hcoef)

/-- Lefschetz: `ω^k ∪ (•) : ⋀² V → ⋀^{2k+2} V` is injective for `k + 2 ≤ 2n`. -/
theorem s62_sl2_injective (Λ : ExtV F n →ₗ[F] ExtV F n) {ω : ExtV F n}
    (hω : ω ∈ ⋀[F]^2 (V F n))
    (hΛ : ∀ (p : ℕ) (y : ExtV F n), y ∈ ⋀[F]^p (V F n) →
      Λ (ω * y) = ω * Λ y + (2 * (p : F) - 4 * n) • y)
    (hΛ1 : Λ 1 = 0) (hΛ2 : ∀ x ∈ ⋀[F]^2 (V F n), ∃ c : F, Λ x = algebraMap F (ExtV F n) c)
    (k : ℕ) (hk : k + 2 ≤ 2 * n) {x : ExtV F n} (hx : x ∈ ⋀[F]^2 (V F n))
    (h0 : ω ^ k * x = 0) : x = 0 := by
  induction k with
  | zero => simp only [pow_zero, one_mul] at h0; exact h0
  | succ k ih =>
    apply ih (by omega)
    have h1 := s62_sl2_pow F n Λ hω hΛ hx k
    obtain ⟨c, hc⟩ := hΛ2 x hx
    rw [h0, map_zero, hc, ← Algebra.commutes, ← Algebra.smul_def] at h1
    -- `0 = c ω^{k+1} + (k+1)(2k + 4 - 4n) ω^k x`; multiply by `ω`
    have h2 := congrArg (fun z => ω * z) h1
    simp only [mul_zero, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ'] at h2
    rw [h0, smul_zero, add_zero] at h2
    have hc0 : c = 0 := (smul_eq_zero.mp h2.symm).resolve_right
      (s62_sl2_pow_ne_zero F n Λ hω hΛ hΛ1 (by omega))
    rw [hc0, zero_smul, zero_add] at h1
    have hcoef : ((k : F) + 1) * (2 * ((2 : ℕ) : F) + 2 * k - 4 * n) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) ?_
      rw [sub_ne_zero]
      exact_mod_cast (by omega : 2 * 2 + 2 * k ≠ 4 * n)
    exact (smul_eq_zero.mp h1.symm).resolve_left hcoef

omit [CharZero F] in
theorem s62_pairing_vecF (i : Fin (2 * n)) (u : V F n) : pairing F n (vecF F n i) u = u.2 i := by
  rw [s62_pairing_apply]; simp [vecF, f]

omit [CharZero F] in
theorem s62_pairing_vecE (i : Fin (2 * n)) (u : V F n) :
    pairing F n (vecE F n i) u = u.1 (e F n i) := by
  rw [s62_pairing_apply]; simp [vecE]

omit [CharZero F] in
theorem s62_dual_expand (u : V F n) :
    ∑ i, u.2 i • vecE F n i + ∑ i, u.1 (e F n i) • vecF F n i = u := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, vecE, vecF, smul_zero,
      Finset.sum_const_zero, zero_add]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    conv_rhs => rw [pi_eq_sum_univ w, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    congr 2
    funext j; simp [e, Pi.single_apply, eq_comm]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, vecE, vecF, smul_zero,
      Finset.sum_const_zero, add_zero]
    conv_rhs => rw [pi_eq_sum_univ u.2]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    funext j; simp [e, Pi.single_apply, eq_comm]

omit [CharZero F] in
theorem s62_dual_expand₁ (u : V F n) :
    ∑ j : Fin (2 * n) ⊕ Fin (2 * n), pairing F n (Sum.elim (vecF F n) (vecE F n) j) u •
      Sum.elim (vecE F n) (vecF F n) j = u := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, s62_pairing_vecF, s62_pairing_vecE]
  exact s62_dual_expand F n u

omit [CharZero F] in
theorem s62_dual_expand₂ (u : V F n) :
    ∑ j : Fin (2 * n) ⊕ Fin (2 * n), pairing F n (Sum.elim (vecE F n) (vecF F n) j) u •
      Sum.elim (vecF F n) (vecE F n) j = u := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, s62_pairing_vecF, s62_pairing_vecE]
  rw [add_comm]
  exact s62_dual_expand F n u

omit [CharZero F] in
theorem s62_dual_diag (j : Fin (2 * n) ⊕ Fin (2 * n)) :
    pairing F n (Sum.elim (vecE F n) (vecF F n) j) (Sum.elim (vecF F n) (vecE F n) j) = 1 := by
  rcases j with i | i
  · rw [Sum.elim_inl, Sum.elim_inl, s62_pairing_vecE]; simp [vecF, f, e]
  · rw [Sum.elim_inr, Sum.elim_inr, s62_pairing_vecF]; simp [vecE, e]

omit [CharZero F] in
theorem s62_combine {M : Type*} [AddCommGroup M] [Module F M] (c₁ c₂ c₃ c : F) (y S : M)
    (h : c₁ - c₂ + c₃ = c) : c₁ • y - c₂ • y + (c₃ • y + S) = S + c • y := by
  rw [← h, add_smul, sub_smul]; abel

/-- The operator `Λ = Σ_j ι_{ψ_j} ι_{φ_j}` of the `sl₂`-triple of a class `ω ∈ ⋀² V` with
`ι_{(x,·)} ω = A x` (contraction with the bivector dual to `ω`), for the dual bases
`(f_i, e_i)` and `(e_i, f_i)` of `V`: `φ_j = (a_j, ·)_V`, `ψ_j = (b_j, ·)_V`,
`b_j = -c⁻¹ A(a'_j)`. -/
noncomputable def s62_lam (A : V F n →ₗ[F] V F n) (c : F) : Module.End F (ExtV F n) :=
  ∑ j : Fin (2 * n) ⊕ Fin (2 * n),
    contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (Sum.elim (vecE F n) (vecF F n) j))) ∘ₗ
      contractLeft (Q := 0) (pairing F n (Sum.elim (vecF F n) (vecE F n) j))

omit [CharZero F] in
theorem s62_lam_apply (A : V F n →ₗ[F] V F n) (c : F) (y : ExtV F n) :
    s62_lam F n A c y = ∑ j : Fin (2 * n) ⊕ Fin (2 * n),
      contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (Sum.elim (vecE F n) (vecF F n) j)))
        (contractLeft (Q := 0) (pairing F n (Sum.elim (vecF F n) (vecE F n) j)) y) := by
  simp [s62_lam, LinearMap.sum_apply]

omit [CharZero F] in
theorem s62_lam_one (A : V F n →ₗ[F] V F n) (c : F) : s62_lam F n A c 1 = 0 := by
  rw [s62_lam_apply]
  simp [contractLeft_one]

omit [CharZero F] in
theorem s62_lam_two (A : V F n →ₗ[F] V F n) (c : F) (x : ExtV F n) (hx : x ∈ ⋀[F]^2 (V F n)) :
    ∃ r : F, s62_lam F n A c x = algebraMap F (ExtV F n) r := by
  have hmem : s62_lam F n A c x ∈ ⋀[F]^0 (V F n) := by
    rw [s62_lam_apply]
    exact Submodule.sum_mem _ fun j _ =>
      s62_contractLeft_mem F n _ (s62_contractLeft_mem F n (k := 1) _ hx)
  rw [ExteriorAlgebra.exteriorPower, pow_zero] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hmem
  exact ⟨r, hr.symm⟩

/-- The `sl₂`-relation `[Λ, L_ω] = 2p - 4n` on `⋀^p V`. -/
theorem s62_lam_spec {ω : ExtV F n} (hω : ω ∈ ⋀[F]^2 (V F n)) (A : V F n →ₗ[F] V F n) (c : F)
    (hc : c ≠ 0)
    (hωA : ∀ x, contractLeft (Q := 0) (pairing F n x) ω = ExteriorAlgebra.ι F (A x))
    (hAA : ∀ x, A (A x) = -(c • x))
    (hskew : ∀ x y, pairing F n (A x) y = -pairing F n x (A y))
    (p : ℕ) (y : ExtV F n) (hy : y ∈ ⋀[F]^p (V F n)) :
    s62_lam F n A c (ω * y) = ω * s62_lam F n A c y + (2 * (p : F) - 4 * n) • y := by
  rw [s62_lam_apply, s62_lam_apply]
  set a := Sum.elim (vecF F n) (vecE F n)
  set a' := Sum.elim (vecE F n) (vecF F n)
  -- `ψ_j(u) = c⁻¹ (a'_j, A u)`
  have hψ : ∀ j u, pairing F n (-(c⁻¹) • A (a' j)) u = c⁻¹ * pairing F n (a' j) (A u) := by
    intro j u
    rw [map_smul, LinearMap.smul_apply, hskew, smul_eq_mul]; ring
  have hd₁ : ∀ u, ∑ j, pairing F n (a j) u • a' j = u := s62_dual_expand₁ F n
  have hd₂ : ∀ u, ∑ j, pairing F n (a' j) u • a j = u := s62_dual_expand₂ F n
  have hdiag : ∀ j, pairing F n (a' j) (a j) = 1 := s62_dual_diag F n
  -- `A b_j = a'_j`
  have hAb : ∀ j, A (-(c⁻¹) • A (a' j)) = a' j := by
    intro j
    rw [map_smul, hAA, smul_neg, smul_smul, show -c⁻¹ * c = -1 by field_simp, neg_one_smul,
      neg_neg]
  -- Euler identities
  have he1 : ∀ u, ∑ j, pairing F n (-(c⁻¹) • A (a' j)) u • A (a j) = (-1 : F) • u := by
    intro u
    calc ∑ j, pairing F n (-(c⁻¹) • A (a' j)) u • A (a j)
        = c⁻¹ • A (∑ j, pairing F n (a' j) (A u) • a j) := by
          rw [map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hψ, map_smul, smul_smul]
      _ = (-1 : F) • u := by
          rw [hd₂, hAA, smul_neg, smul_smul, inv_mul_cancel₀ hc, one_smul, neg_one_smul]
  have he2 : ∀ u, ∑ j, pairing F n (a j) u • A (-(c⁻¹) • A (a' j)) = (1 : F) • u := by
    intro u
    rw [Finset.sum_congr rfl fun j _ => by rw [hAb j], hd₁ u, one_smul]
  have hconst : ∑ j, pairing F n (-(c⁻¹) • A (a' j)) (A (a j)) = -(4 * n : F) := by
    have hj : ∀ j, pairing F n (-(c⁻¹) • A (a' j)) (A (a j)) = -1 := by
      intro j
      rw [hψ, hAA, map_neg, map_smul, smul_eq_mul, hdiag j]; field_simp
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hterm : ∀ j, contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (a' j)))
      (contractLeft (Q := 0) (pairing F n (a j)) (ω * y)) =
      pairing F n (-(c⁻¹) • A (a' j)) (A (a j)) • y -
        ExteriorAlgebra.ι F (A (a j)) * contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (a' j))) y +
      (ExteriorAlgebra.ι F (A (-(c⁻¹) • A (a' j))) *
        contractLeft (Q := 0) (pairing F n (a j)) y +
        ω * contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (a' j)))
          (contractLeft (Q := 0) (pairing F n (a j)) y)) := by
    intro j
    rw [s62_contractLeft_mul_two F n _ hω, hωA, map_add, s62_contractLeft_ι_mul,
      s62_contractLeft_mul_two F n _ hω, hωA]
  have h1 : ∑ j, pairing F n (-(c⁻¹) • A (a' j)) (A (a j)) • y = (-(4 * (n : F))) • y := by
    rw [← Finset.sum_smul, hconst]
  have h2 := s62_euler F n _ _ _ he1 hy
  have h3 := s62_euler F n _ _ _ he2 hy
  have h4 : ∑ j, ω * contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (a' j)))
      (contractLeft (Q := 0) (pairing F n (a j)) y) =
      ω * ∑ j, contractLeft (Q := 0) (pairing F n (-(c⁻¹) • A (a' j)))
        (contractLeft (Q := 0) (pairing F n (a j)) y) := (Finset.mul_sum _ _ _).symm
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (2 * n) ⊕ Fin (2 * n)))) rfl
    fun j (_ : j ∈ Finset.univ) => hterm j
  refine hsum.trans ?_
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
  exact s62_combine F (-(4 * (n : F))) ((-1 : F) * p) ((1 : F) * p) (2 * (p : F) - 4 * n) y _
    (by ring)

omit [CharZero F] in
theorem s62_pairing_comm (x y : V F n) : pairing F n x y = pairing F n y x := by
  rw [s62_pairing_apply, s62_pairing_apply, add_comm]

/-! ### The invariant pairing of `⋀² V` and the codimension of `H²_P` -/

/-- The pairing of `⋀² V` induced by `(·,·)_V` (determinant pairing `⟨x₁ ∧ x₂, y₁ ∧ y₂⟩ =
det((xᵢ, yⱼ)_V)`). -/
noncomputable def s62_B2 : LinearMap.BilinForm F (⋀[F]^2 (V F n)) :=
  (exteriorPower.pairingDual F (V F n) 2).comp (exteriorPower.map 2 (pairing F n))

omit [CharZero F] in
theorem s62_B2_ιMulti (v w : Fin 2 → V F n) :
    s62_B2 F n (exteriorPower.ιMulti F 2 v) (exteriorPower.ιMulti F 2 w) =
      (Matrix.of fun i j => pairing F n (v j) (w i)).det := by
  simp [s62_B2, exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]

/-- The pairing of `⋀² V` is `ρ(g)`-invariant. -/
theorem s62_B2_rho (g : Spin F n) (x y : ⋀[F]^2 (V F n)) :
    s62_B2 F n (exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) x)
      (exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) y) = s62_B2 F n x y := by
  have : (s62_B2 F n).compl₁₂ (exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n))
      (exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n)) = s62_B2 F n := by
    apply exteriorPower.linearMap_ext
    ext v w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
      exteriorPower.map_apply_ιMulti, s62_B2_ιMulti, Function.comp_apply, LinearEquiv.coe_coe,
      s62_rho_pairing]
  exact LinearMap.congr_fun (LinearMap.congr_fun this x) y

omit [CharZero F] in
theorem s62_B2_nondegenerate : (s62_B2 F n).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  have hB : Function.Bijective (pairing F n) :=
    ⟨s62_pairing_injective F n, fun φ => s62_pairing_surjective F n φ⟩
  have hbij : Function.Bijective (s62_B2 F n) :=
    (exteriorPower.bijective_pairingDual F (V F n) (n := 2)).comp
      ⟨exteriorPower.map_injective (LinearEquiv.ofBijective _ hB).symm
          (LinearMap.ext fun v => (LinearEquiv.ofBijective _ hB).symm_apply_apply v),
        exteriorPower.map_surjective hB.surjective⟩
  apply hbij.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem s62_rhoExt_inv (g : Spin F n) (z : ExtV F n) : rhoExt F n g (rhoExt F n g⁻¹ z) = z := by
  have h := LinearMap.congr_fun ((rhoRep F n).map_mul g g⁻¹) z
  rw [mul_inv_cancel, map_one] at h
  exact h.symm

/-- The span of the `ρ_g x - x` (`x ∈ ⋀² V`, `g ∈ G`) has codimension at most the dimension of the
`G`-invariants of `⋀² V` (it is their orthogonal for the invariant nondegenerate pairing). -/
theorem s62_finrank_le_span_add_inv (G : Subgroup (Spin F n)) :
    Module.finrank F (⋀[F]^2 (V F n)) ≤
      Module.finrank F (Submodule.span F
          {y | ∃ g ∈ G, ∃ x ∈ ⋀[F]^2 (V F n), y = rhoExt F n g x - x}) +
        Module.finrank F (⋀[F]^2 (V F n) ⊓ invariantsExt F n G : Submodule F (ExtV F n)) := by
  set M := ⋀[F]^2 (V F n)
  set H := Submodule.span F {y | ∃ g ∈ G, ∃ x ∈ M, y = rhoExt F n g x - x}
  have hHM : H ≤ M := Submodule.span_le.mpr (by
    rintro y ⟨g, -, x, hx, rfl⟩; exact Submodule.sub_mem _ (s62_rhoExt_mem F n g hx) hx)
  have hρ : ∀ (g : Spin F n) (x : M),
      ((exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) x : M) : ExtV F n) =
        rhoExt F n g x := fun g x => exteriorPower.coe_map _ _
  -- the orthogonal of `H` consists of invariants
  have horth : (s62_B2 F n).orthogonal (H.comap M.subtype) ≤ (M ⊓ invariantsExt F n G).comap M.subtype := by
    intro m hm
    refine ⟨m.2, fun g hg => ?_⟩
    have hm' : ∀ x : M, s62_B2 F n (exteriorPower.map 2 (rho F n g⁻¹ : V F n →ₗ[F] V F n) x) m = s62_B2 F n x m := by
      intro x
      have hmem : (exteriorPower.map 2 (rho F n g⁻¹ : V F n →ₗ[F] V F n) x - x : M) ∈
          H.comap M.subtype := by
        apply Submodule.subset_span
        refine ⟨g⁻¹, G.inv_mem hg, x, x.2, ?_⟩
        simp [hρ]
      have := hm _ hmem
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    -- `B(x, ρ_g m - m) = 0` for all `x`
    have h0 : ∀ x : M, s62_B2 F n x (exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) m - m) = 0 := by
      intro x
      have h1 := s62_B2_rho F n g (exteriorPower.map 2 (rho F n g⁻¹ : V F n →ₗ[F] V F n) x) m
      have hinv : exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n)
          (exteriorPower.map 2 (rho F n g⁻¹ : V F n →ₗ[F] V F n) x) = x := by
        apply Subtype.ext
        rw [hρ, hρ, s62_rhoExt_inv]
      rw [hinv] at h1
      rw [map_sub, h1, hm' x, sub_self]
    have := (s62_B2_nondegenerate F n).2 _ h0
    rw [sub_eq_zero] at this
    have := congrArg Subtype.val this
    rwa [hρ] at this
  have h1 := LinearMap.BilinForm.finrank_orthogonal (s62_B2_nondegenerate F n) (H.comap M.subtype)
  have h2 := Submodule.finrank_mono horth
  have h3 : Module.finrank F (H.comap M.subtype) = Module.finrank F H :=
    (Submodule.comapSubtypeEquivOfLe hHM).finrank_eq
  have h4 : Module.finrank F ((M ⊓ invariantsExt F n G).comap M.subtype) =
      Module.finrank F (M ⊓ invariantsExt F n G : Submodule F (ExtV F n)) :=
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  have h5 := Submodule.finrank_le (H.comap M.subtype)
  calc Module.finrank F M
      = Module.finrank F ((s62_B2 F n).orthogonal (H.comap M.subtype)) +
          Module.finrank F (H.comap M.subtype) := by rw [h1]; exact (Nat.sub_add_cancel h5).symm
    _ ≤ Module.finrank F ((M ⊓ invariantsExt F n G).comap M.subtype) +
          Module.finrank F (H.comap M.subtype) := Nat.add_le_add_right h2 _
    _ = _ := by rw [h3, h4, add_comm]

/-- `ρ_g` acts trivially on the top degree `⋀^{4n} V` if it fixes a nonzero class of degree `4n`. -/
theorem s62_rhoExt_top (g : Spin F n) {z₀ : ExtV F n}
    (hz₀ : z₀ ∈ ⋀[F]^(4 * n) (V F n)) (hz₀0 : z₀ ≠ 0) (hg : rhoExt F n g z₀ = z₀)
    {z : ExtV F n} (hz : z ∈ ⋀[F]^(4 * n) (V F n)) : rhoExt F n g z = z := by
  have hfr : Module.finrank F (⋀[F]^(4 * n) (V F n)) = 1 := by
    rw [exteriorPower.finrank_eq, s62_finrank_V, Nat.choose_self]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z₀, hz₀⟩ : ⋀[F]^(4 * n) (V F n))
    (by simpa using hz₀0)).mp hfr ⟨z, hz⟩
  have hc' : z = c • z₀ := by
    have := congrArg Subtype.val hc; simpa using this.symm
  rw [hc', map_smul, hg]

/-! ### Poincaré duality for `∫_{X̂ × X}` (moved here from `WeilClasses.Orlov.Sec6_4`) -/

omit [CharZero F] in
theorem s62_basisExt_mem (S : Finset (Fin (2 * n + 2 * n))) :
    basisExt F n S ∈ ⋀[F]^S.card (V F n) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard (b := basisV F n) (rfl : S.card = S.card)]
  exact ExteriorAlgebra.ιMulti_range F _ ⟨_, rfl⟩

omit [CharZero F] in
/-- `∫_{X̂ × X}` vanishes outside the top degree `4n`. -/
theorem s62_integralExt_projDeg (m : ℕ) (hm : m ≠ 4 * n) (x : ExtV F n) :
    integralExt F n (projDeg F n m x) = 0 := by
  have : (integralExt F n) ∘ₗ (projDeg F n m) = 0 := by
    refine (basisExt F n).ext fun S => ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, s62_projDeg_of_mem F n (s62_basisExt_mem F n S)]
    split_ifs with h
    · rw [integralExt, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right]
      rintro rfl
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    · rw [map_zero]
  exact LinearMap.congr_fun this x

omit [CharZero F] in
theorem s62_integralExt_of_mem {m : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^m (V F n)) (hm : m ≠ 4 * n) :
    integralExt F n z = 0 := by
  rw [← s62_projDeg_self F n hz]; exact s62_integralExt_projDeg F n m hm z

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` is injective (`φ_𝒫` and `ψ_{𝒫⁻¹[n]}` are mutually inverse). -/
theorem s62_PiMap_injective : Function.Injective (PiMap F n) := by
  have hinv : ∀ x, kunnethHatX F n (TensorProduct.map (psiPinvShift F n) (phiP F n)
      ((kunnethXHat F n).symm (PiMap F n x))) = x := by
    intro x
    have hP : PiMap F n x = kunnethXHat F n (TensorProduct.map (phiP F n) (psiPinvShift F n)
        ((kunnethHatX F n).symm x)) := rfl
    rw [hP, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
      ← TensorProduct.map_comp, psiPinvShift_comp_phiP, phiP_comp_psiPinvShift,
      TensorProduct.map_id, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  intro x y hxy
  rw [← hinv x, ← hinv y, hxy]

/-- Poincaré duality for `∫_{X̂ × X}`: a class `z ∈ ⋀^d V` with `∫ z ∧ y = 0` for all
`y ∈ ⋀^{4n-d} V` is `0`. By Lemma 6.3.2, `(Π₀ z, y) = ±∫ z ∧ y` for `Π₀ = φ_𝒫 ⊗ ψ_{𝒫⁻¹}`, the
pairing `( , )` is nondegenerate (`s61_extPairing_nondeg`) and `Π₀ = (-1)ⁿ Π` is injective. -/
theorem s62_eq_zero_of_integralExt_mul {d : ℕ} (hd : d ≤ 4 * n) {z : ExtV F n}
    (hz : z ∈ ⋀[F]^d (V F n))
    (h : ∀ y ∈ ⋀[F]^(4 * n - d) (V F n), integralExt F n (z * y) = 0) : z = 0 := by
  -- `∫ z ∧ y = 0` for every `y`: only the degree-`(4n - d)` part of `y` contributes
  have hall : ∀ y : ExtV F n, integralExt F n (z * y) = 0 := by
    intro y
    induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[F]^i (V F n)) with
    | zero => rw [mul_zero, map_zero]
    | @homogeneous j y =>
      obtain ⟨y, hy⟩ := y
      show integralExt F n (z * y) = 0
      by_cases hj : j = 4 * n - d
      · subst hj; exact h y hy
      · exact s62_integralExt_of_mem F n (SetLike.mul_mem_graded hz hy) (by omega)
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', add_zero]
  -- `(Π₀ z, y) = ±∫ z ∧ y = 0` for every `y` (Lemma 6.3.2), so `Π₀ z = 0`
  have h0 : PiMap0 F n z = 0 :=
    s61_extPairing_nondeg F n fun y => by rw [lemma6_3_2 F n d hz y, hall y, mul_zero]
  apply s62_PiMap_injective F n
  rw [s61_PiMap_eq_smul, LinearMap.smul_apply, h0, smul_zero, map_zero]

/-! ### The canonical element `Σᵢ eᵢ ∧ fᵢ` -/

/-- `x ↦ θ ↦ π_X^*x ∪ π_X̂^*θ`, bilinear. -/
noncomputable def s62_Φ : H1 F n →ₗ[F] Module.Dual F (H1 F n) →ₗ[F] ExtV F n :=
  (LinearMap.mul F (ExtV F n)).compl₁₂ ((ExteriorAlgebra.ι F).comp (LinearMap.inr F _ _))
    ((ExteriorAlgebra.ι F).comp (LinearMap.inl F _ _))

omit [CharZero F] in
theorem s62_Φ_apply (x : H1 F n) (θ : Module.Dual F (H1 F n)) :
    s62_Φ F n x θ = ExteriorAlgebra.ι F ((0 : Module.Dual F (H1 F n)), x) *
      ExteriorAlgebra.ι F (θ, (0 : H1 F n)) := rfl

omit [CharZero F] in
theorem s62_e_expand (w : H1 F n) : w = ∑ j, w j • e F n j := by
  simpa [e] using ((Pi.basisFun F (Fin (2 * n))).sum_repr w).symm

omit [CharZero F] in
/-- The canonical element `Σᵢ eᵢ ⊗ fᵢ`: `Σᵢ B(eᵢ) ∧ C(fᵢ) = Σᵢ eᵢ ∧ C(fᵢ ∘ B)`. -/
theorem s62_canonical (B : H1 F n →ₗ[F] H1 F n)
    (C : Module.Dual F (H1 F n) →ₗ[F] Module.Dual F (H1 F n)) :
    ∑ i, s62_Φ F n (B (e F n i)) (C (f F n i)) = ∑ i, s62_Φ F n (e F n i) (C (f F n i ∘ₗ B)) := by
  have hf : ∀ j, f F n j ∘ₗ B = ∑ i, B (e F n i) j • f F n i := fun j => by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    conv_lhs => rw [s62_e_expand F n w]
    simp only [map_sum, map_smul, LinearMap.smul_apply, f, LinearMap.proj_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  calc ∑ i, s62_Φ F n (B (e F n i)) (C (f F n i))
      = ∑ i, ∑ j, s62_Φ F n (e F n j) (C (B (e F n i) j • f F n i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [s62_e_expand F n (B (e F n i))]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply, map_smul, map_smul]
    _ = ∑ j, ∑ i, s62_Φ F n (e F n j) (C (B (e F n i) j • f F n i)) := Finset.sum_comm
    _ = ∑ j, s62_Φ F n (e F n j) (C (f F n j ∘ₗ B)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hf j, map_sum, map_sum]

end Helpers

/-! ## Helpers: change of coefficients -/

section BaseChangeHelpers

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s62_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) := by
  exact ExteriorAlgebra.lift_ι_apply F _ _ v

theorem s62_bcExt_mem {i : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^i (V F n)) :
    bcExt F F' n x ∈ ⋀[F']^i (V F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    have : (bcExt F F' n ∘ fun j => ExteriorAlgebra.ι F (v j)) =
        fun j => ExteriorAlgebra.ι F' (bcV F F' n (v j)) := by
      funext j; exact s62_bcExt_ι F F' n (v j)
    rw [this, ← ExteriorAlgebra.ιMulti_apply]
    exact ExteriorAlgebra.ιMulti_range F' i ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul, algebra_compatible_smul F' c]; exact Submodule.smul_mem _ _ hy

theorem s62_projDeg_bcExt (k : ℕ) (x : ExtV F n) :
    projDeg F' n k (bcExt F F' n x) = bcExt F F' n (projDeg F n k x) :=
  s62_projDeg_comm F n (bcExt F F' n).toRingHom.toAddMonoidHom
    (fun _ _ hx => s62_bcExt_mem F F' n hx) k x

theorem s62_rankExt_bcExt (x : ExtV F n) :
    rankExt F' n (bcExt F F' n x) = algebraMap F F' (rankExt F n x) := by
  have : ((rankExt F' n).restrictScalars F).comp (bcExt F F' n) =
      (Algebra.ofId F F').comp (rankExt F n) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by
      simp [rankExt, ExteriorAlgebra.algebraMapInv, s62_bcExt_ι])
  exact congrArg (fun φ : ExtV F n →ₐ[F] F' => φ x) this

theorem s62_bcExt_exp {c : ExtV F n} (hc : c ∈ ⋀[F]^2 (V F n)) :
    bcExt F F' n (IsNilpotent.exp c) = IsNilpotent.exp (bcExt F F' n c) :=
  IsNilpotent.map_exp (s62_isNilpotent F n hc) (bcExt F F' n)

omit [CharZero F] [CharZero F'] in
theorem s62_bcH1_e (i : Fin (2 * n)) : bcH1 F F' n (e F n i) = e F' n i := by
  funext j
  simp only [bcH1, LinearMap.compLeft_apply, Function.comp_apply, e, Pi.single_apply]
  split_ifs <;> simp

theorem s62_bcDual_f (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk, f, e, LinearMap.proj_apply, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

theorem s62_bcExt_c1P : bcExt F F' n (c1P F n) = c1P F' n := by
  simp only [c1P, map_sum, map_mul, pullX, pullXHat, ExteriorAlgebra.map_apply_ι, s62_bcExt_ι,
    bcV, LinearMap.prodMap_apply, LinearMap.inr_apply, LinearMap.inl_apply, map_zero,
    s62_bcH1_e, s62_bcDual_f]

theorem s62_bcExt_kappa (x : ExtV F n) :
    bcExt F F' n (kappa F n x) = kappa F' n (bcExt F F' n x) := by
  simp only [kappa]
  rw [map_mul, s62_bcExt_exp F F' n (Submodule.smul_mem _ _ (s62_projDeg_mem F n 2 x)),
    map_smul, s62_rankExt_bcExt, s62_projDeg_bcExt, algebra_compatible_smul F', map_neg,
    map_inv₀]

end BaseChangeHelpers

/-! ## Helpers: `m`, `ρ`, the pairing and contraction commute with change of coefficients -/

section BaseChangeHelpers2

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] [CharZero F'] in
theorem s62_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) :=
  ExteriorAlgebra.lift_ι_apply F _ _ w

omit [CharZero F] in
theorem s62_dualBasis_eq_f (i : Fin (2 * n)) : (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
  refine LinearMap.ext fun w => ?_
  rw [Module.Basis.dualBasis_apply, Pi.basisFun_repr]; rfl

theorem s62_mOf_apply (s : S F n) (v : V F n) :
    mOf F n s v = ExteriorAlgebra.ι F v.2 * s + D F n v.1 s := by
  simp only [mOf, LinearMap.comp_apply, AlgHom.toLinearMap_apply, m, CliffordAlgebra.lift_ι_apply,
    LinearMap.applyₗ_apply_apply, cliffordOp, L, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.mul_apply']

theorem s62_bcDual_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  show (∑ i, algebraMap F F' (θ (e F n i)) • f F' n i) (bcH1 F F' n w) = _
  rw [LinearMap.sum_apply]
  conv_rhs => rw [s62_e_expand F n w, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, f, LinearMap.proj_apply, smul_eq_mul, bcH1,
    LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_smul, map_mul]
  rw [mul_comm]

/-- Contraction commutes with change of coefficients on `S`. -/
theorem s62_D_bcS (θ : Module.Dual F (H1 F n)) (x : S F n) :
    D F' n (bcDual F F' n θ) (bcS F F' n x) = bcS F F' n (D F n θ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n)]
    simp only [D, contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x w hx =>
    have h1 : bcS F F' n (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w * x) =
        CliffordAlgebra.ι (0 : QuadraticForm F' (H1 F' n)) (bcH1 F F' n w) * bcS F F' n x := by
      rw [map_mul]; exact congrArg (· * bcS F F' n x) (s62_bcS_ι F F' n w)
    simp only [D] at hx ⊢
    rw [h1, contractLeft_ι_mul, contractLeft_ι_mul, hx, s62_bcDual_bcH1, map_sub, map_smul,
      map_mul, algebraMap_smul,
      show bcS F F' n (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w) =
        CliffordAlgebra.ι (0 : QuadraticForm F' (H1 F' n)) (bcH1 F F' n w) from s62_bcS_ι F F' n w]

theorem s62_bcC_ι (v : V F n) :
    bcC F F' n (CliffordAlgebra.ι (Q F n) v) = CliffordAlgebra.ι (Q F' n) (bcV F F' n v) :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- The spin representation commutes with change of coefficients. -/
theorem s62_m_bcC (x : C F n) (s : S F n) :
    m F' n (bcC F F' n x) (bcS F F' n s) = bcS F F' n (m F n x s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n), AlgHom.commutes,
      AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      algebraMap_smul]
  | ι v =>
    rw [s62_bcC_ι]
    change mOf F' n (bcS F F' n s) (bcV F F' n v) = bcS F F' n (mOf F n s v)
    rw [s62_mOf_apply, s62_mOf_apply, map_add, map_mul, s62_bcS_ι]
    simp only [bcV, LinearMap.prodMap_apply]
    rw [s62_D_bcS]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, hb, ha, map_mul (m F n), Module.End.mul_apply]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, ha, hb, map_add (m F n), LinearMap.add_apply,
      map_add]

theorem s62_bcC_involute (x : C F n) :
    bcC F F' n (CliffordAlgebra.involute x) = CliffordAlgebra.involute (bcC F F' n x) := by
  have : (bcC F F' n).comp CliffordAlgebra.involute =
      (CliffordAlgebra.involute.restrictScalars F).comp (bcC F F' n) :=
    CliffordAlgebra.hom_ext (LinearMap.ext fun v => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        CliffordAlgebra.involute_ι, map_neg, s62_bcC_ι, AlgHom.restrictScalars_apply])
  exact congrArg (fun φ : C F n →ₐ[F] C F' n => φ x) this

theorem s62_bcC_reverse (x : C F n) :
    bcC F F' n (CliffordAlgebra.reverse x) = CliffordAlgebra.reverse (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.reverse.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (C F' n), CliffordAlgebra.reverse.commutes]
  | ι v => rw [CliffordAlgebra.reverse_ι, s62_bcC_ι, CliffordAlgebra.reverse_ι]
  | mul a b ha hb =>
    rw [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb, map_mul, CliffordAlgebra.reverse.map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem s62_bcC_star (x : C F n) : bcC F F' n (star x) = star (bcC F F' n x) := by
  rw [CliffordAlgebra.star_def, CliffordAlgebra.star_def, s62_bcC_reverse, s62_bcC_involute]

/-- `ρ` commutes with change of coefficients. -/
theorem s62_rho_bcV (g : Spin F n) (v : V F n) :
    rho F' n (bcSpin F F' n g) (bcV F F' n v) = bcV F F' n (rho F n g v) := by
  apply CliffordAlgebra.ι_injective (Q F' n)
  calc CliffordAlgebra.ι (Q F' n) (rho F' n (bcSpin F F' n g) (bcV F F' n v))
      = bcC F F' n g * CliffordAlgebra.ι (Q F' n) (bcV F F' n v) * star (bcC F F' n g) :=
        ι_rho F' n (bcSpin F F' n g) (bcV F F' n v)
    _ = bcC F F' n (g * CliffordAlgebra.ι (Q F n) v * star (g : C F n)) := by
        rw [map_mul, map_mul, s62_bcC_ι, s62_bcC_star]
    _ = CliffordAlgebra.ι (Q F' n) (bcV F F' n (rho F n g v)) := by
        rw [← ι_rho, s62_bcC_ι]

theorem s62_rhoExt_bcExt (g : Spin F n) (x : ExtV F n) :
    rhoExt F' n (bcSpin F F' n g) (bcExt F F' n x) = bcExt F F' n (rhoExt F n g x) := by
  have : ((rhoExt F' n (bcSpin F F' n g)).restrictScalars F).comp (bcExt F F' n) =
      (bcExt F F' n).comp (rhoExt F n g) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.restrictScalars_apply, s62_bcExt_ι, rhoExt, ExteriorAlgebra.map_apply_ι,
        LinearEquiv.coe_coe, s62_rho_bcV])
  exact congrArg (fun φ : ExtV F n →ₐ[F] ExtV F' n => φ x) this

theorem s62_bcV_basisV (i : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n i) = basisV F' n i := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with a | a
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
      Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, bcV, LinearMap.prodMap_apply,
      map_zero, s62_dualBasis_eq_f, s62_bcDual_f]
  · simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
      Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, bcV, LinearMap.prodMap_apply,
      map_zero, Pi.basisFun_apply]
    exact congrArg _ (s62_bcH1_e F F' n a)

theorem s62_bcExt_basisExt (T : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n T) = basisExt F' n T := by
  rw [basisExt, basisExt, ExteriorAlgebra.basis_apply_ofCard (b := basisV F n) rfl,
    ExteriorAlgebra.basis_apply_ofCard (b := basisV F' n) rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply,
    map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  simp only [Function.comp_apply, s62_bcExt_ι, s62_bcV_basisV]

theorem s62_bcExt_eq_sum (x : ExtV F n) :
    bcExt F F' n x = ∑ T, algebraMap F F' ((basisExt F n).repr x T) • basisExt F' n T := by
  conv_lhs => rw [← (basisExt F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_smul, s62_bcExt_basisExt, algebraMap_smul]

theorem s62_repr_bcExt (x : ExtV F n) (T : Finset (Fin (2 * n + 2 * n))) :
    (basisExt F' n).repr (bcExt F F' n x) T = algebraMap F F' ((basisExt F n).repr x T) := by
  rw [s62_bcExt_eq_sum, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem s62_bcExt_injective : Function.Injective (bcExt F F' n) := by
  intro x y h
  apply (basisExt F n).repr.injective
  ext T
  have := congrArg (fun z => (basisExt F' n).repr z T) h
  simp only [s62_repr_bcExt] at this
  exact (algebraMap F F').injective this

/-- The pairing of `V` commutes with change of coefficients. -/
theorem s62_pairing_bcV (x y : V F n) :
    pairing F' n (bcV F F' n x) (bcV F F' n y) = algebraMap F F' (pairing F n x y) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add, Q_bcV, Q_bcV, Q_bcV, map_sub, map_sub]

/-- Contraction commutes with change of coefficients on `⋀• V`. -/
theorem s62_contractLeft_bcExt (x : V F n) (ξ : ExtV F n) :
    contractLeft (Q := 0) (pairing F' n (bcV F F' n x)) (bcExt F F' n ξ) =
      bcExt F F' n (contractLeft (Q := 0) (pairing F n x) ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExtV F' n), contractLeft_algebraMap,
      contractLeft_algebraMap, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | ι_mul ξ v hξ =>
    have h1 : bcExt F F' n (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) v * ξ) =
        CliffordAlgebra.ι (0 : QuadraticForm F' (V F' n)) (bcV F F' n v) * bcExt F F' n ξ := by
      rw [map_mul]; exact congrArg (· * bcExt F F' n ξ) (s62_bcExt_ι F F' n v)
    rw [h1, contractLeft_ι_mul, contractLeft_ι_mul, hξ, s62_pairing_bcV, map_sub, map_smul, map_mul,
      algebraMap_smul,
      show bcExt F F' n (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) v) =
        CliffordAlgebra.ι (0 : QuadraticForm F' (V F' n)) (bcV F F' n v) from s62_bcExt_ι F F' n v]

theorem s62_bcV_injective : Function.Injective (bcV F F' n) := by
  intro v w h
  apply (ExteriorAlgebra.ι_leftInverse (R := F) (M := V F n)).injective
  apply s62_bcExt_injective F F' n
  rw [s62_bcExt_ι, s62_bcExt_ι, h]

end BaseChangeHelpers2

/-! ## Helpers: the pairings `⟪ξ, (x,·) ∧ (y,·)⟫` -/

section EvalHelpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `⟪ξ, (x,·)_V ∧ (y,·)_V⟫ = ι_{(y,·)} ι_{(x,·)} ξ` (degree-`0` part). -/
noncomputable def s62_ev (ξ : ExtV F n) (x y : V F n) : F :=
  ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) (pairing F n y)
    (contractLeft (Q := 0) (pairing F n x) ξ))

omit [CharZero F] in
theorem s62_ev_add (ξ η : ExtV F n) (x y : V F n) :
    s62_ev F n (ξ + η) x y = s62_ev F n ξ x y + s62_ev F n η x y := by
  simp only [s62_ev, map_add]

omit [CharZero F] in
theorem s62_ev_smul (c : F) (ξ : ExtV F n) (x y : V F n) :
    s62_ev F n (c • ξ) x y = c * s62_ev F n ξ x y := by
  simp only [s62_ev, map_smul, smul_eq_mul]

omit [CharZero F] in
theorem s62_ev_add_left (ξ : ExtV F n) (x x' y : V F n) :
    s62_ev F n ξ (x + x') y = s62_ev F n ξ x y + s62_ev F n ξ x' y := by
  simp only [s62_ev, map_add, LinearMap.add_apply]

omit [CharZero F] in
theorem s62_ev_add_right (ξ : ExtV F n) (x y y' : V F n) :
    s62_ev F n ξ x (y + y') = s62_ev F n ξ x y + s62_ev F n ξ x y' := by
  simp only [s62_ev, map_add, LinearMap.add_apply]

omit [CharZero F] in
theorem s62_ev_ι_mul_ι (a b x y : V F n) :
    s62_ev F n (ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b) x y =
      pairing F n x a * pairing F n y b - pairing F n x b * pairing F n y a := by
  have e : ExteriorAlgebra.ι F a * algebraMap F (ExtV F n) (pairing F n x b) =
      pairing F n x b • ExteriorAlgebra.ι F a := by
    rw [← Algebra.commutes, ← Algebra.smul_def]
  simp only [s62_ev]
  rw [s62_contractLeft_ι_mul, s62_contractLeft_ι, e, map_sub, map_smul, map_smul,
    s62_contractLeft_ι, s62_contractLeft_ι]
  simp only [map_sub, map_smul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    smul_eq_mul]

omit [CharZero F] in
/-- `⟪ξ, (x,·) ∧ (y,·)⟫` vanishes on the span of the `a ∧ b` (`a ∈ U`, `b ∈ U'`) when it vanishes on
the generators. -/
theorem s62_ev_span (U U' : Submodule F (V F n)) {ξ : ExtV F n}
    (hξ : ξ ∈ Submodule.span F
      {z | ∃ a ∈ U, ∃ b ∈ U', z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b})
    (x y : V F n)
    (h : ∀ a ∈ U, ∀ b ∈ U',
      pairing F n x a * pairing F n y b - pairing F n x b * pairing F n y a = 0) :
    s62_ev F n ξ x y = 0 := by
  induction hξ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [s62_ev_ι_mul_ι]; exact h a ha b hb
  | zero => simp [s62_ev]
  | add a b _ _ ha hb => rw [s62_ev_add, ha, hb, add_zero]
  | smul c a _ ha => rw [s62_ev_smul, ha, mul_zero]

omit [CharZero F] in
theorem s62_span_ιι_le (U U' : Submodule F (V F n)) :
    Submodule.span F
        {z | ∃ a ∈ U, ∃ b ∈ U', z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b} ≤
      ⋀[F]^2 (V F n) :=
  Submodule.span_le.mpr (by rintro _ ⟨a, -, b, -, rfl⟩; exact s62_ι_mul_ι_mem F n a b)

omit [CharZero F] in
theorem s62_ιMulti_two (v : Fin 2 → V F n) :
    ExteriorAlgebra.ιMulti F 2 v = ExteriorAlgebra.ι F (v 0) * ExteriorAlgebra.ι F (v 1) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

omit [CharZero F] in
theorem s62_ιMulti_one (v : Fin 1 → V F n) :
    ExteriorAlgebra.ιMulti F 1 v = ExteriorAlgebra.ι F (v 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

omit [CharZero F] in
theorem s62_pqPiece_two_zero_le (A B : Submodule F (V F n)) :
    pqPiece A B 2 0 ≤ Submodule.span F
      {z | ∃ a ∈ A, ∃ b ∈ A, z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b} := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, ha, -, rfl⟩
  refine Submodule.subset_span ⟨a 0, ha 0, a 1, ha 1, ?_⟩
  rw [s62_ιMulti_two, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

omit [CharZero F] in
theorem s62_pqPiece_one_one_le (A B : Submodule F (V F n)) :
    pqPiece A B 1 1 ≤ Submodule.span F
      {z | ∃ a ∈ A, ∃ b ∈ B, z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b} := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact Submodule.subset_span ⟨a 0, ha 0, b 0, hb 0, by rw [s62_ιMulti_one, s62_ιMulti_one]⟩

omit [CharZero F] in
theorem s62_pqPiece_zero_two_le (A B : Submodule F (V F n)) :
    pqPiece A B 0 2 ≤ Submodule.span F
      {z | ∃ a ∈ B, ∃ b ∈ B, z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b} := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, -, hb, rfl⟩
  refine Submodule.subset_span ⟨b 0, hb 0, b 1, hb 1, ?_⟩
  rw [s62_ιMulti_two, ExteriorAlgebra.ιMulti_zero_apply, one_mul]

omit [CharZero F] in
theorem s62_pairing_eq_zero_of_isMaxIsotropic {W : Submodule F (V F n)}
    (hW : IsMaxIsotropic F n W) {x y : V F n} (hx : x ∈ W) (hy : y ∈ W) :
    pairing F n x y = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hW.1 _ (W.add_mem hx hy),
    hW.1 _ hx, hW.1 _ hy, sub_zero, sub_zero]

omit [CharZero F] in
/-- `⟪ξ, (a,·) ∧ (b,·)⟫` is the pairing of `ξ` with `a ∧ b` in `⋀² V`. -/
theorem s62_ev_eq_B2 (a b : V F n) {Y : ExtV F n} (hY : Y ∈ ⋀[F]^2 (V F n)) :
    s62_ev F n Y a b = s62_B2 F n (exteriorPower.ιMulti F 2 ![a, b]) ⟨Y, hY⟩ := by
  refine (s62_eval_eq_pairingDual F n (pairing F n a) (pairing F n b) ⟨Y, hY⟩).trans ?_
  simp only [s62_B2, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti]
  congr 2

/-- The span of the `ρ_g x - x` (`x ∈ ⋀² V`, `g ∈ G`) is orthogonal to the `G`-invariants for the
pairing of `⋀² V`. -/
theorem s62_B2_span_inv (G : Subgroup (Spin F n)) (Z : ⋀[F]^2 (V F n))
    (hZ : ∀ g ∈ G, rhoExt F n g (Z : ExtV F n) = Z) {y : ExtV F n}
    (hy : y ∈ Submodule.span F
      {y | ∃ g ∈ G, ∃ x ∈ ⋀[F]^2 (V F n), y = rhoExt F n g x - x})
    (hy2 : y ∈ ⋀[F]^2 (V F n)) : s62_B2 F n Z ⟨y, hy2⟩ = 0 := by
  have hρ : ∀ (g : Spin F n) (x : ⋀[F]^2 (V F n)),
      ((exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) x : ⋀[F]^2 (V F n)) : ExtV F n) =
        rhoExt F n g x := fun g x => exteriorPower.coe_map _ _
  have hle : Submodule.span F {y | ∃ g ∈ G, ∃ x ∈ ⋀[F]^2 (V F n), y = rhoExt F n g x - x} ≤
      ⋀[F]^2 (V F n) := Submodule.span_le.mpr (by
    rintro y ⟨g, -, x, hx, rfl⟩; exact Submodule.sub_mem _ (s62_rhoExt_mem F n g hx) hx)
  revert hy2
  induction hy using Submodule.span_induction with
  | mem w hw =>
    intro hy2
    obtain ⟨g, hg, x, hx, rfl⟩ := hw
    have h1 : (⟨rhoExt F n g x - x, hy2⟩ : ⋀[F]^2 (V F n)) =
        exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) ⟨x, hx⟩ - ⟨x, hx⟩ :=
      Subtype.ext (by rw [Submodule.coe_sub, hρ])
    have h2 : exteriorPower.map 2 (rho F n g : V F n →ₗ[F] V F n) Z = Z :=
      Subtype.ext (by rw [hρ, hZ g hg])
    rw [h1, map_sub, sub_eq_zero]
    conv_lhs => rw [← h2]
    exact s62_B2_rho F n g Z ⟨x, hx⟩
  | zero =>
    intro hy2
    have : (⟨0, hy2⟩ : ⋀[F]^2 (V F n)) = 0 := rfl
    rw [this, map_zero]
  | add a b ha hb iha ihb =>
    intro hy2
    have : (⟨a + b, hy2⟩ : ⋀[F]^2 (V F n)) = ⟨a, hle ha⟩ + ⟨b, hle hb⟩ := rfl
    rw [this, map_add, iha (hle ha), ihb (hle hb), add_zero]
  | smul c a ha iha =>
    intro hy2
    have : (⟨c • a, hy2⟩ : ⋀[F]^2 (V F n)) = c • ⟨a, hle ha⟩ := rfl
    rw [this, map_smul, iha (hle ha), smul_zero]

omit [CharZero F] in
/-- For `W` isotropic and `ξ ∈ ⋀² W`: `⟪ξ, (x,·) ∧ (y,·)⟫ = 0` if `x ∈ W`. -/
theorem s62_ev_isotropic_left (W : Submodule F (V F n))
    (hW : ∀ x ∈ W, ∀ y ∈ W, pairing F n x y = 0) {ξ : ExtV F n}
    (hξ : ξ ∈ Submodule.span F
      {z | ∃ a ∈ W, ∃ b ∈ W, z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b})
    {x : V F n} (hx : x ∈ W) (y : V F n) : s62_ev F n ξ x y = 0 :=
  s62_ev_span F n W W hξ x y fun a ha b hb => by rw [hW x hx a ha, hW x hx b hb]; ring

omit [CharZero F] in
/-- For `W` isotropic and `ξ ∈ ⋀² W`: `⟪ξ, (x,·) ∧ (y,·)⟫ = 0` if `y ∈ W`. -/
theorem s62_ev_isotropic_right (W : Submodule F (V F n))
    (hW : ∀ x ∈ W, ∀ y ∈ W, pairing F n x y = 0) {ξ : ExtV F n}
    (hξ : ξ ∈ Submodule.span F
      {z | ∃ a ∈ W, ∃ b ∈ W, z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b})
    (x : V F n) {y : V F n} (hy : y ∈ W) : s62_ev F n ξ x y = 0 :=
  s62_ev_span F n W W hξ x y fun a ha b hb => by rw [hW y hy a ha, hW y hy b hb]; ring

omit [CharZero F] in
/-- For `W` isotropic and `ξ ∈ W ∧ W'`: `⟪ξ, (x,·) ∧ (y,·)⟫ = 0` if `x, y ∈ W`. -/
theorem s62_ev_mixed_left (W W' : Submodule F (V F n))
    (hW : ∀ x ∈ W, ∀ y ∈ W, pairing F n x y = 0) {ξ : ExtV F n}
    (hξ : ξ ∈ Submodule.span F
      {z | ∃ a ∈ W, ∃ b ∈ W', z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b})
    {x y : V F n} (hx : x ∈ W) (hy : y ∈ W) : s62_ev F n ξ x y = 0 :=
  s62_ev_span F n W W' hξ x y fun a ha b hb => by rw [hW x hx a ha, hW y hy a ha]; ring

omit [CharZero F] in
/-- For `W'` isotropic and `ξ ∈ W ∧ W'`: `⟪ξ, (x,·) ∧ (y,·)⟫ = 0` if `x, y ∈ W'`. -/
theorem s62_ev_mixed_right (W W' : Submodule F (V F n))
    (hW' : ∀ x ∈ W', ∀ y ∈ W', pairing F n x y = 0) {ξ : ExtV F n}
    (hξ : ξ ∈ Submodule.span F
      {z | ∃ a ∈ W, ∃ b ∈ W', z = ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b})
    {x y : V F n} (hx : x ∈ W') (hy : y ∈ W') : s62_ev F n ξ x y = 0 :=
  s62_ev_span F n W W' hξ x y fun a ha b hb => by rw [hW' x hx b hb, hW' y hy b hb]; ring

omit [CharZero F] in
/-- For `V = W + W'`: a class `ξ ∈ ⋀² V` whose pairings `⟪ξ, (x,·) ∧ (y,·)⟫` vanish when `x ∈ W'`,
when `y ∈ W'`, and when `x, y ∈ W`, is zero. -/
theorem s62_eq_zero_of_ev (W W' : Submodule F (V F n)) (hWW : W ⊔ W' = ⊤) {ξ : ExtV F n}
    (hξ : ξ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x ∈ W', ∀ y, s62_ev F n ξ x y = 0) (h₂ : ∀ x, ∀ y ∈ W', s62_ev F n ξ x y = 0)
    (h₃ : ∀ x ∈ W, ∀ y ∈ W, s62_ev F n ξ x y = 0) : ξ = 0 := by
  apply s62_eq_zero_of_eval F n hξ
  intro x y
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp (hWW ▸ Submodule.mem_top : x ∈ W ⊔ W')
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp (hWW ▸ Submodule.mem_top : y ∈ W ⊔ W')
  show s62_ev F n ξ (x₁ + x₂) (y₁ + y₂) = 0
  rw [s62_ev_add_left, s62_ev_add_right, s62_ev_add_right, h₃ x₁ hx₁ y₁ hy₁, h₂ x₁ y₂ hy₂,
    h₁ x₂ hx₂ y₁, h₁ x₂ hx₂ y₂]
  simp only [add_zero]

end EvalHelpers


variable {n : ℕ} {d : ℚ}

/-! ## Helpers: the class `h = Ξ_P^♯` -/

section HClass

/-- `h = Ξ_P^♯` is fixed by `ρ(g)` if `ρ(g)` commutes with `f`. -/
theorem s62_rhoExt_hClass_of_comm (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n)
    (hcomm : ∀ x, rho ℚ n g (P.fη hW x) = P.fη hW (rho ℚ n g x)) :
    rhoExt ℚ n g (P.hClass hW) = P.hClass hW := by
  have hcomm' : ∀ x, (rho ℚ n g).symm (P.fη hW x) = P.fη hW ((rho ℚ n g).symm x) := by
    intro x
    apply (rho ℚ n g).injective
    rw [LinearEquiv.apply_symm_apply, hcomm, LinearEquiv.apply_symm_apply]
  have hh : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  rw [← sub_eq_zero]
  apply s62_eq_zero_of_eval ℚ n (Submodule.sub_mem _ (s62_rhoExt_mem ℚ n g hh) hh)
  intro x y
  rw [map_sub, map_sub, map_sub, s62_eval_rhoExt, KSecant.hClass_spec, KSecant.hClass_spec,
    sub_eq_zero]
  simp only [KSecant.XiQ, LinearMap.BilinForm.compLeft_apply]
  rw [← hcomm', s62_rho_symm_pairing]

/-- `h = Ξ_P^♯` is invariant under `Spin(V_ℚ)_P`: `ρ(g)` is an isometry commuting with
`f = η_{√-d}`, by Lemma 2.2.4 (its direction "`⇐`", `KSecant.s22b_η_commute`: "The image of `η`
clearly centralizes `ρ(Spin(V_ℚ)_P)`", TeX line 862; the paper takes the properties of `f` from
Lemma 2.2.4, TeX line 1240). -/
theorem s62_rhoExt_hClass (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) :
    rhoExt ℚ n g (P.hClass hP.isCompl) = P.hClass hP.isCompl :=
  s62_rhoExt_hClass_of_comm P hP.isCompl g fun x =>
    (P.s22b_η_commute hP.pos hP.isCompl (Kd.sqrtNeg d) g hg x).symm


theorem s62_hClass_mem_invQ (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : P.hClass hP.isCompl ∈ P.invQ 2 :=
  ⟨formToExt2_mem ℚ n _, fun g hg => s62_rhoExt_hClass P J hP g (Subgroup.mem_inf.mp hg).2⟩

theorem s62_hClass_ne_zero (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (hn : 1 ≤ n) :
    P.hClass hW ≠ 0 := by
  intro h0
  have hXi : ∀ x y, P.XiQ hW x y = 0 := fun x y => by
    rw [← KSecant.hClass_spec, h0]; simp
  have hv : ((0 : Module.Dual ℚ (H1 ℚ n)), e ℚ n ⟨0, by omega⟩) ≠ (0 : V ℚ n) := by
    intro hv
    have := congrArg (fun v : V ℚ n => v.2 ⟨0, by omega⟩) hv
    simp [e] at this
  exact hv ((P.XiQ_nondegenerate hW).1 _ (hXi _))

/-- `ι_{(x,·)_V} Ξ_P^♯ = f(x)`: contraction with `h = Ξ_P^♯` is `f` (`Ξ_P(x, y) = (f x, y)_V`). -/
theorem s62_contractLeft_hClass (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    contractLeft (Q := 0) (pairing ℚ n x) (P.hClass hW) = ExteriorAlgebra.ι ℚ (P.fη hW x) := by
  have hmem : contractLeft (Q := 0) (pairing ℚ n x) (P.hClass hW) ∈ ⋀[ℚ]^1 (V ℚ n) :=
    s62_contractLeft_mem ℚ n _ (k := 1) (formToExt2_mem ℚ n _)
  rw [ExteriorAlgebra.exteriorPower, pow_one] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [← hw]
  congr 1
  apply s62_pairing_injective ℚ n
  refine LinearMap.ext fun y => ?_
  have h1 := P.hClass_spec hW x y
  rw [← hw, s62_contractLeft_ι] at h1
  simp only [ExteriorAlgebra.algebraMapInv, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply] at h1
  rw [s62_pairing_comm, h1]
  rfl

/-- `c₁(𝒫)` is of type `(1,1)` for the complex structure of `X × X̂`. -/
theorem s62_c1P_hodge (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) :
    c1P ℚ n ∈ hodgeClassesV n (productStructure n J) 1 := by
  rw [mem_hodgeClassesV_one_iff (productStructure n J) (isComplexStructure_productStructure J hJ)
    _ (s62_c1P_mem ℚ n), s62_bcExt_c1P]
  have hc : c1P ℝ n = ∑ i, s62_Φ ℝ n (e ℝ n i) (f ℝ n i) := by
    simp only [c1P, pullX, pullXHat, ExteriorAlgebra.map_apply_ι, s62_Φ_apply]
    rfl
  rw [hc, map_sum]
  have hterm : ∀ i, ExteriorAlgebra.map (productStructure n J) (s62_Φ ℝ n (e ℝ n i) (f ℝ n i)) =
      s62_Φ ℝ n ((-J) (e ℝ n i)) (J.dualMap (f ℝ n i)) := by
    intro i
    simp only [s62_Φ_apply, map_mul, ExteriorAlgebra.map_apply_ι, productStructure,
      LinearMap.prodMap_apply, map_zero]
  simp only [hterm]
  rw [s62_canonical ℝ n (-J) J.dualMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine LinearMap.ext fun w => ?_
  have hJw : J (J w) = -w := by
    have := LinearMap.congr_fun hJ w
    simpa using this
  simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, LinearMap.neg_apply, hJw, neg_neg]

end HClass

/-! ## Helpers: `h = Ξ_P^♯` without Assumption 2.4.1, and the case `n = 1` -/

section HClassOne

/-- `h^j ≠ 0` for `j ≤ 2n` (`Ξ_P` is nondegenerate; the `sl₂`-relation of `h`). -/
theorem s62_hClass_pow_ne_zero (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) {j : ℕ}
    (hj : j ≤ 2 * n) : P.hClass hW ^ j ≠ 0 := by
  have hh := formToExt2_mem ℚ n (P.XiQ hW)
  exact s62_sl2_pow_ne_zero ℚ n (s62_lam ℚ n (P.fη hW) d) hh
    (s62_lam_spec ℚ n hh (P.fη hW) d hd.ne' (s62_contractLeft_hClass P hW)
      (fun x => by
        have := LinearMap.congr_fun (P.fη_comp_fη hW) x
        simpa using this)
      (P.pairing_fη_left hW))
    (s62_lam_one ℚ n _ _) hj

/-- `m_g` fixes the pure spinors `uᵢ` for `g` in the integral `Spin(V)_P` (it fixes `P` pointwise). -/
theorem s62_m_fix (P : KSecant n d) (g : Spin ℚ n) (hg : g ∈ P.spinPZ) {u : S (Kd d) n}
    (hu : u ∈ P.PK) : m (Kd d) n ((bcSpin ℚ (Kd d) n g : Spin (Kd d) n) : C (Kd d) n) u = u := by
  have hle : P.PK ≤ LinearMap.eqLocus (m (Kd d) n ((bcSpin ℚ (Kd d) n g : Spin (Kd d) n) :
      C (Kd d) n)) LinearMap.id := by
    rw [← P.span_bcS_Pℚ, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    show m (Kd d) n (bcC ℚ (Kd d) n g) (bcS ℚ (Kd d) n p) = bcS ℚ (Kd d) n p
    rw [s62_m_bcC, (Subgroup.mem_inf.mp hg).2 p hp]
  exact hle hu

theorem s62_bcSpin_mem_spinL₁L₂ (P : KSecant n d) (g : Spin ℚ n) (hg : g ∈ P.spinPZ) :
    bcSpin ℚ (Kd d) n g ∈ P.spinL₁L₂ := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show ∃ c : Kd d, m (Kd d) n ((bcSpin ℚ (Kd d) n g : Spin (Kd d) n) : C (Kd d) n) P.u₁ =
      c • P.u₁
    exact ⟨1, by rw [one_smul]; exact s62_m_fix P g hg (Submodule.subset_span (Set.mem_insert _ _))⟩
  · show ∃ c : Kd d, m (Kd d) n ((bcSpin ℚ (Kd d) n g : Spin (Kd d) n) : C (Kd d) n) P.u₂ =
      c • P.u₂
    exact ⟨1, by
      rw [one_smul]; exact s62_m_fix P g hg (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩

theorem s62_ηK_W₁ (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {v : V (Kd d) n}
    (hv : v ∈ P.W₁) : P.ηK hW l v = l • v := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_left hW hv,
    Submodule.projectionOnto_apply_of_mem_right hW.symm hv, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, add_zero]

theorem s62_ηK_W₂ (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {v : V (Kd d) n}
    (hv : v ∈ P.W₂) : P.ηK hW l v = Kd.σ d l • v := by
  simp only [KSecant.ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_left hW.symm hv,
    Submodule.projectionOnto_apply_of_mem_right hW hv, Submodule.subtype_apply,
    ZeroMemClass.coe_zero, smul_zero, zero_add]

/-- `ρ(g)` commutes with `f = η_{√-d}` for `g` in the integral `Spin(V)_P`: `ρ(g)` preserves
`W₁` and `W₂`. -/
theorem s62_rho_fη (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n)
    (hg : g ∈ P.spinPZ) (x : V ℚ n) : rho ℚ n g (P.fη hW x) = P.fη hW (rho ℚ n g x) := by
  have hmem := s62_bcSpin_mem_spinL₁L₂ P g hg
  have hη : ∀ v, rho (Kd d) n (bcSpin ℚ (Kd d) n g) (P.ηK hW (Kd.sqrtNeg d) v) =
      P.ηK hW (Kd.sqrtNeg d) (rho (Kd d) n (bcSpin ℚ (Kd d) n g) v) := by
    intro v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ : ∃ v₁ ∈ P.W₁, ∃ v₂ ∈ P.W₂, v₁ + v₂ = v :=
      Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top)
    have hm₁ : rho (Kd d) n (bcSpin ℚ (Kd d) n g) v₁ ∈ P.W₁ := P.rho_mem_W₁ ⟨_, hmem⟩ v₁ hv₁
    have hm₂ : rho (Kd d) n (bcSpin ℚ (Kd d) n g) v₂ ∈ P.W₂ := P.rho_mem_W₂ ⟨_, hmem⟩ v₂ hv₂
    rw [map_add, s62_ηK_W₁ P hW _ hv₁, s62_ηK_W₂ P hW _ hv₂, map_add, map_smul, map_smul, map_add,
      map_add, s62_ηK_W₁ P hW _ hm₁, s62_ηK_W₂ P hW _ hm₂]
  apply s62_bcV_injective ℚ (Kd d) n
  rw [← s62_rho_bcV]
  change rho (Kd d) n (bcSpin ℚ (Kd d) n g) (bcV ℚ (Kd d) n (P.η hW (Kd.sqrtNeg d) x)) =
    bcV ℚ (Kd d) n (P.η hW (Kd.sqrtNeg d) (rho ℚ n g x))
  rw [← P.ηK_bcV hd hW, ← P.ηK_bcV hd hW, hη, s62_rho_bcV]

/-- `h = Ξ_P^♯` is `Spin(V)_P`-invariant (without Assumption 2.4.1). -/
theorem s62_hClass_mem_invQ' (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    P.hClass hW ∈ P.invQ 2 :=
  ⟨formToExt2_mem ℚ n _, fun g hg => s62_rhoExt_hClass_of_comm P hW g (s62_rho_fη P hd hW g hg)⟩

/-- Rational `Spin(V)_P`-invariants stay invariant over `K`. -/
theorem s62_bcExt_mem_invK (P : KSecant n d) {k : ℕ} {y : ExtV ℚ n} (hy : y ∈ P.invQ k) :
    bcExt ℚ (Kd d) n y ∈ P.invK k := by
  refine ⟨s62_bcExt_mem ℚ (Kd d) n hy.1, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [s62_rhoExt_bcExt, hy.2 g hg]

/-- The base change of `H²_P` lies in the span of the `ρ_g x - x` over `K`. -/
theorem s62_bcExt_H2P (P : KSecant n d) {y : ExtV ℚ n} (hy : y ∈ P.H2P) :
    bcExt ℚ (Kd d) n y ∈ Submodule.span (Kd d)
      {z | ∃ g ∈ P.spinPZ.map (bcSpin ℚ (Kd d) n), ∃ x ∈ ⋀[Kd d]^2 (V (Kd d) n),
        z = rhoExt (Kd d) n g x - x} := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, hg, x, hx, rfl⟩ := hw
    refine Submodule.subset_span ⟨bcSpin ℚ (Kd d) n g, ⟨g, hg, rfl⟩, bcExt ℚ (Kd d) n x,
      s62_bcExt_mem ℚ (Kd d) n hx, ?_⟩
    rw [map_sub, s62_rhoExt_bcExt]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul, algebra_compatible_smul (Kd d) c]; exact Submodule.smul_mem _ _ ha

/-- `ι_{(x,·)} h_K = η_{√-d}(x)` over `K`. -/
theorem s62_contractLeft_bcExt_hClass (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (x : V (Kd d) n) :
    contractLeft (Q := 0) (pairing (Kd d) n x) (bcExt ℚ (Kd d) n (P.hClass hW)) =
      ExteriorAlgebra.ι (Kd d) (P.ηK hW (Kd.sqrtNeg d) x) := by
  have key : ((contractLeft (Q := (0 : QuadraticForm (Kd d) (V (Kd d) n)))).flip
      (bcExt ℚ (Kd d) n (P.hClass hW))) ∘ₗ pairing (Kd d) n =
      ExteriorAlgebra.ι (Kd d) ∘ₗ P.ηK hW (Kd.sqrtNeg d) := by
    refine (basisV (Kd d) n).ext fun i => ?_
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [← s62_bcV_basisV ℚ (Kd d) n i, s62_contractLeft_bcExt, s62_contractLeft_hClass,
      s62_bcExt_ι, P.ηK_bcV hd hW]
    rfl
  exact LinearMap.congr_fun key x

/-- (`n = 1`) An invariant `Y ∈ ⋀² V_K` whose pairings `⟪Y, (x,·) ∧ (y,·)⟫` vanish for `x, y` both
in `W₁` or both in `W₂` lies in the line `L = (W₁ ⊗ W₂)^{Spin(V)_P}` of Lemma 2.2.7. -/
theorem s62_core_one (P : KSecant 1 d) (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    {Y : ExtV (Kd d) 1} (hY : Y ∈ P.invK 2)
    (h₁ : ∀ x ∈ P.W₁, ∀ y ∈ P.W₁, s62_ev (Kd d) 1 Y x y = 0)
    (h₂ : ∀ x ∈ P.W₂, ∀ y ∈ P.W₂, s62_ev (Kd d) 1 Y x y = 0) :
    Y ∈ pqPiece P.W₁ P.W₂ 1 1 := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have hi₁ : ∀ x ∈ P.W₁, ∀ y ∈ P.W₁, pairing (Kd d) 1 x y = 0 := fun x hx y hy =>
    s62_pairing_eq_zero_of_isMaxIsotropic (Kd d) 1 P.isPure.2 hx hy
  have hi₂ : ∀ x ∈ P.W₂, ∀ y ∈ P.W₂, pairing (Kd d) 1 x y = 0 := fun x hx y hy =>
    s62_pairing_eq_zero_of_isMaxIsotropic (Kd d) 1 P.isPure₂.2 hx hy
  have hK : P.invK 2 = pqPiece P.W₁ P.W₂ 2 0 ⊔ pqPiece P.W₁ P.W₂ 0 2 ⊔
      (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1) := lemma2_2_7_K_eq P hd hP
  have hY' : Y ∈ pqPiece P.W₁ P.W₂ 2 0 ⊔ pqPiece P.W₁ P.W₂ 0 2 ⊔
      (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1) := hK ▸ hY
  obtain ⟨AB, hAB, C, hC, hYeq⟩ := Submodule.mem_sup.mp hY'
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hAB
  have hA' := s62_pqPiece_two_zero_le (Kd d) 1 P.W₁ P.W₂ hA
  have hB' := s62_pqPiece_zero_two_le (Kd d) 1 P.W₁ P.W₂ hB
  have hC' := s62_pqPiece_one_one_le (Kd d) 1 P.W₁ P.W₂ hC.2
  have hB0 : B = 0 := by
    refine s62_eq_zero_of_ev (Kd d) 1 P.W₁ P.W₂ hW.sup_eq_top (s62_span_ιι_le _ _ _ _ hB')
      (fun x hx y => s62_ev_isotropic_left _ _ P.W₂ hi₂ hB' hx y)
      (fun x y hy => s62_ev_isotropic_right _ _ P.W₂ hi₂ hB' x hy) (fun x hx y hy => ?_)
    have h := h₁ x hx y hy
    rw [← hYeq, s62_ev_add, s62_ev_add, s62_ev_isotropic_left _ _ P.W₁ hi₁ hA' hx y,
      s62_ev_mixed_left _ _ P.W₁ P.W₂ hi₁ hC' hx hy, zero_add, add_zero] at h
    exact h
  have hA0 : A = 0 := by
    refine s62_eq_zero_of_ev (Kd d) 1 P.W₂ P.W₁ hW.symm.sup_eq_top (s62_span_ιι_le _ _ _ _ hA')
      (fun x hx y => s62_ev_isotropic_left _ _ P.W₁ hi₁ hA' hx y)
      (fun x y hy => s62_ev_isotropic_right _ _ P.W₁ hi₁ hA' x hy) (fun x hx y hy => ?_)
    have h := h₂ x hx y hy
    rw [← hYeq, hB0, add_zero, s62_ev_add, s62_ev_mixed_right _ _ P.W₁ P.W₂ hi₂ hC' hx hy,
      add_zero] at h
    exact h
  rw [← hYeq, hA0, hB0, zero_add, zero_add]
  exact hC.2

/-- (`n = 1`) `h_K = Ξ_P^♯` spans the line `L = (W₁ ⊗ W₂)^{Spin(V)_P}`. -/
theorem s62_bcExt_hClass_mem_L (P : KSecant 1 d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    bcExt ℚ (Kd d) 1 (P.hClass (P.isCompl_of_not_isIsotropic hd hP)) ∈
      pqPiece P.W₁ P.W₂ 1 1 := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have hev : ∀ x y, s62_ev (Kd d) 1 (bcExt ℚ (Kd d) 1 (P.hClass hW)) x y =
      pairing (Kd d) 1 y (P.ηK hW (Kd.sqrtNeg d) x) := by
    intro x y
    simp only [s62_ev]
    rw [s62_contractLeft_bcExt_hClass P hd hW, s62_contractLeft_ι]
    simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hi₁ : ∀ x ∈ P.W₁, ∀ y ∈ P.W₁, pairing (Kd d) 1 x y = 0 := fun x hx y hy =>
    s62_pairing_eq_zero_of_isMaxIsotropic (Kd d) 1 P.isPure.2 hx hy
  have hi₂ : ∀ x ∈ P.W₂, ∀ y ∈ P.W₂, pairing (Kd d) 1 x y = 0 := fun x hx y hy =>
    s62_pairing_eq_zero_of_isMaxIsotropic (Kd d) 1 P.isPure₂.2 hx hy
  refine s62_core_one P hd hP (s62_bcExt_mem_invK P (s62_hClass_mem_invQ' P hd hW)) ?_ ?_
  · intro x hx y hy
    rw [hev, s62_ηK_W₁ P hW _ hx, map_smul, hi₁ y hy x hx, smul_zero]
  · intro x hx y hy
    rw [hev, s62_ηK_W₂ P hW _ hx, map_smul, hi₂ y hy x hx, smul_zero]

/-- (`n = 1`) `H²_P ∪ h = 0`: `ρ_g` is trivial on `⋀⁴ V_ℚ` and fixes `h`. -/
theorem s62_H2P_mul_hClass_one (P : KSecant 1 d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    {z : ExtV ℚ 1} (hz : z ∈ P.H2P) : z * P.hClass hW = 0 := by
  have hh2 : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ 1) := formToExt2_mem ℚ 1 _
  have hinv := s62_hClass_mem_invQ' P hd hW
  have hsq : P.hClass hW ^ 2 ≠ 0 := s62_hClass_pow_ne_zero P hd hW (by norm_num)
  have htop : ∀ g ∈ P.spinPZ, ∀ z ∈ ⋀[ℚ]^(4 * 1) (V ℚ 1), rhoExt ℚ 1 g z = z := by
    intro g hg z hz
    refine s62_rhoExt_top ℚ 1 g (s62_pow_mem ℚ 1 hh2 2) hsq ?_ hz
    rw [map_pow, hinv.2 g hg]
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, hg, x, hx, rfl⟩ := hw
    have hxh : x * P.hClass hW ∈ ⋀[ℚ]^(2 + 2) (V ℚ 1) :=
      SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[ℚ]^i (V ℚ 1)) hx hh2
    have h1 := htop g hg _ hxh
    rw [map_mul, hinv.2 g hg] at h1
    rw [sub_mul, h1, sub_self]
  | zero => rw [zero_mul]
  | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_mul_assoc, ha, smul_zero]

/-- (`n = 1`) `x ∧ x' ∈ (⋀² V_K)^{Spin(V)_P}` for `x, x' ∈ W₁` (Lemma 2.2.7). -/
theorem s62_ιι_mem_invK₁ (P : KSecant 1 d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) {x x' : V (Kd d) 1}
    (hx : x ∈ P.W₁) (hx' : x' ∈ P.W₁) :
    ExteriorAlgebra.ι (Kd d) x * ExteriorAlgebra.ι (Kd d) x' ∈ P.invK 2 := by
  have hK : P.invK 2 = pqPiece P.W₁ P.W₂ 2 0 ⊔ pqPiece P.W₁ P.W₂ 0 2 ⊔
      (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1) := lemma2_2_7_K_eq P hd hP
  have hmem : ExteriorAlgebra.ι (Kd d) x * ExteriorAlgebra.ι (Kd d) x' ∈ pqPiece P.W₁ P.W₂ 2 0 :=
    Submodule.subset_span ⟨![x, x'], ![], fun i => by fin_cases i <;> assumption,
      fun i => i.elim0, by
        rw [s62_ιMulti_two, ExteriorAlgebra.ιMulti_zero_apply]; exact (mul_one _).symm⟩
  rw [hK]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left hmem)

/-- (`n = 1`) `x ∧ x' ∈ (⋀² V_K)^{Spin(V)_P}` for `x, x' ∈ W₂` (Lemma 2.2.7). -/
theorem s62_ιι_mem_invK₂ (P : KSecant 1 d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) {x x' : V (Kd d) 1}
    (hx : x ∈ P.W₂) (hx' : x' ∈ P.W₂) :
    ExteriorAlgebra.ι (Kd d) x * ExteriorAlgebra.ι (Kd d) x' ∈ P.invK 2 := by
  have hK : P.invK 2 = pqPiece P.W₁ P.W₂ 2 0 ⊔ pqPiece P.W₁ P.W₂ 0 2 ⊔
      (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1) := lemma2_2_7_K_eq P hd hP
  have hmem : ExteriorAlgebra.ι (Kd d) x * ExteriorAlgebra.ι (Kd d) x' ∈ pqPiece P.W₁ P.W₂ 0 2 :=
    Submodule.subset_span ⟨![], ![x, x'], fun i => i.elim0,
      fun i => by fin_cases i <;> assumption, by
        rw [s62_ιMulti_two, ExteriorAlgebra.ιMulti_zero_apply]; exact (one_mul _).symm⟩
  rw [hK]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hmem)

/-- For `y ∈ H²_P` and an invariant `x ∧ x' ∈ (⋀² V_K)^{Spin(V)_P}`:
`⟪y_K, (x,·) ∧ (x',·)⟫ = 0` (`H²_P` is orthogonal to the invariants). -/
theorem s62_ev_bcExt_H2P (P : KSecant n d) {y : ExtV ℚ n} (hy : y ∈ P.H2P)
    (hy2 : bcExt ℚ (Kd d) n y ∈ ⋀[Kd d]^2 (V (Kd d) n)) {x x' : V (Kd d) n}
    (hxx : ExteriorAlgebra.ι (Kd d) x * ExteriorAlgebra.ι (Kd d) x' ∈ P.invK 2) :
    s62_ev (Kd d) n (bcExt ℚ (Kd d) n y) x x' = 0 := by
  rw [s62_ev_eq_B2 (Kd d) n x x' hy2]
  refine s62_B2_span_inv (Kd d) n _ _ (fun g hg => ?_) (s62_bcExt_H2P P hy) hy2
  rw [exteriorPower.ιMulti_apply_coe, s62_ιMulti_two]
  exact hxx.2 g hg

/-- `H²_P ∩ (⋀² V_ℚ)^{Spin(V)_P} = 0` for `n = 1`: `H²_P` is orthogonal to the invariants for the
pairing of `⋀² V_K`, which puts the base change of an element of `H²_P ∩ (⋀² V_ℚ)^{Spin(V)_P}` in
the line `L = K h` of Lemma 2.2.7; and `H²_P ∪ h = 0` while `h² ≠ 0`. -/
theorem s62_H2P_inf_invQ_one (P : KSecant 1 d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    P.H2P ⊓ P.invQ 2 = ⊥ := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have hinv := s62_hClass_mem_invQ' P hd hW
  have hsq : P.hClass hW ^ 2 ≠ 0 := s62_hClass_pow_ne_zero P hd hW (by norm_num)
  have hh0 : P.hClass hW ≠ 0 := s62_hClass_ne_zero P hW le_rfl
  rw [eq_bot_iff]
  rintro y ⟨hyH, hyI⟩
  rw [Submodule.mem_bot]
  have hY := s62_bcExt_mem_invK P hyI (d := d)
  have hYL := s62_core_one P hd hP hY
    (fun x hx x' hx' => s62_ev_bcExt_H2P P hyH hY.1 (s62_ιι_mem_invK₁ P hd hP hx hx'))
    (fun x hx x' hx' => s62_ev_bcExt_H2P P hyH hY.1 (s62_ιι_mem_invK₂ P hd hP hx hx'))
  have hhL := s62_bcExt_hClass_mem_L P hd hP
  have hfr : Module.finrank (Kd d) (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1 :
      Submodule (Kd d) (ExtV (Kd d) 1)) = 1 := (lemma2_2_7_K_finrank P hd hP).2.2
  have hbch0 : bcExt ℚ (Kd d) 1 (P.hClass hW) ≠ 0 := fun h0 =>
    hh0 (s62_bcExt_injective ℚ (Kd d) 1 (h0.trans (map_zero _).symm))
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨bcExt ℚ (Kd d) 1 (P.hClass hW), s62_bcExt_mem_invK P hinv, hhL⟩ :
      (P.invK 2 ⊓ pqPiece P.W₁ P.W₂ 1 1 : Submodule (Kd d) (ExtV (Kd d) 1)))
    (fun h0 => hbch0 (congrArg Subtype.val h0))).mp hfr ⟨_, hY, hYL⟩
  have hYt : bcExt ℚ (Kd d) 1 y = t • bcExt ℚ (Kd d) 1 (P.hClass hW) :=
    (congrArg Subtype.val ht).symm
  have h1 := congrArg (bcExt ℚ (Kd d) 1) (s62_H2P_mul_hClass_one P hd hW hyH)
  rw [map_mul, hYt, map_zero, smul_mul_assoc, ← map_mul, ← pow_two] at h1
  have ht0 : t = 0 := (smul_eq_zero.mp h1).resolve_right fun h0 =>
    hsq (s62_bcExt_injective ℚ (Kd d) 1 (h0.trans (map_zero _).symm))
  rw [ht0, zero_smul] at hYt
  exact s62_bcExt_injective ℚ (Kd d) 1 (hYt.trans (map_zero _).symm)

end HClassOne

/-! ## `H²(X × X̂, ℚ)_P` -/

namespace KSecant

variable (P : KSecant n d)

/-- `H²(X × X̂, ℚ)_P ⊆ H²(X × X̂, ℚ)`. -/
theorem H2P_le : P.H2P ≤ ⋀[ℚ]^2 (V ℚ n) := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨g, -, x, hx, rfl⟩
  exact Submodule.sub_mem _ (s62_rhoExt_mem ℚ n g hx) hx

/-- `H²_P` contains no non-zero `Spin(V)_P`-invariant class: it is the sum of the non-trivial
irreducible subrepresentations of `H²(X × X̂, ℚ)` (used for the uniqueness in Lemma 6.2.3 and in
Remark 6.2.4).

Proof (the paper takes this for granted, `H²_P` being defined there as a sum of non-trivial
irreducible subrepresentations): `n ≥ 2`: a nonzero invariant `y ∈ H²_P` has `y^{2n} ≠ 0`
(Lemma 2.2.7, note), `ρ_g` is trivial on `⋀^{4n} V`, so `H²_P ∪ y^{2n-1} = 0`, a contradiction.
`n = 1`: over `K`, `H²_P` is orthogonal to the invariants `⋀² W₁ ⊕ ⋀² W₂ ⊕ L` (Lemma 2.2.7) for the
invariant pairing of `⋀² V_K`, which forces an invariant `y ∈ H²_P` into `L = K Ξ_P`; and
`H²_P ∪ Ξ_P = 0` while `Ξ_P² ≠ 0` (`s62_H2P_inf_invQ_one`). -/
theorem H2P_inf_invQ (hd : 0 < d) (hP : ¬ P.IsIsotropic) : P.H2P ⊓ P.invQ 2 = ⊥ := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rcases Nat.lt_or_ge n 1 with hn0 | hn1
    · have hbot : ⋀[ℚ]^2 (V ℚ n) = ⊥ := s62_exteriorPower_eq_bot ℚ n (by omega)
      refine eq_bot_iff.mpr fun y hy => ?_
      have := P.H2P_le hy.1
      rwa [hbot] at this
    · obtain rfl : n = 1 := by omega
      exact s62_H2P_inf_invQ_one P hd hP
  · rw [eq_bot_iff]
    rintro y ⟨hyH, hyI⟩
    rw [Submodule.mem_bot]
    by_contra hy0
    have hpow := (lemma2_2_7_note P hd hn hP y hyI hy0).1
    have hy2 : y ∈ ⋀[ℚ]^2 (V ℚ n) := hyI.1
    have hytop : y ^ (2 * n) ∈ ⋀[ℚ]^(4 * n) (V ℚ n) := by
      have := s62_pow_mem ℚ n hy2 (2 * n); rwa [show 2 * (2 * n) = 4 * n by ring] at this
    -- `ρ_g` is trivial on `⋀^{4n} V`
    have htop : ∀ g ∈ P.spinPZ, ∀ z ∈ ⋀[ℚ]^(4 * n) (V ℚ n), rhoExt ℚ n g z = z := by
      intro g hg z hz
      refine s62_rhoExt_top ℚ n g hytop hpow ?_ hz
      rw [map_pow, hyI.2 g hg]
    -- `H²_P ∪ y^{2n-1} = 0`
    have hkill : ∀ z ∈ P.H2P, z * y ^ (2 * n - 1) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, hg, x, hx, rfl⟩ := hw
        have hxy : x * y ^ (2 * n - 1) ∈ ⋀[ℚ]^(4 * n) (V ℚ n) := by
          have := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[ℚ]^i (V ℚ n)) hx
            (s62_pow_mem ℚ n hy2 (2 * n - 1))
          rwa [show 2 + 2 * (2 * n - 1) = 4 * n by omega] at this
        have h1 := htop g hg _ hxy
        rw [map_mul, map_pow, hyI.2 g hg] at h1
        rw [sub_mul, h1, sub_self]
      | zero => rw [zero_mul]
      | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_mul_assoc, ha, smul_zero]
    have := hkill y hyH
    rw [← pow_succ', Nat.sub_add_cancel (by omega)] at this
    exact hpow this


/-- (§6.2, TeX lines 2414–2416) "`H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P + ℚ Ξ_P`, by Lemma 2.2.7", with `Ξ_P`
regarded as the class `h = Ξ_P^♯ ∈ ⋀² V_ℚ` (`hClass`). Needs `n ≥ 2` (the paper's standing
assumption): for `n = 1` the invariants of `⋀² V_ℚ` form the three-dimensional middle degree.

Departure from the paper: the paper's `H²_P` is the sum of the non-trivial irreducible
subrepresentations, so the decomposition rests on complete reducibility, which is not available for
the arithmetic group `Spin(V)_P`; with `H²_P` the span of the `ρ_g x - x`, the codimension of `H²_P`
is bounded by the dimension of the invariants using the `Spin(V)`-invariant nondegenerate pairing of
`⋀² V` (`s62_finrank_le_span_add_inv`), and `H²_P ∩ ℚ Ξ_P = 0` (`H2P_inf_invQ`); then Lemma 2.2.7
(`dim H²^{Spin(V)_P} = 1`) as in the paper. -/
theorem exteriorPower_two_eq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (hn : 2 ≤ n) :
    ⋀[ℚ]^2 (V ℚ n) = P.H2P ⊔ Submodule.span ℚ {P.hClass hP.isCompl} := by
  have : Module.Finite ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
  have hh := s62_hClass_mem_invQ P J hP
  have hh0 := s62_hClass_ne_zero P hP.isCompl (by omega)
  have hspan : Submodule.span ℚ {P.hClass hP.isCompl} ≤ P.invQ 2 := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hh
  have hle : P.H2P ⊔ Submodule.span ℚ {P.hClass hP.isCompl} ≤ ⋀[ℚ]^2 (V ℚ n) :=
    sup_le P.H2P_le (hspan.trans inf_le_left)
  refine le_antisymm ?_ hle
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm.le
  have h1 : Module.finrank ℚ (⋀[ℚ]^2 (V ℚ n)) ≤ Module.finrank ℚ P.H2P +
      Module.finrank ℚ (P.invQ 2) := s62_finrank_le_span_add_inv ℚ n P.spinPZ
  have h2 : Module.finrank ℚ (P.invQ 2) = 1 :=
    lemma2_2_7_even P hP.pos hP.nonIsotropic 2 even_two (by omega) (by omega)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq P.H2P (Submodule.span ℚ {P.hClass hP.isCompl})
  have hinf : P.H2P ⊓ Submodule.span ℚ {P.hClass hP.isCompl} = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hspan).trans (P.H2P_inf_invQ hP.pos hP.nonIsotropic).le)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hh0] at h3
  calc Module.finrank ℚ (⋀[ℚ]^2 (V ℚ n))
      ≤ Module.finrank ℚ P.H2P + Module.finrank ℚ (P.invQ 2) := h1
    _ = Module.finrank ℚ (P.H2P ⊔ Submodule.span ℚ {P.hClass hP.isCompl} :
          Submodule ℚ (ExtV ℚ n)) := by rw [h2, h3]



/-- `H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P ⊕ H²(X × X̂, ℚ)^{Spin(V)_P}` (`H²_P` has codimension at most
`dim H²^{Spin(V)_P}` and meets the invariants in `0`). -/
theorem s62_two_le_sup (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    ⋀[ℚ]^2 (V ℚ n) ≤ P.H2P ⊔ P.invQ 2 := by
  have : Module.Finite ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
  have hle : P.H2P ⊔ P.invQ 2 ≤ ⋀[ℚ]^2 (V ℚ n) := sup_le P.H2P_le inf_le_left
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm.le
  have h1 : Module.finrank ℚ (⋀[ℚ]^2 (V ℚ n)) ≤ Module.finrank ℚ P.H2P +
      Module.finrank ℚ (P.invQ 2) := s62_finrank_le_span_add_inv ℚ n P.spinPZ
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq P.H2P (P.invQ 2)
  rw [P.H2P_inf_invQ hd hP, finrank_bot, add_zero] at h3
  calc Module.finrank ℚ (⋀[ℚ]^2 (V ℚ n))
      ≤ Module.finrank ℚ P.H2P + Module.finrank ℚ (P.invQ 2) := h1
    _ = Module.finrank ℚ (P.H2P ⊔ P.invQ 2 : Submodule ℚ (ExtV ℚ n)) := h3.symm

end KSecant

/-! ## Lemma 6.2.3 -/

section Lemma623

variable (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))

/-- (Proof of Lemma 6.2.3, TeX lines 2441–2448) For `w₁, w₂ ∈ P`, the class
`β = ch(Φ(F₂ ⊠ F₁^∨)) = φ(w₂ ⊗ τ w₁)` is `Spin(V)_P`-invariant with respect to `ρ'`: `w₂ ⊗ τ(w₁)` is
invariant under `m ⊗ m†` (Remark 5.2.3) and `φ` intertwines `m ⊗ m†` with `ρ'` ((6.1.4)). -/
theorem lemma6_2_3_rhoPrime_invariant (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) :
    rhoPrime ℚ n g (secantSqClass ℚ n w₂ w₁) = secantSqClass ℚ n w₂ w₁ := by
  have hg' : g ∈ P.spinPℚ := (Subgroup.mem_inf.mp hg).2
  have h₁ : m ℚ n (g : C ℚ n) w₁ = w₁ := hg' w₁ hw₁
  have h₂ : m ℚ n (g : C ℚ n) w₂ = w₂ := hg' w₂ hw₂
  -- `w₁^∨ = τ(w₁)` is invariant under `m†_g` (Remark 5.2.3)
  have hτ : mDagger ℚ n (g : C ℚ n) (tau ℚ n w₁) = tau ℚ n w₁ :=
    remark5_2_3 ℚ n w₁ (P.Pℚ_le_Splus hw₁) g h₁
  -- `ρ'_g = φ (m_g ⊗ m†_g) φ⁻¹` ((6.1.4))
  rw [rhoPrime_eq_phiOrlov_conj]
  simp only [LinearMap.comp_apply, secantSqClass]
  rw [← LinearMap.comp_apply (phiOrlovInv ℚ n) (phiOrlov ℚ n), phiOrlovInv_comp_phiOrlov,
    LinearMap.id_apply, TensorProduct.map_tmul, h₂, hτ]

/-- **(6.2.4)** (`eq-N-g-beta`): for `g ∈ Spin(V)_P`, `β = ch(N_g) ρ_g(β)`, where `N_g` is the line
bundle of (6.1.8) (`ρ'_g = ch(N_g) ∪ ρ_g`; in the model `ch(N_g) = exp(c)`, `c = c₁(N_g) ∈ ⋀² V_ℚ`,
which exists by (6.1.8), `equation6_1_8`, and is integral by `equation6_1_8_integral`). Here
`β = φ(w₂ ⊗ τ w₁)` with `w₁, w₂ ∈ P`.
Proof (TeX lines 2449–2456): `β` is `ρ'_g`-invariant (`lemma6_2_3_rhoPrime_invariant`) and
`ρ'_g = exp(c) ∪ ρ_g`. -/
theorem equation6_2_4 (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (g : Spin ℚ n)
    (hg : g ∈ P.spinPZ) (c : ExtV ℚ n)
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    secantSqClass ℚ n w₂ w₁ = IsNilpotent.exp c * rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) := by
  rw [← hc, lemma6_2_3_rhoPrime_invariant P w₁ w₂ hw₁ hw₂ g hg]

/-- **(6.2.4)** (`eq-N-g-beta`), as printed: given `g ∈ Spin(V)_P` there exists a topological
complex line bundle `N_g` on `X × X̂` such that `β = ch(N_g) ρ_g(β)`. Model: an integral class
`c = c₁(N_g) ∈ H²(X × X̂, ℤ)` with `β = exp(c) ρ_g(β)`.
Proof: "by Equation (6.1.8)" (TeX line 2456), for the integral `g`: `equation6_1_8_integral`
([Orlov, Th. 2.10]) and `equation6_2_4`. -/
theorem equation6_2_4_exists (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (g : Spin ℚ n)
    (hg : g ∈ P.spinPZ) :
    ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧
      secantSqClass ℚ n w₂ w₁ = IsNilpotent.exp c * rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) := by
  obtain ⟨c, hc2, hcZ, hc⟩ := equation6_1_8_integral n g (Subgroup.mem_inf.mp hg).1
  exact ⟨c, hc2, hcZ, equation6_2_4 P w₁ w₂ hw₁ hw₂ g hg c hc⟩

/-- (Proof of Lemma 6.2.3, TeX line 2458) If `k < n` is the least `j` with `β_j ≠ 0`, then
`β_k` is `Spin(V)_P`-invariant with respect to `ρ` (by the minimality of `k`) and hence a non-zero
multiple of `Ξ_P^k` (`h^k`, `h = Ξ_P^♯`), by `k < dim X` (Lemma 2.2.7). -/
theorem lemma6_2_3_lowest (hP : Assumption2_4_1 P J) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ)
    (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n) :
    projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ ∧
      ∃ c : ℚ, c ≠ 0 ∧
        projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) = c • P.hClass hP.isCompl ^ k := by
  have hlow : ∀ j < k, projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) = 0 := fun j hj => by
    by_contra h; exact absurd (hk.2 h) (by omega)
  -- `β_k` is `ρ`-invariant by the minimality of `k`: `β = ch(N_g) ρ_g(β)` ((6.2.4), with the
  -- class `c₁(N_g)` of (6.1.8), [Orlov, Th. 2.10])
  have hinv : projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ := by
    intro g hg
    obtain ⟨c, hc2, hcg⟩ := equation6_1_8 ℚ n g
    have hc := equation6_2_4 P w₁ w₂ hw₁ hw₂ g hg c hcg
    have h1 := (s62_projDeg_exp_mul ℚ n hc2 (rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁)) k
      (fun j hj => by rw [s62_projDeg_rhoExt, hlow j hj, map_zero])).1
    rw [← hc, s62_projDeg_rhoExt] at h1
    exact h1.symm
  refine ⟨hinv, ?_⟩
  have hβk : projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ≠ 0 := hk.1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨rankExt ℚ n (secantSqClass ℚ n w₂ w₁), ?_, ?_⟩
    · intro h0; apply hβk; rw [mul_zero, s62_projDeg_zero, h0, map_zero]
    · rw [mul_zero, pow_zero, s62_projDeg_zero, Algebra.algebraMap_eq_smul_one]
  · -- `k < dim X`: `(⋀^{2k} V_ℚ)^{Spin(V)_P}` is spanned by `Ξ_P^k` (Lemma 2.2.7)
    have hspan := lemma2_2_7_note_pow P hP.pos (by omega) hP.nonIsotropic _
      (s62_hClass_mem_invQ P J hP) (s62_hClass_ne_zero P hP.isCompl (by omega)) k (by omega)
      (by omega)
    have hmem : projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ P.invQ (2 * k) :=
      ⟨s62_projDeg_mem ℚ n _ _, hinv⟩
    rw [hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl; apply hβk; rw [← hc, zero_smul]

/-- (Proof of Lemma 6.2.3, TeX line 2458) "the homomorphism
`β_k ∪ (•) : H²(X × X̂, ℚ) → H^{2k+2}(X × X̂, ℚ)` is injective, as `Ξ_P` is ample" (hard Lefschetz;
`k < n` and `dim(X × X̂) = 2n`).

Departure from the paper (reason 2): the paper invokes the hard Lefschetz theorem for the ample
class `Ξ_P` (Hodge theory, not available in Lean). Here `β_k = c Ξ_P^k` (`c ≠ 0`,
`lemma6_2_3_lowest`) and the injectivity of `Ξ_P^k ∪ (•)` on `⋀² V_ℚ` (`k + 2 ≤ 2n`) is the
algebraic Lefschetz property of the nondegenerate `2`-form `Ξ_P`: the operator `Λ` of the
`sl₂`-triple of `h = Ξ_P^♯` (`s62_lam`, `[Λ, L_h] = 2p - 4n` on `⋀^p V`, from `f² = -d` and
`(f x, y) = -(x, f y)`).
Ampleness (`hample`) is not used. -/
theorem lemma6_2_3_injective (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (x : ExtV ℚ n) (hx : x ∈ ⋀[ℚ]^2 (V ℚ n))
    (h0 : projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * x = 0) : x = 0 := by
  -- `β_k = c Ξ_P^k` with `c ≠ 0`, and `Ξ_P^k ∪ (•)` is injective on `H²` for `k + 2 ≤ 2n` (the
  -- Lefschetz property of the nondegenerate `2`-form `Ξ_P`, from the `sl₂`-triple `(L, Λ, H)`)
  obtain ⟨-, c, hc, hck⟩ := lemma6_2_3_lowest P J hP w₁ w₂ hw₁ hw₂ k hk hkn
  rw [hck, smul_mul_assoc] at h0
  have h1 := (smul_eq_zero.mp h0).resolve_left hc
  have hh := formToExt2_mem ℚ n (P.XiQ hP.isCompl)
  refine s62_sl2_injective ℚ n (s62_lam ℚ n (P.fη hP.isCompl) d) hh ?_
    (s62_lam_one ℚ n _ _) (s62_lam_two ℚ n _ _) k (by omega) hx h1
  exact s62_lam_spec ℚ n hh (P.fη hP.isCompl) d hP.pos.ne' (s62_contractLeft_hClass P hP.isCompl)
    (fun x => by
      have := LinearMap.congr_fun (P.fη_comp_fη hP.isCompl) x
      simpa using this)
    (P.pairing_fη_left hP.isCompl)


/-- (6.2.4) in degree `2k + 2`: `β_{k+1} = ρ_g(β_{k+1}) + c₁(N_g) β_k`, for the lowest degree
`2k` of `β`; hence "the coset `β_{k+1} + β_k ∪ H²` is `Spin(V)_P`-invariant" (TeX lines 2462–2463,
used in `lemma6_2_3`). -/
theorem s62_deg_succ (hP : Assumption2_4_1 P J) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ)
    (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) (c : ExtV ℚ n) (hc2 : c ∈ ⋀[ℚ]^2 (V ℚ n))
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) =
      rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) +
        c * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) := by
  have hlow : ∀ j < k, projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) = 0 := fun j hj => by
    by_contra h; exact absurd (hk.2 h) (by omega)
  have hβk := (lemma6_2_3_lowest P J hP w₁ w₂ hw₁ hw₂ k hk hkn).1 g hg
  have h1 := (s62_projDeg_exp_mul ℚ n hc2 (rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁)) k
    (fun j hj => by rw [s62_projDeg_rhoExt, hlow j hj, map_zero])).2
  rw [← equation6_2_4 P w₁ w₂ hw₁ hw₂ g hg c hc, s62_projDeg_rhoExt, s62_projDeg_rhoExt,
    hβk] at h1
  exact h1

/-- (Proof of Lemma 6.2.3, TeX lines 2462–2464) The pairing `B(x, y) = ∫ x ∧ y ∧ Ξ_P^{2n-2k-2}` of
`H^{2k+2}(X × X̂, ℚ)` is nondegenerate on `N = β_k ∪ H²(X × X̂, ℚ)`, for `β_k = c Ξ_P^k`, `c ≠ 0`,
`k < n`: `B(β_k b, β_k a) = c² ∫ (Ξ_P^{2n-2} ∧ a) ∧ b` (classes of degree `2` are central), the map
`a ↦ Ξ_P^{2n-2} ∧ a` is injective on `H²` (the Lefschetz property of the nondegenerate `2`-form
`Ξ_P`, from the `sl₂`-triple of `h = Ξ_P^♯` as in `lemma6_2_3_injective`) and `∫_{X̂ × X}` is a
perfect pairing (Poincaré duality, by Lemma 6.3.2: `s62_eq_zero_of_integralExt_mul`). -/
theorem s62_pairing_nondeg (hP : Assumption2_4_1 P J) {k : ℕ} (hkn : k < n) {βk : ExtV ℚ n}
    {c : ℚ} (hc : c ≠ 0) (hβk : βk = c • P.hClass hP.isCompl ^ k) {a : ExtV ℚ n}
    (ha : a ∈ ⋀[ℚ]^2 (V ℚ n))
    (h0 : ∀ b ∈ ⋀[ℚ]^2 (V ℚ n),
      integralExt ℚ n (βk * b * (βk * a) * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) = 0) :
    a = 0 := by
  have hh : P.hClass hP.isCompl ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  have hz : P.hClass hP.isCompl ^ (2 * n - 2) * a ∈ ⋀[ℚ]^(4 * n - 2) (V ℚ n) := by
    have := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[ℚ]^i (V ℚ n))
      (s62_pow_mem ℚ n hh (2 * n - 2)) ha
    rwa [show 2 * (2 * n - 2) + 2 = 4 * n - 2 by omega] at this
  -- `∫ (Ξ_P^{2n-2} ∧ a) ∧ b = c⁻² B(β_k b, β_k a) = 0` for all `b ∈ H²`, so `Ξ_P^{2n-2} ∧ a = 0`
  have hz0 : P.hClass hP.isCompl ^ (2 * n - 2) * a = 0 := by
    refine s62_eq_zero_of_integralExt_mul ℚ n (by omega) hz fun b hb => ?_
    rw [show 4 * n - (4 * n - 2) = 2 by omega] at hb
    have hbc : ∀ x, Commute b x := fun x => s62_commute_of_mem_two ℚ n hb x
    have hac : ∀ x, Commute a x := fun x => s62_commute_of_mem_two ℚ n ha x
    have key : βk * b * (βk * a) * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2) =
        (c * c) • (P.hClass hP.isCompl ^ (2 * n - 2) * a * b) := by
      rw [hβk]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      set h := P.hClass hP.isCompl
      calc h ^ k * b * (h ^ k * a) * h ^ (2 * n - 2 * k - 2)
          = h ^ k * (b * (h ^ k * a * h ^ (2 * n - 2 * k - 2))) := by simp only [mul_assoc]
        _ = h ^ k * (h ^ k * a * h ^ (2 * n - 2 * k - 2) * b) := by rw [(hbc _).eq]
        _ = h ^ k * (h ^ k * (a * h ^ (2 * n - 2 * k - 2))) * b := by simp only [mul_assoc]
        _ = h ^ k * (h ^ k * (h ^ (2 * n - 2 * k - 2) * a)) * b := by rw [(hac _).eq]
        _ = h ^ (k + k + (2 * n - 2 * k - 2)) * a * b := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
        _ = h ^ (2 * n - 2) * a * b := by
          rw [show k + k + (2 * n - 2 * k - 2) = 2 * n - 2 by omega]
    have hb0 := h0 b hb
    rw [key, map_smul, smul_eq_mul] at hb0
    exact (mul_eq_zero.mp hb0).resolve_left (mul_ne_zero hc hc)
  -- Lefschetz: `Ξ_P^{2n-2} ∪ (•)` is injective on `H²` (`(2n - 2) + 2 ≤ 2n`)
  refine s62_sl2_injective ℚ n (s62_lam ℚ n (P.fη hP.isCompl) d) hh ?_
    (s62_lam_one ℚ n _ _) (s62_lam_two ℚ n _ _) (2 * n - 2) (by omega) ha hz0
  exact s62_lam_spec ℚ n hh (P.fη hP.isCompl) d hP.pos.ne' (s62_contractLeft_hClass P hP.isCompl)
    (fun x => by
      have := LinearMap.congr_fun (P.fη_comp_fη hP.isCompl) x
      simpa using this)
    (P.pairing_fη_left hP.isCompl)

/-- (Proof of Lemma 6.2.3, TeX lines 2462–2464) "The coset `β_{k+1} + β_k ∪ H²(X × X̂, ℚ)` is
`Spin(V)_P`-invariant. Hence, `β_{k+1}` belongs to the sum of `β_k ∪ H²(X × X̂, ℚ)` and the
`Spin(V)_P`-invariant subspace `H^{2k+2}(X × X̂, ℚ)^{Spin(V)_P}`": for `N = β_k ∪ H²` with
`β_k = c Ξ_P^k`, `c ≠ 0`, `k < n`, if `ρ_g(y) - y ∈ N` for all `g ∈ Spin(V)_P`, then
`y - β_k a₀` is `Spin(V)_P`-invariant for some `a₀ ∈ H²`.

Departure from the paper (reason 2): the paper's "Hence" uses that `N` has a `Spin(V)_P`-invariant
complement in `H^{2k+2}`, i.e. the complete reducibility of the representation of the arithmetic
group `Spin(V)_P` on `H^{2k+2}`, which rests on its Zariski density (not available in Lean). Here
the invariant complement is the orthogonal `N^⊥` of `N` for the pairing
`B(x, y) = ∫ x ∧ y ∧ Ξ_P^{2n-2k-2}` of `H^{2k+2}`, which is `Spin(V)_P`-invariant (`Ξ_P` is
invariant, `s62_rhoExt_hClass`, and `ρ_g` preserves `∫`, `s61_integralExt_rhoExt`) and nondegenerate
on `N` (`s62_pairing_nondeg`). So `y = β_k a₀ + p` with `β_k a₀` the `B`-orthogonal projection of
`y` to `N` (Riesz representation for the nondegenerate restriction of `B` to `N`) and `p ∈ N^⊥`;
`ρ_g(p) - p` lies in `N` (the coset `y + N` is invariant) and in `N^⊥` (`B` and `N` are invariant),
hence vanishes. -/
theorem s62_coset_inv (hP : Assumption2_4_1 P J) {k : ℕ} (hkn : k < n) {βk : ExtV ℚ n} {c : ℚ}
    (hc : c ≠ 0) (hβk : βk = c • P.hClass hP.isCompl ^ k) (y : ExtV ℚ n)
    (hy : ∀ g ∈ P.spinPZ, ∃ a ∈ ⋀[ℚ]^2 (V ℚ n), rhoExt ℚ n g y - y = βk * a) :
    ∃ a ∈ ⋀[ℚ]^2 (V ℚ n), y - βk * a ∈ invariantsExt ℚ n P.spinPZ := by
  have : Module.Finite ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
  have hinvh : ∀ g ∈ P.spinPZ, rhoExt ℚ n g (P.hClass hP.isCompl) = P.hClass hP.isCompl :=
    fun g hg => s62_rhoExt_hClass P J hP g (Subgroup.mem_inf.mp hg).2
  have hinvβ : ∀ g ∈ P.spinPZ, rhoExt ℚ n g βk = βk := fun g hg => by
    rw [hβk, map_smul, map_pow, hinvh g hg]
  -- `B(x, z) = ∫ x ∧ z ∧ Ξ_P^{2n-2k-2}` is `Spin(V)_P`-invariant
  have hB : ∀ g ∈ P.spinPZ, ∀ x z : ExtV ℚ n,
      integralExt ℚ n (rhoExt ℚ n g x * rhoExt ℚ n g z *
        P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) =
        integralExt ℚ n (x * z * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) := by
    intro g hg x z
    rw [← s61_integralExt_rhoExt ℚ n g (x * z * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)),
      map_mul (rhoExt ℚ n g), map_mul (rhoExt ℚ n g), map_pow (rhoExt ℚ n g), hinvh g hg]
  -- the restriction of `B` to `N`, as a bilinear form on `H²` (`b, a ↦ B(β_k b, β_k a)`); it is
  -- nondegenerate
  let C : LinearMap.BilinForm ℚ (⋀[ℚ]^2 (V ℚ n)) :=
    ((LinearMap.mul ℚ (ExtV ℚ n)).compl₁₂
      (LinearMap.mulLeft ℚ βk ∘ₗ (⋀[ℚ]^2 (V ℚ n)).subtype)
      (LinearMap.mulLeft ℚ βk ∘ₗ (⋀[ℚ]^2 (V ℚ n)).subtype)).compr₂
      (integralExt ℚ n ∘ₗ LinearMap.mulRight ℚ (P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)))
  have hCnd : C.flip.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun a ha =>
      Subtype.ext (s62_pairing_nondeg P J hP hkn hc hβk a.2 fun b hb => ha ⟨b, hb⟩)
  -- the `B`-orthogonal projection `β_k a₀` of `y` to `N`: `B(β_k b, β_k a₀) = B(β_k b, y)` for all
  -- `b ∈ H²` (Riesz representation for the nondegenerate form)
  let φ : Module.Dual ℚ (⋀[ℚ]^2 (V ℚ n)) :=
    (integralExt ℚ n ∘ₗ LinearMap.mulRight ℚ (P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) ∘ₗ
      LinearMap.mulRight ℚ y ∘ₗ LinearMap.mulLeft ℚ βk) ∘ₗ (⋀[ℚ]^2 (V ℚ n)).subtype
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ⋀[ℚ]^2 (V ℚ n), a₀ = (C.flip.toDual hCnd).symm φ := ⟨_, rfl⟩
  have hrep : ∀ b ∈ ⋀[ℚ]^2 (V ℚ n),
      integralExt ℚ n (βk * b * (βk * a₀) * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) =
        integralExt ℚ n (βk * b * y * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) := by
    intro b hb
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hCnd) φ ⟨b, hb⟩
    rw [← ha₀] at this
    exact this
  refine ⟨(a₀ : ExtV ℚ n), a₀.2, ?_⟩
  -- `p = y - β_k a₀ ∈ N^⊥`
  have hp : ∀ b ∈ ⋀[ℚ]^2 (V ℚ n),
      integralExt ℚ n (βk * b * (y - βk * a₀) * P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) = 0 := by
    intro b hb
    rw [mul_sub, sub_mul, map_sub, hrep b hb, sub_self]
  intro g hg
  -- `ρ_g(p) - p ∈ N`: the coset `y + N` is invariant
  obtain ⟨a, ha, hya⟩ := hy g hg
  have ha' : a - (rhoExt ℚ n g a₀ - a₀) ∈ ⋀[ℚ]^2 (V ℚ n) :=
    Submodule.sub_mem _ ha (Submodule.sub_mem _ (s62_rhoExt_mem ℚ n g a₀.2) a₀.2)
  have hN : rhoExt ℚ n g (y - βk * a₀) - (y - βk * a₀) = βk * (a - (rhoExt ℚ n g a₀ - a₀)) := by
    rw [map_sub, map_mul, hinvβ g hg, mul_sub, mul_sub, ← hya]
    abel
  -- `ρ_g(p) - p ∈ N^⊥`: `B` is invariant and `N` is `ρ_g`-stable
  have hperp : ∀ b ∈ ⋀[ℚ]^2 (V ℚ n), integralExt ℚ n (βk * b * (βk * (a - (rhoExt ℚ n g a₀ - a₀))) *
      P.hClass hP.isCompl ^ (2 * n - 2 * k - 2)) = 0 := by
    intro b hb
    have hb' : rhoExt ℚ n g⁻¹ b ∈ ⋀[ℚ]^2 (V ℚ n) := s62_rhoExt_mem ℚ n g⁻¹ hb
    have hρb : βk * b = rhoExt ℚ n g (βk * rhoExt ℚ n g⁻¹ b) := by
      rw [map_mul, hinvβ g hg, s62_rhoExt_inv]
    rw [← hN, mul_sub, sub_mul, map_sub, hp b hb, sub_zero, hρb, hB g hg, hp _ hb']
  -- hence `ρ_g(p) = p`
  rw [s62_pairing_nondeg P J hP hkn hc hβk ha' hperp, mul_zero, sub_eq_zero] at hN
  exact hN

/-- The ring identity behind `c₁(N_g) = ρ_g(ℓ) - ℓ` (proof of Lemma 6.2.3): from
`β_{k+1} = ρ_g(β_{k+1}) + c β_k` and `ρ_g(β_{k+1}) + ρ_g(ℓ) β_k = β_{k+1} + ℓ β_k`,
`(c - (ρ_g(ℓ) - ℓ)) β_k = 0`. -/
theorem s62_ring_aux {R : Type*} [Ring R] (B B' ρB' c l ρl : R) (E1 : B' = ρB' + c * B)
    (E2 : ρB' + ρl * B = B' + l * B) : (c - (ρl - l)) * B = 0 := by
  have h1 : c * B = B' - ρB' := by rw [E1]; abel
  have h2 : ρl * B - l * B = B' - ρB' := by
    calc ρl * B - l * B = (ρB' + ρl * B) - (ρB' + l * B) := by abel
      _ = (B' + l * B) - (ρB' + l * B) := by rw [E2]
      _ = B' - ρB' := by abel
  rw [sub_mul, sub_mul, h1, h2, sub_self]

/-- The step of the proof of Lemma 6.2.3 (TeX lines 2472–2481): if `γ = β_{k+1} + ℓ β_k` is
`Spin(V)_P`-invariant (`ℓ ∈ H²`), then `c₁(N_g) = ρ_g(ℓ) - ℓ` for every `g ∈ Spin(V)_P`, by the
injectivity of `β_k ∪ (•)` on `H²`. -/
theorem s62_c1N_of_gamma (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (ℓ : ExtV ℚ n) (hℓ2 : ℓ ∈ ⋀[ℚ]^2 (V ℚ n))
    (hγ : projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) +
      ℓ * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) (c : ExtV ℚ n) (hc2 : c ∈ ⋀[ℚ]^2 (V ℚ n))
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    c = rhoExt ℚ n g ℓ - ℓ := by
  have hlow : ∀ j < k, projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) = 0 := fun j hj => by
    by_contra h; exact absurd (hk.2 h) (by omega)
  have hβk := (lemma6_2_3_lowest P J hP w₁ w₂ hw₁ hw₂ k hk hkn).1 g hg
  -- `β = ch(N_g) ρ_g(β)` ((6.2.4)), in degree `2k + 2`: `β_{k+1} = ρ_g(β_{k+1}) + c₁(N_g) β_k`
  have E1 : projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) =
      rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) +
        c * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) := by
    have h1 := (s62_projDeg_exp_mul ℚ n hc2 (rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁)) k
      (fun j hj => by rw [s62_projDeg_rhoExt, hlow j hj, map_zero])).2
    rw [← equation6_2_4 P w₁ w₂ hw₁ hw₂ g hg c hc, s62_projDeg_rhoExt, s62_projDeg_rhoExt,
      hβk] at h1
    exact h1
  -- the invariance of `γ`: `ρ_g(β_{k+1}) + ρ_g(ℓ) β_k = β_{k+1} + ℓ β_k`
  have E2 := hγ g hg
  rw [map_add, map_mul, hβk] at E2
  have h0 := s62_ring_aux _ _ _ _ _ _ E1 E2
  have hmem : c - (rhoExt ℚ n g ℓ - ℓ) ∈ ⋀[ℚ]^2 (V ℚ n) :=
    Submodule.sub_mem _ hc2 (Submodule.sub_mem _ (s62_rhoExt_mem ℚ n g hℓ2) hℓ2)
  rw [(s62_commute_of_mem_two ℚ n hmem _).eq] at h0
  exact sub_eq_zero.mp (lemma6_2_3_injective P J hP w₁ w₂ hw₁ hw₂ k hk hkn _ hmem h0)

/-- `c₁(N_g) = ρ_g(ℓ) - ℓ` (proof of Lemma 6.2.3; `lemma6_2_3_c1N`). -/
theorem s62_c1N (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (ℓ : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) (c : ExtV ℚ n) (hc2 : c ∈ ⋀[ℚ]^2 (V ℚ n))
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    c = rhoExt ℚ n g ℓ - ℓ := by
  have hℓ2 := P.H2P_le hℓ
  have hlow : ∀ j < k, projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) = 0 := fun j hj => by
    by_contra h; exact absurd (hk.2 h) (by omega)
  -- `γ := β_{k+1} + ℓ β_k` is the degree-`(2k+2)` part of the invariant class `α = exp(ℓ) β`
  have hγ : projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) +
      ℓ * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ := by
    intro g' hg'
    rw [← (s62_projDeg_exp_mul ℚ n hℓ2 _ k hlow).2, ← s62_projDeg_rhoExt, hα g' hg']
  exact s62_c1N_of_gamma P J hP w₁ w₂ hw₁ hw₂ k hk hkn ℓ hℓ2 hγ g hg c hc2 hc

/-- The uniqueness of `ℓ` in Lemma 6.2.3 (`lemma6_2_3_unique`). -/
theorem s62_unique (hP : Assumption2_4_1 P J)
    (w₁ w₂ w₁' w₂' : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (hw₁' : w₁' ∈ P.Pℚ)
    (hw₂' : w₂' ∈ P.Pℚ) (k k' : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (hk' : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂' w₁') ≠ 0} k')
    (hkn' : k' < n) (ℓ ℓ' : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P) (hℓ' : ℓ' ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (hα' : IsNilpotent.exp ℓ' * secantSqClass ℚ n w₂' w₁' ∈ invariantsExt ℚ n P.spinPZ) :
    ℓ = ℓ' := by
  -- `c₁(N_g) = ρ_g(ℓ) - ℓ = ρ_g(ℓ') - ℓ'` for all `g ∈ Spin(V)_P`, so `ℓ - ℓ'` is an invariant
  -- class of `H²_P`, hence `0`
  have hdiff : ℓ - ℓ' ∈ P.H2P ⊓ P.invQ 2 := by
    refine ⟨Submodule.sub_mem _ hℓ hℓ', Submodule.sub_mem _ (P.H2P_le hℓ) (P.H2P_le hℓ'),
      fun g hg => ?_⟩
    obtain ⟨c, hc2, hc⟩ := equation6_1_8 ℚ n g
    have h1 := s62_c1N P J hP w₁ w₂ hw₁ hw₂ k hk hkn ℓ hℓ hα g hg c hc2 hc
    have h2 := s62_c1N P J hP w₁' w₂' hw₁' hw₂' k' hk' hkn' ℓ' hℓ' hα' g hg c hc2 hc
    rw [map_sub, sub_eq_iff_eq_add.mp h1.symm, sub_eq_iff_eq_add.mp h2.symm]
    abel
  rw [P.H2P_inf_invQ hP.pos hP.nonIsotropic, Submodule.mem_bot, sub_eq_zero] at hdiff
  exact hdiff

/-- **Lemma 6.2.3** (`ch-3-alpha-is-second-partial-of-J`). Assume that `k < dim_ℂ(X) = n`. There
exists a unique class `ℓ` of type `(1,1)` in `H²(X × X̂, ℚ)_P` such that the class
`α := exp(ℓ) ch(Φ(F₂ ⊠ F₁^∨))` is `Spin(V)_P`-invariant.

Model: `ch(Φ(F₂ ⊠ F₁^∨)) = φ(w₂ ⊗ τ w₁)` (`secantSqClass ℚ n w₂ w₁`) with `wᵢ = ch(Fᵢ) ∈ P`; `k` the
least `j` with `ch_j ≠ 0`; invariance for the `ρ`-action of the integral group `Spin(V)_P`; "type
`(1,1)`" for the complex structure of `X × X̂`. Setting of §6.2: Assumption 2.4.1 and `Ξ_P` ample
(`hample`, see the module docstring). Reading: "unique class `ℓ` of type `(1,1)` in `H²_P`" is read
literally (uniqueness among the `(1,1)`-classes of `H²_P`); the proof gives uniqueness in all of
`H²_P` (`lemma6_2_3_unique`).

Proof (the paper's, TeX lines 2438–2490): `β = φ(w₂ ⊗ τ w₁)` is `ρ'`-invariant
(`lemma6_2_3_rhoPrime_invariant`, Remark 5.2.3), so `β = ch(N_g) ρ_g(β)` for `g ∈ Spin(V)_P`
((6.2.4), with `c₁(N_g)` the class of (6.1.8), [Orlov, Th. 2.10]); `β_k` is invariant and a non-zero
multiple of `Ξ_P^k` (`lemma6_2_3_lowest`, Lemma 2.2.7) and `β_k ∪ (•)` is injective on `H²`
(`lemma6_2_3_injective`). The coset `β_{k+1} + β_k ∪ H²` is invariant ((6.2.4) in degree `2k + 2`,
`s62_deg_succ`), hence `β_{k+1} = β_k a₀ + p` with `p` invariant (`s62_coset_inv`); writing
`-a₀ = ℓ + ι` with `ℓ ∈ H²_P` and `ι` invariant (`H² = H²_P ⊕ H²^{Spin(V)_P}`,
`KSecant.s62_two_le_sup`; the paper's `H² = H²_P + ℚ Ξ_P`, TeX line 2416), `γ = β_{k+1} + β_k ℓ =
p - β_k ι` is invariant. Then `c₁(N_g) = ρ_g(ℓ) - ℓ` by the injectivity of `β_k ∪ (•)`
(`s62_c1N_of_gamma`), which gives the invariance of `α`, the uniqueness of `ℓ` and its independence
of the `Fᵢ` (`s62_unique`, `lemma6_2_3_unique`), as in the paper.

Departure from the paper (reason 2), at two steps: (a) "Hence, `β_{k+1}` belongs to the sum of
`β_k ∪ H²` and `H^{2k+2}(X × X̂, ℚ)^{Spin(V)_P}`" (TeX lines 2462–2464) uses the complete
reducibility of the representation of the arithmetic group `Spin(V)_P` on `H^{2k+2}` (its Zariski
density, not available in Lean); here the invariant complement of `β_k ∪ H²` is its orthogonal for
the `Spin(V)_P`-invariant pairing `B(x, y) = ∫ x ∧ y ∧ Ξ_P^{2n-2k-2}`, which is nondegenerate on
`β_k ∪ H²` (`s62_coset_inv`, `s62_pairing_nondeg`); (b) the hard Lefschetz theorem for the ample
class `Ξ_P` (TeX line 2458) is replaced by the algebraic Lefschetz property of the
nondegenerate `2`-form `Ξ_P` (`lemma6_2_3_injective`; also used in (a)).

Gap in the paper (filled), reason 1: the paper does not show that `ℓ` is of type `(1,1)`. Here: by
Proposition 6.1.2, the class `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` satisfies (6.1.8) for `g`, so it equals
`ρ_g(ℓ) - ℓ` (`s62_c1N_of_gamma`); thus `ℓ + ½ c₁(𝒫)` is `Spin(V)_P`-invariant, hence a Hodge class
(Lemma 2.2.7), and `c₁(𝒫)` is of type `(1,1)`. (So `ℓ` is the `H²_P`-component of `-½ c₁(𝒫)`, the
claim of the proof of Lemma 6.2.5, `ell_eq_proj_c1P`.) Proposition 6.1.2 is proved here without
Lemma 6.2.3 (authorized departure, `proposition6_1_2`), so this is not circular; it is used only for
the type of `ℓ`. -/
theorem lemma6_2_3 (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n) :
    ∃! ℓ : ExtV ℚ n, ℓ ∈ hodgeClassesV n (productStructure n J) 1 ∧ ℓ ∈ P.H2P ∧
      IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ := by
  -- `β_k` is invariant and `β_k = c Ξ_P^k` with `c ≠ 0` (`k < dim X`)
  obtain ⟨hβk, c, hc0, hck⟩ := lemma6_2_3_lowest P J hP w₁ w₂ hw₁ hw₂ k hk hkn
  -- "The coset `β_{k+1} + β_k ∪ H²` is `Spin(V)_P`-invariant": by (6.2.4) in degree `2k + 2`,
  -- `ρ_g(β_{k+1}) - β_{k+1} = -c₁(N_g) β_k`, with `c₁(N_g)` the class of (6.1.8)
  have hcoset : ∀ g ∈ P.spinPZ, ∃ a ∈ ⋀[ℚ]^2 (V ℚ n),
      rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) -
        projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) =
        projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * a := by
    intro g hg
    obtain ⟨cg, hcg2, hcg⟩ := equation6_1_8 ℚ n g
    have E1 := s62_deg_succ P J hP w₁ w₂ hw₁ hw₂ k hk hkn g hg cg hcg2 hcg
    refine ⟨-cg, neg_mem hcg2, ?_⟩
    calc rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) -
          projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)
        = rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) -
          (rhoExt ℚ n g (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁)) +
            cg * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁)) := by rw [← E1]
      _ = projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * -cg := by
        rw [mul_neg, ← (s62_commute_of_mem_two ℚ n hcg2 _).eq]
        abel
  -- "Hence, `β_{k+1}` belongs to the sum of `β_k ∪ H²` and `H^{2k+2}(X × X̂, ℚ)^{Spin(V)_P}`"
  -- (departure (a): an invariant pairing instead of complete reducibility, see the docstring)
  obtain ⟨a₀, ha₀, hp⟩ := s62_coset_inv P J hP hkn hc0 hck _ hcoset
  -- "Thus, there exists `ℓ ∈ H²_P` such that `γ := β_{k+1} + β_k ℓ` is invariant": with
  -- `H² = H²_P ⊕ H²^{Spin(V)_P}`, write `-a₀ = ℓ + ι`; then `γ = (β_{k+1} - β_k a₀) - β_k ι`
  obtain ⟨ℓ, hℓ, ι, hι, hdec⟩ : ∃ ℓ ∈ P.H2P, ∃ ι ∈ P.invQ 2, ℓ + ι = -a₀ :=
    Submodule.mem_sup.mp (P.s62_two_le_sup hP.pos hP.nonIsotropic (neg_mem ha₀))
  have hℓ2 := P.H2P_le hℓ
  have hγ : projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) +
      ℓ * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ := by
    have heq : projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) +
        ℓ * projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) =
        (projDeg ℚ n (2 * k + 2) (secantSqClass ℚ n w₂ w₁) -
          projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * a₀) -
          projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * ι := by
      rw [(s62_commute_of_mem_two ℚ n hℓ2 _).eq, show ℓ = -a₀ - ι by rw [← hdec]; abel, mul_sub,
        mul_neg]
      abel
    rw [heq]
    intro g hg
    rw [map_sub, hp g hg, map_mul, hβk g hg, hι.2 g hg]
  -- `c₁(N_g) = ρ_g(ℓ) - ℓ` (injectivity of `β_k ∪ (•)`), hence `α = exp(ℓ) β` is invariant
  have hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ := by
    intro g hg
    obtain ⟨cg, hcg2, hcg⟩ := equation6_1_8 ℚ n g
    have hcℓ := s62_c1N_of_gamma P J hP w₁ w₂ hw₁ hw₂ k hk hkn ℓ hℓ2 hγ g hg cg hcg2 hcg
    have hβ := equation6_2_4 P w₁ w₂ hw₁ hw₂ g hg cg hcg
    have hρβ : rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) =
        IsNilpotent.exp (-cg) * secantSqClass ℚ n w₂ w₁ := by
      conv_rhs => rw [hβ]
      rw [← mul_assoc, s62_exp_neg_mul ℚ n hcg2, one_mul]
    rw [map_mul, s62_rhoExt_exp ℚ n g hℓ2, hρβ, ← mul_assoc,
      ← s62_exp_add ℚ n (s62_rhoExt_mem ℚ n g hℓ2) (neg_mem hcg2), hcℓ,
      show rhoExt ℚ n g ℓ + -(rhoExt ℚ n g ℓ - ℓ) = ℓ by abel]
  refine ⟨ℓ, ⟨?_, hℓ, hα⟩, fun ℓ' ⟨_, hℓ', hα'⟩ =>
    s62_unique P J hP w₁ w₂ w₁ w₂ hw₁ hw₂ hw₁ hw₂ k k hk hkn hk hkn ℓ' ℓ hℓ' hℓ
      hα' hα⟩
  -- gap in the paper (filled): `ℓ` is of type `(1,1)`. By Proposition 6.1.2,
  -- `½[c₁(𝒫) - ρ_g(c₁(𝒫))]` satisfies (6.1.8), so it is `ρ_g(ℓ) - ℓ`: `ℓ + ½c₁(𝒫)` is invariant,
  -- hence a Hodge class (Lemma 2.2.7); and `c₁(𝒫)` is of type `(1,1)`
  have hc := s62_c1P_mem ℚ n
  have hc' : (2 : ℚ)⁻¹ • c1P ℚ n ∈ ⋀[ℚ]^2 (V ℚ n) := Submodule.smul_mem _ _ hc
  have hinv' : ℓ + (2 : ℚ)⁻¹ • c1P ℚ n ∈ P.invQ 2 := by
    refine ⟨Submodule.add_mem _ hℓ2 hc', fun g hg => ?_⟩
    have hcg : (2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)) ∈ ⋀[ℚ]^2 (V ℚ n) :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hc (s62_rhoExt_mem ℚ n g hc))
    have h1 := s62_c1N_of_gamma P J hP w₁ w₂ hw₁ hw₂ k hk hkn ℓ hℓ2 hγ g hg _ hcg
      (proposition6_1_2 ℚ n g)
    rw [map_add, map_smul]
    calc rhoExt ℚ n g ℓ + (2 : ℚ)⁻¹ • rhoExt ℚ n g (c1P ℚ n)
        = (rhoExt ℚ n g ℓ - ℓ) + ℓ + (2 : ℚ)⁻¹ • rhoExt ℚ n g (c1P ℚ n) := by abel
      _ = ℓ + (2 : ℚ)⁻¹ • c1P ℚ n := by rw [← h1, smul_sub]; abel
  have hℓeq : ℓ = (ℓ + (2 : ℚ)⁻¹ • c1P ℚ n) - (2 : ℚ)⁻¹ • c1P ℚ n := by abel
  rw [hℓeq]
  exact Submodule.sub_mem _
    (lemma2_2_7_hodge P hP.pos hP.nonIsotropic J hP.isComplex hP.hodge 1 hinv')
    (Submodule.smul_mem _ _ (s62_c1P_hodge J hP.isComplex))

/-- **Lemma 6.2.3** (`ch-3-alpha-is-second-partial-of-J`), last sentence: "The class `ℓ` depends on
the secant line `P`, but not on the choice of `Fᵢ`, `i = 1, 2`." If `(w₁, w₂)` and `(w₁', w₂')` are
two pairs of classes in `P` satisfying the hypothesis of the lemma, and `ℓ, ℓ' ∈ H²_P` make
`exp(ℓ) φ(w₂ ⊗ τ w₁)` and `exp(ℓ') φ(w₂' ⊗ τ w₁')` invariant, then `ℓ = ℓ'`. (With
`(w₁', w₂') = (w₁, w₂)`, this is the uniqueness of `ℓ` in `H²_P` proved in the paper.) -/
theorem lemma6_2_3_unique (hP : Assumption2_4_1 P J)
    (w₁ w₂ w₁' w₂' : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (hw₁' : w₁' ∈ P.Pℚ)
    (hw₂' : w₂' ∈ P.Pℚ) (k k' : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (hk' : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂' w₁') ≠ 0} k')
    (hkn' : k' < n) (ℓ ℓ' : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P) (hℓ' : ℓ' ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (hα' : IsNilpotent.exp ℓ' * secantSqClass ℚ n w₂' w₁' ∈ invariantsExt ℚ n P.spinPZ) :
    ℓ = ℓ' :=
  s62_unique P J hP w₁ w₂ w₁' w₂' hw₁ hw₂ hw₁' hw₂' k k' hk hkn hk' hkn' ℓ ℓ' hℓ hℓ' hα hα'

/-- (Proof of Lemma 6.2.3, TeX lines 2478–2481) `c₁(N_g) = ρ_g(ℓ) - ℓ` for all `g ∈ Spin(V)_P`, where
`ℓ` is the class of Lemma 6.2.3 and `c₁(N_g) = c` is the class of (6.1.8)
(`ρ'_g = exp(c) ∪ ρ_g`). -/
theorem lemma6_2_3_c1N (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (ℓ : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) (c : ExtV ℚ n) (hc2 : c ∈ ⋀[ℚ]^2 (V ℚ n))
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    c = rhoExt ℚ n g ℓ - ℓ :=
  s62_c1N P J hP w₁ w₂ hw₁ hw₂ k hk hkn ℓ hℓ hα g hg c hc2 hc

end Lemma623

/-! ## Remark 6.2.4 -/

/-- **Remark 6.2.4** (`remark-k-equal-0-case`). Assume `k = 0`, so that the rank `r` of
`Φ(F₂ ⊠ F₁^∨)` is non-zero, and set `β₁ = c₁(Φ(F₂ ⊠ F₁^∨))`. The class
`κ(Φ(F₂ ⊠ F₁^∨)) = exp(-β₁/r) ch(Φ(F₂ ⊠ F₁^∨))` is then `Spin(V)_P`-invariant, by Lemma 6.2.3; and
there is a unique scalar `t` such that `(t Ξ_P - β₁)/r` belongs to `H²(X × X̂, ℚ)_P` (the class `ℓ`,
`remark6_2_4_ell`).

Model: `β = φ(w₂ ⊗ τ w₁)`, `r = rankExt β`, `β₁ = projDeg 2 β`, `Ξ_P = hClass`; setting of §6.2.
The existence of `t` uses `H² = H²_P + ℚ Ξ_P`, hence the standing assumption `n ≥ 2`. -/
theorem remark6_2_4 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x) (hn : 2 ≤ n)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₂ w₁) ≠ 0) :
    kappa ℚ n (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ ∧
      ∃! t : ℚ, (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
          (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) ∈ P.H2P := by
  have hh := s62_hClass_mem_invQ P J hP
  have hh0 := s62_hClass_ne_zero P hP.isCompl (by omega)
  -- `k = 0`: Lemma 6.2.3 gives `ℓ ∈ H²_P` with `exp(ℓ) β` invariant
  have hk0 : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} 0 := by
    refine ⟨?_, fun j _ => Nat.zero_le j⟩
    show projDeg ℚ n (2 * 0) (secantSqClass ℚ n w₂ w₁) ≠ 0
    rw [mul_zero, s62_projDeg_zero]
    exact (map_ne_zero _).mpr hr
  obtain ⟨ℓ, ⟨-, hℓ, hα⟩, -⟩ := lemma6_2_3 P J hP w₁ w₂ hw₁ hw₂ 0 hk0 (by omega)
  have hℓ2 := P.H2P_le hℓ
  -- its degree-`2` part `β₁ + r ℓ` is invariant, hence a multiple `t Ξ_P` (Lemma 2.2.7)
  have hdeg2 : projDeg ℚ n 2 (IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁) =
      projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁) + rankExt ℚ n (secantSqClass ℚ n w₂ w₁) • ℓ := by
    have h := (s62_projDeg_exp_mul ℚ n hℓ2 (secantSqClass ℚ n w₂ w₁) 0
      (fun j hj => absurd hj (Nat.not_lt_zero _))).2
    simp only [mul_zero, zero_add] at h
    rw [h, s62_projDeg_zero, ← Algebra.commutes, ← Algebra.smul_def]
  have hinv2 : projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁) +
      rankExt ℚ n (secantSqClass ℚ n w₂ w₁) • ℓ ∈ P.invQ 2 := by
    refine ⟨Submodule.add_mem _ (s62_projDeg_mem ℚ n 2 _) (Submodule.smul_mem _ _ hℓ2),
      fun g hg => ?_⟩
    rw [← hdeg2, ← s62_projDeg_rhoExt, hα g hg]
  have hspan := lemma2_2_7_note_pow P hP.pos hn hP.nonIsotropic _ hh hh0 1 (by omega) (by omega)
  rw [mul_one, pow_one] at hspan
  rw [hspan, Submodule.mem_span_singleton] at hinv2
  obtain ⟨t, ht⟩ := hinv2
  -- `ℓ = (t Ξ_P - β₁)/r`
  have hℓeq : ℓ = (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
      (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) := by
    rw [ht, add_sub_cancel_left, inv_smul_smul₀ hr]
  constructor
  · -- `κ = exp(-β₁/r) β = exp(-(t/r) Ξ_P) exp(ℓ) β` is invariant
    intro g hg
    have hth : (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ • t • P.hClass hP.isCompl ∈
        ⋀[ℚ]^2 (V ℚ n) := Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hh.1)
    have hκ : kappa ℚ n (secantSqClass ℚ n w₂ w₁) =
        IsNilpotent.exp (-((rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ • t • P.hClass hP.isCompl)) *
          (IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁) := by
      rw [kappa, ← mul_assoc, ← s62_exp_add ℚ n (neg_mem hth) hℓ2, hℓeq, smul_sub, neg_smul]
      congr 2
      abel
    rw [hκ, map_mul, hα g hg, s62_rhoExt_exp ℚ n g (neg_mem hth), map_neg, map_smul, map_smul,
      s62_rhoExt_hClass P J hP g (Subgroup.mem_inf.mp hg).2]
  · -- `t` is unique: `H²_P ∩ ℚ Ξ_P = 0`
    have hmemt : (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
        (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) ∈ P.H2P := by
      rw [← hℓeq]; exact hℓ
    refine ⟨t, hmemt, fun t' ht' => ?_⟩
    have hdiff : ((rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ * (t' - t)) • P.hClass hP.isCompl ∈
        P.H2P ⊓ P.invQ 2 := by
      have hsub := Submodule.sub_mem _ ht' hmemt
      rw [← smul_sub, sub_sub_sub_cancel_right, ← sub_smul, smul_smul] at hsub
      exact Submodule.mem_inf.mpr ⟨hsub, Submodule.smul_mem _ _ hh⟩
    rw [P.H2P_inf_invQ hP.pos hP.nonIsotropic, Submodule.mem_bot, smul_eq_zero] at hdiff
    rcases hdiff with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (inv_eq_zero.mp h) hr
      · exact sub_eq_zero.mp h
    · exact absurd h hh0

/-- **Remark 6.2.4** (`remark-k-equal-0-case`), last sentence: "In this case `ℓ = (t Ξ_P - β₁)/r`,
where `t` is the unique scalar such that `ℓ` belongs to `H²(X × X̂, ℚ)_P`": every `ℓ ∈ H²_P` making
`exp(ℓ) β` invariant (the class of Lemma 6.2.3) is `(t Ξ_P - β₁)/r` for this `t`. -/
theorem remark6_2_4_ell (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (w₁ w₂ : S ℚ n)     (hr : rankExt ℚ n (secantSqClass ℚ n w₂ w₁) ≠ 0) (t : ℚ)
    (ht : (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
        (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) ∈ P.H2P)
    (ℓ : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ) :
    ℓ = (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
      (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) := by
  -- the degree-`2` part `β₁ + r ℓ` of `exp(ℓ) β` is invariant
  have hℓ2 : ℓ ∈ ⋀[ℚ]^2 (V ℚ n) := P.H2P_le hℓ
  have hdeg2 : projDeg ℚ n 2 (IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁) =
      projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁) + rankExt ℚ n (secantSqClass ℚ n w₂ w₁) • ℓ := by
    have h := (s62_projDeg_exp_mul ℚ n hℓ2 (secantSqClass ℚ n w₂ w₁) 0
      (fun j hj => absurd hj (Nat.not_lt_zero _))).2
    simp only [mul_zero, zero_add] at h
    rw [h, s62_projDeg_zero, ← Algebra.commutes, ← Algebra.smul_def]
  have hinv2 : projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁) +
      rankExt ℚ n (secantSqClass ℚ n w₂ w₁) • ℓ ∈ P.invQ 2 := by
    refine ⟨Submodule.add_mem _ (s62_projDeg_mem ℚ n 2 _) (Submodule.smul_mem _ _ hℓ2),
      fun g hg => ?_⟩
    rw [← hdeg2, ← s62_projDeg_rhoExt, hα g hg]
  -- `ℓ - (t Ξ_P - β₁)/r` is an invariant class of `H²_P`, hence `0`
  have hdiff : ℓ - (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
      (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) ∈
        P.H2P ⊓ P.invQ 2 := by
    refine ⟨Submodule.sub_mem _ hℓ ht, ?_⟩
    have heq : ℓ - (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
        (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) =
        (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ • (projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁) +
          rankExt ℚ n (secantSqClass ℚ n w₂ w₁) • ℓ) -
          ((rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ * t) • P.hClass hP.isCompl := by
      rw [smul_sub, smul_add, inv_smul_smul₀ hr, smul_smul]
      abel
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hinv2)
      (Submodule.smul_mem _ _ (s62_hClass_mem_invQ P J hP))
  rw [P.H2P_inf_invQ hP.pos hP.nonIsotropic, Submodule.mem_bot, sub_eq_zero] at hdiff
  exact hdiff

/-! ## Lemma 6.2.5 -/

section Lemma625

variable (F : Type*) [Field F] [CharZero F]

/-- **Lemma 6.2.5** (`example-conjecture-holds-for-abelian-surfaces`). Proposition 6.1.2 holds in case
`X` is an abelian surface (`n = 2`): `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`.

Departure from the paper (reason 2; authorized with Proposition 6.1.2, `notes/design.md`): the
paper's proof (TeX lines 2537–2575) takes for `F₁, F₂` ideal sheaves of length-`n` subschemes of `X`
(Chern character `w_n = (1, 0, -n)`), computes the first graded summands of the Chern character of
`E = Rπ_{23,*}(π₁^*F₁^∨ ⊗ 𝓕₂)` by the proof of [Markman, generalized Kummers, Prop. 11.2],
identifies the class `ℓ` of Lemma 6.2.3 with the projection of `-c₁(𝒫)/2` to `H²_P` by
Remark 6.2.4, deduces (6.2.5) for `g ∈ Spin(V)_P`, extends it by the cocycle identity (6.1.9) to the
subgroup `Γ ⊆ Spin(V)` generated by these groups `Spin(V)_P`, and concludes by the Zariski density
of `Γ` in `Spin(V_ℚ)` ([Verbitsky, Th. 2.1]). The sheaves, the Chern character computation and the
Zariski density are not available in Lean. Here Proposition 6.1.2 is proved for every `n` by the
authorized algebraic argument (`proposition6_1_2`), and this lemma is its case `n = 2`. As there,
`g` ranges over `Spin(V_F)` for every field `F` of characteristic `0` (the paper: the integral
`Spin(V)`). -/
theorem lemma6_2_5 (g : Spin F 2) (x : ExtV F 2) :
    rhoPrime F 2 g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F 2 - rhoExt F 2 g (c1P F 2))) * rhoExt F 2 g x :=
  proposition6_1_2 F 2 g x

/-- **(6.2.5)** (`eq-c-1-N-g`): `c₁(N_g) = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]` (abelian surfaces), where `c₁(N_g)`
is the class of (6.1.8) (`ρ'_g = exp(c₁(N_g)) ∪ ρ_g`, `c₁(N_g) ∈ H²`). The paper derives it for
`g ∈ Spin(V)_P` and every negative definite rational plane `P` containing `w_n`; in the model it holds
for every `g ∈ Spin(V_F)` (Proposition 6.1.2), which is what the paper concludes.

Departure from the paper (reason 2; part of the authorized departure for Lemma 6.2.5): the paper
obtains (6.2.5) from the Chern character of `Rπ_{23,*}(π₁^*F₁^∨ ⊗ 𝓕₂)` for ideal sheaves of points
and Remark 6.2.4; here it follows from Lemma 6.2.5 (Proposition 6.1.2) applied to `1`, since
`c₁(N_g)` is determined by `ρ'_g(1) = exp(c₁(N_g))`. -/
theorem equation6_2_5 (g : Spin F 2) (c : ExtV F 2) (hc2 : c ∈ ⋀[F]^2 (V F 2))
    (hc : ∀ x : ExtV F 2, rhoPrime F 2 g x = IsNilpotent.exp c * rhoExt F 2 g x) :
    c = (2 : F)⁻¹ • (c1P F 2 - rhoExt F 2 g (c1P F 2)) := by
  -- the class `c₁(N_g)` of (6.1.8) is unique: `ρ'_g(1) = exp(c₁(N_g))`; Lemma 6.2.5 gives
  -- `ρ'_g(1) = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))])`
  have hc' : (2 : F)⁻¹ • (c1P F 2 - rhoExt F 2 g (c1P F 2)) ∈ ⋀[F]^2 (V F 2) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (s62_c1P_mem F 2)
      (s62_rhoExt_mem F 2 g (s62_c1P_mem F 2)))
  have h1 := hc 1
  rw [lemma6_2_5 F g 1, map_one, mul_one, mul_one] at h1
  have h2 := congrArg (projDeg F 2 2) h1
  rwa [s62_projDeg_two_exp F 2 hc', s62_projDeg_two_exp F 2 hc2, eq_comm] at h2

end Lemma625

/-- (Proof of Lemma 6.2.5, TeX lines 2557–2558: "The class `ℓ` is the projection of `-c₁(𝒫)/2` to
`H²(X × X̂, ℚ)_P`, by Remark 6.2.4.") In the model this holds for every `n` and every pair of classes
of `P` (a consequence of Proposition 6.1.2): with `-½ c₁(𝒫) = ℓ₀ + t Ξ_P`, `ℓ₀ ∈ H²_P`, the class `ℓ`
of Lemma 6.2.3 is `ℓ₀`. Stated: `ℓ₀ := -½ c₁(𝒫) - t h ∈ H²_P` makes `exp(ℓ₀) φ(w₂ ⊗ τ w₁)` invariant
for all `w₁, w₂ ∈ P`. (Checked numerically for `n = 2, 3`.) -/
theorem ell_eq_proj_c1P (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (t : ℚ)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) :
    IsNilpotent.exp (-((2 : ℚ)⁻¹ • c1P ℚ n) - t • P.hClass hP.isCompl) *
      secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ := by
  intro g hg
  have hc := s62_c1P_mem ℚ n
  have hh : P.hClass hP.isCompl ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  have hhg := s62_rhoExt_hClass P J hP g (Subgroup.mem_inf.mp hg).2
  have hℓ₀ : -((2 : ℚ)⁻¹ • c1P ℚ n) - t • P.hClass hP.isCompl ∈ ⋀[ℚ]^2 (V ℚ n) :=
    Submodule.sub_mem _ (neg_mem (Submodule.smul_mem _ _ hc)) (Submodule.smul_mem _ _ hh)
  have hδ : (2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)) ∈ ⋀[ℚ]^2 (V ℚ n) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hc (s62_rhoExt_mem ℚ n g hc))
  -- `β = ρ'_g β = exp(½[c₁(𝒫) - ρ_g c₁(𝒫)]) ρ_g β` (Proposition 6.1.2)
  have hβ := lemma6_2_3_rhoPrime_invariant P w₁ w₂ hw₁ hw₂ g hg
  rw [proposition6_1_2] at hβ
  have hρβ : rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) =
      IsNilpotent.exp (-((2 : ℚ)⁻¹ • (c1P ℚ n - rhoExt ℚ n g (c1P ℚ n)))) *
        secantSqClass ℚ n w₂ w₁ := by
    conv_rhs => rw [← hβ]
    rw [← mul_assoc, s62_exp_neg_mul ℚ n hδ, one_mul]
  rw [map_mul, s62_rhoExt_exp ℚ n g hℓ₀, hρβ, ← mul_assoc,
    ← s62_exp_add ℚ n (s62_rhoExt_mem ℚ n g hℓ₀) (neg_mem hδ)]
  congr 2
  rw [map_sub, map_neg, map_smul, map_smul, hhg, smul_sub]
  abel

/-! ## Lemma 6.2.6 -/

/-- **Lemma 6.2.6(1)** (`lemma-Spin-V-ell-1-ell-2-invariance-conditions`). Let `E` be an object of
`Dᵇ(X × X̂)` of non-zero rank `r` and `G` a subgroup of `Spin(V)`. The class `ch(E)` is
`G`-`ρ'`-invariant if and only if both `κ(E)` and `c₁(E) - (r/2) c₁(𝒫)` are `G`-`ρ`-invariant.

Model: `ch(E)` is any class `x ∈ ⋀• V_F` with `r = rankExt x ≠ 0`, `c₁(E) = projDeg 2 x`. Reading:
stated for a subgroup `G` of `Spin(V_F)` over every field `F` of characteristic `0` (the paper's
`G ⊆ Spin(V)` is the case `F = ℚ`; part (2) applies part (1) to `Spin(V_K)_{ℓ₁,ℓ₂}`). -/
theorem lemma6_2_6_1 (F : Type*) [Field F] [CharZero F] (n : ℕ) (G : Subgroup (Spin F n))
    (x : ExtV F n) (hr : rankExt F n x ≠ 0) :
    (∀ g ∈ G, rhoPrime F n g x = x) ↔
      (∀ g ∈ G, rhoExt F n g (kappa F n x) = kappa F n x) ∧
        ∀ g ∈ G, rhoExt F n g (projDeg F n 2 x - (rankExt F n x / 2) • c1P F n) =
          projDeg F n 2 x - (rankExt F n x / 2) • c1P F n := by
  have hc : c1P F n ∈ ⋀[F]^2 (V F n) := s62_c1P_mem F n
  have hc' : (2 : F)⁻¹ • c1P F n ∈ ⋀[F]^2 (V F n) := Submodule.smul_mem _ _ hc
  -- `y = ch(E) ∪ exp(-c₁(𝒫)/2) = r + [c₁(E) - (r/2) c₁(𝒫)] + ⋯`
  obtain ⟨y, hy_def⟩ : ∃ y, y = IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n)) * x := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁_def⟩ : ∃ y₁, y₁ = projDeg F n 2 x - (rankExt F n x / 2) • c1P F n := ⟨_, rfl⟩
  have hy₁ : y₁ ∈ ⋀[F]^2 (V F n) := hy₁_def ▸
    Submodule.sub_mem _ (s62_projDeg_mem F n 2 x) (Submodule.smul_mem _ _ hc)
  have hy₁' : (rankExt F n x)⁻¹ • y₁ ∈ ⋀[F]^2 (V F n) := Submodule.smul_mem _ _ hy₁
  have hy2 : projDeg F n 2 y = y₁ := by
    have h := (s62_projDeg_exp_mul F n (neg_mem hc') x 0
      (fun j hj => absurd hj (Nat.not_lt_zero _))).2
    simp only [mul_zero, zero_add] at h
    rw [hy_def, h, s62_projDeg_zero, hy₁_def, ← Algebra.commutes, ← Algebra.smul_def, smul_neg,
      smul_smul, ← sub_eq_add_neg, div_eq_mul_inv]
  -- `κ(E) = exp(-y₁/r) y`
  have hκ : kappa F n x = IsNilpotent.exp (-((rankExt F n x)⁻¹ • y₁)) * y := by
    rw [hy_def, ← mul_assoc, ← s62_exp_add F n (neg_mem hy₁') (neg_mem hc'), kappa]
    congr 2
    have hr2 : (rankExt F n x)⁻¹ * (rankExt F n x / 2) = 2⁻¹ := by field_simp
    rw [hy₁_def, smul_sub, smul_smul, hr2, neg_sub, neg_smul]
    abel
  have hy_eq : y = IsNilpotent.exp ((rankExt F n x)⁻¹ • y₁) * kappa F n x := by
    rw [hκ, ← mul_assoc, s62_exp_mul_neg F n hy₁', one_mul]
  -- for each `g`: `ρ'_g ch(E) = ch(E)` iff `ρ_g y = y` iff `κ(E)` and `y₁` are `ρ_g`-invariant
  have key : ∀ g : Spin F n, rhoPrime F n g x = x ↔
      rhoExt F n g (kappa F n x) = kappa F n x ∧ rhoExt F n g y₁ = y₁ := by
    intro g
    rw [s62_rhoPrime_fixed_iff, ← hy_def]
    constructor
    · intro h
      have h1 : rhoExt F n g y₁ = y₁ := by
        rw [← hy2, ← s62_projDeg_rhoExt, h]
      refine ⟨?_, h1⟩
      rw [hκ, map_mul, h, s62_rhoExt_exp F n g (neg_mem hy₁'), map_neg, map_smul, h1]
    · rintro ⟨h1, h2⟩
      rw [hy_eq, map_mul, h1, s62_rhoExt_exp F n g hy₁', map_smul, h2]
  constructor
  · intro h
    exact ⟨fun g hg => ((key g).mp (h g hg)).1, fun g hg => hy₁_def ▸ ((key g).mp (h g hg)).2⟩
  · rintro ⟨h1, h2⟩ g hg
    exact (key g).mpr ⟨h1 g hg, hy₁_def ▸ h2 g hg⟩


/-- **Lemma 6.2.6(2)** (`lemma-Spin-V-ell-1-ell-2-invariance-conditions`). Assume that `ch(E)` is
`Spin(V)_P`-`ρ'`-invariant. Then `ch(E)` is `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ'`-invariant if and only if `κ(E)`
is `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ`-invariant.

Model: `ch(E) = x ∈ ⋀• V_ℚ` with `rankExt x ≠ 0`; `Spin(V)_P` the integral group (`P.spinPZ`);
`Spin(V_K)_{ℓ₁,ℓ₂}` (`P.spinL₁L₂`, "the group appearing in Lemma 2.2.7") acts on the base change
`x_K` (`bcExt`). Hypotheses of Lemma 2.2.7, which the proof uses for `H²`: `P` non-isotropic, `d > 0`,
and `n ≥ 2` (for `n = 1`, `H²` is the middle degree and its invariants are not a trivial character). -/
theorem lemma6_2_6_2 (P : KSecant n d) (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (x : ExtV ℚ n) (hr : rankExt ℚ n x ≠ 0) (hx : ∀ g ∈ P.spinPZ, rhoPrime ℚ n g x = x) :
    (∀ g ∈ P.spinL₁L₂, rhoPrime (Kd d) n g (bcExt ℚ (Kd d) n x) = bcExt ℚ (Kd d) n x) ↔
      ∀ g ∈ P.spinL₁L₂,
        rhoExt (Kd d) n g (bcExt ℚ (Kd d) n (kappa ℚ n x)) = bcExt ℚ (Kd d) n (kappa ℚ n x) := by
  -- part (1) for `Spin(V)_P`: `c₁(E) - (r/2) c₁(𝒫)` is `Spin(V)_P`-`ρ`-invariant ...
  have h1 := ((lemma6_2_6_1 ℚ n P.spinPZ x hr).mp hx).2
  have hmem : projDeg ℚ n 2 x - (rankExt ℚ n x / 2) • c1P ℚ n ∈ P.invQ (2 * 1) :=
    ⟨Submodule.sub_mem _ (s62_projDeg_mem ℚ n 2 x) (Submodule.smul_mem _ _ (s62_c1P_mem ℚ n)),
      h1⟩
  -- ... hence also `Spin(V_K)_{ℓ₁,ℓ₂}`-`ρ`-invariant, by Lemma 2.2.7
  have h2 := fun (g : Spin (Kd d) n) (hg : g ∈ P.spinL₁L₂) =>
    lemma2_2_7_trivial P hd hP 1 (by omega) (by omega) _ hmem ⟨g, hg⟩
  have hrK : rankExt (Kd d) n (bcExt ℚ (Kd d) n x) ≠ 0 := by
    rw [s62_rankExt_bcExt]; exact (map_ne_zero _).mpr hr
  have hbc : bcExt ℚ (Kd d) n (projDeg ℚ n 2 x - (rankExt ℚ n x / 2) • c1P ℚ n) =
      projDeg (Kd d) n 2 (bcExt ℚ (Kd d) n x) -
        (rankExt (Kd d) n (bcExt ℚ (Kd d) n x) / 2) • c1P (Kd d) n := by
    rw [map_sub, map_smul, s62_projDeg_bcExt, s62_rankExt_bcExt, s62_bcExt_c1P,
      algebra_compatible_smul (Kd d), map_div₀, map_ofNat]
  -- part (1) for `Spin(V_K)_{ℓ₁,ℓ₂}`
  rw [lemma6_2_6_1 (Kd d) n P.spinL₁L₂ _ hrK, s62_bcExt_kappa]
  exact ⟨fun h => h.1, fun h => ⟨h, fun g hg => hbc ▸ h2 g hg⟩⟩

end WeilClasses
