module

public import WeilClasses.PureSpinor.Stabilizer
public import WeilClasses.PureSpinor.Lemma2_2_4
public import WeilClasses.PureSpinor.Lemma2_2_6
import WeilClasses.External.Chevalley.Sec3

/-!
# Weight decompositions of `⋀• V` and Lemma 2.2.7 (paper §2.2, end)

Setting: a rational `K`-secant `P` (`WeilClasses.KSecant`) which is non-isotropic, so that
`V_K = W₁ ⊕ W₂` and `K` acts on `V_ℚ` by `η` (2.2.4).

## Main definitions

* `WeilClasses.pqPiece A B p q`: the subspace `⋀^p A ∧ ⋀^q B ⊆ ⋀^{p+q} M` spanned by products of
  `p` vectors of `A` and `q` vectors of `B` (the foundation's `pqPiece`, over any field); for
  `A = W₁`, `B = W₂` this is the paper's `⋀^p W₁ ⊗ ⋀^q W₂`.
* `WeilClasses.weightSpaceK d act a b`: for an action `λ ↦ act λ` of `K^×` on a `K`-vector space `U`
  (the paper's `U_K = U ⊗_ℚ K`, with the `K`-linear extension of the action), the subspace
  `U_{a,b}` on which `λ` acts by `λ^a σ(λ)^b`.
* `KSecant.ηExt`: the action `⋀ η_λ` of `λ ∈ K` on `⋀• V_K`; `KSecant.wedgeAB`:
  `⋀_{a,b} V := (⋀^{a+b} V)_{a,b}`; `KSecant.wedgePQAB`: `⋀^{p,q}_{a,b} V ⊆ ⋀^{p+q} V_ℂ` (Hodge type
  `(p, q)` for the complex structure of `X × X̂`, `K`-weight `(a, b)`).
* `KSecant.spinPZ`: the integral group `Spin(V)_P` of (2.2.2), i.e. `SpinZ n ⊓ Spin(V_ℚ)_P`.
* `WeilClasses.invariantsExt F n H`: the vectors of `⋀• V_F` fixed by a subgroup `H ⊆ Spin(V_F)`
  (acting by `ρ`, preserving the grading); `KSecant.invQ k = (⋀^k V_ℚ)^{Spin(V)_P}` and
  `KSecant.invK k = (⋀^k V_K)^{Spin(V)_P}`.

## Statements

* The claims between Lemma 2.2.6 and Lemma 2.2.7: `KSecant.weightSpaceK_ηK_one_zero`,
  `KSecant.weightSpaceK_ηK_zero_one` (`W₁ = V_{1,0}`, `W₂ = V_{0,1}`), `KSecant.wedgeAB_eq`
  (`⋀_{a,b} V = ⋀^a W₁ ⊗ ⋀^b W₂`), `KSecant.conjExt_mem_wedgeAB` (`U_{a,b} ⊕ U_{b,a}` is defined
  over `ℚ`), `KSecant.wedge_decomp` (`⋀^k V_K = ⊕_{a+b=k} ⋀^a W₁ ⊗ ⋀^b W₂`),
  `KSecant.wedgePQAB_decomp` (`⋀^k V_ℂ = ⊕ ⋀^{p,q}_{a,b} V`), `KSecant.map_ι_W₁ℂ_V10` (and three
  more: `W₁^{1,0} = ⋀^{1,0}_{1,0}V`, etc.).
* **Lemma 2.2.7**: `lemma2_2_7_hodge` (the invariants are of Hodge type), `lemma2_2_7_odd`,
  `lemma2_2_7_even`, `lemma2_2_7_middle` (the dimensions `0`, `1`, `3`), `lemma2_2_7_K_*` (the
  decomposition of `(⋀^{2n} V_K)^{Spin(V)_P}` into the characters `det₁`, `det₂`, `1` of
  `Spin(V_K)_{ℓ₁,ℓ₂}`), `lemma2_2_7_trivial` (for `j ≠ n` the invariant line is a trivial
  character), the irreducibility used in the proof (`lemma2_2_7_irreducible₁`,
  `lemma2_2_7_irreducible₂`), and the note after the lemma (`lemma2_2_7_note`,
  `lemma2_2_7_note_pow`: the invariants are the powers of a non-degenerate invariant `2`-form, apart
  from the Hodge–Weil plane in degree `2n`).
* `eq_of_character_eq`: the characters `λ ↦ λ^a σ(λ)^b` of `K^×` are pairwise distinct (the paper's
  "`Hom(K^×, K^×) ≅ ℤ × ℤ`").

## Note for the proofs

The group of Lemma 2.2.7 is the *integral* group `Spin(V)_P` of (2.2.2), acting on `⋀• V_ℚ` through
`ρ` (`WeilClasses.rhoExt`), as printed. The paper's proof uses, without proof, that `⋀^k Wᵢ`
(`0 ≤ k ≤ 2n`) is an irreducible representation of `Spin(V)_P`. This holds for the algebraic group
`Spin(V_K)_P ≅ SL(W₁)`; for the integral group it needs a density argument (`Spin(V)_P` is an
arithmetic subgroup of a `ℚ`-form of `SL_{2n}` with noncompact real points, hence Zariski dense by
Borel's density theorem; or an argument with unipotent elements `1 + t N`, `t ∈ ℤ`).

The proofs use the second route (gap filled per `notes/proof-plans.md`):
1. The unitary transvections `E_{x,t} = 1 + t ι(f x) ι(x)` (`x` isotropic and integral, `t ∈ ℤ`) lie
   in `Spin(V)_P`. Their action on `⋀• V_K` is a polynomial of degree `2` in `t`. So a subspace
   stable under `Spin(V)_P` is stable under the derivations `D_{N_x}` (`KSecant.s22b_Der_Dop_mem`).
2. The `K`-span of the `N_x` contains the operators `D_{a,c}` (`a ∈ W₁`, `c ∈ W₂`, `(a, c) = 0`)
   that act as `sl(W₁)`. Its torus and root operators give the invariants of
   `⋀^a W₁ ⊗ ⋀^b W₂`: zero unless `a = b` (the line of `ω^a`, `ω = Σ uᵢ ∧ uᵢ*`) or
   `(a, b) ∈ {(2n, 0), (0, 2n)}` (`KSecant.s22b_inv_decomp`). The same operators give the
   irreducibility of `⋀^k Wᵢ`.
3. Galois descent gives the rational dimensions (`s22b_finrank_descent`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Products of exterior powers of two subspaces -/

section Pieces

variable (F : Type*) [Field F] {M : Type*} [AddCommGroup M] [Module F M]

end Pieces

/-! ## Weight spaces of an action of `K^×` -/

section Weight

variable (d : ℚ) {U : Type*} [AddCommGroup U] [Module (Kd d) U]

theorem s22b_σ_natCast_add (t : ℕ) :
    Kd.σ d ((t : Kd d) + Kd.sqrtNeg d) = (t : Kd d) - Kd.sqrtNeg d := by
  rw [map_add, map_natCast, s22b_σ_sqrtNeg, sub_eq_add_neg]

theorem s22b_natCast_add_ne_zero (hd : 0 < d) (t : ℕ) : (t : Kd d) + Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := congrArg (fun z : Kd d => ((z : ℂ)).im) h
  simp [Kd.sqrtNeg, WeilClasses.sqrtNeg] at this
  have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  linarith

/-- "**The character group `Hom(K^×, K^×)` is isomorphic to `ℤ × ℤ`, generated by `id` and
conjugation**" (§2.2, before Lemma 2.2.7). Reading: the algebraic characters of the torus
`R_{K/ℚ} 𝔾_m` over `K` (algebraic groups are not modeled; as abstract groups `Hom(K^×, K^×)` is much
larger). We state the part used for the weight decompositions: the characters
`λ ↦ λ^a σ(λ)^b`, `(a, b) ∈ ℤ²`, are pairwise distinct on `K^×`. -/
theorem eq_of_character_eq (hd : 0 < d) (a b a' b' : ℤ)
    (h : ∀ l : Kd d, l ≠ 0 → l ^ a * Kd.σ d l ^ b = l ^ a' * Kd.σ d l ^ b') :
    a = a' ∧ b = b' := by
  -- `l = 2`: `a + b = a' + b'`
  have h2 := h 2 two_ne_zero
  have hσ2 : Kd.σ d 2 = 2 := map_ofNat (Kd.σ d) 2
  rw [hσ2, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero] at h2
  have hab : a + b = a' + b' := by
    have h2' : ((2 : ℚ) ^ (a + b) : ℚ) = (2 : ℚ) ^ (a' + b') := by
      apply (algebraMap ℚ (Kd d)).injective
      simpa using h2
    exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) h2'
  -- `(σ l / l)^(b - b') = 1` for all `l ≠ 0`
  have hroot : ∀ l : Kd d, l ≠ 0 → (Kd.σ d l / l) ^ (b - b') = 1 := by
    intro l hl
    have hσl : Kd.σ d l ≠ 0 := by simpa using hl
    have := h l hl
    have e1 : (Kd.σ d l / l) ^ (b - b') =
        (l ^ a * Kd.σ d l ^ b) / (l ^ a' * Kd.σ d l ^ b') := by
      rw [div_zpow, zpow_sub₀ hσl, show b - b' = a' - a by omega, zpow_sub₀ hl]
      field_simp
    rw [e1, this, div_self (mul_ne_zero (zpow_ne_zero _ hl) (zpow_ne_zero _ hσl))]
  -- the values `σ(l_t)/l_t`, `l_t = t + √-d`, are pairwise distinct
  have hinj : Function.Injective fun t : ℕ =>
      Kd.σ d ((t : Kd d) + Kd.sqrtNeg d) / ((t : Kd d) + Kd.sqrtNeg d) := by
    intro s t hst
    simp only at hst
    rw [s22b_σ_natCast_add, s22b_σ_natCast_add, div_eq_div_iff (s22b_natCast_add_ne_zero d hd s)
      (s22b_natCast_add_ne_zero d hd t)] at hst
    have h3 : (2 : Kd d) * Kd.sqrtNeg d * ((s : Kd d) - t) = 0 := by linear_combination hst
    have h4 : ((s : Kd d) - t) = 0 := by
      rcases mul_eq_zero.mp h3 with h5 | h5
      · exact absurd h5 (mul_ne_zero two_ne_zero (s22b_sqrtNeg_ne_zero hd))
      · exact h5
    exact_mod_cast sub_eq_zero.mp h4
  suffices hb : b = b' from ⟨by omega, hb⟩
  by_contra hbb
  have hk : 0 < (b - b').natAbs := by omega
  have hsub : Set.range (fun t : ℕ =>
      Kd.σ d ((t : Kd d) + Kd.sqrtNeg d) / ((t : Kd d) + Kd.sqrtNeg d)) ⊆
      ↑(Polynomial.nthRoots (b - b').natAbs (1 : Kd d)).toFinset := by
    rintro _ ⟨t, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hk]
    have := hroot _ (s22b_natCast_add_ne_zero d hd t)
    rcases Int.natAbs_eq (b - b') with h5 | h5
    · rw [h5, zpow_natCast] at this; exact this
    · rw [h5, zpow_neg, zpow_natCast, inv_eq_one] at this; exact this
  exact (Set.infinite_range_of_injective hinj).mono hsub (Finset.finite_toSet _)


/-- The weight space `U_{a,b}` (§2.2, before Lemma 2.2.7): given a `ℚ`-vector space with an action
of `K^×`, the subspace of `U_K = U ⊗_ℚ K` on which `λ ∈ K^×` acts by `λ^a σ(λ)^b`. Here `U` is the
`K`-vector space `U_K` and `act λ` the `K`-linear extension of the action of `λ`. -/
def weightSpaceK (act : Kd d → Module.End (Kd d) U) (a b : ℤ) : Submodule (Kd d) U where
  carrier := {x | ∀ l : Kd d, l ≠ 0 → act l x = (l ^ a * Kd.σ d l ^ b) • x}
  add_mem' := by
    intro x y hx hy l hl
    rw [map_add, hx l hl, hy l hl, smul_add]
  zero_mem' := by
    intro l _
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c x hx l hl
    rw [map_smul, hx l hl, smul_comm]

end Weight

/-! ## Invariants of a subgroup of `Spin(V_F)` in `⋀• V_F` -/

section Invariants

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The vectors of `⋀• V_F = H*(X × X̂, F)` fixed by every element of a subgroup `H ⊆ Spin(V_F)`,
acting by `ρ_g = ⋀• ρ(g)` (the action of Diagram (1.3.1) preserving the grading). -/
def invariantsExt (H : Subgroup (Spin F n)) : Submodule F (ExteriorAlgebra F (V F n)) where
  carrier := {α | ∀ g ∈ H, rhoExt F n g α = α}
  add_mem' := by
    intro x y hx hy g hg
    rw [map_add, hx g hg, hy g hg]
  zero_mem' := by
    intro g _
    rw [map_zero]
  smul_mem' := by
    intro c x hx g hg
    rw [map_smul, hx g hg]

end Invariants

section ConjHelpers

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s22b_basisExt_singleton (k : Fin (2 * n + 2 * n)) :
    basisExt F n {k} = ExteriorAlgebra.ι F (basisV F n k) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard (basisV F n) (Finset.card_singleton k)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply]
  congr 2
  have h := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (Set.powersetCard.ofCard (Finset.card_singleton k)) ((Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton k))) 0)).mp ⟨0, rfl⟩
  simpa [Set.powersetCard.ofCard, Set.powersetCard.mem_coe_iff] using h

variable (c : F ≃+* F)

theorem s22b_conjExt_apply (x : ExteriorAlgebra F (V F n)) :
    conjExt c n x = ∑ K, c ((basisExt F n).repr x K) • basisExt F n K := rfl

theorem s22b_conjExt_smul (a : F) (x : ExteriorAlgebra F (V F n)) :
    conjExt c n (a • x) = c a • conjExt c n x := by
  simp only [s22b_conjExt_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Finset.smul_sum, mul_smul]

theorem s22b_conjExt_basisExt (K : Finset (Fin (2 * n + 2 * n))) :
    conjExt c n (basisExt F n K) = basisExt F n K := by
  rw [s22b_conjExt_apply, Finset.sum_eq_single K]
  · simp
  · intro L _ hL
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hL, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ K) h

omit [CharZero F] in
theorem s22b_basisV_repr_inl (w : V F n) (i : Fin (2 * n)) :
    (basisV F n).repr w (finSumFinEquiv (Sum.inl i)) = w.1 (e F n i) := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inl,
    Module.Basis.dualBasis_repr, Pi.basisFun_apply]
  rfl

omit [CharZero F] in
theorem s22b_basisV_repr_inr (w : V F n) (j : Fin (2 * n)) :
    (basisV F n).repr w (finSumFinEquiv (Sum.inr j)) = w.2 j := by
  rw [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inr]
  simp

theorem s22b_conjV_eq_sum (v : V F n) :
    conjV c n v = ∑ k, c ((basisV F n).repr v k) • basisV F n k := by
  apply (basisV F n).repr.injective
  ext k
  rw [map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | j
  · rw [s22b_basisV_repr_inl, s22b_basisV_repr_inl, s22b_conjV_fst]
  · rw [s22b_basisV_repr_inr, s22b_basisV_repr_inr, s22b_conjV_snd]

theorem s22b_conjExt_ι (v : V F n) :
    conjExt c n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F (conjV c n v) := by
  conv_lhs => rw [← (basisV F n).sum_repr v]
  rw [map_sum, map_sum, s22b_conjV_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, s22b_conjExt_smul, ← s22b_basisExt_singleton, s22b_conjExt_basisExt,
    s22b_basisExt_singleton, map_smul]


theorem s22b_conjExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    conjExt c n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F k (conjV c n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [s22b_conjExt_ι]

theorem s22b_conjExt_mem_exteriorPower {k : ℕ} {x : ExteriorAlgebra F (V F n)}
    (hx : x ∈ ⋀[F]^k (V F n)) : conjExt c n x ∈ ⋀[F]^k (V F n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [s22b_conjExt_ιMulti]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [s22b_conjExt_smul]; exact Submodule.smul_mem _ _ hx

theorem s22b_conjExt_algebraMap (r : F) :
    conjExt c n (algebraMap F (ExteriorAlgebra F (V F n)) r) =
      algebraMap F (ExteriorAlgebra F (V F n)) (c r) := by
  rw [Algebra.algebraMap_eq_smul_one, s22b_conjExt_smul, map_one, Algebra.algebraMap_eq_smul_one]

/-- `σ ∘ ⋀ A = ⋀ A ∘ σ` when `A` commutes with `σ` on `V`. -/
theorem s22b_conjExt_map (A : V F n →ₗ[F] V F n)
    (hA : ∀ v, conjV c n (A v) = A (conjV c n v)) (x : ExteriorAlgebra F (V F n)) :
    conjExt c n (ExteriorAlgebra.map A x) = ExteriorAlgebra.map A (conjExt c n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, s22b_conjExt_algebraMap, AlgHom.commutes]
  | ι v =>
    have h : (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) v) = ExteriorAlgebra.ι F v := rfl
    rw [h, ExteriorAlgebra.map_apply_ι, s22b_conjExt_ι, s22b_conjExt_ι, hA,
      ExteriorAlgebra.map_apply_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

end ConjHelpers

section Expansion

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- `L_a`, left exterior multiplication. -/
noncomputable abbrev s22b_L (a : M) : ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  LinearMap.mul K (ExteriorAlgebra K M) (ExteriorAlgebra.ι K a)

/-- `ι_φ`, contraction. -/
noncomputable abbrev s22b_C (φ : Module.Dual K M) : ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K M)) φ

theorem s22b_C_ι_mul (φ : Module.Dual K M) (v : M) (y : ExteriorAlgebra K M) :
    s22b_C φ (ExteriorAlgebra.ι K v * y) = φ v • y - ExteriorAlgebra.ι K v * s22b_C φ y :=
  contractLeft_ι_mul (Q := (0 : QuadraticForm K M)) φ v y

theorem s22b_ι_anticomm (a v : M) :
    ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K v = -(ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a v)

/-- **The expansion `⋀(1 + t X) = 1 + t D_X + t² E_X`** for the rank-two map
`X z = φ_c(z) a - φ_a(z) c` (`φ_a`, `φ_c` linear forms): `D_X = L_a ι_{φ_c} - L_c ι_{φ_a}` and
`E_X = -L_a L_c ι_{φ_a} ι_{φ_c}`. -/
theorem s22b_map_one_add_smul (a c : M) (φa φc : Module.Dual K M) (t : K)
    (y : ExteriorAlgebra K M) :
    ExteriorAlgebra.map (LinearMap.id + t • (φc.smulRight a - φa.smulRight c)) y =
      y + t • (ExteriorAlgebra.ι K a * s22b_C φc y - ExteriorAlgebra.ι K c * s22b_C φa y) +
        t ^ 2 • -(ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K c * s22b_C φa (s22b_C φc y)) := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [contractLeft_algebraMap]
  | add x y hx hy =>
    rw [map_add, hx, hy]
    simp only [map_add, mul_add]
    module
  | ι_mul y v hy =>
    have h1 : (CliffordAlgebra.ι (0 : QuadraticForm K M) v) = ExteriorAlgebra.ι K v := rfl
    rw [h1, map_mul, ExteriorAlgebra.map_apply_ι, hy]
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.smulRight_apply, map_add, map_smul, map_sub, s22b_C_ι_mul]
    set A := ExteriorAlgebra.ι K a
    set Cc := ExteriorAlgebra.ι K c
    set Vv := ExteriorAlgebra.ι K v
    have hAA : A * A = 0 := ExteriorAlgebra.ι_sq_zero a
    have hCC : Cc * Cc = 0 := ExteriorAlgebra.ι_sq_zero c
    have hVA : Vv * A = -(A * Vv) := s22b_ι_anticomm v a
    have hVC : Vv * Cc = -(Cc * Vv) := s22b_ι_anticomm v c
    have hCA : Cc * A = -(A * Cc) := s22b_ι_anticomm c a
    have hAA' : ∀ z, A * (A * z) = 0 := fun z => by rw [← mul_assoc, hAA, zero_mul]
    have hCC' : ∀ z, Cc * (Cc * z) = 0 := fun z => by rw [← mul_assoc, hCC, zero_mul]
    have hVA' : ∀ z, Vv * (A * z) = -(A * (Vv * z)) := fun z => by
      rw [← mul_assoc, hVA, neg_mul, mul_assoc]
    have hVC' : ∀ z, Vv * (Cc * z) = -(Cc * (Vv * z)) := fun z => by
      rw [← mul_assoc, hVC, neg_mul, mul_assoc]
    have hCA' : ∀ z, Cc * (A * z) = -(A * (Cc * z)) := fun z => by
      rw [← mul_assoc, hCA, neg_mul, mul_assoc]
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_neg,
      mul_assoc, hAA', hCC', hVA', hVC', hCA', smul_add, smul_sub, smul_neg, neg_neg,
      smul_zero, neg_zero, mul_zero, smul_smul]
    module

end Expansion

section Integrality

variable {n : ℕ}

theorem s22b_exists_mul_den_int (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ z : ℤ, (D : ℚ) * q = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ), mul_assoc, Rat.den_mul_eq_num]

theorem s22b_exists_nat_smul_mem_VZ (v : V ℚ n) : ∃ M : ℕ, 0 < M ∧ (M : ℚ) • v ∈ VZ n := by
  refine ⟨(∏ i, (v.1 (e ℚ n i)).den) * ∏ i, (v.2 i).den,
    Nat.mul_pos (Finset.prod_pos fun i _ => Rat.den_pos _) (Finset.prod_pos fun i _ => Rat.den_pos _),
    fun i => ?_, fun i => ?_⟩
  · simp only [Prod.smul_fst, LinearMap.smul_apply, smul_eq_mul]
    exact s22b_exists_mul_den_int _ _ (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _
      (Finset.mem_univ i)) _)
  · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    exact s22b_exists_mul_den_int _ _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _
      (Finset.mem_univ i)) _)

theorem s22b_pairing_VZ {v w : V ℚ n} (hv : v ∈ VZ n) (hw : w ∈ VZ n) :
    ∃ z : ℤ, pairing ℚ n v w = z := by
  have hdual : ∀ (θ : Module.Dual ℚ (H1 ℚ n)) (u : H1 ℚ n), (∀ i, ∃ z : ℤ, θ (e ℚ n i) = z) →
      (∀ i, ∃ z : ℤ, u i = z) → ∃ z : ℤ, θ u = z := by
    intro θ u hθ hu
    have hu' : u = ∑ i, u i • e ℚ n i := by ext j; simp [e, Pi.single_apply]
    choose zθ hzθ using hθ
    choose zu hzu using hu
    refine ⟨∑ i, zu i * zθ i, ?_⟩
    rw [hu', map_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, hzθ, hzu]
  obtain ⟨z₁, hz₁⟩ := hdual v.1 w.2 hv.1 hw.2
  obtain ⟨z₂, hz₂⟩ := hdual w.1 v.2 hw.1 hv.2
  refine ⟨z₁ + z₂, ?_⟩
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, hz₁, hz₂]
  push_cast; rfl

end Integrality

section Indices

variable {n : ℕ}

/-- Indices of the adapted basis: `L i ↦ uᵢ ∈ W₁`, `R j ↦ uⱼ* ∈ W₂`. -/
def s22b_iL (i : Fin (2 * n)) : Fin (2 * n + 2 * n) := finSumFinEquiv (Sum.inl i)

def s22b_iR (j : Fin (2 * n)) : Fin (2 * n + 2 * n) := finSumFinEquiv (Sum.inr j)

theorem s22b_iL_inj : Function.Injective (s22b_iL (n := n)) := fun i j h => by
  simpa [s22b_iL] using finSumFinEquiv.injective h

theorem s22b_iR_inj : Function.Injective (s22b_iR (n := n)) := fun i j h => by
  simpa [s22b_iR] using finSumFinEquiv.injective h

theorem s22b_iL_ne_iR (i j : Fin (2 * n)) : s22b_iL i ≠ s22b_iR j := fun h => by
  simpa [s22b_iL, s22b_iR] using finSumFinEquiv.injective h

theorem s22b_iLR_cases (k : Fin (2 * n + 2 * n)) : (∃ i, k = s22b_iL i) ∨ ∃ j, k = s22b_iR j := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | j
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

@[simp] theorem s22b_iL_eq_iff (i j : Fin (2 * n)) : s22b_iL i = s22b_iL j ↔ i = j :=
  s22b_iL_inj.eq_iff

@[simp] theorem s22b_iR_eq_iff (i j : Fin (2 * n)) : s22b_iR i = s22b_iR j ↔ i = j :=
  s22b_iR_inj.eq_iff

@[simp] theorem s22b_iL_ne_iR' (i j : Fin (2 * n)) : s22b_iL i = s22b_iR j ↔ False :=
  ⟨s22b_iL_ne_iR i j, False.elim⟩

@[simp] theorem s22b_iR_ne_iL' (i j : Fin (2 * n)) : s22b_iR j = s22b_iL i ↔ False :=
  ⟨fun h => s22b_iL_ne_iR i j h.symm, False.elim⟩

/-- `D(I) = {Lᵢ, Rᵢ : i ∈ I}`. -/
def s22b_Dset (I : Finset (Fin (2 * n))) : Finset (Fin (2 * n + 2 * n)) :=
  I.image s22b_iL ∪ I.image s22b_iR

/-- All `L`-indices (the monomial `u₁ ∧ ⋯ ∧ u_{2n}`). -/
def s22b_allL : Finset (Fin (2 * n + 2 * n)) := Finset.univ.image (s22b_iL (n := n))

/-- All `R`-indices. -/
def s22b_allR : Finset (Fin (2 * n + 2 * n)) := Finset.univ.image (s22b_iR (n := n))

@[simp] theorem s22b_iL_mem_Dset (I : Finset (Fin (2 * n))) (i : Fin (2 * n)) :
    s22b_iL i ∈ s22b_Dset I ↔ i ∈ I := by
  simp [s22b_Dset]

@[simp] theorem s22b_iR_mem_Dset (I : Finset (Fin (2 * n))) (i : Fin (2 * n)) :
    s22b_iR i ∈ s22b_Dset I ↔ i ∈ I := by
  simp [s22b_Dset]

theorem s22b_card_Dset (I : Finset (Fin (2 * n))) : (s22b_Dset I).card = 2 * I.card := by
  rw [s22b_Dset, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ s22b_iL_inj,
    Finset.card_image_of_injective _ s22b_iR_inj]
  · omega
  rw [Finset.disjoint_left]
  intro m hm hm'
  simp only [Finset.mem_image] at hm hm'
  obtain ⟨i, -, rfl⟩ := hm
  obtain ⟨j, -, h⟩ := hm'
  exact s22b_iL_ne_iR _ _ h.symm

theorem s22b_card_allL : (s22b_allL (n := n)).card = 2 * n := by
  rw [s22b_allL, Finset.card_image_of_injective _ s22b_iL_inj, Finset.card_univ, Fintype.card_fin]

theorem s22b_card_allR : (s22b_allR (n := n)).card = 2 * n := by
  rw [s22b_allR, Finset.card_image_of_injective _ s22b_iR_inj, Finset.card_univ, Fintype.card_fin]

/-- Classification of the supports of weight-zero vectors. -/
theorem s22b_support_cases (S : Finset (Fin (2 * n + 2 * n)))
    (hw : ∀ i j : Fin (2 * n),
      ((if s22b_iL i ∈ S then (1 : ℤ) else 0) - (if s22b_iR i ∈ S then 1 else 0)) =
        ((if s22b_iL j ∈ S then 1 else 0) - (if s22b_iR j ∈ S then 1 else 0))) :
    (∃ I, S = s22b_Dset I) ∨ S = s22b_allL ∨ S = s22b_allR := by
  classical
  by_cases h1 : ∃ i, s22b_iL i ∈ S ∧ s22b_iR i ∉ S
  · obtain ⟨i, hi1, hi2⟩ := h1
    right; left
    have hall : ∀ j, s22b_iL j ∈ S ∧ s22b_iR j ∉ S := by
      intro j
      have := hw i j
      simp only [hi1, hi2, ite_true, ite_false] at this
      by_cases a : s22b_iL j ∈ S <;> by_cases b : s22b_iR j ∈ S <;> simp [a, b] at this ⊢
    ext m
    rcases s22b_iLR_cases m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [s22b_allL, (hall j).1]
    · simp [s22b_allL, (hall j).2, (s22b_iL_ne_iR _ _)]
  by_cases h2 : ∃ i, s22b_iL i ∉ S ∧ s22b_iR i ∈ S
  · obtain ⟨i, hi1, hi2⟩ := h2
    right; right
    have hall : ∀ j, s22b_iL j ∉ S ∧ s22b_iR j ∈ S := by
      intro j
      have := hw i j
      simp only [hi1, hi2, ite_true, ite_false] at this
      by_cases a : s22b_iL j ∈ S <;> by_cases b : s22b_iR j ∈ S <;> simp [a, b] at this ⊢
    ext m
    rcases s22b_iLR_cases m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [s22b_allR, (hall j).1, (s22b_iL_ne_iR _ _).symm]
    · simp [s22b_allR, (hall j).2]
  · left
    push Not at h1 h2
    refine ⟨Finset.univ.filter fun i => s22b_iL i ∈ S, ?_⟩
    ext m
    rcases s22b_iLR_cases m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp
    · simp only [s22b_iR_mem_Dset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; by_contra h'; exact h2 j h' h
      · intro h; by_contra h'; exact h' (h1 j h)

end Indices

section Commuting

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

theorem s22b_ι2_comm_ι (a b c : M) :
    ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b * ExteriorAlgebra.ι K c =
      ExteriorAlgebra.ι K c * (ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) := by
  rw [mul_assoc, s22b_ι_anticomm b c, mul_neg, ← mul_assoc, s22b_ι_anticomm a c, neg_mul,
    neg_neg, mul_assoc]

theorem s22b_ι2_comm (a b c e : M) :
    ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b * (ExteriorAlgebra.ι K c * ExteriorAlgebra.ι K e) =
      ExteriorAlgebra.ι K c * ExteriorAlgebra.ι K e * (ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) := by
  rw [← mul_assoc, s22b_ι2_comm_ι, mul_assoc, s22b_ι2_comm_ι, ← mul_assoc]

theorem s22b_ι2_sq (a b : M) :
    ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b * (ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) =
      0 := by
  rw [← mul_assoc, s22b_ι2_comm_ι, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul]

/-- Binomial formula for a square-zero element commuting with `y`. -/
theorem s22b_add_pow_sq_zero {A : Type*} [Ring A] [Algebra K A] {x y : A} (hxy : Commute x y)
    (hx : x * x = 0) (m : ℕ) : (x + y) ^ (m + 1) = y ^ (m + 1) + ((m + 1 : ℕ) : K) • (x * y ^ m) := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    have h1 : y ^ (m + 1) * x = x * y ^ (m + 1) := ((hxy.pow_right (m + 1)).eq).symm
    have h2 : x * y ^ m * x = 0 := by
      rw [mul_assoc, ← (hxy.pow_right m).eq, ← mul_assoc, hx, zero_mul]
    calc (y ^ (m + 1) + ((m + 1 : ℕ) : K) • (x * y ^ m)) * (x + y)
        = y ^ (m + 1) * x + y ^ (m + 1) * y + ((m + 1 : ℕ) : K) • (x * y ^ m * x) +
            ((m + 1 : ℕ) : K) • (x * y ^ m * y) := by
          simp only [add_mul, mul_add, smul_mul_assoc]; abel
      _ = _ := by
          rw [h1, h2, smul_zero, add_zero, ← pow_succ, mul_assoc, ← pow_succ]
          push_cast
          module

end Commuting

/-! ## Products of pieces, Galois descent, index facts (helpers for Lemma 2.2.7) -/

section S22bGeneric

variable {n : ℕ} {d : ℚ}

theorem s22b_bcExt_eq_sum (x : ExteriorAlgebra ℚ (V ℚ n)) :
    bcExt ℚ (Kd d) n x =
      ∑ T, algebraMap ℚ (Kd d) ((basisExt ℚ n).repr x T) • basisExt (Kd d) n T := by
  conv_lhs => rw [← (basisExt ℚ n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_smul, s22b_bcExt_basisExt, algebraMap_smul]

theorem s22b_repr_bcExt (x : ExteriorAlgebra ℚ (V ℚ n)) (S : Finset (Fin (2 * n + 2 * n))) :
    (basisExt (Kd d) n).repr (bcExt ℚ (Kd d) n x) S =
      algebraMap ℚ (Kd d) ((basisExt ℚ n).repr x S) := by
  rw [s22b_bcExt_eq_sum, Module.Basis.repr_sum_self]

theorem s22b_repr_conjExt (c : Kd d ≃+* Kd d) (y : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (S : Finset (Fin (2 * n + 2 * n))) :
    (basisExt (Kd d) n).repr (conjExt c n y) S = c ((basisExt (Kd d) n).repr y S) := by
  rw [s22b_conjExt_apply, Module.Basis.repr_sum_self]

theorem s22b_conjExt_conjExt (y : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    conjExt (Kd.σ d) n (conjExt (Kd.σ d) n y) = y := by
  apply (basisExt (Kd d) n).repr.injective
  ext S
  rw [s22b_repr_conjExt, s22b_repr_conjExt, s22b_σ_σ]

theorem s22b_conjExt_bcExt (x : ExteriorAlgebra ℚ (V ℚ n)) :
    conjExt (Kd.σ d) n (bcExt ℚ (Kd d) n x) = bcExt ℚ (Kd d) n x := by
  apply (basisExt (Kd d) n).repr.injective
  ext S
  rw [s22b_repr_conjExt, s22b_repr_bcExt, s22b_σ_algebraMap]

theorem s22b_exists_bcExt (hd : 0 < d) (y : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hy : conjExt (Kd.σ d) n y = y) : ∃ x, bcExt ℚ (Kd d) n x = y := by
  have hc : ∀ S, Kd.σ d ((basisExt (Kd d) n).repr y S) = (basisExt (Kd d) n).repr y S := by
    intro S
    have := congrArg (fun z => (basisExt (Kd d) n).repr z S) hy
    simpa only [s22b_repr_conjExt] using this
  refine ⟨∑ S, Kd.ratPart d ((basisExt (Kd d) n).repr y S) • basisExt ℚ n S, ?_⟩
  apply (basisExt (Kd d) n).repr.injective
  ext S
  rw [s22b_repr_bcExt, Module.Basis.repr_sum_self, ← (s22b_eq_algebraMap_of_σ_eq hd _ (hc S))]

theorem s22b_rhoExt_bcExt (g : Spin ℚ n) (x : ExteriorAlgebra ℚ (V ℚ n)) :
    rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) (bcExt ℚ (Kd d) n x) =
      bcExt ℚ (Kd d) n (rhoExt ℚ n g x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    exact ((rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g)).restrictScalars ℚ).commutes r
  | ι v =>
    rw [s22b_bcExt_ι]
    simp only [rhoExt, ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe]
    rw [s22b_bcExt_ι, s22b_rho_bcSpin]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem s22b_mem_exteriorPower_iff_basisExt {F : Type*} [Field F] [CharZero F] {k : ℕ}
    {x : ExteriorAlgebra F (V F n)} :
    x ∈ ⋀[F]^k (V F n) ↔ ∀ S, (basisExt F n).repr x S ≠ 0 → S.card = k :=
  s22b_mem_exteriorPower_iff (basisV F n)

theorem s22b_bcExt_mem_iff {k : ℕ} {x : ExteriorAlgebra ℚ (V ℚ n)} :
    bcExt ℚ (Kd d) n x ∈ ⋀[Kd d]^k (V (Kd d) n) ↔ x ∈ ⋀[ℚ]^k (V ℚ n) := by
  rw [s22b_mem_exteriorPower_iff_basisExt, s22b_mem_exteriorPower_iff_basisExt]
  refine forall_congr' fun S => ?_
  rw [s22b_repr_bcExt]
  have hinj : ∀ q : ℚ, algebraMap ℚ (Kd d) q ≠ 0 ↔ q ≠ 0 := fun q =>
    map_ne_zero_iff _ (algebraMap ℚ (Kd d)).injective
  rw [hinj]

theorem s22b_mem_invariantsExt_map (H : Subgroup (Spin ℚ n))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    z ∈ invariantsExt (Kd d) n (H.map (bcSpin ℚ (Kd d) n)) ↔
      ∀ g ∈ H, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z := by
  constructor
  · intro h g hg; exact h _ (Subgroup.mem_map_of_mem _ hg)
  · rintro h _ ⟨g, hg, rfl⟩; exact h g hg

/-- Base change preserves linear independence (`K = ℚ ⊕ ℚ √-d`). -/
theorem s22b_linearIndependent_bcExt (hd : 0 < d) {ι : Type*} (v : ι → ExteriorAlgebra ℚ (V ℚ n))
    (hv : LinearIndependent ℚ v) :
    LinearIndependent (Kd d) (fun i => bcExt ℚ (Kd d) n (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have hg' : ∀ i, g i = algebraMap ℚ (Kd d) (Kd.ratPart d (g i)) +
      algebraMap ℚ (Kd d) (Kd.sqrtNegCoeff d (g i)) * Kd.sqrtNeg d :=
    fun i => Kd.eq_ratPart_add_sqrtNegCoeff hd (g i)
  set A := ∑ i ∈ s, Kd.ratPart d (g i) • v i
  set B := ∑ i ∈ s, Kd.sqrtNegCoeff d (g i) • v i
  have hAB : bcExt ℚ (Kd d) n A + Kd.sqrtNeg d • bcExt ℚ (Kd d) n B = 0 := by
    rw [← hg]
    simp only [A, B, map_sum, map_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [hg' i]
    rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul, smul_comm (Kd.sqrtNeg d)]
  have hAB' : bcExt ℚ (Kd d) n A - Kd.sqrtNeg d • bcExt ℚ (Kd d) n B = 0 := by
    have := congrArg (conjExt (Kd.σ d) n) hAB
    rw [map_add, s22b_conjExt_smul, s22b_conjExt_bcExt, s22b_conjExt_bcExt, s22b_σ_sqrtNeg,
      map_zero, neg_smul, ← sub_eq_add_neg] at this
    exact this
  have hA : A = 0 := by
    apply s22b_bcExt_injective (F' := Kd d)
    rw [map_zero]
    have : (2 : Kd d) • bcExt ℚ (Kd d) n A = 0 := by
      rw [two_smul]; linear_combination (norm := module) hAB + hAB'
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have hB : B = 0 := by
    apply s22b_bcExt_injective (F' := Kd d)
    rw [map_zero]
    have : (2 * Kd.sqrtNeg d) • bcExt ℚ (Kd d) n B = 0 := by
      rw [mul_smul, two_smul]; linear_combination (norm := module) hAB - hAB'
    exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero (s22b_sqrtNeg_ne_zero hd))
  rw [hg' i, hv s _ hA i hi, hv s _ hB i hi]
  simp

theorem s22b_two_parts {X : Type*} [AddCommGroup X] [Module (Kd d) X] (hd : 0 < d) (y z : X) :
    y = (2 : Kd d)⁻¹ • (y + z) + (2 * Kd.sqrtNeg d)⁻¹ • (Kd.sqrtNeg d • (y - z)) := by
  have hs := s22b_sqrtNeg_ne_zero hd
  rw [smul_smul, show (2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d = (2 : Kd d)⁻¹ by field_simp]
  module

/-- A `σ`-stable subspace of `⋀• V_K` is spanned by its rational points. -/
theorem s22b_descent_le_span (hd : 0 < d) (N : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)))
    (M : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNM : ∀ x, x ∈ N ↔ bcExt ℚ (Kd d) n x ∈ M)
    (hM : ∀ y ∈ M, conjExt (Kd.σ d) n y ∈ M) :
    M ≤ Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' (N : Set (ExteriorAlgebra ℚ (V ℚ n)))) := by
  have hfix : ∀ z ∈ M, conjExt (Kd.σ d) n z = z →
      z ∈ Submodule.span (Kd d) (bcExt ℚ (Kd d) n '' (N : Set (ExteriorAlgebra ℚ (V ℚ n)))) := by
    intro z hz hfz
    obtain ⟨x, rfl⟩ := s22b_exists_bcExt hd z hfz
    exact Submodule.subset_span ⟨x, (hNM x).mpr hz, rfl⟩
  intro y hy
  have hσy := hM y hy
  have h1 := hfix _ (M.add_mem hy hσy) (by rw [map_add, s22b_conjExt_conjExt, add_comm])
  have h2 := hfix _ (M.smul_mem (Kd.sqrtNeg d) (M.sub_mem hy hσy)) (by
    rw [s22b_conjExt_smul, map_sub, s22b_conjExt_conjExt, s22b_σ_sqrtNeg, neg_smul, ← smul_neg,
      neg_sub])
  rw [s22b_two_parts hd y (conjExt (Kd.σ d) n y)]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem s22b_bcExt_mem_span_basis (N : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n))) {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℚ N) (x : ExteriorAlgebra ℚ (V ℚ n)) (hx : x ∈ N) :
    bcExt ℚ (Kd d) n x ∈ Submodule.span (Kd d)
      (Set.range fun i => bcExt ℚ (Kd d) n (b i : ExteriorAlgebra ℚ (V ℚ n))) := by
  have h1 := congrArg N.subtype (b.sum_repr ⟨x, hx⟩)
  simp only [map_sum, map_smul, Submodule.subtype_apply] at h1
  rw [← h1, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, ← algebraMap_smul (Kd d)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Galois descent for dimensions**: if `N = {x | x_K ∈ M}` and `M` is `σ`-stable, then
`dim_ℚ N = dim_K M`. -/
theorem s22b_finrank_descent (hd : 0 < d) (N : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)))
    (M : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNM : ∀ x, x ∈ N ↔ bcExt ℚ (Kd d) n x ∈ M)
    (hM : ∀ y ∈ M, conjExt (Kd.σ d) n y ∈ M) :
    Module.finrank ℚ N = Module.finrank (Kd d) M := by
  have : Module.Finite ℚ (ExteriorAlgebra ℚ (V ℚ n)) := Module.Finite.of_basis (basisExt ℚ n)
  have : Module.Finite (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)) :=
    Module.Finite.of_basis (basisExt (Kd d) n)
  let b := Module.finBasis ℚ N
  let v : Fin (Module.finrank ℚ N) → ExteriorAlgebra (Kd d) (V (Kd d) n) :=
    fun i => bcExt ℚ (Kd d) n (b i : ExteriorAlgebra ℚ (V ℚ n))
  apply le_antisymm
  · have hli : LinearIndependent (Kd d) v :=
      s22b_linearIndependent_bcExt hd _ (b.linearIndependent.map' N.subtype N.ker_subtype)
    have hli' : LinearIndependent (Kd d) (fun i => (⟨v i, (hNM _).mp (b i).2⟩ : M)) :=
      LinearIndependent.of_comp M.subtype hli
    have := hli'.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  · have hspan : M ≤ Submodule.span (Kd d) (Set.range v) :=
      (s22b_descent_le_span hd N M hNM hM).trans (Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        exact s22b_bcExt_mem_span_basis N b x hx))
    have h1 := Submodule.finrank_mono hspan
    have h2 := finrank_range_le_card (R := Kd d) v
    rw [Fintype.card_fin] at h2
    exact h1.trans h2

theorem s22b_iL_mem_allL (i : Fin (2 * n)) : s22b_iL i ∈ s22b_allL :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem s22b_iR_mem_allR (i : Fin (2 * n)) : s22b_iR i ∈ s22b_allR :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem s22b_iL_notMem_allR (i : Fin (2 * n)) : s22b_iL i ∉ s22b_allR := by
  simp [s22b_allR]

theorem s22b_iR_notMem_allL (i : Fin (2 * n)) : s22b_iR i ∉ s22b_allL := by
  simp [s22b_allL]

theorem s22b_allR_inter_allL : (s22b_allR (n := n)) ∩ s22b_allL = ∅ := by
  ext m
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro hm hm'
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hm
  exact s22b_iR_notMem_allL j hm'

theorem s22b_allL_ne_allR (hn : 0 < n) : (s22b_allL (n := n)) ≠ s22b_allR := fun h =>
  s22b_iL_notMem_allR ⟨0, by omega⟩ (h ▸ s22b_iL_mem_allL _)

theorem s22b_Dset_ne_allL (hn : 0 < n) (I : Finset (Fin (2 * n))) : s22b_Dset I ≠ s22b_allL := by
  intro h
  rcases I.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have := s22b_iL_mem_allL (n := n) ⟨0, by omega⟩
    rw [← h] at this
    simp at this
  · have := (s22b_iR_mem_Dset I i).mpr hi
    rw [h] at this
    exact s22b_iR_notMem_allL i this

theorem s22b_Dset_ne_allR (hn : 0 < n) (I : Finset (Fin (2 * n))) : s22b_Dset I ≠ s22b_allR := by
  intro h
  rcases I.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have := s22b_iR_mem_allR (n := n) ⟨0, by omega⟩
    rw [← h] at this
    simp at this
  · have := (s22b_iL_mem_Dset I i).mpr hi
    rw [h] at this
    exact s22b_iL_notMem_allR i this

/-- A choice of subsets `I_a ⊆ {0, …, 2n-1}` with `|I_a| = a` (`a ≤ 2n`). -/
theorem s22b_exists_Isel : ∃ Isel : ℕ → Finset (Fin (2 * n)), ∀ a ≤ 2 * n, (Isel a).card = a := by
  have hex : ∀ a : ℕ, ∃ I : Finset (Fin (2 * n)), a ≤ 2 * n → I.card = a := fun a => by
    by_cases ha : a ≤ 2 * n
    · obtain ⟨I, -, hI⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * n))))
        (by simpa using ha)
      exact ⟨I, fun _ => hI⟩
    · exact ⟨∅, fun h => absurd h ha⟩
  choose Isel hIsel using hex
  exact ⟨Isel, hIsel⟩

theorem s22b_σV_rho_bcSpin (g : Spin ℚ n) (v : V (Kd d) n) :
    σV n d (rho (Kd d) n (bcSpin ℚ (Kd d) n g) v) =
      rho (Kd d) n (bcSpin ℚ (Kd d) n g) (σV n d v) := by
  have hv : v ∈ Submodule.span (Kd d) (Set.range (bcV ℚ (Kd d) n)) := by
    rw [s22b_span_bcV]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [s22b_rho_bcSpin, s22b_σV_bcV, s22b_σV_bcV, s22b_rho_bcSpin]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, s22b_σV_smul, hx, s22b_σV_smul, map_smul]

theorem s22b_conjExt_rhoExt_bcSpin (g : Spin ℚ n) (x : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    conjExt (Kd.σ d) n (rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x) =
      rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) (conjExt (Kd.σ d) n x) :=
  s22b_conjExt_map (Kd.σ d) _ (fun v => s22b_σV_rho_bcSpin g v) x

end S22bGeneric

/-! ## Hodge types of the invariants (helpers for Lemma 2.2.7) -/

section S22bHodgeGeneric

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
/-- `ω = Σ aᵢ ∧ bᵢ` (`a` spanning `A`, `b` spanning `B`, dual bases) is invariant under an
isometry `T` of `V` preserving `A` and `B`. -/
theorem s22b_omega_inv_general {m : ℕ} (A B : Submodule F (V F n)) (a b : Fin m → V F n)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hexpA : ∀ x ∈ A, x = ∑ i, pairing F n x (b i) • a i)
    (hexpB : ∀ y ∈ B, y = ∑ i, pairing F n (a i) y • b i)
    (T T' : V F n →ₗ[F] V F n) (hTT' : ∀ x, T (T' x) = x)
    (hTB : ∀ y ∈ B, T y ∈ B) (hT'A : ∀ x ∈ A, T' x ∈ A)
    (hiso : ∀ x y, pairing F n (T x) (T y) = pairing F n x y) :
    ∑ i, ExteriorAlgebra.ι F (T (a i)) * ExteriorAlgebra.ι F (T (b i)) =
      ∑ i, ExteriorAlgebra.ι F (a i) * ExteriorAlgebra.ι F (b i) := by
  have key : ∀ l, ∑ i, pairing F n (a l) (T (b i)) • T (a i) = a l := by
    intro l
    have h1 : ∀ i, pairing F n (a l) (T (b i)) = pairing F n (T' (a l)) (b i) := by
      intro i
      conv_lhs => rw [← hTT' (a l)]
      rw [hiso]
    simp only [h1, ← map_smul, ← map_sum]
    rw [← hexpA _ (hT'A _ (ha l)), hTT']
  calc ∑ i, ExteriorAlgebra.ι F (T (a i)) * ExteriorAlgebra.ι F (T (b i))
      = ∑ i, ∑ l, pairing F n (a l) (T (b i)) •
          (ExteriorAlgebra.ι F (T (a i)) * ExteriorAlgebra.ι F (b l)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [hexpB _ (hTB _ (hb i))]
        rw [map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [map_smul, mul_smul_comm]
    _ = ∑ l, ∑ i, pairing F n (a l) (T (b i)) •
          (ExteriorAlgebra.ι F (T (a i)) * ExteriorAlgebra.ι F (b l)) := Finset.sum_comm
    _ = ∑ l, ExteriorAlgebra.ι F (∑ i, pairing F n (a l) (T (b i)) • T (a i)) *
          ExteriorAlgebra.ι F (b l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_mul_assoc]
    _ = _ := Finset.sum_congr rfl fun l _ => by rw [key l]

omit [CharZero F] in
/-- Expansion in a dual family. -/
theorem s22b_expand_of_span {m : ℕ} (a b : Fin m → V F n)
    (hdual : ∀ i j, pairing F n (a i) (b j) = if i = j then 1 else 0)
    {x : V F n} (hx : x ∈ Submodule.span F (Set.range a)) :
    x = ∑ i, pairing F n x (b i) • a i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [CharZero F] in
theorem s22b_expand_of_span' {m : ℕ} (a b : Fin m → V F n)
    (hdual : ∀ i j, pairing F n (a i) (b j) = if i = j then 1 else 0)
    {y : V F n} (hy : y ∈ Submodule.span F (Set.range b)) :
    y = ∑ i, pairing F n (a i) y • b i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hy
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [map_sum]
  simp only [map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- A spin element fixing a spinor preserves its annihilator. -/
theorem s22b_rho_mem_ann_of_fix (g : Spin F n) {u : S F n} (hfix : m F n (g : C F n) u = u)
    {v : V F n} (hv : v ∈ ann F n u) : rho F n g v ∈ ann F n u := by
  show m F n (ι (Q F n) (rho F n g v)) u = 0
  have h1 := m_ι_rho_m F n g v u
  rw [hfix] at h1
  rw [h1]
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  rw [hv', map_zero]

theorem s22b_fix_inv (g : Spin F n) {u : S F n} (hfix : m F n (g : C F n) u = u) :
    m F n ((g⁻¹ : Spin F n) : C F n) u = u := by
  conv_lhs => rw [← hfix]
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel,
    OneMemClass.coe_one, map_one, Module.End.one_apply]

theorem s22b_rho_inv_rho (g : Spin F n) (v : V F n) : rho F n g (rho F n g⁻¹ v) = v := by
  simp only [rho, ← LinearEquiv.mul_apply, ← spinVectorAction_mul, mul_inv_cancel,
    spinVectorAction_one, LinearEquiv.refl_apply]

/-- Fixed points of `⋀T` (`T = 1/2` on `A`, `2` on `B`, `V = A ⊕ B`) in degree `2j` have type
`(j, j)`. -/
theorem s22b_mem_pq_of_fixed {M : Type*} [AddCommGroup M] [Module ℂ M] {A B : Submodule ℂ M}
    (hAB : IsCompl A B) (T : Module.End ℂ M) (hA : ∀ x ∈ A, T x = (1 / 2 : ℂ) • x)
    (hB : ∀ x ∈ B, T x = (2 : ℂ) • x) (j : ℕ) {x : ExteriorAlgebra ℂ M}
    (hx : x ∈ ⋀[ℂ]^(2 * j) M) (hTx : ExteriorAlgebra.map T x = x) :
    x ∈ pqPiece A B j j := by
  have hmem := s22b_wedge_le_iSup hAB.sup_eq_top (2 * j) hx
  have := s22b_mem_of_separating (fun a : Fin (2 * j + 1) => pqPiece A B a (2 * j - a))
    (s22b_iSupIndep_pqPiece hAB (2 * j)) (fun _ : Unit => (ExteriorAlgebra.map T).toLinearMap)
    (fun _ a => (1 / 2 : ℂ) ^ (a : ℕ) * 2 ^ (2 * j - a))
    (fun _ a y hy => s22b_map_pqPiece T _ _ hA hB hy) ⟨j, by omega⟩
    (fun a ha => ⟨(), fun h => ha (Fin.ext (by
      have hχj : (1 / 2 : ℂ) ^ j * 2 ^ (2 * j - j) = 1 := by
        rw [show 2 * j - j = j by omega, ← mul_pow]; norm_num
      have h1 : (1 / 2 : ℂ) ^ (a : ℕ) * 2 ^ (2 * j - (a : ℕ)) = 1 := h.trans hχj
      have h2 : ((1 / 2 : ℂ) ^ (a : ℕ) * 2 ^ (2 * j - (a : ℕ))) * 2 ^ (a : ℕ) =
          1 * 2 ^ (a : ℕ) := by rw [h1]
      rw [one_mul, mul_comm ((1 / 2 : ℂ) ^ (a : ℕ)), mul_assoc, ← mul_pow] at h2
      norm_num at h2
      have h3 : ((2 ^ (2 * j - (a : ℕ)) : ℕ) : ℂ) = ((2 ^ (a : ℕ) : ℕ) : ℂ) := by
        push_cast; exact h2
      have h4 := Nat.pow_right_injective le_rfl (Nat.cast_injective h3)
      have ha2 : (a : ℕ) ≤ 2 * j := Nat.lt_succ_iff.mp a.2
      show (a : ℕ) = j
      omega))⟩) hmem
    (fun _ => by
      simp only [AlgHom.toLinearMap_apply, show 2 * j - j = j by omega, hTx]
      rw [← mul_pow]
      norm_num)
  simpa [show 2 * j - j = j by omega] using this

/-- `⋀T` acts on `⋀^m A` (`dim A = m`, `T(A) ⊆ A`) by `det(T|_A)`. -/
theorem s22b_map_top_sub {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (A B : Submodule K M) [Module.Finite K A] {m : ℕ} (hA : Module.finrank K A = m)
    (T : M →ₗ[K] M) (hT : ∀ v ∈ A, T v ∈ A) {x : ExteriorAlgebra K M}
    (hx : x ∈ pqPiece A B m 0) :
    ExteriorAlgebra.map T x = LinearMap.det (T.restrict hT) • x := by
  let bA := Module.finBasisOfFinrankEq K A hA
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, -, rfl⟩ := hy
    simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rw [ExteriorAlgebra.map_apply_ιMulti]
    set a' : Fin m → A := fun i => ⟨a i, ha i⟩
    have h1 : a = A.subtype ∘ a' := rfl
    have h2 : T ∘ a = A.subtype ∘ ((T.restrict hT) ∘ a') := by
      funext i; rfl
    rw [h2, h1]
    exact s22b_alternating_comp bA ((ExteriorAlgebra.ιMulti K m).compLinearMap A.subtype) _ a'
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- `⋀T` acts on `⋀^m B` (`dim B = m`, `T(B) ⊆ B`) by `det(T|_B)`. -/
theorem s22b_map_top_sub' {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (A B : Submodule K M) [Module.Finite K B] {m : ℕ} (hB : Module.finrank K B = m)
    (T : M →ₗ[K] M) (hT : ∀ v ∈ B, T v ∈ B) {x : ExteriorAlgebra K M}
    (hx : x ∈ pqPiece A B 0 m) :
    ExteriorAlgebra.map T x = LinearMap.det (T.restrict hT) • x := by
  let bB := Module.finBasisOfFinrankEq K B hB
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, -, hb, rfl⟩ := hy
    simp only [ExteriorAlgebra.ιMulti_zero_apply, one_mul]
    rw [ExteriorAlgebra.map_apply_ιMulti]
    set b' : Fin m → B := fun i => ⟨b i, hb i⟩
    have h1 : b = B.subtype ∘ b' := rfl
    have h2 : T ∘ b = B.subtype ∘ ((T.restrict hT) ∘ b') := by
      funext i; rfl
    rw [h2, h1]
    exact s22b_alternating_comp bB ((ExteriorAlgebra.ιMulti K m).compLinearMap B.subtype) _ b'
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- Chevalley: a spin element fixing an even pure spinor acts with determinant `1` on its
annihilator. -/
theorem s22b_det_one (hn : 0 < n) (g : Spin F n) {u : S F n} (hu : IsEvenPureSpinor F n u)
    (hfix : m F n (g : C F n) u = u) :
    LinearMap.det ((rho F n g : V F n →ₗ[F] V F n).restrict
      (fun _ hv => s22b_rho_mem_ann_of_fix g hfix hv)) = 1 := by
  obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 F n u hu g
    (fun _ hv => s22b_rho_mem_ann_of_fix g hfix hv)
  have hu0 : u ≠ 0 := hu.ne_zero hn
  have hc1 : c = 1 := by
    rw [hfix] at hc
    have : (1 - c) • u = 0 := by rw [sub_smul, one_smul, ← hc, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)).symm
  rw [← hc2, hc1, one_pow]

end S22bHodgeGeneric

section S22bBC2

variable {n : ℕ} {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']

theorem s22b_bcExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) =
      ExteriorAlgebra.ιMulti F' k (bcV F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact s22b_bcExt_ι (v i)

theorem s22b_bcExt_mem_exteriorPower' {k : ℕ} {x : ExteriorAlgebra F (V F n)}
    (hx : x ∈ ⋀[F]^k (V F n)) : bcExt F F' n x ∈ ⋀[F']^k (V F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [s22b_bcExt_ιMulti]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, ← algebraMap_smul F']; exact Submodule.smul_mem _ _ hx

/-- Base change of `⋀^p A ∧ ⋀^q B` lands in `⋀^p A_{F'} ∧ ⋀^q B_{F'}`. -/
theorem s22b_bcExt_mem_pqPiece (A B : Submodule F (V F n)) {p q : ℕ}
    {x : ExteriorAlgebra F (V F n)} (hx : x ∈ pqPiece A B p q) :
    bcExt F F' n x ∈ pqPiece (Submodule.span F' (bcV F F' n '' (A : Set (V F n))))
      (Submodule.span F' (bcV F F' n '' (B : Set (V F n)))) p q := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    rw [map_mul, s22b_bcExt_ιMulti, s22b_bcExt_ιMulti]
    exact Submodule.subset_span ⟨_, _, fun i => Submodule.subset_span ⟨a i, ha i, rfl⟩,
      fun j => Submodule.subset_span ⟨b j, hb j, rfl⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, ← algebraMap_smul F']; exact Submodule.smul_mem _ _ hx

theorem s22b_span_bcV_range {ι : Type*} (u : ι → V F n) :
    Submodule.span F' (bcV F F' n '' (Submodule.span F (Set.range u) : Set (V F n))) =
      Submodule.span F' (Set.range (bcV F F' n ∘ u)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← algebraMap_smul F']; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨u i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem s22b_ιMulti_mem_span (A : Submodule F (V F n)) :
    ∀ (a : ℕ) (v' : Fin a → V F' n),
      (∀ i, v' i ∈ Submodule.span F' (bcV F F' n '' (A : Set (V F n)))) →
      ExteriorAlgebra.ιMulti F' a v' ∈ Submodule.span F'
        {x | ∃ v : Fin a → V F n, (∀ i, v i ∈ A) ∧
          x = ExteriorAlgebra.ιMulti F' a (bcV F F' n ∘ v)} := by
  intro a
  induction a with
  | zero =>
    intro v' _
    exact Submodule.subset_span ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  | succ a ih =>
    intro v' hv'
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have h0 : ExteriorAlgebra.ι F' (v' 0) ∈ Submodule.span F'
        ((ExteriorAlgebra.ι F' : V F' n →ₗ[F'] ExteriorAlgebra F' (V F' n)) ''
          (bcV F F' n '' (A : Set (V F n)))) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem (hv' 0)
    have h1 := ih (Matrix.vecTail v') (fun i => hv' i.succ)
    have hmul := Submodule.mul_mem_mul h0 h1
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_le.mpr ?_ hmul
    rintro _ ⟨x, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Fin.cons w v, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hw
      · simpa using hv j
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
      rfl

/-- `⋀^p A_{F'} ∧ ⋀^q B_{F'}` is spanned by the base change of `⋀^p A ∧ ⋀^q B`. -/
theorem s22b_pqPiece_bc_le (A B : Submodule F (V F n)) (p q : ℕ) :
    pqPiece (Submodule.span F' (bcV F F' n '' (A : Set (V F n))))
        (Submodule.span F' (bcV F F' n '' (B : Set (V F n)))) p q ≤
      Submodule.span F' (bcExt F F' n '' (pqPiece A B p q : Set (ExteriorAlgebra F (V F n)))) := by
  rw [pqPiece, Submodule.span_le]
  rintro _ ⟨a, b, ha, hb, rfl⟩
  have hmul := Submodule.mul_mem_mul (s22b_ιMulti_mem_span A p a ha)
    (s22b_ιMulti_mem_span B q b hb)
  rw [Submodule.span_mul_span] at hmul
  refine Submodule.span_le.mpr ?_ hmul
  rintro _ ⟨x, ⟨v, hv, rfl⟩, y, ⟨w, hw, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨ExteriorAlgebra.ιMulti F p v * ExteriorAlgebra.ιMulti F q w,
    Submodule.subset_span ⟨v, w, hv, hw, rfl⟩, ?_⟩
  rw [map_mul, s22b_bcExt_ιMulti, s22b_bcExt_ιMulti]

theorem s22b_span_bcExt_pqPiece (A B : Submodule F (V F n)) (p q : ℕ) :
    Submodule.span F' (bcExt F F' n '' (pqPiece A B p q : Set (ExteriorAlgebra F (V F n)))) =
      pqPiece (Submodule.span F' (bcV F F' n '' (A : Set (V F n))))
        (Submodule.span F' (bcV F F' n '' (B : Set (V F n)))) p q := by
  apply le_antisymm _ (s22b_pqPiece_bc_le A B p q)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact s22b_bcExt_mem_pqPiece A B hx

end S22bBC2

section S22bTransExt

variable {n : ℕ} {d : ℚ}

theorem s22b_bcV_trans (v : V ℚ n) : bcV (Kd d) ℂ n (bcV ℚ (Kd d) n v) = bcV ℚ ℂ n v := by
  apply s22b_V_ext
  · intro i
    rw [s22b_bcV_fst, s22b_bcV_fst, s22b_bcV_fst]
    exact (IsScalarTower.algebraMap_apply ℚ (Kd d) ℂ _).symm
  · intro i
    rw [s22b_bcV_snd, s22b_bcV_snd, s22b_bcV_snd]
    exact (IsScalarTower.algebraMap_apply ℚ (Kd d) ℂ _).symm

theorem s22b_bcExt_trans (x : ExteriorAlgebra ℚ (V ℚ n)) :
    bcExt (Kd d) ℂ n (bcExt ℚ (Kd d) n x) = bcExt ℚ ℂ n x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ (Kd d)
      (ExteriorAlgebra (Kd d) (V (Kd d) n)), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι v =>
    show bcExt (Kd d) ℂ n (bcExt ℚ (Kd d) n (ExteriorAlgebra.ι ℚ v)) =
      bcExt ℚ ℂ n (ExteriorAlgebra.ι ℚ v)
    rw [s22b_bcExt_ι, s22b_bcExt_ι, s22b_bcExt_ι, s22b_bcV_trans]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end S22bTransExt

section S22bIndep

/-- Pairwise intersections of two independent families are independent. -/
theorem s22b_iSupIndep_inf {R M ι₁ ι₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype ι₁] [Fintype ι₂] (A : ι₁ → Submodule R M) (B : ι₂ → Submodule R M)
    (hA : iSupIndep A) (hB : iSupIndep B) :
    iSupIndep (fun pa : ι₁ × ι₂ => A pa.1 ⊓ B pa.2) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hA hB ⊢
  intro s v hv hsum pa hpa
  let w : ι₁ × ι₂ → M := fun x => if x ∈ s then v x else 0
  have hw : ∀ x, w x ∈ A x.1 ⊓ B x.2 := fun x => by
    by_cases h : x ∈ s
    · simp only [w, h, ↓reduceIte]; exact hv x h
    · simp only [w, h, ↓reduceIte]; exact Submodule.zero_mem _
  have hsum' : ∑ x, w x = 0 := by
    rw [← hsum]
    simp only [w]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h1 : ∀ p, ∑ a, w (p, a) = 0 := by
    intro p
    refine hA Finset.univ (fun p => ∑ a, w (p, a)) (fun p _ => Submodule.sum_mem _ fun a _ =>
      (Submodule.mem_inf.mp (hw (p, a))).1) ?_ p (Finset.mem_univ _)
    rw [← hsum', Fintype.sum_prod_type]
  have h2 := hB Finset.univ (fun a => w (pa.1, a))
    (fun a _ => (Submodule.mem_inf.mp (hw (pa.1, a))).2)
    (h1 pa.1) pa.2 (Finset.mem_univ _)
  simpa [w, hpa] using h2

theorem s22b_char_ne {k p p' : ℕ} (hp : p ≤ k) (hp' : p' ≤ k) (hne : p' ≠ p) :
    (1 / 2 : ℂ) ^ p' * 2 ^ (k - p') ≠ (1 / 2) ^ p * 2 ^ (k - p) := by
  intro h
  have hA : ∀ q : ℕ, (1 / 2 : ℂ) ^ q * 2 ^ q = 1 := fun q => by rw [← mul_pow]; norm_num
  have h2 : ((1 / 2 : ℂ) ^ p' * 2 ^ (k - p')) * (2 ^ p' * 2 ^ p) =
      ((1 / 2) ^ p * 2 ^ (k - p)) * (2 ^ p' * 2 ^ p) := by rw [h]
  have e1 : ((1 / 2 : ℂ) ^ p' * 2 ^ (k - p')) * (2 ^ p' * 2 ^ p) = 2 ^ (k - p') * 2 ^ p := by
    calc _ = ((1 / 2 : ℂ) ^ p' * 2 ^ p') * (2 ^ (k - p') * 2 ^ p) := by ring
      _ = _ := by rw [hA, one_mul]
  have e2 : ((1 / 2 : ℂ) ^ p * 2 ^ (k - p)) * (2 ^ p' * 2 ^ p) = 2 ^ (k - p) * 2 ^ p' := by
    calc _ = ((1 / 2 : ℂ) ^ p * 2 ^ p) * (2 ^ (k - p) * 2 ^ p') := by ring
      _ = _ := by rw [hA, one_mul]
  rw [e1, e2, ← pow_add, ← pow_add] at h2
  have h3 : ((2 ^ (k - p' + p) : ℕ) : ℂ) = ((2 ^ (k - p + p') : ℕ) : ℂ) := by
    push_cast; exact h2
  have h4 := Nat.pow_right_injective le_rfl (Nat.cast_injective h3)
  omega

/-- `⋀T` preserves `⋀^p A ∧ ⋀^q B` if `T` preserves `A` and `B`. -/
theorem s22b_map_mem_pqPiece {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {A B : Submodule K M} (T : M →ₗ[K] M) (hA : ∀ v ∈ A, T v ∈ A) (hB : ∀ v ∈ B, T v ∈ B)
    {p q : ℕ} {x : ExteriorAlgebra K M} (hx : x ∈ pqPiece A B p q) :
    ExteriorAlgebra.map T x ∈ pqPiece A B p q := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    rw [map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
    exact Submodule.subset_span ⟨_, _, fun i => hA _ (ha i), fun j => hB _ (hb j), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end S22bIndep

theorem s22b_span_range_subtype {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    (W : Submodule K M) (b : Module.Basis ι K W) :
    Submodule.span K (Set.range fun i => (b i : M)) = W := by
  have : (Set.range fun i => (b i : M)) = W.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-! ## The `K`-weight decomposition of `⋀• V_K` -/

/-! ### The basis of `V_K` adapted to `V_K = W₁ ⊕ W₂` -/

/-- The pairing `W₂ → W₁*`, `y ↦ (·, y)_V`. -/
noncomputable def s22b_pairW₂ : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁ :=
  ((pairing (Kd d) n).compl₁₂ P.W₁.subtype P.W₂.subtype).flip

theorem s22b_pairW₂_apply (y : P.W₂) (x : P.W₁) :
    P.s22b_pairW₂ y x = pairing (Kd d) n x y := rfl

theorem s22b_pairW₂_injective (hW : IsCompl P.W₁ P.W₂) : Function.Injective P.s22b_pairW₂ := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  by_contra h0
  have h0' : (y : V (Kd d) n) ≠ 0 := fun h => h0 (Subtype.ext h)
  obtain ⟨z, hz, hzy⟩ := P.s22b_nd₁₂ hW y y.2 h0'
  exact hzy (by have := LinearMap.congr_fun hy ⟨z, hz⟩; simpa [s22b_pairW₂_apply] using this)

/-- `W₂ ≅ W₁*` via the pairing. -/
noncomputable def s22b_pairW₂Equiv (hW : IsCompl P.W₁ P.W₂) :
    P.W₂ ≃ₗ[Kd d] Module.Dual (Kd d) P.W₁ :=
  LinearMap.linearEquivOfInjective P.s22b_pairW₂ (P.s22b_pairW₂_injective hW) (by
    rw [Subspace.dual_finrank_eq, show P.W₂ = ann (Kd d) n P.u₂ from rfl, P.isPure₂.2.2,
      show P.W₁ = ann (Kd d) n P.u₁ from rfl, P.isPure.2.2])

/-- A basis of `W₁`. -/
noncomputable def s22b_b₁ : Module.Basis (Fin (2 * n)) (Kd d) P.W₁ :=
  Module.finBasisOfFinrankEq (Kd d) P.W₁ P.isPure.2.2

/-- The dual basis of `W₂`: `(b₁ i, b₂ j)_V = δ_ij`. -/
noncomputable def s22b_b₂ (hW : IsCompl P.W₁ P.W₂) : Module.Basis (Fin (2 * n)) (Kd d) P.W₂ :=
  P.s22b_b₁.dualBasis.map (P.s22b_pairW₂Equiv hW).symm

theorem s22b_pairing_b₁_b₂ (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    pairing (Kd d) n (P.s22b_b₁ i) (P.s22b_b₂ hW j) = if i = j then 1 else 0 := by
  have : P.s22b_pairW₂ (P.s22b_b₂ hW j) = P.s22b_b₁.dualBasis j := by
    rw [s22b_b₂, Module.Basis.map_apply]
    exact (P.s22b_pairW₂Equiv hW).apply_symm_apply _
  have h2 := LinearMap.congr_fun this (P.s22b_b₁ i)
  rw [s22b_pairW₂_apply, Module.Basis.dualBasis_apply_self] at h2
  rw [h2]

/-- The basis `u₁, …, u_{2n}, u₁*, …, u_{2n}*` of `V_K` adapted to `V_K = W₁ ⊕ W₂`
(`uᵢ ∈ W₁`, `uⱼ* ∈ W₂`, `(uᵢ, uⱼ*)_V = δᵢⱼ`). -/
noncomputable def s22b_bV (hW : IsCompl P.W₁ P.W₂) : Module.Basis (Fin (2 * n + 2 * n)) (Kd d) (V (Kd d) n) :=
  ((P.s22b_b₁.prod (P.s22b_b₂ hW)).map (Submodule.prodEquivOfIsCompl P.W₁ P.W₂ hW)).reindex
    finSumFinEquiv

theorem s22b_bV_L (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    P.s22b_bV hW (finSumFinEquiv (Sum.inl i)) = P.s22b_b₁ i := by
  rw [s22b_bV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  simp

theorem s22b_bV_R (hW : IsCompl P.W₁ P.W₂) (j : Fin (2 * n)) :
    P.s22b_bV hW (finSumFinEquiv (Sum.inr j)) = P.s22b_b₂ hW j := by
  rw [s22b_bV, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  simp

/-! ### From the integral group `Spin(V)_P` to the Lie algebra `sl(W₁)` -/

/-- `E_{x,t} ∈ Spin(V)` for `x, f x ∈ V` integral and `t ∈ ℤ`. -/
theorem s22b_E_mem_SpinZ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℤ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) (hxZ : x ∈ VZ n) (hfxZ : P.fη hW x ∈ VZ n) :
    P.s22b_E hd hW (t : ℚ) x hx ∈ SpinZ n := by
  refine ⟨?_, fun v hv => ?_⟩
  · rw [s22b_coe_E]
    refine Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _ (Subring.subset_closure
      ⟨_, ?_, rfl⟩) (Subring.subset_closure ⟨_, hxZ, rfl⟩))
    rw [Int.cast_smul_eq_zsmul ℚ]
    exact AddSubgroup.zsmul_mem _ hfxZ t
  · rw [P.s22b_rho_E hd hW]
    obtain ⟨z₁, hz₁⟩ := s22b_pairing_VZ hv hxZ
    obtain ⟨z₂, hz₂⟩ := s22b_pairing_VZ hv hfxZ
    rw [hz₁, hz₂, Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul ℚ]
    exact AddSubgroup.add_mem _ hv (AddSubgroup.zsmul_mem _ (AddSubgroup.sub_mem _
      (AddSubgroup.zsmul_mem _ hfxZ _) (AddSubgroup.zsmul_mem _ hxZ _)) _)

/-- `ρ(E_{x,t}) = 1 + t D_{f x, x}` on `V_K`. -/
theorem s22b_rhoK_E (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (t : ℚ) (x : V ℚ n)
    (hx : Q ℚ n x = 0) :
    (rho (Kd d) n (bcSpin ℚ (Kd d) n (P.s22b_E hd hW t x hx)) : V (Kd d) n →ₗ[Kd d] V (Kd d) n) =
      LinearMap.id + algebraMap ℚ (Kd d) t •
        s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x)) (bcV ℚ (Kd d) n x) := by
  apply s22b_linearMap_ext_bcV (F := ℚ)
  intro y
  rw [LinearEquiv.coe_coe, s22b_rho_bcSpin, P.s22b_rho_E hd hW, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.smul_apply, s22b_Dop_apply, s22b_pairing_bcV, s22b_pairing_bcV,
    s22b_pairing_comm x y, s22b_pairing_comm (P.fη hW x) y]
  simp only [map_add, map_smul, map_sub, algebraMap_smul]

theorem s22b_vandermonde {K X : Type*} [Field K] [CharZero K] [AddCommGroup X] [Module K X]
    (z D E U₁ U₂ : X) (h₁ : U₁ = z + (1 : K) • D + (1 : K) ^ 2 • E)
    (h₂ : U₂ = z + (2 : K) • D + (2 : K) ^ 2 • E) :
    D = (2 : K)⁻¹ • ((4 : K) • (U₁ - z) - (U₂ - z)) := by
  subst h₁ h₂
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  module

theorem s22b_Dop_smul_smul {F : Type*} [Field F] [CharZero F] (r : F) (a c : V F n) :
    s22b_Dop (r • a) (r • c) = (r ^ 2) • s22b_Dop a c := by
  refine LinearMap.ext fun w => ?_
  simp only [s22b_Dop_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_sub, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem s22b_Dop_eq_smulRight {F : Type*} [Field F] [CharZero F] (a c : V F n) :
    s22b_Dop a c = (pairing F n c).smulRight a - (pairing F n a).smulRight c := rfl

/-- Vandermonde: if `⋀(1 + X)` and `⋀(1 + 2X)` preserve a submodule `N`, so does `D_X`
(`X = D_{a,c}`). -/
theorem s22b_Der_mem_of_map_mem {ι : Type*} [Fintype ι] (b : Module.Basis ι (Kd d) (V (Kd d) n))
    (a c : V (Kd d) n) (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (h1 : ExteriorAlgebra.map (LinearMap.id + (1 : Kd d) • s22b_Dop a c) z - z ∈ N)
    (h2 : ExteriorAlgebra.map (LinearMap.id + (2 : Kd d) • s22b_Dop a c) z - z ∈ N) :
    s22b_Der b (s22b_Dop a c) z ∈ N := by
  have e1 := s22b_map_one_add_smul a c (pairing (Kd d) n a) (pairing (Kd d) n c) 1 z
  have e2 := s22b_map_one_add_smul a c (pairing (Kd d) n a) (pairing (Kd d) n c) 2 z
  rw [← s22b_Dop_eq_smulRight] at e1 e2
  have hD : s22b_Der b (s22b_Dop a c) z = (ExteriorAlgebra.ι (Kd d) a * s22b_C (pairing (Kd d) n c) z -
      ExteriorAlgebra.ι (Kd d) c * s22b_C (pairing (Kd d) n a) z) := by
    rw [s22b_Dop_eq_smulRight, s22b_Der_sub, s22b_Der_smulRight, s22b_Der_smulRight]
    rfl
  have key := s22b_vandermonde z _ _ _ _ e1 e2
  rw [hD, key]
  exact N.smul_mem _ (N.sub_mem (N.smul_mem _ h1) h2)

/-- **A subspace of `⋀• V_K` stable under the integral group `Spin(V)_P` is stable under the
derivations `D_{f x, x}`, `x ∈ V_ℚ` isotropic** (the plan for the gap in Lemmas 2.2.4/2.2.7: the
unitary transvections `E_{x,t}`, `t ∈ ℤ`, are integral for integral `x, f x`). -/
theorem s22b_Der_fx_x_mem {ι : Type*} [Fintype ι] (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (b : Module.Basis ι (Kd d) (V (Kd d) n))
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z - z ∈ N)
    (x : V ℚ n) (hx : Q ℚ n x = 0) :
    s22b_Der b (s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x)) (bcV ℚ (Kd d) n x)) z ∈ N := by
  obtain ⟨M₁, hM₁, h₁⟩ := s22b_exists_nat_smul_mem_VZ x
  obtain ⟨M₂, hM₂, h₂⟩ := s22b_exists_nat_smul_mem_VZ (P.fη hW x)
  set M : ℚ := (M₁ : ℚ) * M₂
  have hM : M ≠ 0 := by positivity
  set x' := M • x
  have hx' : Q ℚ n x' = 0 := by simp [x', QuadraticMap.map_smul, hx]
  have hx'Z : x' ∈ VZ n := by
    have : x' = M₂ • ((M₁ : ℚ) • x) := by
      simp only [x', M, mul_smul, Nat.cast_smul_eq_nsmul]; rw [smul_comm]
    rw [this]; exact AddSubgroup.nsmul_mem _ h₁ _
  have hfx'Z : P.fη hW x' ∈ VZ n := by
    have : P.fη hW x' = M₁ • ((M₂ : ℚ) • P.fη hW x) := by
      simp only [x', M, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [this]; exact AddSubgroup.nsmul_mem _ h₂ _
  -- the transvections `E_{x', 1}`, `E_{x', 2}` lie in `Spin(V)_P`
  have hmem : ∀ t : ℤ, P.s22b_E hd hW (t : ℚ) x' hx' ∈ P.spinPZ := fun t =>
    ⟨P.s22b_E_mem_SpinZ hd hW t x' hx' hx'Z hfx'Z, P.s22b_E_mem_spinPℚ hd hW _ x' hx'⟩
  have hU : ∀ t : ℤ, ExteriorAlgebra.map (LinearMap.id + ((t : ℚ) : Kd d) •
      s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x')) (bcV ℚ (Kd d) n x')) z - z ∈ N := by
    intro t
    have := hz _ (hmem t)
    rwa [rhoExt, P.s22b_rhoK_E hd hW, eq_ratCast] at this
  have hD' := s22b_Der_mem_of_map_mem b _ _ N z (by simpa using hU 1) (by simpa using hU 2)
  have hscale : s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x')) (bcV ℚ (Kd d) n x') =
      ((M : Kd d) ^ 2) • s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x)) (bcV ℚ (Kd d) n x) := by
    have e3 : bcV ℚ (Kd d) n (P.fη hW x') = (M : Kd d) • bcV ℚ (Kd d) n (P.fη hW x) := by
      rw [map_smul, map_smul, ← algebraMap_smul (Kd d) M, eq_ratCast]
    have e4 : bcV ℚ (Kd d) n x' = (M : Kd d) • bcV ℚ (Kd d) n x := by
      rw [map_smul, ← algebraMap_smul (Kd d) M, eq_ratCast]
    rw [e3, e4, s22b_Dop_smul_smul]
  rw [hscale, s22b_Der_smul, LinearMap.smul_apply] at hD'
  have := N.smul_mem ((M : Kd d) ^ 2)⁻¹ hD'
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hM)), one_smul] at this

theorem s22b_Mbil_bcV_self_eq (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    P.s22b_Mbil hW (bcV ℚ (Kd d) n x) (bcV ℚ (Kd d) n x) =
      (2 : Kd d) • s22b_Dop (bcV ℚ (Kd d) n (P.fη hW x)) (bcV ℚ (Kd d) n x) := by
  refine LinearMap.ext fun w => ?_
  rw [s22b_Mbil_apply, P.ηK_bcV hd hW, ← fη, LinearMap.smul_apply, s22b_Dop_apply, two_smul]
  abel

/-- The derivations of `𝔫` preserve every subspace stable under `Spin(V)_P`. -/
theorem s22b_Der_nK_mem {ι : Type*} [Fintype ι] (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (b : Module.Basis ι (Kd d) (V (Kd d) n))
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z - z ∈ N)
    (T : Module.End (Kd d) (V (Kd d) n)) (hT : T ∈ P.s22b_nK hW) : s22b_Der b T z ∈ N := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨x, hx, rfl⟩ := hT
    rw [P.s22b_Mbil_bcV_self_eq hd hW, s22b_Der_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (P.s22b_Der_fx_x_mem hd hW b N z hz x hx)
  | zero =>
    have : s22b_Der b (0 : Module.End (Kd d) (V (Kd d) n)) = 0 := by
      simp [s22b_Der]
    rw [this, LinearMap.zero_apply]; exact N.zero_mem
  | add T₁ T₂ _ _ h₁ h₂ => rw [s22b_Der_add, LinearMap.add_apply]; exact N.add_mem h₁ h₂
  | smul c T _ h => rw [s22b_Der_smul, LinearMap.smul_apply]; exact N.smul_mem _ h

/-- **`D_{a,c}`, `a ∈ W₁`, `c ∈ W₂`, `(a, c) = 0`, preserves every subspace stable under
`Spin(V)_P`**: the Lie algebra `sl(W₁)` acts. -/
theorem s22b_Der_Dop_mem {ι : Type*} [Fintype ι] (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (b : Module.Basis ι (Kd d) (V (Kd d) n))
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z - z ∈ N)
    {a c : V (Kd d) n} (ha : a ∈ P.W₁) (hc : c ∈ P.W₂) (hac : pairing (Kd d) n a c = 0) :
    s22b_Der b (s22b_Dop a c) z ∈ N :=
  P.s22b_Der_nK_mem hd hW b N z hz _ (P.s22b_Dop_mem_nK hd hW ha hc hac)





/-- The action `⋀ η_λ` of `λ ∈ K` on `⋀• V_K` induced by (2.2.4). -/
noncomputable def ηExt (hW : IsCompl P.W₁ P.W₂) (l : Kd d) :
    Module.End (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)) :=
  (ExteriorAlgebra.map (P.ηK hW l)).toLinearMap

/-- `⋀_{a,b} V := (⋀^{a+b} V)_{a,b}` (§2.2, before Lemma 2.2.7): the vectors of `⋀^{a+b} V_K` on
which `λ ∈ K^×` acts by `λ^a σ(λ)^b`. -/
noncomputable def wedgeAB (hW : IsCompl P.W₁ P.W₂) (a b : ℕ) :
    Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)) :=
  ⋀[Kd d]^(a + b) (V (Kd d) n) ⊓ weightSpaceK d (P.ηExt hW) a b

/-! ### Monomials in the adapted basis: weights and root operators -/

theorem s22b_bV_iL (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    P.s22b_bV hW (s22b_iL i) = P.s22b_b₁ i := P.s22b_bV_L hW i

theorem s22b_bV_iR (hW : IsCompl P.W₁ P.W₂) (j : Fin (2 * n)) :
    P.s22b_bV hW (s22b_iR j) = P.s22b_b₂ hW j := P.s22b_bV_R hW j

theorem s22b_bV_L_mem (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    P.s22b_bV hW (s22b_iL i) ∈ P.W₁ := by
  rw [P.s22b_bV_iL hW]; exact (P.s22b_b₁ i).2

theorem s22b_bV_R_mem (hW : IsCompl P.W₁ P.W₂) (j : Fin (2 * n)) :
    P.s22b_bV hW (s22b_iR j) ∈ P.W₂ := by
  rw [P.s22b_bV_iR hW]; exact (P.s22b_b₂ hW j).2

theorem s22b_pairing_bV_LR (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    pairing (Kd d) n (P.s22b_bV hW (s22b_iL i)) (P.s22b_bV hW (s22b_iR j)) =
      if i = j then 1 else 0 := by
  rw [P.s22b_bV_iL hW, P.s22b_bV_iR hW, P.s22b_pairing_b₁_b₂ hW]

theorem s22b_coord_L (hW : IsCompl P.W₁ P.W₂) (j : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iL j) = pairing (Kd d) n (P.s22b_bV hW (s22b_iR j)) := by
  refine (P.s22b_bV hW).ext fun k => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  rcases s22b_iLR_cases k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [s22b_pairing_comm, P.s22b_pairing_bV_LR hW, Finsupp.single_apply]
    simp [eq_comm]
  · rw [P.s22b_pairing_W₂ (P.s22b_bV_R_mem hW j) (P.s22b_bV_R_mem hW i),
      Finsupp.single_eq_of_ne (s22b_iL_ne_iR _ _)]

theorem s22b_coord_R (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iR i) = pairing (Kd d) n (P.s22b_bV hW (s22b_iL i)) := by
  refine (P.s22b_bV hW).ext fun k => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  rcases s22b_iLR_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [P.s22b_pairing_W₁ (P.s22b_bV_L_mem hW i) (P.s22b_bV_L_mem hW j),
      Finsupp.single_eq_of_ne (s22b_iL_ne_iR _ _).symm]
  · rw [P.s22b_pairing_bV_LR hW, Finsupp.single_apply]
    simp [eq_comm]

/-- `D_{uᵢ, uⱼ*} = R_{Lᵢ,Lⱼ} - R_{Rⱼ,Rᵢ}` in the adapted basis. -/
theorem s22b_Dop_bV (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    s22b_Dop (P.s22b_bV hW (s22b_iL i)) (P.s22b_bV hW (s22b_iR j)) =
      s22b_rOp (P.s22b_bV hW) (s22b_iL i) (s22b_iL j) -
        s22b_rOp (P.s22b_bV hW) (s22b_iR j) (s22b_iR i) := by
  rw [s22b_Dop_eq_smulRight, s22b_rOp, s22b_rOp, P.s22b_coord_L hW, P.s22b_coord_R hW]

theorem s22b_Dop_sub_add {F : Type*} [Field F] [CharZero F] (a₁ a₂ c₁ c₂ : V F n) :
    s22b_Dop (a₁ - a₂) (c₁ + c₂) =
      s22b_Dop a₁ c₁ + s22b_Dop a₁ c₂ - s22b_Dop a₂ c₁ - s22b_Dop a₂ c₂ := by
  refine LinearMap.ext fun z => ?_
  simp only [s22b_Dop_apply, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub,
    LinearMap.add_apply, LinearMap.sub_apply]
  module

variable {P}

/-- The weight operators `H_{ij} = (N_{Lᵢ} - N_{Rᵢ}) - (N_{Lⱼ} - N_{Rⱼ})` preserve every subspace
stable under `Spin(V)_P`. -/
theorem s22b_H_mem (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z - z ∈ N)
    (i j : Fin (2 * n)) (hij : i ≠ j) :
    s22b_Der (P.s22b_bV hW) (s22b_numOp (P.s22b_bV hW) (s22b_iL i) -
      s22b_numOp (P.s22b_bV hW) (s22b_iR i) - s22b_numOp (P.s22b_bV hW) (s22b_iL j) +
      s22b_numOp (P.s22b_bV hW) (s22b_iR j)) z ∈ N := by
  set u := fun k => P.s22b_bV hW (s22b_iL k)
  set u' := fun k => P.s22b_bV hW (s22b_iR k)
  have h1 := P.s22b_Der_Dop_mem hd hW (P.s22b_bV hW) N z hz (a := u i - u j) (c := u' i + u' j)
    (P.W₁.sub_mem (P.s22b_bV_L_mem hW i) (P.s22b_bV_L_mem hW j))
    (P.W₂.add_mem (P.s22b_bV_R_mem hW i) (P.s22b_bV_R_mem hW j)) (by
      simp only [u, u']
      rw [map_sub, LinearMap.sub_apply, map_add, map_add, P.s22b_pairing_bV_LR hW,
        P.s22b_pairing_bV_LR hW, P.s22b_pairing_bV_LR hW, P.s22b_pairing_bV_LR hW]
      simp [hij, hij.symm])
  have h2 := P.s22b_Der_Dop_mem hd hW (P.s22b_bV hW) N z hz (a := u i) (c := u' j)
    (P.s22b_bV_L_mem hW i) (P.s22b_bV_R_mem hW j) (by
      simp only [u, u']; rw [P.s22b_pairing_bV_LR hW]; simp [hij])
  have h3 := P.s22b_Der_Dop_mem hd hW (P.s22b_bV hW) N z hz (a := u j) (c := u' i)
    (P.s22b_bV_L_mem hW j) (P.s22b_bV_R_mem hW i) (by
      simp only [u, u']; rw [P.s22b_pairing_bV_LR hW]; simp [hij.symm])
  have key : s22b_numOp (P.s22b_bV hW) (s22b_iL i) - s22b_numOp (P.s22b_bV hW) (s22b_iR i) -
      s22b_numOp (P.s22b_bV hW) (s22b_iL j) + s22b_numOp (P.s22b_bV hW) (s22b_iR j) =
      s22b_Dop (u i - u j) (u' i + u' j) - s22b_Dop (u i) (u' j) + s22b_Dop (u j) (u' i) := by
    rw [s22b_Dop_sub_add]
    simp only [u, u', P.s22b_Dop_bV hW, s22b_numOp, s22b_rOp]
    abel
  rw [key, s22b_Der_add, s22b_Der_sub, LinearMap.add_apply, LinearMap.sub_apply]
  exact N.add_mem (N.sub_mem h1 h2) h3

/-- The root operators `R_{Lᵢ,Lⱼ} - R_{Rⱼ,Rᵢ}` (`i ≠ j`) preserve every subspace stable under
`Spin(V)_P`. -/
theorem s22b_root_mem (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z - z ∈ N)
    (i j : Fin (2 * n)) (hij : i ≠ j) :
    s22b_Der (P.s22b_bV hW) (s22b_rOp (P.s22b_bV hW) (s22b_iL i) (s22b_iL j) -
      s22b_rOp (P.s22b_bV hW) (s22b_iR j) (s22b_iR i)) z ∈ N := by
  rw [← P.s22b_Dop_bV hW]
  exact P.s22b_Der_Dop_mem hd hW (P.s22b_bV hW) N z hz (P.s22b_bV_L_mem hW i)
    (P.s22b_bV_R_mem hW j) (by rw [P.s22b_pairing_bV_LR hW]; simp [hij])

/-- Support of a `Spin(V)_P`-invariant vector: only the monomials `D(I)`, `u₁ ∧ ⋯ ∧ u_{2n}` and
`u₁* ∧ ⋯ ∧ u_{2n}*` occur (weight zero for the torus of `sl(W₁)`). -/
theorem s22b_inv_support (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (S : Finset (Fin (2 * n + 2 * n))) (hS : (P.s22b_bV hW).ExteriorAlgebra.repr z S ≠ 0) :
    (∃ I, S = s22b_Dset I) ∨ S = s22b_allL ∨ S = s22b_allR := by
  apply s22b_support_cases
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have h := s22b_H_mem hd hW ⊥ z (fun g hg => by rw [hz g hg, sub_self]; exact Submodule.zero_mem _)
    i j hij
  rw [Submodule.mem_bot] at h
  have h2 := congrArg (fun x => (P.s22b_bV hW).ExteriorAlgebra.repr x S) h
  simp only [s22b_Der_add, s22b_Der_sub, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub,
    Finsupp.add_apply, Finsupp.sub_apply, s22b_repr_Der_numOp, map_zero, Finsupp.zero_apply,
    ← sub_mul, ← add_mul] at h2
  have h3 := (mul_eq_zero.mp h2).resolve_right hS
  by_cases a : s22b_iL i ∈ S <;> by_cases b : s22b_iR i ∈ S <;> by_cases c : s22b_iL j ∈ S <;>
    by_cases e : s22b_iR j ∈ S <;> simp [a, b, c, e] at h3 ⊢ <;> norm_num at h3

theorem s22b_Dset_swap_L (I : Finset (Fin (2 * n))) (i j : Fin (2 * n)) (hj : j ∈ I) (hi : i ∉ I) :
    insert (s22b_iL j) ((insert (s22b_iL i) ((s22b_Dset I).erase (s22b_iL j))).erase (s22b_iL i)) =
      s22b_Dset I := by
  rw [Finset.erase_insert (by simp [hi]), Finset.insert_erase (by simp [hj])]

theorem s22b_Dset_swap_R (I : Finset (Fin (2 * n))) (i j : Fin (2 * n)) :
    insert (s22b_iR i) ((insert (s22b_iL i) ((s22b_Dset I).erase (s22b_iL j))).erase (s22b_iR j)) =
      s22b_Dset (insert i (I.erase j)) := by
  ext m
  rcases s22b_iLR_cases m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp [s22b_iL_ne_iR']
  · simp [s22b_iR_ne_iL']

/-- The root operators relate the coefficients of `D(I)` and `D(I - j + i)`. -/
theorem s22b_inv_swap (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (I : Finset (Fin (2 * n))) (i j : Fin (2 * n)) (hij : i ≠ j) (hj : j ∈ I) (hi : i ∉ I) :
    (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset I) = 0 ↔
      (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset (insert i (I.erase j))) = 0 := by
  have h := s22b_root_mem hd hW ⊥ z (fun g hg => by rw [hz g hg, sub_self]; exact Submodule.zero_mem _)
    i j hij
  rw [Submodule.mem_bot] at h
  set T := insert (s22b_iL i) ((s22b_Dset I).erase (s22b_iL j))
  have h2 := congrArg (fun x => (P.s22b_bV hW).ExteriorAlgebra.repr x T) h
  simp only [s22b_Der_sub, LinearMap.sub_apply, map_sub, Finsupp.sub_apply, map_zero,
    Finsupp.zero_apply] at h2
  obtain ⟨ε₁, hε₁, e₁⟩ := s22b_repr_Der_rOp (P.s22b_bV hW) (s22b_iL i) (s22b_iL j)
    (by simpa using hij) z T (Finset.mem_insert_self _ _) (by simp [T, hij.symm])
  obtain ⟨ε₂, hε₂, e₂⟩ := s22b_repr_Der_rOp (P.s22b_bV hW) (s22b_iR j) (s22b_iR i)
    (by simpa using hij.symm) z T (by simp [T, hj]) (by simp [T, hi])
  rw [e₁, e₂, s22b_Dset_swap_L I i j hj hi, s22b_Dset_swap_R I i j, sub_eq_zero] at h2
  have hε₁0 : ε₁ ≠ 0 := by rcases hε₁ with rfl | rfl <;> norm_num
  have hε₂0 : ε₂ ≠ 0 := by rcases hε₂ with rfl | rfl <;> norm_num
  constructor
  · intro h0; rw [h0, mul_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left hε₂0
  · intro h0; rw [h0, mul_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_left hε₁0

/-- Within a block `{D(I) : |I| = a}`, the coefficients of an invariant vector vanish together. -/
theorem s22b_inv_block (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (I₀ : Finset (Fin (2 * n))) :
    ∀ m : ℕ, ∀ I : Finset (Fin (2 * n)), I.card = I₀.card → (I \ I₀).card = m →
      ((P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset I) = 0 ↔
        (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset I₀) = 0) := by
  classical
  intro m
  induction m with
  | zero =>
    intro I hcard hm
    have hsub : I ⊆ I₀ := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]
  | succ m ih =>
    intro I hcard hm
    obtain ⟨j, hj⟩ : (I \ I₀).Nonempty := Finset.card_pos.mp (by omega)
    rw [Finset.mem_sdiff] at hj
    have : (I₀ \ I).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have hsub : I₀ ⊆ I := Finset.sdiff_eq_empty_iff_subset.mp h
      have := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hj.2 (this ▸ hj.1)
    obtain ⟨i, hi⟩ := this
    rw [Finset.mem_sdiff] at hi
    have hij : i ≠ j := fun h => hj.2 (h ▸ hi.1)
    rw [P.s22b_inv_swap hd hW z hz I i j hij hj.1 hi.2]
    apply ih
    · rw [Finset.card_insert_of_notMem (by simp [hi.2]), Finset.card_erase_of_mem hj.1]
      have : 0 < I.card := Finset.card_pos.mpr ⟨j, hj.1⟩
      omega
    · have h1 : insert i (I.erase j) \ I₀ = (I \ I₀).erase j := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hkj, hk⟩, hk0⟩
          · exact absurd hi.1 hk0
          · exact ⟨hkj, hk, hk0⟩
        · rintro ⟨hkj, hk, hk0⟩
          exact ⟨Or.inr ⟨hkj, hk⟩, hk0⟩
      rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hj)]
      omega


/-! ### The invariants: support, the canonical form `ω` -/

/-- The number operator counting the factors in `W₁`. -/
noncomputable def s22b_NL (hW : IsCompl P.W₁ P.W₂) :
    ExteriorAlgebra (Kd d) (V (Kd d) n) →ₗ[Kd d] ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  s22b_Der (P.s22b_bV hW) (∑ i, s22b_numOp (P.s22b_bV hW) (s22b_iL i))

theorem s22b_NL_basis (hW : IsCompl P.W₁ P.W₂) (S : Finset (Fin (2 * n + 2 * n))) :
    s22b_NL hW ((P.s22b_bV hW).ExteriorAlgebra S) =
      ((S ∩ s22b_allL).card : Kd d) • (P.s22b_bV hW).ExteriorAlgebra S := by
  classical
  rw [s22b_NL, s22b_Der_finset_sum, LinearMap.sum_apply]
  simp only [s22b_Der_numOp, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_boole, Nat.cast_inj]
  rw [← Finset.card_image_of_injective _ s22b_iL_inj]
  congr 1
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    s22b_allL]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i, rfl⟩
  · rintro ⟨hm, i, rfl⟩; exact ⟨i, hm, rfl⟩

omit P in
theorem s22b_iL_eq_castAdd (i : Fin (2 * n)) : s22b_iL i = Fin.castAdd (2 * n) i := by
  simp [s22b_iL]

omit P in
theorem s22b_iR_eq_natAdd (j : Fin (2 * n)) : s22b_iR j = Fin.natAdd (2 * n) j := by
  simp [s22b_iR]

theorem s22b_sum_numOp_W₁ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₁) :
    (∑ i, s22b_numOp (P.s22b_bV hW) (s22b_iL i)) w = w := by
  conv_rhs => rw [← (P.s22b_bV hW).sum_repr w]
  rw [LinearMap.sum_apply, Fin.sum_univ_add]
  simp only [← s22b_iL_eq_castAdd, ← s22b_iR_eq_natAdd, s22b_numOp, LinearMap.smulRight_apply,
    Module.Basis.coord_apply]
  have h0 : ∀ j, (P.s22b_bV hW).repr w (s22b_iR j) = 0 := fun j => by
    rw [← Module.Basis.coord_apply, P.s22b_coord_R hW, P.s22b_pairing_W₁ (P.s22b_bV_L_mem hW j) hw]
  simp [h0]

theorem s22b_sum_numOp_W₂ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₂) :
    (∑ i, s22b_numOp (P.s22b_bV hW) (s22b_iL i)) w = 0 := by
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [s22b_numOp, LinearMap.smulRight_apply, P.s22b_coord_L hW,
    P.s22b_pairing_W₂ (P.s22b_bV_R_mem hW i) hw, zero_smul]

/-- `N_L` acts by `p` on `⋀^p W₁ ∧ ⋀^q W₂`. -/
theorem s22b_NL_pqPiece (hW : IsCompl P.W₁ P.W₂) {p q : ℕ} {x : ExteriorAlgebra (Kd d) (V (Kd d) n)}
    (hx : x ∈ pqPiece P.W₁ P.W₂ p q) : s22b_NL hW x = (p : Kd d) • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti, s22b_NL, s22b_Der_ιMulti, Fin.sum_univ_add]
    have h1 : ∀ i : Fin p, ExteriorAlgebra.ιMulti (Kd d) (p + q)
        (Function.update (Fin.append a b) (Fin.castAdd q i)
          ((∑ i, s22b_numOp (P.s22b_bV hW) (s22b_iL i)) (Fin.append a b (Fin.castAdd q i)))) =
        ExteriorAlgebra.ιMulti (Kd d) (p + q) (Fin.append a b) := by
      intro i
      rw [Fin.append_left, P.s22b_sum_numOp_W₁ hW (ha i), ← Fin.append_left a b i,
        Function.update_eq_self]
    have h2 : ∀ j : Fin q, ExteriorAlgebra.ιMulti (Kd d) (p + q)
        (Function.update (Fin.append a b) (Fin.natAdd p j)
          ((∑ i, s22b_numOp (P.s22b_bV hW) (s22b_iL i)) (Fin.append a b (Fin.natAdd p j)))) = 0 := by
      intro j
      rw [Fin.append_right, P.s22b_sum_numOp_W₂ hW (hb j)]
      exact AlternatingMap.map_update_zero _ _ _
    simp only [h1, h2, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (Kd d)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- The monomials occurring in `⋀^p W₁ ∧ ⋀^q W₂` have `p` factors in `W₁` and `q` in `W₂`. -/
theorem s22b_support_pqPiece (hW : IsCompl P.W₁ P.W₂) {p q : ℕ}
    {x : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hx : x ∈ pqPiece P.W₁ P.W₂ p q)
    (S : Finset (Fin (2 * n + 2 * n))) (hS : (P.s22b_bV hW).ExteriorAlgebra.repr x S ≠ 0) :
    (S ∩ s22b_allL).card = p ∧ S.card = p + q := by
  refine ⟨?_, s22b_card_of_repr_ne _ (s22b_pqPiece_le _ _ _ _ hx) S hS⟩
  have h := congrArg (fun y => (P.s22b_bV hW).ExteriorAlgebra.repr y S) (s22b_NL_pqPiece hW hx)
  rw [s22b_repr_map] at h
  simp only [s22b_NL_basis, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [mul_comm] at h
  have := mul_right_cancel₀ hS h
  exact_mod_cast this

/-- Every monomial lies in some `⋀^a W₁ ∧ ⋀^b W₂`. -/
theorem s22b_basis_mem_pqPiece (hW : IsCompl P.W₁ P.W₂) (S : Finset (Fin (2 * n + 2 * n))) :
    (P.s22b_bV hW).ExteriorAlgebra S ∈
      pqPiece P.W₁ P.W₂ (S ∩ s22b_allL).card (S.card - (S ∩ s22b_allL).card) := by
  have hle : (S ∩ s22b_allL).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hmem := s22b_wedge_le_iSup hW.sup_eq_top S.card
    (s22b_basis_mem_exteriorPower (P.s22b_bV hW) S)
  have := s22b_mem_of_separating (fun a : Fin (S.card + 1) => pqPiece P.W₁ P.W₂ a (S.card - a))
    (s22b_iSupIndep_pqPiece hW S.card) (fun _ : Unit => s22b_NL hW) (fun _ a => (a : Kd d))
    (fun _ a x hx => s22b_NL_pqPiece hW hx) ⟨(S ∩ s22b_allL).card, by omega⟩
    (fun a ha => ⟨(), fun h => ha (Fin.ext (by exact_mod_cast h))⟩) hmem
    (fun _ => s22b_NL_basis hW S)
  exact this

/-- **An invariant vector is determined by three coefficients** (the heart of Lemma 2.2.7): if
`z ∈ ⋀^{2a} V_K` is `Spin(V)_P`-invariant and its coefficients at `D(I₀)` (`|I₀| = a`),
`u₁ ∧ ⋯ ∧ u_{2n}` and `u₁* ∧ ⋯ ∧ u_{2n}*` vanish, then `z = 0`. -/
theorem s22b_inv_eq_zero (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (a : ℕ) (hzk : z ∈ ⋀[Kd d]^(2 * a) (V (Kd d) n)) (I₀ : Finset (Fin (2 * n)))
    (hI₀ : I₀.card = a) (h0 : (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset I₀) = 0)
    (hL : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL = 0)
    (hR : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR = 0) : z = 0 := by
  apply (P.s22b_bV hW).ExteriorAlgebra.repr.injective
  refine Finsupp.ext fun S => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hS
  rcases s22b_inv_support hd hW z hz S hS with ⟨I, rfl⟩ | rfl | rfl
  · have hcard := s22b_card_of_repr_ne _ hzk _ hS
    rw [s22b_card_Dset] at hcard
    exact hS ((s22b_inv_block hd hW z hz I₀ _ I (by omega) rfl).mpr h0)
  · exact hS hL
  · exact hS hR

omit P in
theorem s22b_rho_pairing {F : Type*} [Field F] [CharZero F] (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, rho,
    spinVectorAction_map_app]

/-- Expansion of a vector of `W₁` in the basis `uᵢ`: `w = Σ_k (u_k*, w) u_k`. -/
theorem s22b_expand_W₁ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₁) :
    w = ∑ k, pairing (Kd d) n (P.s22b_bV hW (s22b_iR k)) w • P.s22b_bV hW (s22b_iL k) := by
  conv_lhs => rw [← (P.s22b_bV hW).sum_repr w]
  rw [Fin.sum_univ_add]
  simp only [← s22b_iL_eq_castAdd, ← s22b_iR_eq_natAdd]
  have h0 : ∀ j, (P.s22b_bV hW).repr w (s22b_iR j) = 0 := fun j => by
    rw [← Module.Basis.coord_apply, P.s22b_coord_R hW, P.s22b_pairing_W₁ (P.s22b_bV_L_mem hW j) hw]
  simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Module.Basis.coord_apply, P.s22b_coord_L hW]

/-- Expansion of a vector of `W₂` in the basis `uⱼ*`: `w = Σ_l (u_l, w) u_l*`. -/
theorem s22b_expand_W₂ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₂) :
    w = ∑ l, pairing (Kd d) n (P.s22b_bV hW (s22b_iL l)) w • P.s22b_bV hW (s22b_iR l) := by
  conv_lhs => rw [← (P.s22b_bV hW).sum_repr w]
  rw [Fin.sum_univ_add]
  simp only [← s22b_iL_eq_castAdd, ← s22b_iR_eq_natAdd]
  have h0 : ∀ j, (P.s22b_bV hW).repr w (s22b_iL j) = 0 := fun j => by
    rw [← Module.Basis.coord_apply, P.s22b_coord_L hW, P.s22b_pairing_W₂ (P.s22b_bV_R_mem hW j) hw]
  simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Module.Basis.coord_apply, P.s22b_coord_R hW]

/-- The canonical `2`-form `ω = Σᵢ uᵢ ∧ uᵢ*` (the identity of `W₁` in `W₁ ⊗ W₂ ≅ End W₁`). -/
noncomputable def s22b_omega (hW : IsCompl P.W₁ P.W₂) : ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  ∑ i, ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iL i)) *
    ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iR i))

/-- **`ω` is invariant under `Spin(V_K)_{ℓ₁,ℓ₂}`** (it does not depend on the choice of dual
bases). -/
theorem s22b_rhoExt_omega (hW : IsCompl P.W₁ P.W₂) (g : P.spinL₁L₂) :
    rhoExt (Kd d) n g (s22b_omega hW) = s22b_omega hW := by
  set ρ := rho (Kd d) n (g : Spin (Kd d) n)
  set u := fun k => P.s22b_bV hW (s22b_iL k)
  set u' := fun k => P.s22b_bV hW (s22b_iR k)
  have hρ₁ : ∀ i, ρ (u i) ∈ P.W₁ := fun i => P.rho_mem_W₁ g _ (P.s22b_bV_L_mem hW i)
  have hρ₂ : ∀ i, ρ (u' i) ∈ P.W₂ := fun i => P.rho_mem_W₂ g _ (P.s22b_bV_R_mem hW i)
  -- `ρ` maps `W₂` onto `W₂`
  have honto : ∀ c ∈ P.W₂, ∃ c' ∈ P.W₂, ρ c' = c := by
    intro c hc
    refine ⟨rho (Kd d) n (g⁻¹ : P.spinL₁L₂) c, P.rho_mem_W₂ _ _ hc, ?_⟩
    simp only [ρ, Subgroup.coe_inv, rho, ← LinearEquiv.mul_apply, ← spinVectorAction_mul,
      mul_inv_cancel, spinVectorAction_one, LinearEquiv.refl_apply]
  -- `Σᵢ (u_l, ρ uᵢ*) ρ uᵢ = u_l`
  have hδ : ∀ i j, pairing (Kd d) n (ρ (u' j)) (ρ (u i)) = if i = j then 1 else 0 := by
    intro i j
    rw [s22b_rho_pairing, s22b_pairing_comm]
    exact P.s22b_pairing_bV_LR hW i j
  have key : ∀ l, ∑ i, pairing (Kd d) n (u l) (ρ (u' i)) • ρ (u i) = u l := by
    intro l
    set v := ∑ i, pairing (Kd d) n (u l) (ρ (u' i)) • ρ (u i) - u l with hv_def
    have hv : ∀ j, pairing (Kd d) n (ρ (u' j)) v = 0 := by
      intro j
      rw [hv_def, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul, hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [s22b_pairing_comm, sub_self]
    rw [← sub_eq_zero]
    by_contra hne
    have hmem : v ∈ P.W₁ :=
      P.W₁.sub_mem (P.W₁.sum_mem fun i _ => P.W₁.smul_mem _ (hρ₁ i)) (P.s22b_bV_L_mem hW l)
    obtain ⟨c, hc, hpair⟩ := P.s22b_nd₂₁ hW v hmem hne
    obtain ⟨c', hc', rfl⟩ := honto c hc
    apply hpair
    rw [P.s22b_expand_W₂ hW hc', map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, hv j, smul_zero]
  rw [s22b_omega, map_sum]
  simp only [rhoExt, map_mul, ExteriorAlgebra.map_apply_ι]
  change ∑ i, ExteriorAlgebra.ι (Kd d) (ρ (u i)) * ExteriorAlgebra.ι (Kd d) (ρ (u' i)) =
    ∑ l, ExteriorAlgebra.ι (Kd d) (u l) * ExteriorAlgebra.ι (Kd d) (u' l)
  have h2 : ∀ i, ρ (u' i) = ∑ l, pairing (Kd d) n (u l) (ρ (u' i)) • u' l := fun i =>
    P.s22b_expand_W₂ hW (hρ₂ i)
  calc ∑ i, ExteriorAlgebra.ι (Kd d) (ρ (u i)) * ExteriorAlgebra.ι (Kd d) (ρ (u' i))
      = ∑ i, ∑ l, pairing (Kd d) n (u l) (ρ (u' i)) •
          (ExteriorAlgebra.ι (Kd d) (ρ (u i)) * ExteriorAlgebra.ι (Kd d) (u' l)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [h2 i]
        rw [map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [map_smul, mul_smul_comm]
    _ = ∑ l, ∑ i, pairing (Kd d) n (u l) (ρ (u' i)) •
          (ExteriorAlgebra.ι (Kd d) (ρ (u i)) * ExteriorAlgebra.ι (Kd d) (u' l)) :=
        Finset.sum_comm
    _ = ∑ l, ExteriorAlgebra.ι (Kd d) (∑ i, pairing (Kd d) n (u l) (ρ (u' i)) • ρ (u i)) *
          ExteriorAlgebra.ι (Kd d) (u' l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_mul_assoc]
    _ = _ := Finset.sum_congr rfl fun l _ => by rw [key l]

/-- `xᵢ = uᵢ ∧ uᵢ*`. -/
noncomputable def s22b_x (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iL i)) *
    ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iR i))

/-- Partial sums `ω_S = Σ_{i ∈ S} xᵢ`. -/
noncomputable def s22b_omegaS (hW : IsCompl P.W₁ P.W₂) (S : Finset (Fin (2 * n))) :
    ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  ∑ i ∈ S, s22b_x hW i

theorem s22b_contract_x (hW : IsCompl P.W₁ P.W₂) (φ : Module.Dual (Kd d) (V (Kd d) n))
    (j : Fin (2 * n)) (y : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    s22b_C φ (s22b_x hW j * y) =
      φ (P.s22b_bV hW (s22b_iL j)) • (ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iR j)) * y) -
        φ (P.s22b_bV hW (s22b_iR j)) • (ExteriorAlgebra.ι (Kd d) (P.s22b_bV hW (s22b_iL j)) * y) +
        s22b_x hW j * s22b_C φ y := by
  rw [s22b_x, mul_assoc, s22b_C_ι_mul, s22b_C_ι_mul, mul_sub, mul_smul_comm, ← mul_assoc]
  abel

theorem s22b_coord_L_apply (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iL i) (P.s22b_bV hW (s22b_iL j)) = if i = j then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem s22b_coord_L_apply_R (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iL i) (P.s22b_bV hW (s22b_iR j)) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp

theorem s22b_coord_R_apply (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iR i) (P.s22b_bV hW (s22b_iR j)) = if i = j then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem s22b_coord_R_apply_L (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    (P.s22b_bV hW).coord (s22b_iR i) (P.s22b_bV hW (s22b_iL j)) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp

theorem s22b_x_comm (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    s22b_x hW i * s22b_x hW j = s22b_x hW j * s22b_x hW i := s22b_ι2_comm _ _ _ _

theorem s22b_x_sq (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) : s22b_x hW i * s22b_x hW i = 0 :=
  s22b_ι2_sq _ _

theorem s22b_contract_omegaS_pow (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n))
    (S : Finset (Fin (2 * n))) (hi : i ∉ S) (m : ℕ) :
    s22b_C ((P.s22b_bV hW).coord (s22b_iL i)) (s22b_omegaS hW S ^ m) = 0 ∧
      s22b_C ((P.s22b_bV hW).coord (s22b_iR i)) (s22b_omegaS hW S ^ m) = 0 := by
  induction m with
  | zero =>
    rw [pow_zero, ← map_one (algebraMap (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))]
    exact ⟨by simp [s22b_C], by simp [s22b_C]⟩
  | succ m ih =>
    rw [pow_succ', s22b_omegaS, Finset.sum_mul]
    constructor
    · rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [s22b_contract_x, P.s22b_coord_L_apply hW, P.s22b_coord_L_apply_R hW, ← s22b_omegaS, ih.1]
      simp [hij]
    · rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [s22b_contract_x, P.s22b_coord_R_apply_L hW, P.s22b_coord_R_apply hW, ← s22b_omegaS, ih.2]
      simp [hij]

/-- **`ω^a ≠ 0` for `a ≤ 2n`**: applying `ι_{u_i*^*} ι_{u_i^*}` lowers the power. -/
theorem s22b_omegaS_pow_ne_zero (hW : IsCompl P.W₁ P.W₂) (S : Finset (Fin (2 * n))) :
    ∀ a ≤ S.card, s22b_omegaS hW S ^ a ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a ha
    simp only [Finset.card_empty, Nat.le_zero] at ha
    subst ha
    rw [pow_zero]
    exact one_ne_zero
  | insert i S hi ih =>
    intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [pow_zero]; exact one_ne_zero
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    rw [Finset.card_insert_of_notMem hi] at ha
    intro h0
    have hS : s22b_omegaS hW (insert i S) = s22b_x hW i + s22b_omegaS hW S := by
      rw [s22b_omegaS, Finset.sum_insert hi, ← s22b_omegaS]
    have hcomm : Commute (s22b_x hW i) (s22b_omegaS hW S) := by
      rw [s22b_omegaS]
      exact Commute.sum_right _ _ _ fun j _ => s22b_x_comm hW i j
    rw [hS, s22b_add_pow_sq_zero (K := Kd d) hcomm (s22b_x_sq hW i)] at h0
    have h1 := congrArg (fun z => s22b_C ((P.s22b_bV hW).coord (s22b_iR i))
      (s22b_C ((P.s22b_bV hW).coord (s22b_iL i)) z)) h0
    have hc := P.s22b_contract_omegaS_pow hW i S hi
    simp only [map_add, map_smul, map_zero, (hc (m + 1)).1, zero_add] at h1
    rw [s22b_contract_x, P.s22b_coord_L_apply hW, P.s22b_coord_L_apply_R hW,
      (hc m).1, mul_zero, add_zero, zero_smul, sub_zero] at h1
    simp only [↓reduceIte, one_smul] at h1
    rw [s22b_C_ι_mul, P.s22b_coord_R_apply hW, (hc m).2, mul_zero, sub_zero] at h1
    simp only [↓reduceIte, one_smul] at h1
    have h2 : (((m + 1 : ℕ) : Kd d)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    exact ih m (by omega) ((smul_eq_zero.mp h1).resolve_left h2)

theorem s22b_omega_eq (hW : IsCompl P.W₁ P.W₂) :
    s22b_omega hW = s22b_omegaS hW Finset.univ := rfl

theorem s22b_omega_pow_ne_zero (hW : IsCompl P.W₁ P.W₂) (a : ℕ) (ha : a ≤ 2 * n) :
    s22b_omega hW ^ a ≠ 0 :=
  s22b_omegaS_pow_ne_zero hW Finset.univ a (by simpa using ha)


variable (P)

/-- "**`W₁ = V_{1,0}`**" (§2.2): `W₁` is the subspace of `V_K` on which `λ` acts by `λ`. -/
theorem weightSpaceK_ηK_one_zero (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    weightSpaceK d (P.ηK hW) 1 0 = P.W₁ := by
  ext x
  constructor
  · intro hx
    have h := hx (Kd.sqrtNeg d) (s22b_sqrtNeg_ne_zero hd)
    rw [zpow_one, zpow_zero, mul_one, ← P.s22b_decomp hW x,
      P.s22b_fK_add_mem hW (P.s22b_proj₁_mem hW x) (P.s22b_proj₂_mem hW x), smul_add] at h
    have h2 : (2 * Kd.sqrtNeg d) • P.W₂.projection P.W₁ hW.symm x = 0 := by
      rw [mul_smul, two_smul]
      linear_combination (norm := module) -h
    have h3 := (smul_eq_zero.mp h2).resolve_left
      (mul_ne_zero two_ne_zero (s22b_sqrtNeg_ne_zero hd))
    rw [← P.s22b_decomp hW x, h3, add_zero]
    exact P.s22b_proj₁_mem hW x
  · intro hx l _
    rw [zpow_one, zpow_zero, mul_one, P.s22b_ηK_of_mem_W₁ hW l hx]

/-- "**`W₂ = V_{0,1}`**" (§2.2): `W₂` is the subspace of `V_K` on which `λ` acts by `σ(λ)`. -/
theorem weightSpaceK_ηK_zero_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    weightSpaceK d (P.ηK hW) 0 1 = P.W₂ := by
  ext x
  constructor
  · intro hx
    have h := hx (Kd.sqrtNeg d) (s22b_sqrtNeg_ne_zero hd)
    rw [zpow_one, zpow_zero, one_mul, s22b_σ_sqrtNeg, ← P.s22b_decomp hW x,
      P.s22b_fK_add_mem hW (P.s22b_proj₁_mem hW x) (P.s22b_proj₂_mem hW x), smul_add] at h
    have h2 : (2 * Kd.sqrtNeg d) • P.W₁.projection P.W₂ hW x = 0 := by
      rw [mul_smul, two_smul]
      linear_combination (norm := module) h
    have h3 := (smul_eq_zero.mp h2).resolve_left
      (mul_ne_zero two_ne_zero (s22b_sqrtNeg_ne_zero hd))
    rw [← P.s22b_decomp hW x, h3, zero_add]
    exact P.s22b_proj₂_mem hW x
  · intro hx l _
    rw [zpow_one, zpow_zero, one_mul, P.s22b_ηK_of_mem_W₂ hW l hx]

/-- "**`⋀_{a,b} V = ⋀^a W₁ ⊗ ⋀^b W₂`**" (§2.2). -/
theorem wedgeAB_eq (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (a b : ℕ) :
    P.wedgeAB hW a b = pqPiece P.W₁ P.W₂ a b := by
  -- `ηExt λ` acts on `⋀^{a'} W₁ ∧ ⋀^{b'} W₂` by `λ^{a'} σ(λ)^{b'}`
  have hact : ∀ (l : Kd d) (a' b' : ℕ), ∀ x ∈ pqPiece P.W₁ P.W₂ a' b',
      P.ηExt hW l x = (l ^ a' * Kd.σ d l ^ b') • x := fun l a' b' x hx =>
    s22b_map_pqPiece _ _ _ (fun v hv => P.s22b_ηK_of_mem_W₁ hW l hv)
      (fun v hv => P.s22b_ηK_of_mem_W₂ hW l hv) hx
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    replace hx1 := s22b_wedge_le_iSup hW.sup_eq_top (a + b) hx1
    have := s22b_mem_of_separating (fun a' : Fin (a + b + 1) => pqPiece P.W₁ P.W₂ a' (a + b - a'))
      (s22b_iSupIndep_pqPiece hW (a + b)) (fun l : {l : Kd d // l ≠ 0} => P.ηExt hW l)
      (fun l a' => (l : Kd d) ^ (a' : ℕ) * Kd.σ d l ^ (a + b - a'))
      (fun l a' x hx => hact l a' _ x hx) ⟨a, by omega⟩ (fun a' ha' => by
        by_contra hall
        push Not at hall
        have := eq_of_character_eq d hd (a' : ℕ) ((a + b - a' : ℕ) : ℤ) (a : ℕ) ((a + b - a : ℕ) : ℤ)
          (fun l hl => by
            simpa only [zpow_natCast] using hall ⟨l, hl⟩)
        apply ha'
        exact Fin.ext (by exact_mod_cast this.1)) hx1 (fun l => by
          have := hx2 l l.2
          simpa only [zpow_natCast, show a + b - a = b by omega] using this)
    simpa only [show a + b - a = b by omega] using this
  · intro x hx
    refine ⟨s22b_pqPiece_le _ _ a b hx, fun l _ => ?_⟩
    rw [hact l a b x hx, zpow_natCast, zpow_natCast]

/-- "**The subspaces `U_{a,b} ⊕ U_{b,a}` are defined over `ℚ`**" (§2.2), for `U = ⋀• V`: the Galois
involution `σ` maps `⋀_{a,b} V` to `⋀_{b,a} V`. -/
theorem conjExt_mem_wedgeAB (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (a b : ℕ)
    (x : ExteriorAlgebra (Kd d) (V (Kd d) n)) (hx : x ∈ P.wedgeAB hW a b) :
    conjExt (Kd.σ d) n x ∈ P.wedgeAB hW b a := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨by rw [add_comm]; exact s22b_conjExt_mem_exteriorPower _ hx1, fun l hl => ?_⟩
  have hσl : Kd.σ d l ≠ 0 := by simpa using hl
  have h := hx2 (Kd.σ d l) hσl
  have hcomm : ∀ l' : Kd d, conjExt (Kd.σ d) n (P.ηExt hW l' x) =
      P.ηExt hW l' (conjExt (Kd.σ d) n x) := fun l' =>
    s22b_conjExt_map _ _ (fun v => P.σV_ηK hd hW l' v) x
  rw [← hcomm l]
  have h2 := hx2 l hl
  rw [h2, s22b_conjExt_smul, map_mul, map_zpow₀, map_zpow₀, s22b_σ_σ]
  congr 1
  ring

/-- "**`⋀^k V_K ≅ ⊕_{a+b=k} (⋀^a W₁) ⊗ (⋀^b W₂)`**" (proof of Lemma 2.2.7): `⋀^k V_K` is the
internal direct sum of the subspaces `⋀^a W₁ ∧ ⋀^{k-a} W₂`, `0 ≤ a ≤ k`. -/
theorem wedge_decomp (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (k : ℕ) :
    iSupIndep (fun a : Fin (k + 1) => pqPiece P.W₁ P.W₂ a (k - a)) ∧
      ⨆ a : Fin (k + 1), pqPiece P.W₁ P.W₂ a (k - a) = ⋀[Kd d]^k (V (Kd d) n) := by
  have _ := hd
  refine ⟨s22b_iSupIndep_pqPiece hW k, le_antisymm (iSup_le fun a => ?_)
    (s22b_wedge_le_iSup hW.sup_eq_top k)⟩
  have h := s22b_pqPiece_le P.W₁ P.W₂ a (k - a)
  rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp a.2)] at h

/-- `⋀^{p,q}_{a,b} V ⊆ ⋀^{p+q} V_ℂ` (§2.2, before Lemma 2.2.7): the vectors of Hodge type `(p, q)`
for the complex structure `I` (the `ℂ^×`-action `x + iy ↦ x + y I`) and of `K`-weight `(a, b)`. -/
noncomputable def wedgePQAB (hW : IsCompl P.W₁ P.W₂) (I : Module.End ℝ (V ℝ n)) (p q a b : ℕ) :
    Submodule ℂ (ExteriorAlgebra ℂ (V ℂ n)) :=
  pqPiece (V10 n I) (V01 n I) p q ⊓
    Submodule.span ℂ
      (bcExt (Kd d) ℂ n '' (P.wedgeAB hW a b : Set (ExteriorAlgebra (Kd d) (V (Kd d) n))))

section S22bHodgeA

variable (J : Module.End ℝ (H1 ℝ n))

theorem s22b_torus_P (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    ∃ g : Spin ℂ n,
      (∀ x ∈ P.PK, m ℂ n (g : C ℂ n) (bcS (Kd d) ℂ n x) = bcS (Kd d) ℂ n x) ∧
      (∀ v ∈ V10 n (productStructure n J), rho ℂ n g v = (1 / 2 : ℂ) • v) ∧
      (∀ v ∈ V01 n (productStructure n J), rho ℂ n g v = (2 : ℂ) • v) := by
  obtain ⟨g, hmg, h10, h01⟩ := s22b_exists_torus J P.s22b_n_pos hJ
  exact ⟨g, fun x hx => by
    rw [hmg, AlgHom.toLinearMap_apply]; exact P.s22b_map_T_fix J hPJ hx, h10, h01⟩

theorem s22b_u₁_mem_PK : P.u₁ ∈ P.PK := Submodule.subset_span (by simp)

theorem s22b_u₂_mem_PK : P.u₂ ∈ P.PK := Submodule.subset_span (by simp)

theorem s22b_span_uL (hW : IsCompl P.W₁ P.W₂) :
    Submodule.span (Kd d) (Set.range fun i => P.s22b_bV hW (s22b_iL i)) = P.W₁ := by
  have : (fun i => P.s22b_bV hW (s22b_iL i)) = fun i => (P.s22b_b₁ i : V (Kd d) n) :=
    funext fun i => P.s22b_bV_iL hW i
  rw [this, s22b_span_range_subtype]

theorem s22b_span_uR (hW : IsCompl P.W₁ P.W₂) :
    Submodule.span (Kd d) (Set.range fun i => P.s22b_bV hW (s22b_iR i)) = P.W₂ := by
  have : (fun i => P.s22b_bV hW (s22b_iR i)) = fun i => (P.s22b_b₂ hW i : V (Kd d) n) :=
    funext fun i => P.s22b_bV_iR hW i
  rw [this, s22b_span_range_subtype]

theorem s22b_W₁ℂ_span (hW : IsCompl P.W₁ P.W₂) :
    P.W₁ℂ = Submodule.span ℂ (Set.range fun i => bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iL i))) := by
  rw [W₁ℂ, ← P.s22b_span_uL hW, s22b_span_bcV_range]; rfl

theorem s22b_W₂ℂ_span (hW : IsCompl P.W₁ P.W₂) :
    P.W₂ℂ = Submodule.span ℂ (Set.range fun i => bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iR i))) := by
  rw [W₂ℂ, ← P.s22b_span_uR hW, s22b_span_bcV_range]; rfl

theorem s22b_dual_ab (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n)) :
    pairing ℂ n (bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iL i)))
      (bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iR j))) = if i = j then 1 else 0 := by
  rw [s22b_pairing_bcV, P.s22b_pairing_bV_LR hW]
  split_ifs <;> simp

/-- `V_ℂ = W_{1,ℂ} ⊕ W_{2,ℂ}`. -/
theorem s22b_isCompl_Wℂ (hW : IsCompl P.W₁ P.W₂) : IsCompl P.W₁ℂ P.W₂ℂ := by
  have hn := P.s22b_n_pos
  have h1 : Module.finrank ℂ P.W₁ℂ = 2 * n := by
    rw [W₁ℂ, s22b_finrank_span_bcV]; exact P.isPure.2.2
  have h2 : Module.finrank ℂ P.W₂ℂ = 2 * n := by
    rw [W₂ℂ, s22b_finrank_span_bcV]; exact P.isPure₂.2.2
  have hu₂ : bcS (Kd d) ℂ n P.u₂ ≠ 0 := (s22b_isEvenPureSpinor_bcS (F' := ℂ) hn P.isPure₂).ne_zero hn
  have hdisj : P.W₁ℂ ⊓ P.W₂ℂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Submodule.mem_bot]
    rw [P.s22b_W₁ℂ_span hW] at hx1
    rw [s22b_expand_of_span _ _ (P.s22b_dual_ab hW) hx1]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hb : bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iR i)) ∈ P.W₂ℂ :=
      Submodule.subset_span ⟨_, P.s22b_bV_R_mem hW i, rfl⟩
    rw [P.s22b_W₂ℂ_eq hn] at hb
    have hx2' : x ∈ ann ℂ n (bcS (Kd d) ℂ n P.u₂) := by rwa [← P.s22b_W₂ℂ_eq hn]
    rw [s22b_pairing_of_mem_ann hu₂ hx2' hb, zero_smul]
  constructor
  · rw [disjoint_iff]; exact hdisj
  · rw [codisjoint_iff]
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq P.W₁ℂ P.W₂ℂ
    rw [hdisj, finrank_bot, h1, h2] at this
    rw [Module.finrank_eq_card_basis (basisV ℂ n), Fintype.card_fin]
    omega

end S22bHodgeA

/-- "**`⋀^k V_ℂ = ⊕_{p+q=k, a+b=k} ⋀^{p,q}_{a,b} V`**" (§2.2): the actions of `K^×` and of `ℂ^×`
on `⋀• V_ℂ` commute (this uses that `P` is contained in the Hodge ring, through Lemma 2.2.6), and
`⋀^k V_ℂ` is the direct sum of their joint weight spaces. -/
theorem wedgePQAB_decomp (hd : 0 < d) (hP : ¬ P.IsIsotropic) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) (k : ℕ) :
    iSupIndep (fun pa : Fin (k + 1) × Fin (k + 1) =>
        P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J)
          pa.1 (k - pa.1) pa.2 (k - pa.2)) ∧
      ⨆ pa : Fin (k + 1) × Fin (k + 1),
          P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J)
            pa.1 (k - pa.1) pa.2 (k - pa.2) = ⋀[ℂ]^k (V ℂ n) := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have hn := P.s22b_n_pos
  have hWℂ := P.s22b_isCompl_Wℂ hW
  have hV := s22b_isCompl_V10 J hJ
  have hU : (fun pa : Fin (k + 1) × Fin (k + 1) =>
      P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J)
        pa.1 (k - pa.1) pa.2 (k - pa.2)) = fun pa =>
      pqPiece (V10 n (productStructure n J)) (V01 n (productStructure n J)) pa.1 (k - pa.1) ⊓
        pqPiece P.W₁ℂ P.W₂ℂ pa.2 (k - pa.2) := by
    funext pa
    rw [wedgePQAB, P.wedgeAB_eq hd hW, s22b_span_bcExt_pqPiece]
    rfl
  rw [hU]
  refine ⟨s22b_iSupIndep_inf _ _ (s22b_iSupIndep_pqPiece hV k) (s22b_iSupIndep_pqPiece hWℂ k),
    le_antisymm (iSup_le fun pa => inf_le_left.trans ?_) ?_⟩
  · have := s22b_pqPiece_le (V10 n (productStructure n J)) (V01 n (productStructure n J))
      pa.1 (k - pa.1)
    rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp pa.1.2)] at this
  obtain ⟨g, hfix, h10, h01⟩ := P.s22b_torus_P J hJ hPJ
  set T : V ℂ n →ₗ[ℂ] V ℂ n := (rho ℂ n g : V ℂ n →ₗ[ℂ] V ℂ n)
  have hTW₁ : ∀ v ∈ P.W₁ℂ, T v ∈ P.W₁ℂ := fun v hv => by
    rw [P.s22b_W₁ℂ_eq hn] at hv ⊢
    exact s22b_rho_mem_ann_of_fix g (hfix _ P.s22b_u₁_mem_PK) hv
  have hTW₂ : ∀ v ∈ P.W₂ℂ, T v ∈ P.W₂ℂ := fun v hv => by
    rw [P.s22b_W₂ℂ_eq hn] at hv ⊢
    exact s22b_rho_mem_ann_of_fix g (hfix _ P.s22b_u₂_mem_PK) hv
  intro x hx
  have hxA := s22b_wedge_le_iSup hV.sup_eq_top k hx
  clear hx
  induction hxA using Submodule.iSup_induction' with
  | mem p y hy =>
    have hyk : y ∈ ⋀[ℂ]^k (V ℂ n) := by
      have := s22b_pqPiece_le (V10 n (productStructure n J)) (V01 n (productStructure n J))
        p (k - p)
      rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.2)] at this
      exact this hy
    have hyT : ExteriorAlgebra.map T y = ((1 / 2 : ℂ) ^ (p : ℕ) * 2 ^ (k - p)) • y :=
      s22b_map_pqPiece T _ _ h10 h01 hy
    have hyB := s22b_wedge_le_iSup hWℂ.sup_eq_top k hyk
    obtain ⟨f, hf, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hyB
    have heig : ∀ a, ExteriorAlgebra.map T (f a) =
        ((1 / 2 : ℂ) ^ (p : ℕ) * 2 ^ (k - p)) • f a := by
      have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
        (s22b_iSupIndep_pqPiece hWℂ k) f.support
        (fun a => ExteriorAlgebra.map T (f a) - ((1 / 2 : ℂ) ^ (p : ℕ) * 2 ^ (k - p)) • f a)
        (fun a _ => Submodule.sub_mem _ (s22b_map_mem_pqPiece T hTW₁ hTW₂ (hf a))
          (Submodule.smul_mem _ _ (hf a)))
        (by
          rw [Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum]
          have : ∑ a ∈ f.support, f a = y := hfsum
          rw [this, hyT, sub_self])
      intro a
      by_cases ha : a ∈ f.support
      · exact sub_eq_zero.mp (hind a ha)
      · rw [Finsupp.notMem_support_iff.mp ha, map_zero, smul_zero]
    rw [← hfsum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hfa_k : f a ∈ ⋀[ℂ]^k (V ℂ n) := by
      have := s22b_pqPiece_le P.W₁ℂ P.W₂ℂ a (k - a)
      rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp a.2)] at this
      exact this (hf a)
    have hfaA := s22b_mem_of_separating
      (fun p' : Fin (k + 1) => pqPiece (V10 n (productStructure n J))
        (V01 n (productStructure n J)) p' (k - p'))
      (s22b_iSupIndep_pqPiece hV k) (fun _ : Unit => (ExteriorAlgebra.map T).toLinearMap)
      (fun _ p' => (1 / 2 : ℂ) ^ (p' : ℕ) * 2 ^ (k - p'))
      (fun _ p' z hz => s22b_map_pqPiece T _ _ h10 h01 hz) p
      (fun p' hp' => ⟨(), s22b_char_ne (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp p'.2)
        (fun h => hp' (Fin.ext h))⟩)
      (s22b_wedge_le_iSup hV.sup_eq_top k hfa_k) (fun _ => heig a)
    exact Submodule.mem_iSup_of_mem (p, a) ⟨hfaA, hf a⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy

/-- "**`W₁^{1,0} = ⋀^{1,0}_{1,0} V`**" (§2.2), under the hypotheses of Lemma 2.2.6. -/
theorem map_ι_W₁ℂ_V10 (hd : 0 < d) (hP : ¬ P.IsIsotropic) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    (P.W₁ℂ ⊓ V10 n (productStructure n J)).map (ExteriorAlgebra.ι ℂ) =
      P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J) 1 0 1 0 := by
  have _ := hJ
  have _ := hPJ
  have hW := P.isCompl_of_not_isIsotropic hd hP
  -- `⋀^{1,0}`-type pieces are images of subspaces under `ι`
  have hspan : ∀ (A : Submodule (Kd d) (V (Kd d) n)),
      Submodule.span ℂ (bcExt (Kd d) ℂ n '' (A.map (ExteriorAlgebra.ι (Kd d)) :
        Set (ExteriorAlgebra (Kd d) (V (Kd d) n)))) =
      (Submodule.span ℂ (bcV (Kd d) ℂ n '' A)).map (ExteriorAlgebra.ι ℂ) := by
    intro A
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => s22b_bcExt_ι v
  rw [wedgePQAB, s22b_pqPiece_one_zero, P.wedgeAB_eq hd hW, s22b_pqPiece_one_zero, hspan,
    ← Submodule.map_inf _ s22b_ι_injective, inf_comm]
  rfl

/-- "**`W₁^{0,1} = ⋀^{0,1}_{1,0} V`**" (§2.2). -/
theorem map_ι_W₁ℂ_V01 (hd : 0 < d) (hP : ¬ P.IsIsotropic) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    (P.W₁ℂ ⊓ V01 n (productStructure n J)).map (ExteriorAlgebra.ι ℂ) =
      P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J) 0 1 1 0 := by
  have _ := hJ
  have _ := hPJ
  have hW := P.isCompl_of_not_isIsotropic hd hP
  -- `⋀^{1,0}`-type pieces are images of subspaces under `ι`
  have hspan : ∀ (A : Submodule (Kd d) (V (Kd d) n)),
      Submodule.span ℂ (bcExt (Kd d) ℂ n '' (A.map (ExteriorAlgebra.ι (Kd d)) :
        Set (ExteriorAlgebra (Kd d) (V (Kd d) n)))) =
      (Submodule.span ℂ (bcV (Kd d) ℂ n '' A)).map (ExteriorAlgebra.ι ℂ) := by
    intro A
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => s22b_bcExt_ι v
  rw [wedgePQAB, s22b_pqPiece_zero_one, P.wedgeAB_eq hd hW, s22b_pqPiece_one_zero, hspan,
    ← Submodule.map_inf _ s22b_ι_injective, inf_comm]
  rfl

/-- "**`W₂^{1,0} = ⋀^{1,0}_{0,1} V`**" (§2.2). -/
theorem map_ι_W₂ℂ_V10 (hd : 0 < d) (hP : ¬ P.IsIsotropic) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    (P.W₂ℂ ⊓ V10 n (productStructure n J)).map (ExteriorAlgebra.ι ℂ) =
      P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J) 1 0 0 1 := by
  have _ := hJ
  have _ := hPJ
  have hW := P.isCompl_of_not_isIsotropic hd hP
  -- `⋀^{1,0}`-type pieces are images of subspaces under `ι`
  have hspan : ∀ (A : Submodule (Kd d) (V (Kd d) n)),
      Submodule.span ℂ (bcExt (Kd d) ℂ n '' (A.map (ExteriorAlgebra.ι (Kd d)) :
        Set (ExteriorAlgebra (Kd d) (V (Kd d) n)))) =
      (Submodule.span ℂ (bcV (Kd d) ℂ n '' A)).map (ExteriorAlgebra.ι ℂ) := by
    intro A
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => s22b_bcExt_ι v
  rw [wedgePQAB, s22b_pqPiece_one_zero, P.wedgeAB_eq hd hW, s22b_pqPiece_zero_one, hspan,
    ← Submodule.map_inf _ s22b_ι_injective, inf_comm]
  rfl

/-- "**`W₂^{0,1} = ⋀^{0,1}_{0,1} V`**" (§2.2). -/
theorem map_ι_W₂ℂ_V01 (hd : 0 < d) (hP : ¬ P.IsIsotropic) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    (P.W₂ℂ ⊓ V01 n (productStructure n J)).map (ExteriorAlgebra.ι ℂ) =
      P.wedgePQAB (P.isCompl_of_not_isIsotropic hd hP) (productStructure n J) 0 1 0 1 := by
  have _ := hJ
  have _ := hPJ
  have hW := P.isCompl_of_not_isIsotropic hd hP
  -- `⋀^{1,0}`-type pieces are images of subspaces under `ι`
  have hspan : ∀ (A : Submodule (Kd d) (V (Kd d) n)),
      Submodule.span ℂ (bcExt (Kd d) ℂ n '' (A.map (ExteriorAlgebra.ι (Kd d)) :
        Set (ExteriorAlgebra (Kd d) (V (Kd d) n)))) =
      (Submodule.span ℂ (bcV (Kd d) ℂ n '' A)).map (ExteriorAlgebra.ι ℂ) := by
    intro A
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => s22b_bcExt_ι v
  rw [wedgePQAB, s22b_pqPiece_zero_one, P.wedgeAB_eq hd hW, s22b_pqPiece_zero_one, hspan,
    ← Submodule.map_inf _ s22b_ι_injective, inf_comm]
  rfl

/-! ## The integral group `Spin(V)_P` and its invariants -/

/-- `(⋀^k V_ℚ)^{Spin(V)_P}`: the `Spin(V)_P`-invariant rational classes of degree `k` on
`X × X̂`. -/
noncomputable def invQ (k : ℕ) : Submodule ℚ (ExteriorAlgebra ℚ (V ℚ n)) :=
  ⋀[ℚ]^k (V ℚ n) ⊓ invariantsExt ℚ n P.spinPZ

/-- `(⋀^k V_K)^{Spin(V)_P}`: the vectors of `⋀^k V_K` invariant under the integral group
`Spin(V)_P`, acting through `Spin(V) ⊆ Spin(V_ℚ) → Spin(V_K)`. -/
noncomputable def invK (k : ℕ) : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)) :=
  ⋀[Kd d]^k (V (Kd d) n) ⊓ invariantsExt (Kd d) n (P.spinPZ.map (bcSpin ℚ (Kd d) n))

/-! ## The `Spin(V)_P`-invariants of `⋀• V_K` (helpers for Lemma 2.2.7) -/

section S22bInvariants

variable {P}

theorem s22b_omega_mem_pqPiece (hW : IsCompl P.W₁ P.W₂) :
    s22b_omega hW ∈ pqPiece P.W₁ P.W₂ 1 1 := by
  rw [s22b_omega]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨fun _ => P.s22b_bV hW (s22b_iL i), fun _ => P.s22b_bV hW (s22b_iR i),
      fun _ => P.s22b_bV_L_mem hW i, fun _ => P.s22b_bV_R_mem hW i, ?_⟩
  simp

theorem s22b_omega_pow_mem (hW : IsCompl P.W₁ P.W₂) (a : ℕ) :
    s22b_omega hW ^ a ∈ pqPiece P.W₁ P.W₂ a a :=
  s22b_pqPiece_pow (s22b_omega_mem_pqPiece hW) a

theorem s22b_omega_pow_mem_wedge (hW : IsCompl P.W₁ P.W₂) (a : ℕ) :
    s22b_omega hW ^ a ∈ ⋀[Kd d]^(2 * a) (V (Kd d) n) := by
  have h := s22b_pqPiece_le _ _ _ _ (s22b_omega_pow_mem hW a)
  rwa [← two_mul] at h

/-- `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `⋀^{2n} W₁` by `det₁` (proof of `lemma2_2_7_K_det₁`). -/
theorem s22b_rhoExt_top₁ (g : P.spinL₁L₂) (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hx : x ∈ pqPiece P.W₁ P.W₂ (2 * n) 0) : rhoExt (Kd d) n g x = P.det₁ g • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, -, rfl⟩ := hy
    simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one, rhoExt]
    rw [ExteriorAlgebra.map_apply_ιMulti]
    set a' : Fin (2 * n) → P.W₁ := fun i => ⟨a i, ha i⟩
    have h1 : a = P.W₁.subtype ∘ a' := rfl
    have h2 : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∘ a =
        P.W₁.subtype ∘ (((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
          (fun v hv => P.rho_mem_W₁ g v hv)) ∘ a') := by
      funext i; rfl
    rw [h2, h1]
    exact s22b_alternating_comp P.s22b_b₁
      ((ExteriorAlgebra.ιMulti (Kd d) (2 * n)).compLinearMap P.W₁.subtype) _ a'
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `⋀^{2n} W₂` by `det₂`. -/
theorem s22b_rhoExt_top₂ (hW : IsCompl P.W₁ P.W₂) (g : P.spinL₁L₂)
    (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hx : x ∈ pqPiece P.W₁ P.W₂ 0 (2 * n)) : rhoExt (Kd d) n g x = P.det₂ g • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, -, hb, rfl⟩ := hy
    simp only [ExteriorAlgebra.ιMulti_zero_apply, one_mul, rhoExt]
    rw [ExteriorAlgebra.map_apply_ιMulti]
    set b' : Fin (2 * n) → P.W₂ := fun i => ⟨b i, hb i⟩
    have h1 : b = P.W₂.subtype ∘ b' := rfl
    have h2 : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∘ b =
        P.W₂.subtype ∘ (((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
          (fun v hv => P.rho_mem_W₂ g v hv)) ∘ b') := by
      funext i; rfl
    rw [h2, h1]
    exact s22b_alternating_comp (P.s22b_b₂ hW)
      ((ExteriorAlgebra.ιMulti (Kd d) (2 * n)).compLinearMap P.W₂.subtype) _ b'
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

omit P in
theorem s22b_u₂_ne_zero (P : KSecant n d) : P.u₂ ≠ 0 :=
  P.linIndep.ne_zero 1

/-- The characters `χ₁`, `χ₂` (hence `det₁`, `det₂`) are trivial on `Spin(V)_P`. -/
theorem s22b_χ₁_eq_one (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) :
    P.χ₁ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ = 1 := by
  have h : m (Kd d) n (bcC ℚ (Kd d) n g) P.u₁ =
      P.χ₁ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ • P.u₁ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp (P.s22b_bcSpin_mem_spinL₁L₂ g hg)).1)
  have h2 := P.s22b_bcSpin_fix_PK g hg P.u₁ (Submodule.subset_span (by simp))
  rw [h2] at h
  have : (1 - P.χ₁ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩) • P.u₁ = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  have := (smul_eq_zero.mp this).resolve_right P.u₁_ne_zero
  exact (sub_eq_zero.mp this).symm

theorem s22b_χ₂_eq_one (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) :
    P.χ₂ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ = 1 := by
  have h : m (Kd d) n (bcC ℚ (Kd d) n g) P.u₂ =
      P.χ₂ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ • P.u₂ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp (P.s22b_bcSpin_mem_spinL₁L₂ g hg)).2)
  have h2 := P.s22b_bcSpin_fix_PK g hg P.u₂ (Submodule.subset_span (by simp))
  rw [h2] at h
  have : (1 - P.χ₂ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩) • P.u₂ = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  have := (smul_eq_zero.mp this).resolve_right (s22b_u₂_ne_zero P)
  exact (sub_eq_zero.mp this).symm

theorem s22b_mem_spinPℚ_of_mem_spinPZ {g : Spin ℚ n} (hg : g ∈ P.spinPZ) : g ∈ P.spinPℚ :=
  (Subgroup.mem_inf.mp (show g ∈ SpinZ n ⊓ P.spinPℚ from hg)).2

theorem s22b_det₁_eq_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n)
    (hg : g ∈ P.spinPℚ) : P.det₁ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ = 1 := by
  rw [← P.χ₁_sq hd hW.inf_eq_bot, s22b_χ₁_eq_one g hg, one_pow]

theorem s22b_det₂_eq_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (g : Spin ℚ n)
    (hg : g ∈ P.spinPℚ) : P.det₂ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg⟩ = 1 := by
  rw [← P.χ₂_sq hd hW.inf_eq_bot, s22b_χ₂_eq_one g hg, one_pow]

/-- `⋀^{2n} W₁` is fixed by `Spin(V)_P`. -/
theorem s22b_top₁_inv (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    {x : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hx : x ∈ pqPiece P.W₁ P.W₂ (2 * n) 0)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) : rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x = x := by
  have hg' := s22b_mem_spinPℚ_of_mem_spinPZ hg
  have h := s22b_rhoExt_top₁ ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg'⟩ x hx
  rwa [s22b_det₁_eq_one hd hW g hg', one_smul] at h

/-- `⋀^{2n} W₂` is fixed by `Spin(V)_P`. -/
theorem s22b_top₂_inv (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    {x : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hx : x ∈ pqPiece P.W₁ P.W₂ 0 (2 * n))
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) : rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x = x := by
  have hg' := s22b_mem_spinPℚ_of_mem_spinPZ hg
  have h := s22b_rhoExt_top₂ hW ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g hg'⟩ x hx
  rwa [s22b_det₂_eq_one hd hW g hg', one_smul] at h

theorem s22b_repr_basis (hW : IsCompl P.W₁ P.W₂) (S T : Finset (Fin (2 * n + 2 * n))) :
    (P.s22b_bV hW).ExteriorAlgebra.repr ((P.s22b_bV hW).ExteriorAlgebra S) T =
      if S = T then 1 else 0 := by
  rw [Module.Basis.repr_self, Finsupp.single_apply]

theorem s22b_eL_mem (hW : IsCompl P.W₁ P.W₂) :
    (P.s22b_bV hW).ExteriorAlgebra s22b_allL ∈ pqPiece P.W₁ P.W₂ (2 * n) 0 := by
  have h := s22b_basis_mem_pqPiece hW s22b_allL
  rwa [Finset.inter_self, s22b_card_allL, Nat.sub_self] at h

theorem s22b_eR_mem (hW : IsCompl P.W₁ P.W₂) :
    (P.s22b_bV hW).ExteriorAlgebra s22b_allR ∈ pqPiece P.W₁ P.W₂ 0 (2 * n) := by
  have h := s22b_basis_mem_pqPiece hW s22b_allR
  rwa [s22b_allR_inter_allL, Finset.card_empty, s22b_card_allR, Nat.sub_zero] at h

theorem s22b_eq_smul_of_support (hW : IsCompl P.W₁ P.W₂) (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (S₀ : Finset (Fin (2 * n + 2 * n)))
    (h : ∀ S, (P.s22b_bV hW).ExteriorAlgebra.repr x S ≠ 0 → S = S₀) :
    x = (P.s22b_bV hW).ExteriorAlgebra.repr x S₀ • (P.s22b_bV hW).ExteriorAlgebra S₀ := by
  conv_lhs => rw [← (P.s22b_bV hW).ExteriorAlgebra.sum_repr x]
  rw [Finset.sum_eq_single S₀]
  · intro S _ hS
    by_cases h0 : (P.s22b_bV hW).ExteriorAlgebra.repr x S = 0
    · rw [h0, zero_smul]
    · exact absurd (h S h0) hS
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-- `⋀^{2n} W₁` is the line spanned by `u₁ ∧ ⋯ ∧ u_{2n}`. -/
theorem s22b_pq_top₁_eq (hW : IsCompl P.W₁ P.W₂) :
    pqPiece P.W₁ P.W₂ (2 * n) 0 =
      Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allL} := by
  apply le_antisymm
  · intro x hx
    rw [s22b_eq_smul_of_support hW x s22b_allL (fun S hS => by
      obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW hx S hS
      have h3 : S ∩ s22b_allL = s22b_allL := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by rw [h1, s22b_card_allL])
      have h4 : s22b_allL ⊆ S := h3 ▸ Finset.inter_subset_left
      exact (Finset.eq_of_subset_of_card_le h4 (by rw [h2, s22b_card_allL]; omega)).symm)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact s22b_eL_mem hW

/-- `⋀^{2n} W₂` is the line spanned by `u₁* ∧ ⋯ ∧ u_{2n}*`. -/
theorem s22b_pq_top₂_eq (hW : IsCompl P.W₁ P.W₂) :
    pqPiece P.W₁ P.W₂ 0 (2 * n) =
      Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allR} := by
  apply le_antisymm
  · intro x hx
    rw [s22b_eq_smul_of_support hW x s22b_allR (fun S hS => by
      obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW hx S hS
      have h4 : S ⊆ s22b_allR := by
        intro m hm
        rcases s22b_iLR_cases m with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exfalso
          have : s22b_iL i ∈ S ∩ s22b_allL := Finset.mem_inter.mpr ⟨hm, s22b_iL_mem_allL i⟩
          rw [Finset.card_eq_zero.mp h1] at this
          simp at this
        · exact s22b_iR_mem_allR j
      exact Finset.eq_of_subset_of_card_le h4 (by rw [h2, s22b_card_allR]; omega))]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact s22b_eR_mem hW

theorem s22b_omega_pow_repr_allL (hW : IsCompl P.W₁ P.W₂) (a : ℕ) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) s22b_allL = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW (s22b_omega_pow_mem hW a) _ h
  rw [Finset.inter_self, s22b_card_allL] at h1
  rw [s22b_card_allL] at h2
  have := P.s22b_n_pos
  omega

theorem s22b_omega_pow_repr_allR (hW : IsCompl P.W₁ P.W₂) (a : ℕ) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) s22b_allR = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW (s22b_omega_pow_mem hW a) _ h
  rw [s22b_allR_inter_allL, Finset.card_empty] at h1
  rw [s22b_card_allR] at h2
  have := P.s22b_n_pos
  omega

theorem s22b_omega_pow_inv (hW : IsCompl P.W₁ P.W₂) (a : ℕ) (g : Spin ℚ n) (hg : g ∈ P.spinPZ) :
    rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) (s22b_omega hW ^ a) = s22b_omega hW ^ a := by
  have h := s22b_rhoExt_omega hW ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g
    (s22b_mem_spinPℚ_of_mem_spinPZ hg)⟩
  rw [map_pow]
  exact congrArg (· ^ a) h

theorem s22b_omega_pow_repr_ne (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (a : ℕ) (ha : a ≤ 2 * n)
    (I₀ : Finset (Fin (2 * n))) (hI₀ : I₀.card = a) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) (s22b_Dset I₀) ≠ 0 := fun h0 =>
  s22b_omega_pow_ne_zero hW a ha (s22b_inv_eq_zero hd hW _ (s22b_omega_pow_inv hW a) a
    (s22b_omega_pow_mem_wedge hW a) I₀ hI₀ h0 (s22b_omega_pow_repr_allL hW a)
    (s22b_omega_pow_repr_allR hW a))

/-- An invariant of degree `2a` with vanishing `allL`, `allR` coefficients is a multiple of
`ω^a`. -/
theorem s22b_inv_mem_span_omega (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z) (a : ℕ) (ha : a ≤ 2 * n)
    (hzk : z ∈ ⋀[Kd d]^(2 * a) (V (Kd d) n))
    (hL : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL = 0)
    (hR : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR = 0) :
    z ∈ Submodule.span (Kd d) {s22b_omega hW ^ a} := by
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * n))))
    (by simpa using ha)
  have hr := s22b_omega_pow_repr_ne hd hW a ha I₀ hI₀
  set c := (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset I₀) /
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) (s22b_Dset I₀)
  have hw := s22b_inv_eq_zero hd hW (z - c • s22b_omega hW ^ a)
    (fun g hg => by rw [map_sub, map_smul, hz g hg, s22b_omega_pow_inv hW a g hg]) a
    (Submodule.sub_mem _ hzk (Submodule.smul_mem _ _ (s22b_omega_pow_mem_wedge hW a))) I₀ hI₀
    (by rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        simp only [c, div_mul_cancel₀ _ hr, sub_self])
    (by rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hL,
      s22b_omega_pow_repr_allL, smul_zero, sub_zero])
    (by rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hR,
      s22b_omega_pow_repr_allR, smul_zero, sub_zero])
  rw [sub_eq_zero] at hw
  rw [hw]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem s22b_mem_invK_iff (k : ℕ) (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    z ∈ P.invK k ↔ z ∈ ⋀[Kd d]^k (V (Kd d) n) ∧
      ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z := by
  rw [invK, Submodule.mem_inf, s22b_mem_invariantsExt_map]

theorem s22b_conjExt_mem_invK (k : ℕ) (y : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hy : y ∈ P.invK k) : conjExt (Kd.σ d) n y ∈ P.invK k := by
  rw [s22b_mem_invK_iff] at hy ⊢
  refine ⟨s22b_conjExt_mem_exteriorPower _ hy.1, fun g hg => ?_⟩
  rw [← s22b_conjExt_rhoExt_bcSpin, hy.2 g hg]

theorem s22b_mem_invQ_iff (k : ℕ) (x : ExteriorAlgebra ℚ (V ℚ n)) :
    x ∈ P.invQ k ↔ bcExt ℚ (Kd d) n x ∈ P.invK k := by
  rw [s22b_mem_invK_iff, invQ, Submodule.mem_inf, s22b_bcExt_mem_iff]
  refine and_congr Iff.rfl ⟨fun h g hg => ?_, fun h g hg => ?_⟩
  · have h' : rhoExt ℚ n g x = x := h g hg
    rw [s22b_rhoExt_bcExt, h']
  · apply s22b_bcExt_injective (F' := Kd d)
    rw [← s22b_rhoExt_bcExt, h g hg]

theorem s22b_finrank_invQ (hd : 0 < d) (k : ℕ) :
    Module.finrank ℚ (P.invQ k) = Module.finrank (Kd d) (P.invK k) :=
  s22b_finrank_descent hd _ _ (s22b_mem_invQ_iff k) (s22b_conjExt_mem_invK k)

theorem s22b_invK_odd (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (k : ℕ) (hk : Odd k) :
    P.invK k = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [s22b_mem_invK_iff] at hz
  rw [Submodule.mem_bot]
  apply (P.s22b_bV hW).ExteriorAlgebra.repr.injective
  refine Finsupp.ext fun S => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hS
  have hcard := s22b_card_of_repr_ne _ hz.1 S hS
  obtain ⟨m, hm⟩ := hk
  rcases s22b_inv_support hd hW z hz.2 S hS with ⟨I, rfl⟩ | rfl | rfl
  · rw [s22b_card_Dset] at hcard; omega
  · rw [s22b_card_allL] at hcard; omega
  · rw [s22b_card_allR] at hcard; omega

theorem s22b_invK_eq_span (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (a : ℕ) (ha : a ≤ 2 * n)
    (han : a ≠ n) : P.invK (2 * a) = Submodule.span (Kd d) {s22b_omega hW ^ a} := by
  apply le_antisymm
  · intro z hz
    rw [s22b_mem_invK_iff] at hz
    refine s22b_inv_mem_span_omega hd hW z hz.2 a ha hz.1 ?_ ?_
    · by_contra h
      have := s22b_card_of_repr_ne _ hz.1 _ h
      rw [s22b_card_allL] at this; omega
    · by_contra h
      have := s22b_card_of_repr_ne _ hz.1 _ h
      rw [s22b_card_allR] at this; omega
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, s22b_mem_invK_iff]
    exact ⟨s22b_omega_pow_mem_wedge hW a, s22b_omega_pow_inv hW a⟩

theorem s22b_eL_mem_wedge (hW : IsCompl P.W₁ P.W₂) :
    (P.s22b_bV hW).ExteriorAlgebra s22b_allL ∈ ⋀[Kd d]^(2 * n) (V (Kd d) n) := by
  have h := s22b_basis_mem_exteriorPower (P.s22b_bV hW) s22b_allL
  rwa [s22b_card_allL] at h

theorem s22b_eR_mem_wedge (hW : IsCompl P.W₁ P.W₂) :
    (P.s22b_bV hW).ExteriorAlgebra s22b_allR ∈ ⋀[Kd d]^(2 * n) (V (Kd d) n) := by
  have h := s22b_basis_mem_exteriorPower (P.s22b_bV hW) s22b_allR
  rwa [s22b_card_allR] at h

theorem s22b_residual_repr_L (hW : IsCompl P.W₁ P.W₂) (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (z -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR)
      s22b_allL = 0 := by
  have hLR := s22b_allL_ne_allR P.s22b_n_pos
  rw [map_sub, map_sub, map_smul, map_smul, Finsupp.sub_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, s22b_repr_basis, s22b_repr_basis]
  simp [hLR.symm]

theorem s22b_residual_repr_R (hW : IsCompl P.W₁ P.W₂) (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (z -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR)
      s22b_allR = 0 := by
  have hLR := s22b_allL_ne_allR P.s22b_n_pos
  rw [map_sub, map_sub, map_smul, map_smul, Finsupp.sub_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, s22b_repr_basis, s22b_repr_basis]
  simp [hLR]

theorem s22b_residual_mem (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (hzk : z ∈ ⋀[Kd d]^(2 * n) (V (Kd d) n)) :
    z - (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR ∈
      Submodule.span (Kd d) {s22b_omega hW ^ n} := by
  have hinv : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) (z -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR) =
      (z - (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR) := by
    intro g hg
    rw [map_sub, map_sub, map_smul, map_smul, hz g hg,
      s22b_top₁_inv hd hW (s22b_eL_mem hW) g hg, s22b_top₂_inv hd hW (s22b_eR_mem hW) g hg]
  have hk : z - (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL •
      (P.s22b_bV hW).ExteriorAlgebra s22b_allL -
      (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR ∈
      ⋀[Kd d]^(2 * n) (V (Kd d) n) :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hzk (Submodule.smul_mem _ _ (s22b_eL_mem_wedge hW)))
      (Submodule.smul_mem _ _ (s22b_eR_mem_wedge hW))
  exact s22b_inv_mem_span_omega hd hW _ hinv n (by omega) hk (s22b_residual_repr_L hW z)
    (s22b_residual_repr_R hW z)

/-- The middle degree: `(⋀^{2n} V_K)^{Spin(V)_P} = ⟨e_L⟩ ⊕ ⟨e_R⟩ ⊕ ⟨ω^n⟩`. -/
theorem s22b_invK_middle (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    P.invK (2 * n) = Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allL} ⊔
      Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allR} ⊔
      Submodule.span (Kd d) {s22b_omega hW ^ n} := by
  apply le_antisymm
  · intro z hz
    rw [s22b_mem_invK_iff] at hz
    have hw := s22b_residual_mem hd hW z hz.2 hz.1
    rw [sub_sub] at hw
    rw [← add_sub_cancel ((P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL •
      (P.s22b_bV hW).ExteriorAlgebra s22b_allL + (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR •
      (P.s22b_bV hW).ExteriorAlgebra s22b_allR) z]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
      (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))))
      (Submodule.mem_sup_right hw)
  · refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, s22b_mem_invK_iff]
    · exact ⟨s22b_eL_mem_wedge hW, fun g hg => s22b_top₁_inv hd hW (s22b_eL_mem hW) g hg⟩
    · exact ⟨s22b_eR_mem_wedge hW, fun g hg => s22b_top₂_inv hd hW (s22b_eR_mem hW) g hg⟩
    · exact ⟨s22b_omega_pow_mem_wedge hW n, s22b_omega_pow_inv hW n⟩

theorem s22b_invK_inf_pq (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    P.invK (2 * n) ⊓ pqPiece P.W₁ P.W₂ n n = Submodule.span (Kd d) {s22b_omega hW ^ n} := by
  have hn := P.s22b_n_pos
  apply le_antisymm
  · rintro z ⟨hz, hzp⟩
    rw [SetLike.mem_coe, s22b_mem_invK_iff] at hz
    refine s22b_inv_mem_span_omega hd hW z hz.2 n (by omega) hz.1 ?_ ?_
    · by_contra h
      have := (s22b_support_pqPiece hW hzp _ h).1
      rw [Finset.inter_self, s22b_card_allL] at this; omega
    · by_contra h
      have := (s22b_support_pqPiece hW hzp _ h).1
      rw [s22b_allR_inter_allL, Finset.card_empty] at this; omega
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨?_, s22b_omega_pow_mem hW n⟩
    rw [SetLike.mem_coe, s22b_mem_invK_iff]
    exact ⟨s22b_omega_pow_mem_wedge hW n, s22b_omega_pow_inv hW n⟩

theorem s22b_linIndep_three (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    LinearIndependent (Kd d) ![(P.s22b_bV hW).ExteriorAlgebra s22b_allL,
      (P.s22b_bV hW).ExteriorAlgebra s22b_allR, s22b_omega hW ^ n] := by
  have hn := P.s22b_n_pos
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * n))))
    (show n ≤ Finset.univ.card by simp; omega)
  have hr := s22b_omega_pow_repr_ne hd hW n (by omega) I₀ hI₀
  have hLR := s22b_allL_ne_allR hn
  have hDL := s22b_Dset_ne_allL hn I₀
  have hDR := s22b_Dset_ne_allR hn I₀
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have h1 := congrArg (fun x => (P.s22b_bV hW).ExteriorAlgebra.repr x s22b_allL) hg
  have h2 := congrArg (fun x => (P.s22b_bV hW).ExteriorAlgebra.repr x s22b_allR) hg
  have h3 := congrArg (fun x => (P.s22b_bV hW).ExteriorAlgebra.repr x (s22b_Dset I₀)) hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s22b_repr_basis,
    s22b_omega_pow_repr_allL, s22b_omega_pow_repr_allR, map_zero, Finsupp.zero_apply,
    smul_eq_mul] at h1 h2 h3
  simp only [hLR, hLR.symm, hDL.symm, hDR.symm, ↓reduceIte, mul_one, mul_zero, add_zero,
    zero_add] at h1 h2 h3
  have h3' := (mul_eq_zero.mp h3).resolve_right hr
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3'

theorem s22b_finrank_invK_middle (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    Module.finrank (Kd d) (P.invK (2 * n)) = 3 := by
  have heq : Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allL} ⊔
      Submodule.span (Kd d) {(P.s22b_bV hW).ExteriorAlgebra s22b_allR} ⊔
      Submodule.span (Kd d) {s22b_omega hW ^ n} =
      Submodule.span (Kd d) (Set.range ![(P.s22b_bV hW).ExteriorAlgebra s22b_allL,
        (P.s22b_bV hW).ExteriorAlgebra s22b_allR, s22b_omega hW ^ n]) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Submodule.span_union, Submodule.span_union, sup_assoc]
  rw [s22b_invK_middle hd hW, heq, finrank_span_eq_card (s22b_linIndep_three hd hW),
    Fintype.card_fin]

/-- An invariant vector with vanishing coefficients at `D(I_a)` (`a ≤ 2n`), `allL`, `allR` is
zero (no homogeneity assumption). -/
theorem s22b_inv_eq_zero' (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z)
    (Isel : ℕ → Finset (Fin (2 * n))) (hIsel : ∀ a ≤ 2 * n, (Isel a).card = a)
    (h0 : ∀ a ≤ 2 * n, (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset (Isel a)) = 0)
    (hL : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL = 0)
    (hR : (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR = 0) : z = 0 := by
  apply (P.s22b_bV hW).ExteriorAlgebra.repr.injective
  refine Finsupp.ext fun S => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hS
  rcases s22b_inv_support hd hW z hz S hS with ⟨I, rfl⟩ | rfl | rfl
  · have hIc : I.card ≤ 2 * n := by simpa using I.card_le_univ
    exact hS ((s22b_inv_block hd hW z hz (Isel I.card) _ I (hIsel _ hIc).symm rfl).mpr
      (h0 _ hIc))
  · exact hS hL
  · exact hS hR

theorem s22b_repr_sum_omega (hW : IsCompl P.W₁ P.W₂) (c : ℕ → Kd d)
    (S : Finset (Fin (2 * n + 2 * n))) :
    (P.s22b_bV hW).ExteriorAlgebra.repr
        (∑ a ∈ Finset.range (2 * n + 1), c a • s22b_omega hW ^ a) S =
      ∑ a ∈ Finset.range (2 * n + 1),
        c a * (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) S := by
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem s22b_repr_omega_pow_Dset (hW : IsCompl P.W₁ P.W₂) (a : ℕ) (I : Finset (Fin (2 * n)))
    (ha : I.card ≠ a) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) (s22b_Dset I) = 0 := by
  by_contra h
  have := s22b_card_of_repr_ne _ (s22b_omega_pow_mem_wedge hW a) _ h
  rw [s22b_card_Dset] at this
  omega

/-- `c_L e_L + c_R e_R + Σ_{a ≤ 2n} c_a ω^a`. -/
noncomputable def s22b_combo (hW : IsCompl P.W₁ P.W₂) (cL cR : Kd d) (c : ℕ → Kd d) :
    ExteriorAlgebra (Kd d) (V (Kd d) n) :=
  cL • (P.s22b_bV hW).ExteriorAlgebra s22b_allL + cR • (P.s22b_bV hW).ExteriorAlgebra s22b_allR +
    ∑ a ∈ Finset.range (2 * n + 1), c a • s22b_omega hW ^ a

theorem s22b_combo_inv (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (cL cR : Kd d) (c : ℕ → Kd d)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) :
    rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) (s22b_combo hW cL cR c) = s22b_combo hW cL cR c := by
  unfold s22b_combo
  rw [map_add, map_add, map_smul, map_smul, map_sum, s22b_top₁_inv hd hW (s22b_eL_mem hW) g hg,
    s22b_top₂_inv hd hW (s22b_eR_mem hW) g hg]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, s22b_omega_pow_inv hW a g hg]

theorem s22b_combo_rhoExt (hW : IsCompl P.W₁ P.W₂) (g : P.spinL₁L₂) (cL cR : Kd d)
    (c : ℕ → Kd d) :
    rhoExt (Kd d) n g (s22b_combo hW cL cR c) =
      s22b_combo hW (P.det₁ g * cL) (P.det₂ g * cR) c := by
  unfold s22b_combo
  rw [map_add, map_add, map_smul, map_smul, map_sum, s22b_rhoExt_top₁ g _ (s22b_eL_mem hW),
    s22b_rhoExt_top₂ hW g _ (s22b_eR_mem hW), smul_smul, smul_smul, mul_comm cL, mul_comm cR]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_pow, s22b_rhoExt_omega hW g]

theorem s22b_combo_repr_allL (hW : IsCompl P.W₁ P.W₂) (cL cR : Kd d) (c : ℕ → Kd d) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_combo hW cL cR c) s22b_allL = cL := by
  have hLR := s22b_allL_ne_allR P.s22b_n_pos
  unfold s22b_combo
  rw [map_add, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, s22b_repr_basis, s22b_repr_basis, s22b_repr_sum_omega]
  simp [hLR.symm, s22b_omega_pow_repr_allL]

theorem s22b_combo_repr_allR (hW : IsCompl P.W₁ P.W₂) (cL cR : Kd d) (c : ℕ → Kd d) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_combo hW cL cR c) s22b_allR = cR := by
  have hLR := s22b_allL_ne_allR P.s22b_n_pos
  unfold s22b_combo
  rw [map_add, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, s22b_repr_basis, s22b_repr_basis, s22b_repr_sum_omega]
  simp [hLR, s22b_omega_pow_repr_allR]

theorem s22b_combo_repr_Dset (hW : IsCompl P.W₁ P.W₂) (cL cR : Kd d) (c : ℕ → Kd d)
    (I : Finset (Fin (2 * n))) (hI : I.card ≤ 2 * n) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_combo hW cL cR c) (s22b_Dset I) =
      c I.card * (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ I.card) (s22b_Dset I) := by
  have hn := P.s22b_n_pos
  unfold s22b_combo
  rw [map_add, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, s22b_repr_basis, s22b_repr_basis, s22b_repr_sum_omega,
    Finset.sum_eq_single I.card]
  · simp [(s22b_Dset_ne_allL hn I).symm, (s22b_Dset_ne_allR hn I).symm]
  · intro a _ hab
    rw [s22b_repr_omega_pow_Dset hW a I (Ne.symm hab), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Every `Spin(V)_P`-invariant of `⋀• V_K`** is `c_L e_L + c_R e_R + Σ_a c_a ω^a`. -/
theorem s22b_inv_decomp (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) z = z) :
    ∃ cL cR : Kd d, ∃ c : ℕ → Kd d, z = s22b_combo hW cL cR c := by
  obtain ⟨Isel, hIsel⟩ := s22b_exists_Isel (n := n)
  refine ⟨(P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allL,
    (P.s22b_bV hW).ExteriorAlgebra.repr z s22b_allR,
    fun a => (P.s22b_bV hW).ExteriorAlgebra.repr z (s22b_Dset (Isel a)) /
      (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_omega hW ^ a) (s22b_Dset (Isel a)), ?_⟩
  rw [← sub_eq_zero]
  refine s22b_inv_eq_zero' hd hW _ (fun g hg => by
    rw [map_sub, hz g hg, s22b_combo_inv hd hW _ _ _ g hg]) Isel hIsel (fun b hb => ?_) ?_ ?_
  · have hr := s22b_omega_pow_repr_ne hd hW b hb (Isel b) (hIsel b hb)
    rw [map_sub, Finsupp.sub_apply, s22b_combo_repr_Dset hW _ _ _ _ (by rw [hIsel b hb]; exact hb),
      hIsel b hb]
    simp only [div_mul_cancel₀ _ hr, sub_self]
  · rw [map_sub, Finsupp.sub_apply, s22b_combo_repr_allL, sub_self]
  · rw [map_sub, Finsupp.sub_apply, s22b_combo_repr_allR, sub_self]

/-- An element of `Spin(V_K)_{ℓ₁,ℓ₂}` acting on `W₁` by `2`, so that `det₁ ≠ 1 ≠ det₂`. -/
theorem s22b_exists_det_ne_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    ∃ g : P.spinL₁L₂, P.det₁ g ≠ 1 ∧ P.det₂ g ≠ 1 := by
  have hn := P.s22b_n_pos
  have : SMulCommClass (Kd d) (Kd d) P.W₁ := smulCommClass_self _ _
  let A : (Module.End (Kd d) P.W₁)ˣ :=
    ⟨(2 : Kd d) • 1, (2⁻¹ : Kd d) • 1, by rw [smul_mul_smul_comm, mul_inv_cancel₀ two_ne_zero,
      mul_one, one_smul], by rw [smul_mul_smul_comm, inv_mul_cancel₀ two_ne_zero, mul_one,
      one_smul]⟩
  have hdetA : LinearMap.det (A : Module.End (Kd d) P.W₁) = 2 ^ (2 * n) := by
    show LinearMap.det ((2 : Kd d) • (1 : Module.End (Kd d) P.W₁)) = _
    rw [LinearMap.det_smul, map_one, mul_one,
      show Module.finrank (Kd d) P.W₁ = 2 * n from P.isPure.2.2]
  have hA : A ∈ (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) := by
    rw [P.range_restrictW₁ hd hW.inf_eq_bot]
    show IsSquare (LinearMap.det (A : Module.End (Kd d) P.W₁))
    rw [hdetA]
    exact ⟨2 ^ n, by ring⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hA
  have h1 : P.det₁ g = 2 ^ (2 * n) := by
    rw [← P.det_restrictW₁ g, hg, hdetA]
  have h2 : (2 : Kd d) ^ (2 * n) ≠ 1 := by
    have : (1 : ℕ) < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
    intro h
    have h' : ((2 ^ (2 * n) : ℕ) : Kd d) = ((1 : ℕ) : Kd d) := by push_cast; exact h
    exact absurd (Nat.cast_injective h') (by omega)
  refine ⟨g, by rw [h1]; exact h2, ?_⟩
  rw [P.det₂_eq_inv hd hW.inf_eq_bot, h1]
  exact fun h => h2 (inv_eq_one.mp h)

/-- An invariant of `Spin(V_K)_{ℓ₁,ℓ₂}` is a combination of powers of `ω`. -/
theorem s22b_inv_spinL₁L₂ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (x : ExteriorAlgebra (Kd d) (V (Kd d) n)) (hx : ∀ g : P.spinL₁L₂, rhoExt (Kd d) n g x = x) :
    ∃ c : ℕ → Kd d, x = ∑ a ∈ Finset.range (2 * n + 1), c a • s22b_omega hW ^ a := by
  obtain ⟨cL, cR, c, hxc⟩ := s22b_inv_decomp hd hW x (fun g hg =>
    hx ⟨_, P.s22b_bcSpin_mem_spinL₁L₂ g (s22b_mem_spinPℚ_of_mem_spinPZ hg)⟩)
  obtain ⟨g₀, h1, h2⟩ := s22b_exists_det_ne_one hd hW
  have hgx := hx g₀
  rw [hxc, s22b_combo_rhoExt] at hgx
  have hL := congrArg (fun y => (P.s22b_bV hW).ExteriorAlgebra.repr y s22b_allL) hgx
  have hR := congrArg (fun y => (P.s22b_bV hW).ExteriorAlgebra.repr y s22b_allR) hgx
  simp only [s22b_combo_repr_allL, s22b_combo_repr_allR] at hL hR
  have hcL : cL = 0 := by
    have : (P.det₁ g₀ - 1) * cL = 0 := by linear_combination hL
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)
  have hcR : cR = 0 := by
    have : (P.det₂ g₀ - 1) * cR = 0 := by linear_combination hR
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  refine ⟨c, ?_⟩
  rw [hxc, s22b_combo, hcL, hcR, zero_smul, zero_smul, zero_add, zero_add]

/-- A nonzero invariant `2`-form is a nonzero multiple of `ω` (for `n ≥ 2`). -/
theorem s22b_bcExt_omega_eq (hd : 0 < d) (hn : 2 ≤ n) (hW : IsCompl P.W₁ P.W₂)
    (ω : ExteriorAlgebra ℚ (V ℚ n)) (hω : ω ∈ P.invQ 2) (hω0 : ω ≠ 0) :
    ∃ c : Kd d, c ≠ 0 ∧ bcExt ℚ (Kd d) n ω = c • s22b_omega hW := by
  have h : bcExt ℚ (Kd d) n ω ∈ P.invK (2 * 1) := (s22b_mem_invQ_iff 2 ω).mp hω
  rw [s22b_invK_eq_span hd hW 1 (by omega) (by omega), pow_one] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  refine ⟨c, fun h0 => hω0 ?_, hc.symm⟩
  apply s22b_bcExt_injective (F' := Kd d)
  rw [map_zero, ← hc, h0, zero_smul]

/-! ### Irreducibility of `⋀^k W₁` and `⋀^k W₂` under `Spin(V)_P` -/

theorem s22b_repr_H (hW : IsCompl P.W₁ P.W₂) (i j : Fin (2 * n))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) (T : Finset (Fin (2 * n + 2 * n))) :
    (P.s22b_bV hW).ExteriorAlgebra.repr (s22b_Der (P.s22b_bV hW)
      (s22b_numOp (P.s22b_bV hW) (s22b_iL i) - s22b_numOp (P.s22b_bV hW) (s22b_iR i) -
        s22b_numOp (P.s22b_bV hW) (s22b_iL j) + s22b_numOp (P.s22b_bV hW) (s22b_iR j)) z) T =
      ((if s22b_iL i ∈ T then (1 : Kd d) else 0) - (if s22b_iR i ∈ T then 1 else 0) -
        (if s22b_iL j ∈ T then 1 else 0) + (if s22b_iR j ∈ T then 1 else 0)) *
        (P.s22b_bV hW).ExteriorAlgebra.repr z T := by
  simp only [s22b_Der_add, s22b_Der_sub, LinearMap.add_apply, LinearMap.sub_apply, map_add,
    map_sub, Finsupp.add_apply, Finsupp.sub_apply, s22b_repr_Der_numOp]
  ring

theorem s22b_subset_allL_of_pq (hW : IsCompl P.W₁ P.W₂) {k : ℕ}
    {x : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hx : x ∈ pqPiece P.W₁ P.W₂ k 0)
    (S : Finset (Fin (2 * n + 2 * n))) (hS : (P.s22b_bV hW).ExteriorAlgebra.repr x S ≠ 0) :
    S ⊆ s22b_allL ∧ S.card = k := by
  obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW hx S hS
  refine ⟨?_, by omega⟩
  have : S ∩ s22b_allL = S :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h1, h2]; omega)
  rw [← this]
  exact Finset.inter_subset_right

theorem s22b_subset_allR_of_pq (hW : IsCompl P.W₁ P.W₂) {k : ℕ}
    {x : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hx : x ∈ pqPiece P.W₁ P.W₂ 0 k)
    (S : Finset (Fin (2 * n + 2 * n))) (hS : (P.s22b_bV hW).ExteriorAlgebra.repr x S ≠ 0) :
    S ⊆ s22b_allR ∧ S.card = k := by
  obtain ⟨h1, h2⟩ := s22b_support_pqPiece hW hx S hS
  refine ⟨fun m hm => ?_, by omega⟩
  rcases s22b_iLR_cases m with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    have : s22b_iL i ∈ S ∩ s22b_allL := Finset.mem_inter.mpr ⟨hm, s22b_iL_mem_allL i⟩
    rw [Finset.card_eq_zero.mp h1] at this
    simp at this
  · exact s22b_iR_mem_allR j

theorem s22b_eq_zero_of_repr (hW : IsCompl P.W₁ P.W₂) (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (h : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr z T = 0) : z = 0 := by
  apply (P.s22b_bV hW).ExteriorAlgebra.repr.injective
  refine Finsupp.ext fun T => ?_
  rw [map_zero, Finsupp.zero_apply, h T]

theorem s22b_mono_of_single (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n)) (hz : z ∈ N) (S : Finset (Fin (2 * n + 2 * n)))
    (hS : (P.s22b_bV hW).ExteriorAlgebra.repr z S ≠ 0)
    (hsingle : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0 → T = S) :
    (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
  have hzS := s22b_eq_smul_of_support hW z S hsingle
  have key : ∀ c : Kd d, c ≠ 0 → z = c • (P.s22b_bV hW).ExteriorAlgebra S →
      (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
    intro c hc h
    have : (P.s22b_bV hW).ExteriorAlgebra S = c⁻¹ • z := by
      rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact N.smul_mem _ hz
  exact key _ hS hzS

theorem s22b_card_supp_lt (hW : IsCompl P.W₁ P.W₂) (z w : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (S : Finset (Fin (2 * n + 2 * n))) (hS : (P.s22b_bV hW).ExteriorAlgebra.repr z S ≠ 0)
    (hwS : (P.s22b_bV hW).ExteriorAlgebra.repr w S = 0)
    (hwz : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr z T = 0 →
      (P.s22b_bV hW).ExteriorAlgebra.repr w T = 0) :
    (Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr w T ≠ 0).card <
      (Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun T hT => ?_) |>.mpr ⟨S, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact fun h => hT (hwz T h)
  · simp [hS]
  · simp [hwS]

/-- Minimal support (side `W₁`): a nonzero `Spin(V)_P`-stable `N ⊆ ⋀^k W₁` contains a
monomial. -/
theorem s22b_irr_mono₁ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) (k : ℕ)
    (hN : N ≤ pqPiece P.W₁ P.W₂ k 0) :
    ∀ m : ℕ, ∀ z ∈ N, z ≠ 0 →
      (Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0).card ≤ m →
      ∃ S, (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
  intro m
  induction m with
  | zero =>
    intro z _ hz0 hcard
    exfalso
    apply hz0
    refine s22b_eq_zero_of_repr hW z fun T => ?_
    by_contra hT
    have : T ∈ Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
    simp at this
  | succ m ih =>
    intro z hz hz0 hcard
    obtain ⟨S, hS⟩ : ∃ S, (P.s22b_bV hW).ExteriorAlgebra.repr z S ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (s22b_eq_zero_of_repr hW z h)
    by_cases hsingle : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0 → T = S
    · exact ⟨S, s22b_mono_of_single hW N z hz S hS hsingle⟩
    push Not at hsingle
    obtain ⟨S', hS', hSS'⟩ := hsingle
    obtain ⟨hSL, hSk⟩ := s22b_subset_allL_of_pq hW (hN hz) S hS
    obtain ⟨hS'L, hS'k⟩ := s22b_subset_allL_of_pq hW (hN hz) S' hS'
    have hnsub : ¬ S ⊆ S' := fun h => hSS'.symm (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨a, haS, haS'⟩ := Finset.not_subset.mp hnsub
    have hnsub' : ¬ S' ⊆ S := fun h => hSS' (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨b, hbS', hbS⟩ := Finset.not_subset.mp hnsub'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hSL haS)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hS'L hbS')
    have hij : i ≠ j := by rintro rfl; exact hbS haS
    have hHz := s22b_H_mem hd hW N z (fun g hg => N.sub_mem (hNinv g hg z hz) hz) i j hij
    obtain ⟨w, hwdef⟩ : ∃ w, w = s22b_Der (P.s22b_bV hW)
        (s22b_numOp (P.s22b_bV hW) (s22b_iL i) - s22b_numOp (P.s22b_bV hW) (s22b_iR i) -
          s22b_numOp (P.s22b_bV hW) (s22b_iL j) + s22b_numOp (P.s22b_bV hW) (s22b_iR j)) z - z :=
      ⟨_, rfl⟩
    have hw : w ∈ N := hwdef ▸ N.sub_mem hHz hz
    have hwT : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr w T =
        (((if s22b_iL i ∈ T then (1 : Kd d) else 0) - (if s22b_iR i ∈ T then 1 else 0) -
          (if s22b_iL j ∈ T then 1 else 0) + (if s22b_iR j ∈ T then 1 else 0)) - 1) *
          (P.s22b_bV hW).ExteriorAlgebra.repr z T := by
      intro T
      rw [hwdef, map_sub, Finsupp.sub_apply, s22b_repr_H]
      ring
    refine ih w hw ?_ ?_
    · intro h0
      have := hwT S'
      rw [h0, map_zero, Finsupp.zero_apply] at this
      have hiR : s22b_iR i ∉ S' := fun h => s22b_iR_notMem_allL i (hS'L h)
      have hjR : s22b_iR j ∉ S' := fun h => s22b_iR_notMem_allL j (hS'L h)
      simp only [haS', hiR, hbS', hjR, ↓reduceIte] at this
      apply hS'
      linear_combination (1 / 2 : Kd d) * this
    · have hlt := s22b_card_supp_lt hW z w S hS (by
        rw [hwT S]
        have hiR : s22b_iR i ∉ S := fun h => s22b_iR_notMem_allL i (hSL h)
        have hjR : s22b_iR j ∉ S := fun h => s22b_iR_notMem_allL j (hSL h)
        simp only [haS, hiR, hbS, hjR, ↓reduceIte]
        ring) (fun T hT => by rw [hwT T, hT, mul_zero])
      omega

/-- Minimal support (side `W₂`). -/
theorem s22b_irr_mono₂ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) (k : ℕ)
    (hN : N ≤ pqPiece P.W₁ P.W₂ 0 k) :
    ∀ m : ℕ, ∀ z ∈ N, z ≠ 0 →
      (Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0).card ≤ m →
      ∃ S, (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
  intro m
  induction m with
  | zero =>
    intro z _ hz0 hcard
    exfalso
    apply hz0
    refine s22b_eq_zero_of_repr hW z fun T => ?_
    by_contra hT
    have : T ∈ Finset.univ.filter fun T => (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
    simp at this
  | succ m ih =>
    intro z hz hz0 hcard
    obtain ⟨S, hS⟩ : ∃ S, (P.s22b_bV hW).ExteriorAlgebra.repr z S ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (s22b_eq_zero_of_repr hW z h)
    by_cases hsingle : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr z T ≠ 0 → T = S
    · exact ⟨S, s22b_mono_of_single hW N z hz S hS hsingle⟩
    push Not at hsingle
    obtain ⟨S', hS', hSS'⟩ := hsingle
    obtain ⟨hSR, hSk⟩ := s22b_subset_allR_of_pq hW (hN hz) S hS
    obtain ⟨hS'R, hS'k⟩ := s22b_subset_allR_of_pq hW (hN hz) S' hS'
    have hnsub : ¬ S ⊆ S' := fun h => hSS'.symm (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨a, haS, haS'⟩ := Finset.not_subset.mp hnsub
    have hnsub' : ¬ S' ⊆ S := fun h => hSS' (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨b, hbS', hbS⟩ := Finset.not_subset.mp hnsub'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hSR haS)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hS'R hbS')
    have hij : i ≠ j := by rintro rfl; exact hbS haS
    have hHz := s22b_H_mem hd hW N z (fun g hg => N.sub_mem (hNinv g hg z hz) hz) i j hij
    obtain ⟨w, hwdef⟩ : ∃ w, w = s22b_Der (P.s22b_bV hW)
        (s22b_numOp (P.s22b_bV hW) (s22b_iL i) - s22b_numOp (P.s22b_bV hW) (s22b_iR i) -
          s22b_numOp (P.s22b_bV hW) (s22b_iL j) + s22b_numOp (P.s22b_bV hW) (s22b_iR j)) z + z :=
      ⟨_, rfl⟩
    have hw : w ∈ N := hwdef ▸ N.add_mem hHz hz
    have hwT : ∀ T, (P.s22b_bV hW).ExteriorAlgebra.repr w T =
        (((if s22b_iL i ∈ T then (1 : Kd d) else 0) - (if s22b_iR i ∈ T then 1 else 0) -
          (if s22b_iL j ∈ T then 1 else 0) + (if s22b_iR j ∈ T then 1 else 0)) + 1) *
          (P.s22b_bV hW).ExteriorAlgebra.repr z T := by
      intro T
      rw [hwdef, map_add, Finsupp.add_apply, s22b_repr_H]
      ring
    refine ih w hw ?_ ?_
    · intro h0
      have := hwT S'
      rw [h0, map_zero, Finsupp.zero_apply] at this
      have hiL : s22b_iL i ∉ S' := fun h => s22b_iL_notMem_allR i (hS'R h)
      have hjL : s22b_iL j ∉ S' := fun h => s22b_iL_notMem_allR j (hS'R h)
      simp only [haS', hiL, hbS', hjL, ↓reduceIte] at this
      apply hS'
      linear_combination (-1 / 2 : Kd d) * this
    · have hlt := s22b_card_supp_lt hW z w S hS (by
        rw [hwT S]
        have hiL : s22b_iL i ∉ S := fun h => s22b_iL_notMem_allR i (hSR h)
        have hjL : s22b_iL j ∉ S := fun h => s22b_iL_notMem_allR j (hSR h)
        simp only [haS, hiL, hbS, hjL, ↓reduceIte]
        ring) (fun T hT => by rw [hwT T, hT, mul_zero])
      omega

theorem s22b_sdiff_swap {α : Type*} [DecidableEq α] (S S₀ : Finset α) (a b : α) (ha : a ∈ S₀) :
    insert a (S.erase b) \ S₀ = (S \ S₀).erase b := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨hx1 | ⟨hx1, hx2⟩, hx3⟩
    · exact absurd (hx1 ▸ ha) hx3
    · exact ⟨hx1, hx2, hx3⟩
  · rintro ⟨hx1, hx2, hx3⟩
    exact ⟨Or.inr ⟨hx1, hx2⟩, hx3⟩

/-- Connectivity (side `W₁`): the root operators move any monomial of `⋀^k W₁` to any other. -/
theorem s22b_irr_conn₁ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N)
    (S₀ : Finset (Fin (2 * n + 2 * n))) (hS₀ : (P.s22b_bV hW).ExteriorAlgebra S₀ ∈ N)
    (hS₀L : S₀ ⊆ s22b_allL) :
    ∀ m : ℕ, ∀ S, S ⊆ s22b_allL → S.card = S₀.card → (S \ S₀).card = m →
      (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
  intro m
  induction m with
  | zero =>
    intro S _ hSc hm
    have hsub : S ⊆ S₀ := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]
    exact hS₀
  | succ m ih =>
    intro S hSL hSc hm
    obtain ⟨b, hb⟩ : (S \ S₀).Nonempty := Finset.card_pos.mp (by omega)
    rw [Finset.mem_sdiff] at hb
    have hnsub : ¬ S₀ ⊆ S := fun h => hb.2 (by
      rw [Finset.eq_of_subset_of_card_le h (by omega)]; exact hb.1)
    obtain ⟨a, haS₀, haS⟩ := Finset.not_subset.mp hnsub
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hSL hb.1)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hS₀L haS₀)
    have hji : j ≠ i := by rintro rfl; exact hb.2 haS₀
    have hiS' : s22b_iL i ∉ S.erase (s22b_iL j) := fun h => haS (Finset.mem_of_mem_erase h)
    have hS''L : insert (s22b_iL i) (S.erase (s22b_iL j)) ⊆ s22b_allL :=
      Finset.insert_subset (hS₀L haS₀) ((Finset.erase_subset _ _).trans hSL)
    have hS''c : (insert (s22b_iL i) (S.erase (s22b_iL j))).card = S₀.card := by
      rw [Finset.card_insert_of_notMem hiS', Finset.card_erase_of_mem hb.1]
      have : 0 < S.card := Finset.card_pos.mpr ⟨_, hb.1⟩
      omega
    have hS''m : (insert (s22b_iL i) (S.erase (s22b_iL j)) \ S₀).card = m := by
      rw [s22b_sdiff_swap S S₀ _ _ haS₀,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hb)]
      omega
    have he := ih _ hS''L hS''c hS''m
    have hr := s22b_root_mem hd hW N _ (fun g hg => N.sub_mem (hNinv g hg _ he) he) j i hji
    rw [s22b_Der_sub, LinearMap.sub_apply,
      (s22b_Der_rOp _ (s22b_iR i) (s22b_iR j) (by simpa using hji.symm) _).1
        (Or.inl fun h => s22b_iR_notMem_allL j (hS''L h)), sub_zero] at hr
    obtain ⟨ε, hε, heq⟩ := (s22b_Der_rOp (P.s22b_bV hW) (s22b_iL j) (s22b_iL i)
      (by simpa using hji) (insert (s22b_iL i) (S.erase (s22b_iL j)))).2
      (Finset.mem_insert_self _ _) (by
        rw [Finset.mem_insert, not_or]
        exact ⟨by simpa using hji, Finset.notMem_erase _ _⟩)
    rw [heq, Finset.erase_insert hiS', Finset.insert_erase hb.1] at hr
    have : (P.s22b_bV hW).ExteriorAlgebra S = ε • (ε • (P.s22b_bV hW).ExteriorAlgebra S) := by
      rcases hε with rfl | rfl <;> simp
    rw [this]
    exact N.smul_mem _ hr

/-- Connectivity (side `W₂`). -/
theorem s22b_irr_conn₂ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hNinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N)
    (S₀ : Finset (Fin (2 * n + 2 * n))) (hS₀ : (P.s22b_bV hW).ExteriorAlgebra S₀ ∈ N)
    (hS₀R : S₀ ⊆ s22b_allR) :
    ∀ m : ℕ, ∀ S, S ⊆ s22b_allR → S.card = S₀.card → (S \ S₀).card = m →
      (P.s22b_bV hW).ExteriorAlgebra S ∈ N := by
  intro m
  induction m with
  | zero =>
    intro S _ hSc hm
    have hsub : S ⊆ S₀ := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]
    exact hS₀
  | succ m ih =>
    intro S hSR hSc hm
    obtain ⟨b, hb⟩ : (S \ S₀).Nonempty := Finset.card_pos.mp (by omega)
    rw [Finset.mem_sdiff] at hb
    have hnsub : ¬ S₀ ⊆ S := fun h => hb.2 (by
      rw [Finset.eq_of_subset_of_card_le h (by omega)]; exact hb.1)
    obtain ⟨a, haS₀, haS⟩ := Finset.not_subset.mp hnsub
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hSR hb.1)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hS₀R haS₀)
    have hji : j ≠ i := by rintro rfl; exact hb.2 haS₀
    have hiS' : s22b_iR i ∉ S.erase (s22b_iR j) := fun h => haS (Finset.mem_of_mem_erase h)
    have hS''R : insert (s22b_iR i) (S.erase (s22b_iR j)) ⊆ s22b_allR :=
      Finset.insert_subset (hS₀R haS₀) ((Finset.erase_subset _ _).trans hSR)
    have hS''c : (insert (s22b_iR i) (S.erase (s22b_iR j))).card = S₀.card := by
      rw [Finset.card_insert_of_notMem hiS', Finset.card_erase_of_mem hb.1]
      have : 0 < S.card := Finset.card_pos.mpr ⟨_, hb.1⟩
      omega
    have hS''m : (insert (s22b_iR i) (S.erase (s22b_iR j)) \ S₀).card = m := by
      rw [s22b_sdiff_swap S S₀ _ _ haS₀,
        Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hb)]
      omega
    have he := ih _ hS''R hS''c hS''m
    have hr := s22b_root_mem hd hW N _ (fun g hg => N.sub_mem (hNinv g hg _ he) he) i j hji.symm
    rw [s22b_Der_sub, LinearMap.sub_apply,
      (s22b_Der_rOp _ (s22b_iL i) (s22b_iL j) (by simpa using hji.symm) _).1
        (Or.inl fun h => s22b_iL_notMem_allR j (hS''R h)), zero_sub] at hr
    obtain ⟨ε, hε, heq⟩ := (s22b_Der_rOp (P.s22b_bV hW) (s22b_iR j) (s22b_iR i)
      (by simpa using hji) (insert (s22b_iR i) (S.erase (s22b_iR j)))).2
      (Finset.mem_insert_self _ _) (by
        rw [Finset.mem_insert, not_or]
        exact ⟨by simpa using hji, Finset.notMem_erase _ _⟩)
    rw [heq, Finset.erase_insert hiS', Finset.insert_erase hb.1] at hr
    have : (P.s22b_bV hW).ExteriorAlgebra S = -ε • -(ε • (P.s22b_bV hW).ExteriorAlgebra S) := by
      rcases hε with rfl | rfl <;> simp
    rw [this]
    exact N.smul_mem _ hr

/-- **`⋀^k W₁` is an irreducible `Spin(V)_P`-module** (the gap filled by the `sl(W₁)` argument). -/
theorem s22b_irreducible₁ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (k : ℕ)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hN : N ≤ pqPiece P.W₁ P.W₂ k 0)
    (hinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) :
    N = ⊥ ∨ N = pqPiece P.W₁ P.W₂ k 0 := by
  rcases eq_or_ne N ⊥ with h | hbot
  · exact Or.inl h
  right
  apply le_antisymm hN
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨S₀, hS₀⟩ := s22b_irr_mono₁ hd hW N hinv k hN _ z hz hz0 le_rfl
  obtain ⟨hS₀L, hS₀k⟩ := s22b_subset_allL_of_pq hW (hN hS₀) S₀ (by
    rw [s22b_repr_basis]; simp)
  intro x hx
  rw [← (P.s22b_bV hW).ExteriorAlgebra.sum_repr x]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases h : (P.s22b_bV hW).ExteriorAlgebra.repr x S = 0
  · rw [h, zero_smul]; exact N.zero_mem
  · obtain ⟨hSL, hSk⟩ := s22b_subset_allL_of_pq hW hx S h
    exact N.smul_mem _ (s22b_irr_conn₁ hd hW N hinv S₀ hS₀ hS₀L _ S hSL (by omega) rfl)

/-- **`⋀^k W₂` is an irreducible `Spin(V)_P`-module**. -/
theorem s22b_irreducible₂ (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (k : ℕ)
    (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hN : N ≤ pqPiece P.W₁ P.W₂ 0 k)
    (hinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) :
    N = ⊥ ∨ N = pqPiece P.W₁ P.W₂ 0 k := by
  rcases eq_or_ne N ⊥ with h | hbot
  · exact Or.inl h
  right
  apply le_antisymm hN
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨S₀, hS₀⟩ := s22b_irr_mono₂ hd hW N hinv k hN _ z hz hz0 le_rfl
  obtain ⟨hS₀R, hS₀k⟩ := s22b_subset_allR_of_pq hW (hN hS₀) S₀ (by
    rw [s22b_repr_basis]; simp)
  intro x hx
  rw [← (P.s22b_bV hW).ExteriorAlgebra.sum_repr x]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases h : (P.s22b_bV hW).ExteriorAlgebra.repr x S = 0
  · rw [h, zero_smul]; exact N.zero_mem
  · obtain ⟨hSR, hSk⟩ := s22b_subset_allR_of_pq hW hx S h
    exact N.smul_mem _ (s22b_irr_conn₂ hd hW N hinv S₀ hS₀ hS₀R _ S hSR (by omega) rfl)

end S22bInvariants

section S22bHodgeB

theorem s22b_rhoExt_bcExt_omega (hW : IsCompl P.W₁ P.W₂) (g : Spin ℂ n)
    (hfix : ∀ x ∈ P.PK, m ℂ n (g : C ℂ n) (bcS (Kd d) ℂ n x) = bcS (Kd d) ℂ n x) :
    rhoExt ℂ n g (bcExt (Kd d) ℂ n (s22b_omega hW)) = bcExt (Kd d) ℂ n (s22b_omega hW) := by
  have hn := P.s22b_n_pos
  set a : Fin (2 * n) → V ℂ n := fun i => bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iL i)) with ha_def
  set b : Fin (2 * n) → V ℂ n := fun i => bcV (Kd d) ℂ n (P.s22b_bV hW (s22b_iR i)) with hb_def
  have hdual : ∀ i j, pairing ℂ n (a i) (b j) = if i = j then 1 else 0 := by
    intro i j
    simp only [a, b]
    rw [s22b_pairing_bcV, P.s22b_pairing_bV_LR hW]
    split_ifs <;> simp
  have hA : P.W₁ℂ = Submodule.span ℂ (Set.range a) := by
    rw [W₁ℂ, ← P.s22b_span_uL hW, s22b_span_bcV_range]; rfl
  have hB : P.W₂ℂ = Submodule.span ℂ (Set.range b) := by
    rw [W₂ℂ, ← P.s22b_span_uR hW, s22b_span_bcV_range]; rfl
  have hfix₁ := hfix _ P.s22b_u₁_mem_PK
  have hfix₂ := hfix _ P.s22b_u₂_mem_PK
  have hW₁ := P.s22b_W₁ℂ_eq hn
  have hW₂ := P.s22b_W₂ℂ_eq hn
  have key := s22b_omega_inv_general P.W₁ℂ P.W₂ℂ a b
    (fun i => hA ▸ Submodule.subset_span ⟨i, rfl⟩) (fun i => hB ▸ Submodule.subset_span ⟨i, rfl⟩)
    (fun x hx => s22b_expand_of_span a b hdual (hA ▸ hx))
    (fun y hy => s22b_expand_of_span' a b hdual (hB ▸ hy))
    (rho ℂ n g : V ℂ n →ₗ[ℂ] V ℂ n) (rho ℂ n g⁻¹ : V ℂ n →ₗ[ℂ] V ℂ n)
    (fun x => s22b_rho_inv_rho g x)
    (fun y hy => by rw [hW₂] at hy ⊢; exact s22b_rho_mem_ann_of_fix g hfix₂ hy)
    (fun x hx => by rw [hW₁] at hx ⊢; exact s22b_rho_mem_ann_of_fix g⁻¹ (s22b_fix_inv g hfix₁) hx)
    (fun x y => KSecant.s22b_rho_pairing g x y)
  rw [s22b_omega, map_sum]
  simp only [map_mul, s22b_bcExt_ι, rhoExt, map_sum, ExteriorAlgebra.map_apply_ι]
  exact key

/-- `⋀^{2n} W₁` (base-changed) is fixed by the torus element (`det = 1`, Chevalley). -/
theorem s22b_rhoExt_bcExt_eL (hW : IsCompl P.W₁ P.W₂) (g : Spin ℂ n)
    (hfix : ∀ x ∈ P.PK, m ℂ n (g : C ℂ n) (bcS (Kd d) ℂ n x) = bcS (Kd d) ℂ n x) :
    rhoExt ℂ n g (bcExt (Kd d) ℂ n ((P.s22b_bV hW).ExteriorAlgebra s22b_allL)) =
      bcExt (Kd d) ℂ n ((P.s22b_bV hW).ExteriorAlgebra s22b_allL) := by
  have hn := P.s22b_n_pos
  have hfix₁ := hfix _ P.s22b_u₁_mem_PK
  have hpure := s22b_isEvenPureSpinor_bcS (F' := ℂ) hn P.isPure
  have hmem := s22b_bcExt_mem_pqPiece (F' := ℂ) P.W₁ P.W₂ (P.s22b_eL_mem hW)
  rw [show Submodule.span ℂ (bcV (Kd d) ℂ n '' (P.W₁ : Set (V (Kd d) n))) = P.W₁ℂ from rfl,
    show Submodule.span ℂ (bcV (Kd d) ℂ n '' (P.W₂ : Set (V (Kd d) n))) = P.W₂ℂ from rfl,
    P.s22b_W₁ℂ_eq hn] at hmem
  show ExteriorAlgebra.map _ _ = _
  rw [s22b_map_top_sub _ _ hpure.2.2 _ (fun _ hv => s22b_rho_mem_ann_of_fix g hfix₁ hv) hmem,
    s22b_det_one hn g hpure hfix₁, one_smul]

theorem s22b_rhoExt_bcExt_eR (hW : IsCompl P.W₁ P.W₂) (g : Spin ℂ n)
    (hfix : ∀ x ∈ P.PK, m ℂ n (g : C ℂ n) (bcS (Kd d) ℂ n x) = bcS (Kd d) ℂ n x) :
    rhoExt ℂ n g (bcExt (Kd d) ℂ n ((P.s22b_bV hW).ExteriorAlgebra s22b_allR)) =
      bcExt (Kd d) ℂ n ((P.s22b_bV hW).ExteriorAlgebra s22b_allR) := by
  have hn := P.s22b_n_pos
  have hfix₂ := hfix _ P.s22b_u₂_mem_PK
  have hpure := s22b_isEvenPureSpinor_bcS (F' := ℂ) hn P.isPure₂
  have hmem := s22b_bcExt_mem_pqPiece (F' := ℂ) P.W₁ P.W₂ (P.s22b_eR_mem hW)
  rw [show Submodule.span ℂ (bcV (Kd d) ℂ n '' (P.W₁ : Set (V (Kd d) n))) = P.W₁ℂ from rfl,
    show Submodule.span ℂ (bcV (Kd d) ℂ n '' (P.W₂ : Set (V (Kd d) n))) = P.W₂ℂ from rfl,
    P.s22b_W₂ℂ_eq hn] at hmem
  show ExteriorAlgebra.map _ _ = _
  rw [s22b_map_top_sub' _ _ hpure.2.2 _ (fun _ hv => s22b_rho_mem_ann_of_fix g hfix₂ hv) hmem,
    s22b_det_one hn g hpure hfix₂, one_smul]

/-- Every `Spin(V)_P`-invariant of `⋀• V_K`, base-changed to `ℂ`, is fixed by the torus element. -/
theorem s22b_rhoExt_bcExt_inv (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (g : Spin ℂ n)
    (hfix : ∀ x ∈ P.PK, m ℂ n (g : C ℂ n) (bcS (Kd d) ℂ n x) = bcS (Kd d) ℂ n x)
    (z : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hz : ∀ g' ∈ P.spinPZ, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g') z = z) :
    rhoExt ℂ n g (bcExt (Kd d) ℂ n z) = bcExt (Kd d) ℂ n z := by
  have hsmul : ∀ (c : Kd d) (y : ExteriorAlgebra ℂ (V ℂ n)),
      rhoExt ℂ n g (c • y) = c • rhoExt ℂ n g y := fun c y => by
    rw [← algebraMap_smul ℂ c y, map_smul, algebraMap_smul]
  obtain ⟨cL, cR, c, rfl⟩ := s22b_inv_decomp hd hW z hz
  rw [s22b_combo]
  simp only [map_add, map_sum, map_smul, hsmul, map_pow, P.s22b_rhoExt_bcExt_eL hW g hfix,
    P.s22b_rhoExt_bcExt_eR hW g hfix, P.s22b_rhoExt_bcExt_omega hW g hfix]

end S22bHodgeB

/-! ## Lemma 2.2.7 -/

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), first sentence: the
`Spin(V)_P`-invariant subspace `(⋀^{2j} V_ℚ)^{Spin(V)_P}` is a subspace of `⋀^{j,j} V_ℂ`, i.e. it
consists of Hodge classes for the complex structure of `X × X̂`. Reading: as in Lemma 2.2.6 (whose
conclusion the proof uses), `P` is contained in the Hodge ring of `X` for the complex structure `J`
of `X`; without this the statement is false. Group: the integral `Spin(V)_P` (see the module
docstring).

Proof: the paper says the invariant lines are `U(1)`-invariant and defined over `ℚ`, hence trivial
`U(1)`-characters. Here the `K`-invariants are spanned by `ω^j`, and also by `⋀^{2n} W₁` and
`⋀^{2n} W₂` when `j = n`. All of them are fixed by the element `g` of the complexified circle used
in Lemma 2.2.6 (`KSecant.s22b_torus_P`). For `ω`, this holds because `ρ(g)` is an isometry
preserving `W₁` and `W₂`. For `⋀^{2n} W_i`, it holds because `det(ρ(g)|_{W_i}) = 1`, the step of
Lemma 2.2.6 that gives `dim W_i^{1,0} = dim W_i^{0,1}`. Fixed vectors of `g` in degree `2j` have
type `(j, j)`. -/
theorem _root_.WeilClasses.lemma2_2_7_hodge (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J)
    (j : ℕ) :
    P.invQ (2 * j) ≤ hodgeClassesV n (productStructure n J) j := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  obtain ⟨g, hfix, h10, h01⟩ := P.s22b_torus_P J hJ hPJ
  intro α hα
  rw [mem_hodgeClassesV_iff]
  have hα' := (KSecant.s22b_mem_invQ_iff (2 * j) α).mp hα
  rw [KSecant.s22b_mem_invK_iff] at hα'
  refine ⟨(Submodule.mem_inf.mp hα).1, ?_⟩
  rw [← s22b_bcExt_trans]
  exact s22b_mem_pq_of_fixed (s22b_isCompl_V10 J hJ) (rho ℂ n g : V ℂ n →ₗ[ℂ] V ℂ n) h10 h01 j
    (s22b_bcExt_mem_exteriorPower' hα'.1) (P.s22b_rhoExt_bcExt_inv hd hW g hfix _ hα'.2)

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), dimensions, `k` odd:
`dim (⋀^k V_ℚ)^{Spin(V)_P} = 0`. -/
theorem _root_.WeilClasses.lemma2_2_7_odd (hd : 0 < d) (hP : ¬ P.IsIsotropic) (k : ℕ)
    (hk : Odd k) :
    Module.finrank ℚ (P.invQ k) = 0 := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  rw [KSecant.s22b_finrank_invQ hd, KSecant.s22b_invK_odd hd hW k hk, finrank_bot]

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), dimensions, `k` even:
`dim (⋀^k V_ℚ)^{Spin(V)_P} = 1` if `0 ≤ k ≤ 4n`, `k` even, `k ≠ 2n`. -/
theorem _root_.WeilClasses.lemma2_2_7_even (hd : 0 < d) (hP : ¬ P.IsIsotropic) (k : ℕ)
    (hk : Even k) (hk4 : k ≤ 4 * n) (hk2 : k ≠ 2 * n) :
    Module.finrank ℚ (P.invQ k) = 1 := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  obtain ⟨a, rfl⟩ := hk
  rw [KSecant.s22b_finrank_invQ hd, show a + a = 2 * a by ring,
    KSecant.s22b_invK_eq_span hd hW a (by omega) (by omega),
    finrank_span_singleton (KSecant.s22b_omega_pow_ne_zero hW a (by omega))]

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), dimensions, middle degree:
`dim (⋀^{2n} V_ℚ)^{Spin(V)_P} = 3`. -/
theorem _root_.WeilClasses.lemma2_2_7_middle (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    Module.finrank ℚ (P.invQ (2 * n)) = 3 := by
  rw [KSecant.s22b_finrank_invQ hd,
    KSecant.s22b_finrank_invK_middle hd (P.isCompl_of_not_isIsotropic hd hP)]

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence, the sum:
`(⋀^{2n} V_K)^{Spin(V)_P} = ⋀^{2n} W₁ ⊕ ⋀^{2n} W₂ ⊕ L`, where the trivial line is
`L = (⋀^n W₁ ⊗ ⋀^n W₂)^{Spin(V)_P}` (proof of Lemma 2.2.7). -/
theorem _root_.WeilClasses.lemma2_2_7_K_eq (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    P.invK (2 * n) =
      pqPiece P.W₁ P.W₂ (2 * n) 0 ⊔ pqPiece P.W₁ P.W₂ 0 (2 * n) ⊔
        (P.invK (2 * n) ⊓ pqPiece P.W₁ P.W₂ n n) := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  rw [KSecant.s22b_invK_inf_pq hd hW, KSecant.s22b_pq_top₁_eq hW, KSecant.s22b_pq_top₂_eq hW]
  exact KSecant.s22b_invK_middle hd hW

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence: the sum
`⋀^{2n} W₁ + ⋀^{2n} W₂ + L` is direct. -/
theorem _root_.WeilClasses.lemma2_2_7_K_indep (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    iSupIndep ![pqPiece P.W₁ P.W₂ (2 * n) 0, pqPiece P.W₁ P.W₂ 0 (2 * n),
      P.invK (2 * n) ⊓ pqPiece P.W₁ P.W₂ n n] := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have hn := P.s22b_n_pos
  have h := (P.wedge_decomp hd hW (2 * n)).1
  let f : Fin 3 → Fin (2 * n + 1) := ![⟨2 * n, by omega⟩, ⟨0, by omega⟩, ⟨n, by omega⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Fin.ext_iff] at hij ⊢ <;> omega
  refine (h.comp hinj).mono fun i => ?_
  fin_cases i
  · simp [f]
  · simp [f]
  · simp only [f, Function.comp_apply]
    simp [show 2 * n - n = n by omega]

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence: the three
summands `⋀^{2n} W₁`, `⋀^{2n} W₂` and `L = (⋀^n W₁ ⊗ ⋀^n W₂)^{Spin(V)_P}` are lines. -/
theorem _root_.WeilClasses.lemma2_2_7_K_finrank (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    Module.finrank (Kd d) (pqPiece P.W₁ P.W₂ (2 * n) 0) = 1 ∧
      Module.finrank (Kd d) (pqPiece P.W₁ P.W₂ 0 (2 * n)) = 1 ∧
      Module.finrank (Kd d) (P.invK (2 * n) ⊓ pqPiece P.W₁ P.W₂ n n :
        Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n))) = 1 := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  refine ⟨?_, ?_, ?_⟩
  · rw [KSecant.s22b_pq_top₁_eq hW]
    exact finrank_span_singleton ((P.s22b_bV hW).ExteriorAlgebra.ne_zero _)
  · rw [KSecant.s22b_pq_top₂_eq hW]
    exact finrank_span_singleton ((P.s22b_bV hW).ExteriorAlgebra.ne_zero _)
  · rw [KSecant.s22b_invK_inf_pq hd hW]
    exact finrank_span_singleton (KSecant.s22b_omega_pow_ne_zero hW n (by omega))

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence: `⋀^{2n} W₁` is
the character `det₁` of `Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem _root_.WeilClasses.lemma2_2_7_K_det₁ (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (g : P.spinL₁L₂) (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hx : x ∈ pqPiece P.W₁ P.W₂ (2 * n) 0) :
    rhoExt (Kd d) n g x = P.det₁ g • x := by
  have _ := hd
  have _ := hP
  exact KSecant.s22b_rhoExt_top₁ g x hx

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence: `⋀^{2n} W₂` is
the character `det₂` of `Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem _root_.WeilClasses.lemma2_2_7_K_det₂ (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (g : P.spinL₁L₂) (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hx : x ∈ pqPiece P.W₁ P.W₂ 0 (2 * n)) :
    rhoExt (Kd d) n g x = P.det₂ g • x := by
  exact KSecant.s22b_rhoExt_top₂ (P.isCompl_of_not_isIsotropic hd hP) g x hx

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), third sentence: the third
summand `L = (⋀^n W₁ ⊗ ⋀^n W₂)^{Spin(V)_P}` is the trivial character of `Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem _root_.WeilClasses.lemma2_2_7_K_trivial (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (g : P.spinL₁L₂) (x : ExteriorAlgebra (Kd d) (V (Kd d) n))
    (hx : x ∈ P.invK (2 * n) ⊓ pqPiece P.W₁ P.W₂ n n) :
    rhoExt (Kd d) n g x = x := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  rw [KSecant.s22b_invK_inf_pq hd hW] at hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, map_pow, KSecant.s22b_rhoExt_omega hW g]

/-- **Lemma 2.2.7** (`lemma-Spin-V-P-invariant-classes-are-Hodge`), last sentence: for `j ≠ n`,
`0 ≤ j ≤ 2n`, the space `(⋀^{2j} V_ℚ)^{Spin(V)_P}` is a trivial character of
`Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem _root_.WeilClasses.lemma2_2_7_trivial (hd : 0 < d) (hP : ¬ P.IsIsotropic) (j : ℕ)
    (hj : j ≠ n) (hj2 : j ≤ 2 * n) (α : ExteriorAlgebra ℚ (V ℚ n)) (hα : α ∈ P.invQ (2 * j))
    (g : P.spinL₁L₂) :
    rhoExt (Kd d) n g (bcExt ℚ (Kd d) n α) = bcExt ℚ (Kd d) n α := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have h := (KSecant.s22b_mem_invQ_iff (2 * j) α).mp hα
  rw [KSecant.s22b_invK_eq_span hd hW j hj2 hj] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  rw [← hc, map_smul, map_pow, KSecant.s22b_rhoExt_omega hW g]

/-- Claim in the proof of Lemma 2.2.7 (`lemma-Spin-V-P-invariant-classes-are-Hodge`), stated there
without proof: for `0 ≤ k ≤ 2n`, `⋀^k W₁` is an irreducible representation of the integral group
`Spin(V)_P`. True for the algebraic group `Spin(V_K)_P ≅ SL(W₁)`; for `Spin(V)_P` it needs a density
argument (see the module docstring). -/
theorem _root_.WeilClasses.lemma2_2_7_irreducible₁ (hd : 0 < d) (hP : ¬ P.IsIsotropic) (k : ℕ)
    (hk : k ≤ 2 * n) (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hN : N ≤ pqPiece P.W₁ P.W₂ k 0)
    (hinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) :
    N = ⊥ ∨ N = pqPiece P.W₁ P.W₂ k 0 := by
  have _ := hk
  exact KSecant.s22b_irreducible₁ hd (P.isCompl_of_not_isIsotropic hd hP) k N hN hinv

/-- Claim in the proof of Lemma 2.2.7: for `0 ≤ k ≤ 2n`, `⋀^k W₂` is an irreducible representation
of the integral group `Spin(V)_P` (see `lemma2_2_7_irreducible₁`). -/
theorem _root_.WeilClasses.lemma2_2_7_irreducible₂ (hd : 0 < d) (hP : ¬ P.IsIsotropic) (k : ℕ)
    (hk : k ≤ 2 * n) (N : Submodule (Kd d) (ExteriorAlgebra (Kd d) (V (Kd d) n)))
    (hN : N ≤ pqPiece P.W₁ P.W₂ 0 k)
    (hinv : ∀ g ∈ P.spinPZ, ∀ x ∈ N, rhoExt (Kd d) n (bcSpin ℚ (Kd d) n g) x ∈ N) :
    N = ⊥ ∨ N = pqPiece P.W₁ P.W₂ 0 k := by
  have _ := hk
  exact KSecant.s22b_irreducible₂ hd (P.isCompl_of_not_isIsotropic hd hP) k N hN hinv

/-- The note after Lemma 2.2.7 (`lemma-Spin-V-P-invariant-classes-are-Hodge`): "the space
`(⋀² V_ℚ)^{Spin(V)_P}` is spanned by a non-degenerate `2`-form on `V_K^*`, and so the subspace
`(⋀• V_K)^{Spin(V_K)_{ℓ₁,ℓ₂}}` consists of powers of this `2`-form". For a nonzero invariant
`ω ∈ ⋀² V_ℚ`: `ω^{2n} ≠ 0` (non-degenerate), and the `Spin(V_K)_{ℓ₁,ℓ₂}`-invariants of `⋀• V_K` are
spanned by the powers of `ω`. Needs `n ≥ 2` (for `n = 1`, `(⋀² V_ℚ)^{Spin(V)_P}` is the
three-dimensional middle degree); this is the paper's standing hypothesis. -/
theorem _root_.WeilClasses.lemma2_2_7_note (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (ω : ExteriorAlgebra ℚ (V ℚ n)) (hω : ω ∈ P.invQ 2) (hω0 : ω ≠ 0) :
    ω ^ (2 * n) ≠ 0 ∧
      invariantsExt (Kd d) n P.spinL₁L₂ =
        Submodule.span (Kd d) (Set.range fun j : ℕ => bcExt ℚ (Kd d) n ω ^ j) := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  obtain ⟨c, hc0, hc⟩ := KSecant.s22b_bcExt_omega_eq hd hn hW ω hω hω0
  refine ⟨fun h => ?_, le_antisymm ?_ ?_⟩
  · have := congrArg (bcExt ℚ (Kd d) n) h
    rw [map_pow, hc, smul_pow, map_zero] at this
    exact KSecant.s22b_omega_pow_ne_zero hW (2 * n) le_rfl
      ((smul_eq_zero.mp this).resolve_left (pow_ne_zero _ hc0))
  · intro x hx
    obtain ⟨cc, hcc⟩ := KSecant.s22b_inv_spinL₁L₂ hd hW x (fun g => hx g g.2)
    rw [hcc]
    refine Submodule.sum_mem _ fun a _ => ?_
    have : cc a • KSecant.s22b_omega hW ^ a = (cc a * (c ^ a)⁻¹) • bcExt ℚ (Kd d) n ω ^ a := by
      rw [hc, smul_pow, smul_smul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc0), mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ∀ g ∈ P.spinL₁L₂, rhoExt (Kd d) n g (bcExt ℚ (Kd d) n ω ^ j) = bcExt ℚ (Kd d) n ω ^ j
    intro g hg
    rw [hc, smul_pow, map_smul, map_pow, KSecant.s22b_rhoExt_omega hW ⟨g, hg⟩]

/-- Consequence of Lemma 2.2.7 and the note after it, used in the proof of Corollary 4.0.4 ("the
space of powers of classes in the one-dimensional `⋀²(V_ℚ)^{Spin(V)_P}`"): for `n ≥ 2`, a nonzero
invariant `ω ∈ ⋀² V_ℚ`, and `j ≠ n`, `0 ≤ j ≤ 2n`, the invariants `(⋀^{2j} V_ℚ)^{Spin(V)_P}` are
spanned by `ω^j`. -/
theorem _root_.WeilClasses.lemma2_2_7_note_pow (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (ω : ExteriorAlgebra ℚ (V ℚ n)) (hω : ω ∈ P.invQ 2) (hω0 : ω ≠ 0) (j : ℕ) (hj : j ≠ n)
    (hj2 : j ≤ 2 * n) :
    P.invQ (2 * j) = Submodule.span ℚ {ω ^ j} := by
  have hW := P.isCompl_of_not_isIsotropic hd hP
  have : Module.Finite ℚ (ExteriorAlgebra ℚ (V ℚ n)) := Module.Finite.of_basis (basisExt ℚ n)
  obtain ⟨c, hc0, hc⟩ := KSecant.s22b_bcExt_omega_eq hd hn hW ω hω hω0
  have hmem : ω ^ j ∈ P.invQ (2 * j) := by
    rw [KSecant.s22b_mem_invQ_iff, KSecant.s22b_invK_eq_span hd hW j hj2 hj, map_pow, hc,
      smul_pow]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hne : ω ^ j ≠ 0 := by
    intro h
    have := congrArg (bcExt ℚ (Kd d) n) h
    rw [map_pow, hc, smul_pow, map_zero] at this
    exact KSecant.s22b_omega_pow_ne_zero hW j hj2
      ((smul_eq_zero.mp this).resolve_left (pow_ne_zero _ hc0))
  have hfin : Module.finrank ℚ (P.invQ (2 * j)) = 1 :=
    WeilClasses.lemma2_2_7_even P hd hP (2 * j) (even_two_mul j) (by omega) (by omega)
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hmem
  · rw [finrank_span_singleton hne, hfin]

end KSecant

end WeilClasses
