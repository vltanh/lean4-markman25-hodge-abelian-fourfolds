module

public import WeilClasses.Chevalley.Defs
public import WeilClasses.External.Chevalley.Sec2_2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Chevalley, *The algebraic theory of spinors*, results used in §2.3 (and §6.1–6.3) of the paper

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954.
The quadratic space is `V_F = H¹(X̂, F) ⊕ H¹(X, F)` with `Q(θ, w) = θ(w)`, over a field `F` of
characteristic zero (the paper uses these results over `ℚ`, deducing the integral statements).

* [II.1.6] For a bilinear form `B` on `V` with `B(u, u) = Q(u)`, the map
  `ψ_B = changeForm(-B) : C(V) → ⋀•V` (`ψ_B(v x) = v ∧ ψ_B(x) + B(v, ·) ⌋ ψ_B(x)`, `ψ_B(1) = 1`;
  Chevalley's `λ`, [Bourbaki, §9]) maps `C(V)_k` into `F^k(⋀•V)` and induces isomorphisms
  `C(V)_k / C(V)_{k-1} ≅ ⋀^k V` (`chevalley_II_1_6_*`). Used in §2.3 for `B = B₀`.
* [Sec. 3.3] These graded isomorphisms are `Spin(V)`-equivariant, for the conjugation action on
  `C(V)` and `⋀^k ρ` on `⋀^k V` (`chevalley_sec3_3_*`). Used in §2.3.
* [p. 85, discussion after III.3.1] The `Spin(V)`-action on `⋀•V` transported by
  `ψ_B ∘ φ : S ⊗ S → ⋀•V` preserves `F^k(⋀•V)`, with associated graded action `⋀ρ`, independent of
  `B` (`chevalley_p85_transport_graded`). Used in §2.3 (and, through Lemma 6.1.1, in §6.1).
* [III.3.1] `φ : S ⊗ S → C(V)` (2.2.5) is an isomorphism of `Spin(V)`-representations: stated in
  `WeilClasses.External.Chevalley.Sec2_2` (`chevalley_III_3_1_bijective`,
  `chevalley_III_3_1_equivariant`), where §2.2 first uses it; §2.3 uses it as well.

## Proofs

`C(V)_k` is Tau Ceti's degree filtration `CliffordAlgebra.filtration (Q F n) k` and `F^k(⋀•V)` is
the degree filtration of `CliffordAlgebra 0 = ⋀•V`. Both are spanned by products of at most `k`
vectors, and `ψ_B(v₁ ⋯ v_j) = v₁ ∧ ⋯ ∧ v_j + (terms of degree < j)` (Tau Ceti's
`changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration`), so:

* [II.1.6]: `ψ_B` is filtered (Tau Ceti's `changeForm_mem_filtration`); the graded map is onto,
  since `⋀^k V` is spanned by the `v₁ ∧ ⋯ ∧ v_k`, which are the leading terms of the `v₁ ⋯ v_k`; it
  is injective because `ψ_B` is an isomorphism (`changeFormEquiv`) and reflects the filtration
  (`changeForm_mem_filtration_iff`).
* [Sec. 3.3]: on `C(V)`, conjugation by `g ∈ Spin(V)` is `CliffordAlgebra.map` of the isometry
  `ρ_g` (`sb_conjSpin_eq_map`; `g⁻¹ = g*`), which maps products of `j` vectors to products of `j`
  vectors; so it preserves `C(V)_k`, and the leading terms satisfy
  `ψ̄_B(g v₁ ⋯ v_k g⁻¹) = ρ_g v₁ ∧ ⋯ ∧ ρ_g v_k = ⋀ρ_g(ψ̄_B(v₁ ⋯ v_k))`.
* [p. 85]: by [III.3.1] (`chevalley_III_3_1_equivariant`, extended to all of `S ⊗ S` in
  `sb_varphi_map`), `φ ∘ (m_g ⊗ m_g)` is conjugation by `g` after `φ`; apply [Sec. 3.3] to `φ(y)`,
  which lies in `C(V)_k` when `ψ_B(φ(y)) ∈ F^k(⋀•V)` (`ψ_B` reflects the filtration).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-! ## Helpers -/

/-! ### The conjugation action of `Spin(V)` on `C(V)` -/

/-- `ρ_g : V → V` for `g ∈ Spin(V)`, as an isometry of `Q` (Tau Ceti's
`spinVectorAction_map_app`). -/
noncomputable def sb_rhoIsometry (g : Spin F n) : Q F n →qᵢ Q F n where
  toLinearMap := (rho F n g).toLinearMap
  map_app' v := spinVectorAction_map_app (Q F n) g v

omit [CharZero F] in
/-- On `Spin(V)`, the inverse is the Clifford conjugate: `g⁻¹ = g*`. -/
theorem sb_coe_inv (g : Spin F n) : ((g⁻¹ : Spin F n) : C F n) = star (g : C F n) := by
  rw [← spinGroup.star_eq_inv, spinGroup.coe_star]

/-- Conjugation by `g ∈ Spin(V)` on `C(V)` is the algebra automorphism induced by the isometry
`ρ_g` of `V`: both are algebra homomorphisms and `g v g⁻¹ = ρ_g(v)` on `V`. -/
theorem sb_conjSpin_eq_map (g : Spin F n) (x : C F n) :
    conjSpin F n g x = CliffordAlgebra.map (sb_rhoIsometry F n g) x := by
  have hgg : star (g : C F n) * (g : C F n) = 1 := spinGroup.coe_star_mul_self g
  have hgg' : (g : C F n) * star (g : C F n) = 1 := spinGroup.coe_mul_star_self g
  unfold conjSpin
  rw [sb_coe_inv]
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, ← Algebra.commutes, mul_assoc, hgg', mul_one]
  | ι v =>
    rw [map_apply_ι]
    exact (ι_rho F n g v).symm
  | mul a b ha hb =>
    rw [map_mul, ← ha, ← hb]
    calc (g : C F n) * (a * b) * star (g : C F n)
        = (g : C F n) * a * (star (g : C F n) * (g : C F n)) * b * star (g : C F n) := by
          rw [hgg]; noncomm_ring
      _ = _ := by noncomm_ring
  | add a b ha hb =>
    rw [map_add, ← ha, ← hb]
    noncomm_ring

/-- **[Chevalley, III.3.1]** (`chevalley_III_3_1_equivariant`) on all of `S ⊗ S`:
`φ ∘ (m_g ⊗ m_g) = conjSpin g ∘ φ`. -/
theorem sb_varphi_map (g : Spin F n) (y : S F n ⊗[F] S F n) :
    varphi F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y) =
      conjSpin F n g (varphi F n y) := by
  unfold conjSpin
  rw [sb_coe_inv]
  induction y with
  | tmul s t => rw [TensorProduct.map_tmul, chevalley_III_3_1_equivariant]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, mul_add, add_mul]

/-! ### The grading of `⋀•V` and the two filtrations (after P05's `s23_` lemmas in
`WeilClasses.Chevalley.Sec2_3`, which imports this file) -/

omit [CharZero F] in
private theorem sb_projDeg_of_mem {k : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^k (V F n)) :
    projDeg F n k z = z :=
  DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) hz

omit [CharZero F] in
private theorem sb_projDeg_of_mem_ne {i j : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^i (V F n))
    (hij : i ≠ j) : projDeg F n j z = 0 :=
  DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) hz hij

omit [CharZero F] in
private theorem sb_eq_zero_of_projDeg {z : ExtV F n} (h : ∀ j, projDeg F n j z = 0) : z = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) z]
  exact Finset.sum_eq_zero fun j _ => h j

omit [CharZero F] in
/-- `F^k(⋀•V)` is the set of elements without components of degree `> k`. -/
private theorem sb_mem_extFiltLE_iff (k : ℕ) (z : ExtV F n) :
    z ∈ extFiltLE F n k ↔ ∀ j, k < j → projDeg F n j z = 0 := by
  classical
  constructor
  · intro hz
    have hle : extFiltLE F n k ≤ ⨅ (j : ℕ) (_ : k < j), LinearMap.ker (projDeg F n j) :=
      iSup₂_le fun i hi y hy => by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker]
        intro j hj
        exact sb_projDeg_of_mem_ne F n hy (by omega)
    have := hle hz
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this
  · intro h
    rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) z]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hjk : j ≤ k
    · exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hjk
        (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) z j).2)
    · have h0 := h j (lt_of_not_ge hjk)
      change projDeg F n j z ∈ _
      rw [h0]
      exact zero_mem _

omit [CharZero F] in
private theorem sb_projDeg_eq_zero_of_mem_extFiltLE {k j : ℕ} (hkj : k < j) {z : ExtV F n}
    (hz : z ∈ extFiltLE F n k) : projDeg F n j z = 0 :=
  (sb_mem_extFiltLE_iff F n k z).1 hz j hkj

omit [CharZero F] in
private theorem sb_mem_extFiltLE_of_mem {i k : ℕ} (hik : i ≤ k) {z : ExtV F n}
    (hz : z ∈ ⋀[F]^i (V F n)) : z ∈ extFiltLE F n k :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hik hz)

omit [CharZero F] in
private theorem sb_extFiltLE_mono {i k : ℕ} (hik : i ≤ k) : extFiltLE F n i ≤ extFiltLE F n k :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ≤ k) => ⋀[F]^j (V F n)) j
    (hj.trans hik) le_rfl

omit [CharZero F] in
private theorem sb_mem_extFiltLE_of_succ {k : ℕ} {z : ExtV F n} (hz : z ∈ extFiltLE F n (k + 1))
    (h0 : projDeg F n (k + 1) z = 0) : z ∈ extFiltLE F n k := by
  rw [sb_mem_extFiltLE_iff] at hz ⊢
  intro j hj
  rcases Nat.lt_or_ge (k + 1) j with h | h
  · exact hz j h
  · rw [show j = k + 1 by omega]; exact h0

omit [CharZero F] in
/-- `F^k(⋀•V)` is Tau Ceti's degree filtration of `CliffordAlgebra 0 = ⋀•V`. -/
private theorem sb_filtration_zero_eq (k : ℕ) :
    CliffordAlgebra.filtration (0 : QuadraticForm F (V F n)) k = extFiltLE F n k := by
  rw [CliffordAlgebra.filtration_eq_iSup_pow, extFiltLE, iSup_subtype']

omit [CharZero F] in
/-- `C(V)_k` is Tau Ceti's degree filtration of `C(V)`. -/
private theorem sb_CFilt_eq (k : ℕ) : CFilt F n k = CliffordAlgebra.filtration (Q F n) k := by
  rw [CliffordAlgebra.filtration_eq_iSup_pow, CFilt, iSup_subtype']

omit [CharZero F] in
private theorem sb_CFiltLT_succ (k : ℕ) : CFiltLT F n (k + 1) = CFilt F n k := by
  simp only [CFiltLT, CFilt, Nat.lt_succ_iff]

omit [CharZero F] in
private theorem sb_CFiltLT_zero : CFiltLT F n 0 = ⊥ := by
  simp [CFiltLT]

omit [CharZero F] in
/-- Exterior multiplication by a vector raises degrees by one. -/
private theorem sb_projDeg_ι_mul (v : V F n) (j : ℕ) (z : ExtV F n) :
    projDeg F n (j + 1) (ExteriorAlgebra.ι F v * z) = ExteriorAlgebra.ι F v * projDeg F n j z := by
  have hz : z ∈ ⨆ i : ℕ, ⋀[F]^i (V F n) := by
    rw [(DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[F]^i (V F n))).submodule_iSup_eq_top]
    exact Submodule.mem_top
  induction hz using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  | mem i z hz =>
    have h1 : ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (V F n) := by
      show ExteriorAlgebra.ι F v ∈ LinearMap.range (ExteriorAlgebra.ι F) ^ 1
      rw [pow_one]
      exact LinearMap.mem_range_self _ v
    have hvz : ExteriorAlgebra.ι F v * z ∈ ⋀[F]^(i + 1) (V F n) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded h1 hz
    by_cases hij : i = j
    · subst hij
      rw [sb_projDeg_of_mem F n hvz, sb_projDeg_of_mem F n hz]
    · rw [sb_projDeg_of_mem_ne F n hvz (by omega), sb_projDeg_of_mem_ne F n hz hij, mul_zero]

omit [CharZero F] in
/-- Contraction preserves `F^k(⋀•V)`. -/
private theorem sb_contractLeft_mem_extFiltLE (d : Module.Dual F (V F n)) {k : ℕ} {z : ExtV F n}
    (hz : z ∈ extFiltLE F n k) : contractLeft d z ∈ extFiltLE F n k := by
  rw [← sb_filtration_zero_eq] at hz ⊢
  exact CliffordAlgebra.contractLeft_mem_filtration _ d hz

omit [CharZero F] in
/-- The leading term of `ψ_B` on a product of vectors: `ψ_B(v₁ ⋯ v_j) ∈ F^j(⋀•V)` with degree-`j`
component `v₁ ∧ ⋯ ∧ v_j` (Tau Ceti's `changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration`). -/
private theorem sb_changeForm_prod (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (l : List (V F n)) :
    CliffordAlgebra.changeForm hB (l.map (CliffordAlgebra.ι (Q F n))).prod ∈
        extFiltLE F n l.length ∧
      projDeg F n l.length
          (CliffordAlgebra.changeForm hB (l.map (CliffordAlgebra.ι (Q F n))).prod) =
        (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod := by
  have hwedge : (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod ∈
      ⋀[F]^l.length (V F n) := CliffordAlgebra.prod_map_ι_mem_pow _ l
  have hdiff : CliffordAlgebra.changeForm hB (l.map (CliffordAlgebra.ι (Q F n))).prod -
      (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod ∈
      extFiltLE F n (l.length - 1) := by
    rw [← sb_filtration_zero_eq]
    exact CliffordAlgebra.changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration (Q F n) hB l
      (by omega)
  refine ⟨?_, ?_⟩
  · rw [← sub_add_cancel (CliffordAlgebra.changeForm hB (l.map (CliffordAlgebra.ι (Q F n))).prod)
      (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod]
    exact add_mem (sb_extFiltLE_mono F n (Nat.sub_le _ _) hdiff)
      (sb_mem_extFiltLE_of_mem F n le_rfl hwedge)
  · rcases Nat.eq_zero_or_pos l.length with h | h
    · have h0 : CliffordAlgebra.changeForm hB (l.map (CliffordAlgebra.ι (Q F n))).prod =
          (l.map (CliffordAlgebra.ι (0 : QuadraticForm F (V F n)))).prod := by
        rw [List.length_eq_zero_iff.1 h]
        simp
      rw [h0, sb_projDeg_of_mem F n hwedge]
    · have := sb_projDeg_eq_zero_of_mem_extFiltLE F n (by omega : l.length - 1 < l.length) hdiff
      rw [map_sub, sub_eq_zero, sb_projDeg_of_mem F n hwedge] at this
      exact this

/-! ## The cited results -/

set_option linter.unusedSectionVars false in
/-- **[Chevalley, II.1.6]** (filtration): for a bilinear form `B` on `V` with `B(u, u) = Q(u)`,
`ψ_B = changeForm(-B)` maps `C(V)_k` into `F^k(⋀•V)`. Special case `B = B₀`: §2.3, TeX line 1064. -/
theorem chevalley_II_1_6_filtration (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {x : C F n}
    (hx : x ∈ CFilt F n k) : CliffordAlgebra.changeForm hB x ∈ extFiltLE F n k := by
  rw [sb_CFilt_eq] at hx
  rw [← sb_filtration_zero_eq]
  exact CliffordAlgebra.changeForm_mem_filtration (Q F n) hB hx

/-- **[Chevalley, II.1.6]** (surjectivity of the graded map): `C(V)_k / C(V)_{k-1} → ⋀^k V`,
`x ↦ degree-k component of ψ_B(x)`, is surjective. Special case `B = B₀`: §2.3, TeX line 1067. -/
theorem chevalley_II_1_6_surjective (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {y : ExtV F n}
    (hy : y ∈ ⋀[F]^k (V F n)) :
    ∃ x ∈ CFilt F n k, projDeg F n k (CliffordAlgebra.changeForm hB x) = y := by
  -- `⋀^k V = (range ι)^k`: induct on `y` along products `v ∧ y'`; lift `v ∧ y'` to `v x'`.
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    refine ⟨algebraMap F (C F n) r, ?_, ?_⟩
    · rw [sb_CFilt_eq]
      exact CliffordAlgebra.algebraMap_mem_filtration (Q F n) r 0
    · rw [changeForm_algebraMap, sb_projDeg_of_mem F n (Submodule.algebraMap_mem r)]
  | add x y i hx hy ihx ihy =>
    obtain ⟨a, ha, rfl⟩ := ihx
    obtain ⟨b, hb, rfl⟩ := ihy
    exact ⟨a + b, add_mem ha hb, by rw [map_add, map_add]⟩
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    obtain ⟨z, hz, rfl⟩ := ih
    refine ⟨CliffordAlgebra.ι (Q F n) v * z, ?_, ?_⟩
    · rw [sb_CFilt_eq] at hz ⊢
      simpa [Nat.add_comm] using CliffordAlgebra.mul_mem_filtration (Q F n)
        (CliffordAlgebra.ι_mem_filtration_one (Q F n) v) hz
    · -- `ψ_B(v z) = v ∧ ψ_B(z) + B(v, ·) ⌋ ψ_B(z)`, and the contraction has degree `≤ i`
      rw [changeForm_ι_mul, map_sub, Nat.succ_eq_add_one, sb_projDeg_ι_mul,
        sb_projDeg_eq_zero_of_mem_extFiltLE F n (Nat.lt_succ_self i)
          (sb_contractLeft_mem_extFiltLE F n _ (chevalley_II_1_6_filtration F n B hB i hz)),
        sub_zero]

/-- **[Chevalley, II.1.6]** (injectivity of the graded map): for `x ∈ C(V)_k`, the degree-`k`
component of `ψ_B(x)` vanishes iff `x ∈ C(V)_{k-1}`. Special case `B = B₀`: §2.3, TeX line 1068
("it induces an isomorphism once we tensor with `ℚ`"). -/
theorem chevalley_II_1_6_injective (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (k : ℕ) {x : C F n}
    (hx : x ∈ CFilt F n k) :
    projDeg F n k (CliffordAlgebra.changeForm hB x) = 0 ↔ x ∈ CFiltLT F n k := by
  have hψ := chevalley_II_1_6_filtration F n B hB k hx
  constructor
  · intro h0
    cases k with
    | zero =>
      -- `ψ_B(x) ∈ F^0` with zero degree-`0` part vanishes, and `ψ_B` is injective
      rw [sb_CFiltLT_zero, Submodule.mem_bot]
      have hz : CliffordAlgebra.changeForm hB x = 0 := by
        refine sb_eq_zero_of_projDeg F n fun j => ?_
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact h0
        · exact sb_projDeg_eq_zero_of_mem_extFiltLE F n hj hψ
      apply (CliffordAlgebra.changeFormEquiv hB).injective
      rw [CliffordAlgebra.changeFormEquiv_apply, hz, map_zero]
    | succ k =>
      -- `ψ_B(x) ∈ F^k`, and `ψ_B` reflects the filtration (Tau Ceti)
      rw [sb_CFiltLT_succ, sb_CFilt_eq,
        ← CliffordAlgebra.changeForm_mem_filtration_iff (Q F n) hB k x, sb_filtration_zero_eq]
      exact sb_mem_extFiltLE_of_succ F n hψ h0
  · intro hlt
    cases k with
    | zero =>
      rw [sb_CFiltLT_zero, Submodule.mem_bot] at hlt
      rw [hlt, map_zero, map_zero]
    | succ k =>
      rw [sb_CFiltLT_succ] at hlt
      exact sb_projDeg_eq_zero_of_mem_extFiltLE F n (Nat.lt_succ_self k)
        (chevalley_II_1_6_filtration F n B hB k hlt)

/-- **[Chevalley, Sec. 3.3]**: conjugation by `Spin(V)` preserves the filtration `C(V)_k`.
Used in §2.3, TeX line 1069. -/
theorem chevalley_sec3_3_conj_mem (g : Spin F n) (k : ℕ) {x : C F n} (hx : x ∈ CFilt F n k) :
    conjSpin F n g x ∈ CFilt F n k := by
  rw [sb_conjSpin_eq_map]
  rw [sb_CFilt_eq] at hx ⊢
  exact CliffordAlgebra.map_mem_filtration (Q F n) (sb_rhoIsometry F n g) hx

/-- **[Chevalley, Sec. 3.3]**: the graded isomorphism `C(V)_k / C(V)_{k-1} ≅ ⋀^k V` induced by
`ψ_B` is `Spin(V)`-equivariant (conjugation on `C(V)`, `⋀^k ρ` on `⋀^k V`). Special case `B = B₀`:
§2.3, TeX line 1069. -/
theorem chevalley_sec3_3_equivariant (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (g : Spin F n) (k : ℕ)
    {x : C F n} (hx : x ∈ CFilt F n k) :
    projDeg F n k (CliffordAlgebra.changeForm hB (conjSpin F n g x)) =
      rhoExt F n g (projDeg F n k (CliffordAlgebra.changeForm hB x)) := by
  rw [sb_conjSpin_eq_map]
  -- both sides are linear in `x`; check them on the products of `j ≤ k` vectors spanning `C(V)_k`
  have hle : CFilt F n k ≤ LinearMap.ker
      (projDeg F n k ∘ₗ CliffordAlgebra.changeForm hB ∘ₗ
          (CliffordAlgebra.map (sb_rhoIsometry F n g)).toLinearMap -
        (rhoExt F n g).toLinearMap ∘ₗ projDeg F n k ∘ₗ CliffordAlgebra.changeForm hB) := by
    rw [sb_CFilt_eq, CliffordAlgebra.filtration_le_iff]
    intro l hl
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    have hmap : CliffordAlgebra.map (sb_rhoIsometry F n g)
        (l.map (CliffordAlgebra.ι (Q F n))).prod =
        ((l.map (rho F n g)).map (CliffordAlgebra.ι (Q F n))).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun v _ => ?_
      simp only [Function.comp_apply, CliffordAlgebra.map_apply_ι]
      rfl
    have hlen : (l.map (rho F n g)).length = l.length := List.length_map _
    rw [hmap]
    rcases hl.lt_or_eq with hlt | heq
    · -- fewer than `k` vectors: both degree-`k` components vanish
      rw [sb_projDeg_eq_zero_of_mem_extFiltLE F n (by omega)
          (sb_changeForm_prod F n B hB (l.map (rho F n g))).1,
        sb_projDeg_eq_zero_of_mem_extFiltLE F n hlt (sb_changeForm_prod F n B hB l).1, map_zero]
    · -- `k` vectors: the leading terms are `ρ_g v₁ ∧ ⋯ ∧ ρ_g v_k = ⋀ρ_g(v₁ ∧ ⋯ ∧ v_k)`
      subst heq
      have h1 := (sb_changeForm_prod F n B hB (l.map (rho F n g))).2
      rw [hlen] at h1
      rw [h1, (sb_changeForm_prod F n B hB l).2, rhoExt, map_list_prod, List.map_map,
        List.map_map]
      congr 1
      refine List.map_congr_left fun v _ => ?_
      simp only [Function.comp_apply]
      exact (ExteriorAlgebra.map_apply_ι _ v).symm
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using this

/-- **[Chevalley, p. 85]** (discussion following the proof of III.3.1): the `Spin(V)`-action on
`⋀•V` obtained from `m ⊗ m` by conjugating with `ψ_B ∘ φ` preserves `F^k(⋀•V)`, and its associated
graded action is `⋀ρ`, whatever `B` is. Special case `B = B₀`: §2.3, TeX lines 1074–1077. -/
theorem chevalley_p85_transport_graded (B : LinearMap.BilinForm F (V F n))
    (hB : (-B).toQuadraticMap = (0 : QuadraticForm F (V F n)) - Q F n) (g : Spin F n) (k : ℕ)
    (y : S F n ⊗[F] S F n) (hy : CliffordAlgebra.changeForm hB (varphi F n y) ∈ extFiltLE F n k) :
    CliffordAlgebra.changeForm hB
        (varphi F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y)) ∈
        extFiltLE F n k ∧
      projDeg F n k (CliffordAlgebra.changeForm hB
          (varphi F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) y))) =
        rhoExt F n g (projDeg F n k (CliffordAlgebra.changeForm hB (varphi F n y))) := by
  -- `φ(y) ∈ C(V)_k`, since `ψ_B` reflects the filtration (Tau Ceti)
  have hx : varphi F n y ∈ CFilt F n k := by
    rw [sb_CFilt_eq, ← CliffordAlgebra.changeForm_mem_filtration_iff (Q F n) hB k,
      sb_filtration_zero_eq]
    exact hy
  -- [III.3.1]: `φ((m_g ⊗ m_g) y) = g φ(y) g⁻¹`; then [Sec. 3.3]
  rw [sb_varphi_map]
  exact ⟨chevalley_II_1_6_filtration F n B hB k (chevalley_sec3_3_conj_mem F n g k hx),
    chevalley_sec3_3_equivariant F n B hB g k hx⟩

end WeilClasses
