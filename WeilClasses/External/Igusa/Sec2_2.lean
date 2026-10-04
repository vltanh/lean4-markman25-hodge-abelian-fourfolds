module

public import WeilClasses.PureSpinor.Stabilizer
public import WeilClasses.External.Igusa.Sec2_4
import WeilClasses.External.Chevalley.Sec2_1
import WeilClasses.External.Chevalley.Sec2_2
import WeilClasses.External.Chevalley.Sec3
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection

/-!
# Igusa, *A classification of spinors up to dimension twelve*, Lemmas 1 and 2, as used in §2.2

[I] J.-I. Igusa, *A classification of spinors up to dimension twelve*, Amer. J. Math. 92 (1970),
no. 4, 997–1028. Igusa works with algebraic groups over a universal domain (an algebraically closed
field). The paper applies his Lemmas 1 and 2 to the groups of `K`-points, `K = ℚ(√-d)`; we state the
results over an arbitrary field `F` of characteristic zero, for two even pure spinors `u₁, u₂` with
`W₁ ∩ W₂ = 0` (`Wᵢ = ker m_{uᵢ}`), in the form valid for `F`-points.

* [Lemma 1] (and its proof, including the second displayed formula for `φ(sᵢ(λ))` in §2), used
  in §2.2: `Spin(V)_{ℓ₁,ℓ₂}/{±1} ≅ GL(W₁)` via `g ↦ ρ(g)|_{W₁}`, the element corresponding to `g`
  acting on `W₂ ≅ W₁*` by `(g*)⁻¹`, and `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`. Over a non-closed field the image of the
  `F`-points is the subgroup of `GL(W₁)` of square determinant (`igusa_lemma1_range`); it is all of
  `GL(W₁)` over an algebraically closed (or quadratically closed) field.
* [Lemma 2] and the remark following it, used in Remark 2.2.3 (and in §10): for `n ≥ 3` and
  `w = a u₁ + b u₂` with `a, b ≠ 0`, the stabilizer of `w` is `Spin(V)_{u₁,u₂}` (pointwise
  stabilizer of `u₁, u₂`) if `n` is odd, and has `Spin(V)_{u₁,u₂}` as identity component, with two
  components, if `n` is even (`F`-points: normal of index at most `2`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prover SC, prefix `sc_`): the quadratic space `V_F` and the vector action -/

section SCGeneral

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem sc_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

theorem sc_Q_rho (g : Spin F n) (v : V F n) : Q F n (rho F n g v) = Q F n v :=
  spinVectorAction_map_app (Q F n) g v

/-- `ρ(g)` is an isometry of the pairing (1.2.2). -/
theorem sc_pairing_rho (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  show QuadraticMap.polar (Q F n) (rho F n g x) (rho F n g y) = QuadraticMap.polar (Q F n) x y
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, sc_Q_rho, sc_Q_rho, sc_Q_rho]

theorem sc_rho_mul (g h : Spin F n) (v : V F n) :
    rho F n (g * h) v = rho F n g (rho F n h v) := by
  simp [rho, spinVectorAction_mul]

theorem sc_rho_one (v : V F n) : rho F n 1 v = v := by
  simp [rho]

theorem sc_rho_inv_rho (g : Spin F n) (v : V F n) : rho F n g⁻¹ (rho F n g v) = v := by
  rw [← sc_rho_mul, inv_mul_cancel, sc_rho_one]

theorem sc_rho_rho_inv (g : Spin F n) (v : V F n) : rho F n g (rho F n g⁻¹ v) = v := by
  rw [← sc_rho_mul, mul_inv_cancel, sc_rho_one]

omit [CharZero F] in
theorem sc_pairing_comm (x y : V F n) : pairing F n x y = pairing F n y x :=
  QuadraticMap.polar_comm _ _ _

omit [CharZero F] in
theorem sc_finrank_V : Module.finrank F (V F n) = 2 * n + 2 * n := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_fin_fun]

omit [CharZero F] in
/-- The pairing vanishes on a maximal isotropic subspace. -/
theorem sc_pairing_eq_zero_of_isMaxIsotropic {W : Submodule F (V F n)}
    (hW : IsMaxIsotropic F n W) {x y : V F n} (hx : x ∈ W) (hy : y ∈ W) : pairing F n x y = 0 := by
  show QuadraticMap.polar (Q F n) x y = 0
  rw [QuadraticMap.polar, hW.1 _ (W.add_mem hx hy), hW.1 x hx, hW.1 y hy]
  ring

omit [CharZero F] in
/-- Two transversal maximal isotropic subspaces are complementary. -/
theorem sc_isCompl {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) (hW : W₁ ⊓ W₂ = ⊥) : IsCompl W₁ W₂ := by
  refine IsCompl.of_eq hW ?_
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  rw [hW, finrank_bot, add_zero, h₁.2, h₂.2] at this
  rw [this, sc_finrank_V]

/-- The pairing (1.2.2) is nondegenerate. -/
theorem sc_eq_zero_of_pairing_eq_zero {y : V F n} (h : ∀ v, pairing F n y v = 0) : y = 0 := by
  have hker : (Q F n).polarBilin.ker = ⊥ := by
    rw [← QuadraticMap.radical_eq_ker_polarBilin]
    exact sc_Q_nondegenerate.radical_eq_bot
  have hy : y ∈ (Q F n).polarBilin.ker := by
    rw [LinearMap.mem_ker]
    exact LinearMap.ext fun v => h v
  rw [hker] at hy
  exact hy

/-- In `V = W₁ ⊕ W₂` with `W₂` isotropic, a vector of `W₂` orthogonal to `W₁` is zero. -/
theorem sc_eq_zero_of_mem_of_orth {W₁ W₂ : Submodule F (V F n)} (hC : IsCompl W₁ W₂)
    (h₂ : IsMaxIsotropic F n W₂) {y : V F n} (hy : y ∈ W₂)
    (h : ∀ x ∈ W₁, pairing F n x y = 0) : y = 0 := by
  apply sc_eq_zero_of_pairing_eq_zero
  intro v
  obtain ⟨x, hx, w, hw, rfl⟩ :=
    Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, sc_pairing_comm y x, h x hx, sc_pairing_eq_zero_of_isMaxIsotropic h₂ hy hw,
    zero_add]

/-- The value of `pairRestrict` is the restriction of `ρ(g)`. -/
theorem sc_pairRestrict_apply (u₁ u₂ : S F n)
    (g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)))
    (x : ann F n u₁) :
    ((((pairRestrict F n u₁ u₂ g : (Module.End F (ann F n u₁))ˣ) : Module.End F (ann F n u₁)) x :
      ann F n u₁) : V F n) = rho F n g x := rfl

omit [CharZero F] in
/-- If `n = 0`, `V` is the zero space. -/
theorem sc_V_subsingleton (hn : n = 0) : Subsingleton (V F n) := by
  subst hn
  have h : Module.finrank F (V F 0) = 0 := by rw [sc_finrank_V]
  exact Module.finrank_zero_iff.mp h

omit [CharZero F] in
theorem sc_V_nontrivial (hn : 0 < n) : Nontrivial (V F n) := by
  apply Module.nontrivial_of_finrank_pos (R := F)
  rw [sc_finrank_V]
  omega

/-- The kernel of `ρ` is `{±1}`. -/
theorem sc_rho_eq_id_iff (g : Spin F n) :
    (∀ v, rho F n g v = v) ↔ (g : C F n) = 1 ∨ (g : C F n) = -1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have := sc_V_subsingleton (F := F) hn
      left
      rw [Subsingleton.elim g 1]
      rfl
    · have := sc_V_nontrivial (F := F) hn
      have hker : g ∈ MonoidHom.ker (spinToOrthogonal (Q F n)) := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        rw [coe_spinToOrthogonal_apply]
        exact h v
      rcases (mem_ker_spinToOrthogonal_iff (Q F n) sc_Q_nondegenerate g).mp hker with h1 | h1
      · left
        rw [h1]
        rfl
      · right
        rw [h1, spinGroup.coe_negOne]
  · intro h v
    apply ι_injective (Q F n)
    rw [ι_rho]
    rcases h with h | h
    · rw [h, star_one, one_mul, mul_one]
    · rw [h, star_neg, star_one, neg_one_mul, mul_neg_one, neg_neg]

end SCGeneral

/-! ## Helpers (prover SC): lifts of transvections and of a diagonal matrix
(for `igusa_lemma1_range`) -/

section SCRange

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- An element of `Spin(V)` preserving `ker m_u` stabilizes the line of `u`
([Chevalley, III.3.2/III.4.5]). -/
theorem sc_mem_lineStabilizer {u : S F n} (hu : IsEvenPureSpinor F n u) (g : Spin F n)
    (hg : ∀ v ∈ ann F n u, rho F n g v ∈ ann F n u) : g ∈ lineStabilizer F n u := by
  obtain ⟨c, hc, -⟩ := chevalley_III_3_2_III_4_5 F n u hu g hg
  exact ⟨c, hc⟩

/-- The pairing identifies `W₂` with `W₁*`: a basis `a` of `W₁` has a dual family `b` in `W₂`,
`(a_i, b_k)_V = δ_{ik}`. -/
theorem sc_exists_dual {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) (hW : W₁ ⊓ W₂ = ⊥) (a : Module.Basis (Fin (2 * n)) F W₁) :
    ∃ b : Fin (2 * n) → V F n, (∀ k, b k ∈ W₂) ∧
      ∀ i k, pairing F n (a i) (b k) = if i = k then 1 else 0 := by
  have hC := sc_isCompl h₁ h₂ hW
  let e : W₂ →ₗ[F] Module.Dual F W₁ := ((pairing F n).compl₁₂ W₁.subtype W₂.subtype).flip
  have he : ∀ (y : W₂) (x : W₁), e y x = pairing F n x y := fun _ _ => rfl
  have hinj : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    apply sc_eq_zero_of_mem_of_orth hC h₂ y.2
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    rwa [he] at this
  have hbij : Function.Bijective e := by
    refine ⟨hinj, ?_⟩
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Subspace.dual_finrank_eq, h₁.2, h₂.2]
  let E := LinearEquiv.ofBijective e hbij
  refine ⟨fun k => (E.symm (a.coord k) : V F n), fun k => (E.symm (a.coord k)).2, ?_⟩
  intro i k
  rw [← he (E.symm (a.coord k)) (a i)]
  show E (E.symm (a.coord k)) (a i) = _
  rw [LinearEquiv.apply_symm_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- Lift of a transvection: for `a ∈ W₁` and `b ∈ W₂` with `(a, b)_V = 0` and `c ∈ F`, an element of
`Spin(V)` preserving `W₁` and `W₂` and acting on `W₁` by `x ↦ x + c (x, b)_V a` (the Spin lift of
the Eichler transvection `E_{b, c a}`). -/
theorem sc_transvection_lift {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) {a b : V F n} (ha : a ∈ W₁) (hb : b ∈ W₂)
    (hab : pairing F n a b = 0) (c : F) :
    ∃ g : Spin F n, (g : C F n) = 1 + ι (Q F n) (c • a) * ι (Q F n) b ∧
      (∀ v ∈ W₁, rho F n g v ∈ W₁) ∧ (∀ v ∈ W₂, rho F n g v ∈ W₂) ∧
      ∀ v ∈ W₁, rho F n g v = v + (c * pairing F n v b) • a := by
  have hu : Q F n b = 0 := h₂.1 b hb
  have huw : QuadraticMap.polar (Q F n) b (c • a) = 0 := by
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm]
    have : QuadraticMap.polar (Q F n) a b = 0 := hab
    rw [this, smul_zero]
  have hQw : Q F n (c • a) = 0 := by rw [QuadraticMap.map_smul, h₁.1 a ha, smul_zero]
  have hρ : ∀ v, rho F n (spinTransvection sc_Q_nondegenerate hu huw) v =
      v + QuadraticMap.polar (Q F n) v b • (c • a) - QuadraticMap.polar (Q F n) v (c • a) • b -
        (Q F n (c • a) * QuadraticMap.polar (Q F n) v b) • b := by
    intro v
    rw [rho, ← coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_spinTransvection,
      QuadraticMap.transvection_apply]
  refine ⟨spinTransvection sc_Q_nondegenerate hu huw, coe_spinTransvection _ _ _, ?_, ?_, ?_⟩
  · intro v hv
    have h0 : QuadraticMap.polar (Q F n) v (c • a) = 0 := by
      rw [QuadraticMap.polar_smul_right]
      have : QuadraticMap.polar (Q F n) v a = 0 := sc_pairing_eq_zero_of_isMaxIsotropic h₁ hv ha
      rw [this, smul_zero]
    rw [hρ, h0, hQw, zero_smul, zero_mul, zero_smul, sub_zero, sub_zero]
    exact W₁.add_mem hv (W₁.smul_mem _ (W₁.smul_mem _ ha))
  · intro v hv
    have h0 : QuadraticMap.polar (Q F n) v b = 0 := sc_pairing_eq_zero_of_isMaxIsotropic h₂ hv hb
    rw [hρ, h0, zero_smul, add_zero, mul_zero, zero_smul, sub_zero]
    exact W₂.sub_mem hv (W₂.smul_mem _ hb)
  · intro v hv
    have h0 : QuadraticMap.polar (Q F n) v (c • a) = 0 := by
      rw [QuadraticMap.polar_smul_right]
      have : QuadraticMap.polar (Q F n) v a = 0 := sc_pairing_eq_zero_of_isMaxIsotropic h₁ hv ha
      rw [this, smul_zero]
    rw [hρ, h0, hQw, zero_smul, zero_mul, zero_smul, sub_zero, sub_zero, smul_smul]
    show v + (QuadraticMap.polar (Q F n) v b * c) • a = v + (c * QuadraticMap.polar (Q F n) v b) • a
    rw [mul_comm (QuadraticMap.polar (Q F n) v b) c]

/-- Lift of a diagonal matrix: for `a ∈ W₁`, `b ∈ W₂` with `(a, b)_V = 1` and `r ≠ 0`, Igusa's
element `s(r)` preserves `W₁` and `W₂` and acts on `W₁` by `x ↦ x + (r² - 1) (x, b)_V a`. -/
theorem sc_diag_lift {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) {a b : V F n} (ha : a ∈ W₁) (hb : b ∈ W₂)
    (hab : pairing F n a b = 1) (r : F) (hr : r ≠ 0) :
    ∃ g : Spin F n, (g : C F n) = igusaFactor a b (Units.mk0 r hr) ∧
      (∀ v ∈ W₁, rho F n g v ∈ W₁) ∧ (∀ v ∈ W₂, rho F n g v ∈ W₂) ∧
      ∀ v ∈ W₁, rho F n g v = v + ((r ^ 2 - 1) * pairing F n v b) • a := by
  have haa : pairing F n a a = 0 := sc_pairing_eq_zero_of_isMaxIsotropic h₁ ha ha
  have hbb : pairing F n b b = 0 := sc_pairing_eq_zero_of_isMaxIsotropic h₂ hb hb
  refine ⟨⟨igusaFactor a b (Units.mk0 r hr), igusa_sec2_mem a b haa hbb hab _⟩, rfl, ?_, ?_, ?_⟩
  · intro v hv
    rw [sc_rho_igusaFactor_eq a b haa hbb hab, sc_pairing_eq_zero_of_isMaxIsotropic h₁ ha hv,
      mul_zero, zero_smul, add_zero]
    exact W₁.add_mem hv (W₁.smul_mem _ ha)
  · intro v hv
    rw [sc_rho_igusaFactor_eq a b haa hbb hab, sc_pairing_eq_zero_of_isMaxIsotropic h₂ hb hv,
      mul_zero, zero_smul, add_zero]
    exact W₂.add_mem hv (W₂.smul_mem _ hb)
  · intro v hv
    rw [sc_rho_igusaFactor_eq a b haa hbb hab, sc_pairing_eq_zero_of_isMaxIsotropic h₁ ha hv,
      mul_zero, zero_smul, add_zero, sc_pairing_comm b v, Units.val_mk0]

omit [CharZero F] in
/-- A two-coordinate diagonal matrix is a product of six transvections (Whitehead). -/
theorem sc_diag2n_decompose {m : Type*} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (c : F) (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij c hc =
      Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
        Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij (-1) *
        Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext p q
  simp only [Matrix.mul_add, mul_one, Matrix.add_mul, one_mul, Matrix.single_mul_single_same,
    mul_neg, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, add_zero, neg_mul, neg_neg,
    ne_eq, hij, not_false_eq_true, Matrix.single_mul_single_of_ne, Matrix.add_apply]
  by_cases hpi : p = i <;> by_cases hpj : p = j <;>
    by_cases hqi : q = i <;> by_cases hqj : q = j
  all_goals simp_all [Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, eq_comm]

omit [CharZero F] in
/-- A transvection matrix acting on a basis vector. -/
theorem sc_toLinAlgEquiv_transvection {M : Type*} [AddCommGroup M] [Module F M] {m : Type*}
    [Fintype m] [DecidableEq m] (a : Module.Basis m F M) (i j : m) (c : F) (k : m) :
    Matrix.toLinAlgEquiv a (Matrix.transvection i j c) (a k) =
      a k + (if k = j then c else 0) • a i := by
  rw [Matrix.toLinAlgEquiv_self]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  by_cases hk : k = j
  · subst hk
    simp
  · have hk' : ¬ j = k := fun h => hk h.symm
    simp [hk', hk]

end SCRange

/-! ## Helpers (prover SC): exterior bases
(as in the helpers `s61_*` of `WeilClasses.Orlov.Defs`) -/

section SCBasis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]
  (b : Module.Basis ι R M)

theorem sc_basis_eq_prod (s : Finset ι) :
    b.ExteriorAlgebra s = ((s.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (b i)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Finset.orderEmbOfFin_apply, Set.powersetCard.ofCard]

theorem sc_basis_insert_min (a : ι) (s : Finset ι) (h : ∀ x ∈ s, a < x) :
    b.ExteriorAlgebra (insert a s) = ExteriorAlgebra.ι R (b a) * b.ExteriorAlgebra s := by
  have ha : a ∉ s := fun ha => lt_irrefl a (h a ha)
  rw [sc_basis_eq_prod, sc_basis_eq_prod, Finset.sort_insert _ (fun x hx => (h x hx).le) ha]
  simp

theorem sc_basis_empty : b.ExteriorAlgebra ∅ = 1 := by
  rw [sc_basis_eq_prod]; simp

/-- `ι(b i) ∧ b_s = ± b_{s ∪ {i}}`, the sign counting the elements of `s` below `i`. -/
theorem sc_ι_mul_basis (i : ι) (s : Finset ι) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0 else (-1 : R) ^ (s.filter (· < i)).card • b.ExteriorAlgebra (insert i s) := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    simp only [Finset.notMem_empty, ite_false, Finset.filter_empty, Finset.card_empty, pow_zero,
      one_smul]
    rw [sc_basis_insert_min b i ∅ (by simp), sc_basis_empty]
  | insert a s ha ih =>
    rw [sc_basis_insert_min b a s ha]
    rcases lt_trichotomy i a with hia | rfl | hai
    · have hi : i ∉ insert a s := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hia.ne, fun hs => lt_asymm hia (ha i hs)⟩
      have hf : (insert a s).filter (· < i) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hx) hxi
        · exact lt_asymm hxi hia
        · exact lt_asymm hxi (hia.trans (ha x hx))
      rw [ite_eq_right hi, hf, Finset.card_empty, pow_zero, one_smul,
        sc_basis_insert_min b i (insert a s), sc_basis_insert_min b a s ha]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hia
      · exact hia.trans (ha x hx)
    · rw [ite_eq_left (Finset.mem_insert_self _ _), ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul]
    · have hswap : ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b a) =
          -(ExteriorAlgebra.ι R (b a) * ExteriorAlgebra.ι R (b i)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hswap, neg_mul, mul_assoc, ih]
      by_cases his : i ∈ s
      · rw [ite_eq_left his, ite_eq_left (Finset.mem_insert_of_mem his), mul_zero, neg_zero]
      · have hi : i ∉ insert a s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hai.ne', his⟩
        rw [ite_eq_right his, ite_eq_right hi, mul_smul_comm,
          ← sc_basis_insert_min b a (insert i s)]
        · have hf : (insert a s).filter (· < i) = insert a (s.filter (· < i)) := by
            rw [Finset.filter_insert, ite_eq_left hai]
          have ha' : a ∉ s.filter (· < i) := fun h => lt_irrefl a (ha a (Finset.mem_filter.mp h).1)
          rw [hf, Finset.card_insert_of_notMem ha', Finset.insert_comm, pow_succ, mul_neg_one,
            neg_smul]
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hai
          · exact ha x hx

/-- Contraction by a coordinate erases it from an exterior basis vector, with the sign counting
the smaller indices. -/
theorem sc_contractLeft_coord_basis (i : ι) (s : Finset ι) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then (-1 : R) ^ (s.filter (· < i)).card • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    rw [sc_basis_empty, ite_eq_right (Finset.notMem_empty i)]
    exact contractLeft_one (Q := (0 : QuadraticForm R M)) (b.coord i)
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [sc_basis_insert_min b a s ha, contractLeft_ι_mul, ih, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hia : a = i
    · subst hia
      have hf : (insert a s).filter (· < a) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hx) hxa
        · exact lt_irrefl _ hxa
        · exact lt_asymm hxa (ha x hx)
      rw [ite_eq_left rfl, ite_eq_right has, mul_zero, sub_zero, one_smul,
        ite_eq_left (Finset.mem_insert_self _ _), hf, Finset.card_empty, pow_zero, one_smul,
        Finset.erase_insert has]
    · rw [ite_eq_right hia, zero_smul, zero_sub]
      by_cases his : i ∈ s
      · have hai : a < i := ha i his
        have hf : (insert a s).filter (· < i) = insert a (s.filter (· < i)) := by
          rw [Finset.filter_insert, ite_eq_left hai]
        have ha' : a ∉ s.filter (· < i) := fun h => has (Finset.mem_filter.mp h).1
        rw [ite_eq_left his, ite_eq_left (Finset.mem_insert_of_mem his), hf,
          Finset.card_insert_of_notMem ha', mul_smul_comm,
          ← sc_basis_insert_min b a (s.erase i) (fun x hx => ha x (Finset.mem_of_mem_erase hx)),
          Finset.erase_insert_of_ne hia, pow_succ, mul_neg_one, neg_smul]
      · have : i ∉ insert a s := by
          simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm hia, his⟩
        rw [ite_eq_right his, ite_eq_right this, mul_zero, neg_zero]

end SCBasis

/-! ## Helpers (prover SC): the pure spinors `1` and `[pt_X]` and a degree argument -/

section SCModel

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem sc_e_eq (i : Fin (2 * n)) : e F n i = Pi.basisFun F (Fin (2 * n)) i := by
  rw [Pi.basisFun_apply]; rfl

omit [CharZero F] in
theorem sc_f_eq (i : Fin (2 * n)) : f F n i = (Pi.basisFun F (Fin (2 * n))).coord i := by
  ext x
  simp [f, Module.Basis.coord_apply]

theorem sc_m_ι (θ : Module.Dual F (H1 F n)) (y : H1 F n) (s : S F n) :
    m F n (ι (Q F n) (θ, y)) s = ExteriorAlgebra.ι F y * s + D F n θ s := by
  rw [m, CliffordAlgebra.lift_ι_apply]
  simp [cliffordOp, L]

omit [CharZero F] in
theorem sc_ι_e_mul_basisS (i : Fin (2 * n)) (s : Finset (Fin (2 * n))) :
    ExteriorAlgebra.ι F (e F n i) * basisS F n s =
      if i ∈ s then 0 else (-1 : F) ^ (s.filter (· < i)).card • basisS F n (insert i s) := by
  rw [sc_e_eq, basisS, sc_ι_mul_basis]

omit [CharZero F] in
theorem sc_D_f_basisS (i : Fin (2 * n)) (s : Finset (Fin (2 * n))) :
    D F n (f F n i) (basisS F n s) =
      if i ∈ s then (-1 : F) ^ (s.filter (· < i)).card • basisS F n (s.erase i) else 0 := by
  rw [sc_f_eq, basisS, D, sc_contractLeft_coord_basis]

omit [CharZero F] in
/-- The coefficient of `e_{K ∪ {i}}` in `e_i ∧ x` is `± x_K` (for `i ∉ K`). -/
theorem sc_repr_ι_e_mul (i : Fin (2 * n)) (K : Finset (Fin (2 * n))) (hi : i ∉ K) (x : S F n) :
    (basisS F n).repr (ExteriorAlgebra.ι F (e F n i) * x) (insert i K) =
      (-1 : F) ^ (K.filter (· < i)).card * (basisS F n).repr x K := by
  have key : ((basisS F n).coord (insert i K)).comp
      (LinearMap.mulLeft F (ExteriorAlgebra.ι F (e F n i))) =
      ((-1 : F) ^ (K.filter (· < i)).card) • (basisS F n).coord K := by
    apply (basisS F n).ext
    intro L
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, sc_ι_e_mul_basisS]
    by_cases hiL : i ∈ L
    · have hLK : L ≠ K := fun h => hi (h ▸ hiL)
      rw [ite_eq_left hiL, map_zero, Finsupp.zero_apply, Finsupp.single_apply, ite_eq_right hLK,
        smul_zero]
    · rw [ite_eq_right hiL, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases hLK : L = K
      · subst hLK
        simp
      · have : insert i L ≠ insert i K := fun h => hLK (by
          rw [← Finset.erase_insert hiL, h, Finset.erase_insert hi])
        rw [ite_eq_right this, ite_eq_right hLK, smul_zero, smul_zero]
  have := LinearMap.congr_fun key x
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul] using this

omit [CharZero F] in
/-- The coefficient of `e_{K ∖ {i}}` in `f_i ⌋ x` is `± x_K` (for `i ∈ K`). -/
theorem sc_repr_D_f (i : Fin (2 * n)) (K : Finset (Fin (2 * n))) (hi : i ∈ K) (x : S F n) :
    (basisS F n).repr (D F n (f F n i) x) (K.erase i) =
      (-1 : F) ^ (K.filter (· < i)).card * (basisS F n).repr x K := by
  have key : ((basisS F n).coord (K.erase i)).comp (D F n (f F n i)) =
      ((-1 : F) ^ (K.filter (· < i)).card) • (basisS F n).coord K := by
    apply (basisS F n).ext
    intro L
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, sc_D_f_basisS]
    by_cases hiL : i ∈ L
    · rw [ite_eq_left hiL, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases hLK : L = K
      · subst hLK
        simp
      · have : L.erase i ≠ K.erase i := fun h => hLK (by
          rw [← Finset.insert_erase hiL, h, Finset.insert_erase hi])
        rw [ite_eq_right this, ite_eq_right hLK, smul_zero, smul_zero]
    · have hLK : L ≠ K := fun h => hiL (h ▸ hi)
      rw [ite_eq_right hiL, map_zero, Finsupp.zero_apply, Finsupp.single_apply, ite_eq_right hLK,
        smul_zero]
  have := LinearMap.congr_fun key x
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul] using this

theorem sc_mem_ann_iff (s : S F n) (v : V F n) : v ∈ ann F n s ↔ m F n (ι (Q F n) v) s = 0 := by
  simp [ann, mOf]

/-- `ker m_1 = H¹(X̂) = H¹(X)* × 0`. -/
theorem sc_mem_ann_one (v : V F n) : v ∈ ann F n 1 ↔ v.2 = 0 := by
  obtain ⟨θ, y⟩ := v
  rw [sc_mem_ann_iff, sc_m_ι, mul_one, D, contractLeft_one, add_zero,
    ExteriorAlgebra.ι_eq_zero_iff]

omit [CharZero F] in
/-- `y ∧ [pt_X] = 0` for `y ∈ H¹(X)`. -/
theorem sc_ι_mul_pt (y : H1 F n) : ExteriorAlgebra.ι F y * pt F n = 0 := by
  have h : (LinearMap.mulRight F (pt F n)).comp (ExteriorAlgebra.ι F : H1 F n →ₗ[F] S F n) = 0 := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← sc_e_eq, pt, sc_ι_e_mul_basisS,
      ite_eq_left (Finset.mem_univ i), LinearMap.zero_apply]
  exact LinearMap.congr_fun h y

omit [CharZero F] in
theorem sc_pt_ne_zero : pt F n ≠ 0 := (basisS F n).ne_zero _

/-- `ker m_{[pt_X]} = H¹(X) = 0 × H¹(X)`. -/
theorem sc_mem_ann_pt (v : V F n) : v ∈ ann F n (pt F n) ↔ v.1 = 0 := by
  obtain ⟨θ, y⟩ := v
  rw [sc_mem_ann_iff, sc_m_ι, sc_ι_mul_pt, zero_add]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ x (pt F n)
    have h2 : (ι (0 : QuadraticForm F (H1 F n)) x * pt F n : S F n) = 0 := sc_ι_mul_pt x
    rw [h2, map_zero] at h1
    have h3 : contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ (pt F n) = 0 := h
    rw [h3, mul_zero, sub_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right sc_pt_ne_zero
  · intro h
    simp only at h
    rw [h, map_zero, LinearMap.zero_apply]

omit [CharZero F] in
theorem sc_one_mem_Splus : (1 : S F n) ∈ Splus F n :=
  CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨1, map_one _⟩)

omit [CharZero F] in
theorem sc_pt_mem_Splus : pt F n ∈ Splus F n := by
  have h := SetLike.list_prod_map_mem_graded
    (A := CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)))
    ((Finset.univ : Finset (Fin (2 * n))).sort (· ≤ ·)) (fun _ => (1 : ZMod 2))
    (fun i => ExteriorAlgebra.ι F (Pi.basisFun F (Fin (2 * n)) i))
    (fun i _ => CliffordAlgebra.ι_mem_evenOdd_one _ _)
  rw [← sc_basis_eq_prod] at h
  have h0 : (((Finset.univ : Finset (Fin (2 * n))).sort (· ≤ ·)).map
      (fun _ => (1 : ZMod 2))).sum = 0 := by
    rw [List.map_const', List.sum_replicate, Finset.length_sort, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul]
    have : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [this, zero_mul]
  rw [h0] at h
  exact h

theorem sc_finrank_ann_one : Module.finrank F (ann F n 1) = 2 * n := by
  have hker : ann F n 1 = LinearMap.ker (LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n)) := by
    ext v
    rw [sc_mem_ann_one, LinearMap.mem_ker, LinearMap.snd_apply]
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n))
  rw [Submodule.range_snd, finrank_top, Module.finrank_fin_fun, sc_finrank_V] at h
  rw [hker]
  exact Nat.add_left_cancel h

theorem sc_finrank_ann_pt : Module.finrank F (ann F n (pt F n)) = 2 * n := by
  have hker : ann F n (pt F n) =
      LinearMap.ker (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n)) := by
    ext v
    rw [sc_mem_ann_pt, LinearMap.mem_ker, LinearMap.fst_apply]
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n))
  rw [Submodule.range_fst, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun,
    sc_finrank_V] at h
  rw [hker]
  exact Nat.add_left_cancel h

theorem sc_isEvenPureSpinor_one : IsEvenPureSpinor F n 1 := by
  refine ⟨sc_one_mem_Splus, fun v hv => ?_, sc_finrank_ann_one⟩
  rw [sc_mem_ann_one] at hv
  obtain ⟨θ, y⟩ := v
  simp only at hv
  rw [hv]
  simp

theorem sc_isEvenPureSpinor_pt : IsEvenPureSpinor F n (pt F n) := by
  refine ⟨sc_pt_mem_Splus, fun v hv => ?_, sc_finrank_ann_pt⟩
  rw [sc_mem_ann_pt] at hv
  obtain ⟨θ, y⟩ := v
  simp only at hv
  rw [hv]
  simp

theorem sc_ann_one_inf_ann_pt : ann F n 1 ⊓ ann F n (pt F n) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, sc_mem_ann_one, sc_mem_ann_pt] at hv
  rw [Submodule.mem_bot]
  exact Prod.ext hv.2 hv.1

omit [CharZero F] in
/-- `ι y` has no component outside degree `1`. -/
theorem sc_repr_ι (y : H1 F n) (K : Finset (Fin (2 * n))) (hK : K.card ≠ 1) :
    (basisS F n).repr (ExteriorAlgebra.ι F y) K = 0 := by
  have h : ((basisS F n).coord K).comp (ExteriorAlgebra.ι F : H1 F n →ₗ[F] S F n) = 0 := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro i
    have h1 := sc_ι_e_mul_basisS (F := F) i ∅
    rw [basisS, sc_basis_empty, mul_one, ← basisS, ite_eq_right (Finset.notMem_empty i),
      Finset.filter_empty, Finset.card_empty, pow_zero, one_smul, insert_empty_eq] at h1
    rw [LinearMap.comp_apply, ← sc_e_eq, h1, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_right, LinearMap.zero_apply]
    rintro rfl
    exact hK (Finset.card_singleton i)
  exact LinearMap.congr_fun h y

omit [CharZero F] in
/-- `θ ⌋ [pt_X]` has no component outside degree `2n - 1`. -/
theorem sc_repr_D_pt (θ : Module.Dual F (H1 F n)) (K : Finset (Fin (2 * n)))
    (hK : K.card ≠ 2 * n - 1) : (basisS F n).repr (D F n θ (pt F n)) K = 0 := by
  have h : ((basisS F n).coord K).comp ((LinearMap.applyₗ (pt F n)).comp (D F n)) = 0 := by
    apply (Pi.basisFun F (Fin (2 * n))).dualBasis.ext
    intro i
    have hfi : (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
      rw [sc_f_eq, Module.Basis.coe_dualBasis]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, hfi, pt,
      sc_D_f_basisS, ite_eq_left (Finset.mem_univ i), map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right, smul_zero, LinearMap.zero_apply]
    rintro rfl
    apply hK
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  exact LinearMap.congr_fun h θ

/-- For `w₀ = α + β [pt_X]`, every `m_v w₀` has components only in degrees `1` and `2n - 1`. -/
theorem sc_repr_m_one_pt (α β : F) (v : V F n) (K : Finset (Fin (2 * n))) (hK1 : K.card ≠ 1)
    (hK2 : K.card ≠ 2 * n - 1) :
    (basisS F n).repr (m F n (ι (Q F n) v) (α • 1 + β • pt F n)) K = 0 := by
  obtain ⟨θ, y⟩ := v
  have h : m F n (ι (Q F n) (θ, y)) (α • 1 + β • pt F n) =
      α • ExteriorAlgebra.ι F y + β • D F n θ (pt F n) := by
    rw [sc_m_ι, mul_add, mul_smul_comm, mul_smul_comm, mul_one, sc_ι_mul_pt, smul_zero, add_zero,
      map_add, map_smul, map_smul, D, contractLeft_one, smul_zero, zero_add]
  rw [h, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    sc_repr_ι y K hK1, sc_repr_D_pt θ K hK2, smul_zero, smul_zero, add_zero]

/-- **A degree argument** (`n ≥ 3`): if every `m_v x`, `v ∈ V`, has components only in degrees
`1` and `2n - 1`, then `x` has components only in degrees `0` and `2n`. -/
theorem sc_repr_eq_zero_of_m (hn : 3 ≤ n) (x : S F n)
    (hx : ∀ v : V F n, ∀ K : Finset (Fin (2 * n)), K.card ≠ 1 → K.card ≠ 2 * n - 1 →
      (basisS F n).repr (m F n (ι (Q F n) v) x) K = 0)
    (K : Finset (Fin (2 * n))) (hK0 : K ≠ ∅) (hKu : K ≠ Finset.univ) :
    (basisS F n).repr x K = 0 := by
  have hcard : K.card < 2 * n := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hKu)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hpos : 0 < K.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hK0)
  have hsign : ∀ k : ℕ, ((-1 : F) ^ k) ≠ 0 := fun k => pow_ne_zero _ (by norm_num)
  by_cases h2 : K.card = 2 * n - 2
  · -- contract by `f_i`, `i ∈ K`: lands in degree `2n - 3 ∉ {1, 2n - 1}`
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hK0
    have h := hx (f F n i, 0) (K.erase i) (by rw [Finset.card_erase_of_mem hi]; omega)
      (by rw [Finset.card_erase_of_mem hi]; omega)
    rw [sc_m_ι, map_zero, zero_mul, zero_add, sc_repr_D_f i K hi] at h
    exact (mul_eq_zero.mp h).resolve_left (hsign _)
  · -- wedge with `e_i`, `i ∉ K`: lands in degree `|K| + 1 ∉ {1, 2n - 1}`
    obtain ⟨i, hi⟩ : ∃ i, i ∉ K := by
      by_contra hc
      push Not at hc
      exact hKu (Finset.eq_univ_iff_forall.mpr hc)
    have h := hx (0, e F n i) (insert i K) (by rw [Finset.card_insert_of_notMem hi]; omega)
      (by rw [Finset.card_insert_of_notMem hi]; omega)
    rw [sc_m_ι, map_zero, LinearMap.zero_apply, add_zero, sc_repr_ι_e_mul i K hi] at h
    exact (mul_eq_zero.mp h).resolve_left (hsign _)

omit [CharZero F] in
/-- A spinor with components only in degrees `0` and `2n` lies in `span {1, [pt_X]}`. -/
theorem sc_eq_of_repr_eq_zero (hn : 0 < n) (x : S F n)
    (hx : ∀ K : Finset (Fin (2 * n)), K ≠ ∅ → K ≠ Finset.univ → (basisS F n).repr x K = 0) :
    x = (basisS F n).repr x ∅ • 1 + (basisS F n).repr x Finset.univ • pt F n := by
  have hne : (∅ : Finset (Fin (2 * n))) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at this
    omega
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ Finset.univ),
    ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ ∅⟩),
    Finset.sum_eq_zero, zero_add, basisS, sc_basis_empty, ← basisS, pt]
  intro K hK
  rw [Finset.mem_erase, Finset.mem_erase] at hK
  rw [hx K hK.1 hK.2.1, zero_smul]

end SCModel

/-! ## Helpers (prover SC): stabilizers of points of a transversal secant -/

section SCLemma2

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `(g s, g t)_S = (s, t)_S` for `g ∈ Spin(V)` ([Chevalley, III.2.1]: `g τ(g) = g g* = 1`). -/
theorem sc_mukai_m_spin (g : Spin F n) (s t : S F n) :
    mukai F n (m F n (g : C F n) s) (m F n (g : C F n) t) = mukai F n s t := by
  have hx : spinGroup.toUnits g ∈ cliffordGroup F n := fun v =>
    ⟨rho F n g v, by
      rw [ι_rho]
      rfl⟩
  have hc : ((spinGroup.toUnits g : (C F n)ˣ) : C F n) *
      reverse ((spinGroup.toUnits g : (C F n)ˣ) : C F n) = algebraMap F (C F n) 1 := by
    have hrev : reverse (g : C F n) = star (g : C F n) := by
      rw [star_def, spinGroup.involute_eq g.2]
    change (g : C F n) * reverse (g : C F n) = _
    rw [hrev, spinGroup.mul_star_self_of_mem g.2, map_one]
  simpa using chevalley_III_2_1 F n (spinGroup.toUnits g) hx 1 hc s t

theorem sc_m_mul (g h : Spin F n) (s : S F n) :
    m F n ((g * h : Spin F n) : C F n) s = m F n (g : C F n) (m F n (h : C F n) s) := by
  rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply]

theorem sc_m_injective (g : Spin F n) : Function.Injective (m F n (g : C F n)) := fun s t h => by
  rw [← fnd_m_inv_m F n g s, h, fnd_m_inv_m]

omit [CharZero F] in
theorem sc_one_ne_zero : (1 : S F n) ≠ 0 := by
  have h := (basisS F n).ne_zero ∅
  rwa [basisS, sc_basis_empty] at h

/-- `ker m_{c s} = ker m_s` for `c ≠ 0`. -/
theorem sc_ann_smul (s : S F n) {c : F} (hc : c ≠ 0) : ann F n (c • s) = ann F n s := by
  ext v
  rw [sc_mem_ann_iff, sc_mem_ann_iff, map_smul, smul_eq_zero, or_iff_right hc]

/-- `ker m_{g u}` is maximal isotropic if `ker m_u` is. -/
theorem sc_isMaxIsotropic_m (g : Spin F n) {u : S F n} (hu : IsMaxIsotropic F n (ann F n u)) :
    IsMaxIsotropic F n (ann F n (m F n (g : C F n) u)) := by
  rw [ann_m_spin]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, sc_Q_rho]
    exact hu.1 v hv
  · rw [LinearEquiv.finrank_map_eq]
    exact hu.2

theorem sc_ne_zero_of_isMaxIsotropic (hn : 0 < n) {u : S F n}
    (hu : IsMaxIsotropic F n (ann F n u)) : u ≠ 0 := by
  rintro rfl
  have h := hu.2
  have htop : ann F n 0 = ⊤ := by
    ext v
    simp only [sc_mem_ann_iff, map_zero, Submodule.mem_top]
  rw [htop, finrank_top, sc_finrank_V] at h
  omega

theorem sc_ann_ne_bot (hn : 0 < n) {u : S F n} (hu : IsMaxIsotropic F n (ann F n u)) :
    ann F n u ≠ ⊥ := by
  intro h
  have := hu.2
  rw [h, finrank_bot] at this
  omega

omit [CharZero F] in
/-- The two coordinates `[1]` and `[pt_X]` of `α + β [pt_X]`. -/
theorem sc_repr_one_pt (hn : 0 < n) (α β : F) :
    (basisS F n).repr (α • 1 + β • pt F n) ∅ = α ∧
      (basisS F n).repr (α • 1 + β • pt F n) Finset.univ = β := by
  have hne : (∅ : Finset (Fin (2 * n))) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at this
    omega
  have h1 : (1 : S F n) = basisS F n ∅ := by rw [basisS, sc_basis_empty]
  rw [h1, pt]
  simp [Module.Basis.repr_self, hne, hne.symm]

/-- `(1, [pt_X])_S ≠ 0` ([Chevalley, III.2.4], `ker m_1 ∩ ker m_{[pt_X]} = 0`). -/
theorem sc_mukai_one_pt_ne_zero (hn : 0 < n) : mukai F n 1 (pt F n) ≠ 0 := by
  intro h
  exact ((chevalley_III_2_4 F n hn 1 (pt F n) sc_isEvenPureSpinor_one
    sc_isEvenPureSpinor_pt).mp h) sc_ann_one_inf_ann_pt

/-- In the model (`n ≥ 3`): a pure spinor `x` all of whose `m_v x` have components only in degrees
`1` and `2n - 1` lies on the line of `1` or on the line of `[pt_X]` ([Chevalley, III.1.12]). -/
theorem sc_model_pure (hn : 3 ≤ n) (x : S F n) (hx : IsMaxIsotropic F n (ann F n x))
    (hm : ∀ v : V F n, ∀ K : Finset (Fin (2 * n)), K.card ≠ 1 → K.card ≠ 2 * n - 1 →
      (basisS F n).repr (m F n (ι (Q F n) v) x) K = 0) :
    (∃ c : F, x = c • 1) ∨ (∃ c : F, x = c • pt F n) := by
  have hn0 : 0 < n := by omega
  have hx' := sc_eq_of_repr_eq_zero hn0 x (sc_repr_eq_zero_of_m hn x hm)
  have hpure : IsEvenPureSpinor F n
      ((basisS F n).repr x ∅ • 1 + (basisS F n).repr x Finset.univ • pt F n) := by
    rw [← hx']
    refine ⟨?_, hx⟩
    rw [hx']
    exact add_mem (Submodule.smul_mem _ _ sc_one_mem_Splus)
      (Submodule.smul_mem _ _ sc_pt_mem_Splus)
  rcases chevalley_III_1_12 F n (by omega) 1 (pt F n) sc_isEvenPureSpinor_one
    sc_isEvenPureSpinor_pt sc_ann_one_inf_ann_pt _ _ hpure with h | h
  · right
    exact ⟨_, by rw [hx', h, zero_smul, zero_add]⟩
  · left
    exact ⟨_, by rw [hx', h, zero_smul, add_zero]⟩

/-- Transport to the model ([Chevalley, §3.3, Lemma 1] and [III.1.4]): some `h ∈ Spin(V)` maps `u₁`
to `α · 1` and `u₂` to `β · [pt_X]`, `α, β ≠ 0`. -/
theorem sc_transport (hn : 0 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) :
    ∃ (h : Spin F n) (α β : F), α ≠ 0 ∧ β ≠ 0 ∧ m F n (h : C F n) u₁ = α • 1 ∧
      m F n (h : C F n) u₂ = β • pt F n := by
  obtain ⟨h, hh₁, hh₂⟩ := chevalley_sec3_3_lemma1 F n u₁ u₂ 1 (pt F n) h₁ h₂
    sc_isEvenPureSpinor_one sc_isEvenPureSpinor_pt hW sc_ann_one_inf_ann_pt
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp
    (chevalley_III_1_4_unique F n 1 (m F n (h : C F n) u₁) sc_one_ne_zero
      sc_isEvenPureSpinor_one.2 (by rw [ann_m_spin, hh₁]))
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp
    (chevalley_III_1_4_unique F n (pt F n) (m F n (h : C F n) u₂) sc_pt_ne_zero
      sc_isEvenPureSpinor_pt.2 (by rw [ann_m_spin, hh₂]))
  refine ⟨h, α, β, ?_, ?_, hα.symm, hβ.symm⟩
  · rintro rfl
    rw [zero_smul] at hα
    exact sc_ne_zero_of_isMaxIsotropic hn h₁.2 (sc_m_injective h (by rw [← hα, map_zero]))
  · rintro rfl
    rw [zero_smul] at hβ
    exact sc_ne_zero_of_isMaxIsotropic hn h₂.2 (sc_m_injective h (by rw [← hβ, map_zero]))

/-- **[Igusa, Lemma 2]** (the key step): for `n ≥ 3`, an element of `Spin(V)` fixing
`w = a u₁ + b u₂` either fixes `u₁` and `u₂`, or (only possible for `n` even) exchanges the lines
`F u₁` and `F u₂`. -/
theorem sc_stab_classify (hn : 3 ≤ n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0)
    (hb : b ≠ 0) (g : Spin F n)
    (hg : m F n (g : C F n) (a • u₁ + b • u₂) = a • u₁ + b • u₂) :
    (m F n (g : C F n) u₁ = u₁ ∧ m F n (g : C F n) u₂ = u₂) ∨
      (Even n ∧ (∃ c : F, m F n (g : C F n) u₁ = c • u₂) ∧
        ∃ c : F, m F n (g : C F n) u₂ = c • u₁) := by
  have hn0 : 0 < n := by omega
  obtain ⟨h, α, β, hα, hβ, hu₁, hu₂⟩ := sc_transport hn0 u₁ u₂ h₁ h₂ hW
  set x := m F n ((h * g : Spin F n) : C F n) u₁ with hxdef
  set y := m F n ((h * g : Spin F n) : C F n) u₂ with hydef
  -- `a x + b y = a α 1 + b β [pt_X]`
  have hw : a • x + b • y = (a * α) • 1 + (b * β) • pt F n := by
    rw [hxdef, hydef, ← map_smul, ← map_smul, ← map_add, sc_m_mul, hg, map_add, map_smul,
      map_smul, hu₁, hu₂, smul_smul, smul_smul]
  -- `ker m_x` and `ker m_y` are complementary maximal isotropic subspaces
  have hxmax : IsMaxIsotropic F n (ann F n x) := sc_isMaxIsotropic_m _ h₁.2
  have hymax : IsMaxIsotropic F n (ann F n y) := sc_isMaxIsotropic_m _ h₂.2
  have hxy : ann F n x ⊓ ann F n y = ⊥ := by
    rw [hxdef, hydef, ann_m_spin, ann_m_spin, ← Submodule.map_inf _
      (rho F n (h * g)).injective, hW, Submodule.map_bot]
  have hC := sc_isCompl hxmax hymax hxy
  -- both satisfy the degree condition of the model
  have hmx : ∀ v : V F n, ∀ K : Finset (Fin (2 * n)), K.card ≠ 1 → K.card ≠ 2 * n - 1 →
      (basisS F n).repr (m F n (ι (Q F n) v) x) K = 0 := by
    intro v K hK1 hK2
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
      Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : m F n (ι (Q F n) v₁) x = 0 := (sc_mem_ann_iff x v₁).mp hv₁
    have h2 : m F n (ι (Q F n) v₂) y = 0 := (sc_mem_ann_iff y v₂).mp hv₂
    have h3 : m F n (ι (Q F n) (v₁ + v₂)) x =
        a⁻¹ • m F n (ι (Q F n) v₂) ((a * α) • 1 + (b * β) • pt F n) := by
      have e1 : m F n (ι (Q F n) (v₁ + v₂)) x = m F n (ι (Q F n) v₂) x := by
        rw [map_add (ι (Q F n)), map_add (m F n), LinearMap.add_apply, h1, zero_add]
      have e2 : m F n (ι (Q F n) v₂) (a • x + b • y) = a • m F n (ι (Q F n) v₂) x := by
        rw [map_add, map_smul, map_smul, h2, smul_zero, add_zero]
      rw [e1, ← hw, e2, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [h3, map_smul, Finsupp.smul_apply, sc_repr_m_one_pt _ _ _ K hK1 hK2, smul_zero]
  have hmy : ∀ v : V F n, ∀ K : Finset (Fin (2 * n)), K.card ≠ 1 → K.card ≠ 2 * n - 1 →
      (basisS F n).repr (m F n (ι (Q F n) v) y) K = 0 := by
    intro v K hK1 hK2
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
      Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : m F n (ι (Q F n) v₁) x = 0 := (sc_mem_ann_iff x v₁).mp hv₁
    have h2 : m F n (ι (Q F n) v₂) y = 0 := (sc_mem_ann_iff y v₂).mp hv₂
    have h3 : m F n (ι (Q F n) (v₁ + v₂)) y =
        b⁻¹ • m F n (ι (Q F n) v₁) ((a * α) • 1 + (b * β) • pt F n) := by
      have e1 : m F n (ι (Q F n) (v₁ + v₂)) y = m F n (ι (Q F n) v₁) y := by
        rw [map_add (ι (Q F n)), map_add (m F n), LinearMap.add_apply, h2, add_zero]
      have e2 : m F n (ι (Q F n) v₁) (a • x + b • y) = b • m F n (ι (Q F n) v₁) y := by
        rw [map_add, map_smul, map_smul, h1, smul_zero, zero_add]
      rw [e1, ← hw, e2, smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [h3, map_smul, Finsupp.smul_apply, sc_repr_m_one_pt _ _ _ K hK1 hK2, smul_zero]
  have hx0 : x ≠ 0 := sc_ne_zero_of_isMaxIsotropic hn0 hxmax
  have hy0 : y ≠ 0 := sc_ne_zero_of_isMaxIsotropic hn0 hymax
  -- coefficients of `a x + b y`
  have hcoef := sc_repr_one_pt (F := F) hn0 (a * α) (b * β)
  rw [← hw] at hcoef
  -- recover `g` on `u₁`, `u₂` from `x`, `y`
  have hgu : ∀ (s : S F n) (t : S F n), m F n ((h * g : Spin F n) : C F n) s = m F n (h : C F n) t →
      m F n (g : C F n) s = t := fun s t hst => sc_m_injective h (by rw [← sc_m_mul, hst])
  rcases sc_model_pure hn x hxmax hmx with ⟨c₁, hc₁⟩ | ⟨c₁, hc₁⟩ <;>
    rcases sc_model_pure hn y hymax hmy with ⟨c₂, hc₂⟩ | ⟨c₂, hc₂⟩
  · -- both on the line of `1`: impossible
    exfalso
    have hc₁0 : c₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₁; exact hx0 hc₁
    have hc₂0 : c₂ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₂; exact hy0 hc₂
    rw [hc₁, hc₂, sc_ann_smul _ hc₁0, sc_ann_smul _ hc₂0, inf_idem] at hxy
    exact sc_ann_ne_bot hn0 sc_isEvenPureSpinor_one.2 hxy
  · -- `x ∈ F 1`, `y ∈ F [pt_X]`: `g` fixes `u₁` and `u₂`
    left
    have e1 := sc_repr_one_pt (F := F) hn0 (a * c₁) (b * c₂)
    rw [hc₁, hc₂] at hcoef
    rw [show a • (c₁ • (1 : S F n)) + b • (c₂ • pt F n) = (a * c₁) • 1 + (b * c₂) • pt F n by
      rw [smul_smul, smul_smul]] at hcoef
    rw [e1.1] at hcoef
    rw [e1.2] at hcoef
    have hc₁α : c₁ = α := mul_left_cancel₀ ha hcoef.1
    have hc₂β : c₂ = β := mul_left_cancel₀ hb hcoef.2
    refine ⟨hgu u₁ u₁ ?_, hgu u₂ u₂ ?_⟩
    · rw [← hxdef, hc₁, hc₁α, hu₁]
    · rw [← hydef, hc₂, hc₂β, hu₂]
  · -- `x ∈ F [pt_X]`, `y ∈ F 1`: `g` exchanges the lines; `n` is even (Mukai pairing)
    right
    have e1 := sc_repr_one_pt (F := F) hn0 (b * c₂) (a * c₁)
    rw [hc₁, hc₂] at hcoef
    rw [show a • (c₁ • pt F n) + b • (c₂ • (1 : S F n)) = (b * c₂) • 1 + (a * c₁) • pt F n by
      rw [smul_smul, smul_smul, add_comm]] at hcoef
    rw [e1.1, e1.2] at hcoef
    -- `(x, y)_S = (u₁, u₂)_S = (h u₁, h u₂)_S`
    have hM1 : mukai F n x y = mukai F n (m F n (h : C F n) u₁) (m F n (h : C F n) u₂) := by
      rw [hxdef, hydef, sc_mukai_m_spin, sc_mukai_m_spin]
    rw [hc₁, hc₂, hu₁, hu₂] at hM1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hM1
    rw [mukai_swap_of_mem_Splus F n 1 (pt F n) sc_one_mem_Splus sc_pt_mem_Splus] at hM1
    have hM0 := sc_mukai_one_pt_ne_zero (F := F) hn0
    have hprod : c₁ * c₂ = α * β := by
      have : (a * c₁) * (b * c₂) = (a * α) * (b * β) := by rw [hcoef.1, hcoef.2]; ring
      have hab : a * b ≠ 0 := mul_ne_zero ha hb
      have : (a * b) * (c₁ * c₂) = (a * b) * (α * β) := by linear_combination this
      exact mul_left_cancel₀ hab this
    have hαβ : α * β ≠ 0 := mul_ne_zero hα hβ
    have hsign : ((-1 : F) ^ n) = 1 := by
      have : (α * β) * ((-1 : F) ^ n * mukai F n 1 (pt F n)) = (α * β) * mukai F n 1 (pt F n) := by
        linear_combination hM1 - ((-1 : F) ^ n * mukai F n 1 (pt F n)) * hprod
      have := mul_left_cancel₀ hαβ this
      exact mul_right_cancel₀ hM0 (by rw [this, one_mul])
    refine ⟨(neg_one_pow_eq_one_iff_even (by norm_num)).mp hsign, ⟨c₁ * β⁻¹, ?_⟩, ⟨c₂ * α⁻¹, ?_⟩⟩
    · apply hgu
      rw [← hxdef, hc₁, map_smul, hu₂, smul_smul, mul_assoc, inv_mul_cancel₀ hβ, mul_one]
    · apply hgu
      rw [← hydef, hc₂, map_smul, hu₁, smul_smul, mul_assoc, inv_mul_cancel₀ hα, mul_one]
  · -- both on the line of `[pt_X]`: impossible
    exfalso
    have hc₁0 : c₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₁; exact hx0 hc₁
    have hc₂0 : c₂ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₂; exact hy0 hc₂
    rw [hc₁, hc₂, sc_ann_smul _ hc₁0, sc_ann_smul _ hc₂0, inf_idem] at hxy
    exact sc_ann_ne_bot hn0 sc_isEvenPureSpinor_pt.2 hxy

theorem sc_mem_fixingSpin_pair_iff (u₁ u₂ : S F n) (g : Spin F n) :
    g ∈ fixingSpin F n (Submodule.span F {u₁, u₂}) ↔
      m F n (g : C F n) u₁ = u₁ ∧ m F n (g : C F n) u₂ = u₂ := by
  constructor
  · intro hg
    exact ⟨hg u₁ (Submodule.subset_span (Set.mem_insert _ _)),
      hg u₂ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨h1, h2⟩ p hp
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
    rw [map_add, map_smul, map_smul, h1, h2]

theorem sc_mem_fixingSpin_singleton_iff (w : S F n) (g : Spin F n) :
    g ∈ fixingSpin F n (Submodule.span F {w}) ↔ m F n (g : C F n) w = w := by
  constructor
  · intro hg
    exact hg w (Submodule.mem_span_singleton_self w)
  · intro h p hp
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hp
    rw [map_smul, h]

/-- A diagonal element: for a basis `a` of `W₁` with dual family `b` in `W₂` and `r ≠ 0`, Igusa's
element `s(r)` for the pair `a₀, b₀` preserves `W₁` and `W₂`, and its restriction to `W₁` (the
matrix `diag(r², 1, …, 1)` in the basis `a`) has determinant `r²`. -/
theorem sc_det_sq_lift (hn : 0 < n) {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) (a : Module.Basis (Fin (2 * n)) F W₁) (b : Fin (2 * n) → V F n)
    (hb : ∀ k, b k ∈ W₂) (hab : ∀ i k, pairing F n (a i) (b k) = if i = k then 1 else 0)
    (r : F) (hr : r ≠ 0) :
    ∃ (g : Spin F n) (hg₁ : ∀ v ∈ W₁, rho F n g v ∈ W₁),
      (g : C F n) = igusaFactor (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (Units.mk0 r hr) ∧
      (∀ v ∈ W₂, rho F n g v ∈ W₂) ∧
      LinearMap.det ((rho F n g : V F n →ₗ[F] V F n).restrict hg₁) = r * r := by
  let i₀ : Fin (2 * n) := ⟨0, by omega⟩
  obtain ⟨g, hgc, hg₁, hg₂, hgv⟩ := sc_diag_lift h₁ h₂ (a i₀).2 (hb i₀)
    (by rw [hab i₀ i₀, ite_eq_left rfl]) r hr
  refine ⟨g, hg₁, hgc, hg₂, ?_⟩
  let d : Fin (2 * n) → F := fun k => if k = i₀ then r ^ 2 else 1
  have hmat : (rho F n g : V F n →ₗ[F] V F n).restrict hg₁ =
      Matrix.toLin a a (Matrix.diagonal d) := by
    apply a.ext
    intro k
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, LinearEquiv.coe_coe, hgv _ (a k).2, Matrix.toLin_self,
      hab k i₀]
    simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, d]
    by_cases hk : k = i₀
    · subst hk
      simp only [ite_true, mul_one, Submodule.coe_smul]
      module
    · simp [hk]
  rw [hmat, LinearMap.det_toLin, Matrix.det_diagonal,
    Finset.prod_ite_eq' Finset.univ i₀ (fun _ => r ^ 2), ite_eq_left (Finset.mem_univ _), sq]

/-- A diagonal element: for `r ≠ 0`, an element of `Spin(V)` preserving `W₁` and `W₂` whose
restriction to `W₁` has determinant `r²` (`sc_det_sq_lift` for some basis). -/
theorem sc_exists_det_sq (hn : 0 < n) {W₁ W₂ : Submodule F (V F n)} (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) (hW : W₁ ⊓ W₂ = ⊥) (r : F) (hr : r ≠ 0) :
    ∃ (g : Spin F n) (hg₁ : ∀ v ∈ W₁, rho F n g v ∈ W₁), (∀ v ∈ W₂, rho F n g v ∈ W₂) ∧
      LinearMap.det ((rho F n g : V F n →ₗ[F] V F n).restrict hg₁) = r * r := by
  let a := Module.finBasisOfFinrankEq F W₁ h₁.2
  obtain ⟨b, hb, hab⟩ := sc_exists_dual h₁ h₂ hW a
  obtain ⟨g, hg₁, -, hg₂, hdet⟩ := sc_det_sq_lift hn h₁ h₂ a b hb hab r hr
  exact ⟨g, hg₁, hg₂, hdet⟩

/-- The core of the image computation in [Igusa, Lemma 1]: given a basis `a` of `W₁ = ker m_{u₁}`,
a dual family `b` in `W₂`, and a subgroup `Γ` of `Spin(V)` containing the lifts
`1 + c a_i b_j` (`i ≠ j`) of the transvections and Igusa's elements `s(r)` for `a₀, b₀`, every
automorphism of `W₁` with square determinant is `ρ(g)|_{W₁}` for some `g ∈ Γ ∩ Spin(V)_{ℓ₁,ℓ₂}`.
(`SL(W₁)` is generated by transvections; `A = (A D⁻¹) D` with `D = diag(r², 1, …, 1)`.) -/
theorem sc_exists_of_isSquare (hn : 0 < n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (a : Module.Basis (Fin (2 * n)) F (ann F n u₁))
    (b : Fin (2 * n) → V F n) (hb : ∀ k, b k ∈ ann F n u₂)
    (hab : ∀ i k, pairing F n (a i) (b k) = if i = k then 1 else 0) (Γ : Subgroup (Spin F n))
    (hT : ∀ i j : Fin (2 * n), i ≠ j → ∀ (c : F) (g : Spin F n),
      (g : C F n) = 1 + ι (Q F n) (c • (a i : V F n)) * ι (Q F n) (b j) → g ∈ Γ)
    (hD : ∀ (r : F) (hr : r ≠ 0) (g : Spin F n),
      (g : C F n) = igusaFactor (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (Units.mk0 r hr) → g ∈ Γ)
    (A : (Module.End F (ann F n u₁))ˣ)
    (hA : IsSquare (LinearMap.det (A : Module.End F (ann F n u₁)))) :
    ∃ g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)),
      (g : Spin F n) ∈ Γ ∧ pairRestrict F n u₁ u₂ g = A := by
  obtain ⟨r, hr⟩ := hA
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hu : IsUnit (LinearMap.det (A : Module.End F (ann F n u₁))) :=
      A.isUnit.map LinearMap.det
    rw [hr, mul_zero] at hu
    exact not_isUnit_zero hu
  set H := (Γ.subgroupOf (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂)).map
    (pairRestrict F n u₁ u₂) with hH
  suffices hAH : A ∈ H by
    obtain ⟨g, hg, hgA⟩ := Subgroup.mem_map.mp hAH
    exact ⟨g, Subgroup.mem_subgroupOf.mp hg, hgA⟩
  -- an element of `Spin(V)` preserving `W₁` and `W₂` lies in `Spin(V)_{ℓ₁,ℓ₂}`
  have hmem : ∀ g : Spin F n, (∀ v ∈ ann F n u₁, rho F n g v ∈ ann F n u₁) →
      (∀ v ∈ ann F n u₂, rho F n g v ∈ ann F n u₂) →
      g ∈ lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ := fun g hg₁ hg₂ =>
    Subgroup.mem_inf.mpr ⟨sc_mem_lineStabilizer h₁ g hg₁, sc_mem_lineStabilizer h₂ g hg₂⟩
  have hmemH : ∀ (g : Spin F n) (hg₁ : ∀ v ∈ ann F n u₁, rho F n g v ∈ ann F n u₁)
      (hg₂ : ∀ v ∈ ann F n u₂, rho F n g v ∈ ann F n u₂), g ∈ Γ →
      pairRestrict F n u₁ u₂ ⟨g, hmem g hg₁ hg₂⟩ ∈ H := fun g hg₁ hg₂ hgΓ =>
    Subgroup.mem_map.mpr ⟨⟨g, hmem g hg₁ hg₂⟩, Subgroup.mem_subgroupOf.mpr hgΓ, rfl⟩
  let φ : Matrix.SpecialLinearGroup (Fin (2 * n)) F →* (Module.End F (ann F n u₁))ˣ :=
    (Units.map (Matrix.toLinAlgEquiv a).toRingEquiv.toMonoidHom).comp
      Matrix.SpecialLinearGroup.toGL
  have hφ : ∀ N, ((φ N : (Module.End F (ann F n u₁))ˣ) : Module.End F (ann F n u₁)) =
      Matrix.toLinAlgEquiv a (N : Matrix (Fin (2 * n)) (Fin (2 * n)) F) := fun N => rfl
  -- transvections lift
  have htr : ∀ (i j : Fin (2 * n)) (hij : i ≠ j) (c : F),
      φ (Matrix.SpecialLinearGroup.transvection hij c) ∈ H := by
    intro i j hij c
    obtain ⟨g, hgc, hg₁, hg₂, hgv⟩ := sc_transvection_lift h₁.2 h₂.2 (a i).2 (hb j)
      (by rw [hab i j, ite_eq_right hij]) c
    convert hmemH g hg₁ hg₂ (hT i j hij c g hgc) using 1
    apply Units.ext
    apply a.ext
    intro k
    apply Subtype.ext
    rw [sc_pairRestrict_apply, hgv _ (a k).2, hφ, Matrix.SpecialLinearGroup.transvection_coe,
      ← Matrix.transvection, sc_toLinAlgEquiv_transvection, hab k j]
    by_cases hkj : k = j
    · simp [hkj]
    · simp [hkj]
  -- the image of `SL_{2n}(F)` lies in `H`
  have hSL : ∀ N, φ N ∈ H := by
    intro N
    have : Nontrivial (Fin (2 * n)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun N => φ N ∈ H) N
      ?_ ?_ ?_
    · intro i j hij c hc
      rw [sc_diag2n_decompose hij c hc]
      simp only [map_mul]
      exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (htr _ _ _ _) (htr _ _ _ _))
        (htr _ _ _ _)) (htr _ _ _ _)) (htr _ _ _ _)) (htr _ _ _ _)
    · exact htr
    · intro A B hA hB
      rw [map_mul]
      exact H.mul_mem hA hB
  -- the diagonal element `diag(r², 1, …, 1)`
  obtain ⟨gD, hgD₁, hgDc, hgD₂, hdetD'⟩ :=
    sc_det_sq_lift hn h₁.2 h₂.2 a b hb hab r hr0
  set D := pairRestrict F n u₁ u₂ ⟨gD, hmem gD hgD₁ hgD₂⟩ with hDdef
  have hDH : D ∈ H := hmemH gD hgD₁ hgD₂ (hD r hr0 gD hgDc)
  have hdetD : LinearMap.det (D : Module.End F (ann F n u₁)) = r * r := hdetD'
  -- `A = A₁ D` with `A₁ = A D⁻¹ ∈ SL(W₁)`
  set A₁ := A * D⁻¹ with hA₁
  have hdetA₁ : LinearMap.det (A₁ : Module.End F (ann F n u₁)) = 1 := by
    have h1 : LinearMap.det (A₁ : Module.End F (ann F n u₁)) *
        LinearMap.det (D : Module.End F (ann F n u₁)) =
          LinearMap.det (A : Module.End F (ann F n u₁)) := by
      rw [← map_mul, ← Units.val_mul, hA₁, inv_mul_cancel_right]
    rw [hdetD, ← hr] at h1
    have hA0 : LinearMap.det (A : Module.End F (ann F n u₁)) ≠ 0 := by
      rw [hr]; exact mul_ne_zero hr0 hr0
    exact (mul_eq_right₀ hA0).mp h1
  let M₁ : Matrix.SpecialLinearGroup (Fin (2 * n)) F :=
    ⟨LinearMap.toMatrix a a (A₁ : Module.End F (ann F n u₁)),
      by rw [LinearMap.det_toMatrix, hdetA₁]⟩
  have hM₁ : φ M₁ = A₁ := by
    apply Units.ext
    rw [hφ]
    apply a.ext
    intro k
    rw [Matrix.toLinAlgEquiv_self]
    simp only [M₁, LinearMap.toMatrix_apply]
    exact a.sum_repr _
  have hA₁H : A₁ ∈ H := hM₁ ▸ hSL M₁
  have hA : A = A₁ * D := by rw [hA₁, inv_mul_cancel_right]
  rw [hA]
  exact H.mul_mem hA₁H hDH

theorem sc_neg_one_mem (hn : 0 < n) : (-1 : C F n) ∈ spinGroup (Q F n) := by
  apply neg_one_mem_spinGroup
  intro h
  have := congrArg (fun q : QuadraticForm F (V F n) =>
    q (f F n ⟨0, by omega⟩, e F n ⟨0, by omega⟩)) h
  simp [e, f] at this

/-- The character `χ₁` of `Spin(V)_{ℓ₁,ℓ₂}` takes every value `ν ∈ F^×`: some element acts on
`u₁` by `ν` and on `u₂` by `ν⁻¹` (by `sc_exists_det_sq` and `χ₁² = det₁`, `χ₁ χ₂ = 1`, up to
`-1`). -/
theorem sc_exists_scalar (hn : 0 < n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (ν : F) (hν : ν ≠ 0) :
    ∃ d : Spin F n, m F n (d : C F n) u₁ = ν • u₁ ∧ m F n (d : C F n) u₂ = ν⁻¹ • u₂ := by
  obtain ⟨g, hg₁, hg₂, hdet⟩ := sc_exists_det_sq hn h₁.2 h₂.2 hW ν hν
  obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 F n u₁ h₁ g hg₁
  obtain ⟨c', hc', -⟩ := chevalley_III_3_2_III_4_5 F n u₂ h₂ g hg₂
  rw [hdet, ← sq] at hc2
  have hM : mukai F n u₁ u₂ ≠ 0 := fun h => (chevalley_III_2_4 F n hn u₁ u₂ h₁ h₂).mp h hW
  have hcc' : c * c' = 1 := by
    have h := sc_mukai_m_spin g u₁ u₂
    rw [hc, hc'] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ hM (by linear_combination h)
  have hc'eq : c' = c⁻¹ := eq_inv_of_mul_eq_one_right hcc'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc2 with hcν | hcν
  · exact ⟨g, by rw [hc, hcν], by rw [hc', hc'eq, hcν]⟩
  · refine ⟨⟨-1, sc_neg_one_mem hn⟩ * g, ?_, ?_⟩
    · rw [sc_m_mul, hc, hcν]
      simp
    · rw [sc_m_mul, hc', hc'eq, hcν]
      simp [inv_neg]

/-- `u₁` and `u₂` are linearly independent: `c u₁ = c' u₂` forces `c = 0`. -/
theorem sc_eq_zero_of_smul_eq (hn : 0 < n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) {c c' : F}
    (h : c • u₁ = c' • u₂) : c = 0 := by
  by_contra hc
  have hc' : c' ≠ 0 := by
    rintro rfl
    rw [zero_smul, smul_eq_zero, or_iff_right hc] at h
    exact sc_ne_zero_of_isMaxIsotropic hn h₁.2 h
  have := congrArg (ann F n) h
  rw [sc_ann_smul _ hc, sc_ann_smul _ hc'] at this
  rw [this, inf_idem] at hW
  exact sc_ann_ne_bot hn h₂.2 hW

/-- For `n` even, an element of `Spin(V)` exchanging the lines of `u₁` and `u₂` and fixing
`a u₁ + b u₂` ([Chevalley, §3.3, Lemma 1] for the pair `(W₂, W₁)`, corrected by `sc_exists_scalar`).
-/
theorem sc_exists_swap (hn : 0 < n) (heven : Even n) (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ∃ t : Spin F n, m F n (t : C F n) u₁ = (b / a) • u₂ ∧ m F n (t : C F n) u₂ = (a / b) • u₁ := by
  have hW' : ann F n u₂ ⊓ ann F n u₁ = ⊥ := by rw [inf_comm]; exact hW
  obtain ⟨s, hs₁, hs₂⟩ := chevalley_sec3_3_lemma1 F n u₁ u₂ u₂ u₁ h₁ h₂ h₂ h₁ hW hW'
  have hu₁0 : u₁ ≠ 0 := sc_ne_zero_of_isMaxIsotropic hn h₁.2
  have hu₂0 : u₂ ≠ 0 := sc_ne_zero_of_isMaxIsotropic hn h₂.2
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp
    (chevalley_III_1_4_unique F n u₂ (m F n (s : C F n) u₁) hu₂0 h₂.2 (by rw [ann_m_spin, hs₁]))
  obtain ⟨κ', hκ'⟩ := Submodule.mem_span_singleton.mp
    (chevalley_III_1_4_unique F n u₁ (m F n (s : C F n) u₂) hu₁0 h₁.2 (by rw [ann_m_spin, hs₂]))
  have hM : mukai F n u₁ u₂ ≠ 0 := fun h => (chevalley_III_2_4 F n hn u₁ u₂ h₁ h₂).mp h hW
  have hkk : κ * κ' = 1 := by
    have h := sc_mukai_m_spin s u₁ u₂
    rw [← hκ, ← hκ'] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mukai_swap_of_mem_Splus F n u₁ u₂ h₁.1 h₂.1, heven.neg_one_pow, one_mul] at h
    exact mul_right_cancel₀ hM (by linear_combination h)
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hkk
  have hκ'eq : κ' = κ⁻¹ := eq_inv_of_mul_eq_one_right hkk
  have hν : b / a / κ ≠ 0 := div_ne_zero (div_ne_zero hb ha) hκ0
  obtain ⟨d, hd₁, hd₂⟩ := sc_exists_scalar hn u₁ u₂ h₁ h₂ hW (b / a / κ) hν
  refine ⟨s * d, ?_, ?_⟩
  · rw [sc_m_mul, hd₁, map_smul, ← hκ, smul_smul]
    congr 1
    field_simp
  · rw [sc_m_mul, hd₂, map_smul, ← hκ', smul_smul, hκ'eq]
    congr 1
    field_simp

end SCLemma2

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Igusa, Lemma 1]** (kernel), as used in §2.2: for even pure spinors `u₁, u₂` with
`W₁ ∩ W₂ = 0`, the kernel of `Spin(V_F)_{ℓ₁,ℓ₂} → GL(W₁)` is `{±1}`. -/
theorem igusa_lemma1_ker (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥)
    (g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n))) :
    pairRestrict F n u₁ u₂ g = 1 ↔
      ((g : Spin F n) : C F n) = 1 ∨ ((g : Spin F n) : C F n) = -1 := by
  rw [← sc_rho_eq_id_iff]
  have hC := sc_isCompl h₁.2 h₂.2 hW
  have hg₂ : (g : Spin F n) ∈ lineStabilizer F n u₂ := (Subgroup.mem_inf.mp g.2).2
  constructor
  · intro h
    -- `ρ(g) = 1` on `W₁`, hence on `W₂ ≅ W₁*` (isometry), hence on `V = W₁ ⊕ W₂`.
    have h1 : ∀ x ∈ ann F n u₁, rho F n g x = x := by
      intro x hx
      have := congrArg (fun A : (Module.End F (ann F n u₁))ˣ =>
        (((A : Module.End F (ann F n u₁)) ⟨x, hx⟩ : ann F n u₁) : V F n)) h
      simpa only [sc_pairRestrict_apply, Units.val_one, Module.End.one_apply] using this
    have h2 : ∀ y ∈ ann F n u₂, rho F n g y = y := by
      intro y hy
      rw [← sub_eq_zero]
      apply sc_eq_zero_of_mem_of_orth hC h₂.2
        (Submodule.sub_mem _ (rho_mem_ann_of_mem_lineStabilizer F n u₂ g hg₂ y hy) hy)
      intro x hx
      rw [map_sub, ← sc_pairing_rho (g : Spin F n) x y, h1 x hx, sub_self]
    intro v
    obtain ⟨x, hx, w, hw, rfl⟩ :=
      Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, h1 x hx, h2 w hw]
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [sc_pairRestrict_apply, h]
    rfl

/-- **[Igusa, Lemma 1]** (image), in the form valid for `F`-points: for even pure spinors `u₁, u₂`
with `W₁ ∩ W₂ = 0`, the image of `Spin(V_F)_{ℓ₁,ℓ₂} → GL(W₁)` consists of the automorphisms of `W₁`
with square determinant. Over an algebraically closed field this is Igusa's
`Spin(V)_{ℓ₁,ℓ₂}/{±1} ≅ GL(W₁)`; the paper uses the latter for `K`-points, where it is false (see
`WeilClasses.KSecant.range_restrictW₁`). -/
theorem igusa_lemma1_range (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) :
    ((pairRestrict F n u₁ u₂).range : Set (Module.End F (ann F n u₁))ˣ) =
      {A : (Module.End F (ann F n u₁))ˣ |
        IsSquare (LinearMap.det (A : Module.End F (ann F n u₁)))} := by
  ext A
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_ofPred_eq]
  constructor
  · -- `det₁ = χ₁²` ([Chevalley, III.3.2/III.4.5]).
    rintro ⟨g, rfl⟩
    obtain ⟨c, -, hc2⟩ := chevalley_III_3_2_III_4_5 F n u₁ h₁ g
      (rho_mem_ann_of_mem_lineStabilizer F n u₁ g (Subgroup.mem_inf.mp g.2).1)
    refine ⟨c, ?_⟩
    rw [← sq, hc2]
    rfl
  · intro hA
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: `W₁ = 0` and `GL(W₁)` is trivial.
      have : Subsingleton (V F n) := sc_V_subsingleton hn
      have : Subsingleton (Module.End F (ann F n u₁)) :=
        ⟨fun f f' => LinearMap.ext fun x => Subtype.ext (Subsingleton.elim _ _)⟩
      exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
    -- `n > 0`: generate by lifts of transvections and of `diag(r², 1, …, 1)`.
    let a := Module.finBasisOfFinrankEq F (ann F n u₁) h₁.2.2
    obtain ⟨b, hb, hab⟩ := sc_exists_dual h₁.2 h₂.2 hW a
    obtain ⟨g, -, hg⟩ := sc_exists_of_isSquare hn h₁ h₂ a b hb hab ⊤
      (fun _ _ _ _ _ _ => Subgroup.mem_top _) (fun _ _ _ _ => Subgroup.mem_top _) A hA
    exact ⟨g, hg⟩

/-- **[Igusa, Lemma 1]** (the action on `W₂`), as used in §2.2: an element `g` of
`Spin(V_F)_{ℓ₁,ℓ₂}` acts on `W₂ ≅ W₁*` by the inverse transpose of its action on `W₁`, i.e.
`(ρ(g) x, ρ(g) y)_V = (x, y)_V` for `x ∈ W₁`, `y ∈ W₂` (this is the isometry property of `ρ(g)`
restricted to `W₁ × W₂`, which identifies `W₂` with `W₁*`). -/
theorem igusa_lemma1_dual (u₁ u₂ : S F n)
    (g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)))
    (x y : V F n) (hx : x ∈ ann F n u₁) (hy : y ∈ ann F n u₂) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y :=
  sc_pairing_rho _ x y

/-- **[Igusa, Lemma 1]** (proof; the second displayed formula for `φ(sᵢ(λ))` in [Igusa, §2]; see
also [Chevalley, III.3.2]), as used in §2.2 for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`: if `g ∈ Spin(V_F)` stabilizes
the line of a nonzero even pure spinor `u`, `g u = c u`, then `c² = det(ρ(g)|_{ker m_u})`. (For
`n = 0`, `u = 0` is pure and `c` is arbitrary, hence `u ≠ 0`.) -/
theorem igusa_lemma1_sq (u : S F n) (hu : IsEvenPureSpinor F n u) (hu0 : u ≠ 0) (g : Spin F n)
    (hg : g ∈ lineStabilizer F n u) (c : F) (hc : m F n (g : C F n) u = c • u) :
    c ^ 2 = LinearMap.det (annRestrict F n u ⟨g, hg⟩) := by
  obtain ⟨c', hc', hc'2⟩ := chevalley_III_3_2_III_4_5 F n u hu g
    (rho_mem_ann_of_mem_lineStabilizer F n u g hg)
  have : c = c' := smul_left_injective F hu0 (hc.symm.trans hc')
  rw [this, hc'2]
  rfl

/-- **[Igusa, Lemma 2]** and the remark following it, `n` odd, as used in Remark 2.2.3: for `n ≥ 3`
odd, even pure spinors `u₁, u₂` with `W₁ ∩ W₂ = 0` and `a, b ≠ 0`, the stabilizer of
`w = a u₁ + b u₂` in `Spin(V_F)` is the pointwise stabilizer of `u₁` and `u₂`. -/
theorem igusa_lemma2_stab_odd (hn : 3 ≤ n) (hodd : Odd n) (u₁ u₂ : S F n)
    (h₁ : IsEvenPureSpinor F n u₁) (h₂ : IsEvenPureSpinor F n u₂)
    (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) =
      fixingSpin F n (Submodule.span F {u₁, u₂}) := by
  ext g
  rw [sc_mem_fixingSpin_singleton_iff, sc_mem_fixingSpin_pair_iff]
  constructor
  · intro hg
    rcases sc_stab_classify hn u₁ u₂ h₁ h₂ hW a b ha hb g hg with h | ⟨heven, -, -⟩
    · exact h
    · exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
  · rintro ⟨h1, h2⟩
    rw [map_add, map_smul, map_smul, h1, h2]

/-- **[Igusa, Lemma 2]** and the remark following it, `n` even, as used in Remark 2.2.3: for
`n ≥ 3` even, the stabilizer of `w = a u₁ + b u₂` has two connected components, the identity
component being the pointwise stabilizer of `u₁` and `u₂`. For `F`-points: the pointwise stabilizer
of `u₁, u₂` is a normal subgroup of index `2` of the stabilizer of `w` (an element of `Spin(V_F)`
exchanging the lines of `u₁` and `u₂` and fixing `w` exists for `n` even). -/
theorem igusa_lemma2_stab_even (hn : 3 ≤ n) (heven : Even n) (u₁ u₂ : S F n)
    (h₁ : IsEvenPureSpinor F n u₁) (h₂ : IsEvenPureSpinor F n u₂)
    (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    fixingSpin F n (Submodule.span F {u₁, u₂}) ≤
        fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) ∧
      ((fixingSpin F n (Submodule.span F {u₁, u₂})).subgroupOf
          (fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}))).Normal ∧
      (fixingSpin F n (Submodule.span F {u₁, u₂})).relIndex
          (fixingSpin F n (Submodule.span F {a • u₁ + b • u₂})) = 2 := by
  have hn0 : 0 < n := by omega
  have hHK : fixingSpin F n (Submodule.span F {u₁, u₂}) ≤
      fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) := fun g hg => by
    rw [sc_mem_fixingSpin_pair_iff] at hg
    rw [sc_mem_fixingSpin_singleton_iff, map_add, map_smul, map_smul, hg.1, hg.2]
  obtain ⟨t, ht₁, ht₂⟩ := sc_exists_swap hn0 heven u₁ u₂ h₁ h₂ hW a b ha hb
  have htK : t ∈ fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) := by
    rw [sc_mem_fixingSpin_singleton_iff, map_add, map_smul, map_smul, ht₁, ht₂, smul_smul,
      smul_smul, mul_div_cancel₀ _ ha, mul_div_cancel₀ _ hb, add_comm]
  -- `u₁` is not on the line of `u₂`
  have hind : ∀ c : F, u₁ ≠ c • u₂ := fun c h => by
    have := sc_eq_zero_of_smul_eq hn0 h₁ h₂ hW (c := 1) (c' := c) (by rw [one_smul]; exact h)
    exact one_ne_zero this
  have hrel : (fixingSpin F n (Submodule.span F {u₁, u₂})).relIndex
      (fixingSpin F n (Submodule.span F {a • u₁ + b • u₂})) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, htK, fun g hg => ?_⟩
    rcases sc_stab_classify hn u₁ u₂ h₁ h₂ hW a b ha hb g
        ((sc_mem_fixingSpin_singleton_iff _ g).mp hg) with hfix | ⟨-, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    · -- `g` fixes `u₁, u₂`; then `g t` exchanges the lines
      refine Or.inr ⟨(sc_mem_fixingSpin_pair_iff _ _ _).mpr hfix, fun hgt => ?_⟩
      rw [sc_mem_fixingSpin_pair_iff, sc_m_mul, ht₁, map_smul, hfix.2] at hgt
      exact hind (b / a) hgt.1.symm
    · -- `g` exchanges the lines; then `g t` fixes `u₁, u₂`
      refine Or.inl ⟨?_, fun hgH => ?_⟩
      · rcases sc_stab_classify hn u₁ u₂ h₁ h₂ hW a b ha hb (g * t)
            ((sc_mem_fixingSpin_singleton_iff _ _).mp (Subgroup.mul_mem _ hg htK)) with
          hfix' | ⟨-, ⟨d₁, hd₁⟩, -⟩
        · exact (sc_mem_fixingSpin_pair_iff _ _ _).mpr hfix'
        · exfalso
          rw [sc_m_mul, ht₁, map_smul, hc₂, smul_smul] at hd₁
          have hc₂0 : c₂ ≠ 0 := by
            rintro rfl
            rw [zero_smul] at hc₂
            exact sc_ne_zero_of_isMaxIsotropic hn0 h₂.2 (sc_m_injective g (by rw [hc₂, map_zero]))
          have := sc_eq_zero_of_smul_eq hn0 h₁ h₂ hW hd₁
          exact mul_ne_zero (div_ne_zero hb ha) hc₂0 this
      · rw [sc_mem_fixingSpin_pair_iff] at hgH
        exact hind c₁ (hgH.1.symm.trans hc₁)
  exact ⟨hHK, Subgroup.normal_of_index_eq_two hrel, hrel⟩

/-! ## Helpers (prover SC): generation of `Spin(V)_{ℓ₁,ℓ₂}` by the lifts -/

/-- A subgroup `Γ` of `Spin(V)` containing `-1`, the lifts `1 + c a_i b_j` (`i ≠ j`) of the
transvections and Igusa's elements `s(r)` for `a₀, b₀` (a basis `a` of `W₁` with dual family `b`
in `W₂`) contains `Spin(V)_{ℓ₁,ℓ₂}` ([Igusa, Lemma 1]: image and kernel). -/
theorem sc_le_of_lifts {F : Type*} [Field F] [CharZero F] {n : ℕ} (hn : 0 < n) {u₁ u₂ : S F n}
    (h₁ : IsEvenPureSpinor F n u₁) (h₂ : IsEvenPureSpinor F n u₂)
    (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a : Module.Basis (Fin (2 * n)) F (ann F n u₁))
    (b : Fin (2 * n) → V F n) (hb : ∀ k, b k ∈ ann F n u₂)
    (hab : ∀ i k, pairing F n (a i) (b k) = if i = k then 1 else 0) (Γ : Subgroup (Spin F n))
    (hT : ∀ i j : Fin (2 * n), i ≠ j → ∀ (c : F) (g : Spin F n),
      (g : C F n) = 1 + ι (Q F n) (c • (a i : V F n)) * ι (Q F n) (b j) → g ∈ Γ)
    (hD : ∀ (r : F) (hr : r ≠ 0) (g : Spin F n),
      (g : C F n) = igusaFactor (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (Units.mk0 r hr) → g ∈ Γ)
    (hneg : ∀ g : Spin F n, (g : C F n) = -1 → g ∈ Γ) :
    lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ ≤ Γ := by
  intro g hg
  let g' : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)) := ⟨g, hg⟩
  obtain ⟨c, -, hc2⟩ := chevalley_III_3_2_III_4_5 F n u₁ h₁ g
    (rho_mem_ann_of_mem_lineStabilizer F n u₁ g (Subgroup.mem_inf.mp hg).1)
  obtain ⟨k, hkΓ, hk⟩ := sc_exists_of_isSquare hn h₁ h₂ a b hb hab Γ hT hD
    (pairRestrict F n u₁ u₂ g') ⟨c, by rw [← sq, hc2]; rfl⟩
  have hker : pairRestrict F n u₁ u₂ (k⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, hk, inv_mul_cancel]
  have hg_eq : g = (k : Spin F n) * ((k⁻¹ * g' : (lineStabilizer F n u₁ ⊓
      lineStabilizer F n u₂ : Subgroup (Spin F n))) : Spin F n) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hg_eq]
  refine Γ.mul_mem hkΓ ?_
  rcases (igusa_lemma1_ker F n u₁ u₂ h₁ h₂ hW (k⁻¹ * g')).mp hker with h | h
  · have : ((k⁻¹ * g' : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ :
        Subgroup (Spin F n))) : Spin F n) = 1 := Subtype.ext h
    rw [this]
    exact Γ.one_mem
  · exact hneg _ h

end WeilClasses
