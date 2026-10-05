module

public import WeilClasses.Igusa.Defs
public import WeilClasses.External.Igusa.Sec10
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import WeilClasses.External.Chevalley.Sec2_2
public import WeilClasses.External.Igusa.Sec2_2
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.AlgebraicClosure
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# The secant to the spinor variety through a point off the Igusa quartic (paper §10.1)

Here `X` is an abelian threefold (`n = 3`), and `J` is the Igusa quartic (10.1.1)
(`WeilClasses.J`).

* **Lemma 10.1.1**: for `[w] ∈ ℙ(S⁺_ℂ) ∖ V(J)` there is a unique plane `P_w ∋ w` whose line is a
  secant of the even spinor variety, meeting it in two points with transversal maximal isotropic
  subspaces `W₁, W₂` (`lemma10_1_1`); `ρ` maps `Spin(V_ℂ)_w` isomorphically onto the image of the
  embedding `e : SL(W₁) → SO(V_ℂ)` (10.1.2) (`lemma10_1_1_stabilizer`); if `w` is rational, `P_w` is
  defined over `ℚ` (`lemma10_1_1_rational`).
* **Remark 10.1.2**: (1) the level sets of `J` are single `Spin(V_F)`-orbits
  (`remark10_1_2_orbit`, for `d ≠ 0`: the printed `d ∈ F` fails for `d = 0`), and
  `J(1 + e₁₄^* + e₂₅^* + d e₃₆^*) = d` (`remark10_1_2_value`); (2) the secant `ℙ(P_w)` meets `V(J)`
  exactly at its two points on the spinor variety, each with multiplicity `2`
  (`remark10_1_2_secant`), because the even spinor variety lies in the singular locus of `V(J)`
  (`remark10_1_2_singular`); the length-two subscheme `ℙ(P_w) ∩ (spinor variety)` is defined over
  `ℚ` when `w` is rational (`remark10_1_2_rational`).
* Unnumbered claims of the proofs: `J(1 + c[pt_X]) = -c²/4` (`J_one_add_smul_pt`);
  `ker m_1 = H¹(X̂)`, `ker m_{[pt_X]} = H¹(X)` (`ann_one`, `ann_pt`); `span{1, [pt_X]}` is a
  transversal secant (`isTransversalSecant_one_pt`).

Indices are 0-based: `eStar F 0 3` is the paper's `e₁₄^*`.

**Conditional results.** The proofs of Lemma 10.1.1 and of Remark 10.1.2(2) (rationality, which
cites Lemma 10.1.1) reduce to the normal form `1 + c [pt_X]` of [Igusa, Prop. 3], and
Remark 10.1.2(1) quotes Igusa's orbit statement over subfields of `ℂ`. Both parts of Igusa's
proposition are assumed, as the named hypotheses `IgusaProp3NormalForm` and
`IgusaProp3OrbitSubfield` of the results that use them (see `WeilClasses/External/Igusa/README.md`;
over subfields of `ℂ` the first follows from the second, `s10_normalForm_of_orbitSubfield`). The
other results of this file are unconditional.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prover P14, prefix `s10_`): coordinates, the pure spinors `1` and `[pt_X]` -/

section S10Coords

set_option linter.unusedSectionVars false

variable (F : Type*) [Field F] [CharZero F]

theorem s10_pair_ne_empty (i j : Fin 6) : ({i, j} : Finset (Fin 6)) ≠ ∅ :=
  Finset.insert_ne_empty _ _

theorem s10_pair_ne_univ (i j : Fin 6) : ({i, j} : Finset (Fin 6)) ≠ Finset.univ := by
  intro h
  have h1 := congrArg Finset.card h
  have h2 : ({i, j} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem s10_compl_pair_ne_empty (i j : Fin 6) : ({i, j}ᶜ : Finset (Fin 6)) ≠ ∅ := by
  rw [Ne, Finset.compl_eq_empty_iff]
  exact s10_pair_ne_univ i j

theorem s10_compl_pair_ne_univ (i j : Fin 6) : ({i, j}ᶜ : Finset (Fin 6)) ≠ Finset.univ := by
  rw [Ne, Finset.compl_eq_univ_iff]
  exact s10_pair_ne_empty i j

theorem s10_card_compl_pair {i j : Fin 6} (hij : i ≠ j) : ({i, j}ᶜ : Finset (Fin 6)).card = 4 := by
  rw [Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]

theorem s10_xMat_eq_zero {x : S F 3} (h : ∀ i j, xCoord F x i j = 0) : xMat F x = 0 := by
  ext i j
  simp [xMat, h]

theorem s10_yMat_eq_zero {x : S F 3} (h : ∀ i j, yCoord F x i j = 0) : yMat F x = 0 := by
  ext i j
  simp [yMat, h]

/-- `J` of a class with no `H²`- and no `H⁴`-component: `J(x) = -¼ (x₀ y₀)²`. -/
theorem s10_J_of_coords_zero {x : S F 3} (hx : ∀ i j, xCoord F x i j = 0)
    (hy : ∀ i j, yCoord F x i j = 0) : J F x = -(1 / 4) * (x0 F x * y0 F x) ^ 2 := by
  simp only [J, s10_xMat_eq_zero F hx, s10_yMat_eq_zero F hy, s10_pf6_zero, s10_crossOut_zero,
    s10_pf4_zero, hx, hy]
  simp

/-- `J` of a class with no `H²`-component and no `H⁶`-component: `J(x) = x₀ Pf((y_ij))`. -/
theorem s10_J_of_xCoord_zero {x : S F 3} (hx : ∀ i j, xCoord F x i j = 0) (hy0 : y0 F x = 0) :
    J F x = x0 F x * pf6 (yMat F x) := by
  simp only [J, s10_xMat_eq_zero F hx, s10_pf6_zero, s10_crossOut_zero, s10_pf4_zero, hx, hy0]
  simp

theorem s10_repr_pt (K : Finset (Fin 6)) :
    (basisS F 3).repr (pt F 3) K = if K = Finset.univ then 1 else 0 := by
  rw [pt, s10_repr_basisS]
  simp only [eq_comm]

/-- `J(a + b [pt_X]) = -¼ (a b)²`. -/
theorem s10_J_add_smul_pt (a b : F) : J F (a • 1 + b • pt F 3) = -(1 / 4) * (a * b) ^ 2 := by
  have hr : ∀ K, (basisS F 3).repr (a • 1 + b • pt F 3) K =
      (if K = ∅ then a else 0) + (if K = Finset.univ then b else 0) := by
    intro K
    rw [map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      s10_repr_one, s10_repr_pt]
    split_ifs <;> simp
  have hx : ∀ i j, xCoord F (a • 1 + b • pt F 3) i j = 0 := by
    intro i j
    rw [xCoord, hr, ite_eq_right (s10_pair_ne_empty i j), ite_eq_right (s10_pair_ne_univ i j), add_zero]
  have hy : ∀ i j, yCoord F (a • 1 + b • pt F 3) i j = 0 := by
    intro i j
    rw [yCoord, hr, ite_eq_right (s10_compl_pair_ne_empty i j), ite_eq_right (s10_compl_pair_ne_univ i j),
      add_zero, mul_zero]
  rw [s10_J_of_coords_zero F hx hy, x0, y0, hr, hr, ite_eq_left rfl, ite_eq_left rfl,
    ite_eq_right (Finset.univ_nonempty.ne_empty.symm), ite_eq_right Finset.univ_nonempty.ne_empty]
  ring

theorem s10_eStar_03 : eStar F 0 3 = basisS F 3 ({0, 3}ᶜ) := by
  rw [eStar]; norm_num

theorem s10_eStar_14 : eStar F 1 4 = basisS F 3 ({1, 4}ᶜ) := by
  rw [eStar]; norm_num

theorem s10_eStar_25 : eStar F 2 5 = basisS F 3 ({2, 5}ᶜ) := by
  rw [eStar]; norm_num

/-- `J(a + p e₁₄^* + q e₂₅^* + r e₃₆^*) = a p q r` (0-based indices). -/
theorem s10_J_diag (a p q r : F) :
    J F (a • 1 + p • eStar F 0 3 + q • eStar F 1 4 + r • eStar F 2 5) = a * p * q * r := by
  set x := a • 1 + p • eStar F 0 3 + q • eStar F 1 4 + r • eStar F 2 5 with hxdef
  have hr : ∀ K, (basisS F 3).repr x K =
      (if K = ∅ then a else 0) + (if K = {0, 3}ᶜ then p else 0) + (if K = {1, 4}ᶜ then q else 0) +
        (if K = {2, 5}ᶜ then r else 0) := by
    intro K
    rw [hxdef, s10_eStar_03, s10_eStar_14, s10_eStar_25]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s10_repr_one,
      s10_repr_basisS, smul_eq_mul]
    simp only [eq_comm (b := K)]
    split_ifs <;> simp
  have hcard : ∀ i j : Fin 6, ∀ k l : Fin 6, k ≠ l → ({i, j} : Finset (Fin 6)) ≠ {k, l}ᶜ := by
    intro i j k l hkl h
    have h1 := congrArg Finset.card h
    rw [s10_card_compl_pair hkl] at h1
    have h2 : ({i, j} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
    omega
  have hx : ∀ i j, xCoord F x i j = 0 := by
    intro i j
    rw [xCoord, hr, ite_eq_right (s10_pair_ne_empty i j), ite_eq_right (hcard i j 0 3 (by decide)),
      ite_eq_right (hcard i j 1 4 (by decide)), ite_eq_right (hcard i j 2 5 (by decide))]
    simp
  have hy0 : y0 F x = 0 := by
    rw [y0, hr, ite_eq_right (Finset.univ_nonempty.ne_empty), ite_eq_right (s10_compl_pair_ne_univ 0 3).symm,
      ite_eq_right (s10_compl_pair_ne_univ 1 4).symm, ite_eq_right (s10_compl_pair_ne_univ 2 5).symm]
    simp
  have hx0 : x0 F x = a := by
    rw [x0, hr, ite_eq_left rfl, ite_eq_right (s10_compl_pair_ne_empty 0 3).symm,
      ite_eq_right (s10_compl_pair_ne_empty 1 4).symm, ite_eq_right (s10_compl_pair_ne_empty 2 5).symm]
    simp
  rw [s10_J_of_xCoord_zero F hx hy0, hx0, s10_pf6_expand]
  simp (config := {decide := true}) only [yMat, Matrix.of_apply, yCoord, hr]
  norm_num
  ring

end S10Coords

section S10Pure

set_option linter.unusedSectionVars false

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `m_{(θ, w)}(s) = w ∧ s + θ ⌋ s` (2.1.2). -/
theorem s10_mOf_apply (s : S F n) (v : V F n) :
    mOf F n s v = ExteriorAlgebra.ι F v.2 * s + D F n v.1 s := by
  simp only [mOf, LinearMap.comp_apply, AlgHom.toLinearMap_apply, m, CliffordAlgebra.lift_ι_apply,
    LinearMap.applyₗ_apply_apply, cliffordOp, L, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.mul_apply']

theorem s10_m_ι_apply (v : V F n) (s : S F n) :
    m F n (ι (Q F n) v) s = ExteriorAlgebra.ι F v.2 * s + D F n v.1 s :=
  s10_mOf_apply F n s v

theorem s10_finrank_H1 : Module.finrank F (H1 F n) = 2 * n := Module.finrank_fin_fun F

theorem s10_pt_mem : pt F n ∈ ⋀[F]^(2 * n) (H1 F n) := by
  have h := ExteriorAlgebra.basis_apply_ofCard (b := Pi.basisFun F (Fin (2 * n)))
    (show (Finset.univ : Finset (Fin (2 * n))).card = 2 * n by simp)
  rw [pt, basisS, h]
  exact ExteriorAlgebra.ιMulti_range F _ ⟨_, rfl⟩

theorem s10_ι_mul_pt (w : H1 F n) : ExteriorAlgebra.ι F w * pt F n = 0 := by
  have hι : ExteriorAlgebra.ι F w ∈ ⋀[F]^1 (H1 F n) := by
    rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ w
  have h := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[F]^i (H1 F n)) hι (s10_pt_mem F n)
  have hbot : ⋀[F]^(1 + 2 * n) (H1 F n) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [exteriorPower.finrank_eq, s10_finrank_H1]
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [hbot] at h
  exact (Submodule.mem_bot F).mp h

theorem s10_pt_ne_zero : pt F n ≠ 0 := (basisS F n).ne_zero _

theorem s10_D_pt_eq_zero_iff (θ : Module.Dual F (H1 F n)) : D F n θ (pt F n) = 0 ↔ θ = 0 := by
  refine ⟨fun h => LinearMap.ext fun w => ?_, fun h => by rw [h, map_zero, LinearMap.zero_apply]⟩
  have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w (pt F n)
  have h2 : ExteriorAlgebra.ι F w * pt F n = 0 := s10_ι_mul_pt F n w
  change contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ (pt F n) = 0 at h
  rw [show CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w * pt F n = 0 from h2, map_zero, h,
    mul_zero, sub_zero] at h1
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h1.symm).resolve_right (s10_pt_ne_zero F n)

theorem s10_one_mem_Splus : (1 : S F n) ∈ Splus F n :=
  CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.one_le.mp le_rfl)

theorem s10_pt_mem_Splus : pt F n ∈ Splus F n := by
  have h := s10_pt_mem F n
  rw [ExteriorAlgebra.exteriorPower] at h
  exact Submodule.mem_iSup_of_mem (⟨2 * n, by rw [Nat.cast_mul]; exact mul_eq_zero_of_left rfl _⟩ :
    {j : ℕ // (j : ZMod 2) = 0}) h

theorem s10_top_prod_bot :
    (⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)) =
      LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) := by
  ext v
  simp only [Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, true_and,
    LinearMap.mem_range, LinearMap.inl_apply]
  constructor
  · intro h; exact ⟨v.1, Prod.ext rfl h.symm⟩
  · rintro ⟨θ, rfl⟩; rfl

theorem s10_bot_prod_top :
    (⊥ : Submodule F (Module.Dual F (H1 F n))).prod (⊤ : Submodule F (H1 F n)) =
      LinearMap.range (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) := by
  ext v
  simp only [Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, and_true,
    LinearMap.mem_range, LinearMap.inr_apply]
  constructor
  · intro h; exact ⟨v.2, Prod.ext h.symm rfl⟩
  · rintro ⟨w, rfl⟩; rfl

theorem s10_finrank_top_prod_bot :
    Module.finrank F ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)))
      = 2 * n := by
  rw [s10_top_prod_bot, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    Subspace.dual_finrank_eq, s10_finrank_H1]

theorem s10_finrank_bot_prod_top :
    Module.finrank F ((⊥ : Submodule F (Module.Dual F (H1 F n))).prod (⊤ : Submodule F (H1 F n)))
      = 2 * n := by
  rw [s10_bot_prod_top, LinearMap.finrank_range_of_inj LinearMap.inr_injective, s10_finrank_H1]

end S10Pure

/-! ## Unnumbered claims used in the proofs of Lemmas 10.1.1 and 10.2.1 -/

/-- (Proof of Lemma 10.1.1, l. 9705: `J(1 + d[pt_X]) = -(1/4)d²`; also used in the proof of
Lemma 10.2.1, l. 9792 (`J(1 + 2√-d [pt_X]) = d`) and l. 9795 (`J ≤ 0` on `span{1, [pt_X]}`), and in
Example 10.2.3.) For every `c ∈ F`, `J(1 + c [pt_X]) = -(1/4) c²`. -/
theorem J_one_add_smul_pt (F : Type*) [Field F] [CharZero F] (c : F) :
    J F (1 + c • pt F 3) = -(1 / 4) * c ^ 2 := by
  have h := s10_J_add_smul_pt F 1 c
  rw [one_smul, one_mul] at h
  exact h

/-- (Proof of Lemma 10.1.1, l. 9706.) The kernel of `m_1 : V_F → S_F` is `W₁ = H¹(X̂, F)`, the
summand `H¹(X, F)* × 0` of `V_F` (Mathlib's order `(θ, w)`). -/
theorem ann_one (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    ann F n 1 = (⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥ := by
  ext v
  rw [ann, LinearMap.mem_ker, s10_mOf_apply, mul_one, show D F n v.1 1 = 0 from
    contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) _, add_zero, Submodule.mem_prod,
    ExteriorAlgebra.ι_eq_zero_iff]
  simp

/-- (Proof of Lemma 10.1.1, l. 9706–9707.) The kernel of `m_{[pt_X]} : V_F → S_F` is
`W₂ = H¹(X, F)`, the summand `0 × H¹(X, F)` of `V_F`. -/
theorem ann_pt (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    ann F n (pt F n) = (⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤ := by
  ext v
  rw [ann, LinearMap.mem_ker, s10_mOf_apply, s10_ι_mul_pt, zero_add, s10_D_pt_eq_zero_iff,
    Submodule.mem_prod]
  simp

theorem s10_isEvenPureSpinor_one (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    IsEvenPureSpinor F n 1 := by
  refine ⟨s10_one_mem_Splus F n, ?_, ?_⟩
  · intro v hv
    rw [ann_one, Submodule.mem_prod, Submodule.mem_bot] at hv
    obtain ⟨θ, w⟩ := v
    simp only at hv
    rw [hv.2]
    simp
  · rw [ann_one, s10_finrank_top_prod_bot]

theorem s10_isEvenPureSpinor_pt (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    IsEvenPureSpinor F n (pt F n) := by
  refine ⟨s10_pt_mem_Splus F n, ?_, ?_⟩
  · intro v hv
    rw [ann_pt, Submodule.mem_prod, Submodule.mem_bot] at hv
    obtain ⟨θ, w⟩ := v
    simp only at hv
    rw [hv.1]
    simp
  · rw [ann_pt, s10_finrank_bot_prod_top]

theorem s10_ann_one_inf_ann_pt (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    ann F n 1 ⊓ ann F n (pt F n) = ⊥ := by
  rw [ann_one, ann_pt, eq_bot_iff]
  rintro ⟨θ, w⟩ ⟨h1, h2⟩
  have h1' : (θ, w) ∈ (⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥ := h1
  have h2' : (θ, w) ∈ (⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤ := h2
  rw [Submodule.mem_prod, Submodule.mem_bot] at h1' h2'
  simp only at h1' h2'
  rw [h1'.2, h2'.1]
  exact Submodule.zero_mem _

theorem s10_linearIndependent_one_pt (F : Type*) [Field F] [CharZero F] {n : ℕ} (hn : 0 < n) :
    LinearIndependent F ![(1 : S F n), pt F n] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun x => (basisS F n).repr x ∅) hab
  have h2 := congrArg (fun x => (basisS F n).repr x Finset.univ) hab
  have hne : (∅ : Finset (Fin (2 * n))) ≠ Finset.univ := by
    intro h
    have : (⟨0, by omega⟩ : Fin (2 * n)) ∈ (Finset.univ : Finset (Fin (2 * n))) :=
      Finset.mem_univ _
    rw [← h] at this
    simp at this
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s10_repr_one, pt,
    s10_repr_basisS, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1 h2
  simp only [ite_true, hne.symm, ite_false, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

/-- (Proof of Lemma 10.1.1, l. 9705–9711; proof of Lemma 10.2.1, l. 9792: `P_{g(w)} =
span{1, [pt_X]}`.) The line through the pure spinors `1` and `[pt_X]` is a secant of the even
spinor variety meeting it only at `[1]` and `[pt_X]`, and `ker m_1 ∩ ker m_{[pt_X]} = 0`. -/
theorem isTransversalSecant_one_pt (F : Type*) [Field F] [CharZero F] :
    IsTransversalSecant F 3 (Submodule.span F {1, pt F 3}) 1 (pt F 3) := by
  refine ⟨rfl, s10_linearIndependent_one_pt F (by norm_num), s10_isEvenPureSpinor_one F 3,
    s10_isEvenPureSpinor_pt F 3, s10_ann_one_inf_ann_pt F 3, ?_⟩
  intro u hu hpure
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  -- [Chevalley, III.1.12]: a combination `a·1 + b·[pt_X]` is pure only if `a = 0` or `b = 0`.
  rcases chevalley_III_1_12 F 3 (by norm_num) 1 (pt F 3) (s10_isEvenPureSpinor_one F 3)
      (s10_isEvenPureSpinor_pt F 3) (s10_ann_one_inf_ann_pt F 3) a b hpure with ha | hb
  · right
    rw [ha, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · left
    rw [hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-! ## Helpers (prefix `s10_`): transport by `Spin(V)`, the nilpotents `D_{(f_i,0),(0,e_j)}` -/

section S10Transport

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem s10_m_ι_mem_evenOdd (v : V F n) {i : ZMod 2} {s : S F n}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    m F n (ι (Q F n) v) s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm F (H1 F n)) (i + 1) := by
  rw [s10_m_ι_apply]
  refine add_mem ?_ ?_
  · have h := CliffordAlgebra.evenOdd_mul_le (0 : QuadraticForm F (H1 F n)) 1 i
      (Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one _ v.2) hs)
    rwa [add_comm] at h
  · exact CliffordAlgebra.contractLeft_mem_evenOdd v.1 hs

theorem s10_m_evenOdd_mem_Splus {x : C F n} (hx : x ∈ CliffordAlgebra.evenOdd (Q F n) 0)
    {s : S F n} (hs : s ∈ Splus F n) : m F n x s ∈ Splus F n := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ _ hs
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have h := s10_m_ι_mem_evenOdd m₁ (s10_m_ι_mem_evenOdd m₂ hx)
    have h01 : ((0 : ZMod 2) + 1 + 1) = 0 := by decide
    rw [h01] at h
    exact h

/-- `m_g` preserves `S⁺` for `g ∈ Spin(V_F)` (`g` is even). -/
theorem s10_m_spin_mem_Splus (g : Spin F n) {s : S F n} (hs : s ∈ Splus F n) :
    m F n (g : C F n) s ∈ Splus F n := by
  have hx := spinGroup.mem_even g.2
  rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule] at hx
  exact s10_m_evenOdd_mem_Splus hx hs

theorem s10_m_inv_m (g : Spin F n) (s : S F n) :
    m F n ((g⁻¹ : Spin F n) : C F n) (m F n (g : C F n) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel,
    OneMemClass.coe_one, map_one, Module.End.one_apply]

theorem s10_m_m_inv (g : Spin F n) (s : S F n) :
    m F n (g : C F n) (m F n ((g⁻¹ : Spin F n) : C F n) s) = s := by
  have := s10_m_inv_m g⁻¹ s
  rwa [inv_inv] at this

theorem s10_m_injective (g : Spin F n) : Function.Injective (m F n (g : C F n)) := fun a b h => by
  have := congrArg (m F n ((g⁻¹ : Spin F n) : C F n)) h
  rwa [s10_m_inv_m, s10_m_inv_m] at this

theorem s10_mOf_eq (s : S F n) (v : V F n) : mOf F n s v = m F n (ι (Q F n) v) s := rfl

theorem s10_ann_smul {c : F} (hc : c ≠ 0) (u : S F n) : ann F n (c • u) = ann F n u := by
  ext v
  rw [ann, ann, LinearMap.mem_ker, LinearMap.mem_ker, s10_mOf_eq, s10_mOf_eq, map_smul,
    smul_eq_zero]
  simp [hc]

theorem s10_isEvenPureSpinor_smul {c : F} (hc : c ≠ 0) {u : S F n}
    (hu : IsEvenPureSpinor F n u) : IsEvenPureSpinor F n (c • u) := by
  refine ⟨Submodule.smul_mem _ _ hu.1, ?_⟩
  rw [s10_ann_smul hc]
  exact hu.2

theorem s10_isEvenPureSpinor_m (g : Spin F n) {u : S F n} (hu : IsEvenPureSpinor F n u) :
    IsEvenPureSpinor F n (m F n (g : C F n) u) := by
  refine ⟨s10_m_spin_mem_Splus g hu.1, ?_, ?_⟩
  · intro v hv
    rw [ann_m_spin] at hv
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    rw [LinearEquiv.coe_coe, rho, CliffordAlgebra.spinVectorAction_map_app]
    exact hu.2.1 v' hv'
  · rw [ann_m_spin, LinearEquiv.finrank_map_eq]
    exact hu.2.2

theorem s10_isEvenPureSpinor_m_iff (g : Spin F n) {u : S F n} :
    IsEvenPureSpinor F n (m F n (g : C F n) u) ↔ IsEvenPureSpinor F n u := by
  refine ⟨fun h => ?_, s10_isEvenPureSpinor_m g⟩
  have := s10_isEvenPureSpinor_m g⁻¹ h
  rwa [s10_m_inv_m] at this

theorem s10_mem_span_singleton_m (g : Spin F n) {u v : S F n}
    (h : v ∈ Submodule.span F {u}) :
    m F n (g : C F n) v ∈ Submodule.span F {m F n (g : C F n) u} := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Transport of a transversal secant by `g ∈ Spin(V_F)`. -/
theorem s10_isTransversalSecant_map (g : Spin F n) {P : Submodule F (S F n)} {u₁ u₂ : S F n}
    (h : IsTransversalSecant F n P u₁ u₂) :
    IsTransversalSecant F n (P.map (m F n (g : C F n))) (m F n (g : C F n) u₁)
      (m F n (g : C F n) u₂) := by
  obtain ⟨hP, hli, h₁, h₂, hW, hpure⟩ := h
  refine ⟨?_, ?_, s10_isEvenPureSpinor_m g h₁, s10_isEvenPureSpinor_m g h₂, ?_, ?_⟩
  · rw [hP, Submodule.map_span, Set.image_pair]
  · have := hli.map' (m F n (g : C F n)) (LinearMap.ker_eq_bot.mpr (s10_m_injective g))
    convert this using 1
    ext i
    fin_cases i <;> rfl
  · rw [ann_m_spin, ann_m_spin, ← Submodule.map_inf _ (rho F n g).injective, hW,
      Submodule.map_bot]
  · intro u hu hupure
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    rcases hpure u' hu' ((s10_isEvenPureSpinor_m_iff g).mp hupure) with h | h
    · exact Or.inl (s10_mem_span_singleton_m g h)
    · exact Or.inr (s10_mem_span_singleton_m g h)

theorem s10_map_m_inv_map (g : Spin F n) (P : Submodule F (S F n)) :
    (P.map (m F n (g : C F n))).map (m F n ((g⁻¹ : Spin F n) : C F n)) = P := by
  rw [← Submodule.map_comp]
  have : (m F n ((g⁻¹ : Spin F n) : C F n)).comp (m F n (g : C F n)) = LinearMap.id := by
    refine LinearMap.ext fun s => ?_
    exact s10_m_inv_m g s
  rw [this, Submodule.map_id]

end S10Transport


section S10Clearly

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem s10_pairing_apply (x y : V F n) : pairing F n x y = x.1 y.2 + y.1 x.2 := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd]

/-- The nilpotent `D_{(f_i,0),(0,e_j)}`: `(θ, w) ↦ (θ(e_j) f_i, -w_i e_j)`. -/
noncomputable def s10_N (i j : Fin (2 * n)) : V F n →ₗ[F] V F n where
  toFun v := (v.1 (e F n j) • f F n i, -(v.2 i) • e F n j)
  map_add' v w := by
    refine Prod.ext ?_ ?_
    · simp [add_smul]
    · simp only [Prod.snd_add, Pi.add_apply, neg_add, add_smul]
  map_smul' c v := by
    refine Prod.ext ?_ ?_
    · simp [smul_smul]
    · simp [smul_smul]

theorem s10_N_apply (i j : Fin (2 * n)) (v : V F n) :
    s10_N i j v = (v.1 (e F n j) • f F n i, -(v.2 i) • e F n j) := rfl

theorem s10_f_e (i j : Fin (2 * n)) : f F n i (e F n j) = if i = j then 1 else 0 := by
  simp [f, e, Pi.single_apply]

theorem s10_N_N {i j : Fin (2 * n)} (hij : i ≠ j) (v : V F n) : s10_N i j (s10_N i j v) = 0 := by
  refine Prod.ext ?_ ?_
  · simp [s10_N_apply, s10_f_e, hij]
  · simp [s10_N_apply, e, hij]

/-- The unipotent `1 + D_{(f_i,0),(0,e_j)}` (`i ≠ j`), an element of `e(SL(W₁))` (10.1.2). -/
noncomputable def s10_γ {i j : Fin (2 * n)} (hij : i ≠ j) : V F n ≃ₗ[F] V F n where
  toFun v := v + s10_N i j v
  invFun v := v - s10_N i j v
  map_add' v w := by simp only [map_add]; abel
  map_smul' c v := by simp [map_smul, smul_add]
  left_inv v := by simp only [map_add, s10_N_N hij, add_zero, add_sub_cancel_right]
  right_inv v := by simp only [map_sub, s10_N_N hij, sub_zero, sub_add_cancel]

theorem s10_γ_apply {i j : Fin (2 * n)} (hij : i ≠ j) (v : V F n) :
    s10_γ hij v = v + s10_N i j v := rfl

/-- The determinant of a rank-one perturbation of the identity: `det(1 + φ ⊗ x) = 1 + φ(x)`. -/
theorem s10_det_id_add_smulRight {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    [Module.Finite F M] (φ : Module.Dual F M) (x : M) :
    LinearMap.det (LinearMap.id + φ.smulRight x) = 1 + φ x := by
  let b := Module.Free.chooseBasis F M
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  rw [show Matrix.vecMulVec (b.repr x) (φ ∘ b) =
      Matrix.replicateCol Unit (b.repr x) * Matrix.replicateRow Unit (φ ∘ b) by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]]
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  change ∑ i, φ (b i) * b.repr x i = φ x
  calc ∑ i, φ (b i) * b.repr x i = ∑ i, φ ((b.repr x i) • b i) := by
        simp only [map_smul, smul_eq_mul, mul_comm]
    _ = φ (∑ i, (b.repr x i) • b i) := by rw [map_sum]
    _ = φ x := congrArg φ (b.sum_repr x)

/-- `H¹(X̂) = H¹(X)* × 0` as a submodule of `V`, identified with `H¹(X)*`. -/
noncomputable def s10_eA :
    Module.Dual F (H1 F n) ≃ₗ[F]
      ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n))) where
  toFun θ := ⟨(θ, 0), by simp [Submodule.mem_prod]⟩
  invFun v := v.1.1
  map_add' θ θ' := by ext <;> simp
  map_smul' c θ := by ext <;> simp
  left_inv θ := rfl
  right_inv v := by
    obtain ⟨⟨θ, w⟩, hv⟩ := v
    have hw : w = 0 := by
      have := (Submodule.mem_prod.mp hv).2
      simpa using this
    subst hw
    rfl

theorem s10_γ_mem_slImage {i j : Fin (2 * n)} (hij : i ≠ j) :
    s10_γ hij ∈ slImage F n ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥)
      ((⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤) := by
  have hA : ∀ v ∈ (⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)),
      s10_γ hij v ∈ (⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)) := by
    intro v hv
    have h2 : v.2 = 0 := by simpa using (Submodule.mem_prod.mp hv).2
    refine Submodule.mem_prod.mpr ⟨Submodule.mem_top, ?_⟩
    simp [s10_γ_apply, s10_N_apply, h2]
  refine ⟨?_, hA, ?_, ?_⟩
  · intro x y
    simp only [s10_γ_apply, s10_pairing_apply, s10_N_apply, LinearMap.add_apply, map_add,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [f, e, LinearMap.proj_apply, Pi.single_apply, hij, ite_false]
    ring
  · intro v hv
    have h1 : v.1 = 0 := by simpa using (Submodule.mem_prod.mp hv).1
    refine Submodule.mem_prod.mpr ⟨?_, Submodule.mem_top⟩
    simp [s10_γ_apply, s10_N_apply, h1]
  · -- `γ` acts on `H¹(X̂) ≅ H¹(X)*` as `θ ↦ θ + θ(e_j) f_i`, of determinant `1 + f_i(e_j) = 1`
    have hconj : (s10_γ hij).toLinearMap.restrict hA =
        (s10_eA : Module.Dual F (H1 F n) ≃ₗ[F] _).toLinearMap ∘ₗ
          (LinearMap.id + (LinearMap.applyₗ (e F n j)).smulRight (f F n i)) ∘ₗ
            (s10_eA : Module.Dual F (H1 F n) ≃ₗ[F] _).symm.toLinearMap := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨⟨θ, w⟩, hv⟩ := v
      have hw : w = 0 := by simpa using (Submodule.mem_prod.mp hv).2
      subst hw
      apply Subtype.ext
      simp [s10_eA, s10_γ_apply, s10_N_apply, LinearMap.restrict_apply]
    show LinearMap.det ((s10_γ hij).toLinearMap.restrict hA) = 1
    rw [hconj, LinearMap.det_conj, s10_det_id_add_smulRight]
    simp [s10_f_e, hij]

/-- **"Clearly, `W₁` and `W₂` are the only two maximal isotropic subspaces invariant under
`e(SL(W₁))`"** (proof of Lemma 10.1.1), for `W₁ = H¹(X̂)`, `W₂ = H¹(X)`: a `6`-dimensional subspace
of `V` invariant under the nilpotents `D_{(f_i,0),(0,e_j)}`, `i ≠ j`, is `W₁` or `W₂`. -/
theorem s10_eq_A_or_B (W : Submodule F (V F 3)) (hW : Module.finrank F W = 6)
    (hinv : ∀ i j : Fin 6, i ≠ j → ∀ v ∈ W, s10_N i j v ∈ W) :
    W = (⊤ : Submodule F (Module.Dual F (H1 F 3))).prod ⊥ ∨
      W = (⊥ : Submodule F (Module.Dual F (H1 F 3))).prod ⊤ := by
  by_cases h : ∃ v ∈ W, v.2 ≠ 0
  · right
    obtain ⟨v, hv, hv2⟩ := h
    obtain ⟨j, hj⟩ : ∃ j, v.2 j ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hv2 (funext h')
    have hthird : ∀ a b : Fin 6, ∃ k : Fin 6, k ≠ a ∧ k ≠ b := by decide
    -- `(0, e_m) ∈ W` for `m ≠ j`
    have hm : ∀ m : Fin 6, m ≠ j → ((0, e F 3 m) : V F 3) ∈ W := by
      intro m hmj
      obtain ⟨k, hkj, hkm⟩ := hthird j m
      have h1 := hinv j k (Ne.symm hkj) v hv
      have h2 := hinv k m hkm _ h1
      have e2 : s10_N k m (s10_N j k v) = v.2 j • ((0, e F 3 m) : V F 3) := by
        refine Prod.ext ?_ ?_
        · simp [s10_N_apply, s10_f_e, Ne.symm hmj]
        · simp [s10_N_apply, e]
      rw [e2] at h2
      have := W.smul_mem (v.2 j)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at this
    have hall : ∀ m : Fin 6, ((0, e F 3 m) : V F 3) ∈ W := by
      intro m
      by_cases hmj : m = j
      · subst hmj
        obtain ⟨m₀, hm₀, -⟩ := hthird m m
        have h1 := hinv m₀ m hm₀ _ (hm m₀ hm₀)
        have e1 : s10_N m₀ m ((0, e F 3 m₀) : V F 3) = -((0, e F 3 m) : V F 3) := by
          refine Prod.ext ?_ ?_
          · simp [s10_N_apply]
          · simp [s10_N_apply, e]
        rw [e1] at h1
        have := W.neg_mem h1
        rwa [neg_neg] at this
      · exact hm m hmj
    have hle : (⊥ : Submodule F (Module.Dual F (H1 F 3))).prod ⊤ ≤ W := by
      intro x hx
      have h1 : x.1 = 0 := by simpa using (Submodule.mem_prod.mp hx).1
      have hx' : x = ∑ m : Fin 6, x.2 m • ((0, e F 3 m) : V F 3) := by
        refine Prod.ext ?_ ?_
        · simp [h1, Prod.fst_sum]
        · funext k
          simp [Prod.snd_sum, Finset.sum_apply, e, Pi.single_apply]
      rw [hx']
      exact Submodule.sum_mem _ fun m _ => W.smul_mem _ (hall m)
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [s10_finrank_bot_prod_top, hW])).symm
  · left
    push Not at h
    have hle : W ≤ (⊤ : Submodule F (Module.Dual F (H1 F 3))).prod ⊥ := by
      intro x hx
      exact Submodule.mem_prod.mpr ⟨Submodule.mem_top, by simpa using h x hx⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [s10_finrank_top_prod_bot, hW])

end S10Clearly

section S10Unique

set_option linter.unusedSectionVars false

/-- If `g ∈ Spin(V_F)` fixes `u`, then `ρ(g)` preserves `ker m_u`. -/
theorem s10_rho_mem_ann_of_fix {F : Type*} [Field F] [CharZero F] {n : ℕ} {u : S F n}
    (g : Spin F n) (hg : m F n (g : C F n) u = u) (v : V F n) (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n u := by
  have hinv : m F n ((g⁻¹ : Spin F n) : C F n) u = u := by
    conv_lhs => rw [← hg]
    exact s10_m_inv_m g u
  rw [ann, LinearMap.mem_ker, s10_mOf_eq, ι_rho, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply]
  have hs : star (g : C F n) = ((g⁻¹ : Spin F n) : C F n) := rfl
  rw [hs, hinv]
  rw [ann, LinearMap.mem_ker, s10_mOf_eq] at hv
  rw [hv, map_zero]

theorem s10_J_zero (F : Type*) [Field F] [CharZero F] : J F 0 = 0 := by
  have h := J_smul F 0 0
  rw [zero_smul] at h
  rw [h]; ring

theorem s10_ne_zero_of_J {F : Type*} [Field F] [CharZero F] {w : S F 3} (hJ : J F w ≠ 0) :
    w ≠ 0 := by
  rintro rfl
  exact hJ (s10_J_zero F)

/-- `1 + c [pt_X]`, `c ≠ 0`, is not a pure spinor ([Chevalley, III.1.12]). -/
theorem s10_not_pure_one_add {F : Type*} [Field F] [CharZero F] {c : F} (hc : c ≠ 0) :
    ¬ IsEvenPureSpinor F 3 (1 + c • pt F 3) := by
  intro h
  rw [show (1 : S F 3) + c • pt F 3 = (1 : F) • 1 + c • pt F 3 by rw [one_smul]] at h
  rcases chevalley_III_1_12 F 3 (by norm_num) 1 (pt F 3) (s10_isEvenPureSpinor_one F 3)
      (s10_isEvenPureSpinor_pt F 3) (s10_ann_one_inf_ann_pt F 3) 1 c h with h1 | h1
  · exact one_ne_zero h1
  · exact hc h1

theorem s10_one_add_mem_Splus {F : Type*} [Field F] [CharZero F] (c : F) :
    (1 : S F 3) + c • pt F 3 ∈ Splus F 3 :=
  add_mem (s10_one_mem_Splus F 3) (Submodule.smul_mem _ _ (s10_pt_mem_Splus F 3))

theorem s10_one_add_mem_span {F : Type*} [Field F] [CharZero F] (c : F) :
    (1 : S F 3) + c • pt F 3 ∈ Submodule.span F {1, pt F 3} :=
  add_mem (Submodule.subset_span (by simp))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The reduction step of the proof of Lemma 10.1.1 (l. 9702–9705), by [Igusa, Prop. 3]: every
`w ∈ S⁺_ℂ` with `J(w) ≠ 0` lies in the `Spin(V_ℂ)`-orbit of some `1 + c [pt_X]`, `c ≠ 0`. -/
theorem s10_normal_form (hIgusa : IgusaProp3NormalForm) (w : S ℂ 3) (hw : w ∈ Splus ℂ 3)
    (hJ : J ℂ w ≠ 0) :
    ∃ g : Spin ℂ 3, ∃ c : ℂ, c ≠ 0 ∧ m ℂ 3 (g : C ℂ 3) w = 1 + c • pt ℂ 3 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-J ℂ w) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hJ
    linear_combination hs
  have hJ0 : J ℂ (1 + (2 * s) • pt ℂ 3) = J ℂ w := by
    rw [J_one_add_smul_pt]
    linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := igusa_prop3_orbit_complex hIgusa w _ hw (s10_one_add_mem_Splus _) hJ0.symm hJ
  exact ⟨g, 2 * s, mul_ne_zero two_ne_zero hs0, hg⟩

/-- On the two named hypotheses for [Igusa, Prop. 3] (`WeilClasses/External/Igusa/README.md`):
over a subfield `F ⊆ ℂ`, the normal form (`IgusaProp3NormalForm`) follows from the orbit statement
quoted in Remark 10.1.2(1) (`IgusaProp3OrbitSubfield`), since
`J(1 + 2s [pt_X]) = -s² = J(w) ≠ 0`. -/
theorem s10_normalForm_of_orbitSubfield (hIgusa : IgusaProp3OrbitSubfield) (F : Subfield ℂ)
    (w : S F 3) (hw : w ∈ Splus F 3) (s : F) (hs : s ≠ 0) (hsJ : s ^ 2 = -J F w) :
    ∃ g : Spin F 3, m F 3 (g : C F 3) w = 1 + (2 * s) • pt F 3 := by
  have hJ : J F w ≠ 0 := by
    intro h
    rw [h, neg_zero] at hsJ
    exact hs ((pow_eq_zero_iff two_ne_zero).mp hsJ)
  refine igusa_prop3_orbit_subfield hIgusa F (J F w) hJ w _ hw (s10_one_add_mem_Splus _) rfl ?_
  rw [J_one_add_smul_pt]
  linear_combination (-1 : F) * hsJ

/-- **"The two lines spanned by `1` and `[pt_X]` are the only pure spinor lines in `S⁺_ℂ` stabilized
under `Spin(V_ℂ)_w`"** (proof of Lemma 10.1.1), for `w = 1 + c [pt_X]`: by [Igusa, Lemma 2] the
image of the stabilizer is `e(SL(W₁))`, which leaves only `W₁ = ker m_1` and `W₂ = ker m_{[pt]}`
invariant (`s10_eq_A_or_B`), and `ker m_u` determines `[u]` ([Chevalley, III.1.4]). -/
theorem s10_pure_stable {c : ℂ} (hc : c ≠ 0) {u : S ℂ 3} (hu : IsEvenPureSpinor ℂ 3 u)
    (hstab : ∀ h ∈ spinStab ℂ 3 (1 + c • pt ℂ 3), ∀ v ∈ ann ℂ 3 u, rho ℂ 3 h v ∈ ann ℂ 3 u) :
    u ∈ Submodule.span ℂ {1} ∨ u ∈ Submodule.span ℂ {pt ℂ 3} := by
  have hinv : ∀ i j : Fin 6, i ≠ j → ∀ v ∈ ann ℂ 3 u, s10_N i j v ∈ ann ℂ 3 u := by
    intro i j hij v hv
    have hγ := s10_γ_mem_slImage (F := ℂ) (n := 3) hij
    rw [← igusa_lemma2 c hc] at hγ
    obtain ⟨h, hh, hρ⟩ := hγ
    have h1 := hstab h hh v hv
    rw [hρ, s10_γ_apply] at h1
    have h2 := sub_mem h1 hv
    rwa [add_sub_cancel_left] at h2
  have hfin : Module.finrank ℂ (ann ℂ 3 u) = 6 := hu.2.2
  rcases s10_eq_A_or_B (ann ℂ 3 u) hfin hinv with hA | hB
  · left
    exact chevalley_III_1_4_unique ℂ 3 1 u one_ne_zero (s10_isEvenPureSpinor_one ℂ 3).2
      (hA.trans (ann_one ℂ 3).symm)
  · right
    exact chevalley_III_1_4_unique ℂ 3 (pt ℂ 3) u (s10_pt_ne_zero ℂ 3)
      (s10_isEvenPureSpinor_pt ℂ 3).2 (hB.trans (ann_pt ℂ 3).symm)

theorem s10_span_pair_smul {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (x y : M) :
    Submodule.span F {a • x, b • y} = Submodule.span F {x, y} := by
  rw [Submodule.span_insert, Submodule.span_insert, Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr ha), Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hb)]

theorem s10_span_pair_comm {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    (x y : M) : Submodule.span F {x, y} = Submodule.span F {y, x} := by
  rw [Set.pair_comm]

/-- The core of the uniqueness in Lemma 10.1.1: a transversal secant `P ∋ w`, with `m_g w =
1 + c [pt_X]`, is carried by `m_g` onto `span{1, [pt_X]}`, with `u₁, u₂` going to the two lines
`ℂ·1`, `ℂ·[pt_X]` (in some order). The paper's argument (l. 9709–9711): the only pure spinor lines
stabilized by `Spin(V_ℂ)_{w₀}`, `w₀ = 1 + c [pt_X]`, are `ℂ·1` and `ℂ·[pt_X]` (`s10_pure_stable`).
Gap in the paper (filled): that `Spin(V_ℂ)_w` stabilizes the lines of `u₁` and `u₂` (every point of
`P` is `Spin(V_ℂ)_w`-invariant) is [Igusa, Lemma 2] for the pair `u₁, u₂`
(`igusa_lemma2_stab_odd`), as in Remark 2.2.3 (l. 835). -/
theorem s10_secant_lines (w : S ℂ 3) (hw0 : w ≠ 0) (g : Spin ℂ 3) {c : ℂ} (hc : c ≠ 0)
    (hg : m ℂ 3 (g : C ℂ 3) w = 1 + c • pt ℂ 3) {P : Submodule ℂ (S ℂ 3)} {u₁ u₂ : S ℂ 3}
    (hP : IsTransversalSecant ℂ 3 P u₁ u₂) (hwP : w ∈ P) :
    (m ℂ 3 (g : C ℂ 3) u₁ ∈ Submodule.span ℂ {1} ∧
        m ℂ 3 (g : C ℂ 3) u₂ ∈ Submodule.span ℂ {pt ℂ 3}) ∨
      (m ℂ 3 (g : C ℂ 3) u₁ ∈ Submodule.span ℂ {pt ℂ 3} ∧
        m ℂ 3 (g : C ℂ 3) u₂ ∈ Submodule.span ℂ {1}) := by
  obtain ⟨hPspan, hli, h₁, h₂, hW, -⟩ := hP
  rw [hPspan] at hwP
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hwP
  -- `a, b ≠ 0`: `w` is not pure, since `1 + c [pt]` is not
  have hnp : ¬ IsEvenPureSpinor ℂ 3 w := by
    intro h
    exact s10_not_pure_one_add hc (hg ▸ s10_isEvenPureSpinor_m g h)
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hab
    have hb : b ≠ 0 := by rintro rfl; rw [zero_smul] at hab; exact hw0 hab.symm
    exact hnp (hab ▸ s10_isEvenPureSpinor_smul hb h₂)
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hab
    exact hnp (hab ▸ s10_isEvenPureSpinor_smul ha h₁)
  -- [Igusa, Lemma 2]: the stabilizer of `w = a u₁ + b u₂` fixes `u₁` and `u₂`
  have hfix := igusa_lemma2_stab_odd ℂ 3 (le_refl 3) (by decide) u₁ u₂ h₁ h₂ hW a b ha hb
  rw [hab] at hfix
  -- hence `Spin(V)_{w₀}` stabilizes the pure spinor lines `m_g u₁`, `m_g u₂`
  have hstab : ∀ u ∈ ({u₁, u₂} : Set (S ℂ 3)),
      ∀ h ∈ spinStab ℂ 3 (1 + c • pt ℂ 3), m ℂ 3 (h : C ℂ 3) (m ℂ 3 (g : C ℂ 3) u) =
        m ℂ 3 (g : C ℂ 3) u := by
    intro u hu h hh
    have hconj : g⁻¹ * h * g ∈ fixingSpin ℂ 3 (Submodule.span ℂ {w}) := by
      intro p hp
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hp
      rw [map_smul, Submonoid.coe_mul, Submonoid.coe_mul, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hg, show m ℂ 3 (h : C ℂ 3) (1 + c • pt ℂ 3) = 1 + c • pt ℂ 3 from hh,
        ← hg, s10_m_inv_m]
    rw [hfix] at hconj
    have hu' := hconj u (Submodule.subset_span hu)
    rw [Submonoid.coe_mul, Submonoid.coe_mul, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply] at hu'
    have := congrArg (m ℂ 3 (g : C ℂ 3)) hu'
    rwa [s10_m_m_inv] at this
  have hl₁ := s10_pure_stable hc (s10_isEvenPureSpinor_m g h₁) fun h hh v hv =>
    s10_rho_mem_ann_of_fix h (hstab u₁ (by simp) h hh) v hv
  have hl₂ := s10_pure_stable hc (s10_isEvenPureSpinor_m g h₂) fun h hh v hv =>
    s10_rho_mem_ann_of_fix h (hstab u₂ (by simp) h hh) v hv
  -- the two lines are distinct
  have hli' : LinearIndependent ℂ ![m ℂ 3 (g : C ℂ 3) u₁, m ℂ 3 (g : C ℂ 3) u₂] := by
    have := hli.map' (m ℂ 3 (g : C ℂ 3)) (LinearMap.ker_eq_bot.mpr (s10_m_injective g))
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hnot : ∀ z : S ℂ 3, ¬ (m ℂ 3 (g : C ℂ 3) u₁ ∈ Submodule.span ℂ {z} ∧
      m ℂ 3 (g : C ℂ 3) u₂ ∈ Submodule.span ℂ {z}) := by
    rintro z ⟨hz₁, hz₂⟩
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hz₁
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hz₂
    have h0 := LinearIndependent.pair_iff.mp hli' β (-α) (by
      rw [← hα, ← hβ, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm β α, add_neg_cancel])
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hα
      exact (s10_isEvenPureSpinor_m g h₁).ne_zero (by norm_num) hα.symm
    exact hα0 (neg_eq_zero.mp h0.2)
  rcases hl₁ with h1 | h1 <;> rcases hl₂ with h2 | h2
  · exact absurd ⟨h1, h2⟩ (hnot 1)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd ⟨h1, h2⟩ (hnot _)

/-- Consequently `m_g P = span{1, [pt_X]}`. -/
theorem s10_secant_map_eq (w : S ℂ 3) (hw0 : w ≠ 0) (g : Spin ℂ 3) {c : ℂ} (hc : c ≠ 0)
    (hg : m ℂ 3 (g : C ℂ 3) w = 1 + c • pt ℂ 3) {P : Submodule ℂ (S ℂ 3)} {u₁ u₂ : S ℂ 3}
    (hP : IsTransversalSecant ℂ 3 P u₁ u₂) (hwP : w ∈ P) :
    P.map (m ℂ 3 (g : C ℂ 3)) = Submodule.span ℂ {1, pt ℂ 3} := by
  have hP' := s10_isTransversalSecant_map g hP
  have hne₁ : m ℂ 3 (g : C ℂ 3) u₁ ≠ 0 := hP'.2.2.1.ne_zero (by norm_num)
  have hne₂ : m ℂ 3 (g : C ℂ 3) u₂ ≠ 0 := hP'.2.2.2.1.ne_zero (by norm_num)
  rw [hP'.1]
  rcases s10_secant_lines w hw0 g hc hg hP hwP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp h2
    have hα0 : α ≠ 0 := by rintro rfl; rw [zero_smul] at hα; exact hne₁ hα.symm
    have hβ0 : β ≠ 0 := by rintro rfl; rw [zero_smul] at hβ; exact hne₂ hβ.symm
    rw [← hα, ← hβ, s10_span_pair_smul hα0 hβ0]
  · obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp h2
    have hα0 : α ≠ 0 := by rintro rfl; rw [zero_smul] at hα; exact hne₁ hα.symm
    have hβ0 : β ≠ 0 := by rintro rfl; rw [zero_smul] at hβ; exact hne₂ hβ.symm
    rw [← hα, ← hβ, s10_span_pair_smul hα0 hβ0, s10_span_pair_comm]

end S10Unique

section S10Stab

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem s10_Q_nondegenerate (F : Type*) [Field F] [CharZero F] (n : ℕ) : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

theorem s10_nontrivial_V (hn : 0 < n) : Nontrivial (V F n) :=
  ⟨⟨(0, e F n ⟨0, by omega⟩), 0, fun h => by
    have := congrArg (fun x : V F n => x.2 ⟨0, by omega⟩) h
    simp [e] at this⟩⟩

/-- "**The kernel of `ρ` has order `2`, generated by `-1`, which acts as `-id` on `S`; hence it
meets `Spin(V)_w` trivially**" (proof of Lemma 10.1.1): `ρ` is injective on the stabilizer of a
nonzero spinor. -/
theorem s10_rho_injOn (hn : 0 < n) {w : S F n} (hw : w ≠ 0) :
    Set.InjOn (rho F n) (spinStab F n w : Set (Spin F n)) := by
  intro g hg h hh hgh
  have hQ := s10_Q_nondegenerate F n
  have := s10_nontrivial_V (F := F) hn
  have hker : h⁻¹ * g ∈ MonoidHom.ker (CliffordAlgebra.spinToOrthogonal (Q F n)) := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have h1 : CliffordAlgebra.spinVectorAction (Q F n) g =
        CliffordAlgebra.spinVectorAction (Q F n) h := hgh
    rw [CliffordAlgebra.coe_spinToOrthogonal_apply, CliffordAlgebra.spinVectorAction_mul, h1,
      ← CliffordAlgebra.spinVectorAction_mul, inv_mul_cancel, CliffordAlgebra.spinVectorAction_one]
    rfl
  rcases (CliffordAlgebra.mem_ker_spinToOrthogonal_iff (Q F n) hQ (h⁻¹ * g)).mp hker with h1 | h1
  · exact (inv_mul_eq_one.mp h1).symm
  · exfalso
    have hg' : g = h * CliffordAlgebra.spinGroup.negOne (Q F n) hQ.ne_zero := by
      rw [← h1, mul_inv_cancel_left]
    have hgw : m F n (g : C F n) w = w := hg
    have hhw : m F n (h : C F n) w = w := hh
    rw [hg', Submonoid.coe_mul, CliffordAlgebra.spinGroup.coe_negOne, map_mul, map_neg, map_one,
      mul_neg, mul_one, LinearMap.neg_apply, hhw] at hgw
    have h2 : (2 : F) • w = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hgw]
      exact neg_add_cancel w
    exact hw ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- `e(SL(W₁))` (10.1.2) is compatible with isometries: `σ e(SL(W₁)) σ⁻¹ = e(SL(σ W₁))`. -/
theorem s10_slImage_conj_mem (σ : V F n ≃ₗ[F] V F n)
    (hσ : ∀ x y, pairing F n (σ x) (σ y) = pairing F n x y) {W₁ W₂ : Submodule F (V F n)}
    {γ : V F n ≃ₗ[F] V F n} (hγ : γ ∈ slImage F n W₁ W₂) :
    σ.symm.trans (γ.trans σ) ∈ slImage F n (W₁.map (σ : V F n →ₗ[F] V F n))
      (W₂.map (σ : V F n →ₗ[F] V F n)) := by
  obtain ⟨hiso, h₁, h₂, hdet⟩ := hγ
  have hσ' : ∀ x y, pairing F n (σ.symm x) (σ.symm y) = pairing F n x y := by
    intro x y
    rw [← hσ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hA : ∀ v ∈ W₁.map (σ : V F n →ₗ[F] V F n),
      σ.symm.trans (γ.trans σ) v ∈ W₁.map (σ : V F n →ₗ[F] V F n) := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨γ v', h₁ v' hv', ?_⟩
    simp
  refine ⟨fun x y => ?_, hA, ?_, ?_⟩
  · simp only [LinearEquiv.trans_apply]
    rw [hσ, hiso, hσ']
  · intro v hv
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨γ v', h₂ v' hv', ?_⟩
    simp
  · have hconj : (σ.symm.trans (γ.trans σ)).toLinearMap.restrict hA =
        (σ.submoduleMap W₁).toLinearMap ∘ₗ (γ.toLinearMap.restrict h₁) ∘ₗ
          (σ.submoduleMap W₁).symm.toLinearMap := by
      refine LinearMap.ext fun v => ?_
      apply Subtype.ext
      obtain ⟨v, hv⟩ := v
      obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
      have : (σ.submoduleMap W₁).symm ⟨σ v', hv⟩ = ⟨v', hv'⟩ := by
        apply (σ.submoduleMap W₁).injective
        apply Subtype.ext
        simp [LinearEquiv.submoduleMap_apply]
      simp [this, LinearEquiv.submoduleMap_apply, LinearMap.restrict_apply]
    show LinearMap.det ((σ.symm.trans (γ.trans σ)).toLinearMap.restrict hA) = 1
    rw [hconj, LinearMap.det_conj]
    exact hdet

theorem s10_slImage_conj (σ : V F n ≃ₗ[F] V F n)
    (hσ : ∀ x y, pairing F n (σ x) (σ y) = pairing F n x y) (W₁ W₂ : Submodule F (V F n)) :
    slImage F n (W₁.map (σ : V F n →ₗ[F] V F n)) (W₂.map (σ : V F n →ₗ[F] V F n)) =
      (fun γ => σ.symm.trans (γ.trans σ)) '' slImage F n W₁ W₂ := by
  have hσ' : ∀ x y, pairing F n (σ.symm x) (σ.symm y) = pairing F n x y := by
    intro x y
    rw [← hσ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext γ
  constructor
  · intro hγ
    refine ⟨σ.trans (γ.trans σ.symm), ?_, ?_⟩
    · have := s10_slImage_conj_mem σ.symm hσ' hγ
      have e1 : (W₁.map (σ : V F n →ₗ[F] V F n)).map (σ.symm : V F n →ₗ[F] V F n) = W₁ := by
        rw [← Submodule.map_comp]
        simp
      have e2 : (W₂.map (σ : V F n →ₗ[F] V F n)).map (σ.symm : V F n →ₗ[F] V F n) = W₂ := by
        rw [← Submodule.map_comp]
        simp
      rw [e1, e2, LinearEquiv.symm_symm] at this
      exact this
    · refine LinearEquiv.ext fun v => ?_
      simp
  · rintro ⟨γ', hγ', rfl⟩
    exact s10_slImage_conj_mem σ hσ hγ'

/-- `H¹(X) = 0 × H¹(X)`, identified with `H¹(X)`. -/
noncomputable def s10_eB :
    H1 F n ≃ₗ[F] ((⊥ : Submodule F (Module.Dual F (H1 F n))).prod (⊤ : Submodule F (H1 F n))) where
  toFun w := ⟨(0, w), by simp [Submodule.mem_prod]⟩
  invFun v := v.1.2
  map_add' θ θ' := by ext <;> simp
  map_smul' c θ := by ext <;> simp
  left_inv θ := rfl
  right_inv v := by
    obtain ⟨⟨θ, w⟩, hv⟩ := v
    have hθ : θ = 0 := by
      have := (Submodule.mem_prod.mp hv).1
      simpa using this
    subst hθ
    rfl

/-- For the standard pair, an isometry preserving `W₁ = H¹(X̂)` and `W₂ = H¹(X)` acts on `W₂ ≅ W₁*`
by the inverse transpose, so `det(γ|_{W₁}) det(γ|_{W₂}) = 1`; hence `e(SL(W₁)) = e(SL(W₂))`. -/
theorem s10_slImage_symm_std :
    slImage F n ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥)
        ((⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤) =
      slImage F n ((⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤)
        ((⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥) := by
  -- the key identity `det(γ|_A) * det(γ|_B) = 1`
  have key : ∀ γ : V F n ≃ₗ[F] V F n, (∀ x y, pairing F n (γ x) (γ y) = pairing F n x y) →
      ∀ (hA : ∀ v ∈ (⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)),
        γ v ∈ (⊤ : Submodule F (Module.Dual F (H1 F n))).prod (⊥ : Submodule F (H1 F n)))
      (hB : ∀ v ∈ (⊥ : Submodule F (Module.Dual F (H1 F n))).prod (⊤ : Submodule F (H1 F n)),
        γ v ∈ (⊥ : Submodule F (Module.Dual F (H1 F n))).prod (⊤ : Submodule F (H1 F n))),
      LinearMap.det (γ.toLinearMap.restrict hA) * LinearMap.det (γ.toLinearMap.restrict hB) = 1 := by
    intro γ hiso hA hB
    set φ := (s10_eA (F := F) (n := n)).symm.toLinearMap ∘ₗ (γ.toLinearMap.restrict hA) ∘ₗ
      (s10_eA (F := F) (n := n)).toLinearMap with hφ
    set ψ := (s10_eB (F := F) (n := n)).symm.toLinearMap ∘ₗ (γ.toLinearMap.restrict hB) ∘ₗ
      (s10_eB (F := F) (n := n)).toLinearMap with hψ
    have hdφ : LinearMap.det φ = LinearMap.det (γ.toLinearMap.restrict hA) :=
      LinearMap.det_conj _ (s10_eA (F := F) (n := n)).symm
    have hdψ : LinearMap.det ψ = LinearMap.det (γ.toLinearMap.restrict hB) :=
      LinearMap.det_conj _ (s10_eB (F := F) (n := n)).symm
    have hγA : ∀ θ, γ (θ, 0) = (φ θ, 0) := by
      intro θ
      have h := hA (θ, 0) (by simp [Submodule.mem_prod])
      have h2 : (γ (θ, 0)).2 = 0 := by simpa using (Submodule.mem_prod.mp h).2
      refine Prod.ext rfl ?_
      rw [h2]
    have hγB : ∀ w, γ (0, w) = (0, ψ w) := by
      intro w
      have h := hB (0, w) (by simp [Submodule.mem_prod])
      have h1 : (γ (0, w)).1 = 0 := by simpa using (Submodule.mem_prod.mp h).1
      refine Prod.ext ?_ rfl
      rw [h1]
    have hcomp : ψ.dualMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun θ => LinearMap.ext fun w => ?_
      have h := hiso (θ, 0) (0, w)
      rw [hγA, hγB, s10_pairing_apply, s10_pairing_apply] at h
      simpa [LinearMap.dualMap_apply] using h
    have := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_dualMap, LinearMap.det_id, hdφ, hdψ] at this
    rw [mul_comm]
    exact this
  ext γ
  constructor
  · rintro ⟨hiso, hA, hB, hdet⟩
    refine ⟨hiso, hB, hA, ?_⟩
    have := key γ hiso hA hB
    rw [hdet, one_mul] at this
    exact this
  · rintro ⟨hiso, hB, hA, hdet⟩
    refine ⟨hiso, hA, hB, ?_⟩
    have := key γ hiso hA hB
    rw [hdet, mul_one] at this
    exact this

theorem s10_rho_isometry (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, rho,
    CliffordAlgebra.spinVectorAction_map_app]

end S10Stab

section S10Parity

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The exterior basis is homogeneous: a `k`-vector has no coordinates on index sets of other
cardinalities. -/
theorem s10_repr_eq_zero_of_mem {k : ℕ} {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n))
    {K : Finset (Fin (2 * n))} (hK : K.card ≠ k) : (basisS F n).repr x K = 0 := by
  rw [basisS, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
    Set.powersetCard.prodEquiv_symm_apply]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (Ne.symm hK) hx

theorem s10_basisS_mem (K : Finset (Fin (2 * n))) : basisS F n K ∈ ⋀[F]^K.card (H1 F n) := by
  rw [basisS, ExteriorAlgebra.basis_apply_ofCard (b := Pi.basisFun F (Fin (2 * n))) rfl]
  exact ExteriorAlgebra.ιMulti_range F _ ⟨_, rfl⟩

theorem s10_basisS_mem_Splus {K : Finset (Fin (2 * n))} (hK : Even K.card) :
    basisS F n K ∈ Splus F n := by
  have h := s10_basisS_mem (F := F) K
  rw [ExteriorAlgebra.exteriorPower] at h
  exact Submodule.mem_iSup_of_mem (⟨K.card, by
    obtain ⟨r, hr⟩ := hK
    rw [hr, Nat.cast_add]
    exact (CharTwo.add_self_eq_zero (r : ZMod 2))⟩ : {j : ℕ // (j : ZMod 2) = 0}) h

/-- `S⁺` is the span of the `e_K` with `|K|` even: `s ∈ S⁺` iff its odd coordinates vanish. -/
theorem s10_mem_Splus_iff (s : S F n) :
    s ∈ Splus F n ↔ ∀ K : Finset (Fin (2 * n)), ¬ Even K.card → (basisS F n).repr s K = 0 := by
  constructor
  · intro hs K hK
    have hs' : s ∈ ⨆ j : {j : ℕ // (j : ZMod 2) = 0},
        LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n))) ^ (j : ℕ) := hs
    refine Submodule.iSup_induction (fun j : {j : ℕ // (j : ZMod 2) = 0} =>
      LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n))) ^ (j : ℕ))
      (motive := fun x => (basisS F n).repr x K = 0) hs' ?_ ?_ ?_
    · intro j x hx
      apply s10_repr_eq_zero_of_mem (k := (j : ℕ)) hx
      intro hc
      apply hK
      rw [hc]
      exact (ZMod.natCast_eq_zero_iff_even).mp j.2
    · simp
    · intro x y hx hy
      rw [map_add, Finsupp.add_apply, hx, hy, add_zero]
  · intro h
    rw [← (basisS F n).sum_repr s]
    refine Submodule.sum_mem _ fun K _ => ?_
    by_cases hK : Even K.card
    · exact Submodule.smul_mem _ _ (s10_basisS_mem_Splus hK)
    · rw [h K hK, zero_smul]
      exact Submodule.zero_mem _

end S10Parity

section S10Conj

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ} (c : F ≃+* F)

theorem s10_repr_conjS (s : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F n).repr (conjS c n s) K = c ((basisS F n).repr s K) := by
  show (basisS F n).repr (∑ L, c ((basisS F n).repr s L) • basisS F n L) K = _
  rw [map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem s10_S_ext {s t : S F n} (h : ∀ K, (basisS F n).repr s K = (basisS F n).repr t K) :
    s = t :=
  (basisS F n).repr.injective (Finsupp.ext h)

theorem s10_conjS_smul (a : F) (s : S F n) : conjS c n (a • s) = c a • conjS c n s := by
  apply s10_S_ext
  intro K
  simp [s10_repr_conjS]

theorem s10_conjS_symm_conjS (s : S F n) : conjS c.symm n (conjS c n s) = s := by
  apply s10_S_ext
  intro K
  simp [s10_repr_conjS]

theorem s10_conjS_conjS_symm (s : S F n) : conjS c n (conjS c.symm n s) = s := by
  apply s10_S_ext
  intro K
  simp [s10_repr_conjS]

theorem s10_conjS_injective : Function.Injective (conjS c n) := fun a b h => by
  have := congrArg (conjS c.symm n) h
  rwa [s10_conjS_symm_conjS, s10_conjS_symm_conjS] at this

theorem s10_conjS_basisS (K : Finset (Fin (2 * n))) : conjS c n (basisS F n K) = basisS F n K := by
  apply s10_S_ext
  intro L
  rw [s10_repr_conjS, s10_repr_basisS]
  split_ifs <;> simp

theorem s10_basisS_singleton (i : Fin (2 * n)) :
    basisS F n {i} = ExteriorAlgebra.ι F (e F n i) := by
  rw [basisS, s10_basis_eq_prod]
  simp only [Finset.sort_singleton, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, Pi.basisFun_apply]
  rfl

theorem s10_H1_eq_sum (w : H1 F n) : w = ∑ i, w i • e F n i := by
  ext j
  simp [e, Pi.single_apply]

theorem s10_conjS_ι (w : H1 F n) :
    conjS c n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F (c ∘ w) := by
  conv_lhs => rw [s10_H1_eq_sum w]
  conv_rhs => rw [s10_H1_eq_sum (c ∘ w)]
  simp only [map_sum, map_smul, s10_conjS_smul, ← s10_basisS_singleton, s10_conjS_basisS,
    Function.comp_apply]

theorem s10_dual_apply_eq_sum (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    θ w = ∑ i, w i * θ (e F n i) := by
  conv_lhs => rw [s10_H1_eq_sum w]
  simp [map_sum]

/-- `θ^c(c ∘ w) = c(θ(w))` for `θ^c = Σ c(θ(e_i)) f_i`. -/
theorem s10_conjDual_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    (∑ i, c (θ (e F n i)) • f F n i) (c ∘ w) = c (θ w) := by
  rw [s10_dual_apply_eq_sum θ w, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, f, LinearMap.proj_apply, Function.comp_apply, smul_eq_mul,
    map_mul]
  exact mul_comm _ _

theorem s10_conjS_D (θ : Module.Dual F (H1 F n)) (s : S F n) :
    conjS c n (D F n θ s) = D F n (∑ i, c (θ (e F n i)) • f F n i) (conjS c n s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    have h1 : D F n θ (algebraMap F (S F n) r) = 0 :=
      contractLeft_algebraMap (Q := (0 : QuadraticForm F (H1 F n))) _ r
    have h2 : conjS c n (algebraMap F (S F n) r) = algebraMap F (S F n) (c r) := by
      rw [Algebra.algebraMap_eq_smul_one, s10_conjS_smul, map_one, Algebra.algebraMap_eq_smul_one]
    rw [h1, map_zero, h2]
    exact (contractLeft_algebraMap (Q := (0 : QuadraticForm F (H1 F n))) _ (c r)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x w hx =>
    have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w x
    have h2 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n)))
      (∑ i, c (θ (e F n i)) • f F n i) (c ∘ w) (conjS c n x)
    change conjS c n (D F n θ (ExteriorAlgebra.ι F w * x)) =
      D F n _ (conjS c n (ExteriorAlgebra.ι F w * x))
    change D F n θ (ExteriorAlgebra.ι F w * x) = θ w • x - ExteriorAlgebra.ι F w * D F n θ x at h1
    change D F n _ (ExteriorAlgebra.ι F (c ∘ w) * conjS c n x) = _ • conjS c n x -
      ExteriorAlgebra.ι F (c ∘ w) * D F n _ (conjS c n x) at h2
    rw [h1, map_mul, s10_conjS_ι, h2, map_sub, s10_conjS_smul, map_mul, s10_conjS_ι, hx,
      s10_conjDual_apply]

theorem s10_conjS_m_ι (v : V F n) (s : S F n) :
    conjS c n (m F n (ι (Q F n) v) s) = m F n (ι (Q F n) (conjV c n v)) (conjS c n s) := by
  rw [s10_m_ι_apply, s10_m_ι_apply, map_add, map_mul, s10_conjS_ι, s10_conjS_D]
  rfl

theorem s10_conjV_fst (v : V F n) : (conjV c n v).1 = ∑ i, c (v.1 (e F n i)) • f F n i := rfl

theorem s10_conjV_snd (v : V F n) : (conjV c n v).2 = c ∘ v.2 := rfl

theorem s10_dual_eq_sum (θ : Module.Dual F (H1 F n)) : θ = ∑ i, θ (e F n i) • f F n i := by
  refine LinearMap.ext fun w => ?_
  rw [s10_dual_apply_eq_sum θ w]
  simp [f, mul_comm]

theorem s10_conjV_smul (a : F) (v : V F n) : conjV c n (a • v) = c a • conjV c n v := by
  refine Prod.ext ?_ ?_
  · simp only [s10_conjV_fst, Prod.smul_fst, LinearMap.smul_apply, smul_eq_mul, map_mul,
      Finset.smul_sum, smul_smul]
  · funext i
    simp [s10_conjV_snd]

theorem s10_conjV_symm_conjV (v : V F n) : conjV c.symm n (conjV c n v) = v := by
  refine Prod.ext ?_ ?_
  · rw [s10_conjV_fst, s10_conjV_fst]
    conv_rhs => rw [s10_dual_eq_sum v.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f, e, Pi.single_apply]
  · funext i
    simp [s10_conjV_snd]

theorem s10_conjV_conjV_symm (v : V F n) : conjV c n (conjV c.symm n v) = v := by
  have := s10_conjV_symm_conjV c.symm v
  rwa [RingEquiv.symm_symm] at this

theorem s10_Q_conjV (v : V F n) : Q F n (conjV c n v) = c (Q F n v) := by
  simp only [Q, QuadraticForm.dualProd_apply, s10_conjV_fst, s10_conjV_snd]
  exact s10_conjDual_apply c v.1 v.2

/-- The coordinatewise action of `c` on `S_F`, as a `c`-semilinear map. -/
noncomputable def s10_conjSL : S F n →ₛₗ[(c : F →+* F)] S F n where
  toFun := conjS c n
  map_add' := map_add (conjS c n)
  map_smul' := s10_conjS_smul c

/-- The coordinatewise action of `c` on `V_F`, as a `c`-semilinear map. -/
noncomputable def s10_conjVL : V F n →ₛₗ[(c : F →+* F)] V F n where
  toFun := conjV c n
  map_add' := map_add (conjV c n)
  map_smul' := s10_conjV_smul c

theorem s10_conjSL_apply (s : S F n) : s10_conjSL c s = conjS c n s := rfl

theorem s10_conjVL_apply (v : V F n) : s10_conjVL c v = conjV c n v := rfl

theorem s10_conjS_mem_Splus {s : S F n} (hs : s ∈ Splus F n) : conjS c n s ∈ Splus F n := by
  rw [s10_mem_Splus_iff] at hs ⊢
  intro K hK
  rw [s10_repr_conjS, hs K hK, map_zero]

theorem s10_ann_conjS (u : S F n) :
    ann F n (conjS c n u) = (ann F n u).map (s10_conjVL c) := by
  ext v
  constructor
  · intro hv
    refine Submodule.mem_map.mpr ⟨conjV c.symm n v, ?_, s10_conjV_conjV_symm c v⟩
    rw [ann, LinearMap.mem_ker, s10_mOf_eq]
    apply s10_conjS_injective c
    rw [s10_conjS_m_ι, s10_conjV_conjV_symm, map_zero]
    exact hv
  · rintro ⟨v', hv', rfl⟩
    have hv'' : m F n (ι (Q F n) v') u = 0 := hv'
    rw [ann, LinearMap.mem_ker, s10_mOf_eq, s10_conjVL_apply, ← s10_conjS_m_ι, hv'', map_zero]

theorem s10_finrank_le_map_conjVL (W : Submodule F (V F n)) :
    Module.finrank F W ≤ Module.finrank F (W.map (s10_conjVL c)) := by
  let b := Module.finBasis F W
  have hb : LinearIndependent F (fun i => (b i : V F n)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli : LinearIndependent F (fun i => conjV c n (b i : V F n)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 : ∑ i ∈ s, c.symm (g i) • (b i : V F n) = 0 := by
      have := congrArg (conjV c.symm n) hg
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [s10_conjV_smul, s10_conjV_symm_conjV]
    have := linearIndependent_iff'.mp hb s _ h1 i hi
    simpa using this
  have hmem : ∀ i, conjV c n (b i : V F n) ∈ W.map (s10_conjVL c) :=
    fun i => Submodule.mem_map_of_mem (f := s10_conjVL c) (b i).2
  have hli' : LinearIndependent F (fun i => (⟨conjV c n (b i : V F n), hmem i⟩ :
      W.map (s10_conjVL c))) :=
    LinearIndependent.of_comp (W.map (s10_conjVL c)).subtype hli
  have := hli'.fintype_card_le_finrank
  simpa using this

theorem s10_map_conjVL_symm (W : Submodule F (V F n)) :
    (W.map (s10_conjVL c)).map (s10_conjVL c.symm) = W := by
  ext v
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [s10_conjVL_apply, s10_conjVL_apply, s10_conjV_symm_conjV]
    exact hx
  · intro hv
    exact ⟨conjV c n v, ⟨v, hv, rfl⟩, s10_conjV_symm_conjV c v⟩

theorem s10_finrank_map_conjVL (W : Submodule F (V F n)) :
    Module.finrank F (W.map (s10_conjVL c)) = Module.finrank F W := by
  refine le_antisymm ?_ (s10_finrank_le_map_conjVL c W)
  have := s10_finrank_le_map_conjVL c.symm (W.map (s10_conjVL c))
  rwa [s10_map_conjVL_symm] at this

theorem s10_isEvenPureSpinor_conjS {u : S F n} (hu : IsEvenPureSpinor F n u) :
    IsEvenPureSpinor F n (conjS c n u) := by
  refine ⟨s10_conjS_mem_Splus c hu.1, ?_, ?_⟩
  · intro v hv
    rw [s10_ann_conjS] at hv
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    rw [s10_conjVL_apply, s10_Q_conjV, hu.2.1 v' hv', map_zero]
  · rw [s10_ann_conjS, s10_finrank_map_conjVL]
    exact hu.2.2

/-- Transport of a transversal secant by the coordinatewise action of a field automorphism. -/
theorem s10_isTransversalSecant_conj {P : Submodule F (S F n)} {u₁ u₂ : S F n}
    (h : IsTransversalSecant F n P u₁ u₂) :
    IsTransversalSecant F n (P.map (s10_conjSL c)) (conjS c n u₁) (conjS c n u₂) := by
  obtain ⟨hP, hli, h₁, h₂, hW, hpure⟩ := h
  refine ⟨?_, ?_, s10_isEvenPureSpinor_conjS c h₁, s10_isEvenPureSpinor_conjS c h₂, ?_, ?_⟩
  · rw [hP, Submodule.map_span, Set.image_pair]
    rfl
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro a b hab
    have h := congrArg (conjS c.symm n) hab
    rw [map_add, s10_conjS_smul, s10_conjS_smul, s10_conjS_symm_conjS, s10_conjS_symm_conjS,
      map_zero] at h
    obtain ⟨ha, hb⟩ := hli _ _ h
    exact ⟨by simpa using ha, by simpa using hb⟩
  · rw [s10_ann_conjS, s10_ann_conjS, ← Submodule.map_inf _ ?_, hW, Submodule.map_bot]
    intro x y hxy
    have := congrArg (conjV c.symm n) hxy
    rwa [s10_conjVL_apply, s10_conjVL_apply, s10_conjV_symm_conjV, s10_conjV_symm_conjV] at this
  · intro u hu hupure
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    have hu'p : IsEvenPureSpinor F n u' := by
      have := s10_isEvenPureSpinor_conjS c.symm hupure
      rwa [s10_conjSL_apply, s10_conjS_symm_conjS] at this
    rcases hpure u' hu' hu'p with h | h
    · left
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
      rw [s10_conjSL_apply, s10_conjS_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · right
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
      rw [s10_conjSL_apply, s10_conjS_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The action of `c` fixes the classes defined over `ℚ`. -/
theorem s10_conjS_bcS (w : S ℚ n) : conjS c n (bcS ℚ F n w) = bcS ℚ F n w := by
  apply s10_S_ext
  intro K
  rw [s10_repr_conjS, s10_repr_bcS]
  simp

/-- The action of `c` fixes every subspace of `S_F` defined over `ℚ`. -/
theorem s10_map_conjSL_bcSubS (P₀ : Submodule ℚ (S ℚ n)) :
    (bcSubS ℚ F n P₀).map (s10_conjSL c) = bcSubS ℚ F n P₀ := by
  rw [bcSubS, Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => s10_conjS_bcS c x

end S10Conj

section S10Lines

theorem s10_span_singleton_eq_of_mem {F : Type*} [Field F] {M : Type*} [AddCommGroup M]
    [Module F M] {x y : M} (hx : x ≠ 0) (h : x ∈ Submodule.span F {y}) :
    Submodule.span F {x} = Submodule.span F {y} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
  have ha : a ≠ 0 := by rintro rfl; exact hx (zero_smul _ _)
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) y

theorem s10_not_mem_span_of_li {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {x₁ x₂ : M} (hx : LinearIndependent F ![x₁, x₂]) : x₂ ∉ Submodule.span F {x₁} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have := (LinearIndependent.pair_iff.mp hx a (-1) (by rw [ha, neg_one_smul, add_neg_cancel])).2
  exact one_ne_zero (neg_eq_zero.mp this)

/-- Two independent vectors lying on the lines `F y₁ ∪ F y₂` (with `y₁, y₂` independent) span the
same two lines. -/
theorem s10_pair_lines_eq {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {x₁ x₂ y₁ y₂ : M} (hx : LinearIndependent F ![x₁, x₂])
    (h₁ : x₁ ∈ Submodule.span F {y₁} ∨ x₁ ∈ Submodule.span F {y₂})
    (h₂ : x₂ ∈ Submodule.span F {y₁} ∨ x₂ ∈ Submodule.span F {y₂}) :
    ({Submodule.span F {x₁}, Submodule.span F {x₂}} : Set (Submodule F M)) =
      {Submodule.span F {y₁}, Submodule.span F {y₂}} := by
  have hx₁ : x₁ ≠ 0 := hx.ne_zero 0
  have hx₂ : x₂ ≠ 0 := hx.ne_zero 1
  have hn := s10_not_mem_span_of_li hx
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exfalso
    apply hn
    rw [s10_span_singleton_eq_of_mem hx₁ h₁]
    exact h₂
  · rw [s10_span_singleton_eq_of_mem hx₁ h₁, s10_span_singleton_eq_of_mem hx₂ h₂]
  · rw [s10_span_singleton_eq_of_mem hx₁ h₁, s10_span_singleton_eq_of_mem hx₂ h₂, Set.pair_comm]
  · exfalso
    apply hn
    rw [s10_span_singleton_eq_of_mem hx₁ h₁]
    exact h₂

theorem s10_bcS_mem_Splus {F : Type*} [Field F] [CharZero F] {n : ℕ} {w : S ℚ n}
    (hw : w ∈ Splus ℚ n) : bcS ℚ F n w ∈ Splus F n := by
  rw [s10_mem_Splus_iff] at hw ⊢
  intro K hK
  rw [s10_repr_bcS, hw K hK, map_zero]

theorem s10_J_bcS_ne_zero {F : Type*} [Field F] [CharZero F] {w : S ℚ 3} (hJ : J ℚ w ≠ 0) :
    J F (bcS ℚ F 3 w) ≠ 0 := by
  rw [J_bcS]
  exact (map_ne_zero_iff _ (algebraMap ℚ F).injective).mpr hJ

end S10Lines

section S10BasisPure

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The number of inversions `#{(x, y) ∈ s × t : y < x}`. -/
def s10_inv (s t : Finset (Fin (2 * n))) : ℕ := ∑ x ∈ s, (t.filter (· < x)).card

theorem s10_inv_insert_left {a : Fin (2 * n)} {s : Finset (Fin (2 * n))} (ha : a ∉ s)
    (t : Finset (Fin (2 * n))) :
    s10_inv (insert a s) t = (t.filter (· < a)).card + s10_inv s t := by
  rw [s10_inv, Finset.sum_insert ha, s10_inv]

/-- The product of two basis vectors: `e_s ∧ e_t = (-1)^{inv(s,t)} e_{s ∪ t}` if `s, t` are
disjoint, `0` otherwise. -/
theorem s10_basisS_mul_basisS (s t : Finset (Fin (2 * n))) :
    basisS F n s * basisS F n t =
      if Disjoint s t then (-1 : F) ^ s10_inv s t • basisS F n (s ∪ t) else 0 := by
  induction s using Finset.induction_on_min with
  | empty =>
    simp [s10_basisS_empty, s10_inv]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [basisS, s10_basis_insert_min _ a s ha, ← basisS, mul_assoc, ih]
    by_cases hst : Disjoint s t
    · rw [ite_eq_left hst, mul_smul_comm, show (Pi.basisFun F (Fin (2 * n))) a = e F n a by
        rw [Pi.basisFun_apply]; rfl, s10_ι_e_mul_basisS]
      by_cases hat : a ∈ t
      · have : ¬Disjoint (insert a s) t := by
          rw [Finset.disjoint_left]; push Not; exact ⟨a, Finset.mem_insert_self _ _, hat⟩
        rw [ite_eq_left (Finset.mem_union_right _ hat), ite_eq_right this, smul_zero]
      · have hd : Disjoint (insert a s) t := by
          rw [Finset.disjoint_insert_left]; exact ⟨hat, hst⟩
        have hnot : a ∉ s ∪ t := by simp [has, hat]
        have hf : (s ∪ t).filter (· < a) = t.filter (· < a) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hx | hx, hxa⟩
            · exact absurd hxa (lt_asymm (ha x hx))
            · exact ⟨hx, hxa⟩
          · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
        rw [ite_eq_right hnot, ite_eq_left hd, hf, smul_smul, ← pow_add,
          s10_inv_insert_left has, Finset.insert_union, add_comm]
    · have : ¬Disjoint (insert a s) t := by
        rw [Finset.disjoint_insert_left]; exact fun h => hst h.2
      rw [ite_eq_right hst, ite_eq_right this, mul_zero]

theorem s10_integral_basisS (K : Finset (Fin (2 * n))) :
    integral F n (basisS F n K) = if K = Finset.univ then 1 else 0 := by
  rw [integral, Module.Basis.coord_apply, s10_repr_basisS]

/-- `τ(e_M) = ± e_M`. -/
theorem s10_tau_basisS (M : Finset (Fin (2 * n))) :
    ∃ ε : F, ε ≠ 0 ∧ tau F n (basisS F n M) = ε • basisS F n M := by
  induction M using Finset.induction_on_min with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [s10_basisS_empty, one_smul]
    exact CliffordAlgebra.reverse.map_one
  | insert a M ha ih =>
    obtain ⟨ε, hε, hM⟩ := ih
    have has : a ∉ M := fun h => lt_irrefl a (ha a h)
    have hins : basisS F n (insert a M) = ExteriorAlgebra.ι F (e F n a) * basisS F n M := by
      rw [basisS, s10_basis_insert_min _ a M ha, ← basisS]
      congr 1
      rw [Pi.basisFun_apply]; rfl
    -- `e_M ∧ e_a = (-1)^{|M|} e_a ∧ e_M`
    have hcomm : basisS F n M * ExteriorAlgebra.ι F (e F n a) =
        (-1 : F) ^ M.card • basisS F n (insert a M) := by
      rw [← s10_basisS_singleton, s10_basisS_mul_basisS, ite_eq_left (Finset.disjoint_singleton_right.mpr has)]
      have hinv : s10_inv M {a} = M.card := by
        rw [s10_inv]
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.filter_singleton, ite_eq_left (ha x hx), Finset.card_singleton]
      rw [hinv, Finset.union_singleton]
    refine ⟨ε * (-1) ^ M.card, mul_ne_zero hε (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)), ?_⟩
    have htau : ∀ x, tau F n x = CliffordAlgebra.reverse (Q := (0 : QuadraticForm F (H1 F n))) x :=
      fun x => rfl
    rw [hins, htau, CliffordAlgebra.reverse.map_mul, show CliffordAlgebra.reverse
      (Q := (0 : QuadraticForm F (H1 F n))) (ExteriorAlgebra.ι F (e F n a)) =
      ExteriorAlgebra.ι F (e F n a) from CliffordAlgebra.reverse_ι _, ← htau, hM, smul_mul_assoc,
      hcomm, smul_smul, ← hins]

theorem s10_mukai_apply (s t : S F n) : mukai F n s t = integral F n (tau F n s * t) := rfl

/-- The Mukai pairing against a basis vector picks the complementary coordinate:
`(s, e_L)_S = ± s_{Lᶜ}`. -/
theorem s10_mukai_basisS (s : S F n) (L : Finset (Fin (2 * n))) :
    ∃ c : F, c ≠ 0 ∧ mukai F n s (basisS F n L) = c * (basisS F n).repr s Lᶜ := by
  have hpair : ∀ M : Finset (Fin (2 * n)), M ≠ Lᶜ → mukai F n (basisS F n M) (basisS F n L) = 0 := by
    intro M hM
    obtain ⟨ε, -, hε⟩ := s10_tau_basisS (F := F) M
    rw [s10_mukai_apply, hε, smul_mul_assoc, s10_basisS_mul_basisS, map_smul]
    split_ifs with hd
    · rw [map_smul, s10_integral_basisS, ite_eq_right, smul_zero, smul_zero]
      intro hu
      apply hM
      ext x
      simp only [Finset.mem_compl]
      constructor
      · intro hxM hxL
        exact Finset.disjoint_left.mp hd hxM hxL
      · intro hxL
        have : x ∈ M ∪ L := by rw [hu]; exact Finset.mem_univ x
        rcases Finset.mem_union.mp this with h | h
        · exact h
        · exact absurd h hxL
    · rw [map_zero, smul_zero]
  obtain ⟨ε, hε, hτ⟩ := s10_tau_basisS (F := F) Lᶜ
  have hd : Disjoint Lᶜ L := disjoint_compl_left
  refine ⟨ε * (-1 : F) ^ s10_inv Lᶜ L, mul_ne_zero hε (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
    ?_⟩
  conv_lhs => rw [← (basisS F n).sum_repr s]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single Lᶜ]
  · rw [map_smul, LinearMap.smul_apply, s10_mukai_apply, hτ, smul_mul_assoc,
      s10_basisS_mul_basisS, ite_eq_left hd, map_smul, map_smul,
      show Lᶜ ∪ L = Finset.univ by ext x; by_cases hx : x ∈ L <;> simp [hx],
      s10_integral_basisS, ite_eq_left rfl, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  · intro M _ hM
    rw [map_smul, LinearMap.smul_apply, hpair M hM, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The vector `v_k = (f_k, e_k)` with `Q(v_k) = 1`. -/
noncomputable def s10_vk (k : Fin (2 * n)) : V F n := (f F n k, e F n k)

theorem s10_Q_vk (k : Fin (2 * n)) : Q F n (s10_vk k) = 1 := by
  simp [s10_vk, f, e]

/-- `g_{ab} = v_a v_b ∈ Spin(V_F)`. -/
noncomputable def s10_gab (a b : Fin (2 * n)) : Spin F n :=
  ⟨ι (Q F n) (s10_vk a) * ι (Q F n) (s10_vk b),
    CliffordAlgebra.ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _
      (by rw [s10_Q_vk, s10_Q_vk, mul_one])⟩

/-- `θ ⌋ e_K = 0` when `θ` vanishes on the `e_k`, `k ∈ K`. -/
theorem s10_D_basisS_eq_zero (θ : Module.Dual F (H1 F n)) (K : Finset (Fin (2 * n)))
    (h : ∀ k ∈ K, θ (e F n k) = 0) : D F n θ (basisS F n K) = 0 := by
  induction K using Finset.induction_on_min with
  | empty =>
    rw [s10_basisS_empty]
    exact contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) _
  | insert a K ha ih =>
    rw [basisS, s10_basis_insert_min _ a K ha, ← basisS]
    have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ
      ((Pi.basisFun F (Fin (2 * n))) a) (basisS F n K)
    change D F n θ _ = _ at h1
    have ih' : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ
        (basisS F n K) = 0 := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    rw [h1, ih']
    have : θ ((Pi.basisFun F (Fin (2 * n))) a) = 0 := by
      rw [Pi.basisFun_apply]; exact h a (Finset.mem_insert_self _ _)
    rw [this, zero_smul, mul_zero, sub_zero]

theorem s10_m_vk_basisS {k : Fin (2 * n)} {K : Finset (Fin (2 * n))} (hk : k ∉ K) :
    m F n (ι (Q F n) (s10_vk k)) (basisS F n K) =
      (-1 : F) ^ (K.filter (· < k)).card • basisS F n (insert k K) := by
  rw [s10_m_ι_apply]
  simp only [s10_vk]
  rw [s10_D_basisS_eq_zero, add_zero, s10_ι_e_mul_basisS, ite_eq_right hk]
  intro j hj
  simp only [f, e, LinearMap.proj_apply, Pi.single_apply]
  rw [ite_eq_right]
  rintro rfl
  exact hk hj

/-- The basis vectors `e_L`, `|L|` even, are even pure spinors. -/
theorem s10_isEvenPureSpinor_basisS (L : Finset (Fin (2 * n))) (hL : Even L.card) :
    IsEvenPureSpinor F n (basisS F n L) := by
  obtain ⟨r, hr⟩ := hL
  induction r generalizing L with
  | zero =>
    have : L = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [this, s10_basisS_empty]
    exact s10_isEvenPureSpinor_one F n
  | succ r ih =>
    have hne : L.Nonempty := Finset.card_pos.mp (by omega)
    set a := L.min' hne
    have haL : a ∈ L := L.min'_mem hne
    have hne' : (L.erase a).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haL]; omega)
    set b := (L.erase a).min' hne'
    have hbL : b ∈ L.erase a := (L.erase a).min'_mem hne'
    set K := (L.erase a).erase b
    have hK : K.card = r + r := by
      rw [Finset.card_erase_of_mem hbL, Finset.card_erase_of_mem haL]; omega
    have hbK : b ∉ K := Finset.notMem_erase _ _
    have haK : a ∉ insert b K := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact (Finset.mem_erase.mp hbL).1 h.symm
      · exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)
    have hL' : insert a (insert b K) = L := by
      rw [Finset.insert_erase hbL, Finset.insert_erase haL]
    have hpK := ih K hK
    have hm : m F n (s10_gab (F := F) a b : C F n) (basisS F n K) =
        ((-1 : F) ^ ((insert b K).filter (· < a)).card * (-1 : F) ^ (K.filter (· < b)).card) •
          basisS F n (insert a (insert b K)) := by
      rw [show (s10_gab (F := F) a b : C F n) = ι (Q F n) (s10_vk a) * ι (Q F n) (s10_vk b) from rfl,
        map_mul, Module.End.mul_apply, s10_m_vk_basisS hbK, map_smul, s10_m_vk_basisS haK, smul_smul]
      congr 1
      ring
    have hpure := s10_isEvenPureSpinor_m (s10_gab (F := F) a b) hpK
    rw [hm] at hpure
    have hu : ((-1 : F) ^ ((insert b K).filter (· < a)).card * (-1 : F) ^ (K.filter (· < b)).card)
        ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
          (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have := s10_isEvenPureSpinor_smul (inv_ne_zero hu) hpure
    rw [smul_smul, inv_mul_cancel₀ hu, one_smul, hL'] at this
    exact this

/-- **Every even pure spinor is a multiple of a `Spin(V)`-translate of `1`** ([Chevalley, III.1.4,
III.2.4, §3.3 Lemma 1]): the partner `e_L`, `L = Kᶜ` with `u_K ≠ 0`, is transversal to `u`. -/
theorem s10_pure_eq_smul_m_one (hn : 0 < n) {u : S F n} (hu : IsEvenPureSpinor F n u) :
    ∃ g : Spin F n, ∃ c : F, c ≠ 0 ∧ u = c • m F n (g : C F n) 1 := by
  have hu0 : u ≠ 0 := hu.ne_zero hn
  obtain ⟨K, hK⟩ : ∃ K, (basisS F n).repr u K ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    exact (basisS F n).repr.injective (Finsupp.ext fun K => by simpa using h K)
  have hKe : Even K.card := by
    by_contra hodd
    exact hK ((s10_mem_Splus_iff u).mp hu.1 K hodd)
  have hLe : Even (Kᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    obtain ⟨r, hr⟩ := hKe
    exact ⟨n - r, by omega⟩
  have hpL := s10_isEvenPureSpinor_basisS (F := F) Kᶜ hLe
  obtain ⟨c, hc, hmuk⟩ := s10_mukai_basisS u Kᶜ
  rw [compl_compl] at hmuk
  have htrans : ann F n u ⊓ ann F n (basisS F n Kᶜ) = ⊥ := by
    by_contra h
    have := (chevalley_III_2_4 F n hn u _ hu hpL).mpr h
    rw [hmuk] at this
    exact mul_ne_zero hc hK this
  obtain ⟨g, hg₁, -⟩ := chevalley_sec3_3_lemma1 F n 1 (pt F n) u (basisS F n Kᶜ)
    (s10_isEvenPureSpinor_one F n) (s10_isEvenPureSpinor_pt F n) hu hpL
    (s10_ann_one_inf_ann_pt F n) htrans
  have hann : ann F n u = ann F n (m F n (g : C F n) 1) := by
    rw [ann_m_spin, hg₁]
  have hmax := (s10_isEvenPureSpinor_m g (s10_isEvenPureSpinor_one F n)).2
  have hne : m F n (g : C F n) 1 ≠ 0 :=
    (s10_isEvenPureSpinor_m g (s10_isEvenPureSpinor_one F n)).ne_zero hn
  obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp
    (chevalley_III_1_4_unique F n _ u hne hmax hann)
  refine ⟨g, c', ?_, rfl⟩
  rintro rfl
  exact hu0 (zero_smul _ _)

end S10BasisPure

section S10Singular

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F]

/-- `J` only reads the coordinates of the even part. -/
theorem s10_J_congr {x y : S F 3}
    (h : ∀ K : Finset (Fin 6), Even K.card → (basisS F 3).repr x K = (basisS F 3).repr y K) :
    J F x = J F y := by
  have hpair : ∀ i j : Fin 6, i ≠ j → Even ({i, j} : Finset (Fin 6)).card := by
    intro i j hij
    rw [Finset.card_pair hij]
    exact even_two
  have hcpair : ∀ i j : Fin 6, i ≠ j → Even ({i, j}ᶜ : Finset (Fin 6)).card := by
    intro i j hij
    rw [s10_card_compl_pair hij]
    exact ⟨2, rfl⟩
  have hx0 : x0 F x = x0 F y := h _ (by simp)
  have hy0 : y0 F x = y0 F y := h _ (by rw [Finset.card_univ, Fintype.card_fin]; exact ⟨3, rfl⟩)
  have hxC : ∀ i j : Fin 6, i ≠ j → xCoord F x i j = xCoord F y i j := fun i j hij =>
    h _ (hpair i j hij)
  have hyC : ∀ i j : Fin 6, i ≠ j → yCoord F x i j = yCoord F y i j := fun i j hij => by
    rw [yCoord, yCoord, h _ (hcpair i j hij)]
  have hxM : xMat F x = xMat F y := by
    ext i j
    simp only [xMat, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hxC i j h1.ne
    · rw [hxC j i h2.ne]
    · rfl
  have hyM : yMat F x = yMat F y := by
    ext i j
    simp only [yMat, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hyC i j h1.ne
    · rw [hyC j i h2.ne]
    · rfl
  have hsum : ∑ p : Pair6, xCoord F x p.1.1 p.1.2 * yCoord F x p.1.1 p.1.2 =
      ∑ p : Pair6, xCoord F y p.1.1 p.1.2 * yCoord F y p.1.1 p.1.2 :=
    Finset.sum_congr rfl fun p _ => by rw [hxC _ _ p.2.ne, hyC _ _ p.2.ne]
  simp only [J, hx0, hy0, hxM, hyM, hsum]

/-- The even part `x⁺ = Σ_{|K| even} x_K e_K` of `x ∈ S`. -/
noncomputable def s10_evenPart (x : S F 3) : S F 3 :=
  ∑ K, (if Even K.card then (basisS F 3).repr x K else 0) • basisS F 3 K

theorem s10_repr_evenPart (x : S F 3) (K : Finset (Fin 6)) :
    (basisS F 3).repr (s10_evenPart x) K = if Even K.card then (basisS F 3).repr x K else 0 := by
  rw [s10_evenPart, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem s10_evenPart_mem (x : S F 3) : s10_evenPart x ∈ Splus F 3 := by
  rw [s10_mem_Splus_iff]
  intro K hK
  rw [s10_repr_evenPart, ite_eq_right hK]

/-- `J(1 + s y) = s² R(s)` with `R` an explicit polynomial in `s`: the quartic `J` vanishes to order
`2` at the pure spinor `1`. -/
theorem s10_J_one_add_smul (y : S F 3) (s : F) :
    J F (1 + s • y) = s ^ 2 * ((1 + s * x0 F y) * s * pf6 (yMat F y) +
      s ^ 2 * y0 F y * pf6 (xMat F y) +
      s ^ 2 * ∑ p : Pair6, pf4 (crossOut (xMat F y) p) * pf4 (crossOut (yMat F y) p) -
      (1 / 4) * ((1 + s * x0 F y) * y0 F y -
        s * ∑ p : Pair6, xCoord F y p.1.1 p.1.2 * yCoord F y p.1.1 p.1.2) ^ 2) := by
  have hr : ∀ K, (basisS F 3).repr (1 + s • y) K =
      (if K = ∅ then 1 else 0) + s * (basisS F 3).repr y K := by
    intro K
    rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s10_repr_one, smul_eq_mul]
  have hx0 : x0 F (1 + s • y) = 1 + s * x0 F y := by rw [x0, hr, ite_eq_left rfl]; rfl
  have hy0 : y0 F (1 + s • y) = s * y0 F y := by
    rw [y0, hr, ite_eq_right Finset.univ_nonempty.ne_empty, zero_add]; rfl
  have hxC : ∀ i j, xCoord F (1 + s • y) i j = s * xCoord F y i j := fun i j => by
    rw [xCoord, hr, ite_eq_right (s10_pair_ne_empty i j), zero_add]; rfl
  have hyC : ∀ i j, yCoord F (1 + s • y) i j = s * yCoord F y i j := fun i j => by
    rw [yCoord, hr, ite_eq_right (s10_compl_pair_ne_empty i j), zero_add, yCoord]; ring
  have hxM : xMat F (1 + s • y) = s • xMat F y := by
    ext i j
    simp only [xMat, Matrix.of_apply, Matrix.smul_apply, hxC, smul_eq_mul]
    split_ifs <;> ring
  have hyM : yMat F (1 + s • y) = s • yMat F y := by
    ext i j
    simp only [yMat, Matrix.of_apply, Matrix.smul_apply, hyC, smul_eq_mul]
    split_ifs <;> ring
  simp only [J, hx0, hy0, hxM, hyM, s10_crossOut_smul, s10_pf6_smul, s10_pf4_smul, hxC, hyC]
  have e1 : ∑ p : Pair6, s ^ 2 * pf4 (crossOut (xMat F y) p) * (s ^ 2 * pf4 (crossOut (yMat F y) p))
      = s ^ 4 * ∑ p : Pair6, pf4 (crossOut (xMat F y) p) * pf4 (crossOut (yMat F y) p) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : ∑ p : Pair6, s * xCoord F y p.1.1 p.1.2 * (s * yCoord F y p.1.1 p.1.2) =
      s ^ 2 * ∑ p : Pair6, xCoord F y p.1.1 p.1.2 * yCoord F y p.1.1 p.1.2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1, e2]
  ring

end S10Singular

section S10Quartic

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R]

/-- The coordinate `y_ij` of (10.1.1), for an abstract coordinate function `c`. -/
noncomputable def s10_yCc (c : Finset (Fin 6) → R) (i j : Fin 6) : R :=
  (-1 : R) ^ ((i : ℕ) + j + 1) * c ({i, j}ᶜ)

/-- The matrix `(x_ij)` of (10.1.1), for an abstract coordinate function `c`. -/
noncomputable def s10_xMatc (c : Finset (Fin 6) → R) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun i j => if i < j then c {i, j} else if j < i then -c {j, i} else 0

/-- The matrix `(y_ij)` of (10.1.1), for an abstract coordinate function `c`. -/
noncomputable def s10_yMatc (c : Finset (Fin 6) → R) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun i j => if i < j then s10_yCc c i j else if j < i then -s10_yCc c j i else 0

/-- The formula (10.1.1) for `J`, as a polynomial expression in abstract coordinates `c` over any
commutative ring (with `k` in place of `1/4`). -/
noncomputable def s10_Jc (k : R) (c : Finset (Fin 6) → R) : R :=
  c ∅ * pf6 (s10_yMatc c) + c Finset.univ * pf6 (s10_xMatc c) +
      ∑ p : Pair6, pf4 (crossOut (s10_xMatc c) p) * pf4 (crossOut (s10_yMatc c) p) -
    k * (c ∅ * c Finset.univ - ∑ p : Pair6, c {p.1.1, p.1.2} * s10_yCc c p.1.1 p.1.2) ^ 2

theorem s10_J_eq_Jc (F : Type*) [Field F] [CharZero F] (x : S F 3) :
    J F x = s10_Jc (1 / 4 : F) ((basisS F 3).repr x) := rfl

theorem s10_Jc_map {R' : Type*} [CommRing R'] (f : R →+* R') (k : R) (c : Finset (Fin 6) → R) :
    f (s10_Jc k c) = s10_Jc (f k) (fun K => f (c K)) := by
  have hyC : ∀ i j, f (s10_yCc c i j) = s10_yCc (fun K => f (c K)) i j := by
    intro i j
    simp [s10_yCc]
  have hx : (s10_xMatc c).map f = s10_xMatc (fun K => f (c K)) := by
    ext i j
    simp only [s10_xMatc, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hy : (s10_yMatc c).map f = s10_yMatc (fun K => f (c K)) := by
    ext i j
    simp only [s10_yMatc, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [hyC]
  simp only [s10_Jc, map_sub, map_add, map_mul, map_sum, map_pow, ← s10_pf6_map,
    ← s10_pf4_map, ← s10_crossOut_map, hx, hy, hyC]

variable {σ F : Type*} [Field F]

theorem s10_pf4_isHomogeneous {A : Matrix (Fin 4) (Fin 4) (MvPolynomial σ F)}
    (hA : ∀ i j, (A i j).IsHomogeneous 1) : (pf4 A).IsHomogeneous 2 :=
  (((hA 0 2).mul (hA 1 3)).sub ((hA 0 1).mul (hA 2 3))).sub ((hA 0 3).mul (hA 1 2))

theorem s10_pf6_isHomogeneous {A : Matrix (Fin 6) (Fin 6) (MvPolynomial σ F)}
    (hA : ∀ i j, (A i j).IsHomogeneous 1) : (pf6 A).IsHomogeneous 3 := by
  rw [s10_pf6_expand]
  have h2 : ∀ a b c d e g k l p q r t : Fin 6,
      (A a b * A c d - A e g * A k l - A p q * A r t).IsHomogeneous 2 := by
    intro a b c d e g k l p q r t
    exact (((hA a b).mul (hA c d)).sub ((hA e g).mul (hA k l))).sub ((hA p q).mul (hA r t))
  have t1 := (hA 0 1).mul (h2 2 4 3 5 2 3 4 5 2 5 3 4)
  have t2 := (hA 0 2).mul (h2 1 4 3 5 1 3 4 5 1 5 3 4)
  have t3 := (hA 0 3).mul (h2 1 4 2 5 1 2 4 5 1 5 2 4)
  have t4 := (hA 0 4).mul (h2 1 3 2 5 1 2 3 5 1 5 2 3)
  have t5 := (hA 0 5).mul (h2 1 3 2 4 1 2 3 4 1 4 2 3)
  exact (((t1.sub t2).add t3).sub t4).add t5

/-- `J` is a homogeneous quartic polynomial in the coordinates. -/
theorem s10_Jc_isHomogeneous (k : F) (c : Finset (Fin 6) → MvPolynomial σ F)
    (hc : ∀ K, (c K).IsHomogeneous 1) :
    (s10_Jc (MvPolynomial.C k) c).IsHomogeneous 4 := by
  have hyC : ∀ i j, (s10_yCc c i j).IsHomogeneous 1 := by
    intro i j
    rw [s10_yCc, show ((-1 : MvPolynomial σ F) ^ ((i : ℕ) + j + 1)) =
      MvPolynomial.C ((-1 : F) ^ ((i : ℕ) + j + 1)) by simp]
    exact (hc _).C_mul _
  have hxM : ∀ i j, (s10_xMatc c i j).IsHomogeneous 1 := by
    intro i j
    simp only [s10_xMatc, Matrix.of_apply]
    split_ifs
    · exact hc _
    · exact (hc _).neg
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hyM : ∀ i j, (s10_yMatc c i j).IsHomogeneous 1 := by
    intro i j
    simp only [s10_yMatc, Matrix.of_apply]
    split_ifs
    · exact hyC _ _
    · exact (hyC _ _).neg
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcross : ∀ (A : Matrix (Fin 6) (Fin 6) (MvPolynomial σ F)) (p : Pair6),
      (∀ i j, (A i j).IsHomogeneous 1) → ∀ i j, (crossOut A p i j).IsHomogeneous 1 :=
    fun A p hA i j => hA _ _
  have hsum1 : (∑ p : Pair6, pf4 (crossOut (s10_xMatc c) p) *
      pf4 (crossOut (s10_yMatc c) p)).IsHomogeneous 4 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun p _ =>
      (s10_pf4_isHomogeneous (hcross _ p hxM)).mul (s10_pf4_isHomogeneous (hcross _ p hyM))
  have hsum2 : (∑ p : Pair6, c {p.1.1, p.1.2} * s10_yCc c p.1.1 p.1.2).IsHomogeneous 2 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun p _ => (hc _).mul (hyC _ _)
  have hsq : MvPolynomial.IsHomogeneous
      ((c ∅ * c Finset.univ - ∑ p : Pair6, c {p.1.1, p.1.2} * s10_yCc c p.1.1 p.1.2) ^ 2) 4 :=
    (((hc _).mul (hc _)).sub hsum2).pow 2
  exact ((((hc ∅).mul (s10_pf6_isHomogeneous hyM)).add ((hc _).mul (s10_pf6_isHomogeneous hxM))).add
    hsum1).sub (hsq.C_mul k)

/-- A binary quartic form: a homogeneous polynomial of degree `4` in two variables evaluates to
`Σ_{i ≤ 4} q_i a^i b^{4-i}`. -/
theorem s10_eval_isHomogeneous_four (P : MvPolynomial (Fin 2) F) (hP : P.IsHomogeneous 4) :
    ∃ q : Fin 5 → F, ∀ a b : F,
      MvPolynomial.eval ![a, b] P = ∑ i : Fin 5, q i * a ^ (i : ℕ) * b ^ (4 - (i : ℕ)) := by
  let mo : Fin 5 → (Fin 2 →₀ ℕ) := fun i =>
    Finsupp.single (0 : Fin 2) (i : ℕ) + Finsupp.single (1 : Fin 2) (4 - (i : ℕ))
  have hmo0 : ∀ i, mo i 0 = i := fun i => by
    simp only [mo, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero]
  have hmo1 : ∀ i, mo i 1 = 4 - i := fun i => by
    simp only [mo, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
  have hinj : Function.Injective mo := by
    intro i j h
    have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    simp only [hmo0] at this
    exact Fin.ext this
  refine ⟨fun i => P.coeff (mo i), fun a b => ?_⟩
  rw [MvPolynomial.eval_eq']
  have hsub : P.support ⊆ Finset.univ.image mo := by
    intro d hd
    have hdeg : d.degree = 4 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero h)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    refine Finset.mem_image.mpr ⟨⟨d 0, by omega⟩, Finset.mem_univ _, ?_⟩
    ext j
    fin_cases j
    · simp [hmo0]
    · simp [hmo1]; omega
  rw [Finset.sum_subset hsub, Finset.sum_image (fun i _ j _ h => hinj h)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_two, hmo0, hmo1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

end S10Quartic

/-- The proof of `remark10_1_2_singular` (stated here so that `remark10_1_2_secant` can use it). -/
theorem s10_singular (u : S ℂ 3) (hu : IsEvenPureSpinor ℂ 3 u) :
    J ℂ u = 0 ∧ ∀ x : S ℂ 3, HasDerivAt (fun t : ℂ => J ℂ (u + t • x)) 0 0 := by
  -- every even pure spinor is `c · m_g(1)` ([Chevalley]); `J` is invariant ([Igusa, Prop. 3]) and
  -- vanishes to second order at `1` (formula (10.1.1))
  obtain ⟨g, c, hc, rfl⟩ := s10_pure_eq_smul_m_one (by norm_num) hu
  have key : ∀ x : S ℂ 3, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ t : ℂ, J ℂ (c • m ℂ 3 (g : C ℂ 3) 1 + t • x) = t ^ 2 * G t := by
    intro x
    set y := m ℂ 3 ((g⁻¹ : Spin ℂ 3) : C ℂ 3) (s10_evenPart x) with hy
    have hyS : y ∈ Splus ℂ 3 := s10_m_spin_mem_Splus _ (s10_evenPart_mem x)
    refine ⟨fun t => c ^ 2 * ((1 + t / c * x0 ℂ y) * (t / c) * pf6 (yMat ℂ y) +
      (t / c) ^ 2 * y0 ℂ y * pf6 (xMat ℂ y) +
      (t / c) ^ 2 * ∑ p : Pair6, pf4 (crossOut (xMat ℂ y) p) * pf4 (crossOut (yMat ℂ y) p) -
      (1 / 4) * ((1 + t / c * x0 ℂ y) * y0 ℂ y -
        t / c * ∑ p : Pair6, xCoord ℂ y p.1.1 p.1.2 * yCoord ℂ y p.1.1 p.1.2) ^ 2), ?_, ?_⟩
    · fun_prop
    · intro t
      -- only the even part of `x` matters
      have h1 : J ℂ (c • m ℂ 3 (g : C ℂ 3) 1 + t • x) =
          J ℂ (c • m ℂ 3 (g : C ℂ 3) 1 + t • s10_evenPart x) := by
        apply s10_J_congr
        intro K hK
        simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s10_repr_evenPart,
          ite_eq_left hK]
      have h2 : c • m ℂ 3 (g : C ℂ 3) 1 + t • s10_evenPart x =
          m ℂ 3 (g : C ℂ 3) (c • (1 + (t / c) • y)) := by
        rw [map_smul, map_add, map_smul, hy, s10_m_m_inv, smul_add, smul_smul,
          mul_div_cancel₀ t hc]
      rw [h1, h2, igusa_prop3_invariant ℂ g _, J_smul, s10_J_one_add_smul]
      field_simp
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨G, -, hG⟩ := key 0
    have := hG 0
    simp only [zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at this
    exact this
  · obtain ⟨G, hGd, hG⟩ := key x
    have hd : HasDerivAt (fun t : ℂ => t ^ 2 * G t) 0 0 :=
      ((hasDerivAt_pow 2 (0 : ℂ)).mul (hGd 0).hasDerivAt).congr_deriv (by norm_num)
    have hfun : (fun t : ℂ => J ℂ (c • m ℂ 3 (g : C ℂ 3) 1 + t • x)) = fun t => t ^ 2 * G t :=
      funext hG
    rw [hfun]
    exact hd

section S10BC

set_option linter.unusedSectionVars false

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

theorem s10_bcDual_apply_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  rw [s10_dual_apply_eq_sum θ w, map_sum]
  show (∑ i, algebraMap F F' (θ (e F n i)) • f F' n i) (bcH1 F F' n w) = _
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, f, LinearMap.proj_apply, bcH1, smul_eq_mul,
    LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_mul]
  exact mul_comm _ _

theorem s10_bcS_D (θ : Module.Dual F (H1 F n)) (s : S F n) :
    bcS F F' n (D F n θ s) = D F' n (bcDual F F' n θ) (bcS F F' n s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    have h1 : D F n θ (algebraMap F (S F n) r) = 0 :=
      contractLeft_algebraMap (Q := (0 : QuadraticForm F (H1 F n))) _ r
    have h2 : bcS F F' n (algebraMap F (S F n) r) = algebraMap F' (S F' n) (algebraMap F F' r) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n)]
    rw [h1, map_zero, h2]
    exact (contractLeft_algebraMap (Q := (0 : QuadraticForm F' (H1 F' n))) _ _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x w hx =>
    have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w x
    have h2 := contractLeft_ι_mul (Q := (0 : QuadraticForm F' (H1 F' n)))
      (bcDual F F' n θ) (bcH1 F F' n w) (bcS F F' n x)
    change bcS F F' n (D F n θ (ExteriorAlgebra.ι F w * x)) =
      D F' n _ (bcS F F' n (ExteriorAlgebra.ι F w * x))
    change D F n θ (ExteriorAlgebra.ι F w * x) = θ w • x - ExteriorAlgebra.ι F w * D F n θ x at h1
    change D F' n _ (ExteriorAlgebra.ι F' (bcH1 F F' n w) * bcS F F' n x) = _ • bcS F F' n x -
      ExteriorAlgebra.ι F' (bcH1 F F' n w) * D F' n _ (bcS F F' n x) at h2
    rw [h1, map_mul, s10_bcS_ι, h2, map_sub, map_smul, map_mul, s10_bcS_ι, hx,
      s10_bcDual_apply_bcH1, algebraMap_smul]

theorem s10_bcS_m_ι (v : V F n) (s : S F n) :
    bcS F F' n (m F n (ι (Q F n) v) s) = m F' n (ι (Q F' n) (bcV F F' n v)) (bcS F F' n s) := by
  rw [s10_m_ι_apply, s10_m_ι_apply, map_add, map_mul, s10_bcS_ι, s10_bcS_D]
  rfl

theorem s10_bcC_ι (v : V F n) : bcC F F' n (ι (Q F n) v) = ι (Q F' n) (bcV F F' n v) := by
  simp [bcC]

/-- The spin representation commutes with change of coefficients. -/
theorem s10_bcS_m (x : C F n) : ∀ s : S F n,
    bcS F F' n (m F n x s) = m F' n (bcC F F' n x) (bcS F F' n s) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    intro s
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, map_smul,
      IsScalarTower.algebraMap_apply F F' (C F' n), AlgHom.commutes, Module.algebraMap_end_apply,
      algebraMap_smul]
  | ι v => intro s; rw [s10_bcS_m_ι, s10_bcC_ι]
  | mul a b ha hb =>
    intro s
    rw [map_mul, Module.End.mul_apply, ha, hb, map_mul, map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    intro s
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add, map_add, LinearMap.add_apply]

theorem s10_bcS_m_spin (g : Spin F n) (s : S F n) :
    bcS F F' n (m F n (g : C F n) s) = m F' n (bcSpin F F' n g : C F' n) (bcS F F' n s) :=
  s10_bcS_m (g : C F n) s

theorem s10_bcS_injective : Function.Injective (bcS F F' n) := by
  intro x y h
  apply s10_S_ext
  intro K
  have := congrArg (fun z => (basisS F' n).repr z K) h
  simp only [s10_repr_bcS] at this
  exact (algebraMap F F').injective this

theorem s10_bcS_bcS {F'' : Type*} [Field F''] [CharZero F''] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (x : S F n) :
    bcS F' F'' n (bcS F F' n x) = bcS F F'' n x := by
  apply s10_S_ext
  intro K
  rw [s10_repr_bcS, s10_repr_bcS, s10_repr_bcS, ← IsScalarTower.algebraMap_apply]

end S10BC

section S10Galois

/-- Every ring automorphism of a subfield `L ⊆ ℂ` (over `ℚ`) extends to a ring automorphism of `ℂ`
(through a transcendence basis of `ℂ` over `L`). -/
theorem s10_exists_extend (L : IntermediateField ℚ ℂ) (σ : L ≃+* L) :
    ∃ τ : ℂ ≃+* ℂ, ∀ x : L, τ (x : ℂ) = (σ x : ℂ) := by
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis L ℂ
  let A := Algebra.adjoin L (Set.range ((↑) : T → ℂ))
  have : IsAlgClosure A ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hT
  let ψ : A ≃+* A := hT.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv T σ).trans hT.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ ψ, fun x => ?_⟩
  have h1 := IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ ψ (algebraMap L A x)
  have h2 : ψ (algebraMap L A x) = algebraMap L A (σ x) := by
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    rw [AlgEquiv.commutes]
    simp only [MvPolynomial.mapEquiv_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    exact hT.1.aevalEquiv.commutes (σ x)
  rw [h2] at h1
  exact h1

/-- `ℚ̄`: the algebraic closure of `ℚ` in `ℂ`. -/
noncomputable abbrev s10_Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

noncomputable instance s10_Qbar_isAlgClosed : IsAlgClosed s10_Qbar := IsAlgClosure.isAlgClosed ℚ

/-- An algebraic number fixed by every automorphism of `ℂ` is rational (Galois theory of `ℚ̄/ℚ`
and the extension of automorphisms of `ℚ̄` to `ℂ`). -/
theorem s10_rat_of_fixed (z : s10_Qbar) (hz : ∀ τ : ℂ ≃+* ℂ, τ (z : ℂ) = z) :
    z ∈ Set.range (algebraMap ℚ s10_Qbar) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro f
  obtain ⟨τ, hτ⟩ := s10_exists_extend s10_Qbar f.toRingEquiv
  apply Subtype.ext
  have := hτ z
  rw [hz τ] at this
  exact this.symm

end S10Galois

section S10Descent

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharZero F] [Algebra F ℂ]

theorem s10_bcS_smul (c : F) (x : S F 3) : bcS F ℂ 3 (c • x) = algebraMap F ℂ c • bcS F ℂ 3 x := by
  rw [map_smul, algebraMap_smul]

/-- Two independent vectors have a nonzero `2 × 2` minor. -/
theorem s10_exists_minor {a b : S F 3} (hab : LinearIndependent F ![a, b]) :
    ∃ K₁ K₂ : Finset (Fin 6), (basisS F 3).repr a K₁ * (basisS F 3).repr b K₂ -
      (basisS F 3).repr a K₂ * (basisS F 3).repr b K₁ ≠ 0 := by
  have ha : a ≠ 0 := hab.ne_zero 0
  obtain ⟨K₁, hK₁⟩ : ∃ K, (basisS F 3).repr a K ≠ 0 := by
    by_contra h
    push Not at h
    exact ha ((basisS F 3).repr.injective (Finsupp.ext fun K => by simpa using h K))
  by_contra h
  push Not at h
  have hb : b = ((basisS F 3).repr b K₁ / (basisS F 3).repr a K₁) • a := by
    apply s10_S_ext
    intro K
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have := h K₁ K
    field_simp
    linear_combination this
  have := (LinearIndependent.pair_iff.mp hab ((basisS F 3).repr b K₁ / (basisS F 3).repr a K₁)
    (-1) (by rw [neg_one_smul, ← hb, add_neg_cancel])).2
  exact one_ne_zero (neg_eq_zero.mp this)

/-- **Galois descent for a plane**: if `P = span_ℂ{a, b}` with `a, b ∈ S_{ℚ̄}` independent, and `P` is
stable under every automorphism of `ℂ` (acting on coordinates), then `P` is defined over `ℚ`. -/
theorem s10_isDefinedOver_of_fixed {a b : S s10_Qbar 3} (hab : LinearIndependent s10_Qbar ![a, b])
    (P : Submodule ℂ (S ℂ 3))
    (hP : P = Submodule.span ℂ {bcS s10_Qbar ℂ 3 a, bcS s10_Qbar ℂ 3 b})
    (hfix : ∀ τ : ℂ ≃+* ℂ, P.map (s10_conjSL τ) = P) : IsDefinedOverS ℚ ℂ 3 P := by
  obtain ⟨K₁, K₂, hδ⟩ := s10_exists_minor hab
  obtain ⟨ra, hra⟩ : ∃ f, f = (basisS s10_Qbar 3).repr a := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ f, f = (basisS s10_Qbar 3).repr b := ⟨_, rfl⟩
  rw [← hra, ← hrb] at hδ
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ra K₁ * rb K₂ - ra K₂ * rb K₁ := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = δ⁻¹ • (rb K₂ • a - ra K₂ • b) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, x = δ⁻¹ • (ra K₁ • b - rb K₁ • a) := ⟨_, rfl⟩
  have hr₁ : ∀ K, (basisS s10_Qbar 3).repr x₁ K = δ⁻¹ * (rb K₂ * ra K - ra K₂ * rb K) := by
    intro K; rw [hx₁, hra, hrb]; simp
  have hr₂ : ∀ K, (basisS s10_Qbar 3).repr x₂ K = δ⁻¹ * (ra K₁ * rb K - rb K₁ * ra K) := by
    intro K; rw [hx₂, hra, hrb]; simp
  have h11 : (basisS s10_Qbar 3).repr x₁ K₁ = 1 := by
    rw [hr₁, show rb K₂ * ra K₁ - ra K₂ * rb K₁ = δ by rw [hδdef]; ring, inv_mul_cancel₀ hδ]
  have h12 : (basisS s10_Qbar 3).repr x₁ K₂ = 0 := by rw [hr₁]; ring
  have h21 : (basisS s10_Qbar 3).repr x₂ K₁ = 0 := by rw [hr₂]; ring
  have h22 : (basisS s10_Qbar 3).repr x₂ K₂ = 1 := by
    rw [hr₂, show ra K₁ * rb K₂ - rb K₁ * ra K₂ = δ by rw [hδdef]; ring, inv_mul_cancel₀ hδ]
  have ha : a = ra K₁ • x₁ + ra K₂ • x₂ := by
    have : ra K₁ • x₁ + ra K₂ • x₂ = (δ⁻¹ * δ) • a := by rw [hx₁, hx₂, hδdef]; module
    rw [this, inv_mul_cancel₀ hδ, one_smul]
  have hb : b = rb K₁ • x₁ + rb K₂ • x₂ := by
    have : rb K₁ • x₁ + rb K₂ • x₂ = (δ⁻¹ * δ) • b := by rw [hx₁, hx₂, hδdef]; module
    rw [this, inv_mul_cancel₀ hδ, one_smul]
  obtain ⟨X₁, hX₁⟩ : ∃ X, X = bcS s10_Qbar ℂ 3 x₁ := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X, X = bcS s10_Qbar ℂ 3 x₂ := ⟨_, rfl⟩
  have hPX : P = Submodule.span ℂ {X₁, X₂} := by
    rw [hP]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | h)
      · rw [ha, map_add, s10_bcS_smul, s10_bcS_smul, ← hX₁, ← hX₂]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Set.mem_singleton_iff.mp h, hb, map_add, s10_bcS_smul, s10_bcS_smul, ← hX₁, ← hX₂]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      rintro _ (rfl | h)
      · rw [hX₁, hx₁, s10_bcS_smul, map_sub, s10_bcS_smul, s10_bcS_smul]
        exact Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span
          (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      · rw [Set.mem_singleton_iff.mp h, hX₂, hx₂, s10_bcS_smul, map_sub, s10_bcS_smul,
          s10_bcS_smul]
        exact Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span
          (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hX11 : (basisS ℂ 3).repr X₁ K₁ = 1 := by rw [hX₁, s10_repr_bcS, h11, map_one]
  have hX12 : (basisS ℂ 3).repr X₁ K₂ = 0 := by rw [hX₁, s10_repr_bcS, h12, map_zero]
  have hX21 : (basisS ℂ 3).repr X₂ K₁ = 0 := by rw [hX₂, s10_repr_bcS, h21, map_zero]
  have hX22 : (basisS ℂ 3).repr X₂ K₂ = 1 := by rw [hX₂, s10_repr_bcS, h22, map_one]
  -- an element of `P` is determined by its coordinates at `K₁, K₂`
  have hcoord : ∀ y ∈ P, y = (basisS ℂ 3).repr y K₁ • X₁ + (basisS ℂ 3).repr y K₂ • X₂ := by
    intro y hy
    rw [hPX] at hy
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hX11, hX12,
      hX21, hX22, mul_one, mul_zero, add_zero, zero_add]
  -- every automorphism of `ℂ` fixes `X₁` and `X₂`
  have hfixX : ∀ τ : ℂ ≃+* ℂ, ∀ X ∈ ({X₁, X₂} : Set (S ℂ 3)), conjS τ 3 X = X := by
    intro τ X hX
    have hXP : X ∈ P := by rw [hPX]; exact Submodule.subset_span hX
    have h1 : conjS τ 3 X ∈ P := by
      rw [← hfix τ]
      exact Submodule.mem_map_of_mem hXP
    rw [hcoord _ h1, s10_repr_conjS, s10_repr_conjS]
    rcases hX with rfl | h
    · rw [hX11, hX12, map_one, map_zero, one_smul, zero_smul, add_zero]
    · rw [Set.mem_singleton_iff.mp h, hX21, hX22, map_one, map_zero, one_smul, zero_smul,
        zero_add]
  -- hence `x₁, x₂` are rational
  have hrat : ∀ x : S s10_Qbar 3, (∀ τ : ℂ ≃+* ℂ,
      conjS τ 3 (bcS s10_Qbar ℂ 3 x) = bcS s10_Qbar ℂ 3 x) →
      ∃ r : S ℚ 3, bcS ℚ s10_Qbar 3 r = x := by
    intro x hx
    have hq : ∀ K, ∃ q : ℚ, algebraMap ℚ s10_Qbar q = (basisS s10_Qbar 3).repr x K := by
      intro K
      apply s10_rat_of_fixed
      intro τ
      have := congrArg (fun y => (basisS ℂ 3).repr y K) (hx τ)
      simp only [s10_repr_conjS, s10_repr_bcS] at this
      exact this
    choose q hq using hq
    refine ⟨∑ K, q K • basisS ℚ 3 K, ?_⟩
    apply s10_S_ext
    intro K
    rw [s10_repr_bcS, ← hq K]
    congr 1
    simp [Finsupp.single_apply]
  obtain ⟨r₁, hr₁'⟩ := hrat x₁ fun τ => hX₁ ▸ hfixX τ X₁ (by simp)
  obtain ⟨r₂, hr₂'⟩ := hrat x₂ fun τ => hX₂ ▸ hfixX τ X₂ (by simp)
  have hb₁ : X₁ = bcS ℚ ℂ 3 r₁ := by rw [hX₁, ← hr₁', s10_bcS_bcS]
  have hb₂ : X₂ = bcS ℚ ℂ 3 r₂ := by rw [hX₂, ← hr₂', s10_bcS_bcS]
  refine ⟨Submodule.span ℚ {r₁, r₂}, ?_⟩
  rw [hPX, bcSubS]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ (rfl | h)
    · exact Submodule.subset_span ⟨r₁, Submodule.subset_span (by simp), hb₁.symm⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact Submodule.subset_span ⟨r₂, Submodule.subset_span (by simp), hb₂.symm⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [map_add, map_smul, map_smul, ← algebraMap_smul ℂ p, ← algebraMap_smul ℂ q, ← hb₁, ← hb₂]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end S10Descent

/-! ## Lemma 10.1.1 -/

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), first sentence. For each
`[w] ∈ ℙ(S⁺_ℂ) ∖ V(J)` (that is, `w ∈ S⁺_ℂ` with `J(w) ≠ 0`, see `mk_mem_VJ_iff`) there is a unique
plane `P_w ⊆ S⁺_ℂ` containing `w` such that the line `ℙ(P_w)` meets the even spinor variety in two
pure spinors `[u₁], [u₂]` corresponding to two transversal maximal isotropic subspaces
`W_i = ker m_{u_i}` of `V_ℂ` (`WeilClasses.IsTransversalSecant`).
Reading: "intersects the even spinor variety along two pure spinors" is read as: the intersection
consists of exactly these two points (by [Chevalley, III.1.12] this is automatic for a line through
two pure spinors with `W₁ ∩ W₂ = 0`).
Gap in the paper (filled): the proof shows uniqueness only among the secants through `w` every
point of which is `Spin(V_ℂ)_w`-invariant (l. 9710–9711). That every transversal secant through `w`
has this property is [Igusa, Lemma 2] for its own pair of pure spinors (`igusa_lemma2_stab_odd`,
used in `s10_secant_lines`), as in Remark 2.2.3 (l. 835).
Conditional on [Igusa, Prop. 3] (the normal form, `IgusaProp3NormalForm`), which the proof uses and
this project assumes (see `WeilClasses/External/Igusa/README.md`). -/
theorem lemma10_1_1 (hIgusa : IgusaProp3NormalForm) (w : S ℂ 3) (hw : w ∈ Splus ℂ 3)
    (hJ : J ℂ w ≠ 0) :
    ∃! P : Submodule ℂ (S ℂ 3), w ∈ P ∧ ∃ u₁ u₂ : S ℂ 3, IsTransversalSecant ℂ 3 P u₁ u₂ := by
  -- reduction to `w₀ = 1 + c [pt_X]` by [Igusa, Prop. 3]
  obtain ⟨g, c, hc, hg⟩ := s10_normal_form hIgusa w hw hJ
  have hw0 := s10_ne_zero_of_J hJ
  refine ⟨(Submodule.span ℂ {1, pt ℂ 3}).map (m ℂ 3 ((g⁻¹ : Spin ℂ 3) : C ℂ 3)),
    ⟨?_, _, _, s10_isTransversalSecant_map g⁻¹ (isTransversalSecant_one_pt ℂ)⟩, ?_⟩
  · refine Submodule.mem_map.mpr ⟨1 + c • pt ℂ 3, s10_one_add_mem_span c, ?_⟩
    rw [← hg, s10_m_inv_m]
  · rintro P' ⟨hwP', u₁', u₂', hP'⟩
    rw [← s10_secant_map_eq w hw0 g hc hg hP' hwP', s10_map_m_inv_map]

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), second sentence. Let `w ∈ S⁺_ℂ` with
`J(w) ≠ 0`, and let `P_w = span{u₁, u₂}` be the secant through `w` (as in `lemma10_1_1`), with
`W_i = ker m_{u_i}`. Then `ρ : Spin(V_ℂ) → SO(V_ℂ)` restricted to the stabilizer `Spin(V_ℂ)_w` is
injective, and its image is the image of the embedding `e : SL(W₁) → SO(V_ℂ)` of (10.1.2), acting on
`W₂ ≅ W₁*` (via the pairing (1.2.2)) by the inverse transpose (`WeilClasses.slImage`).
Conditional on [Igusa, Prop. 3] (the normal form, `IgusaProp3NormalForm`), which the proof uses and
this project assumes (see `WeilClasses/External/Igusa/README.md`). -/
theorem lemma10_1_1_stabilizer (hIgusa : IgusaProp3NormalForm) (w : S ℂ 3) (hw : w ∈ Splus ℂ 3)
    (hJ : J ℂ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : w ∈ P) :
    Set.InjOn (rho ℂ 3) (spinStab ℂ 3 w : Set (Spin ℂ 3)) ∧
      rho ℂ 3 '' (spinStab ℂ 3 w : Set (Spin ℂ 3)) = slImage ℂ 3 (ann ℂ 3 u₁) (ann ℂ 3 u₂) := by
  have hw0 := s10_ne_zero_of_J hJ
  refine ⟨s10_rho_injOn (by norm_num) hw0, ?_⟩
  -- reduction to `w₀ = 1 + c [pt_X]` ([Igusa, Prop. 3]), where [Igusa, Lemma 2] applies
  obtain ⟨g, c, hc, hg⟩ := s10_normal_form hIgusa w hw hJ
  set σ := rho ℂ 3 g⁻¹ with hσ
  have hρmul : ∀ a b : Spin ℂ 3, rho ℂ 3 (a * b) = rho ℂ 3 a * rho ℂ 3 b := fun a b =>
    CliffordAlgebra.spinVectorAction_mul _ a b
  have hρinv : ∀ v, rho ℂ 3 g (σ v) = v := by
    intro v
    rw [hσ, ← LinearEquiv.mul_apply, ← hρmul, mul_inv_cancel]
    exact congrArg (fun e : V ℂ 3 ≃ₗ[ℂ] V ℂ 3 => e v) (CliffordAlgebra.spinVectorAction_one _)
  have hσinv : ∀ v, σ (rho ℂ 3 g v) = v := by
    intro v
    rw [hσ, ← LinearEquiv.mul_apply, ← hρmul, inv_mul_cancel]
    exact congrArg (fun e : V ℂ 3 ≃ₗ[ℂ] V ℂ 3 => e v) (CliffordAlgebra.spinVectorAction_one _)
  have hσsymm : σ.symm = rho ℂ 3 g := by
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.symm_apply_eq, hσinv]
  -- `Spin(V)_w = g⁻¹ Spin(V)_{w₀} g`
  have himage : rho ℂ 3 '' (spinStab ℂ 3 w : Set (Spin ℂ 3)) =
      (fun γ => σ.symm.trans (γ.trans σ)) ''
        (rho ℂ 3 '' (spinStab ℂ 3 (1 + c • pt ℂ 3) : Set (Spin ℂ 3))) := by
    ext γ
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨rho ℂ 3 (g * h * g⁻¹), ⟨g * h * g⁻¹, ?_, rfl⟩, ?_⟩
      · show m ℂ 3 ((g * h * g⁻¹ : Spin ℂ 3) : C ℂ 3) (1 + c • pt ℂ 3) = 1 + c • pt ℂ 3
        rw [Submonoid.coe_mul, Submonoid.coe_mul, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, ← hg, s10_m_inv_m, show m ℂ 3 (h : C ℂ 3) w = w from hh]
      · refine LinearEquiv.ext fun v => ?_
        simp only [LinearEquiv.trans_apply, hσsymm, hρmul, LinearEquiv.mul_apply]
        rw [show rho ℂ 3 g⁻¹ (rho ℂ 3 g v) = v from hσinv v, hσinv]
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * h * g, ?_, ?_⟩
      · show m ℂ 3 ((g⁻¹ * h * g : Spin ℂ 3) : C ℂ 3) w = w
        rw [Submonoid.coe_mul, Submonoid.coe_mul, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, hg, show m ℂ 3 (h : C ℂ 3) (1 + c • pt ℂ 3) = 1 + c • pt ℂ 3
          from hh, ← hg, s10_m_inv_m]
      · refine LinearEquiv.ext fun v => ?_
        simp only [LinearEquiv.trans_apply, hσsymm, hρmul, LinearEquiv.mul_apply]
        rfl
  rw [himage, igusa_lemma2 c hc, ← s10_slImage_conj σ (s10_rho_isometry g⁻¹)]
  -- `{ker m_{u₁}, ker m_{u₂}} = {ρ(g)⁻¹ W₁, ρ(g)⁻¹ W₂}`
  have hann : ∀ u z : S ℂ 3, u ≠ 0 → m ℂ 3 (g : C ℂ 3) u ∈ Submodule.span ℂ {z} →
      ann ℂ 3 u = (ann ℂ 3 z).map (σ : V ℂ 3 →ₗ[ℂ] V ℂ 3) := by
    intro u z hu hz
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hz
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hα
      exact hu (s10_m_injective g (by rw [← hα, map_zero]))
    calc ann ℂ 3 u = ann ℂ 3 (m ℂ 3 ((g⁻¹ : Spin ℂ 3) : C ℂ 3) (m ℂ 3 (g : C ℂ 3) u)) := by
          rw [s10_m_inv_m]
      _ = (ann ℂ 3 (m ℂ 3 (g : C ℂ 3) u)).map (σ : V ℂ 3 →ₗ[ℂ] V ℂ 3) := ann_m_spin ℂ 3 g⁻¹ _
      _ = (ann ℂ 3 z).map (σ : V ℂ 3 →ₗ[ℂ] V ℂ 3) := by rw [← hα, s10_ann_smul hα0]
  have hu₁ : u₁ ≠ 0 := hP.2.2.1.ne_zero (by norm_num)
  have hu₂ : u₂ ≠ 0 := hP.2.2.2.1.ne_zero (by norm_num)
  rcases s10_secant_lines w hw0 g hc hg hP hwP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hann u₁ 1 hu₁ h1, hann u₂ _ hu₂ h2, ann_one, ann_pt]
  · rw [hann u₁ _ hu₁ h1, hann u₂ 1 hu₂ h2, ann_one, ann_pt,
      s10_slImage_conj σ (s10_rho_isometry g⁻¹), s10_slImage_conj σ (s10_rho_isometry g⁻¹),
      s10_slImage_symm_std]

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), last sentence. If `w` belongs to `S⁺_ℚ`
(with `J(w) ≠ 0`), then the plane `P_w ⊆ S⁺_ℂ` is defined over `ℚ`: it is the base change of a
plane of `S⁺_ℚ`.
Departure from the paper (reason 3): the paper argues "the stabilizer `Spin(V_ℂ)_w` is defined over
`ℚ`. The latter determines `P_w`. Hence, `P_w` is defined over `ℚ` as well" (l. 9716–9717). Fields
of definition of algebraic subgroups are not part of the model (its groups are groups of points), so
the intermediary is `w` instead of `Spin(V_ℂ)_w`: `P_w` is determined by `w` (the uniqueness in
`lemma10_1_1`), hence every automorphism `τ` of `ℂ` maps `P_w` to the transversal secant through
`τ(w) = w`, i.e. to `P_w`. The descent is then explicit: the normal form over the algebraic closure
`ℚ̄` of `ℚ` in `ℂ` (`IgusaProp3NormalForm`) gives `P_w` a basis of vectors defined over `ℚ̄`, and a
plane with both properties is defined over `ℚ` (`s10_isDefinedOver_of_fixed`, with the Galois theory
of `ℚ̄/ℚ` in `s10_rat_of_fixed`).
Conditional on [Igusa, Prop. 3] (the normal form, `IgusaProp3NormalForm`), which the proof uses and
this project assumes (see `WeilClasses/External/Igusa/README.md`). -/
theorem lemma10_1_1_rational (hIgusa : IgusaProp3NormalForm) (w : S ℚ 3) (hw : w ∈ Splus ℚ 3)
    (hJ : J ℚ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : bcS ℚ ℂ 3 w ∈ P) :
    IsDefinedOverS ℚ ℂ 3 P := by
  -- Galois descent: `P_w` is determined by `w` (Lemma 10.1.1, uniqueness), so it is stable under
  -- every automorphism of `ℂ`; it has a basis defined over `ℚ̄` (the normal form of
  -- [Igusa, Prop. 3] over `ℚ̄`); hence it is defined over `ℚ`.
  set wb := bcS ℚ s10_Qbar 3 w with hwbdef
  have hwb : wb ∈ Splus s10_Qbar 3 := s10_bcS_mem_Splus hw
  have hJb : J s10_Qbar wb ≠ 0 := s10_J_bcS_ne_zero hJ
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-J s10_Qbar wb) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hJb
    linear_combination hs
  obtain ⟨g, hg⟩ := igusa_prop3_normalForm_of_sq hIgusa s10_Qbar wb hwb s hs0 hs
  set a := m s10_Qbar 3 ((g⁻¹ : Spin s10_Qbar 3) : C s10_Qbar 3) 1 with ha
  set b := m s10_Qbar 3 ((g⁻¹ : Spin s10_Qbar 3) : C s10_Qbar 3) (pt s10_Qbar 3) with hb
  set gc := bcSpin s10_Qbar ℂ 3 g with hgc
  have hinv : bcSpin s10_Qbar ℂ 3 g⁻¹ = gc⁻¹ := map_inv _ g
  have hpt : bcS s10_Qbar ℂ 3 (pt s10_Qbar 3) = pt ℂ 3 := s10_bcS_basisS _ _ _ _
  have hA : bcS s10_Qbar ℂ 3 a = m ℂ 3 ((gc⁻¹ : Spin ℂ 3) : C ℂ 3) 1 := by
    rw [ha, s10_bcS_m_spin, hinv, map_one]
  have hB : bcS s10_Qbar ℂ 3 b = m ℂ 3 ((gc⁻¹ : Spin ℂ 3) : C ℂ 3) (pt ℂ 3) := by
    rw [hb, s10_bcS_m_spin, hinv, hpt]
  have hP' := s10_isTransversalSecant_map gc⁻¹ (isTransversalSecant_one_pt ℂ)
  have hwP' : bcS ℚ ℂ 3 w ∈ (Submodule.span ℂ {1, pt ℂ 3}).map (m ℂ 3 ((gc⁻¹ : Spin ℂ 3) : C ℂ 3)) := by
    refine Submodule.mem_map.mpr ⟨1 + (algebraMap s10_Qbar ℂ (2 * s)) • pt ℂ 3,
      s10_one_add_mem_span _, ?_⟩
    have h1 : wb = m s10_Qbar 3 ((g⁻¹ : Spin s10_Qbar 3) : C s10_Qbar 3) (1 + (2 * s) • pt s10_Qbar 3) := by
      rw [← hg, s10_m_inv_m]
    have e1 : bcS ℚ ℂ 3 w = bcS s10_Qbar ℂ 3 wb := (s10_bcS_bcS (F' := s10_Qbar) w).symm
    rw [e1, h1, s10_bcS_m_spin, hinv]
    congr 1
    rw [map_add, map_one, map_smul, hpt, algebraMap_smul]
  -- uniqueness of the secant (Lemma 10.1.1)
  obtain ⟨P₀, -, huniq⟩ := lemma10_1_1 hIgusa (bcS ℚ ℂ 3 w) (s10_bcS_mem_Splus hw) (s10_J_bcS_ne_zero hJ)
  have hPP : P = (Submodule.span ℂ {1, pt ℂ 3}).map (m ℂ 3 ((gc⁻¹ : Spin ℂ 3) : C ℂ 3)) :=
    (huniq P ⟨hwP, u₁, u₂, hP⟩).trans (huniq _ ⟨hwP', _, _, hP'⟩).symm
  have hPab : P = Submodule.span ℂ {bcS s10_Qbar ℂ 3 a, bcS s10_Qbar ℂ 3 b} := by
    rw [hPP, hA, hB, Submodule.map_span, Set.image_pair]
  -- every automorphism `τ` of `ℂ` maps `P_w` to a transversal secant through `τ(w) = w`
  have hfix : ∀ τ : ℂ ≃+* ℂ, P.map (s10_conjSL τ) = P := by
    intro τ
    have hτP := s10_isTransversalSecant_conj τ hP
    have hτw : bcS ℚ ℂ 3 w ∈ P.map (s10_conjSL τ) :=
      Submodule.mem_map.mpr ⟨_, hwP, s10_conjS_bcS τ w⟩
    exact (huniq _ ⟨hτw, _, _, hτP⟩).trans (huniq P ⟨hwP, u₁, u₂, hP⟩).symm
  have hab : LinearIndependent s10_Qbar ![a, b] :=
    (s10_isTransversalSecant_map g⁻¹ (isTransversalSecant_one_pt s10_Qbar)).2.1
  exact s10_isDefinedOver_of_fixed hab P hPab hfix

/-! ## Remark 10.1.2 -/

/-- **Remark 10.1.2(1)** (no label), first sentence: for any subfield `F` of `ℂ` and `d ∈ F`,
`d ≠ 0`, the level set `J⁻¹(d) ⊆ S⁺_F` is a single `Spin(V_F)`-orbit ([Igusa, Prop. 3],
`igusa_prop3_orbit_subfield`).

Correction of a slip: the paper says `d ∈ F`. For `d = 0` the statement fails: `0` and the pure
spinor `1` both lie in `J⁻¹(0)`, and `m_g(0) = 0 ≠ 1` for every `g`. The only reading under which it
holds, `d ∈ F^×`, is the one stated here (REPORT.md).

Conditional on [Igusa, Prop. 3] over subfields of `ℂ` (`IgusaProp3OrbitSubfield`), which the remark
quotes and this project assumes (see `WeilClasses/External/Igusa/README.md`). -/
theorem remark10_1_2_orbit (hIgusa : IgusaProp3OrbitSubfield) (F : Subfield ℂ) (d : F) (hd : d ≠ 0)
    (x y : S F 3) (hx : x ∈ Splus F 3) (hy : y ∈ Splus F 3) (hxd : J F x = d) (hyd : J F y = d) :
    ∃ g : Spin F 3, m F 3 (g : C F 3) x = y :=
  igusa_prop3_orbit_subfield hIgusa F d hd x y hx hy hxd hyd

/-- **Remark 10.1.2(1)** (no label), second sentence: if `w = 1 + e₁₄^* + e₂₅^* + d e₃₆^*`,
`d ∈ F`, then `J(w) = d` (0-based indices: `e₁₄^* = eStar F 0 3`, etc.). The paper has `F ⊆ ℂ`; the
identity holds over every field of characteristic zero. -/
theorem remark10_1_2_value (F : Type*) [Field F] [CharZero F] (d : F) :
    J F (1 + eStar F 0 3 + eStar F 1 4 + d • eStar F 2 5) = d := by
  have h := s10_J_diag F 1 1 1 d
  simp only [one_smul, one_mul] at h
  exact h

/-- **Remark 10.1.2(2)** (no label), first sentence: the secant `ℙ(P_w)` of Lemma 10.1.1 meets the
quartic `V(J)` at the same two points `[u₁], [u₂]` at which it meets the spinor variety, each with
multiplicity `2`. Precise form: the restriction of `J` to `P_w = span{u₁, u₂}` is
`J(a u₁ + b u₂) = c a² b²` for a constant `c ≠ 0`. -/
theorem remark10_1_2_secant (w : S ℂ 3) (_hw : w ∈ Splus ℂ 3) (hJ : J ℂ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : w ∈ P) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a b : ℂ, J ℂ (a • u₁ + b • u₂) = c * a ^ 2 * b ^ 2 := by
  -- `J` restricted to `P` is a binary quartic form `Σ q_i a^i b^{4-i}`
  set P' := s10_Jc (MvPolynomial.C (1 / 4 : ℂ)) (fun K =>
    MvPolynomial.C ((basisS ℂ 3).repr u₁ K) * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C ((basisS ℂ 3).repr u₂ K) * MvPolynomial.X (1 : Fin 2)) with hP'
  have hPh : P'.IsHomogeneous 4 := s10_Jc_isHomogeneous _ _ fun K =>
    (MvPolynomial.isHomogeneous_C_mul_X _ 0).add (MvPolynomial.isHomogeneous_C_mul_X _ 1)
  have hev : ∀ a b : ℂ, J ℂ (a • u₁ + b • u₂) = MvPolynomial.eval ![a, b] P' := by
    intro a b
    rw [hP', s10_Jc_map, s10_J_eq_Jc]
    simp only [MvPolynomial.eval_C, map_add, map_mul, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_smul]
    congr 1
    funext K
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨q, hq⟩ := s10_eval_isHomogeneous_four P' hPh
  have hJ' : ∀ a b : ℂ, J ℂ (a • u₁ + b • u₂) =
      q 0 * b ^ 4 + q 1 * a * b ^ 3 + q 2 * a ^ 2 * b ^ 2 + q 3 * a ^ 3 * b + q 4 * a ^ 4 := by
    intro a b
    rw [hev, hq, Fin.sum_univ_five]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
  -- the pure spinors `u₁, u₂` are singular points of `V(J)` (`remark10_1_2_singular`)
  have hs₁ := s10_singular u₁ hP.2.2.1
  have hs₂ := s10_singular u₂ hP.2.2.2.1
  have hq0 : q 0 = 0 := by
    have := hJ' 0 1
    rw [zero_smul, one_smul, zero_add, hs₂.1] at this
    linear_combination -this
  have hq4 : q 4 = 0 := by
    have := hJ' 1 0
    rw [zero_smul, one_smul, add_zero, hs₁.1] at this
    linear_combination -this
  have hpoly : ∀ r₀ r₁ r₂ r₃ r₄ : ℂ, HasDerivAt
      (fun t : ℂ => r₀ + r₁ * t + r₂ * t ^ 2 + r₃ * t ^ 3 + r₄ * t ^ 4) r₁ 0 := by
    intro r₀ r₁ r₂ r₃ r₄
    have h := (((((hasDerivAt_const (0 : ℂ) r₀).add ((hasDerivAt_id (0 : ℂ)).const_mul r₁)).add
      ((hasDerivAt_pow 2 (0 : ℂ)).const_mul r₂)).add ((hasDerivAt_pow 3 (0 : ℂ)).const_mul r₃)).add
      ((hasDerivAt_pow 4 (0 : ℂ)).const_mul r₄))
    exact h.congr_deriv (by norm_num)
  -- the double roots: vanishing of the derivatives at `[u₂]` and `[u₁]`
  have hq1 : q 1 = 0 := by
    have hfun : (fun t : ℂ => J ℂ (u₂ + t • u₁)) =
        fun t => q 0 + q 1 * t + q 2 * t ^ 2 + q 3 * t ^ 3 + q 4 * t ^ 4 := by
      funext t
      rw [show u₂ + t • u₁ = t • u₁ + (1 : ℂ) • u₂ by rw [one_smul, add_comm], hJ']
      ring
    have h2 := hs₂.2 u₁
    rw [hfun] at h2
    exact (hpoly _ _ _ _ _).unique h2
  have hq3 : q 3 = 0 := by
    have hfun : (fun t : ℂ => J ℂ (u₁ + t • u₂)) =
        fun t => q 4 + q 3 * t + q 2 * t ^ 2 + q 1 * t ^ 3 + q 0 * t ^ 4 := by
      funext t
      rw [show u₁ + t • u₂ = (1 : ℂ) • u₁ + t • u₂ by rw [one_smul], hJ']
      ring
    have h2 := hs₁.2 u₂
    rw [hfun] at h2
    exact (hpoly _ _ _ _ _).unique h2
  have hform : ∀ a b : ℂ, J ℂ (a • u₁ + b • u₂) = q 2 * a ^ 2 * b ^ 2 := by
    intro a b
    rw [hJ', hq0, hq1, hq3, hq4]
    ring
  refine ⟨q 2, ?_, hform⟩
  -- `J(w) ≠ 0` for `w ∈ P`, so the quartic is not identically zero
  intro h0
  rw [hP.1] at hwP
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hwP
  rw [hform, h0, zero_mul, zero_mul] at hJ
  exact hJ rfl

/-- **Remark 10.1.2(2)** (no label), the reason given there: the even spinor variety is contained
in the singular locus of `V(J)`. Precise form: at every even pure spinor `u ∈ S⁺_ℂ`, `J` vanishes
and so does its differential (every directional derivative `t ↦ J(u + t x)` at `t = 0`). -/
theorem remark10_1_2_singular (u : S ℂ 3) (hu : IsEvenPureSpinor ℂ 3 u) :
    J ℂ u = 0 ∧ ∀ x : S ℂ 3, HasDerivAt (fun t : ℂ => J ℂ (u + t • x)) 0 0 :=
  s10_singular u hu

/-- **Remark 10.1.2(2)** (no label), second sentence: for `w ∈ S⁺_ℚ` (with `J(w) ≠ 0`) the plane
`P_w` is defined over `ℚ` (`lemma10_1_1_rational`), and so the length-two subscheme
`ℙ(P_w) ∩ (spinor variety) = {[u₁], [u₂]}` is defined over `ℚ`. Precise form (Galois descent for
the reduced subscheme of two points): every field automorphism `τ` of `ℂ`, acting on coordinates of
`S_ℂ`, permutes the two lines `ℂ u₁`, `ℂ u₂`. As in the paper, the proof cites the last sentence of
Lemma 10.1.1 (`lemma10_1_1_rational`): `τ` fixes the plane `P_w`, which is defined over `ℚ`, so it
permutes the two pure spinor lines of `P_w`.
Conditional on [Igusa, Prop. 3] (the normal form, `IgusaProp3NormalForm`), which the proof uses and
this project assumes (see `WeilClasses/External/Igusa/README.md`). -/
theorem remark10_1_2_rational (hIgusa : IgusaProp3NormalForm) (w : S ℚ 3) (hw : w ∈ Splus ℚ 3)
    (hJ : J ℚ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : bcS ℚ ℂ 3 w ∈ P) (τ : ℂ ≃+* ℂ) :
    ({Submodule.span ℂ {conjS τ 3 u₁}, Submodule.span ℂ {conjS τ 3 u₂}} :
        Set (Submodule ℂ (S ℂ 3))) =
      {Submodule.span ℂ {u₁}, Submodule.span ℂ {u₂}} := by
  -- "The subspace `P_w` is defined over `ℚ`" (Lemma 10.1.1), so `τ(P_w) = P_w`
  obtain ⟨P₀, hP₀⟩ := lemma10_1_1_rational hIgusa w hw hJ P u₁ u₂ hP hwP
  have hPP : P.map (s10_conjSL τ) = P := by rw [hP₀, s10_map_conjSL_bcSubS]
  -- so `τ` maps each pure spinor line of `P_w` to a pure spinor line of `P_w`
  have hτP := s10_isTransversalSecant_conj τ hP
  have hmem : ∀ u ∈ ({u₁, u₂} : Set (S ℂ 3)), conjS τ 3 u ∈ Submodule.span ℂ {u₁} ∨
      conjS τ 3 u ∈ Submodule.span ℂ {u₂} := by
    intro u hu
    have hu' : conjS τ 3 u ∈ P := by
      rw [← hPP]
      refine Submodule.mem_map.mpr ⟨u, ?_, rfl⟩
      rw [hP.1]
      exact Submodule.subset_span hu
    have hpure : IsEvenPureSpinor ℂ 3 (conjS τ 3 u) := by
      rcases hu with rfl | rfl
      · exact hτP.2.2.1
      · exact hτP.2.2.2.1
    exact hP.2.2.2.2.2 _ hu' hpure
  exact s10_pair_lines_eq hτP.2.1 (hmem u₁ (by simp)) (hmem u₂ (by simp))

end WeilClasses
