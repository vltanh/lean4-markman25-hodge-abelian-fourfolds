module

public import WeilClasses.Igusa.Defs
public import WeilClasses.External.Igusa.Sec10
public import Mathlib.Analysis.Calculus.Deriv.Basic

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
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Unnumbered claims used in the proofs of Lemmas 10.1.1 and 10.2.1 -/

/-- (Proof of Lemma 10.1.1, l. 9705: `J(1 + d[pt_X]) = -(1/4)d²`; also used in the proof of
Lemma 10.2.1, l. 9792 (`J(1 + 2√-d [pt_X]) = d`) and l. 9795 (`J ≤ 0` on `span{1, [pt_X]}`), and in
Example 10.2.3.) For every `c ∈ F`, `J(1 + c [pt_X]) = -(1/4) c²`. -/
theorem J_one_add_smul_pt (F : Type*) [Field F] [CharZero F] (c : F) :
    J F (1 + c • pt F 3) = -(1 / 4) * c ^ 2 := by
  sorry

/-- (Proof of Lemma 10.1.1, l. 9706.) The kernel of `m_1 : V_F → S_F` is `W₁ = H¹(X̂, F)`, the
summand `H¹(X, F)* × 0` of `V_F` (Mathlib's order `(θ, w)`). -/
theorem ann_one (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    ann F n 1 = (⊤ : Submodule F (Module.Dual F (H1 F n))).prod ⊥ := by
  sorry

/-- (Proof of Lemma 10.1.1, l. 9706–9707.) The kernel of `m_{[pt_X]} : V_F → S_F` is
`W₂ = H¹(X, F)`, the summand `0 × H¹(X, F)` of `V_F`. -/
theorem ann_pt (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    ann F n (pt F n) = (⊥ : Submodule F (Module.Dual F (H1 F n))).prod ⊤ := by
  sorry

/-- (Proof of Lemma 10.1.1, l. 9705–9711; proof of Lemma 10.2.1, l. 9792: `P_{g(w)} =
span{1, [pt_X]}`.) The line through the pure spinors `1` and `[pt_X]` is a secant of the even
spinor variety meeting it only at `[1]` and `[pt_X]`, and `ker m_1 ∩ ker m_{[pt_X]} = 0`. -/
theorem isTransversalSecant_one_pt (F : Type*) [Field F] [CharZero F] :
    IsTransversalSecant F 3 (Submodule.span F {1, pt F 3}) 1 (pt F 3) := by
  sorry

/-! ## Lemma 10.1.1 -/

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), first sentence. For each
`[w] ∈ ℙ(S⁺_ℂ) ∖ V(J)` (that is, `w ∈ S⁺_ℂ` with `J(w) ≠ 0`, see `mk_mem_VJ_iff`) there is a unique
plane `P_w ⊆ S⁺_ℂ` containing `w` such that the line `ℙ(P_w)` meets the even spinor variety in two
pure spinors `[u₁], [u₂]` corresponding to two transversal maximal isotropic subspaces
`W_i = ker m_{u_i}` of `V_ℂ` (`WeilClasses.IsTransversalSecant`).
Reading: "intersects the even spinor variety along two pure spinors" is read as: the intersection
consists of exactly these two points (by [Chevalley, III.1.12] this is automatic for a line through
two pure spinors with `W₁ ∩ W₂ = 0`). -/
theorem lemma10_1_1 (w : S ℂ 3) (hw : w ∈ Splus ℂ 3) (hJ : J ℂ w ≠ 0) :
    ∃! P : Submodule ℂ (S ℂ 3), w ∈ P ∧ ∃ u₁ u₂ : S ℂ 3, IsTransversalSecant ℂ 3 P u₁ u₂ := by
  sorry

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), second sentence. Let `w ∈ S⁺_ℂ` with
`J(w) ≠ 0`, and let `P_w = span{u₁, u₂}` be the secant through `w` (as in `lemma10_1_1`), with
`W_i = ker m_{u_i}`. Then `ρ : Spin(V_ℂ) → SO(V_ℂ)` restricted to the stabilizer `Spin(V_ℂ)_w` is
injective, and its image is the image of the embedding `e : SL(W₁) → SO(V_ℂ)` of (10.1.2), acting on
`W₂ ≅ W₁*` (via the pairing (1.2.2)) by the inverse transpose (`WeilClasses.slImage`). -/
theorem lemma10_1_1_stabilizer (w : S ℂ 3) (hw : w ∈ Splus ℂ 3) (hJ : J ℂ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : w ∈ P) :
    Set.InjOn (rho ℂ 3) (spinStab ℂ 3 w : Set (Spin ℂ 3)) ∧
      rho ℂ 3 '' (spinStab ℂ 3 w : Set (Spin ℂ 3)) = slImage ℂ 3 (ann ℂ 3 u₁) (ann ℂ 3 u₂) := by
  sorry

/-- **Lemma 10.1.1** (`lemma-secant-to-spinor-variety`), last sentence. If `w` belongs to `S⁺_ℚ`
(with `J(w) ≠ 0`), then the plane `P_w ⊆ S⁺_ℂ` is defined over `ℚ`: it is the base change of a
plane of `S⁺_ℚ`. -/
theorem lemma10_1_1_rational (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hJ : J ℚ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : bcS ℚ ℂ 3 w ∈ P) :
    IsDefinedOverS ℚ ℂ 3 P := by
  sorry

/-! ## Remark 10.1.2 -/

/-- **Remark 10.1.2(1)** (no label), first sentence: for any subfield `F` of `ℂ` and `d ∈ F`,
`d ≠ 0`, the level set `J⁻¹(d) ⊆ S⁺_F` is a single `Spin(V_F)`-orbit ([Igusa, Prop. 3],
`igusa_prop3_orbit_subfield`).

Correction of a slip: the paper says `d ∈ F`. For `d = 0` the statement fails: `0` and the pure
spinor `1` both lie in `J⁻¹(0)`, and `m_g(0) = 0 ≠ 1` for every `g`. The only reading under which it
holds, `d ∈ F^×`, is the one stated here (REPORT.md). -/
theorem remark10_1_2_orbit (F : Subfield ℂ) (d : F) (hd : d ≠ 0) (x y : S F 3)
    (hx : x ∈ Splus F 3) (hy : y ∈ Splus F 3) (hxd : J F x = d) (hyd : J F y = d) :
    ∃ g : Spin F 3, m F 3 (g : C F 3) x = y := by
  sorry

/-- **Remark 10.1.2(1)** (no label), second sentence: if `w = 1 + e₁₄^* + e₂₅^* + d e₃₆^*`,
`d ∈ F`, then `J(w) = d` (0-based indices: `e₁₄^* = eStar F 0 3`, etc.). The paper has `F ⊆ ℂ`; the
identity holds over every field of characteristic zero. -/
theorem remark10_1_2_value (F : Type*) [Field F] [CharZero F] (d : F) :
    J F (1 + eStar F 0 3 + eStar F 1 4 + d • eStar F 2 5) = d := by
  sorry

/-- **Remark 10.1.2(2)** (no label), first sentence: the secant `ℙ(P_w)` of Lemma 10.1.1 meets the
quartic `V(J)` at the same two points `[u₁], [u₂]` at which it meets the spinor variety, each with
multiplicity `2`. Precise form: the restriction of `J` to `P_w = span{u₁, u₂}` is
`J(a u₁ + b u₂) = c a² b²` for a constant `c ≠ 0`. -/
theorem remark10_1_2_secant (w : S ℂ 3) (hw : w ∈ Splus ℂ 3) (hJ : J ℂ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : w ∈ P) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a b : ℂ, J ℂ (a • u₁ + b • u₂) = c * a ^ 2 * b ^ 2 := by
  sorry

/-- **Remark 10.1.2(2)** (no label), the reason given there: the even spinor variety is contained
in the singular locus of `V(J)`. Precise form: at every even pure spinor `u ∈ S⁺_ℂ`, `J` vanishes
and so does its differential (every directional derivative `t ↦ J(u + t x)` at `t = 0`). -/
theorem remark10_1_2_singular (u : S ℂ 3) (hu : IsEvenPureSpinor ℂ 3 u) :
    J ℂ u = 0 ∧ ∀ x : S ℂ 3, HasDerivAt (fun t : ℂ => J ℂ (u + t • x)) 0 0 := by
  sorry

/-- **Remark 10.1.2(2)** (no label), second sentence: for `w ∈ S⁺_ℚ` (with `J(w) ≠ 0`) the plane
`P_w` is defined over `ℚ` (`lemma10_1_1_rational`), and so the length-two subscheme
`ℙ(P_w) ∩ (spinor variety) = {[u₁], [u₂]}` is defined over `ℚ`. Precise form (Galois descent for
the reduced subscheme of two points): every field automorphism `τ` of `ℂ`, acting on coordinates of
`S_ℂ`, permutes the two lines `ℂ u₁`, `ℂ u₂`. -/
theorem remark10_1_2_rational (w : S ℚ 3) (hw : w ∈ Splus ℚ 3) (hJ : J ℚ w ≠ 0)
    (P : Submodule ℂ (S ℂ 3)) (u₁ u₂ : S ℂ 3) (hP : IsTransversalSecant ℂ 3 P u₁ u₂)
    (hwP : bcS ℚ ℂ 3 w ∈ P) (τ : ℂ ≃+* ℂ) :
    ({Submodule.span ℂ {conjS τ 3 u₁}, Submodule.span ℂ {conjS τ 3 u₂}} :
        Set (Submodule ℂ (S ℂ 3))) =
      {Submodule.span ℂ {u₁}, Submodule.span ℂ {u₂}} := by
  sorry

end WeilClasses
