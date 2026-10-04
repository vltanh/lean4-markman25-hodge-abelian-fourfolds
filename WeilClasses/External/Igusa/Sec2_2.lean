module

public import WeilClasses.PureSpinor.Stabilizer

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

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Igusa, Lemma 1]** (kernel), as used in §2.2: for even pure spinors `u₁, u₂` with
`W₁ ∩ W₂ = 0`, the kernel of `Spin(V_F)_{ℓ₁,ℓ₂} → GL(W₁)` is `{±1}`. -/
theorem igusa_lemma1_ker (u₁ u₂ : S F n) (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥)
    (g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n))) :
    pairRestrict F n u₁ u₂ g = 1 ↔
      ((g : Spin F n) : C F n) = 1 ∨ ((g : Spin F n) : C F n) = -1 := by
  sorry

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
  sorry

/-- **[Igusa, Lemma 1]** (the action on `W₂`), as used in §2.2: an element `g` of
`Spin(V_F)_{ℓ₁,ℓ₂}` acts on `W₂ ≅ W₁*` by the inverse transpose of its action on `W₁`, i.e.
`(ρ(g) x, ρ(g) y)_V = (x, y)_V` for `x ∈ W₁`, `y ∈ W₂`. -/
theorem igusa_lemma1_dual (u₁ u₂ : S F n)
    (g : (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)))
    (x y : V F n) (hx : x ∈ ann F n u₁) (hy : y ∈ ann F n u₂) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  sorry

/-- **[Igusa, Lemma 1]** (proof; the second displayed formula for `φ(sᵢ(λ))` in [Igusa, §2]; see
also [Chevalley, III.3.2]), as used in §2.2 for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`: if `g ∈ Spin(V_F)` stabilizes
the line of a nonzero even pure spinor `u`, `g u = c u`, then `c² = det(ρ(g)|_{ker m_u})`. (For
`n = 0`, `u = 0` is pure and `c` is arbitrary, hence `u ≠ 0`.) -/
theorem igusa_lemma1_sq (u : S F n) (hu : IsEvenPureSpinor F n u) (hu0 : u ≠ 0) (g : Spin F n)
    (hg : g ∈ lineStabilizer F n u) (c : F) (hc : m F n (g : C F n) u = c • u) :
    c ^ 2 = LinearMap.det (annRestrict F n u ⟨g, hg⟩) := by
  sorry

/-- **[Igusa, Lemma 2]** and the remark following it, `n` odd, as used in Remark 2.2.3: for `n ≥ 3`
odd, even pure spinors `u₁, u₂` with `W₁ ∩ W₂ = 0` and `a, b ≠ 0`, the stabilizer of
`w = a u₁ + b u₂` in `Spin(V_F)` is the pointwise stabilizer of `u₁` and `u₂`. -/
theorem igusa_lemma2_stab_odd (hn : 3 ≤ n) (hodd : Odd n) (u₁ u₂ : S F n)
    (h₁ : IsEvenPureSpinor F n u₁) (h₂ : IsEvenPureSpinor F n u₂)
    (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) =
      fixingSpin F n (Submodule.span F {u₁, u₂}) := by
  sorry

/-- **[Igusa, Lemma 2]** and the remark following it, `n` even, as used in Remark 2.2.3: for
`n ≥ 3` even, the stabilizer of `w = a u₁ + b u₂` has two connected components, the identity
component being the pointwise stabilizer of `u₁` and `u₂`. For `F`-points: the pointwise stabilizer
of `u₁, u₂` is a normal subgroup of index at most `2` of the stabilizer of `w`. -/
theorem igusa_lemma2_stab_even (hn : 3 ≤ n) (heven : Even n) (u₁ u₂ : S F n)
    (h₁ : IsEvenPureSpinor F n u₁) (h₂ : IsEvenPureSpinor F n u₂)
    (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    fixingSpin F n (Submodule.span F {u₁, u₂}) ≤
        fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}) ∧
      ((fixingSpin F n (Submodule.span F {u₁, u₂})).subgroupOf
          (fixingSpin F n (Submodule.span F {a • u₁ + b • u₂}))).Normal ∧
      (fixingSpin F n (Submodule.span F {u₁, u₂})).relIndex
          (fixingSpin F n (Submodule.span F {a • u₁ + b • u₂})) ≤ 2 := by
  sorry

end WeilClasses
