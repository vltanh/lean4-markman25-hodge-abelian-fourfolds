module

public import WeilClasses.PureSpinor.Lemma2_2_1
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Stabilizers of `K`-secants: `Spin(V_K)_{ℓ₁,ℓ₂}`, `Spin(V_K)_P`, Lemma 2.2.2 and Remark 2.2.3

Paper §2.2, from "Assume that `W₁ ∩ W₂` is the zero subspace" to Remark 2.2.3. Throughout, the
standing hypothesis of the paper `W₁ ∩ W₂ = 0` is an explicit hypothesis `hW`, and `0 < d` is the
paper's "`K` purely imaginary".

## Main definitions

* `WeilClasses.annRestrict F n u`: the action `Spin(V_F)_{[u]} → End(ker m_u)` of the stabilizer of
  the line `[u]` on `W = ker m_u`.
* `WeilClasses.pairRestrict F n u₁ u₂`: the homomorphism
  `Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`.
* `WeilClasses.specialLinearUnits F W`: `SL(W) ⊆ GL(W)`.
* `WeilClasses.KSecant.restrictW₁`: `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, and `KSecant.restrictW₁P`, its
  restriction to `Spin(V_K)_P`.
* `WeilClasses.KSecant.pairingW₂`: the identification `W₂ → W₁*` given by the pairing of `V_K`.

## Statements

* The claims attributed to [Igusa, Lemma 1] (`KSecant.restrictW₁_eq_one_iff`,
  `KSecant.range_restrictW₁` (corrected, see below),
  `KSecant.rho_eq_one_iff`, `KSecant.pairingW₂_bijective`, `KSecant.pairingW₂_rho`),
  `KSecant.det₂_eq_inv` (`det₂ = det₁⁻¹`), `KSecant.χ₁_sq`, `KSecant.χ₂_sq` (`ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`).
* **Lemma 2.2.2** with the misprint `SL_n(K)` corrected to `SL_{2n}(K)` (`lemma2_2_2`,
  `lemma2_2_2_restrict`).
* **Remark 2.2.3** ([Igusa, Lemma 2] and the remark after it): `remark2_2_3_not_pure`,
  `remark2_2_3_odd`, `remark2_2_3_even`, `remark2_2_3_determines`, `remark2_2_3_unique_secant`.

## A false claim of the paper

The paper says "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`". At the
level of `K`-points this contradicts the paper's own `ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁` (`χ₁² = det₁`): `det₁` only
takes square values, so the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)` is the subgroup of
endomorphisms with square determinant. For instance, if `x ∈ W₂`, `y ∈ W₁`, `(x, y)_V = 1`, the
element of `SO(V_K)` acting by `a ∉ K^{×2}` on `y`, by `a⁻¹` on `x` and trivially on the
orthogonal of `x, y` is not in `ρ(Spin(V_K))`: its two lifts `±(√a⁻¹ x y + √a y x)` to
`Spin(V_{K̄})` are not `K`-rational. The isomorphism holds for the algebraic groups (over `K̄`). We
state the corrected claim (`KSecant.range_restrictW₁`), as agreed with the project owner.
Lemma 2.2.2 is unaffected.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section General

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The stabilizer of the line `[u]` preserves `ker m_u` (by `WeilClasses.ann_m_spin`). -/
theorem rho_mem_ann_of_mem_lineStabilizer (u : S F n) (g : Spin F n)
    (hg : g ∈ lineStabilizer F n u) (v : V F n) (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n u := by
  sorry

/-- The action `Spin(V_F)_{[u]} → End(ker m_u)` of the stabilizer of the line `[u]` on the isotropic
subspace `W = ker m_u`, by restriction of `ρ`. -/
noncomputable def annRestrict (u : S F n) : lineStabilizer F n u →* Module.End F (ann F n u) where
  toFun g := (rho F n (g : Spin F n)).toLinearMap.restrict
    (rho_mem_ann_of_mem_lineStabilizer F n u g g.2)
  map_one' := by sorry
  map_mul' := by sorry

/-- The homomorphism `Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def pairRestrict (u₁ u₂ : S F n) :
    (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)) →*
      (Module.End F (ann F n u₁))ˣ :=
  ((annRestrict F n u₁).comp (Subgroup.inclusion inf_le_left)).toHomUnits

/-- `SL(W)`: the automorphisms of determinant one, as a subgroup of `GL(W) = (End W)ˣ`. -/
noncomputable def specialLinearUnits (W : Type*) [AddCommGroup W] [Module F W] :
    Subgroup (Module.End F W)ˣ :=
  (Units.map (LinearMap.det : Module.End F W →* F)).ker

end General

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- The homomorphism `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}` (§2.2). -/
noncomputable def restrictW₁ : P.spinL₁L₂ →* (Module.End (Kd d) P.W₁)ˣ :=
  pairRestrict (Kd d) n P.u₁ P.u₂

/-- `det₁` is the determinant of `restrictW₁`. -/
theorem det_restrictW₁ (g : P.spinL₁L₂) :
    LinearMap.det ((P.restrictW₁ g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) =
      P.det₁ g :=
  rfl

/-- The pairing of `V_K` identifies `W₂` with `W₁*`: `y ↦ (x ↦ (x, y)_V)` (§2.2). -/
noncomputable def pairingW₂ : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁ :=
  ((pairing (Kd d) n).compl₁₂ P.W₁.subtype P.W₂.subtype).flip

/-- **[Igusa, Lemma 1]** as used in §2.2 (kernel): the kernel of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)` is
`{±1}`, so that `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` embeds in `GL(W₁)`. -/
theorem restrictW₁_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.restrictW₁ g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 := by
  sorry

/-- The claim "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`" (§2.2,
[Igusa, Lemma 1]), on `K`-points: the image of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`,
consists of the automorphisms whose determinant is a square in `K` (it contains `SL(W₁)`, and
`det₁ = χ₁²`); with `restrictW₁_eq_one_iff`, `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to that subgroup.

Correction of the paper (agreed with the project owner; REPORT.md): the paper says the quotient is
isomorphic to `GL(W₁)`. That holds for the algebraic groups (over `K̄`, as in Igusa's lemma) but not
for `K`-points: `diag(a, 1, …, 1)` with `a ∉ K^{×2}` is not in the image (its lifts
`±(√a⁻¹ x y + √a y x)` are not `K`-rational). Lemma 2.2.2 and the rest of the paper are unaffected. -/
theorem range_restrictW₁ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) =
      {A : (Module.End (Kd d) P.W₁)ˣ |
        IsSquare (LinearMap.det (A : Module.End (Kd d) P.W₁))} := by
  sorry

/-- "**The quotient maps injectively into `SO⁺(V_K)`**" (§2.2, [Igusa, Lemma 1]): an element of
`Spin(V_K)_{ℓ₁,ℓ₂}` acting trivially on `V_K` is `±1`. -/
theorem rho_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    rho (Kd d) n g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 := by
  sorry

/-- "**`W₂` is identified with `W₁*` via the bilinear pairing of `V_K`**" (§2.2): when
`W₁ ∩ W₂ = 0`, `y ↦ (·, y)_V|_{W₁}` is an isomorphism `W₂ ≅ W₁*`. -/
theorem pairingW₂_bijective (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Bijective P.pairingW₂ := by
  sorry

/-- "**The element of `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` corresponding to `g ∈ GL(W₁)` acts on `W₂` via
`(g*)⁻¹`**, where `W₂` is identified with `W₁*` via the bilinear pairing of `V_K`" (§2.2,
[Igusa, Lemma 1]): under `pairingW₂`, `ρ(g)|_{W₂}` is the inverse transpose of `ρ(g)|_{W₁}`. -/
theorem pairingW₂_rho (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) (y : V (Kd d) n)
    (hy : y ∈ P.W₂) :
    P.pairingW₂ ⟨rho (Kd d) n g y, P.rho_mem_W₂ g y hy⟩ =
      LinearMap.dualMap
        (((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁)
        (P.pairingW₂ ⟨y, hy⟩) := by
  sorry

/-- "**`det₂(s) = det₁(s)⁻¹`**" (§2.2), for `s ∈ Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem det₂_eq_inv (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.det₂ g = (P.det₁ g)⁻¹ := by
  sorry

/-- "**`ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁`**" (§2.2, by the proof of [Igusa, Lemma 1] and [Chevalley, III.3.2]): the
character `χ₁` of `Spin(V_K)_{ℓ₁,ℓ₂}` on `ℓ̃₁` satisfies `χ₁² = det₁`. Used again in §6.4
("`ℓ̃ᵢ²` is the character `⋀^{2n} Wᵢ ≅ detᵢ`"). -/
theorem χ₁_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₁ g ^ 2 = P.det₁ g := by
  sorry

/-- "**`ℓ̃₂ ⊗ ℓ̃₂ ≅ det₂`**" (§2.2): `χ₂² = det₂`. -/
theorem χ₂_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₂ g ^ 2 = P.det₂ g := by
  sorry

/-! ## Lemma 2.2.2 -/

/-- `Spin(V_K)_P ⊆ Spin(V_K)_{ℓ₁,ℓ₂}`: an element fixing `P_K` pointwise fixes `u₁` and `u₂`. -/
theorem spinPK_le_spinL₁L₂ : P.spinPK ≤ P.spinL₁L₂ := by
  sorry

/-- The homomorphism `Spin(V_K)_P → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def restrictW₁P : P.spinPK →* (Module.End (Kd d) P.W₁)ˣ :=
  P.restrictW₁.comp (Subgroup.inclusion P.spinPK_le_spinL₁L₂)

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint corrected: the group `Spin(V_K)_P` is
isomorphic to `SL_{2n}(K)`. The paper prints `SL_n(K)`; this is an obvious misprint, since `W₁` has
dimension `2n` and the text just before says `GL(W₁) ≅ GL_{2n}(K)`. Standing hypothesis:
`W₁ ∩ W₂ = 0`. See `lemma2_2_2_restrict` for the isomorphism itself. -/
theorem _root_.WeilClasses.lemma2_2_2 (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Nonempty (P.spinPK ≃* Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d)) := by
  sorry

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint `SL_n(K)` corrected to `SL_{2n}(K)`,
in the form of its proof: `g ↦ ρ(g)|_{W₁}` maps `Spin(V_K)_P` isomorphically onto `SL(W₁)`.
(The proof's "`Spin(V_K)_P` is the kernel of `det₁` in `Spin(V_K)_{ℓ₁,ℓ₂}`" should read: the kernel
of `det₁` is `{±1} · Spin(V_K)_P`; `Spin(V_K)_P` is the kernel of `χ₁`, and `-1 ∉ Spin(V_K)_P`.) -/
theorem _root_.WeilClasses.lemma2_2_2_restrict (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Injective P.restrictW₁P ∧
      P.restrictW₁P.range = specialLinearUnits (Kd d) P.W₁ := by
  sorry

/-! ## Remark 2.2.3 -/

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), first claim
([Igusa, Lemma 2]): for `n ≥ 3`, a vector `w ∈ P_K` on neither `ℓ̃₁` nor `ℓ̃₂` is not a pure spinor
("as commented above", i.e. by [Chevalley, III.1.12]). Reading: `w` is a `K`-point of the plane
(`w ∈ P_K`); this includes the nonzero rational points of `P`. -/
theorem _root_.WeilClasses.remark2_2_3_not_pure (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    ¬ IsEvenPureSpinor (Kd d) n w := by
  sorry

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` odd
([Igusa, Lemma 2] and the remark after it): for `n ≥ 3` odd and `w ∈ P_K` on neither `ℓ̃₁` nor
`ℓ̃₂`, the stabilizer of `w` in `Spin(V_K)` is `Spin(V_K)_P`. -/
theorem _root_.WeilClasses.remark2_2_3_odd (hd : 0 < d) (hn : 3 ≤ n) (hodd : Odd n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) = P.spinPK := by
  sorry

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` even
([Igusa, Lemma 2] and the remark after it): "the stabilizer has two connected components and the
identity component is `Spin(V_K)_P`". Reading for the group of `K`-points: `Spin(V_K)_P` is a normal
subgroup of index at most `2` of the stabilizer of `w` in `Spin(V_K)`. (The index is in fact `2`:
the non-identity component, the elements exchanging `ℓ₁` and `ℓ₂`, has `K`-points.) -/
theorem _root_.WeilClasses.remark2_2_3_even (hd : 0 < d) (hn : 3 ≤ n) (heven : Even n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    P.spinPK ≤ fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) ∧
      (P.spinPK.subgroupOf (fixingSpin (Kd d) n (Submodule.span (Kd d) {w}))).Normal ∧
      P.spinPK.relIndex (fixingSpin (Kd d) n (Submodule.span (Kd d) {w})) ≤ 2 := by
  sorry

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "in particular,
`w` determines `P`": any `K`-secant `P'` with `W₁' ∩ W₂' = 0` whose plane contains `w` has the same
plane `P'_K = P_K` (hence the same rational plane). -/
theorem _root_.WeilClasses.remark2_2_3_determines (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (P' : KSecant n d) (hW' : P'.W₁ ⊓ P'.W₂ = ⊥) (hwP' : w ∈ P'.PK) :
    P'.PK = P.PK := by
  sorry

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "`ℙ(P)` is the
unique secant to the spinor variety through `w`": if `w` lies on the line through two distinct
points `[x], [y]` of the (complex) even spinor variety, then that line is `ℙ(P_ℂ)`. -/
theorem _root_.WeilClasses.remark2_2_3_unique_secant (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (x y : S ℂ n) (hx : IsEvenPureSpinor ℂ n x) (hy : IsEvenPureSpinor ℂ n y)
    (hxy : LinearIndependent ℂ ![x, y]) (hw : bcS (Kd d) ℂ n w ∈ Submodule.span ℂ {x, y}) :
    Submodule.span ℂ {x, y} =
      Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁, bcS (Kd d) ℂ n P.u₂} := by
  sorry

end KSecant

end WeilClasses
