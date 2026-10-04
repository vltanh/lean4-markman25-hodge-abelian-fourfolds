module

public import WeilClasses.PureSpinor.CM
public import WeilClasses.PureSpinor.Lemma2_2_1

/-!
# The action of `K` on `V_ℚ` and Lemma 2.2.4 (paper §2.2)

Setting of the paper (§2.2, before Lemma 2.2.4): `P ⊆ S⁺_ℚ` is a non-isotropic rational plane
meeting the spinor variety in two `σ`-conjugate points `ℓ₁, ℓ₂` (a `WeilClasses.KSecant` with
`¬ P.IsIsotropic`); then `W₁ ∩ W₂ = 0` by Lemma 2.2.1, i.e. `V_K = W₁ ⊕ W₂`
(`WeilClasses.KSecant.isCompl_of_not_isIsotropic`). The similarity group `Õ(V_ℚ)` (2.2.3)
(`WeilClasses.Otilde`) and the action `η_λ` (2.2.4) (`WeilClasses.KSecant.ηK` on `V_K`,
`WeilClasses.KSecant.η` on `V_ℚ`) are in `WeilClasses.PureSpinor.CM`.

## Statements

* `KSecant.range_bcV_eq`: "the subset `V_ℚ` of `V_K` is `{v₁ + σ(v₁) : v₁ ∈ W₁}`";
* `KSecant.σV_ηK`, `KSecant.ηK_bcV`: `η_λ` commutes with `σ` and leaves `V_ℚ` invariant;
* `KSecant.ηHom`: `η` as a ring homomorphism `K → End_ℚ(V_ℚ)` (the paper's homomorphism
  `η : K^× → GL(V_ℚ)` (2.2.4), "an embedding of `K` in `End(V_ℚ)`" in the table of notation), with
  `KSecant.ηHom_injective`;
* `KSecant.pairing_η`: `(η_λ(v), η_λ(v'))_V = Nm(λ)(v, v')_V` (proof of Lemma 2.2.4; used in §2.4
  for `f = η_{√-d}`);
* **Lemma 2.2.4** (`lemma2_2_4`): the centralizer of `ρ(Spin(V_ℚ)_P)` in `Õ(V_ℚ)` is `η(K^×)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- "**The subset `V_ℚ` of `V_K` is equal to `{v₁ + σ(v₁) : v₁ ∈ W₁}`**" (§2.2), when
`V_K = W₁ ⊕ W₂`. -/
theorem range_bcV_eq (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    Set.range (bcV ℚ (Kd d) n) = {v | ∃ v₁ ∈ P.W₁, v = v₁ + σV n d v₁} := by
  sorry

/-- `η_λ` commutes with the Galois involution `σ` of `V_K` (§2.2). -/
theorem σV_ηK (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V (Kd d) n) :
    σV n d (P.ηK hW l v) = P.ηK hW l (σV n d v) := by
  sorry

/-- "**`η_λ` leaves `V_ℚ` invariant**" (§2.2): the rational endomorphism `η_λ` of (2.2.4) is the
restriction of `η_λ` on `V_K` to `V_ℚ`. -/
theorem ηK_bcV (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V ℚ n) :
    P.ηK hW l (bcV ℚ (Kd d) n v) = bcV ℚ (Kd d) n (P.η hW l v) := by
  sorry

/-- `η_1 = id` (`η` is a homomorphism, (2.2.4)). -/
theorem η_one (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : P.η hW 1 = 1 := by
  sorry

/-- `η_{λλ'} = η_λ ∘ η_{λ'}` (`η` is a homomorphism, (2.2.4)). -/
theorem η_mul (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.η hW (l * l') = P.η hW l * P.η hW l' := by
  sorry

/-- `η_{λ+λ'} = η_λ + η_{λ'}` (`η` is additive: `K` embeds in `End(V_ℚ)`). -/
theorem η_add (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.η hW (l + l') = P.η hW l + P.η hW l' := by
  sorry

/-- `η_0 = 0`. -/
theorem η_zero (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : P.η hW 0 = 0 := by
  sorry

/-- The homomorphism (2.2.4) `η : K → End_ℚ(V_ℚ)`, `λ ↦ η_λ`, as a ring homomorphism (the paper
restricts it to `K^× → GL(V_ℚ)`; the table of notation calls it "an embedding of `K` in
`End(V_ℚ)`"). -/
noncomputable def ηHom (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) : Kd d →+* Module.End ℚ (V ℚ n) where
  toFun := P.η hW
  map_one' := P.η_one hd hW
  map_mul' := P.η_mul hd hW
  map_zero' := P.η_zero hd hW
  map_add' := P.η_add hd hW

/-- `η` is injective (§10.2: "the injective group homomorphism `η : K^× → GL(V_ℚ)`"). -/
theorem ηHom_injective (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) :
    Function.Injective (P.ηHom hd hW) := by
  sorry

/-- **`η_λ` is a similarity with multiplier `Nm(λ)`** (proof of Lemma 2.2.4):
`(η_λ(v), η_λ(v'))_V = Nm(λ) (v, v')_V`. In particular `η_λ ∈ Õ(V_ℚ)` for `λ ≠ 0`; for
`f = η_{√-d}` this gives `(f(x), f(y))_V = d (x, y)_V` (§2.4). -/
theorem pairing_η (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v v' : V ℚ n) :
    pairing ℚ n (P.η hW l v) (P.η hW l v') = Kd.Nm d l * pairing ℚ n v v' := by
  sorry

/-- **Lemma 2.2.4** (`lemma-centralizer-of-rho-Spin-V-P`): the centralizer of `ρ(Spin(V_ℚ)_P)` in
`Õ(V_ℚ)` is `η(K^×)`. That is, for `g ∈ GL(V_ℚ)`: `g ∈ Õ(V_ℚ)` and `g` commutes with every `ρ(h)`,
`h ∈ Spin(V_ℚ)_P`, if and only if `g = η_λ` for some `λ ∈ K^×`.

Hypotheses of the paper at this point: `P` non-isotropic (hence `V_K = W₁ ⊕ W₂`, which is needed to
define `η`), `K` imaginary quadratic (`0 < d`). The group is the rational group `Spin(V_ℚ)_P`, as
printed. We add `2 ≤ n` (the paper's standing hypothesis), which the statement needs: for `n = 1`,
`Spin(V_K)_P ≅ SL₂(K)` and `W₁ ≅ W₁* ≅ W₂` as representations, so the commutant of
`ρ(Spin(V_ℚ)_P)` is a quaternion algebra over `ℚ`, larger than `K`.

Note for the proof: "`W₁` and `W₂` are `g`-invariant and `g` acts on `Wᵢ` by a scalar" uses that
`W₁`, `W₂` are non-isomorphic absolutely irreducible representations of `Spin(V_ℚ)_P`, which needs
the Zariski density of `Spin(V_ℚ)_P` in the algebraic group `Spin(V_K)_P ≅ SL(W₁)` (the paper does
not prove it). -/
theorem _root_.WeilClasses.lemma2_2_4 (hd : 0 < d) (hn : 2 ≤ n) (hP : ¬ P.IsIsotropic)
    (g : V ℚ n ≃ₗ[ℚ] V ℚ n) :
    (g ∈ Otilde n d ∧ ∀ h ∈ P.spinPℚ, g * rho ℚ n h = rho ℚ n h * g) ↔
      ∃ l : Kd d, l ≠ 0 ∧
        (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.η (P.isCompl_of_not_isIsotropic hd hP) l := by
  sorry

end KSecant

end WeilClasses
