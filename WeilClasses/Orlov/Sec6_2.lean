module

public import WeilClasses.Secant.Defs
public import WeilClasses.Orlov.Sec6_1
public import WeilClasses.PureSpinor.Lemma2_2_7
public import WeilClasses.Hermitian.ComplexStructures

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
  (6.1.8)) and the claims of its proof (`lemma6_2_3_rhoPrime_invariant`,
  `lemma6_2_3_lowest`, `lemma6_2_3_injective`, `lemma6_2_3_c1N`).
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

variable {n : ℕ} {d : ℚ}

/-! ## `H²(X × X̂, ℚ)_P` -/

namespace KSecant

variable (P : KSecant n d)

/-- `H²(X × X̂, ℚ)_P ⊆ H²(X × X̂, ℚ)`. -/
theorem H2P_le : P.H2P ≤ ⋀[ℚ]^2 (V ℚ n) := by
  sorry

/-- `H²_P` contains no non-zero `Spin(V)_P`-invariant class: it is the sum of the non-trivial
irreducible subrepresentations of `H²(X × X̂, ℚ)` (used for the uniqueness in Lemma 6.2.3 and in
Remark 6.2.4). -/
theorem H2P_inf_invQ (hd : 0 < d) (hP : ¬ P.IsIsotropic) : P.H2P ⊓ P.invQ 2 = ⊥ := by
  sorry

/-- (§6.2, TeX lines 2414–2416) "`H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P + ℚ Ξ_P`, by Lemma 2.2.7", with `Ξ_P`
regarded as the class `h = Ξ_P^♯ ∈ ⋀² V_ℚ` (`hClass`). Needs `n ≥ 2` (the paper's standing
assumption): for `n = 1` the invariants of `⋀² V_ℚ` form the three-dimensional middle degree. -/
theorem exteriorPower_two_eq (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (hn : 2 ≤ n) :
    ⋀[ℚ]^2 (V ℚ n) = P.H2P ⊔ Submodule.span ℚ {P.hClass hP.isCompl} := by
  sorry

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
  sorry

/-- **(6.2.4)** (`eq-N-g-beta`): for `g ∈ Spin(V)_P`, `β = ch(N_g) ρ_g(β)`, where `N_g` is the line
bundle of (6.1.8) (`ρ'_g = ch(N_g) ∪ ρ_g`; in the model `ch(N_g) = exp(c)`, `c = c₁(N_g) ∈ ⋀² V_ℚ`,
which exists by `equation6_1_8_integral`). Here `β = φ(w₂ ⊗ τ w₁)` with `w₁, w₂ ∈ P`. -/
theorem equation6_2_4 (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (g : Spin ℚ n)
    (hg : g ∈ P.spinPZ) (c : ExtV ℚ n)
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    secantSqClass ℚ n w₂ w₁ = IsNilpotent.exp c * rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) := by
  sorry

/-- **(6.2.4)** (`eq-N-g-beta`), as printed: given `g ∈ Spin(V)_P` there exists a topological
complex line bundle `N_g` on `X × X̂` such that `β = ch(N_g) ρ_g(β)`. Model: an integral class
`c = c₁(N_g) ∈ H²(X × X̂, ℤ)` with `β = exp(c) ρ_g(β)`. -/
theorem equation6_2_4_exists (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (g : Spin ℚ n)
    (hg : g ∈ P.spinPZ) :
    ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧
      secantSqClass ℚ n w₂ w₁ = IsNilpotent.exp c * rhoExt ℚ n g (secantSqClass ℚ n w₂ w₁) := by
  sorry

/-- (Proof of Lemma 6.2.3, TeX lines 2459–2461) If `k < n` is the least `j` with `β_j ≠ 0`, then
`β_k` is `Spin(V)_P`-invariant with respect to `ρ` (by the minimality of `k`) and hence a non-zero
multiple of `Ξ_P^k` (`h^k`, `h = Ξ_P^♯`), by `k < dim X` (Lemma 2.2.7). -/
theorem lemma6_2_3_lowest (hP : Assumption2_4_1 P J) (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ)
    (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n) :
    projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) ∈ invariantsExt ℚ n P.spinPZ ∧
      ∃ c : ℚ, c ≠ 0 ∧
        projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) = c • P.hClass hP.isCompl ^ k := by
  sorry

/-- (Proof of Lemma 6.2.3, TeX lines 2461–2462) "the homomorphism
`β_k ∪ (•) : H²(X × X̂, ℚ) → H^{2k+2}(X × X̂, ℚ)` is injective, as `Ξ_P` is ample" (hard Lefschetz;
`k < n` and `dim(X × X̂) = 2n`). -/
theorem lemma6_2_3_injective (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (x : ExtV ℚ n) (hx : x ∈ ⋀[ℚ]^2 (V ℚ n))
    (h0 : projDeg ℚ n (2 * k) (secantSqClass ℚ n w₂ w₁) * x = 0) : x = 0 := by
  sorry

/-- **Lemma 6.2.3** (`ch-3-alpha-is-second-partial-of-J`). Assume that `k < dim_ℂ(X) = n`. There
exists a unique class `ℓ` of type `(1,1)` in `H²(X × X̂, ℚ)_P` such that the class
`α := exp(ℓ) ch(Φ(F₂ ⊠ F₁^∨))` is `Spin(V)_P`-invariant.

Model: `ch(Φ(F₂ ⊠ F₁^∨)) = φ(w₂ ⊗ τ w₁)` (`secantSqClass ℚ n w₂ w₁`) with `wᵢ = ch(Fᵢ) ∈ P`; `k` the
least `j` with `ch_j ≠ 0`; invariance for the `ρ`-action of the integral group `Spin(V)_P`; "type
`(1,1)`" for the complex structure of `X × X̂`. Setting of §6.2: Assumption 2.4.1 and `Ξ_P` ample
(`hample`, see the module docstring). Reading: "unique class `ℓ` of type `(1,1)` in `H²_P`" is read
literally (uniqueness among the `(1,1)`-classes of `H²_P`); the proof gives uniqueness in all of
`H²_P` (`lemma6_2_3_unique`). -/
theorem lemma6_2_3 (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n) :
    ∃! ℓ : ExtV ℚ n, ℓ ∈ hodgeClassesV n (productStructure n J) 1 ∧ ℓ ∈ P.H2P ∧
      IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ := by
  sorry

/-- **Lemma 6.2.3** (`ch-3-alpha-is-second-partial-of-J`), last sentence: "The class `ℓ` depends on
the secant line `P`, but not on the choice of `Fᵢ`, `i = 1, 2`." If `(w₁, w₂)` and `(w₁', w₂')` are
two pairs of classes in `P` satisfying the hypothesis of the lemma, and `ℓ, ℓ' ∈ H²_P` make
`exp(ℓ) φ(w₂ ⊗ τ w₁)` and `exp(ℓ') φ(w₂' ⊗ τ w₁')` invariant, then `ℓ = ℓ'`. (With
`(w₁', w₂') = (w₁, w₂)`, this is the uniqueness of `ℓ` in `H²_P` proved in the paper.) -/
theorem lemma6_2_3_unique (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x)
    (w₁ w₂ w₁' w₂' : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (hw₁' : w₁' ∈ P.Pℚ)
    (hw₂' : w₂' ∈ P.Pℚ) (k k' : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (hk' : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂' w₁') ≠ 0} k')
    (hkn' : k' < n) (ℓ ℓ' : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P) (hℓ' : ℓ' ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (hα' : IsNilpotent.exp ℓ' * secantSqClass ℚ n w₂' w₁' ∈ invariantsExt ℚ n P.spinPZ) :
    ℓ = ℓ' := by
  sorry

/-- (Proof of Lemma 6.2.3, TeX lines 2488–2491) `c₁(N_g) = ρ_g(ℓ) - ℓ` for all `g ∈ Spin(V)_P`, where
`ℓ` is the class of Lemma 6.2.3 and `c₁(N_g) = c` is the class of (6.1.8)
(`ρ'_g = exp(c) ∪ ρ_g`). -/
theorem lemma6_2_3_c1N (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) (k : ℕ)
    (hk : IsLeast {j : ℕ | projDeg ℚ n (2 * j) (secantSqClass ℚ n w₂ w₁) ≠ 0} k) (hkn : k < n)
    (ℓ : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ)
    (g : Spin ℚ n) (hg : g ∈ P.spinPZ) (c : ExtV ℚ n) (hc2 : c ∈ ⋀[ℚ]^2 (V ℚ n))
    (hc : ∀ x : ExtV ℚ n, rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x) :
    c = rhoExt ℚ n g ℓ - ℓ := by
  sorry

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
  sorry

/-- **Remark 6.2.4** (`remark-k-equal-0-case`), last sentence: "In this case `ℓ = (t Ξ_P - β₁)/r`,
where `t` is the unique scalar such that `ℓ` belongs to `H²(X × X̂, ℚ)_P`": every `ℓ ∈ H²_P` making
`exp(ℓ) β` invariant (the class of Lemma 6.2.3) is `(t Ξ_P - β₁)/r` for this `t`. -/
theorem remark6_2_4_ell (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (hample : ∀ x : V ℝ n, x ≠ 0 → 0 < P.gI hP.isCompl (productStructure n J) x x)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ)
    (hr : rankExt ℚ n (secantSqClass ℚ n w₂ w₁) ≠ 0) (t : ℚ)
    (ht : (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
        (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) ∈ P.H2P)
    (ℓ : ExtV ℚ n) (hℓ : ℓ ∈ P.H2P)
    (hα : IsNilpotent.exp ℓ * secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ) :
    ℓ = (rankExt ℚ n (secantSqClass ℚ n w₂ w₁))⁻¹ •
      (t • P.hClass hP.isCompl - projDeg ℚ n 2 (secantSqClass ℚ n w₂ w₁)) := by
  sorry

/-! ## Lemma 6.2.5 -/

section Lemma625

variable (F : Type*) [Field F] [CharZero F]

/-- **Lemma 6.2.5** (`example-conjecture-holds-for-abelian-surfaces`). Proposition 6.1.2 holds in case
`X` is an abelian surface (`n = 2`): `ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`.

The paper proves this from ideal sheaves of points on `X` and a Zariski-density argument, and then
deduces Proposition 6.1.2 for all `n` from it. Here Proposition 6.1.2 is proved for every `n` by the
authorized algebraic departure (`notes/design.md`), and this lemma is its case `n = 2`
(`proposition6_1_2`). As there, `g` ranges over `Spin(V_F)` for every field `F` of characteristic
`0` (the paper: the integral `Spin(V)`). -/
theorem lemma6_2_5 (g : Spin F 2) (x : ExtV F 2) :
    rhoPrime F 2 g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F 2 - rhoExt F 2 g (c1P F 2))) * rhoExt F 2 g x :=
  proposition6_1_2 F 2 g x

/-- **(6.2.5)** (`eq-c-1-N-g`): `c₁(N_g) = ½[c₁(𝒫) - ρ_g(c₁(𝒫))]` (abelian surfaces), where `c₁(N_g)`
is the class of (6.1.8) (`ρ'_g = exp(c₁(N_g)) ∪ ρ_g`, `c₁(N_g) ∈ H²`). The paper derives it for
`g ∈ Spin(V)_P` and every negative definite rational plane `P` containing `w_n`; in the model it holds
for every `g ∈ Spin(V_F)` (Proposition 6.1.2), which is what the paper concludes. -/
theorem equation6_2_5 (g : Spin F 2) (c : ExtV F 2) (hc2 : c ∈ ⋀[F]^2 (V F 2))
    (hc : ∀ x : ExtV F 2, rhoPrime F 2 g x = IsNilpotent.exp c * rhoExt F 2 g x) :
    c = (2 : F)⁻¹ • (c1P F 2 - rhoExt F 2 g (c1P F 2)) := by
  sorry

end Lemma625

/-- (Proof of Lemma 6.2.5, TeX lines 2557–2558: "The class `ℓ` is the projection of `-c₁(𝒫)/2` to
`H²(X × X̂, ℚ)_P`, by Remark 6.2.4.") In the model this holds for every `n` and every pair of classes
of `P` (a consequence of Proposition 6.1.2): with `-½ c₁(𝒫) = ℓ₀ + t Ξ_P`, `ℓ₀ ∈ H²_P`, the class `ℓ`
of Lemma 6.2.3 is `ℓ₀`. Stated: `ℓ₀ := -½ c₁(𝒫) - t h ∈ H²_P` makes `exp(ℓ₀) φ(w₂ ⊗ τ w₁)` invariant
for all `w₁, w₂ ∈ P`. (Checked numerically for `n = 2, 3`.) -/
theorem ell_eq_proj_c1P (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (t : ℚ) (ht : -((2 : ℚ)⁻¹ • c1P ℚ n) - t • P.hClass hP.isCompl ∈ P.H2P)
    (w₁ w₂ : S ℚ n) (hw₁ : w₁ ∈ P.Pℚ) (hw₂ : w₂ ∈ P.Pℚ) :
    IsNilpotent.exp (-((2 : ℚ)⁻¹ • c1P ℚ n) - t • P.hClass hP.isCompl) *
      secantSqClass ℚ n w₂ w₁ ∈ invariantsExt ℚ n P.spinPZ := by
  sorry

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
  sorry

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
  sorry

end WeilClasses
