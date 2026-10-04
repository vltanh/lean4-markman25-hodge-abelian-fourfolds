module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Main.Coordinates
public import WeilClasses.WeilType.Theta

/-!
# Characteristic classes of secant objects (paper §1.3, §6.2, §8.2–8.3): definitions

The cohomological objects attached to secant sheaves, in the model `H*(X × X̂, F) = ⋀• V_F`
(`ExtV F n`) and `H*(X, F) = S_F`.

## `κ` (§1.3)

For a class `ch ∈ H^{ev}(X × X̂, ℚ)` with graded summands `ch_i ∈ H^{2i}` and `ch₀ = r ≠ 0`,
`κ(ch) = exp(-ch₁/r) ch` (`WeilClasses.kappa`); `κ_k` is its summand in `H^{2k}`
(`WeilClasses.kappaDeg`). Here `r = ch₀` is the degree-`0` coefficient (`WeilClasses.rankExt`,
Mathlib's `ExteriorAlgebra.algebraMapInv`) and `ch₁` the degree-`2` component (`projDeg F n 2`).

## Secant classes (§1.3, Definition 6.2.2)

* `WeilClasses.tauExt`: the main anti-automorphism `τ` of `H*(X × X̂) = ⋀• V` (reversal,
  `(-1)^{k(k-1)/2}` on `⋀^k V`). For an object `G` of `Dᵇ(X × X̂)`, `ch(G^∨) = τ(ch G)` (geometric,
  the analogue of Remark 5.2.3; not formalized).
* `WeilClasses.secantSqClass F n w₁ w₂ = φ(w₁ ⊗ τ(w₂))`, `φ = phiOrlov` (6.1.3): for objects `F₁`,
  `F₂` of `Dᵇ(X)` with `ch(Fᵢ) = wᵢ`, this is `ch(Φ(F₁ ⊠ F₂^∨))`, since `ch(F₂^∨) = τ(ch F₂)` and the
  cohomological action of Orlov's equivalence is `φ` (both geometric: Remark 5.2.3 and GRR, not
  formalized). When `w₁, w₂ ∈ P`, `Φ(F₁ ⊠ F₂^∨)` is a *`P`-secant`^{⊠2}`-object* (§1.3,
  Definition 6.2.2, where the roles of `F₁`, `F₂` are exchanged: `Φ(F₂ ⊠ F₁^∨)` has class
  `secantSqClass F n w₂ w₁`). `secantSqClass F n w₁ w₂ = φ'(w₁ ⊗ w₂)`, `φ' = φ ∘ (id ⊗ τ)`
  (`secantSqClass_eq_phiPrime`).

## The class `h` of `Ξ_P` and `H²(X × X̂, ℚ)_P` (§1.3, §6.2, §8.3)

* `WeilClasses.formToExt2 F n B ∈ ⋀² V_F`: the class of a bilinear form `B` on `V_F` under the
  isomorphism `V_F ≅ V_F*`, `x ↦ (x, ·)_V`; for alternating `B` it is characterized by
  `⟪B^♯, (x, ·)_V ∧ (y, ·)_V⟫ = B(x, y)` (`formToExt2_spec`). In the basis `f_i, e_i` of `V`
  (`vecF`, `vecE`; `(f_i, e_j)_V = δ_{ij}`) it is
  `½ Σ B(f_i, f_j) e_i ∧ e_j + Σ B(f_i, e_j) e_i ∧ f_j + ½ Σ B(e_i, e_j) f_i ∧ f_j`.
* `WeilClasses.KSecant.hClass P hW = Ξ_P^♯`, the class in `H²(X × X̂, ℚ) = ⋀² V_ℚ` of the `2`-form
  `Ξ_P` (2.4.2). This is how the paper regards `Ξ_P` as an element of `H²(X × X̂, ℚ)` (§6.2:
  "`H²(X × X̂, ℚ) = H²(X × X̂, ℚ)_P + ℚ Ξ_P`"); the identification is `Spin(V)`-equivariant. The
  paper's ample class `h` spanning `H²(X × X̂, ℚ)^{Spin(V)_P}` (§1.3, §8.3) is a positive multiple of
  it; we take `h = Ξ_P^♯`. For `P = P_Θ` with `Θ = e₁ ∧ e₂ + ⋯` (`ThetaStd`) it is
  `d Θ + Θ̂`, `Θ̂ = f₁ ∧ f₂ + ⋯` (computed numerically for `n ≤ 3`; this is `WeilClasses.hV` of
  `WeilClasses.Main.Jacobian`).
* `WeilClasses.KSecant.H2P P`: `H²(X × X̂, ℚ)_P`, "the direct sum of all non-trivial irreducible
  `Spin(V)_P`-subrepresentations of `H²(X × X̂, ℚ)`" (§6.2). **Definition used:** the span of the
  vectors `ρ_g(x) - x`, `g ∈ Spin(V)_P` (the integral group `P.spinPZ`), `x ∈ ⋀² V_ℚ`. For a
  completely reducible representation `U` this is the sum of the non-trivial isotypic components
  (each non-trivial irreducible `U'` satisfies `U' = span{ρ_g x - x : x ∈ U'}`, and `ρ_g x - x` has no
  component in the invariants). `⋀² V_ℚ` is completely reducible under `Spin(V)_P` (over `K` it is
  `⋀²W₁ ⊕ ⋀²W₂ ⊕ sl(W₁) ⊕ K`, irreducible summands of `SL(W₁) ≅ Spin(V_K)_P`, in which `Spin(V)_P` is
  Zariski dense; see `WeilClasses.PureSpinor.Lemma2_2_7`), so the two definitions agree.

## The classes of §8.2 (`n = 3`)

`X` is the Jacobian of a non-hyperelliptic genus-`3` curve with theta divisor `Θ`; in the model
`Θ = ThetaStd ℚ 3` (`Θ³/6 = [pt]`, `ThetaStd_pow`), for a complex structure `J` of `H¹(X, ℝ)` for
which `Θ` is ample.

* `WeilClasses.alphaJac d = 1 - (d/2) Θ²`, `WeilClasses.betaJac d = Θ - d [pt]` (§8.2), with
  `exp(√-d Θ) = α + √-d β`.
* `WeilClasses.chF1 d = 1 + Θ - (d/2) Θ² - d [pt]` (Lemma 8.2.1): the Chern character of
  `F₁ = I_{∪_{i=1}^{d+1} Cᵢ}(Θ)` (and of `F₂ = I_{∪ Σᵢ}(Θ)` of Theorem 1.4.1, the `Σᵢ` translates of
  `-AJ(C)`, which have the same class `Θ²/2`). The value of the Chern character is geometric
  (Poincaré's formula `[C_t] = Θ²/2`, `χ(𝒪_C) = -2`, Riemann–Roch); in the model `chF1 d` is the
  input class.
* `WeilClasses.chE d = τ(φ(w ⊗ w))`, `w = chF1 d`: the Chern character of the sheaf `E` of
  Theorem 1.4.1(2). There `Φ(F₂ ⊠ F₁)^∨ ≅ E[-2]` (equivalently `𝒢 = Φ(F₂ ⊠ F₁)[-3]`,
  `E = 𝒢^∨[-1]`, §9.2), so `ch(E) = ch(Φ(F₂ ⊠ F₁)^∨)` (an even shift does not change `ch`)
  `= τ(ch Φ(F₂ ⊠ F₁)) = τ(φ(ch F₂ ⊗ ch F₁))`. Since `τ` acts on `H^{2i}` by `(-1)^i` and is a ring
  automorphism of `H^{ev}`, `κ(τ x) = τ(κ x)`; so `κ₃(E) = -κ₃(Φ(F₂ ⊠ F₁))` and the rank of `E` is that
  of `Φ(F₂ ⊠ F₁)` (it is `8d`, `WeilClasses.Main.Intro`).
* `WeilClasses.kappa3E d = κ₃(E)`.
* `WeilClasses.PJac hΘ d hd`: the oriented `K`-secant `P_Θ` of §2.4 for `Θ = ThetaStd ℚ 3`
  (`P = span{α, β}`, §8.2–8.3), and `PJac_isCompl` (`V_K = W₁ ⊕ W₂`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## `κ` and the rank -/

section Kappa

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The class `φ(w₁ ⊗ τ(w₂))` (`φ = phiOrlov`, (6.1.3)): for objects `F₁, F₂` of `Dᵇ(X)` with
`ch(Fᵢ) = wᵢ` it is `ch(Φ(F₁ ⊠ F₂^∨))` (geometric: `ch(F₂^∨) = τ(ch F₂)` and GRR for Orlov's kernel;
not formalized). For `w₁, w₂` in a `K`-secant plane `P` this is the class of a
`P`-secant`^{⊠2}`-object (§1.3, Definition 6.2.2). -/
noncomputable def secantSqClass (w₁ w₂ : S F n) : ExtV F n :=
  phiOrlov F n (w₁ ⊗ₜ[F] tau F n w₂)

/-- `φ(w₁ ⊗ τ w₂) = φ'(w₁ ⊗ w₂)` with `φ' = φ ∘ (id ⊗ τ)` (`phiPrime`). -/
theorem secantSqClass_eq_phiPrime (w₁ w₂ : S F n) :
    secantSqClass F n w₁ w₂ = phiPrime F n (w₁ ⊗ₜ[F] w₂) := by
  simp [secantSqClass, phiPrime, tauTensor]

end Kappa

/-! ## The class of a bilinear form, `h = Ξ_P^♯`, and `H²(X × X̂, ℚ)_P` -/

section Sharp

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The vector `e_i = (0, e_i) ∈ V_F` (the summand `H¹(X, F)`). -/
noncomputable def vecE (i : Fin (2 * n)) : V F n := (0, e F n i)

/-- The vector `f_i = (f_i, 0) ∈ V_F` (the summand `H¹(X̂, F) = H¹(X, F)*`); `(f_i, e_j)_V = δ_{ij}`. -/
noncomputable def vecF (i : Fin (2 * n)) : V F n := (f F n i, 0)

/-- The class `B^♯ ∈ ⋀² V_F` of a bilinear form `B` on `V_F` under `V_F ≅ V_F*`, `x ↦ (x, ·)_V`:
`½ Σ B(f_i, f_j) e_i ∧ e_j + Σ B(f_i, e_j) e_i ∧ f_j + ½ Σ B(e_i, e_j) f_i ∧ f_j` (the dual basis of
`f_i, e_i` for `(·,·)_V` is `e_i, f_i`). For alternating `B`, `⟪B^♯, (x,·)_V ∧ (y,·)_V⟫ = B(x, y)`
(`formToExt2_spec`). -/
noncomputable def formToExt2 (B : LinearMap.BilinForm F (V F n)) : ExtV F n :=
  (∑ i, ∑ j, ((2 : F)⁻¹ * B (vecF F n i) (vecF F n j)) •
      (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecE F n j))) +
    (∑ i, ∑ j, B (vecF F n i) (vecE F n j) •
      (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecF F n j))) +
    ∑ i, ∑ j, ((2 : F)⁻¹ * B (vecE F n i) (vecE F n j)) •
      (ExteriorAlgebra.ι F (vecF F n i) * ExteriorAlgebra.ι F (vecF F n j))

/-- `B^♯` has degree `2`. -/
theorem formToExt2_mem (B : LinearMap.BilinForm F (V F n)) :
    formToExt2 F n B ∈ ⋀[F]^2 (V F n) := by
  sorry

/-- The characterization of `B^♯` for alternating `B`: `⟪B^♯, (x, ·)_V ∧ (y, ·)_V⟫ = B(x, y)`, where
`⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-`0` part), as in `WeilClasses.eval2`. Equivalently
`extPairing (x ∧ y) B^♯ = B(x, y)`. -/
theorem formToExt2_spec (B : LinearMap.BilinForm F (V F n)) (hB : B.IsAlt) (x y : V F n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing F n y) (contractLeft (Q := 0) (pairing F n x)
          (formToExt2 F n B))) = B x y := by
  sorry

end Sharp

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- **The class `h = Ξ_P^♯ ∈ H²(X × X̂, ℚ)`** of the `2`-form `Ξ_P(x, y) = (f x, y)_V` (2.4.2) under
`V_ℚ ≅ V_ℚ*` (§1.3, §6.2, §8.3). It spans `H²(X × X̂, ℚ)^{Spin(V)_P}` and is ample for `P = P_Θ`
(`WeilClasses.Main.Intro`). -/
noncomputable def hClass (hW : IsCompl P.W₁ P.W₂) : ExtV ℚ n := formToExt2 ℚ n (P.XiQ hW)

/-- `⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`: `h` is the class of `Ξ_P`. -/
theorem hClass_spec (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing ℚ n y) (contractLeft (Q := 0) (pairing ℚ n x)
          (P.hClass hW))) = P.XiQ hW x y := by
  sorry

/-- **`H²(X × X̂, ℚ)_P`** (§6.2): the sum of the non-trivial irreducible `Spin(V)_P`-subrepresentations
of `H²(X × X̂, ℚ) = ⋀² V_ℚ`, defined as the span of the vectors `ρ_g(x) - x`, `g ∈ Spin(V)_P` (the
integral group, `P.spinPZ`), `x ∈ ⋀² V_ℚ` (equivalent definition for the completely reducible
representation `⋀² V_ℚ`; see the module docstring). -/
noncomputable def H2P : Submodule ℚ (ExtV ℚ n) :=
  Submodule.span ℚ {y | ∃ g ∈ P.spinPZ, ∃ x ∈ ⋀[ℚ]^2 (V ℚ n), y = rhoExt ℚ n g x - x}

end KSecant

/-! ## The classes of §8.2 (`n = 3`) -/

section Jacobian

variable (d : ℚ)

/-- `α = 1 - (d/2) Θ² ∈ H^{ev}(X, ℚ)` (§8.2), `Θ = ThetaStd ℚ 3`: `exp(√-d Θ) = α + √-d β`. -/
noncomputable def alphaJac : S ℚ 3 := 1 - (d / 2) • ThetaStd ℚ 3 ^ 2

/-- `β = Θ - d [pt] ∈ H^{ev}(X, ℚ)` (§8.2), `Θ = ThetaStd ℚ 3`. -/
noncomputable def betaJac : S ℚ 3 := ThetaStd ℚ 3 - d • pt ℚ 3

/-- **`κ₃(E)`** (Theorem 1.4.1(4)): the summand in `H⁶(X × X̂, ℚ)` of `κ(E) = exp(-c₁(E)/r) ch(E)`. -/
noncomputable def kappa3E : ExtV ℚ 3 := kappaDeg ℚ 3 3 (chE d)

/-- The oriented `K`-secant `P_Θ` of §2.4 for `Θ = ThetaStd ℚ 3` ample for a complex structure `J`
of `H¹(X, ℝ)` (§8.2–8.3: `P = span{α, β}`, the secant through `exp(±√-d Θ)`). -/
noncomputable abbrev PJac {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    KSecant 3 d :=
  PTheta 3 d hd (ThetaStd ℚ 3) hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos (by norm_num))

/-- `V_K = W₁ ⊕ W₂` for `P_Θ` (§2.4: `θ` is an isomorphism). -/
theorem PJac_isCompl {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    IsCompl (PJac d hΘ hd).W₁ (PJac d hΘ hd).W₂ :=
  PTheta_isCompl 3 d hd _ _ _ hΘ.bijective_thetaMap

end Jacobian

end WeilClasses
