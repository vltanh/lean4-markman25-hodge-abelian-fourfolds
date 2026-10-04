module

public import WeilClasses.WeilType.Theta
public import WeilClasses.AbelianVariety.Defs
public import WeilClasses.Spinor.Integral

/-!
# §8.1: `K`-secants on a generic ppav

Statements of the paper's §8.1 (TeX lines 3634–3720). `(X, Θ)` is a principally polarized abelian
`n`-fold; `θ : H¹(X, ℚ)* → H¹(X, ℚ)` is the contraction with `Θ` ((2.4.3), `contractOne`), and the
paper's `f := (φ_Θ^*)⁻¹ : H¹(X) → H¹(X̂)` is `(-θ)⁻¹` (the footnote of §2.4 identifies `-θ` with
`φ_Θ^*`; `WeilClasses.fOfTheta`). All the identities below are insensitive to the sign of `f`.

## Definitions

* `WeilClasses.fOfTheta θ hθ = -θ⁻¹ : H¹(X, F) → H¹(X̂, F) = H¹(X, F)*` (for invertible `θ`).
* `WeilClasses.hdgMatrix θ hθ a`: the endomorphism of `V_F` with matrix
  `[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]` in the paper's order `(w, θ)` ((8.1.2)); in our order
  `(y, w)` it is `(y, w) ↦ (a₂₁ f(w) + a₂₂ y, a₁₁ w + a₁₂ f⁻¹(y))` (`a = !![a₁₁, a₁₂; a₂₁, a₂₂]`,
  `Fin 2` indices from `0`).
* `WeilClasses.SOplusHdg θ hθ`: the matrices with `a₁₁a₂₂ - a₂₁a₁₂ = 1` (the paper's
  `SO⁺_Hdg(V_F)`, *defined* in §8.1 as this group for `F = ℚ, K`).
* `WeilClasses.iotaTheta Θ c = Σ_j c_j Θ^{n-j}/(n-j)!`: the involution `ι` (interchanging the
  coefficients of `Θ^j/j!` and `Θ^{n-j}/(n-j)!`) applied to `Σ_j c_j Θ^j/j!`.
* `WeilClasses.alphaPP`, `WeilClasses.betaPP`: the classes `α`, `β` enumerating the non-rational pure
  spinors (closed forms of the paper).

## Statements

* (8.1.1) `equation8_1_1`; (8.1.2) `equation8_1_2` (corrected, see below); `SO⁺_Hdg`:
  `hdgMatrix_pairing`, `exists_rho_eq_hdgMatrix`.
* **Lemma 8.1.1** (`lemma8_1_1`), with the Möbius form of the action used in its proof
  (`m_exp_mem_span_hdgMatrix`).
* `ι`: `iotaTheta_exp` (`k^n exp(k⁻¹Θ) = ι(exp(kΘ))`) and the claim that the matrix
  `[[0, -f⁻¹], [f, 0]]` extends `ι`, corrected to `ι ∘ τ` (`iota_tau_extends`, see below).
* The enumeration `q^n exp(kΘ) = α + τ√-d β` (`enumeration8_1`), the displayed expansions
  (`alphaPP_expansion`, `betaPP_expansion` (misprint corrected)),
  `α, β ∈ H^{ev}(X, ℤ)` (`alphaPP_mem_SZ`, `betaPP_mem_SZ`), saturation for `q = 1`
  (`saturated_of_q_eq_one`), and the table of `∫_X (aα + bβ)^∨ (aα + bβ)` (`chi8_1_odd`, `chi8_1_two`,
  `chi8_1_four`, `chi8_1_even`), with `w^∨ = τ(w)` (Remark 5.2.3).

## Corrections of the paper (REPORT.md; checked numerically, exact arithmetic)

* (8.1.2) needs `End_ℚ(X) = ℚ`, which a cyclic Néron–Severi group does not imply (Jacobians of
  Picard curves): stated with that hypothesis, as agreed with the project owner (`equation8_1_2`).
* `[[0, -f⁻¹], [f, 0]]` acts on the pure spinors by `exp(kΘ) ↦ exp(-k⁻¹Θ)`, so it extends `ι ∘ τ`,
  not `ι` (`exp(kΘ) ↦ exp(k⁻¹Θ)` projectively): stated in that form, as agreed with the project
  owner (`iota_tau_extends`).
* The displayed expansion of `β`: the coefficient of `Θ⁴/4!` is `4 q^{n-4} ρ(ρ² - τ²d)`, not
  `q^{n-4} ρ(ρ² - τ²d)` (the closed form is right); an obvious misprint, corrected
  (`betaPP_expansion`).

## Left out (sheaf-theoretic)

The identification of `χ(F^∨ ⊗ F)` with `∫ ch(F^∨) ch(F)` (Hirzebruch–Riemann–Roch), the remark on the
minimum of `|χ(F^∨ ⊗ F)|` over Chern characters of objects and the lift of `ι` to `Aut(Dᵇ(X))`, and
the relation of `χ` to `Ext²(F, F)` and semiregularity for `n = 4`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## The matrices of (8.1.2) -/

section Matrices

variable {F : Type*} [Field F] {n : ℕ}

/-- `f = (φ_Θ^*)⁻¹ = (-θ)⁻¹ : H¹(X, F) → H¹(X̂, F) = H¹(X, F)*` (§8.1), for an invertible `θ`. -/
noncomputable def fOfTheta (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ) :
    H1 F n →ₗ[F] Module.Dual F (H1 F n) :=
  -((LinearEquiv.ofBijective θ hθ).symm : H1 F n →ₗ[F] Module.Dual F (H1 F n))

/-- The endomorphism of `V_F` with matrix `[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]` ((8.1.2), the
paper's order `(w, θ)`), `f⁻¹ = -θ`: in our order, `(y, w) ↦ (a₂₁ f(w) + a₂₂ y, a₁₁ w - a₁₂ θ(y))`,
with `a = !![a₁₁, a₁₂; a₂₁, a₂₂]`. -/
noncomputable def hdgMatrix (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ)
    (a : Matrix (Fin 2) (Fin 2) F) : V F n →ₗ[F] V F n :=
  LinearMap.prod
    (a 1 0 • (fOfTheta θ hθ ∘ₗ LinearMap.snd F _ _) + a 1 1 • LinearMap.fst F _ _)
    (a 0 0 • LinearMap.snd F _ _ + a 0 1 • ((-θ) ∘ₗ LinearMap.fst F _ _))

/-- **`SO⁺_Hdg(V_F)`** (§8.1): the matrices (8.1.2) with coefficients in `F` and
`a₁₁a₂₂ - a₂₁a₁₂ = 1` (the paper's definition for `F = ℚ` and, "allowing the coefficients to belong
to `K`", for `F = K`). -/
def SOplusHdg (θ : Module.Dual F (H1 F n) →ₗ[F] H1 F n) (hθ : Function.Bijective θ) :
    Set (V F n →ₗ[F] V F n) :=
  {A | ∃ a : Matrix (Fin 2) (Fin 2) F, a.det = 1 ∧ A = hdgMatrix θ hθ a}

end Matrices

section MatricesCharZero

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- **(8.1.1)** (`eq-identity-expressing-anti-symmetry-of-theta`): `f(w)(f⁻¹(θ')) = -θ'(w)` for
`w ∈ H¹(X)` and `θ' ∈ H¹(X̂) = H¹(X)*`, where `θ = contractOne Θ` for a class `Θ ∈ ⋀² H¹(X, F)`
with `θ` invertible, `f⁻¹ = -θ`. (Checked numerically for random non-degenerate `Θ`, `n ≤ 3`.) -/
theorem equation8_1_1 (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (w : H1 F n) (y : Module.Dual F (H1 F n)) :
    fOfTheta (contractOne F n Θ) hθ w ((-contractOne F n Θ) y) = -y w := by
  sorry

/-- (§8.1, TeX lines 3653–3655) "The identity (8.1.1) implies that the group `SO⁺_Hdg(V_ℚ)` is the
subgroup of invertible elements of `End_Hdg(V_ℚ)` with `a₁₁a₂₂ - a₂₁a₁₂ = 1`": the matrix (8.1.2)
multiplies the pairing (1.2.2) by its determinant, `(A x, A y)_V = (a₁₁a₂₂ - a₂₁a₁₂)(x, y)_V`. -/
theorem hdgMatrix_pairing (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (a : Matrix (Fin 2) (Fin 2) F) (x y : V F n) :
    pairing F n (hdgMatrix (contractOne F n Θ) hθ a x) (hdgMatrix (contractOne F n Θ) hθ a y) =
      a.det * pairing F n x y := by
  sorry

/-- (§8.1) The matrices (8.1.2) of determinant `1` lie in `SO⁺(V_F) = ρ(Spin(V_F))` (they form
`SL₂(F)`, which has trivial spinor norm). -/
theorem exists_rho_eq_hdgMatrix (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n))
    (hθ : Function.Bijective (contractOne F n Θ)) (a : Matrix (Fin 2) (Fin 2) F) (ha : a.det = 1) :
    ∃ g : Spin F n, (rho F n g : V F n →ₗ[F] V F n) = hdgMatrix (contractOne F n Θ) hθ a := by
  sorry

end MatricesCharZero

/-! ## (8.1.2) -/

section Equation812

variable {n : ℕ}

/-- **(8.1.2)** (`eq-two-by-two-matrix`), corrected: for a principally polarized abelian `n`-fold
`(X, Θ)` with `End_ℚ(X) = ℚ`, `End_ℚ(X × X̂) ≅ End_Hdg(V_ℚ)` is the algebra of the matrices
`[[a₁₁ I_X, a₁₂ f⁻¹], [a₂₁ f, a₂₂ I_X̂]]`, `a_{ij} ∈ ℚ`.

Model: `X` is `H¹(X, ℝ)` with the complex structure `J`, `Θ` ample; `End_ℚ(X) = ℚ`: every rational
Hodge endomorphism of `H¹(X, ℚ)` is a scalar (`IsHodgeMap`); `End_Hdg(V_ℚ)` is the set of rational
endomorphisms of `V_ℚ` commuting with the complex structure `I_{V_ℝ}` of `X × X̂`
(`productStructure`; `End_ℚ(X × X̂) ≅ End_Hdg(V_ℚ)` is the definition of endomorphisms in the
model).

**Correction of the paper** (agreed with the project owner; REPORT.md). The paper assumes only that
the Néron–Severi group is `ℤΘ`, which does not suffice: the Jacobian `X` of a very general Picard
curve `y³ = x⁴ + a x² + b x + c` (genus `3`, automorphism `y ↦ ζ₃ y`) has `NS(X) = ℤΘ` (the
Rosati-symmetric part of `End_ℚ(X) = ℚ(ζ₃)` is `ℚ`) but `End_ℚ(X × X̂) ≅ M₂(ℚ(ζ₃))` has dimension
`8`; for `n = 1` CM elliptic curves are counterexamples. The hypothesis `End_ℚ(X) = ℚ` (which implies
`NS(X)_ℚ = ℚΘ`) holds for a very general principally polarized abelian variety, the setting of the
section title. The rest of §8.1 does not use (8.1.2): `SO⁺_Hdg(V_K)` is defined as the matrix group
(`SOplusHdg`). -/
theorem equation8_1_2 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (Θ : S ℚ n) (hΘ : IsAmple n J Θ)
    (hEnd : ∀ B : H1 ℚ n →ₗ[ℚ] H1 ℚ n, IsHodgeMap J J B → ∃ c : ℚ, B = c • LinearMap.id) :
    {A : V ℚ n →ₗ[ℚ] V ℚ n |
        bcEndV ℝ n A * productStructure n J = productStructure n J * bcEndV ℝ n A} =
      Set.range (hdgMatrix (thetaMap n Θ) hΘ.bijective_thetaMap) := by
  sorry

end Equation812

/-! ## Lemma 8.1.1 -/

section Lemma811

variable {n : ℕ} (d : ℚ)

/-- **Lemma 8.1.1** (`lemma-orbit-of-pure-spinors`). The `SO⁺_Hdg(V_K)`-orbit of the pure spinor
`span_K{1} ∈ ℙ(S⁺_K)` is `{span_K{Θⁿ}} ∪ {span_K{exp(kΘ)} : k ∈ K}`.

Model: `SO⁺_Hdg(V_K)` is the group of matrices (8.1.2) with coefficients in `K` and determinant `1`
(`SOplusHdg`, for the `K`-linear `θ`), acting on `ℙ(S⁺_K)` through `Spin(V_K)` (`ρ` is onto
`SO⁺(V_K)` with kernel `±1`, which acts trivially on `ℙ(S_K)`): the orbit is the set of lines
`K m_g(1)`, `g ∈ Spin(V_K)` with `ρ(g) ∈ SO⁺_Hdg(V_K)`. Reading: the lemma uses only this definition
of `SO⁺_Hdg(V_K)`; it holds for every `Θ ∈ ⋀² H¹(X, ℚ)` with `θ` invertible (the section's hypotheses
on `(X, Θ)` are not needed). -/
theorem lemma8_1_1 (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) :
    {L : Submodule (Kd d) (S (Kd d) n) | ∃ g : Spin (Kd d) n,
        (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) ∈ SOplusHdg (thetaExt n (Kd d) Θ) hθ ∧
        L = Submodule.span (Kd d) {m (Kd d) n (g : C (Kd d) n) 1}} =
      {Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n}} ∪
        Set.range fun k : Kd d => Submodule.span (Kd d) {IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)} := by
  sorry

/-- (Proof of Lemma 8.1.1, reformulated) The matrix `A = [[a₁₁, a₁₂ f⁻¹], [a₂₁ f, a₂₂]]` maps the
maximal isotropic subspace `ker m_{exp(kΘ)} = {(y, -kθ(y))}` to `ker m_{exp(k'Θ)}` with
`k' = (a₁₁ k + a₁₂)/(a₂₁ k + a₂₂)` (a Möbius transformation; `a₂₂ = 0`, `k = 0` gives `H¹(X, K)`,
the line of `Θⁿ`): for `g ∈ Spin(V_K)` with `ρ(g) = A`, `m_g(exp(kΘ)) ∈ K exp(k'Θ)`. (Checked
numerically for `n ≤ 3`.) -/
theorem m_exp_mem_span_hdgMatrix (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) (a : Matrix (Fin 2) (Fin 2) (Kd d))
    (g : Spin (Kd d) n)
    (hg : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) = hdgMatrix (thetaExt n (Kd d) Θ) hθ a)
    (k : Kd d) (hk : a 1 0 * k + a 1 1 ≠ 0) :
    m (Kd d) n (g : C (Kd d) n) (IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)) ∈
      Submodule.span (Kd d)
        {IsNilpotent.exp (((a 0 0 * k + a 0 1) / (a 1 0 * k + a 1 1)) • bcS ℚ (Kd d) n Θ)} := by
  sorry

end Lemma811

/-! ## The involution `ι` -/

section Iota

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The involution `ι` of §8.1, interchanging the coefficients of `Θ^j/j!` and `Θ^{n-j}/(n-j)!`,
applied to `Σ_{j=0}^{n} c_j Θ^j/j!`: the class `Σ_j c_j Θ^{n-j}/(n-j)!`. -/
noncomputable def iotaTheta (Θ : S F n) (c : ℕ → F) : S F n :=
  ∑ j ∈ Finset.range (n + 1), (c j / ((n - j).factorial : F)) • Θ ^ (n - j)

/-- (§8.1, TeX lines 3679–3680) `ι` acts on the pure spinors `exp(kΘ) = Σ_j k^j Θ^j/j!` by
`ι(exp(kΘ)) = kⁿ exp(k⁻¹Θ)` (`k ≠ 0`). (Checked symbolically for `n ≤ 6`.) -/
theorem iotaTheta_exp (Θ : S F n) (hΘ : Θ ∈ ⋀[F]^2 (H1 F n)) (k : F) (hk : k ≠ 0) :
    iotaTheta Θ (fun j => k ^ j) = k ^ n • IsNilpotent.exp (k⁻¹ • Θ) := by
  sorry

variable (d : ℚ)

/-- (§8.1, TeX lines 3680–3681) "The action of the element `[[0, -f⁻¹], [f, 0]]` on `ℙ(S_K)` extends
the action of `ι`", corrected: a lift `g ∈ Spin(V_K)` of `[[0, -f⁻¹], [f, 0]]` maps the line of
`exp(kΘ)` to the line of `exp(-k⁻¹Θ) ∝ ι(τ(exp(kΘ)))` (`k ∈ K^×`), the line of `1` to that of `Θⁿ`
and the line of `Θⁿ` to that of `1`; i.e. it extends `ι ∘ τ` (`τ(exp(kΘ)) = exp(-kΘ)`).

**Correction of the paper** (agreed with the project owner; REPORT.md). As printed ("extends `ι`") the
claim is false: the matrix acts on the pure spinors by the Möbius map `k ↦ -1/k`
(`m_exp_mem_span_hdgMatrix`), so it maps the line of `exp(kΘ)` to that of `exp(-k⁻¹Θ)`, not of
`ι(exp(kΘ)) ∝ exp(k⁻¹Θ)` (checked numerically for `n = 1, 2, 3`, `k = 2`). (An element
`[[0, c f⁻¹], [c f, 0]]` of `SO⁺_Hdg(V_K)` inducing `k ↦ 1/k` needs `-c² = 1`, so it exists only for
`K = ℚ(√-1)`.) The paper uses the claim only to lift `ι` to `Aut(Dᵇ(X))` and obtain an object of
non-zero rank, which `ι ∘ τ` also gives. -/
theorem iota_tau_extends (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hθ : Function.Bijective (thetaExt n (Kd d) Θ)) (g : Spin (Kd d) n)
    (hg : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n) =
      hdgMatrix (thetaExt n (Kd d) Θ) hθ !![0, -1; 1, 0]) :
    (∀ k : Kd d, k ≠ 0 →
      m (Kd d) n (g : C (Kd d) n) (IsNilpotent.exp (k • bcS ℚ (Kd d) n Θ)) ∈
        Submodule.span (Kd d) {IsNilpotent.exp ((-k⁻¹) • bcS ℚ (Kd d) n Θ)}) ∧
      m (Kd d) n (g : C (Kd d) n) 1 ∈ Submodule.span (Kd d) {bcS ℚ (Kd d) n Θ ^ n} ∧
      m (Kd d) n (g : C (Kd d) n) (bcS ℚ (Kd d) n Θ ^ n) ∈ Submodule.span (Kd d) {1} := by
  sorry

end Iota

/-! ## The enumeration of the non-rational pure spinors -/

section Enumeration

variable {n : ℕ}

/-- **`α`** (§8.1): `α = exp(ρΘ/q) Σ_{j=0}^{⌊n/2⌋} (-1)^j q^{n-2j} (τ²d)^j Θ^{2j}/(2j)!`, for
`k = (ρ + τ√-d)/q`. -/
noncomputable def alphaPP (Θ : S ℚ n) (d : ℚ) (ρ τ q : ℤ) : S ℚ n :=
  IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
    ∑ j ∈ Finset.range (n / 2 + 1),
      ((-1 : ℚ) ^ j * (q : ℚ) ^ (n - 2 * j) * ((τ : ℚ) ^ 2 * d) ^ j / ((2 * j).factorial : ℚ)) •
        Θ ^ (2 * j)

/-- **`β`** (§8.1): `β = exp(ρΘ/q) Σ_{j=0}^{⌊(n-1)/2⌋} (-1)^j q^{n-1-2j} (τ²d)^j Θ^{2j+1}/(2j+1)!`. -/
noncomputable def betaPP (Θ : S ℚ n) (d : ℚ) (ρ τ q : ℤ) : S ℚ n :=
  IsNilpotent.exp (((ρ : ℚ) / q) • Θ) *
    ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
      ((-1 : ℚ) ^ j * (q : ℚ) ^ (n - 1 - 2 * j) * ((τ : ℚ) ^ 2 * d) ^ j /
          ((2 * j + 1).factorial : ℚ)) • Θ ^ (2 * j + 1)

/-- (§8.1, TeX lines 3683–3699) The non-rational pure spinors of Lemma 8.1.1: for
`k = (ρ + τ√-d)/q` (`ρ, τ, q ∈ ℤ`, `q > 0`), `qⁿ exp(kΘ) = α + τ√-d β`; so the line of `exp(kΘ)` is
that of `(α + τ√-d β)/qⁿ`. (Checked symbolically for `n ≤ 6`.) The conditions `gcd(ρ, τ, q) = 1`,
`τ ≠ 0` of the paper make the enumeration bijective onto the non-rational lines (`τ ≠ 0`) and are
not needed for the identity. -/
theorem enumeration8_1 (d : ℚ) (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ((q : Kd d) ^ n) • IsNilpotent.exp ((((ρ : Kd d) + (τ : Kd d) * Kd.sqrtNeg d) / (q : Kd d)) •
        bcS ℚ (Kd d) n Θ) =
      bcS ℚ (Kd d) n (alphaPP Θ d ρ τ q) +
        ((τ : Kd d) * Kd.sqrtNeg d) • bcS ℚ (Kd d) n (betaPP Θ d ρ τ q) := by
  sorry

/-- (§8.1, TeX lines 3686–3688) The displayed expansion of `α`:
`α = qⁿ + ρqⁿ⁻¹Θ + qⁿ⁻²(ρ² - τ²d)Θ²/2 + qⁿ⁻³ρ(ρ² - 3τ²d)Θ³/3! + qⁿ⁻⁴(ρ⁴ - 6ρ²τ²d + τ⁴d²)Θ⁴/4! + ⋯`,
the dots being a multiple of `Θ⁵`. (Natural subtraction in the exponents is harmless: `Θ^j = 0` for
`j > n`.) -/
theorem alphaPP_expansion (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ∃ r : S ℚ n, alphaPP Θ d ρ τ q =
      ((q : ℚ) ^ n) • (1 : S ℚ n) + ((ρ : ℚ) * (q : ℚ) ^ (n - 1)) • Θ +
        ((q : ℚ) ^ (n - 2) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 2) • Θ ^ 2 +
        ((q : ℚ) ^ (n - 3) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - 3 * (τ : ℚ) ^ 2 * d) / 6) • Θ ^ 3 +
        ((q : ℚ) ^ (n - 4) * ((ρ : ℚ) ^ 4 - 6 * (ρ : ℚ) ^ 2 * (τ : ℚ) ^ 2 * d +
          (τ : ℚ) ^ 4 * d ^ 2) / 24) • Θ ^ 4 + Θ ^ 5 * r := by
  sorry

/-- (§8.1, TeX lines 3692–3694) The displayed expansion of `β`:
`β = qⁿ⁻¹Θ + ρqⁿ⁻²Θ² + qⁿ⁻³(3ρ² - dτ²)Θ³/3! + 4qⁿ⁻⁴ρ(ρ² - τ²d)Θ⁴/4! + ⋯`, the dots being a multiple
of `Θ⁵`.

**Misprint corrected** (REPORT.md): the paper prints the coefficient of `Θ⁴/4!` as `qⁿ⁻⁴ρ(ρ² - τ²d)`,
without the factor `4`; its closed form for `β`, which is the definition (`betaPP`), gives
`4qⁿ⁻⁴ρ(ρ² - τ²d)` (the imaginary part of `(ρ + τ√-d)⁴` is `4ρτ(ρ² - τ²d)√d`). -/
theorem betaPP_expansion (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (ρ τ q : ℤ)
    (hq : 0 < q) :
    ∃ r : S ℚ n, betaPP Θ d ρ τ q =
      ((q : ℚ) ^ (n - 1)) • Θ + ((ρ : ℚ) * (q : ℚ) ^ (n - 2)) • Θ ^ 2 +
        ((q : ℚ) ^ (n - 3) * (3 * (ρ : ℚ) ^ 2 - d * (τ : ℚ) ^ 2) / 6) • Θ ^ 3 +
        (4 * (q : ℚ) ^ (n - 4) * (ρ : ℚ) * ((ρ : ℚ) ^ 2 - (τ : ℚ) ^ 2 * d) / 24) • Θ ^ 4 +
        Θ ^ 5 * r := by
  sorry

/-- (§8.1, TeX line 3700) "`α, β ∈ H^{ev}(X, ℤ)`": for `Θ ∈ H²(X, ℤ)` and `d ∈ ℤ`, `α` is integral
(`α = Σ_j qⁿ⁻ʲ Re((ρ + τ√-d)^j) Θ^j/j!` and `Θ^j/j!` is integral). -/
theorem alphaPP_mem_SZ (d : ℚ) (hdZ : ∃ z : ℤ, d = z) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hΘZ : Θ ∈ SZ n) (ρ τ q : ℤ) (hq : 0 < q) : alphaPP Θ d ρ τ q ∈ SZ n := by
  sorry

/-- (§8.1, TeX line 3700) "`α, β ∈ H^{ev}(X, ℤ)`": `β` is integral. -/
theorem betaPP_mem_SZ (d : ℚ) (hdZ : ∃ z : ℤ, d = z) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hΘZ : Θ ∈ SZ n) (ρ τ q : ℤ) (hq : 0 < q) : betaPP Θ d ρ τ q ∈ SZ n := by
  sorry

/-- (§8.1, TeX line 3700) "`span_ℤ{α, β}` is saturated in `H^{ev}(X, ℤ)` when `q = 1`": a rational
combination `aα + bβ` is integral only if `a, b ∈ ℤ`. Hypotheses: `Θ` integral and primitive in
`H²(X, ℤ)` (true for the generator `Θ` of `NS(X)`, which is saturated in `H²(X, ℤ)`), `d ∈ ℤ`,
`n ≥ 1`. -/
theorem saturated_of_q_eq_one (d : ℚ) (hdZ : ∃ z : ℤ, d = z) (hn : 1 ≤ n) (Θ : S ℚ n)
    (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘZ : Θ ∈ SZ n)
    (hprim : ∀ c : ℚ, c • Θ ∈ SZ n → ∃ z : ℤ, c = z) (ρ τ : ℤ) (a b : ℚ)
    (hab : a • alphaPP Θ d ρ τ 1 + b • betaPP Θ d ρ τ 1 ∈ SZ n) :
    (∃ z : ℤ, a = z) ∧ ∃ z : ℤ, b = z := by
  sorry

/-- (§8.1, TeX lines 3703–3711) The table of `χ(F^∨ ⊗ F) = ∫_X (aα + bβ)^∨ (aα + bβ)`, `n` odd: it is
`0`. Model: `w^∨ = τ(w)` (Remark 5.2.3), `Θ` principal (`Θⁿ = n! [pt]`), `a, b ∈ ℚ`. (Checked
symbolically for `n ≤ 6`.) -/
theorem chi8_1_odd (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (hn : Odd n) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) = 0 := by
  sorry

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n = 2`: `-2q²(a²τ²d + b²)`. -/
theorem chi8_1_two (d : ℚ) (Θ : S ℚ 2) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ 2))
    (hpp : Θ ^ 2 = (2 : ℚ) • pt ℚ 2) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ 2 (tau ℚ 2 (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      -2 * (q : ℚ) ^ 2 * (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  sorry

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n = 4`: `8dq⁴τ²(a²τ²d + b²)`. -/
theorem chi8_1_four (d : ℚ) (Θ : S ℚ 4) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ 4))
    (hpp : Θ ^ 4 = (24 : ℚ) • pt ℚ 4) (ρ τ q : ℤ) (hq : 0 < q) (a b : ℚ) :
    integral ℚ 4 (tau ℚ 4 (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      8 * d * (q : ℚ) ^ 4 * (τ : ℚ) ^ 2 * (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  sorry

/-- (§8.1) The table of `∫_X (aα + bβ)^∨ (aα + bβ)`, `n` even:
`(-1)^{n/2} 2^{n-1} d^{n/2-1} qⁿ τ^{n-2} (a²τ²d + b²)` (`n ≥ 2`). -/
theorem chi8_1_even (d : ℚ) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n))
    (hpp : Θ ^ n = (n.factorial : ℚ) • pt ℚ n) (hn : Even n) (hn2 : 2 ≤ n) (ρ τ q : ℤ)
    (hq : 0 < q) (a b : ℚ) :
    integral ℚ n (tau ℚ n (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q) *
      (a • alphaPP Θ d ρ τ q + b • betaPP Θ d ρ τ q)) =
      (-1 : ℚ) ^ (n / 2) * 2 ^ (n - 1) * d ^ (n / 2 - 1) * (q : ℚ) ^ n * (τ : ℚ) ^ (n - 2) *
        (a ^ 2 * (τ : ℚ) ^ 2 * d + b ^ 2) := by
  sorry

end Enumeration

end WeilClasses
