module

public import WeilClasses.PureSpinor.CM
public import WeilClasses.Hodge.Defs
public import Mathlib.Algebra.Algebra.Rat

/-!
# Polarized abelian varieties of Weil type from oriented `K`-secants: the setup (paper §2.4)

The first half of §2.4 of the paper (TeX lines 1223–1308):

* Assumption 2.4.1 (`WeilClasses.Assumption2_4_1`) and its consequence `V_K = W₁ ⊕ W₂`;
* the similarity `f = η_{√-d}` of (2.4.1) (`WeilClasses.KSecant.fη`, defined in
  `WeilClasses.PureSpinor.CM`): `f ∈ Õ(V_ℚ)`, `(f x, f y)_V = d (x, y)_V`, `f² = -d`, `f`
  anti-self-dual;
* the `2`-form `Ξ_P(x, y) = (f x, y)_V` of (2.4.2) (`KSecant.XiQ`; on `V_ℝ`, `KSecant.XiR`):
  nondegenerate, equal to `√-d ((x₁, y₂)_V - (x₂, y₁)_V)`;
* the subspaces `W_{i,ℂ} ⊆ V_ℂ` (`KSecant.W₁ℂ`, `KSecant.W₂ℂ`) and the decomposition
  `v = v₁^{1,0} + v₂^{1,0} + v₁^{0,1} + v₂^{0,1}` with its conjugation rules;
* the complex structure `I = I_{V_ℝ}` of `X × X̂` (`productStructure n J`): an isometry,
  anti-self-dual, with isotropic `V^{1,0}` and `V^{0,1}`, commuting with `f`; `Ξ_P` of type `(1,1)`;
  the symmetric form `g_P(x, y) = Ξ_P(I x, y)` (`KSecant.gP`) and Lemma 2.4.2;
* Remark 2.4.3: the lift `ϖ̃(λ) ∈ Spin(V_F)` of `ϖ(λ)` (`WeilClasses.varpiTilde`), and the lift of
  an orthogonal complex structure of `V_ℝ` to `Spin(V_ℝ)`.

The second half of §2.4 (the class `Θ`, `exp(√-d Θ)`, the plane `P_Θ` and Proposition 2.4.4) is in
`WeilClasses.WeilType.Theta`.

## Conventions

* `V_F = H¹(X, F)* × H¹(X, F)`, pairs `(y, w)` (Mathlib's order; the paper writes `(w, y)`); the
  pairing (1.2.2) is `pairing F n`.
* `K = Kd d ⊆ ℂ` with `√-d = i √d` (`Kd.sqrtNeg d`); `σ` is complex conjugation.
* `W₁, W₂ ⊆ V_K` are the maximal isotropic subspaces `ker m_{u₁}`, `ker m_{u₂}` of the `K`-secant
  `P`; `W_{i,ℂ}` is the `ℂ`-span of `Wᵢ` in `V_ℂ` (`bcV (Kd d) ℂ n`).
* The `F'`-linear extension of a rational endomorphism of `V_ℚ` (`F' = K, ℝ, ℂ`) is computed in the
  bases `basisV` (`WeilClasses.bcEndV`); `f` on `V_ℝ` is `KSecant.fR`.
* The complex structure of `V_ℝ = H¹(X × X̂, ℝ)` induced by the complex structure `J` of
  `H¹(X, ℝ)` (with `H^{1,0}(X)` its `i`-eigenspace) is, in the paper's convention (footnote in §2.4:
  the dual of the tangent complex structures, a dual composing with `-I`),
  `productStructure n J : (y, w) ↦ (y ∘ J, -J w)`, the negative of the standard Hodge structure;
  the paper's `V^{1,0} = V10 n I` is its `i`-eigenspace in `V_ℂ`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Extension of scalars of rational endomorphisms of `V` -/

section BcEnd

variable (F' : Type*) [Field F'] [CharZero F'] (n : ℕ)

/-- The `F'`-linear extension to `V_{F'}` of a rational endomorphism `A` of `V_ℚ` (for
`F' = K, ℝ, ℂ`): the endomorphism with the same matrix in the bases `basisV`. -/
noncomputable def bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) : V F' n →ₗ[F'] V F' n :=
  Matrix.toLin (basisV F' n) (basisV F' n)
    ((LinearMap.toMatrix (basisV ℚ n) (basisV ℚ n) A).map (algebraMap ℚ F'))

/-- `bcEndV F' n A` extends `A`. -/
theorem bcEndV_bcV (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V ℚ n) :
    bcEndV F' n A (bcV ℚ F' n v) = bcV ℚ F' n (A v) := by
  sorry

/-- The complexification of the real extension is the complex extension. -/
theorem complexifyV_bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) :
    complexifyV n (bcEndV ℝ n A) = bcEndV ℂ n A := by
  sorry

end BcEnd

/-! ## The field `K`: the coefficient of `√-d` -/

/-! ## Assumption 2.4.1 -/

variable {n : ℕ} {d : ℚ}

/-- **Assumption 2.4.1** (`assumption-on-rational-secant-plane-P`). The rational plane `P` is
non-isotropic with respect to the Mukai pairing (1.2.3) and is contained in the Hodge ring of `X`.
`ℙ(P)` intersects the spinor variety in two complex conjugate points defined over
`K := ℚ[√-d]`, where `d` is a positive rational number.

Representation: `X` is given by the complex structure `J` of `H¹(X, ℝ)` (with `H^{1,0}(X)` its
`i`-eigenspace), and `P` is the rational plane `P.Pℚ` of a rational `K`-secant `P : KSecant n d`,
which records the two conjugate even pure spinor lines `ℓ̃₁ = K u₁`, `ℓ̃₂ = K σ(u₁)` where `ℙ(P)`
meets the spinor variety (the choice of `u₁` is the orientation of `P`). -/
structure Assumption2_4_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) : Prop where
  /-- `J` is a complex structure of `H¹(X, ℝ)` (the complex structure of `X`). -/
  isComplex : IsComplexStructure J
  /-- `P` is non-isotropic for the Mukai pairing (1.2.3). -/
  nonIsotropic : ¬ P.IsIsotropic
  /-- `P` is contained in the Hodge ring `⊕_p H^{p,p}(X, ℚ)` of `X`. -/
  hodge : P.Pℚ ≤ hodgeRingX n J
  /-- `d` is a positive rational number. -/
  pos : 0 < d

/-- Under Assumption 2.4.1, `V_K = W₁ ⊕ W₂`: `W₁ ∩ W₂ = 0` by Lemma 2.2.1 (`P` is non-isotropic;
§2.2, line 846 of the TeX: "The vanishing `W₁ ∩ W₂ = (0)` holds, by Lemma 2.2.1"), and
`dim W₁ + dim W₂ = 4n = dim V_K`. This is what the definition (2.2.4) of `η`, hence of `f`, needs. -/
theorem Assumption2_4_1.isCompl {P : KSecant n d} {J : Module.End ℝ (H1 ℝ n)}
    (hP : Assumption2_4_1 P J) : IsCompl P.W₁ P.W₂ := by
  sorry

namespace KSecant

variable (P : KSecant n d)

/-- A rational `K`-secant exists only when `d > 0`: for `d ≤ 0` the chosen square root `√-d` is
`0`, `Kd d = ℚ`, `σ` is the identity and `u₂ = u₁`. -/
theorem d_pos : 0 < d := by
  sorry

/-! ## The similarity `f` (2.4.1) -/

/-- `f = η_{√-d}` (2.4.1) belongs to the similarity group `Õ(V_ℚ)` of (2.2.3) (§2.4, after
(2.4.1), "by Lemma 2.2.4"). -/
theorem fη_mem_Otilde (hW : IsCompl P.W₁ P.W₂) :
    ∃ g : V ℚ n ≃ₗ[ℚ] V ℚ n, g ∈ Otilde n d ∧ (g : V ℚ n →ₗ[ℚ] V ℚ n) = P.fη hW := by
  sorry

/-- `(f x, f y)_V = d (x, y)_V` (§2.4, after (2.4.1), "by Lemma 2.2.4"). -/
theorem pairing_fη_fη (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) (P.fη hW y) = d * pairing ℚ n x y := by
  sorry

/-- `f² = -d` (§2.4, after (2.4.1), "by Lemma 2.2.4"). -/
theorem fη_comp_fη (hW : IsCompl P.W₁ P.W₂) : P.fη hW ∘ₗ P.fη hW = -(d • LinearMap.id) := by
  sorry

/-- `f` is anti-self-dual: `(f x, y)_V = -(x, f y)_V` (§2.4, after (2.4.1)). -/
theorem pairing_fη_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) y = -pairing ℚ n x (P.fη hW y) := by
  sorry

/-- The real extension `f_ℝ` of `f` to `V_ℝ`. -/
noncomputable def fR (hW : IsCompl P.W₁ P.W₂) : Module.End ℝ (V ℝ n) := bcEndV ℝ n (P.fη hW)

/-! ## The `2`-form `Ξ_P` (2.4.2) -/

/-- **The `2`-form `Ξ_P`** (2.4.2): `Ξ_P(x, y) = (f x, y)_V` on `V_ℚ`. -/
noncomputable def XiQ (hW : IsCompl P.W₁ P.W₂) : LinearMap.BilinForm ℚ (V ℚ n) :=
  (pairing ℚ n).compLeft (P.fη hW)

/-- `Ξ_P` on `V_ℝ`: `Ξ_P(x, y) = (f x, y)_V` (§2.4 and §3.2). -/
noncomputable def XiR (hW : IsCompl P.W₁ P.W₂) : LinearMap.BilinForm ℝ (V ℝ n) :=
  (pairing ℝ n).compLeft (P.fR hW)

/-- `XiR` extends `XiQ`. -/
theorem XiR_bcV (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.XiR hW (bcV ℚ ℝ n x) (bcV ℚ ℝ n y) = (P.XiQ hW x y : ℝ) := by
  sorry

/-- `Ξ_P` is a `2`-form, `Ξ_P ∈ ⋀² V_ℚ*` (§2.4, (2.4.2)): it is alternating. -/
theorem XiQ_isAlt (hW : IsCompl P.W₁ P.W₂) : (P.XiQ hW).IsAlt := by
  sorry

/-- `Ξ_P` is non-degenerate, since `f` is invertible and the pairing on `V` is non-degenerate
(§2.4, after (2.4.2)). -/
theorem XiQ_nondegenerate (hW : IsCompl P.W₁ P.W₂) : (P.XiQ hW).Nondegenerate := by
  sorry

/-- `Ξ_P(x, y) = √-d ((x₁, y₂)_V - (x₂, y₁)_V)`, where `x = x₁ + x₂` and `y = y₁ + y₂` with
`xᵢ, yᵢ ∈ Wᵢ` (decompositions in `V_K`) (§2.4, after (2.4.2)). -/
theorem XiQ_eq (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) (x₁ x₂ y₁ y₂ : V (Kd d) n)
    (hx₁ : x₁ ∈ P.W₁) (hx₂ : x₂ ∈ P.W₂) (hy₁ : y₁ ∈ P.W₁) (hy₂ : y₂ ∈ P.W₂)
    (hx : bcV ℚ (Kd d) n x = x₁ + x₂) (hy : bcV ℚ (Kd d) n y = y₁ + y₂) :
    algebraMap ℚ (Kd d) (P.XiQ hW x y) =
      Kd.sqrtNeg d * (pairing (Kd d) n x₁ y₂ - pairing (Kd d) n x₂ y₁) := by
  sorry

/-! ## The subspaces `W_{i,ℂ}` and the decomposition into four summands -/

/-- The decomposition `v = v₁^{1,0} + v₂^{1,0} + v₁^{0,1} + v₂^{0,1}` (§2.4, after (2.4.2), "by
Lemma 2.2.6"): under Assumption 2.4.1, every `v ∈ V_ℚ` is, in a unique way, a sum of vectors
`vᵢ^{1,0} ∈ W_{i,ℂ} ∩ V^{1,0}` and `vᵢ^{0,1} ∈ W_{i,ℂ} ∩ V^{0,1}` of `V_ℂ` (`I = I_{V_ℝ}`). The
components are listed in the order `(v₁^{1,0}, v₂^{1,0}, v₁^{0,1}, v₂^{0,1})`. -/
theorem existsUnique_decomp (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℚ n) :
    ∃! p : V ℂ n × V ℂ n × V ℂ n × V ℂ n,
      p.1 ∈ P.W₁ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.1 ∈ P.W₂ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.2.1 ∈ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      p.2.2.2 ∈ P.W₂ℂ ⊓ V01 n (productStructure n J) ∧
      bcV ℚ ℂ n v = p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  sorry

/-- The summands of the decomposition of `v ∈ V_ℚ` satisfy `\overline{v₁^{1,0}} = v₂^{0,1}` and
`\overline{v₁^{0,1}} = v₂^{1,0}` (§2.4, after (2.4.2)); here `a = v₁^{1,0}`, `b = v₂^{1,0}`,
`c = v₁^{0,1}`, `e = v₂^{0,1}` and the bar is complex conjugation of `V_ℂ`. -/
theorem conj_decomp (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℚ n)
    (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℚ ℂ n v = a + b + c + e) :
    conjV (starRingAut : ℂ ≃+* ℂ) n a = e ∧ conjV (starRingAut : ℂ ≃+* ℂ) n c = b := by
  sorry

/-- The decomposition into four summands also holds for `v ∈ V_ℝ` (used in Lemma 2.4.2 and
Proposition 2.4.4, where `g_P` is a form on `V_ℝ`). -/
theorem existsUnique_decomp_real (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (v : V ℝ n) :
    ∃! p : V ℂ n × V ℂ n × V ℂ n × V ℂ n,
      p.1 ∈ P.W₁ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.1 ∈ P.W₂ℂ ⊓ V10 n (productStructure n J) ∧
      p.2.2.1 ∈ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      p.2.2.2 ∈ P.W₂ℂ ⊓ V01 n (productStructure n J) ∧
      bcV ℝ ℂ n v = p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  sorry

/-- The conjugation rules `\overline{v₁^{1,0}} = v₂^{0,1}`, `\overline{v₁^{0,1}} = v₂^{1,0}` for
`v ∈ V_ℝ`. -/
theorem conj_decomp_real (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (v : V ℝ n)
    (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℝ ℂ n v = a + b + c + e) :
    conjV (starRingAut : ℂ ≃+* ℂ) n a = e ∧ conjV (starRingAut : ℂ ≃+* ℂ) n c = b := by
  sorry

end KSecant

/-! ## The complex structure `I = I_{V_ℝ}` of `X × X̂` -/

section ProductStructure

variable (J : Module.End ℝ (H1 ℝ n))

/-- `I = I_{V_ℝ}` is a complex structure: `I² = -1`. -/
theorem isComplexStructure_productStructure (hJ : IsComplexStructure J) :
    IsComplexStructure (productStructure n J) := by
  sorry

/-- The complex structure `I = I_{V_ℝ}` of `X × X̂` is an isometry of `(·,·)_V` (§2.4 and its
footnote). -/
theorem pairing_productStructure (hJ : IsComplexStructure J) (x y : V ℝ n) :
    pairing ℝ n (productStructure n J x) (productStructure n J y) = pairing ℝ n x y := by
  sorry

/-- `I^{-1} = -I`, hence `I` is anti-self-dual: `(I x, y)_V = -(x, I y)_V` (§2.4). -/
theorem pairing_productStructure_left (hJ : IsComplexStructure J) (x y : V ℝ n) :
    pairing ℝ n (productStructure n J x) y = -pairing ℝ n x (productStructure n J y) := by
  sorry

/-- The eigenspace `V^{1,0}` of `I` in `V_ℂ` is isotropic (§2.4). -/
theorem V10_isotropic (hJ : IsComplexStructure J) :
    ∀ a ∈ V10 n (productStructure n J), ∀ b ∈ V10 n (productStructure n J), pairing ℂ n a b = 0 := by
  sorry

/-- The eigenspace `V^{0,1}` of `I` in `V_ℂ` is isotropic (§2.4). -/
theorem V01_isotropic (hJ : IsComplexStructure J) :
    ∀ a ∈ V01 n (productStructure n J), ∀ b ∈ V01 n (productStructure n J), pairing ℂ n a b = 0 := by
  sorry

end ProductStructure

namespace KSecant

variable (P : KSecant n d)

/-- `I = I_{V_ℝ}` commutes with `f` (§2.4, "by Lemma 2.2.6"). -/
theorem fR_comm_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.fR hP.isCompl * productStructure n J = productStructure n J * P.fR hP.isCompl := by
  sorry

/-- `Ξ_P` is of Hodge type `(1,1)` for `I = I_{V_ℝ}`: `Ξ_P(I x, I y) = Ξ_P(x, y)` (§2.4). -/
theorem XiR_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (x y : V ℝ n) :
    P.XiR hP.isCompl (productStructure n J x) (productStructure n J y) = P.XiR hP.isCompl x y := by
  sorry

/-- `f ∘ I` is self-dual: `(f(I x), y)_V = (x, f(I y))_V` (§2.4). -/
theorem pairing_fR_productStructure (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (x y : V ℝ n) :
    pairing ℝ n (P.fR hP.isCompl (productStructure n J x)) y =
      pairing ℝ n x (P.fR hP.isCompl (productStructure n J y)) := by
  sorry

/-- **The form `g_P`** (§2.4, before Lemma 2.4.2): `g_P(x, y) = Ξ_P(I x, y) = (f(I x), y)_V` on
`V_ℝ`, for the complex structure `I = I_{V_ℝ} = productStructure n J` of `X × X̂`. -/
noncomputable def gP (hW : IsCompl P.W₁ P.W₂) (J : Module.End ℝ (H1 ℝ n)) :
    LinearMap.BilinForm ℝ (V ℝ n) :=
  (P.XiR hW).compLeft (productStructure n J)

/-- `g_P` is symmetric (§2.4: "We get the symmetric bilinear form on `V_ℝ` …"). -/
theorem gP_isSymm (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    (P.gP hP.isCompl J).IsSymm := by
  sorry

end KSecant

/-- **Lemma 2.4.2** (`lemma-g-P-in-terms-of-4-summands`).
`g_P(v, v) = 2√d (-(v₁^{1,0}, v₂^{0,1})_V + (v₁^{0,1}, v₂^{1,0})_V)`.

Here `v ∈ V_ℝ` and `a = v₁^{1,0}`, `b = v₂^{1,0}`, `c = v₁^{0,1}`, `e = v₂^{0,1}` are the components
of `v` in `V_ℂ = W₁^{1,0} ⊕ W₂^{1,0} ⊕ W₁^{0,1} ⊕ W₂^{0,1}` (`KSecant.existsUnique_decomp_real`),
for the complex structure `I = I_{V_ℝ}` of `X × X̂`; the right-hand side is computed with the
`ℂ`-bilinear extension of the pairing. Standing assumption: Assumption 2.4.1. -/
theorem lemma2_4_2 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (v : V ℝ n) (a b c e : V ℂ n) (ha : a ∈ P.W₁ℂ ⊓ V10 n (productStructure n J))
    (hb : b ∈ P.W₂ℂ ⊓ V10 n (productStructure n J)) (hc : c ∈ P.W₁ℂ ⊓ V01 n (productStructure n J))
    (he : e ∈ P.W₂ℂ ⊓ V01 n (productStructure n J)) (hv : bcV ℝ ℂ n v = a + b + c + e) :
    ((P.gP hP.isCompl J v v : ℝ) : ℂ) =
      2 * (Real.sqrt d : ℂ) * (-pairing ℂ n a e + pairing ℂ n c b) := by
  sorry

/-! ## Remark 2.4.3 -/

section Remark243

variable {F : Type*} [Field F] [CharZero F]

/-- The element `ϖ̃(λ) = ∏_{k=1}^{2n} (λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n})` of `C(V_F)` (Remark 2.4.3), for
a basis `e_1, …, e_{4n}` of `V_F` with `e_k = e k` in a maximal isotropic subspace `L`,
`e_{k+2n} = e' k` in a complementary maximal isotropic subspace `M`, and `(e_i, e_j)_V = 1` if
`|i - j| = 2n`, `0` otherwise. The factors commute; they are multiplied in the order
`k = 1, …, 2n`. -/
noncomputable def varpiTilde (e e' : Fin (2 * n) → V F n) (l : Fˣ) : C F n :=
  (List.ofFn fun k : Fin (2 * n) =>
    algebraMap F (C F n) ((l⁻¹ : Fˣ) : F) +
      ((l : F) - ((l⁻¹ : Fˣ) : F)) •
        (CliffordAlgebra.ι (Q F n) (e k) * CliffordAlgebra.ι (Q F n) (e' k))).prod

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), general part: for a basis
`e₁, …, e_{4n}` of `V_F` as in `varpiTilde` (`L = span(e)`, `M = span(e')` complementary maximal
isotropic subspaces in duality) and `λ ∈ F^×`, `ϖ̃(λ)` is an element of `Spin(V_F)` (by the second
displayed formula in [Igusa, Sec. 2], `WeilClasses.igusa_sec2_mem`). -/
theorem remark2_4_3_mem (e e' : Fin (2 * n) → V F n) (he : ∀ i j, pairing F n (e i) (e j) = 0)
    (he' : ∀ i j, pairing F n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing F n (e i) (e' j) = if i = j then 1 else 0) (l : Fˣ) :
    varpiTilde e e' l ∈ spinGroup (Q F n) := by
  sorry

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), general part, continued: `ϖ̃(λ)` maps to `ϖ(λ) ∈ SO(V_F)`, which acts on `L`
by multiplication by `λ²` and on `M` by multiplication by `λ⁻²`. -/
theorem remark2_4_3_rho (e e' : Fin (2 * n) → V F n) (he : ∀ i j, pairing F n (e i) (e j) = 0)
    (he' : ∀ i j, pairing F n (e' i) (e' j) = 0)
    (hee' : ∀ i j, pairing F n (e i) (e' j) = if i = j then 1 else 0) (l : Fˣ) (i : Fin (2 * n)) :
    rho F n ⟨varpiTilde e e' l, remark2_4_3_mem e e' he he' hee' l⟩ (e i) = ((l : F) ^ 2) • e i ∧
      rho F n ⟨varpiTilde e e' l, remark2_4_3_mem e e' he he' hee' l⟩ (e' i) =
        (((l⁻¹ : Fˣ) : F) ^ 2) • e' i := by
  sorry

end Remark243

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), the special case: if `I` is an (orthogonal) complex structure of `V_ℝ`, take
`L = V^{1,0}`, `M = V^{0,1}` (dual bases `e`, `e'`) and `λ = e^{iπ/4}`: the element `ϖ̃(e^{iπ/4})` of
`Spin(V_ℂ)` is already in `Spin(V_ℝ)` and maps to `I = ϖ(e^{iπ/4})`.

Reading: "complex structure" means a complex structure which is an isometry of `(·,·)_V` (as
`I_{V_ℝ}` is), so that `V^{1,0}` and `V^{0,1}` are complementary maximal isotropic subspaces. -/
theorem remark2_4_3_complexStructure (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (e e' : Fin (2 * n) → V ℂ n)
    (he : ∀ i, e i ∈ V10 n I) (he' : ∀ i, e' i ∈ V01 n I)
    (hee' : ∀ i j, pairing ℂ n (e i) (e' j) = if i = j then 1 else 0) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I ∧
      bcC ℝ ℂ n (g : C ℝ n) =
        varpiTilde e e' (Units.mk0 (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I))
          (Complex.exp_ne_zero _)) := by
  sorry

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`): every complex structure `I` of `V_ℝ` which is an isometry of `(·,·)_V` lifts to
an element of `Spin(V_ℝ)`, i.e. lies in `ρ(Spin(V_ℝ)) = SO_+(V_ℝ)`. -/
theorem remark2_4_3_exists_lift (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I := by
  sorry

/-- **Remark 2.4.3** (`rem-complex-structure-lifts-to-Spin-V-RR`), first sentence: the complex structure `I = I_{V_ℝ}` of `X × X̂` lifts to an
element of `Spin(V_ℝ)`. -/
theorem remark2_4_3 (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) :
    ∃ g : Spin ℝ n, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = productStructure n J := by
  sorry

end WeilClasses
