module

public import WeilClasses.WeilType.Theta
public import WeilClasses.External.Chevalley.Sec3

/-!
# A `Spin(V)_P`-invariant Hermitian form (paper §3.1)

§3.1 of the paper (TeX lines 1440–1568), under Assumption 2.4.1:

* `SO_+(V_F) = ρ(Spin(V_F))` (`WeilClasses.SOplus`; the kernel of the spinor norm on `SO(V_F)`,
  Tau Ceti's `range_spinToSpecialOrthogonal_eq_ker_spinorNorm`), and the group `SO_+(V_ℚ)_f` of
  (3.1.1) (`KSecant.SOplusf`), with its real analogue `SO_+(V_ℝ)_f` (`KSecant.SOplusfR`) used in §4;
* Lemma 3.1.1: `ρ : Spin(V_ℚ)_P ≅ SO_+(V_ℚ)_f` (and the real version used in §4);
* the `K`-valued form `H(x, y) = d (x, y)_V + √-d (f x, y)_V` of (3.1.2) (`KSecant.hermH`);
* Lemma 3.1.2: `H` is Hermitian, `SO_+(V_ℚ)_f`-invariant, of signature `(n, n)`;
  `SO_+(V_ℚ)_f` has finite index in `SU(V_ℚ, H)`, read with `SU(V_ℚ, H)` the special unitary group
  of `H` (`V_ℚ` as a `K`-vector space, as the lemma says; `lemma3_1_2_finiteIndex`); with this
  reading the index is in fact `1` (`lemma3_1_2_eq_SUH`). The literal reading (`ℚ`-determinant `1`)
  gives `U(V_ℚ, H)`, of infinite index. The paper's proof of the finite index needs integrality at
  its last step (a gap; REPORT.md);
* the discriminant `det H ∈ ℚ^×/Nm(K^×)` (`KSecant.DiscIs`) and Lemma 3.1.3 (`det H = (-1)^n` for
  `P = P_Θ`).

## Representation of `V_ℚ` as a `K`-vector space

`K` acts on `V_ℚ` through `η` (2.2.4): `η(a + b√-d) = a + b f`. We do not put a `K`-module
structure on `V_ℚ`. A `K`-linear endomorphism is one commuting with `f`; its `K`-determinant is the
determinant of its `K`-extension restricted to `W₁` (`V_ℚ → W₁`, `v ↦ v₁` is a `K`-isomorphism, the
proof of Lemma 3.1.2). A `K`-basis of `V_ℚ` is a family `b₁, …, b_{2n}` such that `bᵢ, f(bᵢ)` are
`ℚ`-linearly independent (`KSecant.IsKBasis`). `H` is a function `V_ℚ × V_ℚ → K`, `σ`-semilinear in
the first and `K`-linear in the second variable (Lemma 3.1.2).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## `SO_+(V_F) = ρ(Spin(V_F))` -/

section SOplus

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `ρ : Spin(V_F) → GL(V_F)` as a group homomorphism (Tau Ceti's `spinToOrthogonal`). -/
noncomputable def rhoHom : Spin F n →* (V F n ≃ₗ[F] V F n) :=
  (TauCeti.QuadraticMap.orthogonalGroup (Q F n)).subtype.comp (spinToOrthogonal (Q F n))

theorem rhoHom_apply (g : Spin F n) : rhoHom F n g = rho F n g := by
  sorry

/-- **`SO_+(V_F)`**: the image `ρ(Spin(V_F))` of the spin group, equal to the kernel of the spinor
norm `SO(V_F) → F^×/(F^×)²` (notation table of the paper; Tau Ceti
`range_spinToSpecialOrthogonal_eq_ker_spinorNorm`). -/
noncomputable def SOplus : Subgroup (V F n ≃ₗ[F] V F n) := (rhoHom F n).range

theorem mem_SOplus_iff (g : V F n ≃ₗ[F] V F n) : g ∈ SOplus F n ↔ ∃ x : Spin F n, rho F n x = g := by
  sorry

end SOplus

variable {n : ℕ} {d : ℚ}

namespace KSecant

variable (P : KSecant n d)

/-! ## The group `SO_+(V)_f` (3.1.1) -/

/-- **`SO_+(V_ℚ)_f`** (3.1.1) (`eq-so-f`): the subgroup of `SO_+(V_ℚ)` of elements `g` which commute
with `f` and whose restrictions `g|_{Wᵢ}` to the eigenspaces `Wᵢ` of `f` (over `K`) satisfy
`det(g|_{Wᵢ}) = 1`, `i = 1, 2`. -/
noncomputable def SOplusf (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | g ∈ SOplus ℚ n ∧ (∀ x, g (P.fη hW x) = P.fη hW (g x)) ∧
    (∃ h : ∀ x ∈ P.W₁, bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n) x ∈ P.W₁,
      LinearMap.det ((bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict h) = 1) ∧
    (∃ h : ∀ x ∈ P.W₂, bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n) x ∈ P.W₂,
      LinearMap.det ((bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict h) = 1)}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- **`SO_+(V_ℝ)_f`** (§4): the elements of `SO_+(V_ℝ)` commuting with `f` whose complexifications
restrict to `W_{i,ℂ}` with determinant `1`, `i = 1, 2`. -/
noncomputable def SOplusfR (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℝ n ≃ₗ[ℝ] V ℝ n) where
  carrier := {g | g ∈ SOplus ℝ n ∧ (∀ x, g (P.fR hW x) = P.fR hW (g x)) ∧
    (∃ h : ∀ x ∈ P.W₁ℂ, complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n) x ∈ P.W₁ℂ,
      LinearMap.det ((complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n)).restrict h) = 1) ∧
    (∃ h : ∀ x ∈ P.W₂ℂ, complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n) x ∈ P.W₂ℂ,
      LinearMap.det ((complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n)).restrict h) = 1)}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

end KSecant

/-- **Lemma 3.1.1** (`lemma-stabilizer-is-isomorphic-to-so-f`). The stabilizer `Spin(V_ℚ)_P` is
mapped by `ρ` isomorphically onto `SO_+(V_ℚ)_f`: `ρ` is injective on `Spin(V_ℚ)_P` and its image
is `SO_+(V_ℚ)_f`. Standing assumption: Assumption 2.4.1. -/
theorem lemma3_1_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    Set.InjOn (rho ℚ n) (P.spinPℚ : Set (Spin ℚ n)) ∧
      rho ℚ n '' (P.spinPℚ : Set (Spin ℚ n)) = (P.SOplusf hP.isCompl : Set (V ℚ n ≃ₗ[ℚ] V ℚ n)) := by
  sorry

/-- Lemma 3.1.1 over `ℝ`, as cited at the beginning of §4 (TeX line 1713): `ρ` maps `Spin(V_ℝ)_P`
isomorphically onto `SO_+(V_ℝ)_f`. -/
theorem lemma3_1_1_real (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    Set.InjOn (rho ℝ n) (P.spinPR : Set (Spin ℝ n)) ∧
      rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) = (P.SOplusfR hP.isCompl : Set (V ℝ n ≃ₗ[ℝ] V ℝ n)) := by
  sorry

namespace KSecant

variable (P : KSecant n d)

/-! ## The Hermitian form `H` (3.1.2) -/

/-- **The form `H`** (3.1.2) (`eq-H`): the `K`-valued form `H(x, y) = d (x, y)_V + √-d (f(x), y)_V`
on `V_ℚ`. -/
noncomputable def hermH (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) : Kd d :=
  algebraMap ℚ (Kd d) (d * pairing ℚ n x y) +
    Kd.sqrtNeg d * algebraMap ℚ (Kd d) (pairing ℚ n (P.fη hW x) y)

/-- `U(V_ℚ, H)`: the `K`-linear automorphisms of `V_ℚ` (those commuting with `f = η_{√-d}`) leaving
`H` invariant. -/
noncomputable def UH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | (∀ x, g (P.fη hW x) = P.fη hW (g x)) ∧
    ∀ x y, P.hermH hW (g x) (g y) = P.hermH hW x y}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- `SU(V_ℚ, H)`: the elements of `U(V_ℚ, H)` of `K`-determinant `1`; the `K`-determinant of a
`K`-linear `g` is `det(g|_{W₁})` (`g` extended to `V_K`), as in the proof of Lemma 3.1.2. -/
noncomputable def SUH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | g ∈ P.UH hW ∧ ∃ h : ∀ x ∈ P.W₁, bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n) x ∈ P.W₁,
      LinearMap.det ((bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict h) = 1}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- The group of Lemma 3.1.2 read literally, "the subgroup `SU(V_ℚ, H)` of `SL(V_ℚ)` leaving `H`
invariant": the `ℚ`-linear automorphisms of determinant `1` leaving `H` invariant. (It equals
`U(V_ℚ, H)`; see `lemma3_1_2_finiteIndex`.) -/
noncomputable def SLH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | LinearMap.det (g : V ℚ n →ₗ[ℚ] V ℚ n) = 1 ∧
    ∀ x y, P.hermH hW (g x) (g y) = P.hermH hW x y}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- A `K`-basis `b₁, …, b_{2n}` of `V_ℚ` (`K` acting through `η`): the vectors `bᵢ` and `f(bᵢ)` are
`ℚ`-linearly independent (hence a `ℚ`-basis of the `4n`-dimensional `V_ℚ`). -/
def IsKBasis (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n) : Prop :=
  LinearIndependent ℚ (Sum.elim b (fun i => P.fη hW (b i)))

/-- An `H`-orthogonal `K`-basis of `V_ℚ`. -/
def IsOrthKBasis (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n) : Prop :=
  P.IsKBasis hW b ∧ ∀ i j, i ≠ j → P.hermH hW (b i) (b j) = 0

/-- **The signature of `H`** (proof of Lemma 3.1.2): `H` has signature `(a, b)` if the diagonal Gram
matrix of the quadratic form `H(x, x)` (with rational entries) with respect to an orthogonal
`K`-basis has `a` positive and `b` negative diagonal entries. We require that an orthogonal
`K`-basis exists and that every orthogonal `K`-basis gives `(a, b)` (well-definedness, Sylvester). -/
def HasSignature (hW : IsCompl P.W₁ P.W₂) (a b : ℕ) : Prop :=
  (∃ v, P.IsOrthKBasis hW v) ∧ ∀ v, P.IsOrthKBasis hW v →
    (Finset.univ.filter fun i => 0 < Kd.ratPart d (P.hermH hW (v i) (v i))).card = a ∧
      (Finset.univ.filter fun i => Kd.ratPart d (P.hermH hW (v i) (v i)) < 0).card = b

/-- The Gram matrix `(H(bᵢ, bⱼ))ᵢⱼ` of `H` in a family `b`. -/
noncomputable def gramH (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d) :=
  Matrix.of fun i j => P.hermH hW (b i) (b j)

/-- **The discriminant** of `H` (§1.1, §3.1) is the class of `c ∈ ℚ^×` in `ℚ^×/Nm(K^×)`: the
determinant of the matrix of `H` with respect to some `K`-basis of `V_ℚ` (an element of `ℚ^×`) lies
in `c · Nm(K^×)`. (It does not depend on the basis: `KSecant.discIs_iff_forall`.) -/
def DiscIs (hW : IsCompl P.W₁ P.W₂) (c : ℚ) : Prop :=
  ∃ b, P.IsKBasis hW b ∧ ∃ q ∈ Kd.normGroup d, (P.gramH hW b).det = algebraMap ℚ (Kd d) (c * q)

/-- The discriminant does not depend on the `K`-basis: if `DiscIs c`, then for every `K`-basis the
determinant of the Gram matrix lies in `c · Nm(K^×)` (Assumption 2.4.1 in force). -/
theorem discIs_iff_forall (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (c : ℚ) :
    P.DiscIs hP.isCompl c ↔ ∀ b, P.IsKBasis hP.isCompl b →
      ∃ q ∈ Kd.normGroup d, (P.gramH hP.isCompl b).det = algebraMap ℚ (Kd d) (c * q) := by
  sorry

end KSecant

/-! ## Lemma 3.1.2 -/

/-- **Lemma 3.1.2** (`lemma-su-3-3`), Hermitian symmetry: `H(x, y) = σ(H(y, x))`. Standing
assumption: Assumption 2.4.1. -/
theorem lemma3_1_2_hermitian (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (x y : V ℚ n) :
    P.hermH hP.isCompl x y = Kd.σ d (P.hermH hP.isCompl y x) := by
  sorry

/-- **Lemma 3.1.2** (`lemma-su-3-3`), `K`-linearity in the second variable:
`H(x, η_λ(y)) = λ H(x, y)` for `λ ∈ K`. -/
theorem lemma3_1_2_linear (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (l : Kd d) (x y : V ℚ n) :
    P.hermH hP.isCompl x (P.η hP.isCompl l y) = l * P.hermH hP.isCompl x y := by
  sorry

/-- **Lemma 3.1.2** (`lemma-su-3-3`): `H` is `SO_+(V_ℚ)_f`-invariant. -/
theorem lemma3_1_2_invariant (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (g : V ℚ n ≃ₗ[ℚ] V ℚ n) (hg : g ∈ P.SOplusf hP.isCompl)
    (x y : V ℚ n) : P.hermH hP.isCompl (g x) (g y) = P.hermH hP.isCompl x y := by
  sorry

/-- **Lemma 3.1.2** (`lemma-su-3-3`): the signature of `H` is `(n, n)`. -/
theorem lemma3_1_2_signature (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : P.HasSignature hP.isCompl n n := by
  sorry

/-- **Lemma 3.1.2** (`lemma-su-3-3`), last sentence: the group `SO_+(V_ℚ)_f` is a finite index
subgroup of `SU(V_ℚ, H)`.

Reading: `SU(V_ℚ, H)` is the special unitary group of `H` (`KSecant.SUH`: `K`-linear `H`-isometries
of `K`-determinant `1`), as its name and the dimension `(2n)² - 1` used in the proof of Lemma 4.0.2
say. The paper describes it as "the subgroup of `SL(V_ℚ)` leaving `H` invariant"; that subgroup is
all of `U(V_ℚ, H)` (every `H`-isometry has `ℚ`-determinant `Nm(det_K g) = 1`), in which `SO_+(V_ℚ)_f`
has infinite index (`det_K` maps `U(H)` onto the infinite group `K¹` of norm-one elements). The
proof's final step ("`det M` is a unit, and units are finite") needs `g` integral. See REPORT.md.
In fact the index is `1` (`lemma3_1_2_eq_SUH`). -/
theorem lemma3_1_2_finiteIndex (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    P.SOplusf hP.isCompl ≤ P.SUH hP.isCompl ∧
      ((P.SOplusf hP.isCompl).subgroupOf (P.SUH hP.isCompl)).index ≠ 0 := by
  sorry

/-- In the proof of Lemma 3.1.2: `SO_+(V_ℚ)_f` *equals* the special unitary group `SU(V_ℚ, H)`
(`K`-linear `H`-isometries of `K`-determinant `1`). -/
theorem lemma3_1_2_eq_SUH (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.SOplusf hP.isCompl = P.SUH hP.isCompl := by
  sorry

/-! ## Lemma 3.1.3 -/

/-- In the proof of Lemma 3.1.3: for `P = P_Θ` and `y, y' ∈ H¹(X̂, ℚ) = H¹(X, ℚ)*`,
`H((0, y), (0, y')) = d √-d Θ(y, y')` (paper's order; ours: `((y, 0), (y', 0))`), with
`Θ(y, y') = ⟪Θ, y ∧ y'⟫`. -/
theorem PTheta_hermH_inl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y y' : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).hermH (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (y, 0) (y', 0) =
      algebraMap ℚ (Kd d) d * Kd.sqrtNeg d * algebraMap ℚ (Kd d) (eval2 ℚ n Θ y y') := by
  sorry

/-- **Lemma 3.1.3** (`lemma-the-discriminant-is-minus-1-to-the-n`). Assume that the similarity
`f : V_ℚ → V_ℚ` given in Equation (2.4.1) is defined in terms of the oriented plane `P` given in
Equation (2.4.5). Then the discriminant of the Hermitian form `H` is `(-1)^n`.

Here `P = P_Θ` for `Θ` ample for the complex structure `J` of `X` (so that Assumption 2.4.1 holds,
`PTheta_assumption2_4_1`); `d > 0` rational (the paper: a positive integer). -/
theorem lemma3_1_3 (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    (PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)).DiscIs
      (PTheta_isCompl n d hd Θ _ _ hΘ.bijective_thetaMap) ((-1) ^ n) := by
  sorry

end WeilClasses
