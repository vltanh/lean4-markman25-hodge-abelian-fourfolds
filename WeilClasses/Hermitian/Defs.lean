module

public import WeilClasses.WeilType.Theta
public import WeilClasses.External.Chevalley.Sec3
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Surjectivity

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
  gives `U(V_ℚ, H)`, of infinite index. The paper's proof of the finite index ("the norm character
  has finitely many values", "units are finite") needs integrality (a gap; REPORT.md); we prove
  instead that the spinor norm is trivial on `SU(V_ℚ, H)` (`KSecant.s3_mem_SOplus_of_SUH`);
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

theorem rhoHom_apply (g : Spin F n) : rhoHom F n g = rho F n g :=
  LinearEquiv.ext fun _ => coe_spinToOrthogonal_apply _ _ _

/-- **`SO_+(V_F)`**: the image `ρ(Spin(V_F))` of the spin group, equal to the kernel of the spinor
norm `SO(V_F) → F^×/(F^×)²` (notation table of the paper; Tau Ceti
`range_spinToSpecialOrthogonal_eq_ker_spinorNorm`). -/
noncomputable def SOplus : Subgroup (V F n ≃ₗ[F] V F n) := (rhoHom F n).range

theorem mem_SOplus_iff (g : V F n ≃ₗ[F] V F n) : g ∈ SOplus F n ↔ ∃ x : Spin F n, rho F n x = g := by
  simp only [SOplus, MonoidHom.mem_range, rhoHom_apply]

end SOplus

/-! ## Helpers (prefix `s3_`)

Generic facts used in the proofs of §3: the matrix extension of an endomorphism of `V_F` to
`V_{F'}` (`bcEndV` and `complexifyV` are instances), and determinants of restrictions to invariant
subspaces. -/

section S3Ext

variable (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (n : ℕ)

/-- The matrix extension of an endomorphism of `V_F` to `V_{F'}` (same matrix in the bases
`basisV`); `bcEndV F' n = s3_ext ℚ F' n` and `complexifyV n = s3_ext ℝ ℂ n`. -/
noncomputable def s3_ext (A : V F n →ₗ[F] V F n) : V F' n →ₗ[F'] V F' n :=
  Matrix.toLin (basisV F' n) (basisV F' n)
    ((LinearMap.toMatrix (basisV F n) (basisV F n) A).map (algebraMap F F'))

theorem s3_bcEndV_eq (F' : Type*) [Field F'] [CharZero F'] (A : V ℚ n →ₗ[ℚ] V ℚ n) :
    bcEndV F' n A = s3_ext ℚ F' n A := rfl

theorem s3_complexifyV_eq (A : Module.End ℝ (V ℝ n)) : complexifyV n A = s3_ext ℝ ℂ n A := rfl

theorem s3_ext_comp (A B : V F n →ₗ[F] V F n) :
    s3_ext F F' n (A ∘ₗ B) = s3_ext F F' n A ∘ₗ s3_ext F F' n B := by
  simp only [s3_ext]
  rw [LinearMap.toMatrix_comp (basisV F n) (basisV F n), Matrix.map_mul,
    Matrix.toLin_mul (basisV F' n) (basisV F' n)]

theorem s3_ext_mul (A B : V F n →ₗ[F] V F n) :
    s3_ext F F' n (A * B) = s3_ext F F' n A * s3_ext F F' n B :=
  s3_ext_comp F F' n A B

theorem s3_ext_id : s3_ext F F' n LinearMap.id = LinearMap.id := by
  simp only [s3_ext, LinearMap.toMatrix_id]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin_one]

theorem s3_ext_one : s3_ext F F' n 1 = 1 := s3_ext_id F F' n

theorem s3_ext_add (A B : V F n →ₗ[F] V F n) :
    s3_ext F F' n (A + B) = s3_ext F F' n A + s3_ext F F' n B := by
  simp only [s3_ext, map_add]
  rw [Matrix.map_add _ (map_add _), map_add]

theorem s3_ext_smul (c : F) (A : V F n →ₗ[F] V F n) :
    s3_ext F F' n (c • A) = algebraMap F F' c • s3_ext F F' n A := by
  simp only [s3_ext]
  rw [← map_smul, map_smul]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem s3_ext_neg (A : V F n →ₗ[F] V F n) :
    s3_ext F F' n (-A) = -s3_ext F F' n A := by
  simp only [s3_ext]
  rw [map_neg, Matrix.map_neg _ (map_neg _), map_neg]

theorem s3_ext_inv_comp (g : V F n ≃ₗ[F] V F n) :
    s3_ext F F' n (g⁻¹ : V F n ≃ₗ[F] V F n) ∘ₗ s3_ext F F' n g = LinearMap.id := by
  rw [← s3_ext_comp]
  have : ((g⁻¹ : V F n ≃ₗ[F] V F n) : V F n →ₗ[F] V F n) ∘ₗ (g : V F n →ₗ[F] V F n) =
      LinearMap.id :=
    LinearMap.ext fun x => by simp
  rw [this, s3_ext_id]

end S3Ext

section S3DetOne

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- `A` maps `W` into itself, with determinant one there. -/
def s3_DetOne (A : M →ₗ[K] M) (W : Submodule K M) : Prop :=
  ∃ h : ∀ x ∈ W, A x ∈ W, LinearMap.det (A.restrict h) = 1

theorem s3_DetOne_id (W : Submodule K M) : s3_DetOne (LinearMap.id : M →ₗ[K] M) W := by
  refine ⟨fun x hx => hx, ?_⟩
  have : (LinearMap.id : M →ₗ[K] M).restrict (fun x hx => hx) = (LinearMap.id : W →ₗ[K] W) := by
    ext; rfl
  rw [this, LinearMap.det_id]

theorem s3_DetOne_comp {A B : M →ₗ[K] M} {W : Submodule K M} (hA : s3_DetOne A W)
    (hB : s3_DetOne B W) : s3_DetOne (A ∘ₗ B) W := by
  obtain ⟨hA, hA'⟩ := hA
  obtain ⟨hB, hB'⟩ := hB
  refine ⟨fun x hx => hA _ (hB x hx), ?_⟩
  rw [LinearMap.restrict_comp hB hA, LinearMap.det_comp, hA', hB', mul_one]

theorem s3_DetOne_congr {A B : M →ₗ[K] M} {W : Submodule K M} (h : A = B) (hA : s3_DetOne A W) :
    s3_DetOne B W := h ▸ hA

/-- If `B ∘ A = 1` and `A` maps the finite-dimensional `W` into itself with determinant one, so
does `B`. -/
theorem s3_DetOne_inv [FiniteDimensional K M] {A B : M →ₗ[K] M} {W : Submodule K M}
    (hA : s3_DetOne A W) (hBA : B ∘ₗ A = LinearMap.id) : s3_DetOne B W := by
  obtain ⟨hA, hA'⟩ := hA
  have hinj : Function.Injective (A.restrict hA) := by
    intro x y hxy
    have := congrArg (fun z : W => B (z : M)) hxy
    simp only [LinearMap.restrict_apply] at this
    have h1 := LinearMap.congr_fun hBA x
    have h2 := LinearMap.congr_fun hBA y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    exact Subtype.ext (by rw [← h1, ← h2]; exact this)
  have hsurj : Function.Surjective (A.restrict hA) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hB : ∀ x ∈ W, B x ∈ W := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hy' : A y = x := congrArg Subtype.val hy
    have := LinearMap.congr_fun hBA y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← hy', this]
    exact y.2
  refine ⟨hB, ?_⟩
  have hcomp : (B.restrict hB) ∘ₗ (A.restrict hA) = LinearMap.id := by
    ext x
    have := LinearMap.congr_fun hBA x
    simpa using this
  have := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, hA', mul_one, LinearMap.det_id] at this
  exact this

end S3DetOne

/-- The determinant-one condition of `SO_+(V_ℚ)_f`, `SO_+(V_ℝ)_f` and `SU(V_ℚ, H)` is closed under
products, contains `1` and is closed under inverses. -/
theorem s3_DetOne_ext_mul {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {n : ℕ}
    {W : Submodule F' (V F' n)} {g h : V F n ≃ₗ[F] V F n}
    (hg : s3_DetOne (s3_ext F F' n g) W) (hh : s3_DetOne (s3_ext F F' n h) W) :
    s3_DetOne (s3_ext F F' n (g * h : V F n ≃ₗ[F] V F n)) W :=
  s3_DetOne_congr (s3_ext_comp F F' n _ _).symm (s3_DetOne_comp hg hh)

theorem s3_DetOne_ext_one {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {n : ℕ}
    (W : Submodule F' (V F' n)) :
    s3_DetOne (s3_ext F F' n (1 : V F n ≃ₗ[F] V F n)) W :=
  s3_DetOne_congr (s3_ext_id F F' n).symm (s3_DetOne_id W)

theorem s3_DetOne_ext_inv {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {n : ℕ}
    {W : Submodule F' (V F' n)} {g : V F n ≃ₗ[F] V F n} (hg : s3_DetOne (s3_ext F F' n g) W) :
    s3_DetOne (s3_ext F F' n (g⁻¹ : V F n ≃ₗ[F] V F n)) W :=
  s3_DetOne_inv hg (s3_ext_inv_comp F F' n g)

/-- `g⁻¹` commutes with `A` if `g` does. -/
theorem s3_inv_comm {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {A : M →ₗ[F] M}
    {g : M ≃ₗ[F] M} (hg : ∀ x, g (A x) = A (g x)) (x : M) :
    (g⁻¹ : M ≃ₗ[F] M) (A x) = A ((g⁻¹ : M ≃ₗ[F] M) x) := by
  apply g.injective
  rw [hg]
  simp

/-! ### Antisymmetric matrices -/

section S3Pfaffian

open Matrix

/-- The determinant of an antisymmetric matrix over a field of characteristic zero is a square
(the square of its Pfaffian). -/
theorem s3_isSquare_det_of_transpose_eq_neg {F : Type*} [Field F] [CharZero F] :
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) F), Aᵀ = -A → IsSquare A.det := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A hA
  have hdiag : ∀ i, A i i = 0 := by
    intro i
    have := congrFun (congrFun hA i) i
    simp only [transpose_apply, Matrix.neg_apply] at this
    have h2 : (2 : F) * A i i = 0 := by linear_combination this
    simpa using h2
  by_cases hA0 : A = 0
  · subst hA0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨1, by simp⟩
    · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact ⟨0, by simp⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hA0 (Matrix.ext h)
  have hne : i ≠ j := by
    rintro rfl
    exact hij (hdiag i)
  -- `m = k + 2`
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := by
    refine ⟨m - 2, ?_⟩
    have : 2 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m
      · exact i.elim0
      · exact hne (Subsingleton.elim _ _)
    omega
  -- move `(i, j)` to `(0, 1)`
  set τ : Equiv.Perm (Fin (k + 2)) := Equiv.swap 0 i with hτ
  have hτj : τ j ≠ 0 := by
    intro h
    have : j = i := by
      have h' := congrArg τ h
      rw [hτ, Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
      exact h'
    exact hne this.symm
  set σ : Equiv.Perm (Fin (k + 2)) := (Equiv.swap 1 (τ j)).trans τ with hσ
  have hσ0 : σ 0 = i := by
    simp only [hσ, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne zero_ne_one (Ne.symm hτj), hτ, Equiv.swap_apply_left]
  have hσ1 : σ 1 = j := by
    simp only [hσ, Equiv.trans_apply, Equiv.swap_apply_left]
    rw [hτ, Equiv.swap_apply_self]
  set B := A.submatrix σ σ with hBdef
  have hB : Bᵀ = -B := by
    ext a b
    have := congrFun (congrFun hA (σ a)) (σ b)
    simp only [transpose_apply, Matrix.neg_apply] at this
    simp only [hBdef, transpose_apply, submatrix_apply, Matrix.neg_apply, this]
  have hdetB : B.det = A.det := Matrix.det_submatrix_equiv_self σ A
  have hB01 : B 0 1 ≠ 0 := by
    simp only [hBdef, submatrix_apply, hσ0, hσ1]
    exact hij
  -- reindex as a `2 + k` block matrix
  set e : Fin (k + 2) ≃ Fin 2 ⊕ Fin k := (finCongr (add_comm k 2)).trans finSumFinEquiv.symm
    with he
  have he0 : e.symm (Sum.inl 0) = 0 := by
    simp only [he, Equiv.symm_trans_apply, Equiv.symm_symm, finSumFinEquiv_apply_left]
    rfl
  have he1 : e.symm (Sum.inl 1) = 1 := by
    simp only [he, Equiv.symm_trans_apply, Equiv.symm_symm, finSumFinEquiv_apply_left]
    rfl
  set C := Matrix.reindex e e B with hCdef
  have hdetC : C.det = B.det := Matrix.det_reindex_self e B
  have hC : ∀ a b, C b a = -C a b := by
    intro a b
    have := congrFun (congrFun hB (e.symm a)) (e.symm b)
    simp only [transpose_apply, Matrix.neg_apply] at this
    simp only [hCdef, reindex_apply, submatrix_apply, this]
  set E := C.toBlocks₁₁ with hE
  have hE01 : E 0 1 = B 0 1 := by
    simp only [hE, toBlocks₁₁, of_apply, hCdef, reindex_apply, submatrix_apply, he0, he1]
  have hE00 : E 0 0 = 0 := by
    have := hC (Sum.inl 0) (Sum.inl 0)
    simp only [hE, toBlocks₁₁, of_apply]
    have h2 : (2 : F) * C (Sum.inl 0) (Sum.inl 0) = 0 := by linear_combination this
    simpa using h2
  have hE11 : E 1 1 = 0 := by
    have := hC (Sum.inl 1) (Sum.inl 1)
    simp only [hE, toBlocks₁₁, of_apply]
    have h2 : (2 : F) * C (Sum.inl 1) (Sum.inl 1) = 0 := by linear_combination this
    simpa using h2
  have hE10 : E 1 0 = -E 0 1 := by
    simp only [hE, toBlocks₁₁, of_apply]
    exact hC _ _
  have hdetE : E.det = B 0 1 ^ 2 := by
    rw [det_fin_two, hE00, hE11, hE10, hE01]
    ring
  have hdetE0 : E.det ≠ 0 := by
    rw [hdetE]
    exact pow_ne_zero 2 hB01
  have : Invertible E.det := invertibleOfNonzero hdetE0
  have : Invertible E := Matrix.invertibleOfDetInvertible E
  set X := ⅟E with hX
  have hET : Eᵀ = -E := by
    ext a b
    simp only [hE, transpose_apply, toBlocks₁₁, of_apply, Matrix.neg_apply]
    exact hC _ _
  have hXT : Xᵀ = -X := by
    have h1 : E * X = 1 := mul_invOf_self E
    have h2 : Xᵀ * E = -1 := by
      have : (E * X)ᵀ = 1 := by rw [h1, transpose_one]
      rw [transpose_mul, hET] at this
      rw [← neg_neg (Xᵀ * E), ← Matrix.mul_neg, this]
    calc Xᵀ = Xᵀ * (E * X) := by rw [h1, Matrix.mul_one]
      _ = (Xᵀ * E) * X := by rw [Matrix.mul_assoc]
      _ = -X := by rw [h2, Matrix.neg_mul, Matrix.one_mul]
  set S := C.toBlocks₂₂ - C.toBlocks₂₁ * X * C.toBlocks₁₂ with hS
  have h12 : (C.toBlocks₁₂)ᵀ = -C.toBlocks₂₁ := by
    ext a b
    simp only [transpose_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.neg_apply]
    exact hC _ _
  have h21 : (C.toBlocks₂₁)ᵀ = -C.toBlocks₁₂ := by
    ext a b
    simp only [transpose_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.neg_apply]
    exact hC _ _
  have h22 : (C.toBlocks₂₂)ᵀ = -C.toBlocks₂₂ := by
    ext a b
    simp only [transpose_apply, toBlocks₂₂, of_apply, Matrix.neg_apply]
    exact hC _ _
  have hST : Sᵀ = -S := by
    rw [hS, transpose_sub, transpose_mul, transpose_mul, h12, h21, h22, hXT]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_sub, Matrix.mul_assoc]
    abel
  obtain ⟨t, ht⟩ := ih k (by omega) S hST
  have hdet : C.det = E.det * S.det := by
    conv_lhs => rw [← fromBlocks_toBlocks C]
    exact det_fromBlocks₁₁ _ _ _ _
  refine ⟨B 0 1 * t, ?_⟩
  rw [← hdetB, ← hdetC, hdet, hdetE, ht]
  ring

end S3Pfaffian

/-! ### The field `K` -/

section S3Field

variable {d : ℚ}

theorem s3_coe_algebraMap (q : ℚ) : ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := by simp

theorem s3_sqrtNeg_mul_self (hd : 0 < d) :
    Kd.sqrtNeg d * Kd.sqrtNeg d = -algebraMap ℚ (Kd d) d := by
  apply Subtype.ext
  have h := sqrtNeg_sq hd.le
  rw [pow_two] at h
  simp only [Subfield.coe_mul, Subfield.coe_neg, s3_coe_algebraMap]
  exact h

theorem s3_σ_sqrtNeg : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp only [Kd.coe_σ, Subfield.coe_neg]
  show (starRingEnd ℂ) (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) =
    -(Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))
  simp

theorem s3_σ_algebraMap (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp only [Kd.coe_σ, s3_coe_algebraMap]
  simp

theorem s3_sqrtNeg_ne_zero (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := s3_sqrtNeg_mul_self hd
  rw [h, zero_mul, eq_comm, neg_eq_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at this
  exact hd.ne' this

theorem s3_ratPart_ratCast (q : ℚ) : Kd.ratPart d (q : Kd d) = q := by
  have h := Classical.choose_spec (Kd.exists_ratPart d (q : Kd d))
  have h' : ((q : Kd d) : ℂ).re = (q : ℝ) := by simp
  show Classical.choose (Kd.exists_ratPart d (q : Kd d)) = q
  exact_mod_cast h.trans h'

theorem s3_ratPart_algebraMap (q : ℚ) : Kd.ratPart d (algebraMap ℚ (Kd d) q) = q :=
  s3_ratPart_ratCast q

/-- `Θ(a, b) = -Θ(b, a)`. -/
theorem s3_eval2_swap {F : Type*} [Field F] [CharZero F] {n : ℕ} (ξ : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ b a = -eval2 F n ξ a b := by
  simp only [eval2, D]
  rw [contractLeft_comm, map_neg]

/-- `Nm(√-d) = d`: `d^k p² ∈ Nm(K^×)` for `p ≠ 0`. -/
theorem s3_mem_normGroup (hd : 0 < d) (k : ℕ) {p : ℚ} (hp : p ≠ 0) :
    d ^ k * p ^ 2 ∈ Kd.normGroup d := by
  refine ⟨Kd.sqrtNeg d ^ k * algebraMap ℚ (Kd d) p, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (s3_sqrtNeg_ne_zero hd))
      ((map_ne_zero_iff _ (algebraMap ℚ (Kd d)).injective).mpr hp)
  · have h := Kd.coe_Nm hd (Kd.sqrtNeg d ^ k * algebraMap ℚ (Kd d) p)
    have hs : ((Kd.sqrtNeg d : Kd d) : ℂ) * (starRingEnd ℂ) ((Kd.sqrtNeg d : Kd d) : ℂ) = (d : ℂ) := by
      show (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) *
        (starRingEnd ℂ) (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = (d : ℂ)
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      have h1 : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = ((d : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hd.le)]
      have h2 : ((d : ℝ) : ℂ) = (d : ℂ) := Complex.ofReal_ratCast d
      rw [h2] at h1
      linear_combination (-(Complex.I * Complex.I)) * h1 + (-(d : ℂ)) * Complex.I_mul_I
    have h3 : ((Kd.Nm d (Kd.sqrtNeg d ^ k * algebraMap ℚ (Kd d) p) : ℚ) : ℂ) =
        ((d ^ k * p ^ 2 : ℚ) : ℂ) := by
      rw [h]
      simp only [Subfield.coe_mul, SubmonoidClass.coe_pow, s3_coe_algebraMap, map_mul, map_pow,
        map_ratCast]
      push_cast
      rw [← hs]
      ring
    exact_mod_cast h3

end S3Field

/-! ### Change of coefficients in coordinates -/

section S3BaseChange

variable {n : ℕ}

theorem s3_bcDual_apply_e {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (θ : Module.Dual F (H1 F n)) (i : Fin (2 * n)) :
    bcDual F F' n θ (e F' n i) = algebraMap F F' (θ (e F n i)) := by
  simp [bcDual, f, e, Pi.single_apply, Algebra.algebraMap_eq_smul_one]

theorem s3_basisV_inl (F : Type*) [Field F] (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inl i)) = (f F n i, 0) := by
  simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
    Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl]
  congr 1
  ext x
  simp [f, Pi.basisFun_repr]

theorem s3_basisV_inr (F : Type*) [Field F] (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inr i)) = (0, e F n i) := by
  simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
    Sum.elim_inr, Function.comp_apply, LinearMap.coe_inr]
  simp [e, Pi.basisFun_apply]

theorem s3_bcDual_f (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']
    (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp [f, e]
  · intro j _ hj
    simp [f, e, hj]
  · simp

theorem s3_bcH1_e (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (i : Fin (2 * n)) :
    bcH1 F F' n (e F n i) = e F' n i := by
  ext j
  simp [bcH1, e, Pi.single_apply]

/-- Change of coefficients maps the basis `basisV` to the basis `basisV`. -/
theorem s3_bcV_basisV (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (i : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n i) = basisV F' n i := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [s3_basisV_inl, s3_basisV_inl]
    simp [bcV, s3_bcDual_f]
  · rw [s3_basisV_inr, s3_basisV_inr]
    simp [bcV, s3_bcH1_e]

/-- The matrix extension `s3_ext F F' n A` extends `A`. -/
theorem s3_ext_bcV (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']
    (A : V F n →ₗ[F] V F n) (v : V F n) :
    s3_ext F F' n A (bcV F F' n v) = bcV F F' n (A v) := by
  have key : ((s3_ext F F' n A).restrictScalars F) ∘ₗ bcV F F' n = bcV F F' n ∘ₗ A := by
    refine (basisV F n).ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      s3_bcV_basisV, s3_ext, Matrix.toLin_self]
    conv_rhs => rw [← Matrix.toLin_toMatrix (basisV F n) (basisV F n) A, Matrix.toLin_self]
    simp only [map_sum, map_smul, s3_bcV_basisV, Matrix.map_apply, algebraMap_smul]
  exact LinearMap.congr_fun key v

end S3BaseChange

/-! ### Rational parts and descent -/

section S3Descend

variable {n : ℕ} {d : ℚ}

theorem s3_ratPartV_bcV (v : V ℚ n) : ratPartV n d (bcV ℚ (Kd d) n v) = v := by
  ext x
  · simp only [ratPartV, bcV, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.prodMap_apply]
    simp only [s3_bcDual_apply_e, s3_ratPart_algebraMap]
    simp [f, e, Pi.single_apply]
  · simp [ratPartV, bcV, bcH1, s3_ratPart_ratCast]

theorem s3_descend_add (A B : V (Kd d) n →ₗ[Kd d] V (Kd d) n) :
    descend n d (A + B) = descend n d A + descend n d B := by
  ext v <;> simp [descend]

theorem s3_descend_smul (q : ℚ) (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n) :
    descend n d (algebraMap ℚ (Kd d) q • A) = q • descend n d A := by
  apply LinearMap.ext
  intro v
  simp only [descend, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.smul_apply, algebraMap_smul, map_smul]

theorem s3_descend_id : descend n d LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [descend, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.id_apply, s3_ratPartV_bcV]

end S3Descend

theorem s3_pairing_comm {F : Type*} [Field F] [CharZero F] {n : ℕ} (x y : V F n) :
    pairing F n x y = pairing F n y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

/-- `ρ(g)` is an isometry of the pairing `(·,·)_V`. -/
theorem s3_pairing_rho {F : Type*} [Field F] [CharZero F] {n : ℕ} (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, rho, ← map_add,
    spinVectorAction_map_app]

/-- The elements of `SO_+(V_F)` are isometries of `(·,·)_V`. -/
theorem s3_pairing_of_mem_SOplus {F : Type*} [Field F] [CharZero F] {n : ℕ}
    {g : V F n ≃ₗ[F] V F n} (hg : g ∈ SOplus F n) (x y : V F n) :
    pairing F n (g x) (g y) = pairing F n x y := by
  obtain ⟨s, rfl⟩ := (mem_SOplus_iff F n g).mp hg
  exact s3_pairing_rho s x y

section S3Signature

variable {n : ℕ}

theorem s3_finrank_V (F : Type*) [Field F] {n : ℕ} : Module.finrank F (V F n) = 2 * n + 2 * n := by
  rw [Module.finrank_eq_card_basis (basisV F n), Fintype.card_fin]

/-- For an orthogonal basis `c` of `(V_ℚ, Q)`, Sylvester's law: the indices of inertia are the
numbers of positive and of negative values `Q(c_i)`. -/
theorem s3_sig_of_orthogonal_basis {ι : Type*} [Fintype ι] (c : Module.Basis ι ℚ (V ℚ n))
    (hc : ∀ i j, i ≠ j → pairing ℚ n (c i) (c j) = 0) :
    sigPos (Q ℚ n) = {i | 0 < Q ℚ n (c i)}.ncard ∧
      sigNeg (Q ℚ n) = {i | Q ℚ n (c i) < 0}.ncard := by
  have hortho : (QuadraticMap.associated (R := ℚ) (Q ℚ n)).IsOrthoᵢ c := by
    intro i j hij
    have := hc i j hij
    simp only [QuadraticMap.polarBilin_apply_apply] at this
    show QuadraticMap.associated (Q ℚ n) (c i) (c j) = 0
    rw [QuadraticMap.associated_apply, ← QuadraticMap.polar, this, smul_zero]
  have heq : QuadraticMap.Equivalent (Q ℚ n)
      (QuadraticMap.weightedSumSquares ℚ fun i => Q ℚ n (c i)) := by
    rw [← QuadraticMap.basisRepr_eq_of_iIsOrtho (Q ℚ n) c hortho]
    exact ⟨QuadraticMap.isometryEquivBasisRepr _ c⟩
  exact ⟨QuadraticForm.sigPos_of_equiv_weightedSumSquares heq,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares heq⟩


/-- `{s | p s}.ncard` for a predicate on a sum type. -/
theorem s3_ncard_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop) [DecidablePred p] :
    {s | p s}.ncard = (Finset.univ.filter fun a => p (Sum.inl a)).card +
      (Finset.univ.filter fun b => p (Sum.inr b)).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [← Finset.card_disjSum]
  apply Finset.card_bij (fun s _ => s)
  · rintro (a | b) h <;> simpa using h
  · intro a _ b _ h; exact h
  · rintro (a | b) h <;> exact ⟨_, by simpa using h, rfl⟩

/-- The pairing (1.2.2) on `V_ℚ` has signature `(2n, 2n)`. -/
theorem s3_sig_Q : sigPos (Q ℚ n) = 2 * n ∧ sigNeg (Q ℚ n) = 2 * n := by
  let w : Fin (2 * n) ⊕ Fin (2 * n) → V ℚ n :=
    Sum.elim (fun i => (f ℚ n i, e ℚ n i)) (fun i => (f ℚ n i, -e ℚ n i))
  have hfe : ∀ i j, f ℚ n i (e ℚ n j) = if i = j then 1 else 0 := by
    intro i j
    simp [f, e, Pi.single_apply]
  have hQw : ∀ s, Q ℚ n (w s) = Sum.elim (fun _ => (1 : ℚ)) (fun _ => -1) s := by
    rintro (i | i) <;> simp [w, QuadraticForm.dualProd_apply, hfe]
  have hpw : ∀ s t, s ≠ t → pairing ℚ n (w s) (w t) = 0 := by
    rintro (i | i) (j | j) hst <;>
      simp only [w, QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, Sum.elim_inl,
        Sum.elim_inr, map_neg, hfe]
    · have hij : i ≠ j := fun h => hst (h ▸ rfl)
      simp [hij, Ne.symm hij]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · have hij : i ≠ j := fun h => hst (h ▸ rfl)
      simp [hij, Ne.symm hij]
  have hpw' : ∀ s, pairing ℚ n (w s) (w s) ≠ 0 := by
    intro s
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hQw]
    rcases s with i | i <;> norm_num
  have hli : LinearIndependent ℚ w :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := pairing ℚ n)
      (fun s t hst => hpw s t hst) hpw'
  let c := basisOfLinearIndependentOfCardEqFinrank' w hli (by simp)
  have hc : ∀ s, c s = w s := fun s => by simp [c]
  obtain ⟨h1, h2⟩ := s3_sig_of_orthogonal_basis c (fun s t hst => by rw [hc, hc]; exact hpw s t hst)
  simp only [hc, hQw] at h1 h2
  rw [h1, h2, s3_ncard_sum, s3_ncard_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  norm_num


theorem s3_pairing_sepLeft {F : Type*} [Field F] [CharZero F] (x : V F n)
    (hx : ∀ y, pairing F n x y = 0) : x = 0 := by
  obtain ⟨θ, w⟩ := x
  have h1 : θ = 0 := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro i
    have := hx (0, Pi.single i 1)
    simpa [QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd] using this
  have h2 : w = 0 := by
    ext i
    have := hx (f F n i, 0)
    simpa [QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, f] using this
  rw [h1, h2]; rfl

theorem s3_pairing_nondegenerate {F : Type*} [Field F] [CharZero F] :
    (pairing F n).Nondegenerate :=
  ⟨fun x hx => s3_pairing_sepLeft x hx,
    fun y hy => s3_pairing_sepLeft y fun x => by rw [s3_pairing_comm]; exact hy x⟩

theorem s3_pairing_isRefl {F : Type*} [Field F] [CharZero F] : (pairing F n).IsRefl :=
  fun x y h => by rw [s3_pairing_comm]; exact h

theorem s3_pairing_isSymm {F : Type*} [Field F] [CharZero F] : (pairing F n).IsSymm :=
  ⟨fun x y => s3_pairing_comm x y⟩

/-- In a nondegenerate symmetric space, the span of an orthogonal family with nonzero norms has a
nondegenerate orthogonal complement, complementary to it. -/
theorem s3_orth_complement {ι : Type*} [Fintype ι] (c : ι → V ℚ n)
    (hc1 : ∀ s, pairing ℚ n (c s) (c s) ≠ 0)
    (hc2 : ∀ s t, s ≠ t → pairing ℚ n (c s) (c t) = 0) :
    IsCompl (Submodule.span ℚ (Set.range c)) ((pairing ℚ n).orthogonal (Submodule.span ℚ (Set.range c))) ∧
      ((pairing ℚ n).restrict ((pairing ℚ n).orthogonal (Submodule.span ℚ (Set.range c)))).Nondegenerate := by
  set U := Submodule.span ℚ (Set.range c) with hU
  have hdisj : Disjoint U ((pairing ℚ n).orthogonal U) := by
    rw [Submodule.disjoint_def]
    intro u hu hu'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hu
    have ha : ∀ t, a t = 0 := by
      intro t
      have := hu' (c t) (Submodule.subset_span ⟨t, rfl⟩)
      simp only [map_sum, map_smul, smul_eq_mul] at this
      rw [Finset.sum_eq_single t (fun s _ hst => by rw [s3_pairing_comm, hc2 s t hst, mul_zero])
        (by simp)] at this
      exact (mul_eq_zero.mp this).resolve_right (by rw [s3_pairing_comm]; exact hc1 t)
    simp [ha]
  have hcompl : IsCompl U ((pairing ℚ n).orthogonal U) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint s3_pairing_isRefl).mpr hdisj
  refine ⟨hcompl, ?_⟩
  apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ s3_pairing_isRefl
  rw [LinearMap.BilinForm.orthogonal_orthogonal s3_pairing_nondegenerate s3_pairing_isRefl]
  exact hcompl.disjoint.symm

end S3Signature

variable {n : ℕ} {d : ℚ}

/-- A rational `K`-secant exists only when `d > 0`. (The upstream `KSecant.d_pos` lost its
`KSecant` argument in elaboration: it states `∀ d, 0 < d`; we do not use it.) -/
theorem s3_d_pos (P : KSecant n d) : 0 < d := by
  by_contra hd
  rw [not_lt] at hd
  have h0 : sqrtNeg d = 0 := by
    simp [sqrtNeg, Real.sqrt_eq_zero'.mpr (by exact_mod_cast hd : (d : ℝ) ≤ 0)]
  have hσ : ∀ z : Kd d, Kd.σ d z = z := by
    intro z
    apply Subtype.ext
    obtain ⟨a, b, hz⟩ := (Kd.mem_iff d).mp z.2
    rw [Kd.coe_σ, hz, h0]
    simp
  have hu : σS n d P.u₁ = P.u₁ := by
    show (∑ K, Kd.σ d ((basisS (Kd d) n).repr P.u₁ K) • basisS (Kd d) n K) = P.u₁
    simp only [hσ]
    exact (basisS (Kd d) n).sum_repr P.u₁
  have := P.linIndep.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
  simp [hu] at this

namespace KSecant

variable (P : KSecant n d)

/-! ### `η` is `ℚ`-linear in `λ` -/

theorem s3_ηK_add (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.ηK hW (l + l') = P.ηK hW l + P.ηK hW l' := by
  simp only [ηK, add_smul, map_add]
  abel

theorem s3_ηK_algebraMap_mul (hW : IsCompl P.W₁ P.W₂) (q : ℚ) (l : Kd d) :
    P.ηK hW (algebraMap ℚ (Kd d) q * l) = algebraMap ℚ (Kd d) q • P.ηK hW l := by
  simp only [ηK, map_mul, s3_σ_algebraMap, mul_smul, smul_add]

theorem s3_ηK_one (hW : IsCompl P.W₁ P.W₂) : P.ηK hW 1 = LinearMap.id := by
  simp only [ηK, map_one, one_smul]
  exact Submodule.subtype_comp_projectionOnto_add_eq_id hW

theorem s3_η_add (hW : IsCompl P.W₁ P.W₂) (l l' : Kd d) :
    P.η hW (l + l') = P.η hW l + P.η hW l' := by
  simp only [η, s3_ηK_add, s3_descend_add]

theorem s3_η_algebraMap_mul (hW : IsCompl P.W₁ P.W₂) (q : ℚ) (l : Kd d) :
    P.η hW (algebraMap ℚ (Kd d) q * l) = q • P.η hW l := by
  simp only [η, s3_ηK_algebraMap_mul, s3_descend_smul]

theorem s3_η_one (hW : IsCompl P.W₁ P.W₂) : P.η hW 1 = LinearMap.id := by
  simp only [η, s3_ηK_one, s3_descend_id]

/-- `η_λ = a + b f` for `λ = a + b √-d`. -/
theorem s3_η_apply (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (y : V ℚ n) :
    P.η hW l y = Kd.ratPart d l • y + Kd.sqrtNegCoeff d l • P.fη hW y := by
  conv_lhs => rw [Kd.eq_ratPart_add_sqrtNegCoeff (s3_d_pos P) l]
  rw [s3_η_add, ← mul_one (algebraMap ℚ (Kd d) (Kd.ratPart d l)), s3_η_algebraMap_mul,
    s3_η_algebraMap_mul, s3_η_one]
  rfl

/-- `(f x, y)_V = -(f y, x)_V`. -/
theorem s3_pairing_fη_swap (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    pairing ℚ n (P.fη hW x) y = -pairing ℚ n (P.fη hW y) x := by
  rw [P.pairing_fη_left hW, s3_pairing_comm]

/-- `(f x, x)_V = 0`. -/
theorem s3_pairing_fη_self (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    pairing ℚ n (P.fη hW x) x = 0 := by
  have := P.s3_pairing_fη_swap hW x x
  linarith

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
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
    exact ⟨mul_mem hg1 hh1, fun x => by simp only [LinearEquiv.mul_apply, hh2, hg2],
      s3_DetOne_ext_mul hg3 hh3, s3_DetOne_ext_mul hg4 hh4⟩
  one_mem' := ⟨one_mem _, fun _ => rfl, s3_DetOne_ext_one _, s3_DetOne_ext_one _⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨inv_mem hg1, s3_inv_comm hg2, s3_DetOne_ext_inv hg3, s3_DetOne_ext_inv hg4⟩

/-- **`SO_+(V_ℝ)_f`** (§4): the elements of `SO_+(V_ℝ)` commuting with `f` whose complexifications
restrict to `W_{i,ℂ}` with determinant `1`, `i = 1, 2`. -/
noncomputable def SOplusfR (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℝ n ≃ₗ[ℝ] V ℝ n) where
  carrier := {g | g ∈ SOplus ℝ n ∧ (∀ x, g (P.fR hW x) = P.fR hW (g x)) ∧
    (∃ h : ∀ x ∈ P.W₁ℂ, complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n) x ∈ P.W₁ℂ,
      LinearMap.det ((complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n)).restrict h) = 1) ∧
    (∃ h : ∀ x ∈ P.W₂ℂ, complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n) x ∈ P.W₂ℂ,
      LinearMap.det ((complexifyV n (g : V ℝ n →ₗ[ℝ] V ℝ n)).restrict h) = 1)}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
    exact ⟨mul_mem hg1 hh1, fun x => by simp only [LinearEquiv.mul_apply, hh2, hg2],
      s3_DetOne_ext_mul hg3 hh3, s3_DetOne_ext_mul hg4 hh4⟩
  one_mem' := ⟨one_mem _, fun _ => rfl, s3_DetOne_ext_one _, s3_DetOne_ext_one _⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨inv_mem hg1, s3_inv_comm hg2, s3_DetOne_ext_inv hg3, s3_DetOne_ext_inv hg4⟩

end KSecant

/-! ## Base change and Galois conjugation (helpers for Lemma 3.1.1) -/

section S3Coord

/-- Coordinates of the image of a vector under a map sending a basis to a basis. -/
theorem s3_repr_map_basis {F F' ι M M' : Type*} [Field F] [Field F'] [Algebra F F'] [Fintype ι]
    [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F' M'] [Module F M']
    [IsScalarTower F F' M'] (b : Module.Basis ι F M) (b' : Module.Basis ι F' M')
    (φ : M →ₗ[F] M') (hφ : ∀ i, φ (b i) = b' i) (x : M) (i : ι) :
    b'.repr (φ x) i = algebraMap F F' (b.repr x i) := by
  have h1 : φ x = ∑ j, algebraMap F F' (b.repr x j) • b' j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφ, algebraMap_smul]
  rw [h1, b'.repr_sum_self]

theorem s3_injective_map_basis {F F' ι M M' : Type*} [Field F] [Field F'] [Algebra F F'] [Fintype ι]
    [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F' M'] [Module F M']
    [IsScalarTower F F' M'] (b : Module.Basis ι F M) (b' : Module.Basis ι F' M')
    (φ : M →ₗ[F] M') (hφ : ∀ i, φ (b i) = b' i) : Function.Injective φ := by
  intro x y hxy
  apply b.repr.injective
  ext i
  have := congrArg (fun z => b'.repr z i) hxy
  simp only [s3_repr_map_basis b b' φ hφ] at this
  exact (algebraMap F F').injective this

/-- A linear map whose matrix is fixed by a ring automorphism `c` commutes with the
`c`-semilinear map acting on coordinates. -/
theorem s3_conj_comm {K ι M : Type*} [Field K] [Fintype ι] [AddCommGroup M] [Module K M]
    (b : Module.Basis ι K M) (c : K ≃+* K) (T : M →ₗ[K] M)
    (hT : ∀ i j, c (b.repr (T (b j)) i) = b.repr (T (b j)) i) (x : M) :
    T (∑ i, c (b.repr x i) • b i) = ∑ i, c (b.repr (T x) i) • b i := by
  classical
  have hTx : ∀ i, b.repr (T x) i = ∑ j, b.repr x j * b.repr (T (b j)) i := by
    intro i
    rw [← LinearMap.toMatrix_mulVec_repr b b T x]
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hTb : ∀ j, T (b j) = ∑ i, b.repr (T (b j)) i • b i := fun j => (b.sum_repr _).symm
  rw [map_sum]
  simp only [map_smul, hTx, map_sum, map_mul, hT]
  conv_lhs => arg 2; ext j; rw [hTb j]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

end S3Coord

section S3Clifford

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

theorem s3_bcC_ι (v : V F n) : bcC F F' n (ι (Q F n) v) = ι (Q F' n) (bcV F F' n v) := by
  simp [bcC]

theorem s3_bcC_star_spin (g : Spin F n) :
    bcC F F' n (star (g : C F n)) = star (bcC F F' n (g : C F n)) := by
  have h2 : bcC F F' n (g : C F n) * star (bcC F F' n (g : C F n)) = 1 :=
    spinGroup.mul_star_self_of_mem (bcC_mem_spinGroup F F' n g)
  have h3 : bcC F F' n (star (g : C F n)) * bcC F F' n (g : C F n) = 1 := by
    rw [← map_mul, spinGroup.star_mul_self_of_mem g.2, map_one]
  calc bcC F F' n (star (g : C F n))
      = bcC F F' n (star (g : C F n)) * (bcC F F' n (g : C F n) * star (bcC F F' n (g : C F n))) := by
        rw [h2, mul_one]
    _ = (bcC F F' n (star (g : C F n)) * bcC F F' n (g : C F n)) * star (bcC F F' n (g : C F n)) := by
        rw [mul_assoc]
    _ = star (bcC F F' n (g : C F n)) := by rw [h3, one_mul]

/-- `ρ` commutes with change of coefficients. -/
theorem s3_rho_bcV (g : Spin F n) (v : V F n) :
    rho F' n (bcSpin F F' n g) (bcV F F' n v) = bcV F F' n (rho F n g v) := by
  apply CliffordAlgebra.ι_injective (Q F' n)
  rw [ι_rho, ← s3_bcC_ι, ← s3_bcC_ι, ι_rho]
  show bcC F F' n (g : C F n) * bcC F F' n (ι (Q F n) v) * star (bcC F F' n (g : C F n)) = _
  rw [← s3_bcC_star_spin, ← map_mul, ← map_mul]

/-- The extension of `ρ(g)` is `ρ` of the extension of `g`. -/
theorem s3_ext_rho (g : Spin F n) :
    s3_ext F F' n (rho F n g : V F n →ₗ[F] V F n) =
      (rho F' n (bcSpin F F' n g) : V F' n →ₗ[F'] V F' n) := by
  refine (basisV F' n).ext fun i => ?_
  rw [← s3_bcV_basisV F F', s3_ext_bcV]
  simp only [LinearEquiv.coe_coe]
  rw [s3_rho_bcV]

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) := by
  exact ExteriorAlgebra.lift_ι_apply F _ _ w

theorem s3_bcDual_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  have hw : w = ∑ i, w i • e F n i := by
    ext j; simp [e, Pi.single_apply]
  conv_rhs => rw [hw]
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul, map_mul]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [f, bcH1, Algebra.smul_def, mul_comm]

/-- Contraction commutes with change of coefficients. -/
theorem s3_bcS_D (θ : Module.Dual F (H1 F n)) (s : S F n) :
    bcS F F' n (D F n θ s) = D F' n (bcDual F F' n θ) (bcS F F' n s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, contractLeft_algebraMap, map_zero, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x w hx =>
    simp only [D] at hx ⊢
    rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, map_mul, s3_bcS_ι, contractLeft_ι_mul, hx,
      s3_bcDual_bcH1, algebraMap_smul]

/-- The spin representation commutes with change of coefficients. -/
theorem s3_m_bcC (x : C F n) (s : S F n) :
    m F' n (bcC F F' n x) (bcS F F' n s) = bcS F F' n (m F n x s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n),
      AlgHom.commutes]
    simp only [Module.algebraMap_end_apply, map_smul, algebraMap_smul]
  | ι v =>
    rw [s3_bcC_ι]
    simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, map_add]
    obtain ⟨θ, w⟩ := v
    simp only [bcV, LinearMap.prodMap_apply, L, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mul_apply', map_mul, s3_bcS_ι, s3_bcS_D]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, hb, ha]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_ιMulti {k : ℕ} (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact s3_bcS_ι F F' (v i)

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_basisS (K : Finset (Fin (2 * n))) :
    bcS F F' n (basisS F n K) = basisS F' n K := by
  simp only [basisS, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [s3_bcS_ιMulti]
  congr 1
  ext i j
  simp [bcH1, Pi.basisFun_apply, Pi.single_apply]

end S3Clifford

section S3Conj

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_repr (s : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n s) K = algebraMap F F' ((basisS F n).repr s K) :=
  s3_repr_map_basis (basisS F n) (basisS F' n) (bcS F F' n).toLinearMap
    (s3_bcS_basisS F F') s K

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_injective : Function.Injective (bcS F F' n) :=
  s3_injective_map_basis (basisS F n) (basisS F' n) (bcS F F' n).toLinearMap (s3_bcS_basisS F F')

theorem s3_bcV_repr (v : V F n) (i : Fin (2 * n + 2 * n)) :
    (basisV F' n).repr (bcV F F' n v) i = algebraMap F F' ((basisV F n).repr v i) :=
  s3_repr_map_basis (basisV F n) (basisV F' n) (bcV F F' n) (s3_bcV_basisV F F') v i

theorem s3_bcV_injective : Function.Injective (bcV F F' n) :=
  s3_injective_map_basis (basisV F n) (basisV F' n) (bcV F F' n) (s3_bcV_basisV F F')

variable {F'}

theorem s3_conjS_eq (c : F' ≃+* F') (s : S F' n) :
    conjS c n s = ∑ K, c ((basisS F' n).repr s K) • basisS F' n K := rfl

theorem s3_conjS_smul (c : F' ≃+* F') (a : F') (s : S F' n) :
    conjS c n (a • s) = c a • conjS c n s := by
  simp only [s3_conjS_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    smul_smul]

/-- The spin representation of a rational (resp. real) element commutes with the conjugation of
coordinates. -/
theorem s3_m_bcC_conjS (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (x : C F n) (s : S F' n) :
    m F' n (bcC F F' n x) (conjS c n s) = conjS c n (m F' n (bcC F F' n x) s) := by
  rw [s3_conjS_eq, s3_conjS_eq]
  apply s3_conj_comm
  intro i j
  rw [← s3_bcS_basisS F F', s3_m_bcC, s3_bcS_repr, hc]

omit [CharZero F'] in
theorem s3_basisV_repr_inl (v : V F' n) (i : Fin (2 * n)) :
    (basisV F' n).repr v (finSumFinEquiv (Sum.inl i)) = v.1 (e F' n i) := by
  simp only [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inl, Module.Basis.dualBasis_repr, Pi.basisFun_apply, e]

omit [CharZero F'] in
theorem s3_basisV_repr_inr (v : V F' n) (i : Fin (2 * n)) :
    (basisV F' n).repr v (finSumFinEquiv (Sum.inr i)) = v.2 i := by
  simp only [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inr, Pi.basisFun_repr]

/-- `conjV` acts on the coordinates in the basis `basisV`. -/
theorem s3_conjV_eq (c : F' ≃+* F') (v : V F' n) :
    conjV c n v = ∑ j, c ((basisV F' n).repr v j) • basisV F' n j := by
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [s3_basisV_repr_inl, s3_basisV_repr_inr, s3_basisV_inl, s3_basisV_inr]
  ext x
  · simp only [conjV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, Prod.fst_sum,
      Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero]
  · simp only [conjV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_add, Prod.snd_sum,
      Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Function.comp_apply]
    simp [e, Pi.single_apply]

theorem s3_conjV_smul (c : F' ≃+* F') (a : F') (v : V F' n) :
    conjV c n (a • v) = c a • conjV c n v := by
  simp only [s3_conjV_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    smul_smul]

/-- `m` is defined over `F`: `m_{c(v)}(c(s)) = c(m_v(s))`. -/
theorem s3_m_ι_conj (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (v : V F' n) (s : S F' n) :
    m F' n (ι (Q F' n) (conjV c n v)) (conjS c n s) = conjS c n (m F' n (ι (Q F' n) v) s) := by
  have hv : v = ∑ j, (basisV F' n).repr v j • bcV F F' n (basisV F n j) := by
    simp only [s3_bcV_basisV]; exact ((basisV F' n).sum_repr v).symm
  rw [s3_conjV_eq]
  conv_rhs => rw [hv]
  simp only [← s3_bcV_basisV F F', map_sum, map_smul, ← s3_bcC_ι, LinearMap.sum_apply,
    LinearMap.smul_apply, s3_conjS_smul, s3_m_bcC_conjS F c hc]

omit [CharZero F] in
theorem s3_conjS_bcS (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (t : S F n) : conjS c n (bcS F F' n t) = bcS F F' n t := by
  rw [s3_conjS_eq]
  simp only [s3_bcS_repr, hc]
  conv_rhs => rw [← (basisS F' n).sum_repr (bcS F F' n t)]
  simp only [s3_bcS_repr]

omit [CharZero F] in
theorem s3_conjS_ι (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (w : H1 F' n) : conjS c n (ExteriorAlgebra.ι F' w) = ExteriorAlgebra.ι F' (conjH1 c n w) := by
  have hw : ∀ w : H1 F' n, w = ∑ i, w i • e F' n i := by
    intro w
    ext j; simp [e, Pi.single_apply]
  have h1 : ExteriorAlgebra.ι F' w = ∑ i, w i • bcS F F' n (ExteriorAlgebra.ι F (e F n i)) := by
    conv_lhs => rw [hw w]
    simp only [map_sum, map_smul, s3_bcS_ι, s3_bcH1_e]
  have h2 : conjH1 c n w = ∑ i, c (w i) • e F' n i := by
    rw [hw (conjH1 c n w)]
    rfl
  rw [h1, h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s3_conjS_smul, s3_conjS_bcS F c hc, s3_bcS_ι, s3_bcH1_e, map_smul]

theorem s3_conjS_algebraMap (c : F' ≃+* F') (r : F') :
    conjS c n (algebraMap F' (S F' n) r) = algebraMap F' (S F' n) (c r) := by
  rw [Algebra.algebraMap_eq_smul_one, s3_conjS_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

omit [CharZero F] in
/-- The conjugation of coordinates preserves `S⁺`. -/
theorem s3_conjS_Splus (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (s : S F' n) (hs : s ∈ Splus F' n) : conjS c n s ∈ Splus F' n := by
  induction s, hs using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_zero, pow_zero] at hv
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hv
    rw [s3_conjS_algebraMap]
    exact CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨_, rfl⟩)
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul]
    erw [s3_conjS_ι F c hc, s3_conjS_ι F c hc]
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm F' (H1 F' n)) (conjH1 c n m₁)
        (conjH1 c n m₂)) ih
    simp only [add_zero] at h
    exact h

end S3Conj



section S3Ann

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `ann(u)` is totally isotropic when `u ≠ 0`. -/
theorem s3_Q_of_mem_ann {u : S F n} (hu : u ≠ 0) {v : V F n} (hv : v ∈ ann F n u) :
    Q F n v = 0 := by
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  have h : m F n (ι (Q F n) v * ι (Q F n) v) u = Q F n v • u := by
    rw [ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]
  rw [map_mul, Module.End.mul_apply, hv', map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hu

theorem s3_pairing_of_mem_ann {u : S F n} (hu : u ≠ 0) {v w : V F n} (hv : v ∈ ann F n u)
    (hw : w ∈ ann F n u) : pairing F n v w = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, s3_Q_of_mem_ann hu hv,
    s3_Q_of_mem_ann hu hw, s3_Q_of_mem_ann hu (Submodule.add_mem _ hv hw)]
  simp

/-- `ρ(g)(ann u) ⊆ ann(m_g u)`. -/
theorem s3_rho_mem_ann (g : Spin F n) {u : S F n} {v : V F n} (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n (m F n (g : C F n) u) := by
  show m F n (ι (Q F n) (rho F n g v)) (m F n (g : C F n) u) = 0
  have h1 : m F n (star (g : C F n)) (m F n (g : C F n) u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, spinGroup.star_mul_self_of_mem g.2, map_one,
      Module.End.one_apply]
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  rw [ι_rho, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1, hv', map_zero]

end S3Ann

theorem s3_σ_σ (z : Kd d) : Kd.σ d (Kd.σ d z) = z := by
  apply Subtype.ext; simp

theorem s3_σS_σS (s : S (Kd d) n) : σS n d (σS n d s) = s := by
  show conjS (Kd.σ d) n (conjS (Kd.σ d) n s) = s
  rw [s3_conjS_eq (n := n) (Kd.σ d) (conjS (Kd.σ d) n s)]
  conv_rhs => rw [← (basisS (Kd d) n).sum_repr s]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s3_conjS_eq, (basisS (Kd d) n).repr_sum_self, s3_σ_σ]

theorem s3_σV_σV (v : V (Kd d) n) : σV n d (σV n d v) = v := by
  show conjV (Kd.σ d) n (conjV (Kd.σ d) n v) = v
  rw [s3_conjV_eq (n := n) (Kd.σ d) (conjV (Kd.σ d) n v)]
  conv_rhs => rw [← (basisV (Kd d) n).sum_repr v]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s3_conjV_eq, (basisV (Kd d) n).repr_sum_self, s3_σ_σ]

theorem s3_conjS_repr {F' : Type*} [Field F'] [CharZero F'] (c : F' ≃+* F') (s : S F' n)
    (K : Finset (Fin (2 * n))) : (basisS F' n).repr (conjS c n s) K = c ((basisS F' n).repr s K) := by
  rw [s3_conjS_eq, (basisS F' n).repr_sum_self]

/-- `σ`-fixed elements of `K` are rational. -/
theorem s3_eq_algebraMap_of_σ_eq (hd : 0 < d) (z : Kd d) (hz : Kd.σ d z = z) :
    z = algebraMap ℚ (Kd d) (Kd.ratPart d z) := by
  have h := Kd.eq_ratPart_add_sqrtNegCoeff hd z
  have h' := congrArg (Kd.σ d) h
  rw [hz, map_add, map_mul, s3_σ_algebraMap, s3_σ_algebraMap, s3_σ_sqrtNeg] at h'
  have h2 : algebraMap ℚ (Kd d) (2 * Kd.sqrtNegCoeff d z) * Kd.sqrtNeg d = 0 := by
    rw [map_mul, map_ofNat]; linear_combination h' - h
  rcases mul_eq_zero.mp h2 with h2 | h2
  · rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h2
    have : Kd.sqrtNegCoeff d z = 0 := by linarith
    rw [this, map_zero, zero_mul, add_zero] at h
    exact h
  · exact absurd h2 (s3_sqrtNeg_ne_zero hd)

/-- `σ`-fixed spinors are rational (Galois descent). -/
theorem s3_exists_bcS_of_σS_eq (hd : 0 < d) (t : S (Kd d) n) (ht : σS n d t = t) :
    ∃ p : S ℚ n, bcS ℚ (Kd d) n p = t := by
  refine ⟨∑ K, Kd.ratPart d ((basisS (Kd d) n).repr t K) • basisS ℚ n K, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (basisS (Kd d) n).sum_repr t]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s3_bcS_basisS ℚ (Kd d), ← algebraMap_smul (Kd d)]
  congr 1
  have hK : Kd.σ d ((basisS (Kd d) n).repr t K) = (basisS (Kd d) n).repr t K := by
    have h1 : (basisS (Kd d) n).repr (σS n d t) K = Kd.σ d ((basisS (Kd d) n).repr t K) :=
      s3_conjS_repr (Kd.σ d) t K
    rw [← h1, ht]
  exact (s3_eq_algebraMap_of_σ_eq hd _ hK).symm

theorem s3_σhc (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp

namespace KSecant

variable (P : KSecant n d)

theorem s3_u₁_ne_zero : P.u₁ ≠ 0 := by
  have := P.linIndep.ne_zero 0
  simpa using this

theorem s3_u₂_ne_zero : P.u₂ ≠ 0 := by
  have := P.linIndep.ne_zero 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  exact this

theorem s3_σS_u₂ : σS n d P.u₂ = P.u₁ := s3_σS_σS P.u₁

/-- `σ(W₁) ⊆ W₂`. -/
theorem s3_σV_mem_W₂ {v : V (Kd d) n} (hv : v ∈ P.W₁) : σV n d v ∈ P.W₂ := by
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) (conjS (Kd.σ d) n P.u₁) = 0
  rw [s3_m_ι_conj ℚ (Kd.σ d) s3_σhc]
  have hv' : m (Kd d) n (ι (Q (Kd d) n) v) P.u₁ = 0 := hv
  rw [hv', map_zero]

/-- `σ(W₂) ⊆ W₁`. -/
theorem s3_σV_mem_W₁ {v : V (Kd d) n} (hv : v ∈ P.W₂) : σV n d v ∈ P.W₁ := by
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) P.u₁ = 0
  rw [← P.s3_σS_u₂]
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) (conjS (Kd.σ d) n P.u₂) = 0
  rw [s3_m_ι_conj ℚ (Kd.σ d) s3_σhc]
  have hv' : m (Kd d) n (ι (Q (Kd d) n) v) P.u₂ = 0 := hv
  rw [hv', map_zero]

/-- `u₂` is an even pure spinor. -/
theorem s3_isPure₂ (hW : IsCompl P.W₁ P.W₂) : IsEvenPureSpinor (Kd d) n P.u₂ := by
  refine ⟨s3_conjS_Splus ℚ (Kd.σ d) s3_σhc _ P.isPure.1, fun v hv => s3_Q_of_mem_ann P.s3_u₂_ne_zero hv, ?_⟩
  have h1 := Submodule.finrank_add_eq_of_isCompl hW
  have h2 : Module.finrank (Kd d) P.W₁ = 2 * n := P.isPure.2.2
  rw [h2, s3_finrank_V] at h1
  show Module.finrank (Kd d) P.W₂ = 2 * n
  omega


theorem s3_ηK_W₁ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {v : V (Kd d) n} (hv : v ∈ P.W₁) :
    P.ηK hW l v = l • v := by
  simp only [ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.coe_subtype]
  rw [Submodule.projectionOnto_apply_of_mem_left hW hv,
    Submodule.projectionOnto_apply_of_mem_right hW.symm hv]
  simp

theorem s3_ηK_W₂ (hW : IsCompl P.W₁ P.W₂) (l : Kd d) {v : V (Kd d) n} (hv : v ∈ P.W₂) :
    P.ηK hW l v = Kd.σ d l • v := by
  simp only [ηK, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.coe_subtype]
  rw [Submodule.projectionOnto_apply_of_mem_left hW.symm hv,
    Submodule.projectionOnto_apply_of_mem_right hW hv]
  simp

/-- A `K`-linear map preserving `W₁` and `W₂` commutes with `η_λ`. -/
theorem s3_ηK_comm (hW : IsCompl P.W₁ P.W₂) (T : V (Kd d) n →ₗ[Kd d] V (Kd d) n)
    (h₁ : ∀ v ∈ P.W₁, T v ∈ P.W₁) (h₂ : ∀ v ∈ P.W₂, T v ∈ P.W₂) (l : Kd d) (v : V (Kd d) n) :
    P.ηK hW l (T v) = T (P.ηK hW l v) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  calc P.ηK hW l (T (v₁ + v₂)) = P.ηK hW l (T v₁) + P.ηK hW l (T v₂) := by rw [map_add, map_add]
    _ = l • T v₁ + Kd.σ d l • T v₂ := by
      rw [P.s3_ηK_W₁ hW l (h₁ v₁ hv₁), P.s3_ηK_W₂ hW l (h₂ v₂ hv₂)]
    _ = T (l • v₁ + Kd.σ d l • v₂) := by rw [map_add, map_smul, map_smul]
    _ = T (P.ηK hW l (v₁ + v₂)) := by
      rw [map_add (P.ηK hW l), P.s3_ηK_W₁ hW l hv₁, P.s3_ηK_W₂ hW l hv₂]

/-- `η_λ` commutes with `σ` (§2.2). -/
theorem s3_σV_ηK (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V (Kd d) n) :
    σV n d (P.ηK hW l v) = P.ηK hW l (σV n d v) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  calc σV n d (P.ηK hW l (v₁ + v₂)) = σV n d (l • v₁) + σV n d (Kd.σ d l • v₂) := by
        rw [map_add, P.s3_ηK_W₁ hW l hv₁, P.s3_ηK_W₂ hW l hv₂, map_add]
    _ = Kd.σ d l • σV n d v₁ + l • σV n d v₂ := by
        show conjV (Kd.σ d) n (l • v₁) + conjV (Kd.σ d) n (Kd.σ d l • v₂) =
          Kd.σ d l • conjV (Kd.σ d) n v₁ + l • conjV (Kd.σ d) n v₂
        rw [s3_conjV_smul, s3_conjV_smul, s3_σ_σ]
    _ = P.ηK hW l (σV n d (v₁ + v₂)) := by
        rw [map_add, map_add, P.s3_ηK_W₂ hW l (P.s3_σV_mem_W₂ hv₁),
          P.s3_ηK_W₁ hW l (P.s3_σV_mem_W₁ hv₂)]

/-- `η_λ` on `V_K` extends `η_λ` on `V_ℚ`. -/
theorem s3_ηK_bcV (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (v : V ℚ n) :
    P.ηK hW l (bcV ℚ (Kd d) n v) = bcV ℚ (Kd d) n (P.η hW l v) :=
  (bcV_descend n d (P.ηK hW l) (P.s3_σV_ηK hW l) v).symm

/-- The `K`-linear extension of `f` is `η_{√-d}` on `V_K`. -/
theorem s3_ext_fη (hW : IsCompl P.W₁ P.W₂) :
    s3_ext ℚ (Kd d) n (P.fη hW) = P.ηK hW (Kd.sqrtNeg d) := by
  refine (basisV (Kd d) n).ext fun i => ?_
  rw [← s3_bcV_basisV ℚ (Kd d), s3_ext_bcV, P.s3_ηK_bcV]
  rfl


theorem s3_mem_Pℚ_iff (p : S ℚ n) : p ∈ P.Pℚ ↔ bcS ℚ (Kd d) n p ∈ P.PK := by
  simp [Pℚ]

/-- The rational points `p₁ = u₁ + u₂`, `p₂ = √-d (u₁ - u₂)` of `P_K` (`P_K` is defined over `ℚ`). -/
theorem s3_exists_Pℚ : ∃ p₁ p₂ : S ℚ n, p₁ ∈ P.Pℚ ∧ p₂ ∈ P.Pℚ ∧
    bcS ℚ (Kd d) n p₁ = P.u₁ + P.u₂ ∧ bcS ℚ (Kd d) n p₂ = Kd.sqrtNeg d • (P.u₁ - P.u₂) := by
  have hd := s3_d_pos P
  obtain ⟨p₁, hp₁⟩ := s3_exists_bcS_of_σS_eq hd (P.u₁ + P.u₂) (by
    rw [map_add, P.s3_σS_u₂, add_comm]; rfl)
  obtain ⟨p₂, hp₂⟩ := s3_exists_bcS_of_σS_eq hd (Kd.sqrtNeg d • (P.u₁ - P.u₂)) (by
    show conjS (Kd.σ d) n (Kd.sqrtNeg d • (P.u₁ - P.u₂)) = _
    rw [s3_conjS_smul, s3_σ_sqrtNeg, map_sub]
    show -Kd.sqrtNeg d • (σS n d P.u₁ - σS n d P.u₂) = _
    rw [P.s3_σS_u₂]
    show -Kd.sqrtNeg d • (P.u₂ - P.u₁) = _
    rw [neg_smul, ← smul_neg, neg_sub])
  have hu₁ : P.u₁ ∈ P.PK := Submodule.subset_span (Set.mem_insert _ _)
  have hu₂ : P.u₂ ∈ P.PK := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  refine ⟨p₁, p₂, ?_, ?_, hp₁, hp₂⟩
  · rw [s3_mem_Pℚ_iff, hp₁]; exact Submodule.add_mem _ hu₁ hu₂
  · rw [s3_mem_Pℚ_iff, hp₂]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu₁ hu₂)


end KSecant

/-- A rational `K`-secant needs `n > 0` (`S_K` has dimension `2^{2n}`). -/
theorem s3_n_pos (P : KSecant n d) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have : Module.Finite (Kd d) (S (Kd d) 0) := Module.Finite.of_basis (basisS (Kd d) 0)
  have h := P.linIndep.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis (basisS (Kd d) 0)] at h
  simp at h

/-- The pairing of `V_F` is nondegenerate (as a quadratic form). -/
theorem s3_Q_nondegenerate {F : Type*} [Field F] [CharZero F] : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

theorem s3_nontrivial_V {F : Type*} [Field F] (hn : 0 < n) : Nontrivial (V F n) :=
  ⟨⟨(0, 0), (0, e F n ⟨0, by omega⟩), by
    intro h
    have := congrFun (congrArg Prod.snd h) ⟨0, by omega⟩
    simp [e] at this⟩⟩

/-- Two spin elements with the same image under `ρ` differ by a sign. -/
theorem s3_eq_or_eq_neg_of_rho_eq {F : Type*} [Field F] [CharZero F] (hn : 0 < n)
    (a b : Spin F n) (h : rho F n a = rho F n b) :
    (a : C F n) = b ∨ (a : C F n) = -b := by
  have := s3_nontrivial_V (F := F) hn
  have h' : spinToSpecialOrthogonal (Q F n) a = spinToSpecialOrthogonal (Q F n) b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply]
    exact LinearEquiv.congr_fun h v
  rcases eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq (Q F n) s3_Q_nondegenerate a b h' with
    h1 | h1
  · left; rw [h1]
  · right; rw [h1]; simp


/-- `ρ(-g) = ρ(g)`. -/
private theorem s3_rho_negOne_mul {F : Type*} [Field F] [CharZero F] (hQ0 : Q F n ≠ 0) (s : Spin F n) :
    rho F n (spinGroup.negOne (Q F n) hQ0 * s) = rho F n s := by
  have h1 : rho F n (spinGroup.negOne (Q F n) hQ0) = 1 := by
    apply LinearEquiv.ext
    intro v
    have := congrArg
      (fun g : TauCeti.QuadraticMap.orthogonalGroup (Q F n) => (g : V F n ≃ₗ[F] V F n) v)
      (spinGroup.spinToOrthogonal_negOne (Q F n) hQ0)
    simp only [coe_spinToOrthogonal_apply] at this
    exact this
  simp only [rho, spinVectorAction_mul] at h1 ⊢
  rw [h1, one_mul]

section S3Trans

variable (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
  [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F''] {n : ℕ}

omit [CharZero F] [CharZero F'] [CharZero F''] in
theorem s3_bcH1_trans (w : H1 F n) :
    bcH1 F' F'' n (bcH1 F F' n w) = bcH1 F F'' n w := by
  ext i
  simp [bcH1, ← IsScalarTower.algebraMap_apply]

theorem s3_bcDual_trans (θ : Module.Dual F (H1 F n)) :
    bcDual F' F'' n (bcDual F F' n θ) = bcDual F F'' n θ := by
  show (∑ i, algebraMap F' F'' ((bcDual F F' n θ) (e F' n i)) • f F'' n i) =
    ∑ i, algebraMap F F'' (θ (e F n i)) • f F'' n i
  simp only [s3_bcDual_apply_e, ← IsScalarTower.algebraMap_apply]

theorem s3_bcV_trans (v : V F n) : bcV F' F'' n (bcV F F' n v) = bcV F F'' n v := by
  simp only [bcV, LinearMap.prodMap_apply, s3_bcDual_trans, s3_bcH1_trans]

omit [CharZero F] [CharZero F'] [CharZero F''] in
theorem s3_bcS_trans (s : S F n) : bcS F' F'' n (bcS F F' n s) = bcS F F'' n s := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι w =>
    rw [show (ι (0 : QuadraticForm F (H1 F n)) w : S F n) = ExteriorAlgebra.ι F w from rfl,
      s3_bcS_ι, s3_bcS_ι, s3_bcS_ι, s3_bcH1_trans]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

omit [CharZero F] [CharZero F'] [CharZero F''] in
theorem s3_ext_trans (A : V F n →ₗ[F] V F n) :
    s3_ext F' F'' n (s3_ext F F' n A) = s3_ext F F'' n A := by
  simp only [s3_ext, LinearMap.toMatrix_toLin, Matrix.map_map]
  congr 2
  ext x
  exact (IsScalarTower.algebraMap_apply F F' F'' x).symm

end S3Trans

section S3Even

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
/-- Change of coefficients preserves `S⁺`. -/
theorem s3_bcS_Splus (s : S F n) (hs : s ∈ Splus F n) : bcS F F' n s ∈ Splus F' n := by
  induction s, hs using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_zero, pow_zero] at hv
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hv
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n)]
    exact CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨_, rfl⟩)
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul]
    erw [s3_bcS_ι F F', s3_bcS_ι F F']
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm F' (H1 F' n)) (bcH1 F F' n m₁)
        (bcH1 F F' n m₂)) ih
    simp only [add_zero] at h
    exact h

end S3Even


namespace KSecant

variable (P : KSecant n d)

/-- `f_ℂ = η_{√-d}` extended to `V_ℂ`. -/
theorem s3_fℂ_eq (hW : IsCompl P.W₁ P.W₂) :
    complexifyV n (P.fR hW) = s3_ext (Kd d) ℂ n (P.ηK hW (Kd.sqrtNeg d)) := by
  rw [s3_complexifyV_eq, fR, s3_bcEndV_eq, s3_ext_trans ℚ ℝ ℂ, ← s3_ext_trans ℚ (Kd d) ℂ,
    P.s3_ext_fη hW]

theorem s3_fℂ_bcV₁ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₁) :
    complexifyV n (P.fR hW) (bcV (Kd d) ℂ n w) = (Kd.sqrtNeg d : ℂ) • bcV (Kd d) ℂ n w := by
  rw [P.s3_fℂ_eq hW, s3_ext_bcV, P.s3_ηK_W₁ hW _ hw, map_smul]
  rfl

theorem s3_fℂ_bcV₂ (hW : IsCompl P.W₁ P.W₂) {w : V (Kd d) n} (hw : w ∈ P.W₂) :
    complexifyV n (P.fR hW) (bcV (Kd d) ℂ n w) = -(Kd.sqrtNeg d : ℂ) • bcV (Kd d) ℂ n w := by
  rw [P.s3_fℂ_eq hW, s3_ext_bcV, P.s3_ηK_W₂ hW _ hw, map_smul, s3_σ_sqrtNeg]
  rfl

/-- `f_ℂ` acts on `W_{1,ℂ}` by `√-d`. -/
theorem s3_fℂ_W₁ (hW : IsCompl P.W₁ P.W₂) {x : V ℂ n} (hx : x ∈ P.W₁ℂ) :
    complexifyV n (P.fR hW) x = (Kd.sqrtNeg d : ℂ) • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact P.s3_fℂ_bcV₁ hW hw
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul c y _ hy => rw [map_smul, hy, smul_comm]

/-- `f_ℂ` acts on `W_{2,ℂ}` by `-√-d`. -/
theorem s3_fℂ_W₂ (hW : IsCompl P.W₁ P.W₂) {x : V ℂ n} (hx : x ∈ P.W₂ℂ) :
    complexifyV n (P.fR hW) x = -(Kd.sqrtNeg d : ℂ) • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact P.s3_fℂ_bcV₂ hW hw
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul c y _ hy => rw [map_smul, hy, smul_comm]

theorem s3_sup_ℂ (hW : IsCompl P.W₁ P.W₂) : P.W₁ℂ ⊔ P.W₂ℂ = ⊤ := by
  rw [eq_top_iff, ← (basisV ℂ n).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← s3_bcV_basisV (Kd d) ℂ]
  obtain ⟨v₁, hv₁, v₂, hv₂, h⟩ :=
    Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := basisV (Kd d) n i))
  rw [← h, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨v₁, hv₁, rfl⟩)
    (Submodule.subset_span ⟨v₂, hv₂, rfl⟩)

theorem s3_isCompl_ℂ (hW : IsCompl P.W₁ P.W₂) : IsCompl P.W₁ℂ P.W₂ℂ := by
  refine ⟨?_, codisjoint_iff.mpr (P.s3_sup_ℂ hW)⟩
  rw [Submodule.disjoint_def]
  intro x hx₁ hx₂
  have h := (P.s3_fℂ_W₁ hW hx₁).symm.trans (P.s3_fℂ_W₂ hW hx₂)
  have hs : (Kd.sqrtNeg d : ℂ) ≠ 0 := by
    exact_mod_cast s3_sqrtNeg_ne_zero (s3_d_pos P)
  have : (2 * (Kd.sqrtNeg d : ℂ)) • x = 0 := by
    have e : (2 * (Kd.sqrtNeg d : ℂ)) • x = (Kd.sqrtNeg d : ℂ) • x - (-(Kd.sqrtNeg d : ℂ)) • x := by
      module
    rw [e, h, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs)

theorem s3_W₁ℂ_le_ann : P.W₁ℂ ≤ ann ℂ n (bcS (Kd d) ℂ n P.u₁) := by
  rw [W₁ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  show m ℂ n (ι (Q ℂ n) (bcV (Kd d) ℂ n w)) (bcS (Kd d) ℂ n P.u₁) = 0
  rw [← s3_bcC_ι, s3_m_bcC]
  have hw' : m (Kd d) n (ι (Q (Kd d) n) w) P.u₁ = 0 := hw
  rw [hw', map_zero]

theorem s3_W₂ℂ_le_ann : P.W₂ℂ ≤ ann ℂ n (bcS (Kd d) ℂ n P.u₂) := by
  rw [W₂ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  show m ℂ n (ι (Q ℂ n) (bcV (Kd d) ℂ n w)) (bcS (Kd d) ℂ n P.u₂) = 0
  rw [← s3_bcC_ι, s3_m_bcC]
  have hw' : m (Kd d) n (ι (Q (Kd d) n) w) P.u₂ = 0 := hw
  rw [hw', map_zero]

theorem s3_bcS_u₁_ne_zero : bcS (Kd d) ℂ n P.u₁ ≠ 0 := fun h =>
  P.s3_u₁_ne_zero ((s3_bcS_injective (Kd d) ℂ) (h.trans (map_zero _).symm))

theorem s3_bcS_u₂_ne_zero : bcS (Kd d) ℂ n P.u₂ ≠ 0 := fun h =>
  P.s3_u₂_ne_zero ((s3_bcS_injective (Kd d) ℂ) (h.trans (map_zero _).symm))

/-- `W_{1,ℂ} = ann(u_{1,ℂ})`. -/
theorem s3_W₁ℂ_eq_ann (hW : IsCompl P.W₁ P.W₂) : P.W₁ℂ = ann ℂ n (bcS (Kd d) ℂ n P.u₁) := by
  refine le_antisymm P.s3_W₁ℂ_le_ann fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
  have hb' : b ∈ ann ℂ n (bcS (Kd d) ℂ n P.u₁) := by
    have := Submodule.sub_mem _ hx (P.s3_W₁ℂ_le_ann ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := by
    apply s3_pairing_sepLeft
    intro y
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ :=
      Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := y))
    rw [map_add, s3_pairing_of_mem_ann P.s3_bcS_u₁_ne_zero hb' (P.s3_W₁ℂ_le_ann hy₁),
      s3_pairing_of_mem_ann P.s3_bcS_u₂_ne_zero (P.s3_W₂ℂ_le_ann hb) (P.s3_W₂ℂ_le_ann hy₂),
      add_zero]
  rw [hb0, add_zero]; exact ha


/-- `W_{2,ℂ} = ann(u_{2,ℂ})`. -/
theorem s3_W₂ℂ_eq_ann (hW : IsCompl P.W₁ P.W₂) : P.W₂ℂ = ann ℂ n (bcS (Kd d) ℂ n P.u₂) := by
  refine le_antisymm P.s3_W₂ℂ_le_ann fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
  have ha' : a ∈ ann ℂ n (bcS (Kd d) ℂ n P.u₂) := by
    have := Submodule.sub_mem _ hx (P.s3_W₂ℂ_le_ann hb)
    rwa [add_sub_cancel_right] at this
  have ha0 : a = 0 := by
    apply s3_pairing_sepLeft
    intro y
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ :=
      Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := y))
    rw [map_add, s3_pairing_of_mem_ann P.s3_bcS_u₁_ne_zero (P.s3_W₁ℂ_le_ann ha)
      (P.s3_W₁ℂ_le_ann hy₁),
      s3_pairing_of_mem_ann P.s3_bcS_u₂_ne_zero ha' (P.s3_W₂ℂ_le_ann hy₂), add_zero]
  rw [ha0, zero_add]; exact hb

/-- An isotropic subspace of `V_ℂ` has dimension at most `2n`. -/
theorem _root_.WeilClasses.s3_finrank_le_of_isotropic {W : Submodule ℂ (V ℂ n)}
    (hW : ∀ a ∈ W, ∀ b ∈ W, pairing ℂ n a b = 0) : 2 * Module.finrank ℂ W ≤ 4 * n := by
  have hle : W ≤ (pairing ℂ n).orthogonal W := fun x hx y hy => hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal s3_pairing_nondegenerate, s3_finrank_V] at h1
  omega

theorem s3_finrank_W₁ℂ (hW : IsCompl P.W₁ P.W₂) : Module.finrank ℂ P.W₁ℂ = 2 * n := by
  have h1 := s3_finrank_le_of_isotropic (W := P.W₁ℂ) fun a ha b hb =>
    s3_pairing_of_mem_ann P.s3_bcS_u₁_ne_zero (P.s3_W₁ℂ_le_ann ha) (P.s3_W₁ℂ_le_ann hb)
  have h2 := s3_finrank_le_of_isotropic (W := P.W₂ℂ) fun a ha b hb =>
    s3_pairing_of_mem_ann P.s3_bcS_u₂_ne_zero (P.s3_W₂ℂ_le_ann ha) (P.s3_W₂ℂ_le_ann hb)
  have h3 := Submodule.finrank_add_eq_of_isCompl (P.s3_isCompl_ℂ hW)
  rw [s3_finrank_V] at h3
  omega

theorem s3_finrank_W₂ℂ (hW : IsCompl P.W₁ P.W₂) : Module.finrank ℂ P.W₂ℂ = 2 * n := by
  have h1 := P.s3_finrank_W₁ℂ hW
  have h3 := Submodule.finrank_add_eq_of_isCompl (P.s3_isCompl_ℂ hW)
  rw [s3_finrank_V] at h3
  omega

theorem s3_isPure₁ℂ (hW : IsCompl P.W₁ P.W₂) : IsEvenPureSpinor ℂ n (bcS (Kd d) ℂ n P.u₁) :=
  ⟨s3_bcS_Splus (Kd d) ℂ _ P.isPure.1, fun _ hv => s3_Q_of_mem_ann P.s3_bcS_u₁_ne_zero hv,
    by rw [← P.s3_W₁ℂ_eq_ann hW]; exact P.s3_finrank_W₁ℂ hW⟩

theorem s3_isPure₂ℂ (hW : IsCompl P.W₁ P.W₂) : IsEvenPureSpinor ℂ n (bcS (Kd d) ℂ n P.u₂) :=
  ⟨s3_bcS_Splus (Kd d) ℂ _ (P.s3_isPure₂ hW).1, fun _ hv => s3_Q_of_mem_ann P.s3_bcS_u₂_ne_zero hv,
    by rw [← P.s3_W₂ℂ_eq_ann hW]; exact P.s3_finrank_W₂ℂ hW⟩

/-- Complex conjugation of `S_ℂ` restricts to `σ` on `S_K`. -/
theorem _root_.WeilClasses.s3_conj_bcS_σ (t : S (Kd d) n) :
    conjS (starRingAut : ℂ ≃+* ℂ) n (bcS (Kd d) ℂ n t) = bcS (Kd d) ℂ n (σS n d t) := by
  apply (basisS ℂ n).repr.injective
  ext K
  rw [s3_conjS_repr, s3_bcS_repr, s3_bcS_repr]
  show (starRingEnd ℂ) ((basisS (Kd d) n).repr t K : ℂ) = (((basisS (Kd d) n).repr (σS n d t) K : Kd d) : ℂ)
  rw [show (basisS (Kd d) n).repr (σS n d t) K = Kd.σ d ((basisS (Kd d) n).repr t K) from
    s3_conjS_repr (Kd.σ d) t K, Kd.coe_σ]

theorem s3_conj_u₁ℂ :
    conjS (starRingAut : ℂ ≃+* ℂ) n (bcS (Kd d) ℂ n P.u₁) = bcS (Kd d) ℂ n P.u₂ :=
  s3_conj_bcS_σ P.u₁

end KSecant


theorem s3_complexifyV_injective {A B : Module.End ℝ (V ℝ n)}
    (h : complexifyV n A = complexifyV n B) : A = B := by
  apply LinearMap.ext
  intro v
  apply s3_bcV_injective ℝ ℂ
  rw [← s3_ext_bcV, ← s3_ext_bcV]
  exact LinearMap.congr_fun h _

theorem s3_conj_hc (r : ℝ) :
    (starRingAut : ℂ ≃+* ℂ) (algebraMap ℝ ℂ r) = algebraMap ℝ ℂ r := by
  simp

/-- **Lemma 3.1.1** (`lemma-stabilizer-is-isomorphic-to-so-f`). The stabilizer `Spin(V_ℚ)_P` is
mapped by `ρ` isomorphically onto `SO_+(V_ℚ)_f`: `ρ` is injective on `Spin(V_ℚ)_P` and its image
is `SO_+(V_ℚ)_f`. Standing assumption: Assumption 2.4.1. -/
theorem lemma3_1_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    Set.InjOn (rho ℚ n) (P.spinPℚ : Set (Spin ℚ n)) ∧
      rho ℚ n '' (P.spinPℚ : Set (Spin ℚ n)) = (P.SOplusf hP.isCompl : Set (V ℚ n ≃ₗ[ℚ] V ℚ n)) := by
  have hW := hP.isCompl
  have hd := s3_d_pos P
  have hn := s3_n_pos P
  obtain ⟨p₁, p₂, hp₁, hp₂, hbc₁, hbc₂⟩ := P.s3_exists_Pℚ
  have hs0 : Kd.sqrtNeg d ≠ 0 := s3_sqrtNeg_ne_zero hd
  have h2 : (2 : Kd d) ≠ 0 := two_ne_zero
  have hu₁ : P.u₁ = (2 : Kd d)⁻¹ • (bcS ℚ (Kd d) n p₁ + (Kd.sqrtNeg d)⁻¹ • bcS ℚ (Kd d) n p₂) := by
    rw [hbc₁, hbc₂, smul_smul, inv_mul_cancel₀ hs0, one_smul, add_add_sub_cancel, ← two_smul (Kd d),
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hu₂ : P.u₂ = (2 : Kd d)⁻¹ • (bcS ℚ (Kd d) n p₁ - (Kd.sqrtNeg d)⁻¹ • bcS ℚ (Kd d) n p₂) := by
    rw [hbc₁, hbc₂, smul_smul, inv_mul_cancel₀ hs0, one_smul, add_sub_sub_cancel,
      ← two_smul (Kd d), smul_smul, inv_mul_cancel₀ h2, one_smul]
  -- the elements of `Spin(V_ℚ)_P` fix `u₁` and `u₂`
  have hfix : ∀ s : Spin ℚ n, s ∈ P.spinPℚ →
      m (Kd d) n (bcC ℚ (Kd d) n s) P.u₁ = P.u₁ ∧ m (Kd d) n (bcC ℚ (Kd d) n s) P.u₂ = P.u₂ := by
    intro s hs
    have h₁ : m (Kd d) n (bcC ℚ (Kd d) n s) (bcS ℚ (Kd d) n p₁) = bcS ℚ (Kd d) n p₁ := by
      rw [s3_m_bcC, hs p₁ hp₁]
    have h₂ : m (Kd d) n (bcC ℚ (Kd d) n s) (bcS ℚ (Kd d) n p₂) = bcS ℚ (Kd d) n p₂ := by
      rw [s3_m_bcC, hs p₂ hp₂]
    constructor
    · conv_lhs => rw [hu₁]
      rw [map_smul, map_add, map_smul, h₁, h₂, ← hu₁]
    · conv_lhs => rw [hu₂]
      rw [map_smul, map_sub, map_smul, h₁, h₂, ← hu₂]
  -- an element fixing `u₁` and `u₂` fixes `P`
  have hfix' : ∀ s : Spin ℚ n, m (Kd d) n (bcC ℚ (Kd d) n s) P.u₁ = P.u₁ →
      m (Kd d) n (bcC ℚ (Kd d) n s) P.u₂ = P.u₂ → s ∈ P.spinPℚ := by
    intro s h₁ h₂ p hp
    apply s3_bcS_injective ℚ (Kd d)
    rw [← s3_m_bcC]
    have hpK : bcS ℚ (Kd d) n p ∈ P.PK := (P.s3_mem_Pℚ_iff p).mp hp
    have := LinearMap.eqOn_span' (f := m (Kd d) n (bcC ℚ (Kd d) n s)) (g := LinearMap.id)
      (s := {P.u₁, P.u₂}) (by
        rintro x (rfl | rfl)
        · exact h₁
        · exact h₂) hpK
    exact this
  have hu₁₂ : P.u₁ + P.u₂ ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.mp P.linIndep) 1 1 (by
      rw [one_smul, one_smul]; exact h)
    exact one_ne_zero this.1
  refine ⟨?_, ?_⟩
  · -- `ρ` is injective on `Spin(V_ℚ)_P`: its kernel is `±1`, and `-1` acts by `-1` on `S`
    intro a ha b hb hab
    rcases s3_eq_or_eq_neg_of_rho_eq hn a b hab with h | h
    · exact Subtype.ext h
    · exfalso
      have h1 : m ℚ n (a : C ℚ n) p₁ = p₁ := ha p₁ hp₁
      rw [h, map_neg, LinearMap.neg_apply, hb p₁ hp₁, neg_eq_iff_add_eq_zero, ← two_smul ℚ,
        smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact two_ne_zero h1
      · rw [h1, map_zero] at hbc₁
        exact hu₁₂ hbc₁.symm
  · -- the image is `SO_+(V_ℚ)_f`
    have hext : ∀ s : Spin ℚ n, bcEndV (Kd d) n (rho ℚ n s : V ℚ n →ₗ[ℚ] V ℚ n) =
        (rho (Kd d) n (bcSpin ℚ (Kd d) n s) : V (Kd d) n →ₗ[Kd d] V (Kd d) n) :=
      fun s => s3_ext_rho ℚ (Kd d) s
    -- `ρ(s_K)` preserves `Wᵢ = ann uᵢ` when `s_K` fixes the line of `uᵢ`
    have hpres : ∀ (s : Spin ℚ n) (u : S (Kd d) n) (c : Kd d), c ≠ 0 →
        m (Kd d) n (bcC ℚ (Kd d) n s) u = c • u →
        ∀ v ∈ ann (Kd d) n u, rho (Kd d) n (bcSpin ℚ (Kd d) n s) v ∈ ann (Kd d) n u := by
      intro s u c hc hsu v hv
      have := s3_rho_mem_ann (bcSpin ℚ (Kd d) n s) hv
      have hm : m (Kd d) n ((bcSpin ℚ (Kd d) n s : Spin (Kd d) n) : C (Kd d) n) u = c • u := hsu
      rw [hm] at this
      have hann : ann (Kd d) n (c • u) = ann (Kd d) n u := by
        ext w
        show m (Kd d) n (ι (Q (Kd d) n) w) (c • u) = 0 ↔ m (Kd d) n (ι (Q (Kd d) n) w) u = 0
        rw [map_smul, smul_eq_zero]
        simp [hc]
      rwa [hann] at this
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨h₁, h₂⟩ := hfix s hs
      have hT₁ := hpres s P.u₁ 1 one_ne_zero (by rw [h₁, one_smul])
      have hT₂ := hpres s P.u₂ 1 one_ne_zero (by rw [h₂, one_smul])
      -- `ρ(s)` commutes with `f`
      have hcomm : ∀ x, rho ℚ n s (P.fη hW x) = P.fη hW (rho ℚ n s x) := by
        intro x
        apply s3_bcV_injective ℚ (Kd d)
        show bcV ℚ (Kd d) n (rho ℚ n s (P.η hW (Kd.sqrtNeg d) x)) =
          bcV ℚ (Kd d) n (P.η hW (Kd.sqrtNeg d) (rho ℚ n s x))
        have hc := P.s3_ηK_comm hW (rho (Kd d) n (bcSpin ℚ (Kd d) n s) : V (Kd d) n →ₗ[Kd d] V (Kd d) n)
          hT₁ hT₂ (Kd.sqrtNeg d) (bcV ℚ (Kd d) n x)
        simp only [LinearEquiv.coe_coe] at hc
        rw [← s3_rho_bcV, ← P.s3_ηK_bcV, ← hc, s3_rho_bcV, P.s3_ηK_bcV]
      -- `det(ρ(s)|_{Wᵢ}) = 1`, by [Chevalley, III.3.2, III.4.5]
      have hdet : ∀ (u : S (Kd d) n) (hu : IsEvenPureSpinor (Kd d) n u), u ≠ 0 →
          m (Kd d) n (bcC ℚ (Kd d) n s) u = u →
          ∀ hT : ∀ v ∈ ann (Kd d) n u, rho (Kd d) n (bcSpin ℚ (Kd d) n s) v ∈ ann (Kd d) n u,
          s3_DetOne (bcEndV (Kd d) n (rho ℚ n s : V ℚ n →ₗ[ℚ] V ℚ n)) (ann (Kd d) n u) := by
        intro u hu hu0 hsu hT
        obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 (Kd d) n u hu (bcSpin ℚ (Kd d) n s) hT
        have hc1 : c = 1 := by
          have hsu' : m (Kd d) n (bcC ℚ (Kd d) n s) u = c • u := hc
          rw [hsu] at hsu'
          have : (c - 1) • u = 0 := by rw [sub_smul, ← hsu', one_smul, sub_self]
          exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)
        rw [hc1, one_pow] at hc2
        exact s3_DetOne_congr (hext s).symm ⟨hT, hc2.symm⟩
      exact ⟨(mem_SOplus_iff ℚ n _).mpr ⟨s, rfl⟩, hcomm, hdet P.u₁ P.isPure P.s3_u₁_ne_zero h₁ hT₁,
        hdet P.u₂ (P.s3_isPure₂ hW) P.s3_u₂_ne_zero h₂ hT₂⟩
    · rintro ⟨hg1, hg2, hg3, hg4⟩
      obtain ⟨s, rfl⟩ := (mem_SOplus_iff ℚ n g).mp hg1
      obtain ⟨hT₁, hdet₁⟩ := s3_DetOne_congr (hext s) hg3
      obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 (Kd d) n P.u₁ P.isPure
        (bcSpin ℚ (Kd d) n s) hT₁
      have hc' : m (Kd d) n (bcC ℚ (Kd d) n s) P.u₁ = c • P.u₁ := hc
      replace hc2 : c ^ 2 = 1 := hc2.trans hdet₁
      -- `s` acts on `u₂ = σ(u₁)` by `σ(c)`
      have hc₂ : m (Kd d) n (bcC ℚ (Kd d) n s) P.u₂ = Kd.σ d c • P.u₂ := by
        show m (Kd d) n (bcC ℚ (Kd d) n s) (conjS (Kd.σ d) n P.u₁) =
          Kd.σ d c • conjS (Kd.σ d) n P.u₁
        rw [s3_m_bcC_conjS ℚ (Kd.σ d) s3_σhc, hc', s3_conjS_smul]
      have hc1 : c = 1 ∨ c = -1 := by
        have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp this with h | h
        · left; exact sub_eq_zero.mp h
        · right; exact eq_neg_of_add_eq_zero_left h
      rcases hc1 with rfl | rfl
      · refine ⟨s, hfix' s (by rw [hc', one_smul]) (by rw [hc₂, map_one, one_smul]), rfl⟩
      · have hQ0 : Q ℚ n ≠ 0 := by
          have := s3_nontrivial_V (F := ℚ) hn
          exact s3_Q_nondegenerate.ne_zero
        refine ⟨spinGroup.negOne (Q ℚ n) hQ0 * s, hfix' _ ?_ ?_, s3_rho_negOne_mul hQ0 s⟩
        · rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, map_neg, map_neg,
            LinearMap.neg_apply, hc', neg_one_smul, neg_neg]
        · rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, map_neg, map_neg,
            LinearMap.neg_apply, hc₂, map_neg, map_one, neg_one_smul, neg_neg]


/-- Lemma 3.1.1 over `ℝ`, as cited at the beginning of §4 (TeX line 1713): `ρ` maps `Spin(V_ℝ)_P`
isomorphically onto `SO_+(V_ℝ)_f`. -/
theorem lemma3_1_1_real (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    Set.InjOn (rho ℝ n) (P.spinPR : Set (Spin ℝ n)) ∧
      rho ℝ n '' (P.spinPR : Set (Spin ℝ n)) = (P.SOplusfR hP.isCompl : Set (V ℝ n ≃ₗ[ℝ] V ℝ n)) := by
  have hW := hP.isCompl
  have hd := s3_d_pos P
  have hn := s3_n_pos P
  obtain ⟨p₁, p₂, hp₁, hp₂, hbc₁, hbc₂⟩ := P.s3_exists_Pℚ
  have hs0 : Kd.sqrtNeg d ≠ 0 := s3_sqrtNeg_ne_zero hd
  have hs0' : ((Kd.sqrtNeg d : Kd d) : ℂ) ≠ 0 := by exact_mod_cast hs0
  set u₁c := bcS (Kd d) ℂ n P.u₁ with hu₁c
  set u₂c := bcS (Kd d) ℂ n P.u₂ with hu₂c
  -- the real points `qᵢ = pᵢ ⊗ ℝ` of `P`
  set q₁ := bcS ℚ ℝ n p₁
  set q₂ := bcS ℚ ℝ n p₂
  have hq₁ : bcS ℝ ℂ n q₁ = u₁c + u₂c := by
    rw [s3_bcS_trans ℚ ℝ ℂ, ← s3_bcS_trans ℚ (Kd d) ℂ, hbc₁, map_add]
  have hq₂ : bcS ℝ ℂ n q₂ = ((Kd.sqrtNeg d : Kd d) : ℂ) • (u₁c - u₂c) := by
    rw [s3_bcS_trans ℚ ℝ ℂ, ← s3_bcS_trans ℚ (Kd d) ℂ, hbc₂, map_smul, map_sub]
    rfl
  have hq₁P : q₁ ∈ P.PR := Submodule.subset_span ⟨p₁, hp₁, rfl⟩
  have hq₂P : q₂ ∈ P.PR := Submodule.subset_span ⟨p₂, hp₂, rfl⟩
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hu₁ : u₁c = (2 : ℂ)⁻¹ • (bcS ℝ ℂ n q₁ + (((Kd.sqrtNeg d : Kd d) : ℂ))⁻¹ • bcS ℝ ℂ n q₂) := by
    rw [hq₁, hq₂, smul_smul, inv_mul_cancel₀ hs0', one_smul, add_add_sub_cancel, ← two_smul ℂ,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hu₂ : u₂c = (2 : ℂ)⁻¹ • (bcS ℝ ℂ n q₁ - (((Kd.sqrtNeg d : Kd d) : ℂ))⁻¹ • bcS ℝ ℂ n q₂) := by
    rw [hq₁, hq₂, smul_smul, inv_mul_cancel₀ hs0', one_smul, add_sub_sub_cancel,
      ← two_smul ℂ, smul_smul, inv_mul_cancel₀ h2, one_smul]
  -- elements of `Spin(V_ℝ)_P` fix `u_{1,ℂ}` and `u_{2,ℂ}`
  have hfix : ∀ s : Spin ℝ n, s ∈ P.spinPR →
      m ℂ n (bcC ℝ ℂ n s) u₁c = u₁c ∧ m ℂ n (bcC ℝ ℂ n s) u₂c = u₂c := by
    intro s hs
    have h₁ : m ℂ n (bcC ℝ ℂ n s) (bcS ℝ ℂ n q₁) = bcS ℝ ℂ n q₁ := by
      rw [s3_m_bcC, hs q₁ hq₁P]
    have h₂ : m ℂ n (bcC ℝ ℂ n s) (bcS ℝ ℂ n q₂) = bcS ℝ ℂ n q₂ := by
      rw [s3_m_bcC, hs q₂ hq₂P]
    constructor
    · conv_lhs => rw [hu₁]
      rw [map_smul, map_add, map_smul, h₁, h₂, ← hu₁]
    · conv_lhs => rw [hu₂]
      rw [map_smul, map_sub, map_smul, h₁, h₂, ← hu₂]
  -- an element fixing `u_{1,ℂ}`, `u_{2,ℂ}` fixes `P_ℝ`
  have hfix' : ∀ s : Spin ℝ n, m ℂ n (bcC ℝ ℂ n s) u₁c = u₁c →
      m ℂ n (bcC ℝ ℂ n s) u₂c = u₂c → s ∈ P.spinPR := by
    intro s h₁ h₂
    have hspan : ∀ y ∈ P.PK, m ℂ n (bcC ℝ ℂ n s) (bcS (Kd d) ℂ n y) = bcS (Kd d) ℂ n y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        rcases hz with rfl | rfl
        · exact h₁
        · exact h₂
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
      | smul c a _ ha =>
        rw [map_smul, ← algebraMap_smul ℂ c, map_smul, ha]
    intro p hp
    have := LinearMap.eqOn_span' (f := m ℝ n (s : C ℝ n)) (g := LinearMap.id)
      (s := bcS ℚ ℝ n '' P.Pℚ) (by
        rintro _ ⟨q, hq, rfl⟩
        apply s3_bcS_injective ℝ ℂ
        rw [← s3_m_bcC, s3_bcS_trans ℚ ℝ ℂ, ← s3_bcS_trans ℚ (Kd d) ℂ,
          hspan _ ((P.s3_mem_Pℚ_iff q).mp hq), LinearMap.id_apply, s3_bcS_trans ℚ ℝ ℂ,
          s3_bcS_trans ℚ (Kd d) ℂ]) hp
    exact this
  have hu₁₂ : P.u₁ + P.u₂ ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.mp P.linIndep) 1 1 (by
      rw [one_smul, one_smul]; exact h)
    exact one_ne_zero this.1
  have hq₁0 : q₁ ≠ 0 := by
    intro h
    have : bcS ℝ ℂ n q₁ = 0 := by rw [h, map_zero]
    rw [hq₁, hu₁c, hu₂c, ← map_add] at this
    exact hu₁₂ ((s3_bcS_injective (Kd d) ℂ) (this.trans (map_zero _).symm))
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rcases s3_eq_or_eq_neg_of_rho_eq hn a b hab with h | h
    · exact Subtype.ext h
    · exfalso
      have h1 : m ℝ n (a : C ℝ n) q₁ = q₁ := ha q₁ hq₁P
      rw [h, map_neg, LinearMap.neg_apply, hb q₁ hq₁P, neg_eq_iff_add_eq_zero, ← two_smul ℝ,
        smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact two_ne_zero h1
      · exact hq₁0 h1
  · have hext : ∀ s : Spin ℝ n, complexifyV n (rho ℝ n s : V ℝ n →ₗ[ℝ] V ℝ n) =
        (rho ℂ n (bcSpin ℝ ℂ n s) : V ℂ n →ₗ[ℂ] V ℂ n) :=
      fun s => s3_ext_rho ℝ ℂ s
    have hpres : ∀ (s : Spin ℝ n) (u : S ℂ n) (c : ℂ), c ≠ 0 →
        m ℂ n (bcC ℝ ℂ n s) u = c • u →
        ∀ v ∈ ann ℂ n u, rho ℂ n (bcSpin ℝ ℂ n s) v ∈ ann ℂ n u := by
      intro s u c hc hsu v hv
      have := s3_rho_mem_ann (bcSpin ℝ ℂ n s) hv
      have hm : m ℂ n ((bcSpin ℝ ℂ n s : Spin ℂ n) : C ℂ n) u = c • u := hsu
      rw [hm] at this
      have hann : ann ℂ n (c • u) = ann ℂ n u := by
        ext w
        show m ℂ n (ι (Q ℂ n) w) (c • u) = 0 ↔ m ℂ n (ι (Q ℂ n) w) u = 0
        rw [map_smul, smul_eq_zero]
        simp [hc]
      rwa [hann] at this
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨h₁, h₂⟩ := hfix s hs
      have hT₁ := hpres s u₁c 1 one_ne_zero (by rw [h₁, one_smul])
      have hT₂ := hpres s u₂c 1 one_ne_zero (by rw [h₂, one_smul])
      rw [← P.s3_W₁ℂ_eq_ann hW] at hT₁
      rw [← P.s3_W₂ℂ_eq_ann hW] at hT₂
      -- `ρ(s)` commutes with `f`
      have hcomm : ∀ x, rho ℝ n s (P.fR hW x) = P.fR hW (rho ℝ n s x) := by
        have hC : complexifyV n ((rho ℝ n s : V ℝ n →ₗ[ℝ] V ℝ n) * P.fR hW) =
            complexifyV n (P.fR hW * (rho ℝ n s : V ℝ n →ₗ[ℝ] V ℝ n)) := by
          rw [s3_complexifyV_eq, s3_complexifyV_eq, s3_ext_mul, s3_ext_mul, ← s3_complexifyV_eq,
            ← s3_complexifyV_eq, hext]
          apply LinearMap.ext
          intro x
          obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
            Submodule.mem_sup.mp (P.s3_sup_ℂ hW ▸ Submodule.mem_top (x := x))
          simp only [Module.End.mul_apply, LinearEquiv.coe_coe, map_add]
          rw [P.s3_fℂ_W₁ hW hx₁, P.s3_fℂ_W₂ hW hx₂, P.s3_fℂ_W₁ hW (hT₁ x₁ hx₁),
            P.s3_fℂ_W₂ hW (hT₂ x₂ hx₂), map_smul, map_smul]
        intro x
        exact LinearMap.congr_fun (s3_complexifyV_injective hC) x
      have hdet : ∀ (u : S ℂ n) (hu : IsEvenPureSpinor ℂ n u), u ≠ 0 →
          m ℂ n (bcC ℝ ℂ n s) u = u →
          ∀ hT : ∀ v ∈ ann ℂ n u, rho ℂ n (bcSpin ℝ ℂ n s) v ∈ ann ℂ n u,
          s3_DetOne (complexifyV n (rho ℝ n s : V ℝ n →ₗ[ℝ] V ℝ n)) (ann ℂ n u) := by
        intro u hu hu0 hsu hT
        obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 ℂ n u hu (bcSpin ℝ ℂ n s) hT
        have hc1 : c = 1 := by
          have hsu' : m ℂ n (bcC ℝ ℂ n s) u = c • u := hc
          rw [hsu] at hsu'
          have : (c - 1) • u = 0 := by rw [sub_smul, ← hsu', one_smul, sub_self]
          exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)
        rw [hc1, one_pow] at hc2
        exact s3_DetOne_congr (hext s).symm ⟨hT, hc2.symm⟩
      refine ⟨(mem_SOplus_iff ℝ n _).mpr ⟨s, rfl⟩, hcomm, ?_, ?_⟩
      · rw [P.s3_W₁ℂ_eq_ann hW] at hT₁ ⊢
        exact hdet u₁c (P.s3_isPure₁ℂ hW) P.s3_bcS_u₁_ne_zero h₁ hT₁
      · rw [P.s3_W₂ℂ_eq_ann hW] at hT₂ ⊢
        exact hdet u₂c (P.s3_isPure₂ℂ hW) P.s3_bcS_u₂_ne_zero h₂ hT₂
    · rintro ⟨hg1, hg2, hg3, hg4⟩
      obtain ⟨s, rfl⟩ := (mem_SOplus_iff ℝ n g).mp hg1
      have hg3' := s3_DetOne_congr (hext s) hg3
      rw [P.s3_W₁ℂ_eq_ann hW] at hg3'
      obtain ⟨hT₁, hdet₁⟩ := hg3'
      obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 ℂ n u₁c (P.s3_isPure₁ℂ hW)
        (bcSpin ℝ ℂ n s) hT₁
      have hc' : m ℂ n (bcC ℝ ℂ n s) u₁c = c • u₁c := hc
      replace hc2 : c ^ 2 = 1 := hc2.trans hdet₁
      have hc₂ : m ℂ n (bcC ℝ ℂ n s) u₂c = (starRingAut : ℂ ≃+* ℂ) c • u₂c := by
        rw [hu₂c, ← P.s3_conj_u₁ℂ, s3_m_bcC_conjS ℝ (starRingAut : ℂ ≃+* ℂ) s3_conj_hc, hc',
          s3_conjS_smul]
      have hc1 : c = 1 ∨ c = -1 := by
        have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp this with h | h
        · left; exact sub_eq_zero.mp h
        · right; exact eq_neg_of_add_eq_zero_left h
      rcases hc1 with rfl | rfl
      · refine ⟨s, hfix' s (by rw [hc', one_smul]) (by rw [hc₂, map_one, one_smul]), rfl⟩
      · have hQ0 : Q ℝ n ≠ 0 := by
          have := s3_nontrivial_V (F := ℝ) hn
          exact s3_Q_nondegenerate.ne_zero
        refine ⟨spinGroup.negOne (Q ℝ n) hQ0 * s, hfix' _ ?_ ?_, s3_rho_negOne_mul hQ0 s⟩
        · rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, map_neg, map_neg,
            LinearMap.neg_apply, hc', neg_one_smul, neg_neg]
        · rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, map_neg, map_neg,
            LinearMap.neg_apply, hc₂, map_neg, map_one, neg_one_smul, neg_neg]


namespace KSecant

variable (P : KSecant n d)

/-! ## The Hermitian form `H` (3.1.2) -/

/-- **The form `H`** (3.1.2) (`eq-H`): the `K`-valued form `H(x, y) = d (x, y)_V + √-d (f(x), y)_V`
on `V_ℚ`. -/
noncomputable def hermH (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) : Kd d :=
  algebraMap ℚ (Kd d) (d * pairing ℚ n x y) +
    Kd.sqrtNeg d * algebraMap ℚ (Kd d) (pairing ℚ n (P.fη hW x) y)

theorem s3_hermH_add_right (hW : IsCompl P.W₁ P.W₂) (x y z : V ℚ n) :
    P.hermH hW x (y + z) = P.hermH hW x y + P.hermH hW x z := by
  simp only [hermH, map_add, mul_add]
  ring

theorem s3_hermH_smul_right (hW : IsCompl P.W₁ P.W₂) (a : ℚ) (x y : V ℚ n) :
    P.hermH hW x (a • y) = algebraMap ℚ (Kd d) a * P.hermH hW x y := by
  simp only [hermH, map_smul, smul_eq_mul, map_mul]
  ring

theorem s3_hermH_add_left (hW : IsCompl P.W₁ P.W₂) (x y z : V ℚ n) :
    P.hermH hW (x + y) z = P.hermH hW x z + P.hermH hW y z := by
  simp only [hermH, map_add, LinearMap.add_apply, mul_add]
  ring

theorem s3_hermH_smul_left (hW : IsCompl P.W₁ P.W₂) (a : ℚ) (x y : V ℚ n) :
    P.hermH hW (a • x) y = algebraMap ℚ (Kd d) a * P.hermH hW x y := by
  simp only [hermH, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
  ring

/-- `H(x, f y) = √-d H(x, y)`. -/
theorem s3_hermH_fη_right (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.hermH hW x (P.fη hW y) = Kd.sqrtNeg d * P.hermH hW x y := by
  simp only [hermH]
  rw [P.pairing_fη_fη hW, mul_add, ← mul_assoc, s3_sqrtNeg_mul_self (s3_d_pos P),
    P.pairing_fη_left hW, map_mul, map_mul, map_neg]
  ring

/-- Hermitian symmetry `H(x, y) = σ(H(y, x))` (the proof of Lemma 3.1.2: `f` is anti-self-dual). -/
theorem s3_hermH_hermitian (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.hermH hW x y = Kd.σ d (P.hermH hW y x) := by
  simp only [hermH, map_add, map_mul, s3_σ_algebraMap, s3_σ_sqrtNeg]
  rw [s3_pairing_comm y x, P.s3_pairing_fη_swap hW y x, map_neg]
  ring

/-- `H(x, η_λ y) = λ H(x, y)` (Lemma 3.1.2). -/
theorem s3_hermH_η_right (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (x y : V ℚ n) :
    P.hermH hW x (P.η hW l y) = l * P.hermH hW x y := by
  rw [P.s3_η_apply hW, P.s3_hermH_add_right, P.s3_hermH_smul_right, P.s3_hermH_smul_right,
    P.s3_hermH_fη_right]
  conv_rhs => rw [Kd.eq_ratPart_add_sqrtNegCoeff (s3_d_pos P) l]
  ring

/-- `H(η_λ x, y) = σ(λ) H(x, y)`. -/
theorem s3_hermH_η_left (hW : IsCompl P.W₁ P.W₂) (l : Kd d) (x y : V ℚ n) :
    P.hermH hW (P.η hW l x) y = Kd.σ d l * P.hermH hW x y := by
  rw [P.s3_hermH_hermitian, P.s3_hermH_η_right, map_mul, ← P.s3_hermH_hermitian]

/-- `H(x, x) = d (x, x)_V` is rational. -/
theorem s3_hermH_self (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) :
    P.hermH hW x x = algebraMap ℚ (Kd d) (d * pairing ℚ n x x) := by
  simp [hermH, P.s3_pairing_fη_self hW x]

/-- `H` is invariant under the `ℚ`-isometries commuting with `f`. -/
theorem s3_hermH_of_isometry (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x y, pairing ℚ n (g x) (g y) = pairing ℚ n x y)
    (hgf : ∀ x, g (P.fη hW x) = P.fη hW (g x)) (x y : V ℚ n) :
    P.hermH hW (g x) (g y) = P.hermH hW x y := by
  simp only [hermH, hg, ← hgf]

/-- `U(V_ℚ, H)`: the `K`-linear automorphisms of `V_ℚ` (those commuting with `f = η_{√-d}`) leaving
`H` invariant. -/
noncomputable def UH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | (∀ x, g (P.fη hW x) = P.fη hW (g x)) ∧
    ∀ x y, P.hermH hW (g x) (g y) = P.hermH hW x y}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    exact ⟨fun x => by simp only [LinearEquiv.mul_apply, hh1, hg1],
      fun x y => by simp only [LinearEquiv.mul_apply, hg2, hh2]⟩
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨s3_inv_comm hg1, fun x y => ?_⟩
    rw [← hg2]
    simp

/-- `SU(V_ℚ, H)`: the elements of `U(V_ℚ, H)` of `K`-determinant `1`; the `K`-determinant of a
`K`-linear `g` is `det(g|_{W₁})` (`g` extended to `V_K`), as in the proof of Lemma 3.1.2. -/
noncomputable def SUH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | g ∈ P.UH hW ∧ ∃ h : ∀ x ∈ P.W₁, bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n) x ∈ P.W₁,
      LinearMap.det ((bcEndV (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict h) = 1}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    exact ⟨mul_mem hg1 hh1, s3_DetOne_ext_mul hg2 hh2⟩
  one_mem' := ⟨one_mem _, s3_DetOne_ext_one _⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    exact ⟨inv_mem hg1, s3_DetOne_ext_inv hg2⟩

/-- The group of Lemma 3.1.2 read literally, "the subgroup `SU(V_ℚ, H)` of `SL(V_ℚ)` leaving `H`
invariant": the `ℚ`-linear automorphisms of determinant `1` leaving `H` invariant. (It equals
`U(V_ℚ, H)`; see `lemma3_1_2_finiteIndex`.) -/
noncomputable def SLH (hW : IsCompl P.W₁ P.W₂) : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | LinearMap.det (g : V ℚ n →ₗ[ℚ] V ℚ n) = 1 ∧
    ∀ x y, P.hermH hW (g x) (g y) = P.hermH hW x y}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, fun x y => by simp only [LinearEquiv.mul_apply, hg2, hh2]⟩
    rw [LinearEquiv.coe_toLinearMap_mul, map_mul, hg1, hh1, mul_one]
  one_mem' := ⟨by rw [LinearEquiv.coe_toLinearMap_one, LinearMap.det_id], fun _ _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, fun x y => ?_⟩
    · have h := congrArg LinearMap.det
        (LinearEquiv.coe_toLinearMap_mul (e₁ := g⁻¹) (e₂ := g)).symm
      rw [inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, LinearMap.det_id, map_mul,
        hg1, mul_one] at h
      exact h
    · rw [← hg2]
      simp

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

/-! ### Orthogonal `K`-bases, signature and change of `K`-basis -/

/-- `H(x, y) = 0` iff `(x, y)_V = 0` and `(f x, y)_V = 0`. -/
theorem s3_hermH_eq_zero_iff (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.hermH hW x y = 0 ↔ pairing ℚ n x y = 0 ∧ pairing ℚ n (P.fη hW x) y = 0 := by
  have hd := s3_d_pos P
  constructor
  · intro h
    have h' : Kd.σ d (P.hermH hW x y) = 0 := by rw [h, map_zero]
    simp only [hermH, map_add, map_mul, s3_σ_algebraMap, s3_σ_sqrtNeg] at h'
    simp only [hermH] at h
    simp only [map_mul] at h h'
    have h1 : algebraMap ℚ (Kd d) (2 * (d * pairing ℚ n x y)) = 0 := by
      rw [map_mul, map_mul, map_ofNat]; linear_combination h + h'
    have h2 : Kd.sqrtNeg d * algebraMap ℚ (Kd d) (2 * pairing ℚ n (P.fη hW x) y) = 0 := by
      rw [map_mul, map_ofNat]; linear_combination h - h'
    rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h1
    rw [mul_eq_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h2
    refine ⟨?_, ?_⟩
    · have := hd.ne'
      simp_all
    · rcases h2 with h2 | h2
      · exact absurd h2 (s3_sqrtNeg_ne_zero hd)
      · simpa using h2
  · rintro ⟨h1, h2⟩
    simp [hermH, h1, h2]

/-- The family `(b_i, f b_i)` attached to an `H`-orthogonal family `b` is orthogonal for
`(·,·)_V`. -/
theorem s3_orth_family_ortho (hW : IsCompl P.W₁ P.W₂) {m : Type*} (b : m → V ℚ n)
    (hb2 : ∀ i j, i ≠ j → P.hermH hW (b i) (b j) = 0) :
    ∀ s t, s ≠ t → pairing ℚ n (Sum.elim b (fun i => P.fη hW (b i)) s)
      (Sum.elim b (fun i => P.fη hW (b i)) t) = 0 := by
  have hbij : ∀ i j, i ≠ j → pairing ℚ n (b i) (b j) = 0 ∧
      pairing ℚ n (P.fη hW (b i)) (b j) = 0 :=
    fun i j hij => (P.s3_hermH_eq_zero_iff hW _ _).mp (hb2 i j hij)
  rintro (i | i) (j | j) hst
  · exact (hbij i j fun h => hst (h ▸ rfl)).1
  · simp only [Sum.elim_inl, Sum.elim_inr]
    rw [s3_pairing_comm]
    by_cases hij : i = j
    · subst hij; exact P.s3_pairing_fη_self hW _
    · exact (hbij j i (Ne.symm hij)).2
  · simp only [Sum.elim_inl, Sum.elim_inr]
    by_cases hij : i = j
    · subst hij; exact P.s3_pairing_fη_self hW _
    · exact (hbij i j hij).2
  · simp only [Sum.elim_inr, P.pairing_fη_fη hW]
    rw [(hbij i j fun h => hst (h ▸ rfl)).1, mul_zero]

/-- ... with nonzero norms if `(b_i, b_i)_V ≠ 0`. -/
theorem s3_orth_family (hW : IsCompl P.W₁ P.W₂) {m : Type*} (b : m → V ℚ n)
    (hb1 : ∀ i, pairing ℚ n (b i) (b i) ≠ 0) (hb2 : ∀ i j, i ≠ j → P.hermH hW (b i) (b j) = 0) :
    (∀ s, pairing ℚ n (Sum.elim b (fun i => P.fη hW (b i)) s)
        (Sum.elim b (fun i => P.fη hW (b i)) s) ≠ 0) ∧
      ∀ s t, s ≠ t → pairing ℚ n (Sum.elim b (fun i => P.fη hW (b i)) s)
        (Sum.elim b (fun i => P.fη hW (b i)) t) = 0 := by
  refine ⟨?_, P.s3_orth_family_ortho hW b hb2⟩
  rintro (i | i)
  · exact hb1 i
  · simp only [Sum.elim_inr, P.pairing_fη_fη hW]
    exact mul_ne_zero (s3_d_pos P).ne' (hb1 i)

/-- The Gram–Schmidt step: there are `m ≤ 2n` mutually `H`-orthogonal vectors `b_i` with
`(b_i, b_i)_V ≠ 0`. -/
theorem s3_exists_orth (hW : IsCompl P.W₁ P.W₂) : ∀ m ≤ 2 * n, ∃ b : Fin m → V ℚ n,
    (∀ i, pairing ℚ n (b i) (b i) ≠ 0) ∧ ∀ i j, i ≠ j → P.hermH hW (b i) (b j) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨b, hb1, hb2⟩ := ih (by omega)
    obtain ⟨hc1, hc2⟩ := P.s3_orth_family hW b hb1 hb2
    set c : Fin m ⊕ Fin m → V ℚ n := Sum.elim b (fun i => P.fη hW (b i)) with hc
    obtain ⟨hcompl, hnd⟩ := s3_orth_complement c hc1 hc2
    set U := Submodule.span ℚ (Set.range c) with hU
    have hli : LinearIndependent ℚ c :=
      LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := pairing ℚ n) (fun s t hst => hc2 s t hst) hc1
    have hUrank : Module.finrank ℚ U = m + m := by
      rw [hU, finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin]
    have hne : (pairing ℚ n).orthogonal U ≠ ⊥ := by
      intro h
      have := hcompl.sup_eq_top
      rw [h, sup_bot_eq] at this
      have h2 := congrArg (fun W : Submodule ℚ (V ℚ n) => Module.finrank ℚ W) this
      simp only [finrank_top, hUrank, s3_finrank_V] at h2
      omega
    have hB0 : (pairing ℚ n).restrict ((pairing ℚ n).orthogonal U) ≠ 0 := by
      intro h0
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hx0
      have := hnd.1 ⟨x, hx⟩ (fun y => by rw [h0]; rfl)
      exact congrArg Subtype.val this
    have hsymm : LinearMap.IsSymm ((pairing ℚ n).restrict ((pairing ℚ n).orthogonal U)) :=
      ⟨fun x y => s3_pairing_comm (x : V ℚ n) y⟩
    obtain ⟨x, hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB0 hsymm
    refine ⟨Fin.snoc b (x : V ℚ n), ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa using hb1 i
    · have hxperp : ∀ i, P.hermH hW (b i) x = 0 := by
        intro i
        rw [P.s3_hermH_eq_zero_iff hW]
        exact ⟨x.2 _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩),
          x.2 _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)⟩
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [P.s3_hermH_hermitian, hxperp, map_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact hxperp i
        | cast j =>
          simp only [Fin.snoc_castSucc]
          exact hb2 i j fun h => hij (by rw [h])


/-- There is an `H`-orthogonal `K`-basis of `V_ℚ` (Gram–Schmidt). -/
theorem s3_exists_orthKBasis (hW : IsCompl P.W₁ P.W₂) : ∃ v, P.IsOrthKBasis hW v := by
  obtain ⟨b, hb1, hb2⟩ := P.s3_exists_orth hW (2 * n) le_rfl
  obtain ⟨hc1, hc2⟩ := P.s3_orth_family hW b hb1 hb2
  exact ⟨b, LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := pairing ℚ n)
    (fun s t hst => hc2 s t hst) hc1, hb2⟩

/-- `Q(f x) = d Q(x)`. -/
theorem s3_Q_fη (hW : IsCompl P.W₁ P.W₂) (x : V ℚ n) : Q ℚ n (P.fη hW x) = d * Q ℚ n x := by
  have h := P.pairing_fη_fη hW x x
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  linarith

/-- **Lemma 3.1.2**, signature: every `H`-orthogonal `K`-basis has `n` positive and `n` negative
entries `H(v_i, v_i)`. -/
theorem s3_hasSignature (hW : IsCompl P.W₁ P.W₂) : P.HasSignature hW n n := by
  refine ⟨P.s3_exists_orthKBasis hW, fun v hv => ?_⟩
  obtain ⟨hv1, hv2⟩ := hv
  have hortho := P.s3_orth_family_ortho hW v hv2
  have hcard : Fintype.card (Fin (2 * n) ⊕ Fin (2 * n)) = Module.finrank ℚ (V ℚ n) := by
    simp
  let c := basisOfLinearIndependentOfCardEqFinrank' _ hv1 hcard
  have hc : ∀ s, c s = Sum.elim v (fun i => P.fη hW (v i)) s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hv1 hcard) s
  obtain ⟨h1, h2⟩ := s3_sig_of_orthogonal_basis c
    (fun s t hst => by rw [hc, hc]; exact hortho s t hst)
  rw [s3_sig_Q.1, s3_ncard_sum] at h1
  rw [s3_sig_Q.2, s3_ncard_sum] at h2
  simp only [hc, Sum.elim_inl, Sum.elim_inr, P.s3_Q_fη hW] at h1 h2
  have hd := s3_d_pos P
  have hpos : ∀ i, (0 < d * Q ℚ n (v i) ↔ 0 < Q ℚ n (v i)) := fun i => by
    constructor
    · intro h; exact pos_of_mul_pos_right h hd.le
    · intro h; exact mul_pos hd h
  have hneg : ∀ i, (d * Q ℚ n (v i) < 0 ↔ Q ℚ n (v i) < 0) := fun i => by
    constructor
    · intro h; by_contra h'; push Not at h'; linarith [mul_nonneg hd.le h']
    · intro h; exact mul_neg_of_pos_of_neg hd h
  simp only [hpos, hneg] at h1 h2
  have hH : ∀ i, Kd.ratPart d (P.hermH hW (v i) (v i)) = 2 * d * Q ℚ n (v i) := by
    intro i
    rw [P.s3_hermH_self hW, s3_ratPart_algebraMap, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hpos' : ∀ i, (0 < Kd.ratPart d (P.hermH hW (v i) (v i)) ↔ 0 < Q ℚ n (v i)) := fun i => by
    rw [hH]
    constructor
    · intro h; exact pos_of_mul_pos_right h (by positivity)
    · intro h; positivity
  have hneg' : ∀ i, (Kd.ratPart d (P.hermH hW (v i) (v i)) < 0 ↔ Q ℚ n (v i) < 0) := fun i => by
    rw [hH]
    constructor
    · intro h; by_contra h'; push Not at h'; have : 0 ≤ 2 * d * Q ℚ n (v i) := by positivity
      linarith
    · intro h; exact mul_neg_of_pos_of_neg (by positivity) h
  simp only [hpos', hneg']
  omega


/-- `H` as a `ℚ`-bilinear map. -/
noncomputable def s3_hermHℚ (hW : IsCompl P.W₁ P.W₂) : V ℚ n →ₗ[ℚ] V ℚ n →ₗ[ℚ] Kd d :=
  LinearMap.mk₂ ℚ (P.hermH hW) (P.s3_hermH_add_left hW)
    (fun a x y => by rw [P.s3_hermH_smul_left, Algebra.smul_def]) (P.s3_hermH_add_right hW)
    (fun a x y => by rw [P.s3_hermH_smul_right, Algebra.smul_def])

theorem s3_hermHℚ_apply (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.s3_hermHℚ hW x y = P.hermH hW x y := rfl

/-- `H(f x, y) = -√-d H(x, y)`. -/
theorem s3_hermH_fη_left (hW : IsCompl P.W₁ P.W₂) (x y : V ℚ n) :
    P.hermH hW (P.fη hW x) y = -Kd.sqrtNeg d * P.hermH hW x y := by
  rw [P.s3_hermH_hermitian, P.s3_hermH_fη_right, map_mul, s3_σ_sqrtNeg, ← P.s3_hermH_hermitian]

/-- The `ℚ`-basis `(b_i, f b_i)` of a `K`-basis `b`. -/
noncomputable def s3_qBasis (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) : Module.Basis (Fin (2 * n) ⊕ Fin (2 * n)) ℚ (V ℚ n) :=
  basisOfLinearIndependentOfCardEqFinrank' _ hb (by simp)

theorem s3_qBasis_apply (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) (s) :
    P.s3_qBasis hW b hb s = Sum.elim b (fun i => P.fη hW (b i)) s :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hb _) s

/-- The `K`-coordinates of `y` in the `K`-basis `b`. -/
noncomputable def s3_coordK (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) (y : V ℚ n) (i : Fin (2 * n)) : Kd d :=
  algebraMap ℚ (Kd d) ((P.s3_qBasis hW b hb).repr y (Sum.inl i)) +
    algebraMap ℚ (Kd d) ((P.s3_qBasis hW b hb).repr y (Sum.inr i)) * Kd.sqrtNeg d

/-- `H(x, y) = ∑ᵢ yᵢ H(x, bᵢ)`, `yᵢ` the `K`-coordinates of `y`. -/
theorem s3_hermH_expand_right (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) (x y : V ℚ n) :
    P.hermH hW x y = ∑ i, P.s3_coordK hW b hb y i * P.hermH hW x (b i) := by
  conv_lhs => rw [← (P.s3_qBasis hW b hb).sum_repr y]
  rw [← P.s3_hermHℚ_apply, map_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul]
  simp only [P.s3_hermHℚ_apply, P.s3_qBasis_apply, Sum.elim_inl, Sum.elim_inr,
    P.s3_hermH_fη_right, Algebra.smul_def, s3_coordK]
  ring

/-- `H(y, x) = ∑ᵢ σ(yᵢ) H(bᵢ, x)`. -/
theorem s3_hermH_expand_left (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) (x y : V ℚ n) :
    P.hermH hW y x = ∑ i, Kd.σ d (P.s3_coordK hW b hb y i) * P.hermH hW (b i) x := by
  rw [P.s3_hermH_hermitian, P.s3_hermH_expand_right hW b hb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← P.s3_hermH_hermitian]

/-- `y = 0` if all its `K`-coordinates vanish. -/
theorem s3_eq_zero_of_coordK (hW : IsCompl P.W₁ P.W₂) (b : Fin (2 * n) → V ℚ n)
    (hb : P.IsKBasis hW b) (y : V ℚ n) (hy : ∀ i, P.s3_coordK hW b hb y i = 0) : y = 0 := by
  have hd := s3_d_pos P
  apply (P.s3_qBasis hW b hb).repr.injective
  ext s
  have key : ∀ i, (P.s3_qBasis hW b hb).repr y (Sum.inl i) = 0 ∧
      (P.s3_qBasis hW b hb).repr y (Sum.inr i) = 0 := by
    intro i
    have h := hy i
    simp only [s3_coordK] at h
    have h' : Kd.σ d (P.s3_coordK hW b hb y i) = 0 := by rw [hy i, map_zero]
    simp only [s3_coordK, map_add, map_mul, s3_σ_algebraMap, s3_σ_sqrtNeg] at h'
    have h1 : algebraMap ℚ (Kd d) (2 * (P.s3_qBasis hW b hb).repr y (Sum.inl i)) = 0 := by
      rw [map_mul, map_ofNat]; linear_combination h + h'
    have h2 : Kd.sqrtNeg d *
        algebraMap ℚ (Kd d) (2 * (P.s3_qBasis hW b hb).repr y (Sum.inr i)) = 0 := by
      rw [map_mul, map_ofNat]; linear_combination h - h'
    rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h1
    rw [mul_eq_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h2
    refine ⟨by simpa using h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd h2 (s3_sqrtNeg_ne_zero hd)
    · simpa using h2
  rcases s with i | i
  · simp [(key i).1]
  · simp [(key i).2]

theorem s3_coe_Nm (z : Kd d) (hd : 0 < d) :
    algebraMap ℚ (Kd d) (Kd.Nm d z) = z * Kd.σ d z := by
  apply Subtype.ext
  rw [s3_coe_algebraMap, Kd.coe_Nm hd]
  rfl

theorem s3_normGroup_mul {q q' : ℚ} (hq : q ∈ Kd.normGroup d)
    (hq' : q' ∈ Kd.normGroup d) : q * q' ∈ Kd.normGroup d := by
  obtain ⟨z, hz, rfl⟩ := hq
  obtain ⟨z', hz', rfl⟩ := hq'
  exact ⟨z * z', mul_ne_zero hz hz', map_mul _ _ _⟩

/-- The discriminant does not depend on the `K`-basis: `det G_b = Nm(det A) det G_{b₀}`. -/
theorem s3_det_gramH_change (hW : IsCompl P.W₁ P.W₂) (b₀ b : Fin (2 * n) → V ℚ n)
    (hb₀ : P.IsKBasis hW b₀) (hb : P.IsKBasis hW b) :
    ∃ q ∈ Kd.normGroup d, (P.gramH hW b).det = (P.gramH hW b₀).det * algebraMap ℚ (Kd d) q := by
  have hd := s3_d_pos P
  -- the change of basis matrix
  let A : Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d) :=
    Matrix.of fun i j => P.s3_coordK hW b₀ hb₀ (b j) i
  have hgram : P.gramH hW b = (A.map (Kd.σ d)).transpose * P.gramH hW b₀ * A := by
    rw [Matrix.mul_assoc]
    refine Matrix.ext fun j k => ?_
    simp only [gramH, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, A]
    rw [P.s3_hermH_expand_left hW b₀ hb₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.s3_hermH_expand_right hW b₀ hb₀]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- `det A ≠ 0`
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set y : V ℚ n := ∑ k, P.η hW (v k) (b k) with hy
    -- `y` is `H`-orthogonal to everything, hence `0`
    have hHy : ∀ x, P.hermH hW x y = 0 := by
      intro x
      rw [hy, ← P.s3_hermHℚ_apply, map_sum]
      simp only [P.s3_hermHℚ_apply, P.s3_hermH_η_right, P.s3_hermH_expand_right hW b₀ hb₀ x (b _),
        Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ i, ∑ k, v k * (P.s3_coordK hW b₀ hb₀ (b k) i * P.hermH hW x (b₀ i)) =
          (A.mulVec v) i * P.hermH hW x (b₀ i) := by
        intro i
        simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      simp only [this, hv, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    have hy0 : y = 0 := s3_pairing_sepLeft y fun x => by
      rw [s3_pairing_comm]; exact ((P.s3_hermH_eq_zero_iff hW x y).mp (hHy x)).1
    -- but the `K`-coordinates of `y` in `b` are `v ≠ 0`
    apply hv0
    have hy' : y = ∑ s, (Sum.elim (fun k => Kd.ratPart d (v k)) (fun k => Kd.sqrtNegCoeff d (v k))
        s) • Sum.elim b (fun i => P.fη hW (b i)) s := by
      rw [hy, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      simp only [P.s3_η_apply hW, Sum.elim_inl, Sum.elim_inr]
    rw [hy0] at hy'
    have hw := (Fintype.linearIndependent_iff.mp hb) _ hy'.symm
    funext k
    have h1 := hw (Sum.inl k)
    have h2 := hw (Sum.inr k)
    simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2
    rw [Kd.eq_ratPart_add_sqrtNegCoeff hd (v k), h1, h2]
    simp
  refine ⟨Kd.Nm d A.det, ⟨A.det, hA, rfl⟩, ?_⟩
  have hσdet : (A.map (Kd.σ d)).det = Kd.σ d A.det :=
    (RingHom.map_det (Kd.σ d : Kd d →+* Kd d) A).symm
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hσdet, s3_coe_Nm _ hd]
  ring

/-- The discriminant does not depend on the `K`-basis: if `DiscIs c`, then for every `K`-basis the
determinant of the Gram matrix lies in `c · Nm(K^×)` (Assumption 2.4.1 in force). -/
theorem discIs_iff_forall (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) (c : ℚ) :
    P.DiscIs hP.isCompl c ↔ ∀ b, P.IsKBasis hP.isCompl b →
      ∃ q ∈ Kd.normGroup d, (P.gramH hP.isCompl b).det = algebraMap ℚ (Kd d) (c * q) := by
  constructor
  · rintro ⟨b₀, hb₀, q₀, hq₀, h₀⟩ b hb
    obtain ⟨q, hq, h⟩ := P.s3_det_gramH_change hP.isCompl b₀ b hb₀ hb
    refine ⟨q₀ * q, s3_normGroup_mul hq₀ hq, ?_⟩
    rw [h, h₀, ← map_mul, mul_assoc]
  · intro h
    obtain ⟨v, hv, -⟩ := P.s3_exists_orthKBasis hP.isCompl
    obtain ⟨q, hq, h'⟩ := h v hv
    exact ⟨v, hv, q, hq, h'⟩

end KSecant

/-! ## The spinor norm on `SU(V_ℚ, H)` (gap repair for Lemma 3.1.2)

The proof that `SU(V_ℚ, H) ⊆ SO_+(V_ℚ)_f`, which replaces the last paragraph of the proof of
Lemma 3.1.2 (see `lemma3_1_2_finiteIndex`). Ingredients: `(m_x s, t)_S = (s, m_{τ(x)} t)_S` for the
Mukai pairing ([Chevalley, III.2.2]); a pure spinor is Mukai-isotropic, so `(u₁, u₂)_S ≠ 0` for a
non-isotropic `P`; the determinant of a `K`-linear `g` on `W₂ = σ(W₁)` is `σ(det(g|W₁))`;
eigenvalues of rational operators on `u₁` descend from `ℂ` to `K`. -/

section S3Mukai

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
/-- `∫_X D_θ z = 0`: a contraction has no top-degree component. -/
theorem s3_integral_D (θ : Module.Dual F (H1 F n)) (z : S F n) : integral F n (D F n θ z) = 0 := by
  have hθ : θ = ∑ i, θ (e F n i) • (Pi.basisFun F (Fin (2 * n))).coord i := by
    apply LinearMap.ext
    intro w
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, Pi.basisFun_repr]
    conv_lhs => rw [show w = ∑ i, w i • e F n i by ext j; simp [e, Pi.single_apply]]
    simp [map_sum, mul_comm]
  conv_lhs => rw [← (basisS F n).sum_repr z]
  simp only [map_sum, map_smul]
  refine Finset.sum_eq_zero fun K _ => ?_
  refine mul_eq_zero_of_right _ ?_
  rw [hθ]
  simp only [D, map_sum, map_smul]
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, map_smul]
  refine smul_eq_zero_of_right _ ?_
  rw [show basisS F n K = (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra K from rfl,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis]
  split_ifs with hi
  · have h0 : integral F n (basisS F n (K.erase i)) = 0 := by
      rw [integral, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right_iff]
      intro h
      have : i ∈ K.erase i := h ▸ Finset.mem_univ i
      simp at this
    rw [Units.smul_def, map_zsmul,
      show (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra (K.erase i) = basisS F n (K.erase i) from rfl,
      h0, smul_zero]
  · simp

theorem s3_m_ι_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) (x : S F n) :
    m F n (ι (Q F n) (θ, w)) x = ExteriorAlgebra.ι F w * x + D F n θ x := by
  simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, L, LinearMap.mul_apply']

omit [CharZero F] in
theorem s3_mukai_apply (s t : S F n) : mukai F n s t = integral F n (tau F n s * t) := rfl

omit [CharZero F] in
/-- `∫ τ(D_θ s) t = ∫ τ(s) D_θ t`. -/
theorem s3_integral_tau_D (θ : Module.Dual F (H1 F n)) (s t : S F n) :
    integral F n (tau F n (D F n θ s) * t) = integral F n (tau F n s * D F n θ t) := by
  induction s using CliffordAlgebra.left_induction generalizing t with
  | algebraMap r =>
    have h0 : D F n θ (algebraMap F (S F n) r) = 0 := contractLeft_algebraMap (Q := (0 : QuadraticForm F (H1 F n))) θ r
    have h1 : tau F n (algebraMap F (S F n) r) = algebraMap F (S F n) r :=
      CliffordAlgebra.reverse.commutes r
    rw [h0, map_zero, zero_mul, map_zero, h1, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, map_smul, s3_integral_D, smul_zero]
  | add a b ha hb => rw [map_add, map_add, add_mul, map_add, ha, hb, map_add, add_mul, map_add]
  | ι_mul x u hx =>
    have h1 : D F n θ (ι (0 : QuadraticForm F (H1 F n)) u * x) =
        θ u • x - ι (0 : QuadraticForm F (H1 F n)) u * D F n θ x := contractLeft_ι_mul _ _ _
    have h2 : D F n θ (ι (0 : QuadraticForm F (H1 F n)) u * t) =
        θ u • t - ι (0 : QuadraticForm F (H1 F n)) u * D F n θ t := contractLeft_ι_mul _ _ _
    rw [h1, map_sub, map_smul, sub_mul, map_sub, smul_mul_assoc, map_smul]
    have h3 : tau F n (ι (0 : QuadraticForm F (H1 F n)) u * D F n θ x) * t =
        tau F n (D F n θ x) * (ι (0 : QuadraticForm F (H1 F n)) u * t) := by
      simp only [tau, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, mul_assoc]
    rw [h3, hx, h2, mul_sub, map_sub, mul_smul_comm, map_smul]
    have h4 : tau F n (ι (0 : QuadraticForm F (H1 F n)) u * x) * D F n θ t =
        tau F n x * (ι (0 : QuadraticForm F (H1 F n)) u * D F n θ t) := by
      simp only [tau, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, mul_assoc]
    rw [h4]
    abel

/-- **[Chevalley, III.2.2]**: `m_v` is self-adjoint for the Mukai pairing. -/
theorem s3_mukai_m_ι (v : V F n) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) t = mukai F n s (m F n (ι (Q F n) v) t) := by
  obtain ⟨θ, w⟩ := v
  rw [s3_mukai_apply, s3_mukai_apply, s3_m_ι_apply, s3_m_ι_apply, map_add, add_mul, map_add,
    mul_add, map_add, s3_integral_tau_D]
  congr 1
  simp only [tau, CliffordAlgebra.reverse.map_mul]
  rw [show (ExteriorAlgebra.ι F w : S F n) = ι (0 : QuadraticForm F (H1 F n)) w from rfl,
    CliffordAlgebra.reverse_ι, mul_assoc]

/-- `(m_x s, t)_S = (s, m_{τ(x)} t)_S`. -/
theorem s3_mukai_m (x : C F n) (s t : S F n) :
    mukai F n (m F n x s) t = mukai F n s (m F n (CliffordAlgebra.reverse x) t) := by
  induction x using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    simp only [AlgHom.commutes, CliffordAlgebra.reverse.commutes, Module.algebraMap_end_apply,
      map_smul, LinearMap.smul_apply]
  | ι v => rw [s3_mukai_m_ι, CliffordAlgebra.reverse_ι]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, CliffordAlgebra.reverse.map_mul, map_mul,
      Module.End.mul_apply]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, ha, hb, map_add, map_add,
      LinearMap.add_apply, map_add]

/-- A pure spinor is isotropic for the Mukai pairing ([Chevalley, III.2.4]). -/
theorem s3_mukai_self_of_pure (hn : 0 < n) {u : S F n} (hu : IsEvenPureSpinor F n u) :
    mukai F n u u = 0 := by
  have hW : ann F n u ≠ ⊥ := by
    intro h
    have := hu.2.2
    rw [h, finrank_bot] at this
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨w, hw⟩ : ∃ w, pairing F n v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (s3_pairing_sepLeft v h)
  have hvu : m F n (ι (Q F n) v) u = 0 := hv
  have hrel : m F n (ι (Q F n) v) (m F n (ι (Q F n) w) u) = pairing F n v w • u := by
    have h := congrArg (fun x => m F n x u) (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q F n) v w)
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hvu, map_zero,
      add_zero, AlgHom.commutes, Module.algebraMap_end_apply] at h
    rw [h]
    rfl
  have : pairing F n v w • mukai F n u u = 0 := by
    have e : pairing F n v w • mukai F n u u = mukai F n (pairing F n v w • u) u := by
      rw [map_smul, LinearMap.smul_apply]
    rw [e, ← hrel, s3_mukai_m_ι, hvu, map_zero]
  exact (smul_eq_zero.mp this).resolve_left hw

end S3Mukai

section S3MukaiBc

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
theorem s3_bcS_tau (s : S F n) : bcS F F' n (tau F n s) = tau F' n (bcS F F' n s) := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    simp only [tau, CliffordAlgebra.reverse.commutes, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), CliffordAlgebra.reverse.commutes]
  | ι w =>
    simp only [tau, CliffordAlgebra.reverse_ι]
    rw [show (ι (0 : QuadraticForm F (H1 F n)) w : S F n) = ExteriorAlgebra.ι F w from rfl,
      s3_bcS_ι]
    exact (CliffordAlgebra.reverse_ι _).symm
  | mul a b ha hb =>
    simp only [tau, CliffordAlgebra.reverse.map_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit [CharZero F] [CharZero F'] in
theorem s3_integral_bcS (s : S F n) :
    integral F' n (bcS F F' n s) = algebraMap F F' (integral F n s) := by
  simp only [integral, Module.Basis.coord_apply]
  exact s3_bcS_repr F F' s Finset.univ

omit [CharZero F] [CharZero F'] in
/-- The Mukai pairing commutes with change of coefficients. -/
theorem s3_mukai_bcS (s t : S F n) :
    mukai F' n (bcS F F' n s) (bcS F F' n t) = algebraMap F F' (mukai F n s t) := by
  rw [s3_mukai_apply, s3_mukai_apply, ← s3_bcS_tau, ← map_mul, s3_integral_bcS]

theorem s3_bcC_reverse (x : C F n) :
    bcC F F' n (CliffordAlgebra.reverse x) = CliffordAlgebra.reverse (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.reverse.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (C F' n), CliffordAlgebra.reverse.commutes]
  | ι v => rw [CliffordAlgebra.reverse_ι, s3_bcC_ι, CliffordAlgebra.reverse_ι]
  | mul a b ha hb => rw [CliffordAlgebra.reverse.map_mul, map_mul, map_mul, ha, hb,
      CliffordAlgebra.reverse.map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end S3MukaiBc

theorem s3_bcC_trans (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
    [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F'']
    {n : ℕ} (x : C F n) : bcC F' F'' n (bcC F F' n x) = bcC F F'' n x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι v => rw [s3_bcC_ι, s3_bcC_ι, s3_bcC_ι, s3_bcV_trans]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- Rational endomorphisms of `V_K` commute with `σ`. -/
theorem s3_ext_σV {n : ℕ} {d : ℚ} (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V (Kd d) n) :
    s3_ext ℚ (Kd d) n A (σV n d v) = σV n d (s3_ext ℚ (Kd d) n A v) := by
  show s3_ext ℚ (Kd d) n A (conjV (Kd.σ d) n v) = conjV (Kd.σ d) n (s3_ext ℚ (Kd d) n A v)
  rw [s3_conjV_eq, s3_conjV_eq]
  apply s3_conj_comm
  intro i j
  rw [← s3_bcV_basisV ℚ (Kd d), s3_ext_bcV, s3_bcV_repr, s3_σ_algebraMap]

/-- Descent of an eigenvalue: if `bcS t = μ bcS u` with `u ≠ 0` then `μ ∈ K` and `t = μ u`. -/
theorem s3_eigen_descent {n : ℕ} {d : ℚ} {t u : S (Kd d) n} (hu : u ≠ 0) {μ : ℂ}
    (h : bcS (Kd d) ℂ n t = μ • bcS (Kd d) ℂ n u) : ∃ l : Kd d, (l : ℂ) = μ ∧ t = l • u := by
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, (basisS (Kd d) n).repr u K₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu ((basisS (Kd d) n).repr.injective (by ext K; simp [hall K]))
  have hc : ∀ K, (((basisS (Kd d) n).repr t K : Kd d) : ℂ) =
      μ * (((basisS (Kd d) n).repr u K : Kd d) : ℂ) := by
    intro K
    have := congrArg (fun z => (basisS ℂ n).repr z K) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, s3_bcS_repr] at this
    exact this
  set l := (basisS (Kd d) n).repr t K₀ / (basisS (Kd d) n).repr u K₀ with hl
  have hlμ : (l : ℂ) = μ := by
    rw [hl, Subfield.coe_div, hc K₀, mul_div_assoc, div_self (by exact_mod_cast hK₀), mul_one]
  refine ⟨l, hlμ, ?_⟩
  apply (basisS (Kd d) n).repr.injective
  ext K
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Subfield.coe_mul, hlμ, hc K]


/-- The determinant of an endomorphism preserving complementary subspaces. -/
theorem s3_det_of_isCompl {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {p q : Submodule K M} (hpq : IsCompl p q) (T : M →ₗ[K] M)
    (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q) :
    LinearMap.det T = LinearMap.det (T.restrict hp) * LinearMap.det (T.restrict hq) := by
  set e := Submodule.prodEquivOfIsCompl p q hpq
  have h1 : T ∘ₗ (e : p × q →ₗ[K] M) =
      (e : p × q →ₗ[K] M) ∘ₗ LinearMap.prodMap (T.restrict hp) (T.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp [e, LinearMap.restrict_apply]
  have h2 : T = (e : p × q →ₗ[K] M) ∘ₗ LinearMap.prodMap (T.restrict hp) (T.restrict hq) ∘ₗ
      (e.symm : M →ₗ[K] p × q) := by
    rw [← LinearMap.comp_assoc, ← h1, LinearMap.comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  conv_lhs => rw [h2]
  rw [LinearMap.det_conj, LinearMap.det_prodMap]

/-- The determinant of the extension of `A` is the image of the determinant of `A`. -/
theorem s3_det_ext (F F' : Type*) [Field F] [Field F'] [Algebra F F'] {n : ℕ}
    (A : V F n →ₗ[F] V F n) :
    LinearMap.det (s3_ext F F' n A) = algebraMap F F' (LinearMap.det A) := by
  rw [s3_ext, LinearMap.det_toLin, ← LinearMap.det_toMatrix (basisV F n) A, RingHom.map_det]
  rfl

section S3SigmaLI

variable {n : ℕ} {d : ℚ}

theorem s3_σV_injective : Function.Injective (σV n d) :=
  Function.LeftInverse.injective s3_σV_σV

/-- `σ` preserves linear independence. -/
theorem s3_linearIndependent_σV {k : ℕ} {v : Fin k → V (Kd d) n}
    (hv : LinearIndependent (Kd d) v) : LinearIndependent (Kd d) (σV n d ∘ v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : σV n d (∑ i, Kd.σ d (g i) • v i) = 0 := by
    rw [map_sum]
    simp only [show ∀ i, σV n d (Kd.σ d (g i) • v i) = g i • σV n d (v i) from fun i => by
      show conjV (Kd.σ d) n _ = _
      rw [s3_conjV_smul, s3_σ_σ]]
    exact hg
  have h2 := s3_σV_injective (h1.trans (map_zero _).symm)
  intro i
  have := (Fintype.linearIndependent_iff.mp hv) _ h2 i
  rw [← s3_σ_σ (g i), this, map_zero]

end S3SigmaLI

/-- Transport of a restricted determinant along a `τ`-semilinear map sending a basis to a basis. -/
theorem s3_det_restrict_transport {K K' V V' : Type*} [Field K] [Field K'] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K' V'] (τ : K →+* K') (φ : V →+ V')
    (hφ : ∀ (c : K) (v : V), φ (c • v) = τ c • φ v) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Submodule K V} {W' : Submodule K' V'} (e : Module.Basis ι K W)
    (e' : Module.Basis ι K' W') (he : ∀ i, (e' i : V') = φ (e i)) (T : V →ₗ[K] V)
    (T' : V' →ₗ[K'] V') (hT : ∀ x ∈ W, T x ∈ W) (hT' : ∀ x ∈ W', T' x ∈ W')
    (hcomm : ∀ x ∈ W, T' (φ x) = φ (T x)) :
    LinearMap.det (T'.restrict hT') = τ (LinearMap.det (T.restrict hT)) := by
  rw [← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e', RingHom.map_det]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hexp : T'.restrict hT' (e' j) = ∑ k, τ (e.repr (T.restrict hT (e j)) k) • e' k := by
    apply Subtype.ext
    have h2 : (T.restrict hT (e j) : V) = ∑ k, e.repr (T.restrict hT (e j)) k • (e k : V) := by
      have := congrArg Subtype.val (e.sum_repr (T.restrict hT (e j)))
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    simp only [LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul, he]
    rw [hcomm _ (e j).2]
    have h3 : φ (T (e j)) = φ (∑ k, e.repr (T.restrict hT (e j)) k • (e k : V)) := by
      rw [← h2]; rfl
    rw [h3, map_sum]
    simp only [hφ]
    rfl
  rw [hexp, e'.repr_sum_self]

namespace KSecant

variable (P : KSecant n d)

/-- `(u₁, u₂)_S ≠ 0` (or `(u₂, u₁)_S ≠ 0`): `P` is non-isotropic and pure spinors are isotropic. -/
theorem s3_mukai_u₁₂ (hW : IsCompl P.W₁ P.W₂) (hiso : ¬ P.IsIsotropic) :
    mukai (Kd d) n P.u₁ P.u₂ ≠ 0 ∨ mukai (Kd d) n P.u₂ P.u₁ ≠ 0 := by
  have hn := s3_n_pos P
  by_contra h
  push Not at h
  obtain ⟨h12, h21⟩ := h
  apply hiso
  intro a ha b hb
  apply (algebraMap ℚ (Kd d)).injective
  rw [← s3_mukai_bcS, map_zero]
  obtain ⟨α₁, α₂, hα⟩ := Submodule.mem_span_pair.mp ((P.s3_mem_Pℚ_iff a).mp ha)
  obtain ⟨β₁, β₂, hβ⟩ := Submodule.mem_span_pair.mp ((P.s3_mem_Pℚ_iff b).mp hb)
  rw [← hα, ← hβ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    s3_mukai_self_of_pure hn P.isPure, s3_mukai_self_of_pure hn (P.s3_isPure₂ hW), h12, h21]
  ring


theorem s3_mem_W₁_of_eigen (hW : IsCompl P.W₁ P.W₂) {v : V (Kd d) n}
    (hv : P.ηK hW (Kd.sqrtNeg d) v = Kd.sqrtNeg d • v) : v ∈ P.W₁ := by
  have hs := s3_sqrtNeg_ne_zero (s3_d_pos P)
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, P.s3_ηK_W₁ hW _ hv₁, P.s3_ηK_W₂ hW _ hv₂, s3_σ_sqrtNeg] at hv
  have : (2 * Kd.sqrtNeg d) • v₂ = 0 := by
    have e : (2 * Kd.sqrtNeg d) • v₂ = Kd.sqrtNeg d • (v₁ + v₂) -
        (Kd.sqrtNeg d • v₁ + -Kd.sqrtNeg d • v₂) := by module
    rw [e, hv, sub_self]
  rw [(smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs), add_zero]
  exact hv₁

theorem s3_mem_W₂_of_eigen (hW : IsCompl P.W₁ P.W₂) {v : V (Kd d) n}
    (hv : P.ηK hW (Kd.sqrtNeg d) v = -Kd.sqrtNeg d • v) : v ∈ P.W₂ := by
  have hs := s3_sqrtNeg_ne_zero (s3_d_pos P)
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, P.s3_ηK_W₁ hW _ hv₁, P.s3_ηK_W₂ hW _ hv₂, s3_σ_sqrtNeg] at hv
  have : (2 * Kd.sqrtNeg d) • v₁ = 0 := by
    have e : (2 * Kd.sqrtNeg d) • v₁ = (Kd.sqrtNeg d • v₁ + -Kd.sqrtNeg d • v₂) -
        (-Kd.sqrtNeg d) • (v₁ + v₂) := by module
    rw [e, hv, sub_self]
  rw [(smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hs), zero_add]
  exact hv₂

/-- A rational `g` commuting with `f` preserves `W₁` and `W₂`. -/
theorem s3_ext_preserves (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x, g (P.fη hW x) = P.fη hW (g x)) :
    (∀ v ∈ P.W₁, s3_ext ℚ (Kd d) n g v ∈ P.W₁) ∧ (∀ v ∈ P.W₂, s3_ext ℚ (Kd d) n g v ∈ P.W₂) := by
  have hc : s3_ext ℚ (Kd d) n g ∘ₗ P.ηK hW (Kd.sqrtNeg d) =
      P.ηK hW (Kd.sqrtNeg d) ∘ₗ s3_ext ℚ (Kd d) n g := by
    rw [← P.s3_ext_fη hW, ← s3_ext_comp, ← s3_ext_comp]
    congr 1
    exact LinearMap.ext hg
  have hc' : ∀ v, P.ηK hW (Kd.sqrtNeg d) (s3_ext ℚ (Kd d) n g v) =
      s3_ext ℚ (Kd d) n g (P.ηK hW (Kd.sqrtNeg d) v) := fun v =>
    (LinearMap.congr_fun hc v).symm
  constructor
  · intro v hv
    apply P.s3_mem_W₁_of_eigen hW
    rw [hc', P.s3_ηK_W₁ hW _ hv, map_smul]
  · intro v hv
    apply P.s3_mem_W₂_of_eigen hW
    rw [hc', P.s3_ηK_W₂ hW _ hv, map_smul, s3_σ_sqrtNeg]

/-- A basis of `W₁`. -/
noncomputable def s3_eW₁ : Module.Basis (Fin (2 * n)) (Kd d) P.W₁ :=
  Module.finBasisOfFinrankEq (Kd d) P.W₁ P.isPure.2.2

/-- The conjugate basis `σ(e)` of `W₂`. -/
noncomputable def s3_eW₂ (hW : IsCompl P.W₁ P.W₂) : Module.Basis (Fin (2 * n)) (Kd d) P.W₂ :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => (⟨σV n d (P.s3_eW₁ i), P.s3_σV_mem_W₂ (P.s3_eW₁ i).2⟩ : P.W₂))
    (by
      apply LinearIndependent.of_comp P.W₂.subtype
      exact s3_linearIndependent_σV (n := n) (v := fun i => (P.s3_eW₁ i : V (Kd d) n))
        (P.s3_eW₁.linearIndependent.map' P.W₁.subtype (Submodule.ker_subtype _)))
    (by rw [Fintype.card_fin]; exact (P.s3_isPure₂ hW).2.2.symm)

theorem s3_eW₂_apply (hW : IsCompl P.W₁ P.W₂) (i : Fin (2 * n)) :
    (P.s3_eW₂ hW i : V (Kd d) n) = σV n d (P.s3_eW₁ i) := by
  simp [s3_eW₂]


/-- `span_ℂ(bcV(W)) = span_ℂ(bcV(e))` for a basis `e` of `W`. -/
theorem _root_.WeilClasses.s3_span_bcV_basis {W : Submodule (Kd d) (V (Kd d) n)} {ι : Type*}
    [Fintype ι] (e : Module.Basis ι (Kd d) W) :
    Submodule.span ℂ (bcV (Kd d) ℂ n '' W) =
      Submodule.span ℂ (Set.range fun i => bcV (Kd d) ℂ n (e i)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, e.repr ⟨w, hw⟩ i • (e i : V (Kd d) n) := by
      have := congrArg Subtype.val (e.sum_repr ⟨w, hw⟩)
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, ← algebraMap_smul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨_, (e i).2, rfl⟩

/-- A basis of `W'` from a spanning family of the right size. -/
noncomputable def _root_.WeilClasses.s3_basisOfSpan {ι : Type*} [Fintype ι]
    {W : Submodule ℂ (V ℂ n)} (b : ι → V ℂ n) (hb : ∀ i, b i ∈ W)
    (hspan : W = Submodule.span ℂ (Set.range b)) (hcard : Fintype.card ι = Module.finrank ℂ W) :
    Module.Basis ι ℂ W :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (⟨b i, hb i⟩ : W)) (by
    intro x _
    have hx : (x : V ℂ n) ∈ Submodule.span ℂ (Set.range b) := hspan ▸ x.2
    have hmap : Submodule.span ℂ (Set.range b) =
        (Submodule.span ℂ (Set.range fun i => (⟨b i, hb i⟩ : W))).map W.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]) hcard

theorem _root_.WeilClasses.s3_basisOfSpan_apply {ι : Type*} [Fintype ι]
    {W : Submodule ℂ (V ℂ n)} (b : ι → V ℂ n) (hb : ∀ i, b i ∈ W)
    (hspan : W = Submodule.span ℂ (Set.range b)) (hcard : Fintype.card ι = Module.finrank ℂ W)
    (i : ι) : (s3_basisOfSpan b hb hspan hcard i : V ℂ n) = b i := by
  simp [s3_basisOfSpan]

/-- `det(g|W₂) = σ(det(g|W₁))` for a rational `g` commuting with `f` (the proof of Lemma 3.1.2:
the matrix of `g|W₂` in the basis `σ(β)` is `σ(M)`). -/
theorem s3_det_W₂ (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x, g (P.fη hW x) = P.fη hW (g x)) :
    LinearMap.det ((s3_ext ℚ (Kd d) n g).restrict (P.s3_ext_preserves hW g hg).2) =
      Kd.σ d (LinearMap.det ((s3_ext ℚ (Kd d) n g).restrict (P.s3_ext_preserves hW g hg).1)) :=
  s3_det_restrict_transport (Kd.σ d : Kd d →+* Kd d) (σV n d)
    (fun c v => s3_conjV_smul (n := n) (Kd.σ d) c v) P.s3_eW₁ (P.s3_eW₂ hW)
    (P.s3_eW₂_apply hW) _ _ _ _ (fun x _ => s3_ext_σV g x)

theorem s3_finrank_W₁ℂ' (hW : IsCompl P.W₁ P.W₂) :
    Fintype.card (Fin (2 * n)) = Module.finrank ℂ P.W₁ℂ := by
  rw [Fintype.card_fin, P.s3_finrank_W₁ℂ hW]

/-- The basis `bcV(e)` of `W_{1,ℂ}`. -/
noncomputable def s3_eW₁ℂ (hW : IsCompl P.W₁ P.W₂) : Module.Basis (Fin (2 * n)) ℂ P.W₁ℂ :=
  s3_basisOfSpan (fun i => bcV (Kd d) ℂ n (P.s3_eW₁ i))
    (fun i => Submodule.subset_span ⟨_, (P.s3_eW₁ i).2, rfl⟩)
    (by rw [W₁ℂ]; exact s3_span_bcV_basis P.s3_eW₁) (P.s3_finrank_W₁ℂ' hW)


/-- A rational `g` commuting with `f` preserves `W_{1,ℂ}` and `W_{2,ℂ}`. -/
theorem s3_extℂ_preserves (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x, g (P.fη hW x) = P.fη hW (g x)) :
    (∀ v ∈ P.W₁ℂ, s3_ext ℚ ℂ n g v ∈ P.W₁ℂ) ∧ (∀ v ∈ P.W₂ℂ, s3_ext ℚ ℂ n g v ∈ P.W₂ℂ) := by
  obtain ⟨h₁, h₂⟩ := P.s3_ext_preserves hW g hg
  constructor
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      rw [← s3_ext_trans ℚ (Kd d) ℂ, s3_ext_bcV]
      exact Submodule.subset_span ⟨_, h₁ w hw, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      rw [← s3_ext_trans ℚ (Kd d) ℂ, s3_ext_bcV]
      exact Submodule.subset_span ⟨_, h₂ w hw, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem s3_det_W₁ℂ (hW : IsCompl P.W₁ P.W₂) (g : V ℚ n →ₗ[ℚ] V ℚ n)
    (hg : ∀ x, g (P.fη hW x) = P.fη hW (g x)) :
    LinearMap.det ((s3_ext ℚ ℂ n g).restrict (P.s3_extℂ_preserves hW g hg).1) =
      ((LinearMap.det ((s3_ext ℚ (Kd d) n g).restrict (P.s3_ext_preserves hW g hg).1) :
        Kd d) : ℂ) :=
  s3_det_restrict_transport (algebraMap (Kd d) ℂ) (bcV (Kd d) ℂ n).toAddMonoidHom
    (fun c v => by simp only [LinearMap.toAddMonoidHom_coe, map_smul, algebraMap_smul])
    P.s3_eW₁ (P.s3_eW₁ℂ hW) (fun i => s3_basisOfSpan_apply _ _ _ _ i) _ _ _ _
    (fun x _ => by
      simp only [LinearMap.toAddMonoidHom_coe]
      rw [← s3_ext_trans ℚ (Kd d) ℂ, s3_ext_bcV])


end KSecant

section S3SpinorNorm

/-- `bcC` sends `C(V_F)^even` into `C(V_{F'})^even`. -/
theorem s3_bcC_mem_even {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] {n : ℕ} {x : C F n} (hx : x ∈ evenOdd (Q F n) 0) :
    bcC F F' n x ∈ evenOdd (Q F' n) 0 := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n)]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
      simpa only [map_mul, s3_bcC_ι, zero_add] using
        SetLike.mul_mem_graded
          (ι_mul_ι_mem_evenOdd_zero (Q F' n) (bcV F F' n m₁) (bcV F F' n m₂)) hx

/-- If `τ(x) x = c`, then `(m_x s, m_x t)_S = c (s, t)_S`. -/
theorem s3_mukai_m_m {F : Type*} [Field F] [CharZero F] {n : ℕ} (x : C F n) (c : F)
    (hx : CliffordAlgebra.reverse x * x = algebraMap F (C F n) c) (s t : S F n) :
    mukai F n (m F n x s) (m F n x t) = c * mukai F n s t := by
  rw [s3_mukai_m, ← Module.End.mul_apply, ← map_mul, hx, AlgHom.commutes,
    Module.algebraMap_end_apply, map_smul, smul_eq_mul]

/-- The determinant of a restriction depends only on the map and the subspace. -/
theorem s3_det_restrict_congr {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {A B : M →ₗ[K] M} {p q : Submodule K M} (hAB : A = B) (hpq : p = q)
    (hA : ∀ x ∈ p, A x ∈ p) (hB : ∀ x ∈ q, B x ∈ q) :
    LinearMap.det (A.restrict hA) = LinearMap.det (B.restrict hB) := by
  subst hAB hpq
  rfl

/-- If `y = a x_ℂ ∈ Spin(V_ℂ)` for a rational `x` with `x v x⁻¹ = T v`, then `ρ(y) = T_ℂ`. -/
theorem s3_rho_eq_ext {n : ℕ} {T : V ℚ n →ₗ[ℚ] V ℚ n} {X0 X0i : C ℚ n}
    (hconj : ∀ w, X0 * ι (Q ℚ n) w * X0i = ι (Q ℚ n) (T w))
    (y : Spin ℂ n) {a : ℂ} (ha : a ≠ 0)
    (hy : (y : C ℂ n) = algebraMap ℂ (C ℂ n) a * bcC ℚ ℂ n X0)
    (hXXi : bcC ℚ ℂ n X0 * bcC ℚ ℂ n X0i = 1) :
    (rho ℂ n y : V ℂ n →ₗ[ℂ] V ℂ n) = s3_ext ℚ ℂ n T := by
  have hstar : star (y : C ℂ n) = algebraMap ℂ (C ℂ n) a⁻¹ * bcC ℚ ℂ n X0i := by
    have h1 : star (y : C ℂ n) * (y : C ℂ n) = 1 := spinGroup.star_mul_self_of_mem y.2
    have h2 : (y : C ℂ n) * (algebraMap ℂ (C ℂ n) a⁻¹ * bcC ℚ ℂ n X0i) = 1 := by
      rw [hy, ← Algebra.smul_def, ← Algebra.smul_def, smul_mul_smul_comm, mul_inv_cancel₀ ha,
        one_smul, hXXi]
    calc star (y : C ℂ n)
        = star (y : C ℂ n) * ((y : C ℂ n) * (algebraMap ℂ (C ℂ n) a⁻¹ * bcC ℚ ℂ n X0i)) := by
          rw [h2, mul_one]
      _ = algebraMap ℂ (C ℂ n) a⁻¹ * bcC ℚ ℂ n X0i := by rw [← mul_assoc, h1, one_mul]
  refine (basisV ℂ n).ext fun i => ?_
  rw [← s3_bcV_basisV ℚ ℂ, s3_ext_bcV]
  apply CliffordAlgebra.ι_injective (Q ℂ n)
  simp only [LinearEquiv.coe_coe]
  rw [ι_rho, hstar, hy, ← Algebra.smul_def, ← Algebra.smul_def, smul_mul_assoc, smul_mul_assoc,
    mul_smul_comm, smul_smul, mul_inv_cancel₀ ha, one_smul,
    show bcC ℚ ℂ n X0 * ι (Q ℂ n) (bcV ℚ ℂ n (basisV ℚ n i)) * bcC ℚ ℂ n X0i =
      bcC ℚ ℂ n (X0 * ι (Q ℚ n) (basisV ℚ n i) * X0i) by rw [map_mul, map_mul, s3_bcC_ι],
    hconj, s3_bcC_ι]

end S3SpinorNorm

namespace KSecant

variable (P : KSecant n d)

/-- An endomorphism leaving `H` invariant is an isometry of `(·,·)_V` (the real part of `H`). -/
theorem s3_pairing_of_hermH (hW : IsCompl P.W₁ P.W₂) {g : V ℚ n → V ℚ n}
    (hg : ∀ x y, P.hermH hW (g x) (g y) = P.hermH hW x y) (x y : V ℚ n) :
    pairing ℚ n (g x) (g y) = pairing ℚ n x y := by
  have hd := s3_d_pos P
  have key : ∀ a b : V ℚ n, P.hermH hW a b + Kd.σ d (P.hermH hW a b) =
      algebraMap ℚ (Kd d) (2 * d * pairing ℚ n a b) := by
    intro a b
    simp only [hermH, map_add, map_mul, s3_σ_algebraMap, s3_σ_sqrtNeg, map_ofNat]
    ring
  have h := key (g x) (g y)
  rw [hg, key] at h
  have h2 := (algebraMap ℚ (Kd d)).injective h
  have h2d : (2 * d) ≠ 0 := by positivity
  exact (mul_left_cancel₀ h2d h2).symm

/-- The elements of `SU(V_ℚ, H)` have `ℚ`-determinant `det(g|W₁) σ(det(g|W₁)) = 1` (the proof of
Lemma 3.1.2). -/
theorem s3_det_eq_one_of_SUH (hW : IsCompl P.W₁ P.W₂) {g : V ℚ n ≃ₗ[ℚ] V ℚ n}
    (hg : g ∈ P.SUH hW) : LinearMap.det (g : V ℚ n →ₗ[ℚ] V ℚ n) = 1 := by
  obtain ⟨⟨hgf, -⟩, hg1⟩ := hg
  obtain ⟨hp₁, hp₂⟩ := P.s3_ext_preserves hW (g : V ℚ n →ₗ[ℚ] V ℚ n) hgf
  have hdet₁ : LinearMap.det ((s3_ext ℚ (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict hp₁) = 1 := by
    obtain ⟨_, h1⟩ := hg1
    exact h1
  have hdet₂ : LinearMap.det ((s3_ext ℚ (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict hp₂) = 1 := by
    rw [P.s3_det_W₂ hW _ hgf, hdet₁, map_one]
  apply (algebraMap ℚ (Kd d)).injective
  rw [← s3_det_ext, s3_det_of_isCompl hW _ hp₁ hp₂, hdet₁, hdet₂, mul_one, map_one]

/-- The core of the gap repair for Lemma 3.1.2: let `g ∈ SU(V_ℚ, H)`, let `x ∈ C(V_ℚ)` be invertible
with `x v x⁻¹ = g(v)` and `τ(x) x = N ∈ ℚ`, and let `y = a x_ℂ ∈ Spin(V_ℂ)`. Then `N` is a square.
By [Chevalley, III.3.2, III.4.5] `y u₁ = c u₁` with `c² = det(g|W₁) = 1`; so `x u₁ = λ u₁` with
`λ ∈ K`, `λ² = N`; by Galois conjugation `x u₂ = σ(λ) u₂`, and the Mukai pairing (`P` is
non-isotropic) gives `N = λ σ(λ)`. Hence `λ = σ(λ) ∈ ℚ`. -/
theorem s3_norm_isSquare (hW : IsCompl P.W₁ P.W₂) (hiso : ¬ P.IsIsotropic)
    {g : V ℚ n ≃ₗ[ℚ] V ℚ n} (hg : g ∈ P.SUH hW) {X0 X0i : C ℚ n} (hXX : X0 * X0i = 1) {N : ℚ}
    (hN : CliffordAlgebra.reverse X0 * X0 = algebraMap ℚ (C ℚ n) N)
    (hconj : ∀ w, X0 * ι (Q ℚ n) w * X0i = ι (Q ℚ n) (g w))
    (y : Spin ℂ n) {a : ℂ} (ha : a ≠ 0)
    (hy : (y : C ℂ n) = algebraMap ℂ (C ℂ n) a * bcC ℚ ℂ n X0) :
    ∃ q : ℚ, N = q * q := by
  have hd := s3_d_pos P
  have hgf : ∀ x, (g : V ℚ n →ₗ[ℚ] V ℚ n) (P.fη hW x) = P.fη hW ((g : V ℚ n →ₗ[ℚ] V ℚ n) x) :=
    hg.1.1
  obtain ⟨hp₁, -⟩ := P.s3_ext_preserves hW (g : V ℚ n →ₗ[ℚ] V ℚ n) hgf
  have hdet₁ : LinearMap.det ((s3_ext ℚ (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict hp₁) = 1 := by
    obtain ⟨_, h1⟩ := hg.2
    exact h1
  -- `ρ(y) = g_ℂ`
  have hXXi : bcC ℚ ℂ n X0 * bcC ℚ ℂ n X0i = 1 := by rw [← map_mul, hXX, map_one]
  have hrho : (rho ℂ n y : V ℂ n →ₗ[ℂ] V ℂ n) = s3_ext ℚ ℂ n (g : V ℚ n →ₗ[ℚ] V ℚ n) :=
    s3_rho_eq_ext hconj y ha hy hXXi
  -- [Chevalley, III.3.2, III.4.5]: `y u_{1,ℂ} = c₁ u_{1,ℂ}` with `c₁² = det(g|W₁) = 1`
  have hpres := (P.s3_extℂ_preserves hW (g : V ℚ n →ₗ[ℚ] V ℚ n) hgf).1
  have hT₁ : ∀ v ∈ ann ℂ n (bcS (Kd d) ℂ n P.u₁),
      rho ℂ n y v ∈ ann ℂ n (bcS (Kd d) ℂ n P.u₁) := by
    intro v hv
    rw [← P.s3_W₁ℂ_eq_ann hW] at hv ⊢
    have := hpres v hv
    rwa [← hrho] at this
  obtain ⟨c₁, hc₁, hc₁2⟩ := chevalley_III_3_2_III_4_5 ℂ n _ (P.s3_isPure₁ℂ hW) y hT₁
  have hc₁' : c₁ ^ 2 = 1 := by
    rw [hc₁2, s3_det_restrict_congr hrho (P.s3_W₁ℂ_eq_ann hW).symm hT₁ hpres,
      P.s3_det_W₁ℂ hW _ hgf, hdet₁]
    rfl
  -- `a² N = 1`, as `y ∈ Spin(V_ℂ)` has norm `1`
  have hrevX : CliffordAlgebra.reverse (bcC ℚ ℂ n X0) * bcC ℚ ℂ n X0 =
      algebraMap ℂ (C ℂ n) (algebraMap ℚ ℂ N) := by
    rw [← s3_bcC_reverse, ← map_mul, hN, AlgHom.commutes,
      IsScalarTower.algebraMap_apply ℚ ℂ (C ℂ n)]
  have haN : a * a * algebraMap ℚ ℂ N = 1 := by
    have h1 : star (y : C ℂ n) * (y : C ℂ n) = 1 := spinGroup.star_mul_self_of_mem y.2
    rw [CliffordAlgebra.star_def, CliffordAlgebra.involute_eq_of_mem_even
      (spinGroup.mem_even y.2), hy, ← Algebra.smul_def, map_smul, smul_mul_smul_comm, hrevX,
      Algebra.smul_def, ← map_mul] at h1
    exact CliffordAlgebra.algebraMap_injective (Q ℂ n) (h1.trans (map_one _).symm)
  -- `x u_{1,ℂ} = a⁻¹ c₁ u_{1,ℂ}`
  have hXu₁ : m ℂ n (bcC ℚ ℂ n X0) (bcS (Kd d) ℂ n P.u₁) =
      (a⁻¹ * c₁) • bcS (Kd d) ℂ n P.u₁ := by
    have hX : bcC ℚ ℂ n X0 = algebraMap ℂ (C ℂ n) a⁻¹ * (y : C ℂ n) := by
      rw [hy, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [hX, map_mul, Module.End.mul_apply, hc₁, AlgHom.commutes, Module.algebraMap_end_apply,
      smul_smul]
  -- descent to `K`: `x u₁ = l₁ u₁` with `l₁ ∈ K`
  have hdesc : bcS (Kd d) ℂ n (m (Kd d) n (bcC ℚ (Kd d) n X0) P.u₁) =
      (a⁻¹ * c₁) • bcS (Kd d) ℂ n P.u₁ := by
    rw [← s3_m_bcC (Kd d) ℂ, s3_bcC_trans ℚ (Kd d) ℂ]
    exact hXu₁
  obtain ⟨l₁, hl₁, hxu₁⟩ := s3_eigen_descent P.s3_u₁_ne_zero hdesc
  -- Galois conjugation: `x u₂ = σ(l₁) u₂`
  have hxu₂ : m (Kd d) n (bcC ℚ (Kd d) n X0) P.u₂ = Kd.σ d l₁ • P.u₂ := by
    show m (Kd d) n (bcC ℚ (Kd d) n X0) (conjS (Kd.σ d) n P.u₁) =
      Kd.σ d l₁ • conjS (Kd.σ d) n P.u₁
    rw [s3_m_bcC_conjS ℚ (Kd.σ d) s3_σhc, hxu₁, s3_conjS_smul]
  -- the Mukai pairing: `l₁ σ(l₁) = N`
  have hrevK : CliffordAlgebra.reverse (bcC ℚ (Kd d) n X0) * bcC ℚ (Kd d) n X0 =
      algebraMap (Kd d) (C (Kd d) n) (algebraMap ℚ (Kd d) N) := by
    rw [← s3_bcC_reverse, ← map_mul, hN, AlgHom.commutes,
      IsScalarTower.algebraMap_apply ℚ (Kd d) (C (Kd d) n)]
  have hnorm : l₁ * Kd.σ d l₁ = algebraMap ℚ (Kd d) N := by
    have h12 := s3_mukai_m_m _ _ hrevK P.u₁ P.u₂
    have h21 := s3_mukai_m_m _ _ hrevK P.u₂ P.u₁
    rw [hxu₁, hxu₂] at h12 h21
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h12 h21
    rcases P.s3_mukai_u₁₂ hW hiso with h | h
    · apply mul_right_cancel₀ h
      linear_combination h12
    · apply mul_right_cancel₀ h
      linear_combination h21
  -- `l₁² = N`
  have hsq : l₁ * l₁ = algebraMap ℚ (Kd d) N := by
    apply Subtype.ext
    rw [Subfield.coe_mul, hl₁, s3_coe_algebraMap]
    rw [eq_ratCast] at haN
    field_simp
    linear_combination hc₁' - haN
  by_cases hl₁0 : l₁ = 0
  · refine ⟨0, (algebraMap ℚ (Kd d)).injective ?_⟩
    rw [← hsq, hl₁0, mul_zero, mul_zero, map_zero]
  · have hσ : Kd.σ d l₁ = l₁ := mul_left_cancel₀ hl₁0 (hnorm.trans hsq.symm)
    have hq := s3_eq_algebraMap_of_σ_eq hd l₁ hσ
    refine ⟨Kd.ratPart d l₁, (algebraMap ℚ (Kd d)).injective ?_⟩
    rw [← hsq, map_mul, ← hq]

/-- **Gap repair for Lemma 3.1.2**: every element of `SU(V_ℚ, H)` lies in `SO_+(V_ℚ)`: its
spinor norm is trivial. -/
theorem s3_mem_SOplus_of_SUH (hW : IsCompl P.W₁ P.W₂) (hiso : ¬ P.IsIsotropic)
    {g : V ℚ n ≃ₗ[ℚ] V ℚ n} (hg : g ∈ P.SUH hW) : g ∈ SOplus ℚ n := by
  have hn := s3_n_pos P
  have hQnd : (Q ℚ n).Nondegenerate := s3_Q_nondegenerate
  have := s3_nontrivial_V (F := ℂ) hn
  have hv : ∃ v, IsUnit (Q ℂ n v) := (s3_Q_nondegenerate (F := ℂ)).exists_isUnit
  -- `g` is an isometry of determinant `1`
  have hpair : ∀ x y, pairing ℚ n (g x) (g y) = pairing ℚ n x y :=
    P.s3_pairing_of_hermH hW hg.1.2
  have hQg : ∀ v, Q ℚ n (g v) = Q ℚ n v := by
    intro v
    have h := hpair v v
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      Nat.cast_ofNat] at h
    linarith
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q ℚ n) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hQg
  have hgdet : LinearEquiv.det g = 1 :=
    Units.ext (by rw [LinearEquiv.coe_det]; exact P.s3_det_eq_one_of_SUH hW hg)
  have hgSO : g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℚ n) :=
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨hgO, hgdet⟩
  -- a Lipschitz lift `x` of `g`; it is even
  obtain ⟨x, hx⟩ := lipschitzToOrthogonal_surjective (Q ℚ n) hQnd ⟨g, hgO⟩
  have hxeven : ((x : (C ℚ n)ˣ) : C ℚ n) ∈ evenOdd (Q ℚ n) 0 := by
    rw [← even_toSubmodule, Subalgebra.mem_toSubmodule]
    exact mem_even_of_det_lipschitzToOrthogonal_eq_one (Q ℚ n) x (by
      rw [hx, QuadraticMap.orthogonalDet_apply]; exact hgdet)
  have hconj : ∀ w, ((x : (C ℚ n)ˣ) : C ℚ n) * ι (Q ℚ n) w *
      (((x : (C ℚ n)ˣ)⁻¹ : (C ℚ n)ˣ) : C ℚ n) = ι (Q ℚ n) (g w) := by
    intro w
    have h1 := ι_lipschitzVectorAction_apply x w
    rw [CliffordAlgebra.involute_eq_of_mem_even hxeven, ← coe_lipschitzToOrthogonal_apply, hx] at h1
    exact h1.symm
  -- over `ℂ`, a scalar multiple `y = a x_ℂ` of `x` is in `Spin(V_ℂ)`
  obtain ⟨xℂ, hxℂ⟩ : ∃ xℂ : lipschitzGroup (Q ℂ n),
      ((xℂ : (C ℂ n)ˣ) : C ℂ n) = bcC ℚ ℂ n ((x : (C ℚ n)ˣ) : C ℚ n) :=
    ⟨lipschitzGroupMapOf (bcC ℚ ℂ n).toRingHom (bcV ℚ ℂ n) (s3_bcC_ι ℚ ℂ) x, by
      rw [coe_lipschitzGroupMapOf_apply]; rfl⟩
  have hsqℂ : IsSquare (cliffordNorm (Q ℂ n) xℂ) := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self ((cliffordNorm (Q ℂ n) xℂ : ℂˣ) : ℂ)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hz.trans (mul_zero 0))
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  obtain ⟨a, hy⟩ := (exists_scalarUnits_mul_mem_spinGroup_iff hv xℂ).mpr
    ⟨by rw [hxℂ]; exact s3_bcC_mem_even hxeven, hsqℂ⟩
  have hyc : (((scalarUnits (Q ℂ n) hv a * xℂ : lipschitzGroup (Q ℂ n)) : (C ℂ n)ˣ) : C ℂ n) =
      algebraMap ℂ (C ℂ n) (a : ℂ) * bcC ℚ ℂ n ((x : (C ℚ n)ˣ) : C ℚ n) := by
    rw [Subgroup.coe_mul, Units.val_mul, coe_scalarUnits, hxℂ]
  -- the Clifford norm of `x` is a square
  obtain ⟨q, hq⟩ := P.s3_norm_isSquare hW hiso hg (Units.mul_inv _)
    (reverse_mul_self_eq_algebraMap_cliffordNorm x) hconj ⟨_, hy⟩ a.ne_zero hyc
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact Units.ne_zero (cliffordNorm (Q ℚ n) x) (by rw [hq, mul_zero])
  have hsq : IsSquare (cliffordNorm (Q ℚ n) x) := ⟨Units.mk0 q hq0, Units.ext hq⟩
  -- so the spinor norm of `g` is trivial, and `g ∈ ρ(Spin(V_ℚ))`
  have hker : (⟨g, hgSO⟩ : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℚ n)) ∈
      (spinorNorm (Q ℚ n) hQnd).ker := by
    rw [MonoidHom.mem_ker, spinorNorm_apply]
    have : QuadraticMap.specialOrthogonalToOrthogonal (Q ℚ n) ⟨g, hgSO⟩ =
        lipschitzToOrthogonal (Q ℚ n) x := by
      rw [hx]; exact Subtype.ext (QuadraticMap.coe_specialOrthogonalToOrthogonal _)
    rw [this, orthogonalSpinorNorm_lipschitzToOrthogonal, TauCeti.squareClassHom_apply,
      ofAdd_eq_one, TauCeti.squareClass_eq_zero_iff]
    exact hsq
  rw [← range_spinToSpecialOrthogonal_eq_ker_spinorNorm] at hker
  obtain ⟨s, hs⟩ := hker
  refine (mem_SOplus_iff ℚ n g).mpr ⟨s, LinearEquiv.ext fun v => ?_⟩
  have := congrArg
    (fun h : TauCeti.QuadraticMap.specialOrthogonalGroup (Q ℚ n) => (h : V ℚ n ≃ₗ[ℚ] V ℚ n) v) hs
  simp only [coe_spinToSpecialOrthogonal_apply] at this
  exact this

theorem s3_SOplusf_le_SUH (hW : IsCompl P.W₁ P.W₂) : P.SOplusf hW ≤ P.SUH hW := by
  rintro g ⟨hg1, hg2, hg3, -⟩
  exact ⟨⟨hg2, fun x y => P.s3_hermH_of_isometry hW g (s3_pairing_of_mem_SOplus hg1) hg2 x y⟩,
    hg3⟩

theorem s3_SUH_le_SOplusf (hW : IsCompl P.W₁ P.W₂) (hiso : ¬ P.IsIsotropic) :
    P.SUH hW ≤ P.SOplusf hW := by
  intro g hg
  have hgf : ∀ x, (g : V ℚ n →ₗ[ℚ] V ℚ n) (P.fη hW x) = P.fη hW ((g : V ℚ n →ₗ[ℚ] V ℚ n) x) :=
    hg.1.1
  obtain ⟨hp₁, hp₂⟩ := P.s3_ext_preserves hW (g : V ℚ n →ₗ[ℚ] V ℚ n) hgf
  have h1 : LinearMap.det ((s3_ext ℚ (Kd d) n (g : V ℚ n →ₗ[ℚ] V ℚ n)).restrict hp₁) = 1 := by
    obtain ⟨_, h⟩ := hg.2
    exact h
  exact ⟨P.s3_mem_SOplus_of_SUH hW hiso hg, hg.1.1, hg.2, hp₂,
    (P.s3_det_W₂ hW _ hgf).trans (by rw [h1, map_one])⟩

theorem s3_SOplusf_eq_SUH (hW : IsCompl P.W₁ P.W₂) (hiso : ¬ P.IsIsotropic) :
    P.SOplusf hW = P.SUH hW :=
  le_antisymm (P.s3_SOplusf_le_SUH hW) (P.s3_SUH_le_SOplusf hW hiso)

end KSecant

/-! ## Lemma 3.1.2 -/

/-- **Lemma 3.1.2** (`lemma-su-3-3`), Hermitian symmetry: `H(x, y) = σ(H(y, x))`. Standing
assumption: Assumption 2.4.1. -/
theorem lemma3_1_2_hermitian (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (x y : V ℚ n) :
    P.hermH hP.isCompl x y = Kd.σ d (P.hermH hP.isCompl y x) :=
  P.s3_hermH_hermitian hP.isCompl x y

/-- **Lemma 3.1.2** (`lemma-su-3-3`), `K`-linearity in the second variable:
`H(x, η_λ(y)) = λ H(x, y)` for `λ ∈ K`. -/
theorem lemma3_1_2_linear (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (l : Kd d) (x y : V ℚ n) :
    P.hermH hP.isCompl x (P.η hP.isCompl l y) = l * P.hermH hP.isCompl x y :=
  P.s3_hermH_η_right hP.isCompl l x y

/-- **Lemma 3.1.2** (`lemma-su-3-3`): `H` is `SO_+(V_ℚ)_f`-invariant. -/
theorem lemma3_1_2_invariant (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (g : V ℚ n ≃ₗ[ℚ] V ℚ n) (hg : g ∈ P.SOplusf hP.isCompl)
    (x y : V ℚ n) : P.hermH hP.isCompl (g x) (g y) = P.hermH hP.isCompl x y :=
  -- `f` centralizes `SO_+(V_ℚ)_f`, whose elements are isometries of `(·,·)_V`.
  P.s3_hermH_of_isometry hP.isCompl g (s3_pairing_of_mem_SOplus hg.1) hg.2.1 x y

/-- **Lemma 3.1.2** (`lemma-su-3-3`): the signature of `H` is `(n, n)`. -/
theorem lemma3_1_2_signature (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) : P.HasSignature hP.isCompl n n :=
  P.s3_hasSignature hP.isCompl

/-- **Lemma 3.1.2** (`lemma-su-3-3`), last sentence: the group `SO_+(V_ℚ)_f` is a finite index
subgroup of `SU(V_ℚ, H)`.

Reading: `SU(V_ℚ, H)` is the special unitary group of `H` (`KSecant.SUH`: `K`-linear `H`-isometries
of `K`-determinant `1`), as its name and the dimension `(2n)² - 1` used in the proof of Lemma 4.0.2
say. The paper describes it as "the subgroup of `SL(V_ℚ)` leaving `H` invariant"; that subgroup is
all of `U(V_ℚ, H)` (every `H`-isometry has `ℚ`-determinant `Nm(det_K g) = 1`), in which `SO_+(V_ℚ)_f`
has infinite index (`det_K` maps `U(H)` onto the infinite group `K¹` of norm-one elements). The
proof's final step ("`det M` is a unit, and units are finite") needs `g` integral. See REPORT.md.
In fact the index is `1` (`lemma3_1_2_eq_SUH`).

Departure from the paper: the paper reduces the claim to `SO(V_ℚ)_f = SU(V_ℚ, H)` because "the norm
character has finitely many values on `SO(V_ℚ)`", and ends with "`det M` is a unit, and units are
finite". Over `ℚ` the first claim is false (the spinor norm maps `SO(V_ℚ)` onto the infinite group
`ℚ^×/(ℚ^×)²`: `V_ℚ` is hyperbolic) and the second is not available (`det M ∈ K` has norm `1` but need
not be integral); both hold for integral `g`. We keep the paper's computation
`det_ℚ g = det M · σ(det M)` (`KSecant.s3_det_eq_one_of_SUH`), so `SU(V_ℚ, H) ⊆ SO(V_ℚ)_f`, and
replace the norm-character step by a proof that the spinor norm of `g ∈ SU(V_ℚ, H)` is trivial
(`KSecant.s3_mem_SOplus_of_SUH`, `KSecant.s3_norm_isSquare`): for a Lipschitz lift `x` of `g` and
`y = a x ∈ Spin(V_ℂ)`, [Chevalley, III.3.2, III.4.5] (as in the proof of Lemma 3.1.1) gives
`y u₁ = c u₁` with `c² = det M = 1`; hence `x u₁ = λ u₁` with `λ ∈ K` and `λ² = N(x)`, `x u₂ = σ(λ) u₂`
(`u₂ = σ(u₁)`), and the Mukai pairing (`P` is non-isotropic) gives `N(x) = λ σ(λ)`. So `λ = σ(λ) ∈ ℚ`
and `N(x) = λ²` is a square. Thus `SO_+(V_ℚ)_f = SU(V_ℚ, H)`. -/
theorem lemma3_1_2_finiteIndex (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    P.SOplusf hP.isCompl ≤ P.SUH hP.isCompl ∧
      ((P.SOplusf hP.isCompl).subgroupOf (P.SUH hP.isCompl)).index ≠ 0 := by
  refine ⟨P.s3_SOplusf_le_SUH hP.isCompl, ?_⟩
  rw [P.s3_SOplusf_eq_SUH hP.isCompl hP.nonIsotropic, Subgroup.subgroupOf_self, Subgroup.index_top]
  exact one_ne_zero

/-- In the proof of Lemma 3.1.2: `SO_+(V_ℚ)_f` *equals* the special unitary group `SU(V_ℚ, H)`
(`K`-linear `H`-isometries of `K`-determinant `1`).

Departure from the paper (see `lemma3_1_2_finiteIndex`): `SU(V_ℚ, H) ⊆ SO_+(V_ℚ)_f` is proved by
showing that the spinor norm is trivial on `SU(V_ℚ, H)` (Chevalley's III.3.2/III.4.5, the Mukai
pairing and Galois descent), in place of the paper's "the norm character has finitely many values". -/
theorem lemma3_1_2_eq_SUH (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.SOplusf hP.isCompl = P.SUH hP.isCompl :=
  P.s3_SOplusf_eq_SUH hP.isCompl hP.nonIsotropic

/-! ## Lemma 3.1.3 -/

/-- In the proof of Lemma 3.1.3: for `P = P_Θ` and `y, y' ∈ H¹(X̂, ℚ) = H¹(X, ℚ)*`,
`H((0, y), (0, y')) = d √-d Θ(y, y')` (paper's order; ours: `((y, 0), (y', 0))`), with
`Θ(y, y') = ⟪Θ, y ∧ y'⟫`. -/
theorem PTheta_hermH_inl (hd : 0 < d) (Θ : S ℚ n) (hΘ : Θ ∈ ⋀[ℚ]^2 (H1 ℚ n)) (hΘ0 : Θ ≠ 0)
    (hθ : Function.Bijective (thetaMap n Θ)) (y y' : Module.Dual ℚ (H1 ℚ n)) :
    (PTheta n d hd Θ hΘ hΘ0).hermH (PTheta_isCompl n d hd Θ hΘ hΘ0 hθ) (y, 0) (y', 0) =
      algebraMap ℚ (Kd d) d * Kd.sqrtNeg d * algebraMap ℚ (Kd d) (eval2 ℚ n Θ y y') := by
  -- `((y, 0), (y', 0))_V = 0` and `f(y, 0) = (0, d θ(y))`, `((0, θ(y)), (y', 0))_V = Θ(y, y')`
  simp only [KSecant.hermH, PTheta_fη_inl n d hd Θ hΘ hΘ0 hθ y, QuadraticMap.polarBilin_apply_apply,
    TauCeti.polar_dualProd]
  simp only [map_zero, zero_add, add_zero, mul_zero, map_smul, smul_eq_mul,
    thetaMap_apply_eq_eval2 n Θ hΘ, map_mul]
  ring

/-- **Lemma 3.1.3** (`lemma-the-discriminant-is-minus-1-to-the-n`). Assume that the similarity
`f : V_ℚ → V_ℚ` given in Equation (2.4.1) is defined in terms of the oriented plane `P` given in
Equation (2.4.5). Then the discriminant of the Hermitian form `H` is `(-1)^n`.

Here `P = P_Θ` for `Θ` ample for the complex structure `J` of `X` (so that Assumption 2.4.1 holds,
`PTheta_assumption2_4_1`); `d > 0` rational (the paper: a positive integer). -/
theorem lemma3_1_3 (hd : 0 < d) (hn : 0 < n) (J : Module.End ℝ (H1 ℝ n))
    (hJ : IsComplexStructure J) (Θ : S ℚ n) (hΘ : IsAmple n J Θ) :
    (PTheta n d hd Θ hΘ.mem_exteriorPower_two (hΘ.ne_zero_of_pos hn)).DiscIs
      (PTheta_isCompl n d hd Θ _ _ hΘ.bijective_thetaMap) ((-1) ^ n) := by
  have hΘ2 := hΘ.mem_exteriorPower_two
  have hΘ0 := hΘ.ne_zero_of_pos hn
  have hθ := hΘ.bijective_thetaMap
  -- the `K`-basis `(y_i, 0)` of `V_ℚ`, `y_i` the basis of `H¹(X̂, ℚ) = H¹(X, ℚ)*` dual to `e_i`
  let b : Fin (2 * n) → V ℚ n := fun i => (f ℚ n i, 0)
  have hfb : ∀ i, (PTheta n d hd Θ hΘ2 hΘ0).fη (PTheta_isCompl n d hd Θ hΘ2 hΘ0 hθ) (b i) =
      (0, d • thetaMap n Θ (f ℚ n i)) := fun i => PTheta_fη_inl n d hd Θ hΘ2 hΘ0 hθ _
  have hy : ∀ c : Fin (2 * n) → ℚ, ∑ i, c i • f ℚ n i = 0 → c = 0 := by
    intro c hc
    ext j
    have := LinearMap.congr_fun hc (e ℚ n j)
    simpa [f, e, Pi.single_apply] using this
  have hb : (PTheta n d hd Θ hΘ2 hΘ0).IsKBasis (PTheta_isCompl n d hd Θ hΘ2 hΘ0 hθ) b := by
    rw [KSecant.IsKBasis, Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, hfb] at hg
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hg
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
      Prod.smul_snd, smul_zero, Finset.sum_const_zero, add_zero, zero_add, Prod.fst_zero,
      Prod.snd_zero, b] at h1 h2
    have hl := hy (fun i => g (Sum.inl i)) h1
    have hr : (fun i => g (Sum.inr i)) = 0 := by
      apply hy
      apply hθ.1
      rw [map_sum, map_zero]
      have : d • ∑ i, g (Sum.inr i) • thetaMap n Θ (f ℚ n i) = 0 := by
        rw [Finset.smul_sum]
        simpa [smul_comm d] using h2
      simpa [map_smul, hd.ne'] using this
    rintro (i | i)
    · exact congrFun hl i
    · exact congrFun hr i
  -- the Gram matrix: `H((y_i, 0), (y_j, 0)) = d √-d Θ(y_i, y_j)`
  let M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ :=
    Matrix.of fun i j => eval2 ℚ n Θ (f ℚ n i) (f ℚ n j)
  have hgram : (PTheta n d hd Θ hΘ2 hΘ0).gramH (PTheta_isCompl n d hd Θ hΘ2 hΘ0 hθ) b =
      (algebraMap ℚ (Kd d) d * Kd.sqrtNeg d) • (algebraMap ℚ (Kd d)).mapMatrix M := by
    ext i j
    simp only [KSecant.gramH, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, smul_eq_mul, M, b]
    rw [PTheta_hermH_inl hd Θ hΘ2 hΘ0 hθ]
  -- `Θ` is antisymmetric, so `det(Θ(y_i, y_j))` is a square
  have hMT : M.transpose = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, M, Matrix.of_apply]
    exact s3_eval2_swap _ _ _
  obtain ⟨p, hp⟩ := s3_isSquare_det_of_transpose_eq_neg _ M hMT
  -- it is nonzero, since `θ` is an isomorphism
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hp
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hp
    apply hv0
    apply hy
    apply hθ.1
    ext j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply] at this
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← thetaMap_apply_eq_eval2 n Θ hΘ2]
    simp [f]
  refine ⟨b, hb, d ^ (3 * n) * p ^ 2, s3_mem_normGroup hd _ hp0, ?_⟩
  have hsq : (algebraMap ℚ (Kd d) d * Kd.sqrtNeg d) ^ 2 = algebraMap ℚ (Kd d) (-d ^ 3) := by
    rw [mul_pow, sq (Kd.sqrtNeg d), s3_sqrtNeg_mul_self hd]
    simp only [map_neg, map_pow]
    ring
  rw [hgram, Matrix.det_smul, ← RingHom.map_det, hp, Fintype.card_fin, pow_mul, hsq, ← map_pow,
    ← map_mul]
  congr 1
  ring


end WeilClasses
