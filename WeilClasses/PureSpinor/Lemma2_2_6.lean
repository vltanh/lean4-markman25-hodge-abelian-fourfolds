module

public import WeilClasses.Spinor.Embeddings
public import WeilClasses.PureSpinor.Lemma2_2_1
public import WeilClasses.Hodge.Defs
public import WeilClasses.PureSpinor.Lemma2_2_4
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import WeilClasses.External.Chevalley.Sec3
import WeilClasses.External.Chevalley.Sec2_1

/-!
# Remark 2.2.5, Chevalley's isomorphism `φ` (2.2.5), and Lemma 2.2.6 (paper §2.2)

Let `J` be a complex structure on `H¹(X, ℝ)` (the complex structure of `X`, with
`H^{1,0}(X) = i`-eigenspace) and `I = productStructure n J` the induced complex structure of
`X × X̂` on `V_ℝ`; `V^{1,0} = V10 n I`, `V^{0,1} = V01 n I` (`WeilClasses.Hodge.Defs`). The Hodge
ring of `X` is `hodgeRingX n J`.

## Main definitions

* `KSecant.W₁ℂ`, `KSecant.W₂ℂ`: the complexifications `W_{i,ℂ}` of `W₁, W₂ ⊆ V_K`.
* `KSecant.PR`, `KSecant.spinPR`: the real plane `P_ℝ ⊆ S_ℝ` and `Spin(V_ℝ)_P`.
* `iotaX`, `iotaXHat`: the embeddings of `S_X = ⋀• H¹(X)` and `S_X̂ = ⋀• H¹(X̂)` in `C(V)` as
  subalgebras (`H¹(X)` and `H¹(X̂)` are isotropic); `ptHatC = [pt_X̂] = f₁ ⋯ f_{2n} ∈ C(V)`.
* `varphi`: Chevalley's `φ : S ⊗ S → C(V)`, `φ(u ⊗ v) = u [pt_X̂] τ(v)` (2.2.5).
* `cliffordTopPiece F n W`: `⋀^{2n} W` regarded as a subspace of `C(V)` (products of `2n` vectors
  of `W`).

## Statements

* **Remark 2.2.5** (`remark2_2_5`, in the corrected form agreed with the project owner: the whole
  circle `cos θ + sin θ · I` in `ρ(Spin(V_ℝ)_P)`).
* Claims in the proof of Lemma 2.2.6 on `φ`: `m_varphi_tmul` (the footnote: `m ∘ φ` is
  `(-1)^n` times `s ⊗ t ↦ s ⊗ (t, ·)_S`) and `closure_varphi_SZ` (`φ` is onto `C(V)` over
  `ℤ`). The cited facts [Chevalley, III.3.1] (`φ ⊗ ℚ` is a `Spin(V_ℚ)`-equivariant isomorphism) and
  [Chevalley, III.3.2] (`φ(ℓ̃ ⊗ ℓ̃) = ⋀^{2n} W ⊆ C(V)`) are in
  `WeilClasses.External.Chevalley.Sec2_2`.
* **Lemma 2.2.6** (`lemma2_2_6`, `lemma2_2_6_V01`) and the decomposition
  `W_{i,ℂ} = (W_{i,ℂ} ∩ V^{1,0}) ⊕ (W_{i,ℂ} ∩ V^{0,1})` proved on the way (`lemma2_2_6_decomp`,
  used in §2.4: "`I` commutes with `f`, by Lemma 2.2.6").

The Hodge structure on `C(V)` induced by `m : C(V) ≅ End(S)`, used in the paper's proof, is not
formalized as such; in the model it is the action of the circle `exp(t I)` on `V` and of its lift
`exp(-t D_J)` on `S` (`D_J` the derivation of `⋀• H¹(X)` extending `J`; `I = I_{V_ℝ}` acts on the
summand `H¹(X)` by `-J`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P04, prefix `s22b_`) -/

section PiecesHelpers

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

theorem s22b_pqPiece_le (A B : Submodule F M) (p q : ℕ) :
    pqPiece A B p q ≤ ⋀[F]^(p + q) M := by
  rw [pqPiece, Submodule.span_le]
  rintro _ ⟨a, b, -, -, rfl⟩
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact ExteriorAlgebra.ιMulti_range F (p + q) ⟨_, rfl⟩

theorem s22b_ι_mul_ι_anticomm (w v : M) :
    ExteriorAlgebra.ι F w * ExteriorAlgebra.ι F v = -(ExteriorAlgebra.ι F v * ExteriorAlgebra.ι F w) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap w v)

theorem s22b_ι_mul_ιMulti_comm (w : M) (k : ℕ) (v : Fin k → M) :
    ExteriorAlgebra.ι F w * ExteriorAlgebra.ιMulti F k v =
      (-1 : F) ^ k • (ExteriorAlgebra.ιMulti F k v * ExteriorAlgebra.ι F w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc, s22b_ι_mul_ι_anticomm, neg_mul, mul_assoc,
      ih, mul_smul_comm, ← mul_assoc, pow_succ, mul_comm ((-1 : F) ^ k), mul_smul, neg_one_smul]

theorem s22b_ι_mul_mem_pqPiece_left {A B : Submodule F M} {p q : ℕ} {w : M} (hw : w ∈ A)
    {x : ExteriorAlgebra F M} (hx : x ∈ pqPiece A B p q) :
    ExteriorAlgebra.ι F w * x ∈ pqPiece A B (p + 1) q := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    refine Submodule.subset_span ⟨Fin.cons w a, b, fun i => ?_, hb, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hw
      · simpa using ha j
    · rw [← mul_assoc, ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem s22b_ι_mul_mem_pqPiece_right {A B : Submodule F M} {p q : ℕ} {w : M} (hw : w ∈ B)
    {x : ExteriorAlgebra F M} (hx : x ∈ pqPiece A B p q) :
    ExteriorAlgebra.ι F w * x ∈ pqPiece A B p (q + 1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    rw [← mul_assoc, s22b_ι_mul_ιMulti_comm, smul_mul_assoc, mul_assoc]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Fin.cons w b, ha, fun i => ?_, ?_⟩)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hw
      · simpa using hb j
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- An endomorphism acting by scalars `α` on `A` and `β` on `B` acts by `α^p β^q` on
`⋀^p A ∧ ⋀^q B`. -/
theorem s22b_map_pqPiece {A B : Submodule F M} {p q : ℕ} (f : M →ₗ[F] M) (α β : F)
    (hA : ∀ a ∈ A, f a = α • a) (hB : ∀ b ∈ B, f b = β • b) {x : ExteriorAlgebra F M}
    (hx : x ∈ pqPiece A B p q) : ExteriorAlgebra.map f x = (α ^ p * β ^ q) • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hy
    rw [map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
    have h1 : (f ∘ a) = fun i => α • a i := funext fun i => hA _ (ha i)
    have h2 : (f ∘ b) = fun j => β • b j := funext fun j => hB _ (hb j)
    rw [h1, h2, AlternatingMap.map_smul_univ, AlternatingMap.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_mul_smul_comm]
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem s22b_pqPiece_zero_zero (A B : Submodule F M) :
    pqPiece A B 0 0 = ⋀[F]^0 M := by
  apply le_antisymm (by simpa using s22b_pqPiece_le A B 0 0)
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine Submodule.subset_span ⟨v, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  simp

/-- `⋀^k M = Σ_a ⋀^a A ∧ ⋀^{k-a} B` when `A + B = M`. -/
theorem s22b_wedge_le_iSup {A B : Submodule F M} (hAB : A ⊔ B = ⊤) (k : ℕ) :
    ⋀[F]^k M ≤ ⨆ a : Fin (k + 1), pqPiece A B a (k - a) := by
  induction k with
  | zero =>
    rw [← s22b_pqPiece_zero_zero A B]
    exact le_iSup_of_le (0 : Fin 1) le_rfl
  | succ k ih =>
    show LinearMap.range (ExteriorAlgebra.ι F : M →ₗ[F] ExteriorAlgebra F M) ^ (k + 1) ≤ _
    rw [pow_succ']
    refine Submodule.mul_le.mpr fun u hu z hz => ?_
    obtain ⟨v, rfl⟩ := hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hAB.symm ▸ Submodule.mem_top : v ∈ A ⊔ B)
    rw [map_add, add_mul]
    have hz' := ih hz
    clear hz
    refine Submodule.add_mem _ ?_ ?_
    · -- `ι a * z`
      induction hz' using Submodule.iSup_induction' with
      | mem i y hy =>
        refine Submodule.mem_iSup_of_mem (⟨i + 1, by omega⟩ : Fin (k + 2)) ?_
        have h := s22b_ι_mul_mem_pqPiece_left (B := B) ha hy
        convert h using 2
        simp only
        omega
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    · induction hz' using Submodule.iSup_induction' with
      | mem i y hy =>
        refine Submodule.mem_iSup_of_mem (⟨i, by omega⟩ : Fin (k + 2)) ?_
        have h := s22b_ι_mul_mem_pqPiece_right (A := A) hb hy
        convert h using 2
        simp only
        omega
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy

/-- The pieces `⋀^a A ∧ ⋀^{k-a} B` are independent when `M = A ⊕ B`. -/
theorem s22b_iSupIndep_pqPiece [CharZero F] {A B : Submodule F M} (hAB : IsCompl A B) (k : ℕ) :
    iSupIndep (fun a : Fin (k + 1) => pqPiece A B a (k - a)) := by
  set Λ := ExteriorAlgebra.map ((2 : F) • A.projection B hAB + B.projection A hAB.symm)
  have hinj : Function.Injective fun a : Fin (k + 1) => (2 : F) ^ (a : ℕ) := by
    intro a b hab
    have : ((2 ^ (a : ℕ) : ℕ) : F) = ((2 ^ (b : ℕ) : ℕ) : F) := by push_cast; exact hab
    exact Fin.ext (Nat.pow_right_injective le_rfl (Nat.cast_injective this))
  refine ((Module.End.eigenspaces_iSupIndep Λ.toLinearMap).comp hinj).mono fun a => ?_
  intro x hx
  simp only [Function.comp_apply, Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply]
  have := s22b_map_pqPiece ((2 : F) • A.projection B hAB + B.projection A hAB.symm) 2 1
    (fun a ha => by simp [Submodule.projection_apply_of_mem_left hAB ha,
      Submodule.projection_apply_of_mem_right hAB.symm ha])
    (fun b hb => by simp [Submodule.projection_apply_of_mem_right hAB hb,
      Submodule.projection_apply_of_mem_left hAB.symm hb]) hx
  rw [this, one_pow, mul_one]

/-- If `T` acts by `χ i` on `U i` and `x ∈ ⨆ U i` is an eigenvector of `T` with eigenvalue `μ`,
then `x ∈ ⨆_{χ i = μ} U i`. -/
theorem s22b_mem_iSup_eigen {ι : Type*} (U : ι → Submodule F M) (T : Module.End F M)
    (χ : ι → F) (hU : ∀ i, ∀ x ∈ U i, T x = χ i • x) (μ : F) {x : M}
    (hx : x ∈ ⨆ i, U i) (hTx : T x = μ • x) : x ∈ ⨆ (i) (_ : χ i = μ), U i := by
  classical
  have hsplit : (⨆ i, U i) = (⨆ (i) (_ : χ i = μ), U i) ⊔ (⨆ (i) (_ : χ i ≠ μ), U i) := by
    rw [← iSup_sup_eq]
    exact iSup_congr fun i => by by_cases h : χ i = μ <;> simp [h]
  have hT : ∀ w ∈ ⨆ (i) (_ : χ i = μ), U i, T w = μ • w := by
    intro w hw
    induction hw using Submodule.iSup_induction' with
    | mem i w hw =>
      induction hw using Submodule.iSup_induction' with
      | mem h w hw => rw [hU i w hw, h]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  have hE : ∀ w ∈ ⨆ (i) (_ : χ i ≠ μ), U i, w ∈ ⨆ (ν) (_ : ν ≠ μ), T.eigenspace ν := by
    intro w hw
    induction hw using Submodule.iSup_induction' with
    | mem i w hw =>
      induction hw using Submodule.iSup_induction' with
      | mem h w hw =>
        exact Submodule.mem_iSup_of_mem (χ i) (Submodule.mem_iSup_of_mem h
          (Module.End.mem_eigenspace_iff.mpr (hU i w hw)))
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  rw [hsplit] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hTy : T y = μ • y := hT y hy
  have hz0 : z = 0 := by
    have hTz : T z = μ • z := by
      rw [map_add, hTy, smul_add] at hTx
      exact add_left_cancel hTx
    have h1 : z ∈ T.eigenspace μ := Module.End.mem_eigenspace_iff.mpr hTz
    have h2 : z ∈ ⨆ (ν) (_ : ν ≠ μ), T.eigenspace ν := hE z hz
    have := (Module.End.eigenspaces_iSupIndep T μ)
    exact (Submodule.disjoint_def.mp this) z h1 h2
  rw [hz0, add_zero]
  exact hy

/-- Separation of an independent family by a family of operators acting by scalars. -/
theorem s22b_mem_of_separating {ι J : Type*} (U : ι → Submodule F M) (hU : iSupIndep U)
    (T : J → Module.End F M) (χ : J → ι → F) (hTU : ∀ j i, ∀ x ∈ U i, T j x = χ j i • x)
    (i₀ : ι) (hsep : ∀ i ≠ i₀, ∃ j, χ j i ≠ χ j i₀) {x : M} (hx : x ∈ ⨆ i, U i)
    (hTx : ∀ j, T j x = χ j i₀ • x) : x ∈ U i₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp U x).mp hx
  have hzero : ∀ i ≠ i₀, f i = 0 := by
    intro i hi
    obtain ⟨j, hj⟩ := hsep i hi
    have hsum : ∑ k ∈ f.support, (χ j k - χ j i₀) • f k = 0 := by
      have h1 := hTx j
      simp only [Finsupp.sum, map_sum, Finset.smul_sum] at h1
      rw [Finset.sum_congr rfl fun k _ => hTU j k (f k) (hf k)] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
    by_cases hmem : i ∈ f.support
    · have := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero U).mp hU f.support
        (fun k => (χ j k - χ j i₀) • f k) (fun k _ => Submodule.smul_mem _ _ (hf k)) hsum i hmem
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hj)
    · exact Finsupp.notMem_support_iff.mp hmem
  have : (f.sum fun _ xi => xi) = f i₀ := by
    rw [Finsupp.sum, Finset.sum_eq_single i₀ (fun i _ hi => hzero i hi)
      (fun h => Finsupp.notMem_support_iff.mp h)]
  rw [this]
  exact hf i₀

theorem s22b_pqPiece_one_zero (A B : Submodule F M) :
    pqPiece A B 1 0 = A.map (ExteriorAlgebra.ι F) := by
  apply le_antisymm
  · rw [pqPiece, Submodule.span_le]
    rintro _ ⟨a, b, ha, -, rfl⟩
    exact ⟨a 0, ha 0, by simp⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨fun _ => a, Fin.elim0, fun _ => ha, fun i => i.elim0, by simp⟩

theorem s22b_pqPiece_zero_one (A B : Submodule F M) :
    pqPiece A B 0 1 = B.map (ExteriorAlgebra.ι F) := by
  apply le_antisymm
  · rw [pqPiece, Submodule.span_le]
    rintro _ ⟨a, b, -, hb, rfl⟩
    exact ⟨b 0, hb 0, by simp⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact Submodule.subset_span ⟨Fin.elim0, fun _ => b, fun i => i.elim0, fun _ => hb, by simp⟩

theorem s22b_ι_injective : Function.Injective (ExteriorAlgebra.ι F : M →ₗ[F] ExteriorAlgebra F M) :=
  ExteriorAlgebra.ι_leftInverse.injective

end PiecesHelpers

section Monomials

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι K M)

/-- The derivation of `⋀• M` extending an endomorphism `X` of `M`:
`D_X = Σ_k L_{X b_k} ∘ ι_{b_k^*}`. -/
noncomputable def s22b_Der (X : M →ₗ[K] M) : ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  ∑ k, (LinearMap.mul K (ExteriorAlgebra K M) (ExteriorAlgebra.ι K (X (b k)))) ∘ₗ
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K M)) (b.coord k))

theorem s22b_Der_add (X Y : M →ₗ[K] M) : s22b_Der b (X + Y) = s22b_Der b X + s22b_Der b Y := by
  simp only [s22b_Der, LinearMap.add_apply, map_add, LinearMap.add_comp, Finset.sum_add_distrib]

theorem s22b_Der_smul (c : K) (X : M →ₗ[K] M) : s22b_Der b (c • X) = c • s22b_Der b X := by
  simp only [s22b_Der, LinearMap.smul_apply, map_smul, LinearMap.smul_comp, Finset.smul_sum]

theorem s22b_Der_sub (X Y : M →ₗ[K] M) : s22b_Der b (X - Y) = s22b_Der b X - s22b_Der b Y := by
  simp only [s22b_Der, LinearMap.sub_apply, map_sub, LinearMap.sub_comp, Finset.sum_sub_distrib]

theorem s22b_Der_algebraMap (X : M →ₗ[K] M) (r : K) :
    s22b_Der b X (algebraMap K (ExteriorAlgebra K M) r) = 0 := by
  simp [s22b_Der, contractLeft_algebraMap]

/-- `D_X` is a derivation: `D_X(v ∧ y) = X v ∧ y + v ∧ D_X y`. -/
theorem s22b_Der_ι_mul (X : M →ₗ[K] M) (v : M) (y : ExteriorAlgebra K M) :
    s22b_Der b X (ExteriorAlgebra.ι K v * y) =
      ExteriorAlgebra.ι K (X v) * y + ExteriorAlgebra.ι K v * s22b_Der b X y := by
  have h1 : (ExteriorAlgebra.ι K v) = CliffordAlgebra.ι (0 : QuadraticForm K M) v := rfl
  simp only [s22b_Der, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mul_apply']
  rw [h1]
  simp only [contractLeft_ι_mul, mul_sub, mul_smul_comm]
  rw [Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  · have hXv : X v = ∑ k, (b.coord k v) • X (b k) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul, Module.Basis.coord_apply]
    simp_rw [← smul_mul_assoc]
    rw [← Finset.sum_mul, hXv, map_sum]
    simp_rw [map_smul]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← neg_mul]
    congr 1
    have := ExteriorAlgebra.ι_add_mul_swap (R := K) v (X (b k))
    rw [← h1]
    exact neg_eq_of_add_eq_zero_left this

theorem s22b_Der_ιMulti (X : M →ₗ[K] M) (m : ℕ) (v : Fin m → M) :
    s22b_Der b X (ExteriorAlgebra.ιMulti K m v) =
      ∑ k, ExteriorAlgebra.ιMulti K m (Function.update v k (X (v k))) := by
  induction m with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (ExteriorAlgebra K M)),
      s22b_Der_algebraMap]
    simp
  | succ m ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, s22b_Der_ι_mul, ih, Fin.sum_univ_succ,
      Finset.mul_sum]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Function.update_self]
      congr 2
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      funext i
      simp only [Matrix.vecTail, Function.comp_apply]
      rcases eq_or_ne i k with rfl | hik
      · simp
      · rw [Function.update_of_ne hik, Function.update_of_ne (fun h => hik (Fin.succ_injective _ h))]
        rfl

variable [LinearOrder ι]

omit [Fintype ι] in
/-- The monomial `e_S` is `ιMulti` of the basis vectors indexed by the increasing enumeration
of `S`. -/
theorem s22b_basis_eq_ιMulti (S : Finset ι) :
    ∃ t : Fin S.card → ι, Function.Injective t ∧ Set.range t = S ∧
      b.ExteriorAlgebra S = ExteriorAlgebra.ιMulti K S.card (b ∘ t) := by
  refine ⟨Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl),
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl)).injective, ?_, ?_⟩
  · ext i
    rw [Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
    simp [Set.powersetCard.ofCard]
  · rw [ExteriorAlgebra.basis_apply_ofCard b rfl]

omit [Fintype ι] in
/-- `ιMulti` of distinct basis vectors is `± e_S`. -/
theorem s22b_ιMulti_basis {m : ℕ} (s : Fin m → ι) (hs : Function.Injective s) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      ExteriorAlgebra.ιMulti K m (b ∘ s) = ε • b.ExteriorAlgebra (Finset.univ.image s) := by
  classical
  set S := Finset.univ.image s
  have hcard : S.card = m := by
    rw [Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin]
  obtain ⟨t, ht, hrange, he⟩ := s22b_basis_eq_ιMulti b S
  -- `s = t ∘ σ` for a permutation `σ`
  have hex : ∀ i : Fin m, ∃ j : Fin S.card, t j = s i := by
    intro i
    have : s i ∈ Set.range t := by rw [hrange]; simp [S]
    exact this
  choose f hf using hex
  have hfinj : Function.Injective f := fun i i' h => hs (by rw [← hf i, ← hf i', h])
  have hcard' : Fintype.card (Fin m) = Fintype.card (Fin S.card) := by simp [hcard]
  let σ : Fin m ≃ Fin S.card := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard'⟩)
  -- transport to a permutation of `Fin m`
  let τ : Equiv.Perm (Fin m) := σ.trans (finCongr hcard)
  have hτ : s = (t ∘ (finCongr hcard).symm) ∘ τ := by
    funext i
    simp [τ, σ, hf]
  refine ⟨((Equiv.Perm.sign τ : ℤˣ) : ℤ), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [hτ, he, ← Function.comp_assoc, AlternatingMap.map_perm]
    have : ExteriorAlgebra.ιMulti K S.card (b ∘ t) =
        ExteriorAlgebra.ιMulti K m ((b ∘ t) ∘ (finCongr hcard).symm) := by
      rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, List.ofFn_congr hcard]
      rfl
    rw [this, Units.smul_def, Int.cast_smul_eq_zsmul]
    rfl

/-- The "number operator" `N_l = b_l ⊗ b_l^*`. -/
noncomputable def s22b_numOp (l : ι) : M →ₗ[K] M := (b.coord l).smulRight (b l)

/-- The elementary operator `R_{l,k} = b_l ⊗ b_k^*` (`b_k ↦ b_l`). -/
noncomputable def s22b_rOp (l k : ι) : M →ₗ[K] M := (b.coord k).smulRight (b l)

theorem s22b_Der_numOp (l : ι) (S : Finset ι) :
    s22b_Der b (s22b_numOp b l) (b.ExteriorAlgebra S) =
      (if l ∈ S then (1 : K) else 0) • b.ExteriorAlgebra S := by
  classical
  obtain ⟨t, ht, hrange, he⟩ := s22b_basis_eq_ιMulti b S
  rw [he, s22b_Der_ιMulti]
  have hterm : ∀ k, ExteriorAlgebra.ιMulti K S.card
      (Function.update (b ∘ t) k (s22b_numOp b l ((b ∘ t) k))) =
      (if t k = l then (1 : K) else 0) • ExteriorAlgebra.ιMulti K S.card (b ∘ t) := by
    intro k
    have : s22b_numOp b l ((b ∘ t) k) = (if t k = l then (1 : K) else 0) • (b ∘ t) k := by
      by_cases h : t k = l
      · simp [s22b_numOp, h]
      · simp [s22b_numOp, h]
    rw [this, AlternatingMap.map_update_smul, Function.update_eq_self]
  simp_rw [hterm, ← Finset.sum_smul]
  congr 1
  by_cases hl : l ∈ S
  · have : l ∈ Set.range t := by rw [hrange]; exact hl
    obtain ⟨k₀, hk₀⟩ := this
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by
        have : t k ≠ l := fun h => hk (ht (h.trans hk₀.symm))
        simp [this]) (fun h => absurd (Finset.mem_univ _) h)]
    simp [hk₀, hl]
  · simp only [hl, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : t k ≠ l := fun h => hl (by rw [← h, ← Finset.mem_coe, ← hrange]; exact ⟨k, rfl⟩)
    simp [this]

/-- `D_{R_{l,k}}` on monomials: `e_S ↦ ± e_{S - k + l}` if `k ∈ S`, `l ∉ S`, and `0` otherwise. -/
theorem s22b_Der_rOp (l k : ι) (hlk : l ≠ k) (S : Finset ι) :
    (k ∉ S ∨ l ∈ S → s22b_Der b (s22b_rOp b l k) (b.ExteriorAlgebra S) = 0) ∧
      (k ∈ S → l ∉ S → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
        s22b_Der b (s22b_rOp b l k) (b.ExteriorAlgebra S) =
          ε • b.ExteriorAlgebra (insert l (S.erase k))) := by
  classical
  obtain ⟨t, ht, hrange, he⟩ := s22b_basis_eq_ιMulti b S
  rw [he, s22b_Der_ιMulti]
  have hterm : ∀ j, ExteriorAlgebra.ιMulti K S.card
      (Function.update (b ∘ t) j (s22b_rOp b l k ((b ∘ t) j))) =
      (if t j = k then (1 : K) else 0) •
        ExteriorAlgebra.ιMulti K S.card (b ∘ Function.update t j l) := by
    intro j
    have : s22b_rOp b l k ((b ∘ t) j) = (if t j = k then (1 : K) else 0) • b l := by
      by_cases h : t j = k
      · simp [s22b_rOp, h]
      · simp [s22b_rOp, h]
    rw [this, AlternatingMap.map_update_smul, Function.comp_update]
  simp_rw [hterm]
  constructor
  · rintro (hk | hl)
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : t j ≠ k := fun h => hk (by rw [← h, ← Finset.mem_coe, ← hrange]; exact ⟨j, rfl⟩)
      simp [this]
    · refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · rw [one_smul]
        apply AlternatingMap.map_eq_zero_of_not_injective
        intro hinj
        have : l ∈ Set.range t := by rw [hrange]; exact hl
        obtain ⟨j₁, hj₁⟩ := this
        have hj : j₁ ≠ j := fun h' => hlk (by rw [← hj₁, h', h])
        have := hinj (a₁ := j₁) (a₂ := j) (by
          simp only [Function.comp_apply, Function.update_of_ne hj, Function.update_self, hj₁])
        exact hj this
      · rw [zero_smul]
  · intro hk hl
    have : k ∈ Set.range t := by rw [hrange]; exact hk
    obtain ⟨j₀, hj₀⟩ := this
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by
        have : t j ≠ k := fun h => hj (ht (h.trans hj₀.symm))
        simp [this]) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [hj₀, ↓reduceIte, one_smul]
    have hinj : Function.Injective (Function.update t j₀ l) := by
      intro a a' h
      by_cases ha : a = j₀ <;> by_cases ha' : a' = j₀
      · rw [ha, ha']
      · subst ha
        rw [Function.update_self, Function.update_of_ne ha'] at h
        exact absurd (by rw [h, ← Finset.mem_coe, ← hrange]; exact ⟨a', rfl⟩) hl
      · subst ha'
        rw [Function.update_self, Function.update_of_ne ha] at h
        exact absurd (by rw [← h, ← Finset.mem_coe, ← hrange]; exact ⟨a, rfl⟩) hl
      · rw [Function.update_of_ne ha, Function.update_of_ne ha'] at h
        exact ht h
    obtain ⟨ε, hε, heq⟩ := s22b_ιMulti_basis b _ hinj
    refine ⟨ε, hε, ?_⟩
    rw [heq]
    congr 2
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨a, rfl⟩
      by_cases ha : a = j₀
      · subst ha; left; rw [Function.update_self]
      · right
        rw [Function.update_of_ne ha]
        refine ⟨fun h => ha (ht (h.trans hj₀.symm)), ?_⟩
        rw [← Finset.mem_coe, ← hrange]; exact ⟨a, rfl⟩
    · rintro (rfl | ⟨hik, hiS⟩)
      · exact ⟨j₀, Function.update_self _ _ _⟩
      · have : i ∈ Set.range t := by rw [hrange]; exact hiS
        obtain ⟨a, rfl⟩ := this
        refine ⟨a, ?_⟩
        rw [Function.update_of_ne fun h => hik (by rw [h, hj₀])]


omit [LinearOrder ι] in
theorem s22b_Der_smulRight (φ : Module.Dual K M) (a : M) :
    s22b_Der b (φ.smulRight a) =
      (LinearMap.mul K (ExteriorAlgebra K M) (ExteriorAlgebra.ι K a)) ∘ₗ
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K M)) φ := by
  simp only [s22b_Der, LinearMap.smulRight_apply, map_smul, LinearMap.smul_comp]
  refine LinearMap.ext fun y => ?_
  conv_rhs => rw [← b.sum_dual_apply_smul_coord φ]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul,
    LinearMap.mul_apply']

omit [LinearOrder ι] in
theorem s22b_Der_ιMulti_id (m : ℕ) (v : Fin m → M) :
    s22b_Der b LinearMap.id (ExteriorAlgebra.ιMulti K m v) = (m : K) • ExteriorAlgebra.ιMulti K m v := by
  rw [s22b_Der_ιMulti]
  simp only [LinearMap.id_apply, Function.update_eq_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

end Monomials

section MonoRepr

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*} [Fintype ι]
  [LinearOrder ι] (b : Module.Basis ι K M)

theorem s22b_repr_map (D : ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M) (x : ExteriorAlgebra K M)
    (T : Finset ι) :
    b.ExteriorAlgebra.repr (D x) T =
      ∑ S, b.ExteriorAlgebra.repr x S * b.ExteriorAlgebra.repr (D (b.ExteriorAlgebra S)) T := by
  conv_lhs => rw [← b.ExteriorAlgebra.sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem s22b_repr_Der_numOp (l : ι) (x : ExteriorAlgebra K M) (S : Finset ι) :
    b.ExteriorAlgebra.repr (s22b_Der b (s22b_numOp b l) x) S =
      (if l ∈ S then (1 : K) else 0) * b.ExteriorAlgebra.repr x S := by
  classical
  rw [s22b_repr_map, Finset.sum_eq_single S]
  · rw [s22b_Der_numOp, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · intro S' _ hS'
    rw [s22b_Der_numOp, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hS'.symm, smul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem s22b_repr_Der_id (x : ExteriorAlgebra K M) (S : Finset ι) :
    b.ExteriorAlgebra.repr (s22b_Der b LinearMap.id x) S = (S.card : K) * b.ExteriorAlgebra.repr x S := by
  classical
  rw [s22b_repr_map, Finset.sum_eq_single S]
  · obtain ⟨t, -, -, he⟩ := s22b_basis_eq_ιMulti b S
    rw [he, s22b_Der_ιMulti_id, ← he, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · intro S' _ hS'
    obtain ⟨t, -, -, he⟩ := s22b_basis_eq_ιMulti b S'
    rw [he, s22b_Der_ιMulti_id, ← he, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hS'.symm, smul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem s22b_repr_Der_rOp (l k : ι) (hlk : l ≠ k) (x : ExteriorAlgebra K M) (T : Finset ι)
    (hlT : l ∈ T) (hkT : k ∉ T) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ b.ExteriorAlgebra.repr (s22b_Der b (s22b_rOp b l k) x) T =
      ε * b.ExteriorAlgebra.repr x (insert k (T.erase l)) := by
  classical
  set S₀ := insert k (T.erase l)
  have hkS₀ : k ∈ S₀ := Finset.mem_insert_self _ _
  have hlS₀ : l ∉ S₀ := by simp [S₀, hlk]
  have hT : insert l (S₀.erase k) = T := by
    have : S₀.erase k = T.erase l := by
      rw [Finset.erase_insert]; simp [hkT]
    rw [this, Finset.insert_erase hlT]
  obtain ⟨ε, hε, he⟩ := (s22b_Der_rOp b l k hlk S₀).2 hkS₀ hlS₀
  refine ⟨ε, hε, ?_⟩
  rw [s22b_repr_map, Finset.sum_eq_single S₀]
  · rw [he, hT, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, mul_comm]
  · intro S _ hS
    by_cases hc : k ∈ S ∧ l ∉ S
    · obtain ⟨ε', -, he'⟩ := (s22b_Der_rOp b l k hlk S).2 hc.1 hc.2
      rw [he', map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne,
        smul_zero, mul_zero]
      intro hST
      apply hS
      rw [show S₀ = insert k (T.erase l) from rfl, hST,
        Finset.erase_insert (fun h => hc.2 (Finset.mem_of_mem_erase h)), Finset.insert_erase hc.1]
    · rw [(s22b_Der_rOp b l k hlk S).1 (by tauto), map_zero, Finsupp.zero_apply, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem s22b_repr_Der_rOp_zero (l k : ι) (hlk : l ≠ k) (x : ExteriorAlgebra K M) (T : Finset ι)
    (hT : l ∉ T ∨ k ∈ T) : b.ExteriorAlgebra.repr (s22b_Der b (s22b_rOp b l k) x) T = 0 := by
  classical
  rw [s22b_repr_map]
  refine Finset.sum_eq_zero fun S _ => ?_
  by_cases hc : k ∈ S ∧ l ∉ S
  · obtain ⟨ε', -, he'⟩ := (s22b_Der_rOp b l k hlk S).2 hc.1 hc.2
    rw [he', map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne,
      smul_zero, mul_zero]
    intro hST
    rcases hT with hlT | hkT
    · exact hlT (hST ▸ Finset.mem_insert_self _ _)
    · rw [hST] at hkT
      simp [hlk.symm] at hkT
  · rw [(s22b_Der_rOp b l k hlk S).1 (by tauto), map_zero, Finsupp.zero_apply, mul_zero]

end MonoRepr

section Degree

variable {K : Type*} [Field K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*}
  [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K M)

omit [CharZero K] [LinearOrder ι] in
theorem s22b_Der_id_of_mem {k : ℕ} {x : ExteriorAlgebra K M} (hx : x ∈ ⋀[K]^k M) :
    s22b_Der b LinearMap.id x = (k : K) • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact s22b_Der_ιMulti_id b k v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- The monomials occurring in a vector of degree `k` have `k` factors. -/
theorem s22b_card_of_repr_ne {k : ℕ} {x : ExteriorAlgebra K M} (hx : x ∈ ⋀[K]^k M)
    (S : Finset ι) (hS : b.ExteriorAlgebra.repr x S ≠ 0) : S.card = k := by
  have h := congrArg (fun y => b.ExteriorAlgebra.repr y S) (s22b_Der_id_of_mem b hx)
  simp only [s22b_repr_Der_id, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have := mul_right_cancel₀ hS h
  exact_mod_cast this

omit [CharZero K] [Fintype ι] in
theorem s22b_basis_mem_exteriorPower (S : Finset ι) :
    b.ExteriorAlgebra S ∈ ⋀[K]^S.card M := by
  obtain ⟨t, -, -, he⟩ := s22b_basis_eq_ιMulti b S
  rw [he]
  exact ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩

omit [CharZero K] [LinearOrder ι] in
theorem s22b_Der_zero : s22b_Der b (0 : M →ₗ[K] M) = 0 := by
  simp [s22b_Der]

omit [CharZero K] [LinearOrder ι] in
theorem s22b_Der_finset_sum {κ : Type*} (s : Finset κ) (X : κ → M →ₗ[K] M) :
    s22b_Der b (∑ k ∈ s, X k) = ∑ k ∈ s, s22b_Der b (X k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s22b_Der_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, s22b_Der_add, ih]

end Degree

section S22bMul

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

theorem s22b_ιMulti_mul_ιMulti_comm (p q : ℕ) (a : Fin p → M) (b : Fin q → M) :
    ExteriorAlgebra.ιMulti K q b * ExteriorAlgebra.ιMulti K p a =
      (-1 : K) ^ (p * q) • (ExteriorAlgebra.ιMulti K p a * ExteriorAlgebra.ιMulti K q b) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, ih, mul_smul_comm, ← mul_assoc,
      s22b_ι_mul_ιMulti_comm, smul_mul_assoc, smul_smul, mul_assoc, ← ExteriorAlgebra.ιMulti_succ_apply]
    congr 1
    ring

theorem s22b_pqPiece_mul {A B : Submodule K M} {p q p' q' : ℕ} {x y : ExteriorAlgebra K M}
    (hx : x ∈ pqPiece A B p q) (hy : y ∈ pqPiece A B p' q') :
    x * y ∈ pqPiece A B (p + p') (q + q') := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a', b', ha', hb', rfl⟩ := hw
      have : ExteriorAlgebra.ιMulti K p a * ExteriorAlgebra.ιMulti K q b *
          (ExteriorAlgebra.ιMulti K p' a' * ExteriorAlgebra.ιMulti K q' b') =
          (-1 : K) ^ (p' * q) • (ExteriorAlgebra.ιMulti K (p + p') (Fin.append a a') *
            ExteriorAlgebra.ιMulti K (q + q') (Fin.append b b')) := by
        rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ExteriorAlgebra.ιMulti_mul_ιMulti, mul_assoc,
          ← mul_assoc (ExteriorAlgebra.ιMulti K q b), s22b_ιMulti_mul_ιMulti_comm, smul_mul_assoc,
          mul_smul_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ (ExteriorAlgebra.ιMulti K q b)]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, fun i => ?_, fun j => ?_, rfl⟩)
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · rw [Fin.append_left]; exact ha i
        · rw [Fin.append_right]; exact ha' i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · rw [Fin.append_left]; exact hb j
        · rw [Fin.append_right]; exact hb' j
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => rw [mul_add]; exact Submodule.add_mem _ hw hw'
    | smul c w _ hw => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hw
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add z z' _ _ hz hz' => rw [add_mul]; exact Submodule.add_mem _ hz hz'
  | smul c z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hz

theorem s22b_pqPiece_pow {A B : Submodule K M} {x : ExteriorAlgebra K M}
    (hx : x ∈ pqPiece A B 1 1) (a : ℕ) : x ^ a ∈ pqPiece A B a a := by
  induction a with
  | zero =>
    rw [pow_zero]
    exact Submodule.subset_span ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | succ a ih => rw [pow_succ]; exact s22b_pqPiece_mul ih hx

/-- An alternating map in top degree transforms by the determinant. -/
theorem s22b_alternating_comp {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]
    [Module K N] (e : Module.Basis ι K M) (f : M [⋀^ι]→ₗ[K] N) (T : M →ₗ[K] M) (v : ι → M) :
    f (T ∘ v) = LinearMap.det T • f v := by
  have key : ∀ w : ι → M, f w = e.det w • f e := by
    have h : f = (e.det : M [⋀^ι]→ₗ[K] K).smulRight (f e) := by
      refine e.ext_alternating fun i hi => ?_
      let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
      change f (e ∘ σ) = (e.det : M [⋀^ι]→ₗ[K] K).smulRight (f e) (e ∘ σ)
      simp [AlternatingMap.map_perm, Module.Basis.det_self, AlternatingMap.smulRight_apply]
    intro w
    conv_lhs => rw [h]
    rfl
  rw [key, key v, Module.Basis.det_comp, mul_smul]

end S22bMul

section S22bExtPow

/-- A vector lies in `⋀^k` iff all its monomials have `k` factors. -/
theorem s22b_mem_exteriorPower_iff {K : Type*} [Field K] [CharZero K] {M : Type*} [AddCommGroup M]
    [Module K M] {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K M) {k : ℕ}
    {x : ExteriorAlgebra K M} :
    x ∈ ⋀[K]^k M ↔ ∀ S, b.ExteriorAlgebra.repr x S ≠ 0 → S.card = k := by
  refine ⟨fun hx S hS => s22b_card_of_repr_ne b hx S hS, fun h => ?_⟩
  rw [← b.ExteriorAlgebra.sum_repr x]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : b.ExteriorAlgebra.repr x S = 0
  · rw [hS, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (h S hS ▸ s22b_basis_mem_exteriorPower b S)

end S22bExtPow

section S22bComplexify

variable {n : ℕ}

theorem s22b_bcH1_apply {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (w : H1 F n) (i : Fin (2 * n)) :
    bcH1 F F' n w i = algebraMap F F' (w i) := rfl

theorem s22b_bcH1_single {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (i : Fin (2 * n)) :
    bcH1 F F' n (Pi.single i 1) = Pi.single i 1 := by
  ext j
  rw [s22b_bcH1_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem s22b_span_bcH1 {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] : Submodule.span F' (Set.range (bcH1 F F' n)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun F' (Fin (2 * n))).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨Pi.single i 1, by rw [Pi.basisFun_apply]; exact s22b_bcH1_single i⟩

theorem s22b_linearMap_ext_bcH1 {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] {M : Type*} [AddCommGroup M] [Module F' M] {A B : H1 F' n →ₗ[F'] M}
    (h : ∀ w, A (bcH1 F F' n w) = B (bcH1 F F' n w)) : A = B :=
  LinearMap.ext_on_range s22b_span_bcH1 h

theorem s22b_complexifyH1_apply (A : Module.End ℝ (H1 ℝ n)) (w : H1 ℂ n) :
    complexifyH1 n A w = Matrix.mulVec ((LinearMap.toMatrix' A).map (algebraMap ℝ ℂ)) w := by
  rw [complexifyH1, Matrix.toLin_eq_toLin', LinearMap.toMatrix_eq_toMatrix', Matrix.toLin'_apply]

theorem s22b_complexifyH1_bcH1 (A : Module.End ℝ (H1 ℝ n)) (w : H1 ℝ n) :
    complexifyH1 n A (bcH1 ℝ ℂ n w) = bcH1 ℝ ℂ n (A w) := by
  ext i
  rw [s22b_complexifyH1_apply, s22b_bcH1_apply]
  have := RingHom.map_mulVec (algebraMap ℝ ℂ) (LinearMap.toMatrix' A) w i
  rw [LinearMap.toMatrix'_mulVec] at this
  exact this.symm

theorem s22b_complexifyV_basisV (A : Module.End ℝ (V ℝ n)) (k : Fin (2 * n + 2 * n)) :
    complexifyV n A (basisV ℂ n k) = bcV ℝ ℂ n (A (basisV ℝ n k)) := by
  rw [complexifyV, Matrix.toLin_self]
  conv_rhs => rw [← (basisV ℝ n).sum_repr (A (basisV ℝ n k))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, map_smul, s22b_bcV_basisV, algebraMap_smul]

theorem s22b_complexifyV_bcV (A : Module.End ℝ (V ℝ n)) (v : V ℝ n) :
    complexifyV n A (bcV ℝ ℂ n v) = bcV ℝ ℂ n (A v) := by
  have : ((complexifyV n A).restrictScalars ℝ) ∘ₗ bcV ℝ ℂ n = bcV ℝ ℂ n ∘ₗ A := by
    apply (basisV ℝ n).ext
    intro k
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      s22b_bcV_basisV, s22b_complexifyV_basisV]
  exact congrArg (fun f => f v) this

theorem s22b_complexifyV_productStructure (J : Module.End ℝ (H1 ℝ n)) :
    complexifyV n (productStructure n J) =
      (LinearMap.dualMap (complexifyH1 n J)).prodMap (-complexifyH1 n J) := by
  apply s22b_linearMap_ext_bcV (F := ℝ)
  intro v
  rw [s22b_complexifyV_bcV]
  obtain ⟨θ, w⟩ := v
  apply Prod.ext
  · show bcDual ℝ ℂ n (θ ∘ₗ J) = bcDual ℝ ℂ n θ ∘ₗ complexifyH1 n J
    apply s22b_linearMap_ext_bcH1 (F := ℝ)
    intro w'
    rw [LinearMap.comp_apply, s22b_complexifyH1_bcH1, s22b_bcDual_bcH1, s22b_bcDual_bcH1]
    rfl
  · show bcH1 ℝ ℂ n (-J w) = -complexifyH1 n J (bcH1 ℝ ℂ n w)
    rw [s22b_complexifyH1_bcH1, map_neg]

theorem s22b_complexifyH1_sq (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) :
    complexifyH1 n J * complexifyH1 n J = -1 := by
  apply s22b_linearMap_ext_bcH1 (F := ℝ)
  intro w
  rw [Module.End.mul_apply, s22b_complexifyH1_bcH1, s22b_complexifyH1_bcH1, ← Module.End.mul_apply,
    show J * J = -1 from hJ]
  simp

/-- A square root of `-1` splits a complex vector space into its `±i` eigenspaces. -/
theorem s22b_isCompl_eigen {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : T * T = -1) :
    IsCompl (Module.End.eigenspace T Complex.I) (Module.End.eigenspace T (-Complex.I)) := by
  have hT' : ∀ v, T (T v) = -v := fun v => by
    rw [← Module.End.mul_apply, hT]; simp
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [Module.End.mem_eigenspace_iff] at h1 h2
    have : (2 * Complex.I) • v = 0 := by
      have h3 : Complex.I • v - (-Complex.I) • v = 0 := by rw [← h1, ← h2, sub_self]
      rw [← sub_smul] at h3
      convert h3 using 2
      ring
    exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (2⁻¹ : ℂ) • (v - Complex.I • T v) + (2⁻¹ : ℂ) • (v + Complex.I • T v) := by
      module
    rw [hv]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · rw [Module.End.mem_eigenspace_iff, map_sub, map_smul, hT', smul_sub, smul_neg, smul_smul,
        Complex.I_mul_I]
      module
    · rw [Module.End.mem_eigenspace_iff, map_add, map_smul, hT', smul_add, smul_neg, smul_smul,
        neg_mul, Complex.I_mul_I]
      module

end S22bComplexify

section S22bHodgeH1

variable {n : ℕ} (J : Module.End ℝ (H1 ℝ n))

/-- Complex conjugation of `H¹(X, ℂ)` (coordinatewise). -/
noncomputable def s22b_cnj (w : H1 ℂ n) : H1 ℂ n := fun i => (starRingEnd ℂ) (w i)

theorem s22b_cnj_apply (w : H1 ℂ n) (i : Fin (2 * n)) :
    s22b_cnj w i = (starRingEnd ℂ) (w i) := rfl

theorem s22b_cnj_cnj (w : H1 ℂ n) : s22b_cnj (s22b_cnj w) = w := by
  ext i; simp [s22b_cnj]

theorem s22b_cnj_smul (c : ℂ) (w : H1 ℂ n) :
    s22b_cnj (c • w) = (starRingEnd ℂ) c • s22b_cnj w := by
  ext i; simp [s22b_cnj]

theorem s22b_cnj_sum {ι : Type*} (s : Finset ι) (w : ι → H1 ℂ n) :
    s22b_cnj (∑ i ∈ s, w i) = ∑ i ∈ s, s22b_cnj (w i) := by
  ext j; simp [s22b_cnj]

theorem s22b_complexifyH1_cnj (A : Module.End ℝ (H1 ℝ n)) (w : H1 ℂ n) :
    complexifyH1 n A (s22b_cnj w) = s22b_cnj (complexifyH1 n A w) := by
  ext i
  simp only [s22b_complexifyH1_apply, s22b_cnj_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    map_sum, map_mul, Complex.coe_algebraMap, Complex.conj_ofReal]

theorem s22b_cnj_mem_H01 {w : H1 ℂ n} (hw : w ∈ H10 n J) : s22b_cnj w ∈ H01 n J := by
  rw [H01, Module.End.mem_eigenspace_iff, s22b_complexifyH1_cnj,
    Module.End.mem_eigenspace_iff.mp hw, s22b_cnj_smul, Complex.conj_I]

theorem s22b_cnj_mem_H10 {w : H1 ℂ n} (hw : w ∈ H01 n J) : s22b_cnj w ∈ H10 n J := by
  rw [H10, Module.End.mem_eigenspace_iff, s22b_complexifyH1_cnj,
    Module.End.mem_eigenspace_iff.mp hw, s22b_cnj_smul, map_neg, Complex.conj_I, neg_neg]

theorem s22b_finrank_le_of_cnj {A B : Submodule ℂ (H1 ℂ n)} (h : ∀ w ∈ A, s22b_cnj w ∈ B) :
    Module.finrank ℂ A ≤ Module.finrank ℂ B := by
  let b := Module.finBasis ℂ A
  let v : Fin (Module.finrank ℂ A) → B := fun i => ⟨s22b_cnj (b i), h _ (b i).2⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, g i • s22b_cnj (b i : H1 ℂ n) = 0 := by
      have := congrArg B.subtype hg
      simpa [v] using this
    have h2 : ∑ i, (starRingEnd ℂ (g i)) • (b i : H1 ℂ n) = 0 := by
      have := congrArg s22b_cnj h1
      rw [s22b_cnj_sum] at this
      simp only [s22b_cnj_smul, s22b_cnj_cnj] at this
      rw [this]
      ext j; simp [s22b_cnj]
    have h3 : ∑ i, (starRingEnd ℂ (g i)) • b i = 0 := by
      apply Subtype.ext
      simpa using h2
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ h3 i
    simpa using this
  have := hli.fintype_card_le_finrank
  simpa using this

theorem s22b_isCompl_H10 (hJ : IsComplexStructure J) : IsCompl (H10 n J) (H01 n J) :=
  s22b_isCompl_eigen _ (s22b_complexifyH1_sq J hJ)

/-- `dim H^{1,0} = dim H^{0,1} = n`. -/
theorem s22b_finrank_H10 (hJ : IsComplexStructure J) :
    Module.finrank ℂ (H10 n J) = n ∧ Module.finrank ℂ (H01 n J) = n := by
  have h1 := s22b_finrank_le_of_cnj fun w hw => s22b_cnj_mem_H01 J hw
  have h2 := s22b_finrank_le_of_cnj fun w hw => s22b_cnj_mem_H10 J hw
  have hc := s22b_isCompl_H10 J hJ
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (H10 n J) (H01 n J)
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero] at hsum
  have : Module.finrank ℂ (H1 ℂ n) = 2 * n := by simp
  omega

/-- `I = productStructure J` squares to `-1` on `V_ℂ`. -/
theorem s22b_complexifyV_sq (hJ : IsComplexStructure J) :
    complexifyV n (productStructure n J) * complexifyV n (productStructure n J) = -1 := by
  have hJ' : ∀ w, J (J w) = -w := fun w => by
    rw [← Module.End.mul_apply, show J * J = -1 from hJ]; simp
  apply s22b_linearMap_ext_bcV (F := ℝ)
  intro v
  rw [Module.End.mul_apply, s22b_complexifyV_bcV, s22b_complexifyV_bcV]
  obtain ⟨θ, w⟩ := v
  have : productStructure n J (productStructure n J (θ, w)) = -(θ, w) := by
    apply Prod.ext
    · show (θ ∘ₗ J) ∘ₗ J = -θ
      ext x; simp [hJ']
    · show -J (-J w) = -w
      rw [map_neg, neg_neg, hJ']
  rw [this, map_neg]
  rfl

theorem s22b_isCompl_V10 (hJ : IsComplexStructure J) :
    IsCompl (V10 n (productStructure n J)) (V01 n (productStructure n J)) :=
  s22b_isCompl_eigen _ (s22b_complexifyV_sq J hJ)

/-- `I` is an isometry of the pairing on `V_ℂ`. -/
theorem s22b_pairing_complexifyV (hJ : IsComplexStructure J) (v w : V ℂ n) :
    pairing ℂ n (complexifyV n (productStructure n J) v) (complexifyV n (productStructure n J) w) =
      pairing ℂ n v w := by
  have hJ2 := s22b_complexifyH1_sq J hJ
  have hJ' : ∀ x, complexifyH1 n J (complexifyH1 n J x) = -x := fun x => by
    rw [← Module.End.mul_apply, hJ2]; simp
  rw [s22b_complexifyV_productStructure]
  obtain ⟨θ, x⟩ := v
  obtain ⟨θ', x'⟩ := w
  simp only [QuadraticMap.polarBilin_apply_apply, TauCeti.polar_dualProd, LinearMap.prodMap_apply,
    LinearMap.dualMap_apply', LinearMap.comp_apply, LinearMap.neg_apply, map_neg, hJ', neg_neg]

theorem s22b_pairing_V10 (hJ : IsComplexStructure J) {v w : V ℂ n}
    (hv : v ∈ V10 n (productStructure n J)) (hw : w ∈ V10 n (productStructure n J)) :
    pairing ℂ n v w = 0 := by
  have h := s22b_pairing_complexifyV J hJ v w
  rw [Module.End.mem_eigenspace_iff.mp hv, Module.End.mem_eigenspace_iff.mp hw] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have : (2 : ℂ) * pairing ℂ n v w = 0 := by
    linear_combination -h + (pairing ℂ n v w) * Complex.I_mul_I
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

theorem s22b_pairing_V01 (hJ : IsComplexStructure J) {v w : V ℂ n}
    (hv : v ∈ V01 n (productStructure n J)) (hw : w ∈ V01 n (productStructure n J)) :
    pairing ℂ n v w = 0 := by
  have h := s22b_pairing_complexifyV J hJ v w
  rw [Module.End.mem_eigenspace_iff.mp hv, Module.End.mem_eigenspace_iff.mp hw] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have : (2 : ℂ) * pairing ℂ n v w = 0 := by
    linear_combination -h + (pairing ℂ n v w) * Complex.I_mul_I
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

end S22bHodgeH1

section S22bAlt

theorem s22b_map_map {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (f g : M →ₗ[K] M) (x : ExteriorAlgebra K M) :
    ExteriorAlgebra.map g (ExteriorAlgebra.map f x) = ExteriorAlgebra.map (g ∘ₗ f) x := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end S22bAlt

section S22bSpinGeneral

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem s22b_m_ι_apply' (θ : Module.Dual F (H1 F n)) (w : H1 F n) (x : S F n) :
    m F n (ι (Q F n) (θ, w)) x = ExteriorAlgebra.ι F w * x + D F n θ x := by
  simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, L, LinearMap.mul_apply']

theorem s22b_m_anticomm (v w : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) + m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) =
      pairing F n v w • s := by
  have h := congrArg (fun x => m F n x s) (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q F n) v w)
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, AlgHom.commutes,
    Module.algebraMap_end_apply] at h
  rw [h, QuadraticMap.polarBilin_apply_apply]

theorem s22b_Q_of_mem_ann {u : S F n} (hu : u ≠ 0) {v : V F n} (hv : v ∈ ann F n u) :
    Q F n v = 0 := by
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  have h : m F n (ι (Q F n) v * ι (Q F n) v) u = Q F n v • u := by
    rw [ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]
  rw [map_mul, Module.End.mul_apply, hv', map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hu

theorem s22b_pairing_of_mem_ann {u : S F n} (hu : u ≠ 0) {v w : V F n} (hv : v ∈ ann F n u)
    (hw : w ∈ ann F n u) : pairing F n v w = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, s22b_Q_of_mem_ann hu hv,
    s22b_Q_of_mem_ann hu hw, s22b_Q_of_mem_ann hu (Submodule.add_mem _ hv hw)]
  simp

omit [CharZero F] in
/-- An isotropic subspace of `V_F` has dimension at most `2n`. -/
theorem s22b_finrank_le_of_isotropic {W : Submodule F (V F n)}
    (hW : ∀ a ∈ W, ∀ b ∈ W, pairing F n a b = 0) : Module.finrank F W ≤ 2 * n := by
  have hnd : (pairing F n).Nondegenerate :=
    ⟨fun x hx => s22b_pairing_nondeg x hx,
      fun y hy => s22b_pairing_nondeg y fun x => by rw [s22b_pairing_comm]; exact hy x⟩
  have hle : W ≤ (pairing F n).orthogonal W := fun x hx y hy => hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd, Module.finrank_eq_card_basis (basisV F n),
    Fintype.card_fin] at h1
  omega

theorem s22b_mem_even_of_involute {M : Type*} [AddCommGroup M] [Module F M]
    {q : QuadraticForm F M} {x : CliffordAlgebra q} (h : involute x = x) : x ∈ evenOdd q 0 := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩, hsum, -⟩ :=
    Submodule.existsUnique_add_of_isCompl (evenOdd_isCompl q) x
  simp only at hsum
  have h1 : involute x = x₀ - x₁ := by
    rw [← hsum, map_add, involute_eq_of_mem_even hx₀, involute_eq_of_mem_odd hx₁, sub_eq_add_neg]
  have h2 : (2 : F) • x₁ = 0 := by
    have h3 := h1.symm.trans h
    rw [← hsum] at h3
    rw [two_smul]
    have : x₀ - x₁ - (x₀ + x₁) = -(x₁ + x₁) := by abel
    rw [h3, sub_self] at this
    exact neg_eq_zero.mp this.symm
  have hx₁0 : x₁ = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [← hsum, hx₁0, add_zero]
  exact hx₀

/-- `(m_x s, t)_S = (s, m_{τ(x)} t)_S` for `x ∈ C(V_F)`, from [Chevalley, III.2.2]. -/
theorem s22b_mukai_m_rev (x : C F n) (s t : S F n) :
    mukai F n (m F n x s) t = mukai F n s (m F n (reverse x) t) := by
  induction x using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, LinearMap.smul_apply, map_smul]
  | ι v => rw [reverse_ι]; exact chevalley_III_2_2 F n v s t
  | mul x y hx hy =>
    rw [map_mul, Module.End.mul_apply, hx, hy, reverse.map_mul, map_mul, Module.End.mul_apply]
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hx, hy, map_add, map_add,
      LinearMap.add_apply, map_add]

omit [CharZero F] in
/-- Naturality of the contraction: `⋀T (θ ⌋ s) = (θ ∘ T⁻¹) ⌋ (⋀T s)`. -/
theorem s22b_map_D (T T' : Module.End F (H1 F n)) (hT : T' ∘ₗ T = LinearMap.id)
    (θ : Module.Dual F (H1 F n)) (s : S F n) :
    ExteriorAlgebra.map T (D F n θ s) = D F n (θ ∘ₗ T') (ExteriorAlgebra.map T s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, contractLeft_algebraMap, map_zero, AlgHom.commutes]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x w hx =>
    have h1 : D F n θ (ι (0 : QuadraticForm F (H1 F n)) w * x) =
        θ w • x - ι (0 : QuadraticForm F (H1 F n)) w * D F n θ x :=
      contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w x
    have h2 : ∀ y, D F n (θ ∘ₗ T') (ι (0 : QuadraticForm F (H1 F n)) (T w) * y) =
        (θ ∘ₗ T') (T w) • y - ι (0 : QuadraticForm F (H1 F n)) (T w) * D F n (θ ∘ₗ T') y :=
      fun y => contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) (θ ∘ₗ T') (T w) y
    have h3 : ExteriorAlgebra.map T (ι (0 : QuadraticForm F (H1 F n)) w) =
        ι (0 : QuadraticForm F (H1 F n)) (T w) := ExteriorAlgebra.map_apply_ι T w
    rw [h1, map_sub, map_smul, map_mul, h3, hx, map_mul, h3, h2]
    congr 2
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply T' T, hT, LinearMap.id_apply]

/-- Conjugating `m_v` by `⋀T`: `⋀T ∘ m_{(θ, w)} = m_{(θ ∘ T⁻¹, T w)} ∘ ⋀T`. -/
theorem s22b_map_m_ι (T T' : Module.End F (H1 F n)) (hT : T' ∘ₗ T = LinearMap.id) (v : V F n)
    (s : S F n) :
    ExteriorAlgebra.map T (m F n (ι (Q F n) v) s) =
      m F n (ι (Q F n) (v.1 ∘ₗ T', T v.2)) (ExteriorAlgebra.map T s) := by
  obtain ⟨θ, w⟩ := v
  rw [s22b_m_ι_apply', s22b_m_ι_apply', map_add, map_mul, ExteriorAlgebra.map_apply_ι,
    s22b_map_D T T' hT]

omit [CharZero F] in
/-- `⋀T` acts on the top degree `⋀^{2n} H¹` by `det T`. -/
theorem s22b_map_top (T : Module.End F (H1 F n)) {x : S F n}
    (hx : x ∈ ⋀[F]^(2 * n) (H1 F n)) : ExteriorAlgebra.map T x = LinearMap.det T • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact s22b_alternating_comp (Pi.basisFun F (Fin (2 * n))) (ExteriorAlgebra.ιMulti F (2 * n)) T v
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

omit [CharZero F] in
theorem s22b_pt_mem : pt F n ∈ ⋀[F]^(2 * n) (H1 F n) := by
  have h := s22b_basis_mem_exteriorPower (Pi.basisFun F (Fin (2 * n))) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

omit [CharZero F] in
theorem s22b_mukai_one_pt : mukai F n 1 (pt F n) = 1 := by
  show integral F n (tau F n 1 * pt F n) = 1
  rw [show tau F n 1 = 1 from CliffordAlgebra.reverse.map_one, one_mul, integral, pt,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- `m ∘ involute = Π ∘ m ∘ Π` with `Π = ⋀(-1)` the parity operator of `S`. -/
theorem s22b_m_involute (x : C F n) (s : S F n) :
    m F n (involute x) s =
      ExteriorAlgebra.map (-LinearMap.id) (m F n x (ExteriorAlgebra.map (-LinearMap.id) s)) := by
  have hT : (-LinearMap.id : Module.End F (H1 F n)) ∘ₗ (-LinearMap.id) = LinearMap.id :=
    LinearMap.ext fun w => by simp
  have hPar : ∀ y : S F n, ExteriorAlgebra.map (-LinearMap.id : Module.End F (H1 F n))
      (ExteriorAlgebra.map (-LinearMap.id) y) = y := by
    intro y
    rw [s22b_map_map, hT, ExteriorAlgebra.map_id, AlgHom.id_apply]
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [involute.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, hPar]
  | ι v =>
    rw [involute_ι, map_neg, LinearMap.neg_apply, s22b_map_m_ι _ _ hT, hPar]
    obtain ⟨θ, w⟩ := v
    have : ((θ, w) : V F n).1 ∘ₗ (-LinearMap.id) = -θ := by ext; simp
    rw [this, show (-LinearMap.id : Module.End F (H1 F n)) w = -w by simp,
      show ((-θ, -w) : V F n) = -(θ, w) from rfl, map_neg, map_neg, LinearMap.neg_apply]
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hy, hx, hPar]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]

/-- **The spin lift of `⋀T`**: for an automorphism `T` of `H¹(X, F)` with `det T = 1` there is
`g ∈ Spin(V_F)` with `m(g) = ⋀T` and `ρ(g)(θ, w) = (θ ∘ T⁻¹, T w)`. -/
theorem s22b_exists_spin_map (hn : 0 < n) (T T' : Module.End F (H1 F n))
    (hT : T' ∘ₗ T = LinearMap.id) (hT' : T ∘ₗ T' = LinearMap.id) (hdet : LinearMap.det T = 1) :
    ∃ g : Spin F n, m F n (g : C F n) = (ExteriorAlgebra.map T).toLinearMap ∧
      ∀ v : V F n, rho F n g v = (v.1 ∘ₗ T', T v.2) := by
  have hminj : Function.Injective (m F n) := (glo_prop3_2_1_e_field F n).1
  obtain ⟨g, hmg⟩ := (glo_prop3_2_1_e_field F n).2 (ExteriorAlgebra.map T).toLinearMap
  obtain ⟨g', hmg'⟩ := (glo_prop3_2_1_e_field F n).2 (ExteriorAlgebra.map T').toLinearMap
  have hmap : ∀ (A B : Module.End F (H1 F n)), A ∘ₗ B = LinearMap.id → ∀ s : S F n,
      ExteriorAlgebra.map A (ExteriorAlgebra.map B s) = s := by
    intro A B hAB s
    rw [s22b_map_map, hAB, ExteriorAlgebra.map_id, AlgHom.id_apply]
  have hgg' : g * g' = 1 := hminj (by
    rw [map_mul, hmg, hmg', map_one]
    exact LinearMap.ext fun s => hmap T T' hT' s)
  have hg'g : g' * g = 1 := hminj (by
    rw [map_mul, hmg, hmg', map_one]
    exact LinearMap.ext fun s => hmap T' T hT s)
  have hconj : ∀ v : V F n, g * ι (Q F n) v * g' = ι (Q F n) (v.1 ∘ₗ T', T v.2) := by
    intro v
    apply hminj
    refine LinearMap.ext fun s => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hmg, hmg',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, s22b_map_m_ι T T' hT, hmap T T' hT']
  have hinv : involute g = g := by
    apply hminj
    refine LinearMap.ext fun s => ?_
    have hT3 : ((-LinearMap.id : Module.End F (H1 F n)) ∘ₗ T) ∘ₗ (-LinearMap.id) = T :=
      LinearMap.ext fun w => by simp
    rw [s22b_m_involute, hmg, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, s22b_map_map,
      s22b_map_map, hT3]
  have heven : g ∈ evenOdd (Q F n) 0 := s22b_mem_even_of_involute hinv
  let gu : (C F n)ˣ := ⟨g, g', hgg', hg'g⟩
  have hcl : gu ∈ cliffordGroup F n := fun v => ⟨_, hconj v⟩
  obtain ⟨c, hc⟩ := exists_mul_reverse_eq_algebraMap F n gu hcl
  have hc' : g * reverse g = algebraMap F (C F n) c := hc
  have hrev : reverse g = algebraMap F (C F n) c * g' := by
    calc reverse g = g' * (g * reverse g) := by rw [← mul_assoc, hg'g, one_mul]
      _ = g' * algebraMap F (C F n) c := by rw [hc']
      _ = algebraMap F (C F n) c * g' := (Algebra.commutes c g').symm
  have hc1 : c = 1 := by
    have h1 := s22b_mukai_m_rev g 1 (m F n g (pt F n))
    have hL : m F n g 1 = 1 := by rw [hmg, AlgHom.toLinearMap_apply, map_one]
    have hpt : m F n g (pt F n) = pt F n := by
      rw [hmg, AlgHom.toLinearMap_apply, s22b_map_top T s22b_pt_mem, hdet, one_smul]
    have hR : m F n (reverse g) (m F n g (pt F n)) = c • pt F n := by
      rw [hrev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (m F n g'), ← map_mul, hg'g,
        map_one, Module.End.one_apply, AlgHom.commutes, Module.algebraMap_end_apply]
    rw [hR, hL, hpt, map_smul, s22b_mukai_one_pt, smul_eq_mul, mul_one] at h1
    exact h1.symm
  have hrev1 : reverse g = g' := by rw [hrev, hc1, map_one, one_mul]
  have hstar : star g = g' := by rw [CliffordAlgebra.star_def, hinv, hrev1]
  have hspin : g ∈ spinGroup (Q F n) :=
    (mem_spin_iff F n hn g).mpr ⟨heven, by rw [hstar, hgg'], fun v => ⟨_, by
      rw [hstar]; exact hconj v⟩⟩
  refine ⟨⟨g, hspin⟩, hmg, fun v => ?_⟩
  apply CliffordAlgebra.ι_injective (Q F n)
  rw [ι_rho]
  show g * ι (Q F n) v * star g = _
  rw [hstar, hconj]

end S22bSpinGeneral

section S22bDet

/-- The determinant of an endomorphism acting by scalars on two complementary subspaces. -/
theorem s22b_det_of_isCompl {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {A B : Submodule K M} (hAB : IsCompl A B) (T : Module.End K M)
    (a b : K) (hA : ∀ x ∈ A, T x = a • x) (hB : ∀ x ∈ B, T x = b • x) :
    LinearMap.det T = a ^ Module.finrank K A * b ^ Module.finrank K B := by
  let e := Submodule.prodEquivOfIsCompl A B hAB
  have hT : T = (e : (A × B) →ₗ[K] M) ∘ₗ ((a • LinearMap.id : Module.End K A).prodMap
      (b • LinearMap.id : Module.End K B)) ∘ₗ (e.symm : M →ₗ[K] (A × B)) := by
    refine LinearMap.ext fun x => ?_
    conv_lhs => rw [← e.apply_symm_apply x]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, e,
      Submodule.coe_prodEquivOfIsCompl', map_add, Submodule.coe_smul]
    rw [hA _ ((Submodule.prodEquivOfIsCompl A B hAB).symm x).1.2,
      hB _ ((Submodule.prodEquivOfIsCompl A B hAB).symm x).2.2]
  rw [hT, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

end S22bDet

section S22bBaseChange

variable {n : ℕ} {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']

/-- Base change preserves linear independence in `V`. -/
theorem s22b_linearIndependent_bcV {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V F n)
    (hv : LinearIndependent F v) : LinearIndependent F' (fun i => bcV F F' n (v i)) := by
  have hker : LinearMap.ker (Fintype.linearCombination F v) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearCombination_apply] at hc
    exact funext (Fintype.linearIndependent_iff.mp hv c hc)
  obtain ⟨G, hG⟩ := (Fintype.linearCombination F v).exists_leftInverse_of_injective hker
  let G' : V F' n →ₗ[F'] (ι → F') :=
    (basisV F' n).constr F' fun k i => algebraMap F F' (G (basisV F n k) i)
  have hG' : (G'.restrictScalars F) ∘ₗ bcV F F' n =
      ((Algebra.linearMap F F').compLeft ι) ∘ₗ G := by
    apply (basisV F n).ext
    intro k
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      s22b_bcV_basisV, G', Module.Basis.constr_basis]
    rfl
  have hGv : ∀ i, G (v i) = Pi.single i 1 := by
    intro i
    have := congrArg (fun f => f (Pi.single i 1)) hG
    simpa using this
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (fun x => G' x j) hc
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_zero,
    Pi.zero_apply] at h1
  have h2 : ∀ i, G' (bcV F F' n (v i)) j = algebraMap F F' ((Pi.single i (1 : F) : ι → F) j) := by
    intro i
    have := congrArg (fun f => f (v i) j) hG'
    simpa [hGv] using this
  simp only [h2] at h1
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij.symm])
    (fun h => absurd (Finset.mem_univ _) h)] at h1
  simpa using h1

/-- `dim_{F'} span(W_{F'}) = dim_F W`. -/
theorem s22b_finrank_span_bcV (W : Submodule F (V F n)) :
    Module.finrank F' (Submodule.span F' (bcV F F' n '' (W : Set (V F n)))) =
      Module.finrank F W := by
  classical
  let b := Module.finBasis F W
  have hli : LinearIndependent F' (fun i => bcV F F' n ((b i : W) : V F n)) :=
    s22b_linearIndependent_bcV _ (b.linearIndependent.map' W.subtype W.ker_subtype)
  have heq : Submodule.span F' (bcV F F' n '' (W : Set (V F n))) =
      Submodule.span F' (Set.range fun i => bcV F F' n ((b i : W) : V F n)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      have h1 := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at h1
      rw [← h1, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul, ← algebraMap_smul F']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
  rw [heq, finrank_span_eq_card hli, Fintype.card_fin]

omit [CharZero F] [CharZero F'] in
theorem s22b_bcS_involute (s : S F n) :
    bcS F F' n (involute s) = involute (bcS F F' n s) := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [involute.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n),
      involute.commutes]
  | ι w =>
    rw [involute_ι, map_neg]
    show -bcS F F' n (ExteriorAlgebra.ι F w) = involute (bcS F F' n (ExteriorAlgebra.ι F w))
    rw [s22b_bcS_ι]
    exact (involute_ι _).symm
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [CharZero F] in
theorem s22b_bcS_mem_Splus {s : S F n} (hs : s ∈ Splus F n) : bcS F F' n s ∈ Splus F' n :=
  s22b_mem_even_of_involute (by rw [← s22b_bcS_involute, involute_eq_of_mem_even hs])

/-- The annihilator of a base-changed pure spinor is the span of the base-changed annihilator. -/
theorem s22b_ann_bcS (hn : 0 < n) {u : S F n} (hu : IsEvenPureSpinor F n u) :
    ann F' n (bcS F F' n u) = Submodule.span F' (bcV F F' n '' (ann F n u : Set (V F n))) := by
  have hu0 : bcS F F' n u ≠ 0 := fun h =>
    hu.ne_zero hn (s22b_bcS_injective (F' := F') (by rw [h, map_zero]))
  have hle : Submodule.span F' (bcV F F' n '' (ann F n u : Set (V F n))) ≤ ann F' n (bcS F F' n u) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show m F' n (ι (Q F' n) (bcV F F' n v)) (bcS F F' n u) = 0
    rw [← s22b_bcC_ι, s22b_m_bcC_bcS]
    have hv' : m F n (ι (Q F n) v) u = 0 := hv
    rw [hv', map_zero]
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [s22b_finrank_span_bcV, hu.2.2]
  exact s22b_finrank_le_of_isotropic fun a ha b hb => s22b_pairing_of_mem_ann hu0 ha hb

theorem s22b_isEvenPureSpinor_bcS (hn : 0 < n) {u : S F n} (hu : IsEvenPureSpinor F n u) :
    IsEvenPureSpinor F' n (bcS F F' n u) := by
  have hu0 : bcS F F' n u ≠ 0 := fun h =>
    hu.ne_zero hn (s22b_bcS_injective (F' := F') (by rw [h, map_zero]))
  refine ⟨s22b_bcS_mem_Splus hu.1, fun v hv => s22b_Q_of_mem_ann hu0 hv, ?_⟩
  rw [s22b_ann_bcS hn hu, s22b_finrank_span_bcV, hu.2.2]

end S22bBaseChange

section S22bTorus

variable {n : ℕ} (J : Module.End ℝ (H1 ℝ n))

/-- `T_s = 5/4 + s J` on `H¹(X, ℂ)`; for `s = ∓3i/4` it acts by `2, 1/2` (resp. `1/2, 2`) on
`H^{1,0}, H^{0,1}`. -/
noncomputable def s22b_T (s : ℂ) : Module.End ℂ (H1 ℂ n) :=
  (5 / 4 : ℂ) • LinearMap.id + s • complexifyH1 n J

theorem s22b_T_apply (s : ℂ) (w : H1 ℂ n) :
    s22b_T J s w = (5 / 4 : ℂ) • w + s • complexifyH1 n J w := rfl

theorem s22b_T_comp (hJ : IsComplexStructure J) (s : ℂ) (hs : s * s = -9 / 16) :
    s22b_T J s ∘ₗ s22b_T J (-s) = LinearMap.id := by
  have hJ2 := s22b_complexifyH1_sq J hJ
  have hJ' : ∀ x, complexifyH1 n J (complexifyH1 n J x) = -x := fun x => by
    rw [← Module.End.mul_apply, hJ2]; simp
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, s22b_T_apply, s22b_T_apply, map_add, map_smul, map_smul, hJ',
    LinearMap.id_apply]
  have : (5 / 4 : ℂ) • ((5 / 4 : ℂ) • w + -s • complexifyH1 n J w) +
      s • ((5 / 4 : ℂ) • complexifyH1 n J w + -s • -w) = ((25 / 16 : ℂ) + s * s) • w := by
    module
  rw [this, hs]
  norm_num

theorem s22b_T_H10 (s : ℂ) {w : H1 ℂ n} (hw : w ∈ H10 n J) :
    s22b_T J s w = ((5 / 4 : ℂ) + s * Complex.I) • w := by
  rw [s22b_T_apply, Module.End.mem_eigenspace_iff.mp hw, smul_smul, ← add_smul]

theorem s22b_T_H01 (s : ℂ) {w : H1 ℂ n} (hw : w ∈ H01 n J) :
    s22b_T J s w = ((5 / 4 : ℂ) - s * Complex.I) • w := by
  rw [s22b_T_apply, Module.End.mem_eigenspace_iff.mp hw, smul_smul, ← add_smul]
  congr 1
  ring

theorem s22b_c_sq : (3 / 4 * Complex.I) * (3 / 4 * Complex.I) = (-9 / 16 : ℂ) := by
  ring_nf
  rw [Complex.I_sq]
  ring

theorem s22b_c_sq' : (-(3 / 4 * Complex.I)) * (-(3 / 4 * Complex.I)) = (-9 / 16 : ℂ) := by
  rw [neg_mul_neg, s22b_c_sq]

theorem s22b_val_two : (5 / 4 : ℂ) + -(3 / 4 * Complex.I) * Complex.I = 2 := by
  ring_nf; rw [Complex.I_sq]; ring

theorem s22b_val_half : (5 / 4 : ℂ) - -(3 / 4 * Complex.I) * Complex.I = 1 / 2 := by
  ring_nf; rw [Complex.I_sq]; ring

theorem s22b_val_half' : (5 / 4 : ℂ) + (3 / 4 * Complex.I) * Complex.I = 1 / 2 := by
  ring_nf; rw [Complex.I_sq]; ring

theorem s22b_val_two' : (5 / 4 : ℂ) - (3 / 4 * Complex.I) * Complex.I = 2 := by
  ring_nf; rw [Complex.I_sq]; ring

/-- `det T = 2^n (1/2)^n = 1`. -/
theorem s22b_det_T (hJ : IsComplexStructure J) :
    LinearMap.det (s22b_T J (-(3 / 4 * Complex.I))) = 1 := by
  rw [s22b_det_of_isCompl (s22b_isCompl_H10 J hJ) _ 2 (1 / 2)
    (fun w hw => by rw [s22b_T_H10 J _ hw, s22b_val_two])
    (fun w hw => by rw [s22b_T_H01 J _ hw, s22b_val_half]),
    (s22b_finrank_H10 J hJ).1, (s22b_finrank_H10 J hJ).2, ← mul_pow]
  norm_num

/-- The spin lift `g` of `⋀T`, `T = 2` on `H^{1,0}` and `1/2` on `H^{0,1}`: an element of the
(complexified) circle of the Hodge structure. `ρ(g)` acts by `1/2` on `V^{1,0}` and `2` on `V^{0,1}`. -/
theorem s22b_exists_torus (hn : 0 < n) (hJ : IsComplexStructure J) :
    ∃ g : Spin ℂ n, m ℂ n (g : C ℂ n) =
        (ExteriorAlgebra.map (s22b_T J (-(3 / 4 * Complex.I)))).toLinearMap ∧
      (∀ v ∈ V10 n (productStructure n J), rho ℂ n g v = (1 / 2 : ℂ) • v) ∧
      (∀ v ∈ V01 n (productStructure n J), rho ℂ n g v = (2 : ℂ) • v) := by
  have hTT' : s22b_T J (-(3 / 4 * Complex.I)) ∘ₗ s22b_T J (3 / 4 * Complex.I) =
      LinearMap.id := by
    have := s22b_T_comp J hJ (-(3 / 4 * Complex.I)) s22b_c_sq'
    rwa [neg_neg] at this
  obtain ⟨g, hmg, hrho⟩ := s22b_exists_spin_map hn (s22b_T J (-(3 / 4 * Complex.I)))
    (s22b_T J (3 / 4 * Complex.I)) (s22b_T_comp J hJ (3 / 4 * Complex.I) s22b_c_sq) hTT'
    (s22b_det_T J hJ)
  refine ⟨g, hmg, fun v hv => ?_, fun v hv => ?_⟩
  · have hv' := Module.End.mem_eigenspace_iff.mp hv
    rw [s22b_complexifyV_productStructure] at hv'
    obtain ⟨θ, w⟩ := v
    have h1 : θ ∘ₗ complexifyH1 n J = Complex.I • θ := congrArg Prod.fst hv'
    have h2 : -complexifyH1 n J w = Complex.I • w := congrArg Prod.snd hv'
    have hw : w ∈ H01 n J := by
      rw [H01, Module.End.mem_eigenspace_iff, neg_smul, ← h2, neg_neg]
    rw [hrho]
    apply Prod.ext
    · show θ ∘ₗ s22b_T J (3 / 4 * Complex.I) = (1 / 2 : ℂ) • θ
      refine LinearMap.ext fun x => ?_
      have hx := congrArg (fun f => f x) h1
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at hx ⊢
      rw [s22b_T_apply, map_add, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul,
        ← s22b_val_half']
      ring
    · show s22b_T J (-(3 / 4 * Complex.I)) w = (1 / 2 : ℂ) • w
      rw [s22b_T_H01 J _ hw, s22b_val_half]
  · have hv' := Module.End.mem_eigenspace_iff.mp hv
    rw [s22b_complexifyV_productStructure] at hv'
    obtain ⟨θ, w⟩ := v
    have h1 : θ ∘ₗ complexifyH1 n J = (-Complex.I) • θ := congrArg Prod.fst hv'
    have h2 : -complexifyH1 n J w = (-Complex.I) • w := congrArg Prod.snd hv'
    have hw : w ∈ H10 n J := by
      rw [H10, Module.End.mem_eigenspace_iff, ← neg_neg (complexifyH1 n J w), h2, neg_smul,
        neg_neg]
    rw [hrho]
    apply Prod.ext
    · show θ ∘ₗ s22b_T J (3 / 4 * Complex.I) = (2 : ℂ) • θ
      refine LinearMap.ext fun x => ?_
      have hx := congrArg (fun f => f x) h1
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at hx ⊢
      rw [s22b_T_apply, map_add, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul,
        ← s22b_val_two']
      ring
    · show s22b_T J (-(3 / 4 * Complex.I)) w = (2 : ℂ) • w
      rw [s22b_T_H10 J _ hw, s22b_val_two]

end S22bTorus

section S22bTrans

variable {n : ℕ} {d : ℚ}

theorem s22b_bcS_trans (x : S ℚ n) : bcS (Kd d) ℂ n (bcS ℚ (Kd d) n x) = bcS ℚ ℂ n x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ (Kd d) (S (Kd d) n),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι w =>
    show bcS (Kd d) ℂ n (bcS ℚ (Kd d) n (ExteriorAlgebra.ι ℚ w)) = bcS ℚ ℂ n (ExteriorAlgebra.ι ℚ w)
    rw [s22b_bcS_ι, s22b_bcS_ι, s22b_bcS_ι]
    congr 1
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end S22bTrans

section S22bVarphi

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `m(ι_X(s)) = L_s`: the embedded classes of `X` act by cup product. -/
theorem s22b_m_iotaX (s y : S F n) : m F n (iotaX F n s) y = s * y := by
  induction s using CliffordAlgebra.induction generalizing y with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Algebra.smul_def]
  | ι w =>
    show m F n (iotaX F n (ExteriorAlgebra.ι F w)) y = ExteriorAlgebra.ι F w * y
    rw [show iotaX F n (ExteriorAlgebra.ι F w) = ι (Q F n) ((0 : Module.Dual F (H1 F n)), w) from
      ExteriorAlgebra.lift_ι_apply F _ _ w, s22b_m_ι_apply', map_zero, LinearMap.zero_apply,
      add_zero]
  | mul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, hb, ha, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_mul]

omit [CharZero F] in
theorem s22b_iotaXHat_ι (θ : Module.Dual F (H1 F n)) :
    iotaXHat F n (ExteriorAlgebra.ι F θ) = ι (Q F n) (θ, (0 : H1 F n)) :=
  ExteriorAlgebra.lift_ι_apply F _ _ θ

omit [CharZero F] in
theorem s22b_iotaXHat_ιMulti {k : ℕ} (θ : Fin k → Module.Dual F (H1 F n)) :
    iotaXHat F n (ExteriorAlgebra.ιMulti F k θ) =
      ((List.ofFn fun i => ((θ i, (0 : H1 F n)) : V F n)).map (ι (Q F n))).prod := by
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 2
  funext i
  exact s22b_iotaXHat_ι (θ i)

theorem s22b_m_ι_dual (θ : Module.Dual F (H1 F n)) (y : S F n) :
    m F n (ι (Q F n) (θ, (0 : H1 F n))) y = D F n θ y := by
  rw [s22b_m_ι_apply', map_zero, zero_mul, zero_add]

omit [CharZero F] in
/-- Contraction by a functional vanishing on all the vectors kills their product. -/
theorem s22b_D_ιMulti_eq_zero {k : ℕ} (θ : Module.Dual F (H1 F n)) (v : Fin k → H1 F n)
    (h : ∀ i, θ (v i) = 0) : D F n θ (ExteriorAlgebra.ιMulti F k v) = 0 := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply]
    exact contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) θ
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ (v 0)
      (ExteriorAlgebra.ιMulti F k (Matrix.vecTail v))
    rw [show D F n θ = contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ from rfl]
    erw [this]
    rw [h 0, zero_smul, ← show D F n θ = contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ
      from rfl, ih (Matrix.vecTail v) (fun i => h i.succ), mul_zero, sub_zero]

/-- **Contracting from the front**: `θ_{k-1} ⌋ ⋯ θ_0 ⌋ (v_0 ∧ ⋯ ∧ v_{k-1}) = 1` for dual
families. -/
theorem s22b_contract_front {k : ℕ} (θ : Fin k → Module.Dual F (H1 F n)) (v : Fin k → H1 F n)
    (h : ∀ i j, θ i (v j) = if i = j then 1 else 0) :
    m F n ((List.ofFn fun i => ((θ i, (0 : H1 F n)) : V F n)).map (ι (Q F n))).reverse.prod
      (ExteriorAlgebra.ιMulti F k v) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      map_mul, Module.End.mul_apply, s22b_m_ι_dual, ExteriorAlgebra.ιMulti_succ_apply]
    have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) (θ 0) (v 0)
      (ExteriorAlgebra.ιMulti F k (Matrix.vecTail v))
    rw [show D F n (θ 0) = contractLeft (Q := (0 : QuadraticForm F (H1 F n))) (θ 0) from rfl]
    erw [h1]
    rw [← show D F n (θ 0) = contractLeft (Q := (0 : QuadraticForm F (H1 F n))) (θ 0) from rfl,
      s22b_D_ιMulti_eq_zero (θ 0) (Matrix.vecTail v) (fun i => by
        rw [Matrix.vecTail, Function.comp_apply, h]; exact ite_eq_right (Fin.succ_ne_zero i).symm),
      mul_zero, sub_zero, h, ite_eq_left_iff.mpr (fun h' => absurd rfl h'), one_smul]
    exact ih (fun i => θ i.succ) (Matrix.vecTail v) (fun i j => by
      rw [Matrix.vecTail, Function.comp_apply, h]; simp)

/-- The increasing enumeration of a finset, as used by `Module.Basis.ExteriorAlgebra`. -/
theorem s22b_basis_eq_ιMulti' {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [LinearOrder ι] (b : Module.Basis ι K M) (S : Finset ι) :
    b.ExteriorAlgebra S = ExteriorAlgebra.ιMulti K S.card
      (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl) : Fin S.card → ι)) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl]

omit [CharZero F] in
theorem s22b_neg_one_pow_choose (n : ℕ) :
    ((-1 : F) ^ ((2 * n).choose 2)) = (-1) ^ n := by
  have h1 : (2 * n).choose 2 = n * (2 * n - 1) := by
    rw [Nat.choose_two_right]
    rw [show 2 * n * (2 * n - 1) = 2 * (n * (2 * n - 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have h2 : n * (2 * n - 1) + n = 2 * (n * n) := by
    rcases n with _ | n
    · simp
    · rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]; ring
  have h3 : ((-1 : F) ^ (n * (2 * n - 1))) * (-1) ^ n = 1 := by
    rw [← pow_add, h2, pow_mul, neg_one_sq, one_pow]
  have h4 : ((-1 : F) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow]
  rw [h1]
  calc ((-1 : F) ^ (n * (2 * n - 1))) = ((-1 : F) ^ (n * (2 * n - 1))) * ((-1) ^ n * (-1) ^ n) :=
        by rw [h4, mul_one]
    _ = (-1) ^ n := by rw [← mul_assoc, h3, one_mul]

/-- `[pt_X̂]` acts on `S` by `y ↦ (-1)^n ∫_X y` (the footnote in the proof of Lemma 2.2.6). -/
theorem s22b_m_ptHatC (y : S F n) :
    m F n (ptHatC F n) y = ((-1 : F) ^ n * integral F n y) • 1 := by
  classical
  set b := Pi.basisFun F (Fin (2 * n))
  set bd := b.dualBasis
  set t : Fin (Finset.univ : Finset (Fin (2 * n))).card → Fin (2 * n) :=
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl) : _ → Fin (2 * n))
  have ht : Function.Injective t :=
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl)).injective
  have hptHat : ptHat F n = ExteriorAlgebra.ιMulti F _ (bd ∘ t) := s22b_basis_eq_ιMulti' bd _
  have hpt : pt F n = ExteriorAlgebra.ιMulti F _ (b ∘ t) := s22b_basis_eq_ιMulti' b _
  set l : List (V F n) := List.ofFn fun i => ((bd (t i), (0 : H1 F n)) : V F n)
  have hC : ptHatC F n = (l.map (ι (Q F n))).prod := by
    rw [ptHatC, hptHat, s22b_iotaXHat_ιMulti]; rfl
  have hl : l.Pairwise (Q F n).IsOrtho := by
    refine List.pairwise_ofFn.mpr fun i j _ => ?_
    show Q F n _ = Q F n _ + Q F n _
    simp [QuadraticForm.dualProd_apply]
  have hrev := reverse_prod_map_ι_of_pairwise_isOrtho hl
  rw [List.length_ofFn, Finset.card_univ, Fintype.card_fin, s22b_neg_one_pow_choose,
    reverse_prod_map_ι] at hrev
  have hC' : ptHatC F n = (-1 : F) ^ n • ((l.map (ι (Q F n))).reverse.prod) := by
    rw [hrev, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, hC]
  -- value on `[pt]`
  have hval : m F n (ptHatC F n) (pt F n) = (-1 : F) ^ n • 1 := by
    rw [hC', map_smul, LinearMap.smul_apply, hpt, s22b_contract_front]
    intro i j
    simp only [Function.comp_apply, bd, Module.Basis.dualBasis_apply_self, ht.eq_iff]
    rcases eq_or_ne i j with rfl | h
    · simp
    · rw [ite_eq_right h.symm, ite_eq_right h]
  -- vanishing on the other monomials
  have hcoord : ∀ i, b.coord i = bd i := fun i => by
    ext x; simp [bd]
  have hrange : ∀ i : Fin (2 * n), ∃ j, t j = i := by
    intro i
    have : i ∈ Set.range t := by
      rw [Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
      exact Finset.mem_univ i
    exact this
  have hkill : ∀ i, ptHatC F n * ι (Q F n) (b.coord i, (0 : H1 F n)) = 0 := by
    intro i
    obtain ⟨j, rfl⟩ := hrange i
    rw [ptHatC, ← s22b_iotaXHat_ι, ← map_mul, hptHat, hcoord]
    have h1 := s22b_ι_mul_ιMulti_comm (F := F) (bd (t j)) _ (bd ∘ t)
    have h2 : ExteriorAlgebra.ι F (bd (t j)) * ExteriorAlgebra.ιMulti F _ (bd ∘ t) = 0 := by
      have e := ExteriorAlgebra.ιMulti_succ_apply (R := F)
        (Fin.cons (bd (t j)) (bd ∘ t) : Fin (_ + 1) → Module.Dual F (H1 F n))
      rw [Fin.cons_zero, show Matrix.vecTail (Fin.cons (bd (t j)) (bd ∘ t) :
        Fin (_ + 1) → Module.Dual F (H1 F n)) = bd ∘ t from funext fun i => by
          simp [Matrix.vecTail]] at e
      rw [← e]
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro hinj
      have := @hinj 0 j.succ (by rw [Fin.cons_zero, Fin.cons_succ]; rfl)
      exact Fin.succ_ne_zero j this.symm
    have h3 : ExteriorAlgebra.ιMulti F _ (bd ∘ t) * ExteriorAlgebra.ι F (bd (t j)) = 0 := by
      have h4 := congrArg (fun z => ((-1 : F) ^ (Finset.univ : Finset (Fin (2 * n))).card) • z) h1
      simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
        h2, smul_zero] at h4
      exact h4.symm
    rw [h3, map_zero]
  have hvan : ∀ S : Finset (Fin (2 * n)), S ≠ Finset.univ →
      m F n (ptHatC F n) (b.ExteriorAlgebra S) = 0 := by
    intro S hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra h
      push Not at h
      exact hS (Finset.eq_univ_of_forall h)
    have hD := TauCeti.ExteriorAlgebra.contractLeft_coord_basis b i (insert i S)
    rw [ite_eq_left (Finset.mem_insert_self i S), Finset.erase_insert hi] at hD
    set u := TauCeti.ExteriorAlgebra.basisEraseSign i (insert i S)
    have h0 : m F n (ptHatC F n) (u • b.ExteriorAlgebra S) = 0 := by
      rw [← hD, show contractLeft (Q := (0 : QuadraticForm F (H1 F n))) (b.coord i) =
        m F n (ι (Q F n) (b.coord i, (0 : H1 F n))) from LinearMap.ext fun z => by
          rw [s22b_m_ι_dual]; rfl, ← Module.End.mul_apply, ← map_mul, hkill, map_zero,
        LinearMap.zero_apply]
    have : b.ExteriorAlgebra S = u • u • b.ExteriorAlgebra S := by
      rw [smul_smul, Int.units_mul_self, one_smul]
    rw [this, map_zsmul_unit, h0, smul_zero]
  conv_lhs => rw [← (basisS F n).sum_repr y]
  rw [map_sum, Finset.sum_eq_single Finset.univ]
  · rw [map_smul, show basisS F n Finset.univ = pt F n from rfl, hval, smul_smul, integral,
      Module.Basis.coord_apply, mul_comm ((basisS F n).repr y Finset.univ)]
  · intro S _ hS
    rw [map_smul, show basisS F n S = b.ExteriorAlgebra S from rfl, hvan S hS, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [CharZero F] in
theorem s22b_iotaX_ιMulti {k : ℕ} (w : Fin k → H1 F n) :
    iotaX F n (ExteriorAlgebra.ιMulti F k w) =
      (List.ofFn fun i => ι (Q F n) ((0 : Module.Dual F (H1 F n)), w i)).prod := by
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact ExteriorAlgebra.lift_ι_apply F _ _ (w i)

omit [CharZero F] in
theorem s22b_iotaX_tau (s : S F n) : iotaX F n (tau F n s) = reverse (iotaX F n s) := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [show tau F n (algebraMap F (S F n) r) = algebraMap F (S F n) r from reverse.commutes r,
      AlgHom.commutes, reverse.commutes]
  | ι w =>
    rw [show tau F n (ι (0 : QuadraticForm F (H1 F n)) w) = ι (0 : QuadraticForm F (H1 F n)) w
      from reverse_ι w, show iotaX F n (ι (0 : QuadraticForm F (H1 F n)) w) =
        ι (Q F n) ((0 : Module.Dual F (H1 F n)), w) from ExteriorAlgebra.lift_ι_apply F _ _ w,
      reverse_ι]
  | mul x y hx hy =>
    rw [show tau F n (x * y) = tau F n y * tau F n x from reverse.map_mul x y, map_mul, hx, hy,
      map_mul, reverse.map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [CharZero F] in
theorem s22b_integral_basisS (S : Finset (Fin (2 * n))) :
    integral F n (basisS F n S) = if S = Finset.univ then 1 else 0 := by
  rw [integral, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

omit [CharZero F] in
theorem s22b_basisS_mul (M L : Finset (Fin (2 * n))) :
    (¬ Disjoint M L → basisS F n M * basisS F n L = 0) ∧
      (Disjoint M L → ∃ u : ℤˣ, basisS F n M * basisS F n L = u • basisS F n (M ∪ L)) := by
  constructor
  · intro h
    have hKL := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun F (Fin (2 * n)))
      (Set.powersetCard.ofCard (rfl : M.card = M.card))
      (Set.powersetCard.ofCard (rfl : L.card = L.card)) h
    simp only [Set.powersetCard.val_ofCard] at hKL
    exact hKL
  · intro h
    have hKL := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun F (Fin (2 * n)))
      (Set.powersetCard.ofCard (rfl : M.card = M.card))
      (Set.powersetCard.ofCard (rfl : L.card = L.card)) h
    refine ⟨Equiv.Perm.sign (Set.powersetCard.permOfDisjoint
      (s := Set.powersetCard.ofCard (rfl : M.card = M.card))
      (t := Set.powersetCard.ofCard (rfl : L.card = L.card)) h), hKL.trans ?_⟩
    congr 1
    show (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra _ =
      (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra (M ∪ L)
    congr 1
    exact Finset.disjUnion_eq_union _ _ h

omit [CharZero F] in
theorem s22b_tau_basisS (M : Finset (Fin (2 * n))) :
    tau F n (basisS F n M) = (-1 : F) ^ (M.card.choose 2) • basisS F n M := by
  rw [show basisS F n M = (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra M from rfl,
    s22b_basis_eq_ιMulti', ExteriorAlgebra.ιMulti_apply]
  set v := (Pi.basisFun F (Fin (2 * n))) ∘
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard rfl) : Fin M.card → Fin (2 * n))
  have hl : (List.ofFn v).Pairwise (0 : QuadraticForm F (H1 F n)).IsOrtho :=
    List.pairwise_ofFn.mpr fun _ _ _ => by simp [QuadraticMap.IsOrtho]
  have h := reverse_prod_map_ι_of_pairwise_isOrtho hl
  rw [List.length_ofFn, List.map_ofFn] at h
  exact h

end S22bVarphi

section S22bIntegral

variable {n : ℕ}

theorem s22b_basisS_mem_SZ (L : Finset (Fin (2 * n))) : basisS ℚ n L ∈ SZ n := by
  intro K
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s22b_ι_mem_CZ {v : V ℚ n} (hv : v ∈ VZ n) : ι (Q ℚ n) v ∈ CZ n :=
  Subring.subset_closure ⟨v, hv, rfl⟩

theorem s22b_reverse_mem_CZ {x : C ℚ n} (hx : x ∈ CZ n) : reverse x ∈ CZ n := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [reverse_ι]
    exact s22b_ι_mem_CZ hv
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | one => rw [reverse.map_one]; exact Subring.one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact Subring.neg_mem _ hx
  | mul x y _ _ hx hy => rw [reverse.map_mul]; exact Subring.mul_mem _ hy hx

theorem s22b_iotaX_basisS_mem (K : Finset (Fin (2 * n))) : iotaX ℚ n (basisS ℚ n K) ∈ CZ n := by
  rw [show basisS ℚ n K = (Pi.basisFun ℚ (Fin (2 * n))).ExteriorAlgebra K from rfl,
    s22b_basis_eq_ιMulti', s22b_iotaX_ιMulti]
  refine Subring.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  apply s22b_ι_mem_CZ
  refine ⟨fun j => ⟨0, by simp⟩, fun j => ?_⟩
  simp only [Function.comp_apply, Pi.basisFun_apply]
  by_cases h : j = (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard
    (rfl : K.card = K.card)) : Fin K.card → Fin (2 * n)) i
  · exact ⟨1, by rw [h]; simp⟩
  · exact ⟨0, by simp [h]⟩

theorem s22b_iotaX_mem_CZ {s : S ℚ n} (hs : s ∈ SZ n) : iotaX ℚ n s ∈ CZ n := by
  rw [← (basisS ℚ n).sum_repr s, map_sum]
  refine Subring.sum_mem _ fun K _ => ?_
  obtain ⟨z, hz⟩ := hs K
  rw [map_smul, hz, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (s22b_iotaX_basisS_mem K) z

theorem s22b_ptHatC_mem_CZ : ptHatC ℚ n ∈ CZ n := by
  rw [ptHatC, ptHat, basisSHat, s22b_basis_eq_ιMulti', s22b_iotaXHat_ιMulti]
  refine Subring.list_prod_mem _ fun x hx => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  apply s22b_ι_mem_CZ
  refine ⟨fun j => ?_, fun j => ⟨0, by simp⟩⟩
  simp only [Function.comp_apply]
  rw [show e ℚ n j = Pi.basisFun ℚ (Fin (2 * n)) j from (Pi.basisFun_apply ℚ _ j).symm,
    Module.Basis.dualBasis_apply_self]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-- **The Mukai pairing is unimodular**: for every `L` there is `t ∈ S = H*(X, ℤ)` with
`(t, y)_S = y_L` (the `e_L`-coordinate) for all `y`. -/
theorem s22b_mukai_dual (L : Finset (Fin (2 * n))) :
    ∃ t ∈ SZ n, ∀ y : S ℚ n, mukai ℚ n t y = (basisS ℚ n).repr y L := by
  classical
  have hm : ∀ M L' : Finset (Fin (2 * n)), mukai ℚ n (basisS ℚ n M) (basisS ℚ n L') =
      (-1 : ℚ) ^ (M.card.choose 2) * integral ℚ n (basisS ℚ n M * basisS ℚ n L') := by
    intro M L'
    show integral ℚ n (tau ℚ n (basisS ℚ n M) * basisS ℚ n L') = _
    rw [s22b_tau_basisS, smul_mul_assoc, map_smul, smul_eq_mul]
  have h0 : ∀ L', L' ≠ L → mukai ℚ n (basisS ℚ n Lᶜ) (basisS ℚ n L') = 0 := by
    intro L' hL'
    rw [hm]
    by_cases hd : Disjoint Lᶜ L'
    · obtain ⟨u, hu⟩ := (s22b_basisS_mul (F := ℚ) Lᶜ L').2 hd
      rw [hu, Units.smul_def, map_zsmul, s22b_integral_basisS, ite_eq_right, smul_zero, mul_zero]
      intro hU
      apply hL'
      ext x
      constructor
      · intro hx
        by_contra hxL
        exact Finset.disjoint_left.mp hd (Finset.mem_compl.mpr hxL) hx
      · intro hx
        have : x ∈ Lᶜ ∪ L' := hU ▸ Finset.mem_univ x
        rcases Finset.mem_union.mp this with h | h
        · exact absurd hx (Finset.mem_compl.mp h)
        · exact h
    · rw [(s22b_basisS_mul (F := ℚ) Lᶜ L').1 hd, map_zero, mul_zero]
  have h1 : mukai ℚ n (basisS ℚ n Lᶜ) (basisS ℚ n L) = 1 ∨
      mukai ℚ n (basisS ℚ n Lᶜ) (basisS ℚ n L) = -1 := by
    rw [hm]
    have hdisj : Disjoint Lᶜ L := Finset.disjoint_left.mpr fun x hx hx' =>
      (Finset.mem_compl.mp hx) hx'
    have hU : Lᶜ ∪ L = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_univ, iff_true]
      exact (em (x ∈ L)).symm
    obtain ⟨u, hu⟩ := (s22b_basisS_mul (F := ℚ) Lᶜ L).2 hdisj
    rw [hu, hU, Units.smul_def, map_zsmul, s22b_integral_basisS, ite_eq_left rfl]
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases neg_one_pow_eq_or ℚ (Lᶜ.card.choose 2) with h | h <;> simp [h]
  set c := mukai ℚ n (basisS ℚ n Lᶜ) (basisS ℚ n L)
  have hc2 : c * c = 1 := by rcases h1 with h | h <;> rw [h] <;> norm_num
  refine ⟨c • basisS ℚ n Lᶜ, ?_, fun y => ?_⟩
  · intro K
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    rcases h1 with h | h
    · split_ifs
      · exact ⟨1, by rw [h]; simp⟩
      · exact ⟨0, by simp⟩
    · split_ifs
      · exact ⟨-1, by rw [h]; simp⟩
      · exact ⟨0, by simp⟩
  · conv_lhs => rw [← (basisS ℚ n).sum_repr y]
    rw [map_smul, LinearMap.smul_apply, map_sum, Finset.sum_eq_single L]
    · rw [map_smul, smul_eq_mul, smul_eq_mul]
      show c * ((basisS ℚ n).repr y L * c) = _
      rw [mul_comm ((basisS ℚ n).repr y L), ← mul_assoc, hc2, one_mul]
    · intro L' _ hL'
      rw [map_smul, h0 L' hL', smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end S22bIntegral

section S22bDeg

variable {F : Type*} [Field F] {n : ℕ}

/-- The degree-`k` component of a class in `S = ⋀• H¹(X)`. -/
noncomputable def s22b_deg (k : ℕ) : S F n →ₗ[F] S F n :=
  ∑ K ∈ Finset.univ.filter (fun K : Finset (Fin (2 * n)) => K.card = k),
    ((basisS F n).coord K).smulRight (basisS F n K)

theorem s22b_deg_apply (k : ℕ) (x : S F n) :
    s22b_deg k x = ∑ K ∈ Finset.univ.filter (fun K : Finset (Fin (2 * n)) => K.card = k),
      (basisS F n).repr x K • basisS F n K := by
  simp [s22b_deg, LinearMap.sum_apply, Module.Basis.coord_apply]

theorem s22b_sum_deg (x : S F n) : ∑ k ∈ Finset.range (2 * n + 1), s22b_deg k x = x := by
  simp only [s22b_deg_apply]
  rw [Finset.sum_fiberwise_of_maps_to (g := Finset.card) (fun K _ => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (by simpa using K.card_le_univ)))]
  exact (basisS F n).sum_repr x

theorem s22b_deg_mem (k : ℕ) (x : S F n) : s22b_deg k x ∈ ⋀[F]^k (H1 F n) := by
  rw [s22b_deg_apply]
  refine Submodule.sum_mem _ fun K hK => Submodule.smul_mem _ _ ?_
  have h := s22b_basis_mem_exteriorPower (Pi.basisFun F (Fin (2 * n))) K
  rw [(Finset.mem_filter.mp hK).2] at h
  exact h

variable [CharZero F]

theorem s22b_deg_of_mem (k j : ℕ) {x : S F n} (hx : x ∈ ⋀[F]^j (H1 F n)) :
    s22b_deg k x = if j = k then x else 0 := by
  rw [s22b_deg_apply]
  have hsupp : ∀ K, (basisS F n).repr x K ≠ 0 → K.card = j := fun K hK =>
    s22b_card_of_repr_ne (Pi.basisFun F (Fin (2 * n))) hx K hK
  split_ifs with hjk
  · subst hjk
    conv_rhs => rw [← (basisS F n).sum_repr x]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun K _ => ?_
    split_ifs with hK
    · rfl
    · by_cases h0 : (basisS F n).repr x K = 0
      · rw [h0, zero_smul]
      · exact absurd (hsupp K h0) hK
  · refine Finset.sum_eq_zero fun K hK => ?_
    by_cases h0 : (basisS F n).repr x K = 0
    · rw [h0, zero_smul]
    · exact absurd ((hsupp K h0).symm.trans (Finset.mem_filter.mp hK).2) hjk

theorem s22b_deg_pp_even {A B : Submodule F (H1 F n)} {y : S F n}
    (hy : y ∈ ⨆ r : ℕ, pqPiece A B r r) (p : ℕ) : s22b_deg (2 * p) y ∈ pqPiece A B p p := by
  induction hy using Submodule.iSup_induction' with
  | mem r z hz =>
    have hz' : z ∈ ⋀[F]^(2 * r) (H1 F n) := by
      have := s22b_pqPiece_le A B r r hz; rwa [← two_mul] at this
    rw [s22b_deg_of_mem (2 * p) (2 * r) hz']
    split_ifs with h
    · have : r = p := by omega
      subst this; exact hz
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem s22b_deg_pp_odd {A B : Submodule F (H1 F n)} {y : S F n}
    (hy : y ∈ ⨆ r : ℕ, pqPiece A B r r) (k : ℕ) (hk : ¬ Even k) : s22b_deg k y = 0 := by
  induction hy using Submodule.iSup_induction' with
  | mem r z hz =>
    have hz' : z ∈ ⋀[F]^(2 * r) (H1 F n) := by
      have := s22b_pqPiece_le A B r r hz; rwa [← two_mul] at this
    rw [s22b_deg_of_mem k (2 * r) hz', ite_eq_right]
    rintro rfl
    exact hk (even_two_mul r)
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]

omit [CharZero F] in
theorem s22b_S_le_iSup {A B : Submodule F (H1 F n)} (hAB : A ⊔ B = ⊤) (y : S F n) :
    y ∈ ⨆ kr : Fin (2 * n + 1) × Fin (2 * n + 1), pqPiece A B kr.2 (kr.1 - kr.2) := by
  rw [← s22b_sum_deg y]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk' : k < 2 * n + 1 := Finset.mem_range.mp hk
  have h := s22b_wedge_le_iSup hAB k (s22b_deg_mem k y)
  have hle : (⨆ a : Fin (k + 1), pqPiece A B a (k - a)) ≤
      ⨆ kr : Fin (2 * n + 1) × Fin (2 * n + 1), pqPiece A B kr.2 (kr.1 - kr.2) :=
    iSup_le fun a => le_iSup_of_le
      ((⟨k, hk'⟩, ⟨a, by omega⟩) : Fin (2 * n + 1) × Fin (2 * n + 1)) le_rfl
  exact hle h

end S22bDeg

section S22bDegBC

variable {n : ℕ} {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']

omit [CharZero F] [CharZero F'] in
theorem s22b_bcS_eq_sum (x : S F n) :
    bcS F F' n x = ∑ K, algebraMap F F' ((basisS F n).repr x K) • basisS F' n K := by
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s22b_bcS_basisS, algebraMap_smul]

omit [CharZero F] [CharZero F'] in
theorem s22b_repr_bcS (x : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n x) K = algebraMap F F' ((basisS F n).repr x K) := by
  rw [s22b_bcS_eq_sum, Module.Basis.repr_sum_self]

omit [CharZero F] [CharZero F'] in
theorem s22b_deg_bcS (k : ℕ) (x : S F n) :
    s22b_deg k (bcS F F' n x) = bcS F F' n (s22b_deg k x) := by
  rw [s22b_deg_apply, s22b_deg_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s22b_repr_bcS, map_smul, s22b_bcS_basisS, algebraMap_smul]

end S22bDegBC

section S22bRemarkHelpers

variable {n : ℕ}

theorem s22b_bcS_trans_ℝ (x : S ℚ n) : bcS ℝ ℂ n (bcS ℚ ℝ n x) = bcS ℚ ℂ n x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ ℝ (S ℝ n),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι w =>
    show bcS ℝ ℂ n (bcS ℚ ℝ n (ExteriorAlgebra.ι ℚ w)) = bcS ℚ ℂ n (ExteriorAlgebra.ι ℚ w)
    rw [s22b_bcS_ι, s22b_bcS_ι, s22b_bcS_ι]
    congr 1
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem s22b_bcS_map (A : Module.End ℝ (H1 ℝ n)) (x : S ℝ n) :
    bcS ℝ ℂ n (ExteriorAlgebra.map A x) =
      ExteriorAlgebra.map (complexifyH1 n A) (bcS ℝ ℂ n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (((ExteriorAlgebra.map (complexifyH1 n A)).restrictScalars ℝ).commutes r).symm
  | ι w =>
    show bcS ℝ ℂ n (ExteriorAlgebra.map A (ExteriorAlgebra.ι ℝ w)) =
      ExteriorAlgebra.map (complexifyH1 n A) (bcS ℝ ℂ n (ExteriorAlgebra.ι ℝ w))
    rw [ExteriorAlgebra.map_apply_ι, s22b_bcS_ι, s22b_bcS_ι, ExteriorAlgebra.map_apply_ι,
      s22b_complexifyH1_bcH1]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem s22b_complexifyH1_combo (J : Module.End ℝ (H1 ℝ n)) (a b : ℝ) :
    complexifyH1 n (a • (1 : Module.End ℝ (H1 ℝ n)) + b • J) =
      (a : ℂ) • (1 : Module.End ℂ (H1 ℂ n)) + (b : ℂ) • complexifyH1 n J := by
  apply s22b_linearMap_ext_bcH1 (F := ℝ)
  intro w
  rw [s22b_complexifyH1_bcH1, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.smul_apply, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.smul_apply, s22b_complexifyH1_bcH1, ← algebraMap_smul ℂ a,
    ← algebraMap_smul ℂ b]
  rfl

/-- An endomorphism of `S` commuting with all `m_v` is a scalar (`m` is onto `End(S)`). -/
theorem s22b_scalar_of_commute {F : Type*} [Field F] [CharZero F] (Z : Module.End F (S F n))
    (hZ : ∀ v : V F n, Z * m F n (ι (Q F n) v) = m F n (ι (Q F n) v) * Z) :
    ∃ c : F, Z = c • 1 := by
  have hall : ∀ x : C F n, Z * m F n x = m F n x * Z := by
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes]; exact (Algebra.commutes r Z).symm
    | ι v => exact hZ v
    | mul x y hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
  have hcen : Z ∈ Subalgebra.center F (Module.End F (S F n)) := by
    rw [Subalgebra.mem_center_iff]
    intro A
    obtain ⟨x, rfl⟩ := (glo_prop3_2_1_e_field F n).2 A
    exact (hall x).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff F).mp hcen
  exact ⟨c, by rw [hc, Algebra.algebraMap_eq_smul_one]⟩

/-- The characters `μ^r μ̄^s` (`μ = e^{-iθ}`, `θ = π/(4n)`, `r + s ≤ 2n`) are real only for `r = s`. -/
theorem s22b_char_real (hn : 0 < n) (r s : ℕ) (hrs : r + s ≤ 2 * n) (c : ℝ)
    (h : Complex.exp (((-(Real.pi / (4 * n)) : ℝ) : ℂ) * Complex.I) ^ r *
      Complex.exp (((Real.pi / (4 * n) : ℝ) : ℂ) * Complex.I) ^ s = (c : ℂ)) : r = s := by
  set θ := Real.pi / (4 * n)
  have hprod : Complex.exp ((-θ : ℝ) * Complex.I) ^ r * Complex.exp ((θ : ℝ) * Complex.I) ^ s =
      Complex.exp ((((s : ℝ) - r) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hprod] at h
  have him := congrArg Complex.im h
  rw [Complex.exp_ofReal_mul_I_im, Complex.ofReal_im] at him
  have hθ : 0 < θ := by positivity
  have hbound : |((s : ℝ) - r) * θ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hθ]
    have h1 : |(s : ℝ) - r| ≤ 2 * n := by
      have hr : (r : ℝ) + s ≤ 2 * n := by exact_mod_cast hrs
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc |(s : ℝ) - r| * θ ≤ 2 * n * θ := by gcongr
      _ = Real.pi / 2 := by
        simp only [θ]
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp
        ring
  have h0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [abs_le.mp hbound, Real.pi_pos])
    (by linarith [abs_le.mp hbound, Real.pi_pos])).mp him
  have : ((s : ℝ) - r) = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact h'
    · exact absurd h' hθ.ne'
  have : (s : ℝ) = r := by linarith
  exact_mod_cast this.symm

end S22bRemarkHelpers

/-! ## Chevalley's isomorphism `φ` (2.2.5) -/

section Varphi

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The top exterior power `⋀^{2n} W` of a subspace `W ⊆ V_F`, "considered as a one-dimensional
subspace of `C(V)`" (proof of Lemma 2.2.6): the span of the products `w₁ ⋯ w_{2n}` in `C(V_F)` of
`2n` vectors of `W`. For `W` isotropic of dimension `2n` it is a line. -/
noncomputable def cliffordTopPiece (W : Submodule F (V F n)) : Submodule F (C F n) :=
  Submodule.span F
    {x | ∃ w : Fin (2 * n) → V F n, (∀ i, w i ∈ W) ∧ x = (List.ofFn fun i => ι (Q F n) (w i)).prod}

omit [CharZero F] in
theorem varphi_tmul (u v : S F n) :
    varphi F n (u ⊗ₜ v) = iotaX F n u * ptHatC F n * iotaX F n (tau F n v) := by
  simp [varphi]

/-- The footnote in the proof of Lemma 2.2.6: `m ∘ φ : S ⊗ S → End(S)` is `(-1)^n` times the map
`s ⊗ t ↦ s ⊗ (t, ·)_S`, i.e. `m_{φ(s ⊗ t)}(x) = (-1)^n (t, x)_S s`. -/
theorem m_varphi_tmul (s t x : S F n) :
    m F n (varphi F n (s ⊗ₜ t)) x = ((-1) ^ n * mukai F n t x) • s := by
  rw [varphi_tmul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, s22b_m_iotaX,
    s22b_m_ptHatC, s22b_m_iotaX, mul_smul_comm, mul_one]
  rfl

/-- "**`φ` is an isomorphism over `ℤ`**" (proof of Lemma 2.2.6, with its footnote and
[GLO, Prop. 3.2.1(e)]): `φ` maps `S ⊗_ℤ S` onto the integral Clifford algebra `C(V)`, i.e. the
additive group generated by the `φ(s ⊗ t)`, `s, t ∈ S = H*(X, ℤ)`, is `CZ n`. (Injectivity holds
over `ℚ`, [Chevalley, III.3.1].) -/
theorem closure_varphi_SZ (n : ℕ) :
    AddSubgroup.closure
        {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = varphi ℚ n (s ⊗ₜ t)} =
      (CZ n).toAddSubgroup := by
  classical
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [varphi_tmul, s22b_iotaX_tau]
    exact Subring.mul_mem _ (Subring.mul_mem _ (s22b_iotaX_mem_CZ hs) s22b_ptHatC_mem_CZ)
      (s22b_reverse_mem_CZ (s22b_iotaX_mem_CZ ht))
  · intro x hx
    have hA := (glo_prop3_2_1_e_integral n).mapsTo hx
    have hcoef : ∀ K L, ∃ z : ℤ,
        (basisS ℚ n).repr (m ℚ n x (basisS ℚ n L)) K = z := fun K L =>
      hA (basisS ℚ n L) (s22b_basisS_mem_SZ L) K
    choose z hz using hcoef
    choose tL htL hmuk using fun L : Finset (Fin (2 * n)) => s22b_mukai_dual (n := n) L
    set x' := ∑ K, ∑ L, z K L • varphi ℚ n (basisS ℚ n K ⊗ₜ ((-1 : ℚ) ^ n • tL L))
    have hsgn : ∀ L, ((-1 : ℚ) ^ n • tL L) ∈ SZ n := fun L => by
      rcases neg_one_pow_eq_or ℚ n with h | h
      · rw [h, one_smul]; exact htL L
      · rw [h, neg_one_smul]; exact neg_mem (htL L)
    have hx'mem : x' ∈ AddSubgroup.closure
        {x | ∃ s ∈ SZ n, ∃ t ∈ SZ n, x = varphi ℚ n (s ⊗ₜ t)} := by
      refine AddSubgroup.sum_mem _ fun K _ => AddSubgroup.sum_mem _ fun L _ => ?_
      apply zsmul_mem
      apply AddSubgroup.subset_closure
      exact ⟨_, s22b_basisS_mem_SZ K, _, hsgn L, rfl⟩
    have hmx : m ℚ n x' = m ℚ n x := by
      apply (basisS ℚ n).ext
      intro M
      have key : ∀ K L, m ℚ n (varphi ℚ n (basisS ℚ n K ⊗ₜ ((-1 : ℚ) ^ n • tL L)))
          (basisS ℚ n M) = (if L = M then (1 : ℚ) else 0) • basisS ℚ n K := by
        intro K L
        rw [m_varphi_tmul ℚ n, map_smul, LinearMap.smul_apply, hmuk,
          Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, ← mul_assoc, ← pow_add,
          ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · rfl
      calc m ℚ n x' (basisS ℚ n M)
          = ∑ K, ∑ L, z K L • m ℚ n (varphi ℚ n (basisS ℚ n K ⊗ₜ ((-1 : ℚ) ^ n • tL L)))
              (basisS ℚ n M) := by
            simp only [x', map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
        _ = ∑ K, ∑ L, z K L • ((if L = M then (1 : ℚ) else 0) • basisS ℚ n K) := by
            simp only [key]
        _ = ∑ K, z K M • basisS ℚ n K := by
            refine Finset.sum_congr rfl fun K _ => ?_
            rw [Finset.sum_eq_single M (fun L _ hL => by rw [ite_eq_right hL, zero_smul, smul_zero])
              (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, one_smul]
        _ = ∑ K, (basisS ℚ n).repr (m ℚ n x (basisS ℚ n M)) K • basisS ℚ n K := by
            refine Finset.sum_congr rfl fun K _ => ?_
            rw [hz, Int.cast_smul_eq_zsmul]
        _ = m ℚ n x (basisS ℚ n M) := (basisS ℚ n).sum_repr _
    have := (glo_prop3_2_1_e_field ℚ n).1 hmx
    rw [← this]
    exact hx'mem

end Varphi

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-! ## Complexifications and real points -/

section S22bCore

variable (J : Module.End ℝ (H1 ℝ n))


/-- If `P` lies in the Hodge ring, the spinors of `P_K` are sums of classes of type `(p, p)`. -/
theorem s22b_bcS_PK_mem (hPJ : P.Pℚ ≤ hodgeRingX n J) {x : S (Kd d) n} (hx : x ∈ P.PK) :
    bcS (Kd d) ℂ n x ∈ ⨆ p, pqPiece (H10 n J) (H01 n J) p p := by
  rw [← P.span_bcS_Pℚ] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, rfl⟩ := hy
    rw [s22b_bcS_trans]
    have hα' : α ∈ ⨆ p, hodgeClassesX n J p := hPJ hα
    clear hα
    induction hα' using Submodule.iSup_induction' with
    | mem p β hβ => exact Submodule.mem_iSup_of_mem p ((mem_hodgeClassesX_iff n J p β).mp hβ).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, ← algebraMap_smul ℂ]; exact Submodule.smul_mem _ _ hx

theorem s22b_map_T_fix (hPJ : P.Pℚ ≤ hodgeRingX n J) {x : S (Kd d) n} (hx : x ∈ P.PK) :
    ExteriorAlgebra.map (s22b_T J (-(3 / 4 * Complex.I))) (bcS (Kd d) ℂ n x) =
      bcS (Kd d) ℂ n x := by
  have h := P.s22b_bcS_PK_mem J hPJ hx
  generalize bcS (Kd d) ℂ n x = y at h ⊢
  induction h using Submodule.iSup_induction' with
  | mem p y hy =>
    rw [s22b_map_pqPiece _ 2 (1 / 2) (fun w hw => by rw [s22b_T_H10 J _ hw, s22b_val_two])
      (fun w hw => by rw [s22b_T_H01 J _ hw, s22b_val_half]) hy, ← mul_pow]
    norm_num
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]

/-- **The core of Lemma 2.2.6**: for an even pure spinor `u ∈ P_K`, `W = ker m_u` satisfies
`W_ℂ = W_ℂ^{1,0} ⊕ W_ℂ^{0,1}` with both summands of dimension `n`. -/
theorem s22b_core (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J)
    (u : S (Kd d) n) (hu : IsEvenPureSpinor (Kd d) n u) (huP : u ∈ P.PK) :
    ann ℂ n (bcS (Kd d) ℂ n u) = ann ℂ n (bcS (Kd d) ℂ n u) ⊓ V10 n (productStructure n J) ⊔
        ann ℂ n (bcS (Kd d) ℂ n u) ⊓ V01 n (productStructure n J) ∧
      Module.finrank ℂ (ann ℂ n (bcS (Kd d) ℂ n u) ⊓ V10 n (productStructure n J) :
        Submodule ℂ (V ℂ n)) = n ∧
      Module.finrank ℂ (ann ℂ n (bcS (Kd d) ℂ n u) ⊓ V01 n (productStructure n J) :
        Submodule ℂ (V ℂ n)) = n := by
  have hn := P.s22b_n_pos
  obtain ⟨g, hmg, hg10, hg01⟩ := s22b_exists_torus J hn hJ
  set uC := bcS (Kd d) ℂ n u with huC_def
  set W := ann ℂ n uC with hW_def
  set A := V10 n (productStructure n J)
  set B := V01 n (productStructure n J)
  have huC : IsEvenPureSpinor ℂ n uC := s22b_isEvenPureSpinor_bcS hn hu
  have hfix : m ℂ n (g : C ℂ n) uC = uC := by
    rw [hmg, AlgHom.toLinearMap_apply]
    exact P.s22b_map_T_fix J hPJ huP
  have hstab : ∀ v ∈ W, rho ℂ n g v ∈ W := by
    intro v hv
    show m ℂ n (ι (Q ℂ n) (rho ℂ n g v)) uC = 0
    have h1 := m_ι_rho_m ℂ n g v uC
    rw [hfix] at h1
    rw [h1]
    have hv' : m ℂ n (ι (Q ℂ n) v) uC = 0 := hv
    rw [hv', map_zero]
  have hIC := s22b_isCompl_V10 J hJ
  have hdecomp : ∀ v ∈ W, ∃ a ∈ W ⊓ A, ∃ b ∈ W ⊓ B, v = a + b := by
    intro v hv
    have hv2 : v ∈ A ⊔ B := by rw [hIC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv2
    have hρ := hstab _ hv
    rw [map_add, hg10 a ha, hg01 b hb] at hρ
    have ha' : a = (2 / 3 : ℂ) • ((2 : ℂ) • (a + b) - ((1 / 2 : ℂ) • a + (2 : ℂ) • b)) := by
      module
    have haW : a ∈ W := by
      rw [ha']
      exact W.smul_mem _ (W.sub_mem (W.smul_mem _ hv) hρ)
    have hbW : b ∈ W := by
      have := W.sub_mem hv haW
      rwa [add_sub_cancel_left] at this
    exact ⟨a, ⟨haW, ha⟩, b, ⟨hbW, hb⟩, rfl⟩
  have hD : W = W ⊓ A ⊔ W ⊓ B := le_antisymm (fun v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp v hv
      exact Submodule.add_mem_sup ha hb) (sup_le inf_le_left inf_le_left)
  refine ⟨hD, ?_⟩
  -- Chevalley's `c² = det`
  obtain ⟨c, hc, hc2⟩ := chevalley_III_3_2_III_4_5 ℂ n uC huC g hstab
  have huC0 : uC ≠ 0 := huC.ne_zero hn
  have hc1 : c = 1 := by
    rw [hfix] at hc
    have : (1 - c) • uC = 0 := by rw [sub_smul, one_smul, ← hc, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right huC0)).symm
  set A' := A.comap W.subtype
  set B' := B.comap W.subtype
  have hAB' : IsCompl A' B' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx1 hx2
      exact Subtype.ext ((Submodule.disjoint_def.mp hIC.disjoint) _ hx1 hx2)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨a, ha, b, hb, hab⟩ := hdecomp x x.2
      exact Submodule.mem_sup.mpr ⟨⟨a, ha.1⟩, ha.2, ⟨b, hb.1⟩, hb.2, Subtype.ext hab.symm⟩
  have hdet := s22b_det_of_isCompl hAB'
    ((rho ℂ n g : V ℂ n →ₗ[ℂ] V ℂ n).restrict hstab) (1 / 2) 2
    (fun x hx => Subtype.ext (by
      rw [LinearMap.restrict_apply]
      exact hg10 _ hx))
    (fun x hx => Subtype.ext (by
      rw [LinearMap.restrict_apply]
      exact hg01 _ hx))
  rw [← hc2, hc1, one_pow] at hdet
  have hfinA : Module.finrank ℂ A' = Module.finrank ℂ (W ⊓ A : Submodule ℂ (V ℂ n)) := by
    have : A' = (W ⊓ A).comap W.subtype := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    rw [this]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  have hfinB : Module.finrank ℂ B' = Module.finrank ℂ (W ⊓ B : Submodule ℂ (V ℂ n)) := by
    have : B' = (W ⊓ B).comap W.subtype := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    rw [this]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  have hsum : Module.finrank ℂ A' + Module.finrank ℂ B' = 2 * n := by
    rw [Submodule.finrank_add_eq_of_isCompl hAB', huC.2.2]
  rw [hfinA, hfinB] at hdet hsum
  set a := Module.finrank ℂ (W ⊓ A : Submodule ℂ (V ℂ n))
  set b := Module.finrank ℂ (W ⊓ B : Submodule ℂ (V ℂ n))
  have hab : a = b := by
    have h2 : (2 : ℂ) ^ b = 2 ^ a := by
      have h' : ((1 / 2 : ℂ) ^ a * 2 ^ b) * 2 ^ a = 1 * 2 ^ a := by rw [← hdet]
      rw [one_mul, mul_comm ((1 / 2 : ℂ) ^ a), mul_assoc, ← mul_pow] at h'
      norm_num at h'
      exact h'
    have h3 : ((2 ^ b : ℕ) : ℂ) = ((2 ^ a : ℕ) : ℂ) := by push_cast; exact h2
    exact (Nat.pow_right_injective le_rfl (Nat.cast_injective h3)).symm
  exact ⟨by omega, by omega⟩

theorem s22b_W₁ℂ_eq (hn : 0 < n) : P.W₁ℂ = ann ℂ n (bcS (Kd d) ℂ n P.u₁) :=
  (s22b_ann_bcS hn P.isPure).symm

theorem s22b_W₂ℂ_eq (hn : 0 < n) : P.W₂ℂ = ann ℂ n (bcS (Kd d) ℂ n P.u₂) :=
  (s22b_ann_bcS hn P.isPure₂).symm

end S22bCore

/-! ## Remark 2.2.5 -/

/-- **Remark 2.2.5** (`remark-P-is-contained-in-the-Hodge-ring-if-I-is-in-image-of-Spin-V-P`): if the
whole circle group `{cos θ + sin θ · I}` generated by the complex structure `I` of `X × X̂` lies in
`ρ(Spin(V_ℝ)_P)`, then `P` is contained in the Hodge ring of `X`. Standing hypotheses at this point:
`P` non-isotropic, `K` imaginary quadratic.

Correction of the paper (agreed with the project owner; REPORT.md): the paper assumes only
`I ∈ ρ(Spin(V_ℝ)_P)`, and then the remark is false. Counterexample (`n = 2`, `d = 1`): `X = E × E`
with `E = ℂ/ℤ[i]`, `u₁ = dz₁ ∧ dz₂`, so that `P_ℂ = H^{2,0} ⊕ H^{0,2}`; the lift `g₀` of `I` acts on
`H^{p,q}` by `i^{p-q}`, so `-g₀ ∈ Spin(V_ℝ)_P` and `ρ(-g₀) = I`, but `P` meets the Hodge ring in `0`.
The whole circle is what the argument of the paper (proof of Lemma 4.0.3(2)) provides and uses. -/
theorem _root_.WeilClasses.remark2_2_5 (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J)
    (hI : ∀ θ : ℝ, ∃ g ∈ P.spinPR,
      (rho ℝ n g).toLinearMap = Real.cos θ • (1 : Module.End ℝ (V ℝ n)) +
        Real.sin θ • productStructure n J) :
    P.Pℚ ≤ hodgeRingX n J := by
  have _ := hd
  have _ := hP
  have hn := P.s22b_n_pos
  set θ₀ : ℝ := Real.pi / (4 * n) with hθ₀
  obtain ⟨g, hg, hρ⟩ := hI θ₀
  set c₀ := Real.cos θ₀ with hc₀
  set s₀ := Real.sin θ₀ with hs₀
  have hJ' : ∀ w, J (J w) = -w := fun w => by
    rw [← Module.End.mul_apply, show J * J = -1 from hJ]; simp
  have hcs : c₀ * c₀ + s₀ * s₀ = 1 := by
    have := Real.cos_sq_add_sin_sq θ₀
    rw [sq, sq] at this
    exact this
  set T : Module.End ℝ (H1 ℝ n) := c₀ • (1 : Module.End ℝ (H1 ℝ n)) + (-s₀) • J with hT
  set T' : Module.End ℝ (H1 ℝ n) := c₀ • (1 : Module.End ℝ (H1 ℝ n)) + s₀ • J with hT'
  have hTT' : T' ∘ₗ T = LinearMap.id := LinearMap.ext fun w => by
    simp only [T, T', LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, hJ', LinearMap.id_apply]
    linear_combination (norm := module) hcs • w
  have hρ' : ∀ v : V ℝ n, rho ℝ n g v = (v.1 ∘ₗ T', T v.2) := by
    intro v
    have h1 := congrArg (fun f => f v) hρ
    simp only [LinearEquiv.coe_coe] at h1
    rw [h1]
    obtain ⟨θ', w⟩ := v
    apply Prod.ext
    · refine LinearMap.ext fun x => ?_
      simp [T', productStructure, LinearMap.dualMap_apply']
    · simp [T, productStructure]
  set Λ : Module.End ℝ (S ℝ n) := (ExteriorAlgebra.map T).toLinearMap with hΛdef
  have hΛ : ∀ v, Λ * m ℝ n (ι (Q ℝ n) v) = m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) * Λ := by
    intro v
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hρ', hΛdef, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, s22b_map_m_ι T T' hTT']
  have hmg : ∀ v, m ℝ n (g : C ℝ n) * m ℝ n (ι (Q ℝ n) v) =
      m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) * m ℝ n (g : C ℝ n) := by
    intro v
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact (m_ι_rho_m ℝ n g v x).symm
  have hginv : m ℝ n ((g⁻¹ : Spin ℝ n) : C ℝ n) * m ℝ n (g : C ℝ n) = 1 := by
    rw [← map_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, map_one]
  have hginv' : m ℝ n (g : C ℝ n) * m ℝ n ((g⁻¹ : Spin ℝ n) : C ℝ n) = 1 := by
    rw [← map_mul, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one, map_one]
  set gi := m ℝ n ((g⁻¹ : Spin ℝ n) : C ℝ n)
  set gm := m ℝ n (g : C ℝ n)
  have hZ : ∀ v, (gi * Λ) * m ℝ n (ι (Q ℝ n) v) = m ℝ n (ι (Q ℝ n) v) * (gi * Λ) := by
    intro v
    have h1 : m ℝ n (ι (Q ℝ n) v) * gi = gi * m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) := by
      calc m ℝ n (ι (Q ℝ n) v) * gi = (gi * gm) * m ℝ n (ι (Q ℝ n) v) * gi := by
            rw [hginv, one_mul]
        _ = gi * (gm * m ℝ n (ι (Q ℝ n) v)) * gi := by simp only [mul_assoc]
        _ = gi * (m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) * gm) * gi := by rw [hmg]
        _ = gi * m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) * (gm * gi) := by simp only [mul_assoc]
        _ = gi * m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) := by rw [hginv', mul_one]
    calc gi * Λ * m ℝ n (ι (Q ℝ n) v) = gi * (Λ * m ℝ n (ι (Q ℝ n) v)) := by rw [mul_assoc]
      _ = gi * (m ℝ n (ι (Q ℝ n) (rho ℝ n g v)) * Λ) := by rw [hΛ]
      _ = (gi * m ℝ n (ι (Q ℝ n) (rho ℝ n g v))) * Λ := by rw [mul_assoc]
      _ = (m ℝ n (ι (Q ℝ n) v) * gi) * Λ := by rw [h1]
      _ = m ℝ n (ι (Q ℝ n) v) * (gi * Λ) := by rw [mul_assoc]
  obtain ⟨c, hc⟩ := s22b_scalar_of_commute (gi * Λ) hZ
  have hΛg : Λ = c • gm := by
    calc Λ = (gm * gi) * Λ := by rw [hginv', one_mul]
      _ = gm * (gi * Λ) := by rw [mul_assoc]
      _ = gm * (c • 1) := by rw [hc]
      _ = c • gm := by rw [mul_smul_comm, mul_one]
  intro α hα
  have hp : bcS ℚ ℝ n α ∈ P.PR := Submodule.subset_span ⟨α, hα, rfl⟩
  have hfixp : gm (bcS ℚ ℝ n α) = bcS ℚ ℝ n α := hg _ hp
  have hΛp : ExteriorAlgebra.map T (bcS ℚ ℝ n α) = c • bcS ℚ ℝ n α := by
    have h1 := congrArg (fun f => f (bcS ℚ ℝ n α)) hΛg
    simp only [hΛdef, AlgHom.toLinearMap_apply, LinearMap.smul_apply, hfixp] at h1
    exact h1
  set y := bcS ℚ ℂ n α with hy_def
  have hy : (ExteriorAlgebra.map (complexifyH1 n T)).toLinearMap y = (c : ℂ) • y := by
    rw [AlgHom.toLinearMap_apply, hy_def, ← s22b_bcS_trans_ℝ, ← s22b_bcS_map, hΛp, map_smul]
    rfl
  have hTC : complexifyH1 n T = (c₀ : ℂ) • (1 : Module.End ℂ (H1 ℂ n)) +
      ((-s₀ : ℝ) : ℂ) • complexifyH1 n J := s22b_complexifyH1_combo J c₀ (-s₀)
  have hval1 : (c₀ : ℂ) + ((-s₀ : ℝ) : ℂ) * Complex.I =
      Complex.exp (((-θ₀ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
  have hval2 : (c₀ : ℂ) + ((-s₀ : ℝ) : ℂ) * (-Complex.I) =
      Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← hc₀, ← hs₀,
      Complex.ofReal_neg]
    ring
  have hμ : ∀ w ∈ H10 n J, complexifyH1 n T w =
      Complex.exp (((-θ₀ : ℝ) : ℂ) * Complex.I) • w := by
    intro w hw
    rw [hTC, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.smul_apply, Module.End.mem_eigenspace_iff.mp hw, smul_smul, ← add_smul, hval1]
  have hμ' : ∀ w ∈ H01 n J, complexifyH1 n T w =
      Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) • w := by
    intro w hw
    rw [hTC, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.smul_apply, Module.End.mem_eigenspace_iff.mp hw, smul_smul, ← add_smul, hval2]
  have hymem := s22b_S_le_iSup (s22b_isCompl_H10 J hJ).sup_eq_top y
  have heig := s22b_mem_iSup_eigen
    (fun kr : Fin (2 * n + 1) × Fin (2 * n + 1) =>
      pqPiece (H10 n J) (H01 n J) kr.2 (kr.1 - kr.2))
    (ExteriorAlgebra.map (complexifyH1 n T)).toLinearMap
    (fun kr => Complex.exp (((-θ₀ : ℝ) : ℂ) * Complex.I) ^ (kr.2 : ℕ) *
      Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) ^ ((kr.1 : ℕ) - kr.2))
    (fun kr x hx => s22b_map_pqPiece _ _ _ hμ hμ' hx) (c : ℂ) hymem hy
  have hpp : y ∈ ⨆ r : ℕ, pqPiece (H10 n J) (H01 n J) r r := by
    refine (show (⨆ kr : Fin (2 * n + 1) × Fin (2 * n + 1),
        ⨆ (_ : Complex.exp (((-θ₀ : ℝ) : ℂ) * Complex.I) ^ (kr.2 : ℕ) *
          Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) ^ ((kr.1 : ℕ) - kr.2) = (c : ℂ)),
          pqPiece (H10 n J) (H01 n J) kr.2 (kr.1 - kr.2)) ≤
        ⨆ r : ℕ, pqPiece (H10 n J) (H01 n J) r r from
      iSup_le fun kr => iSup_le fun hkr => ?_) heig
    by_cases hle : (kr.2 : ℕ) ≤ kr.1
    · have hrs := s22b_char_real hn kr.2 (kr.1 - kr.2) (by omega) c hkr
      rw [← hrs]
      exact le_iSup_of_le (kr.2 : ℕ) le_rfl
    · exfalso
      have h0 : (kr.1 : ℕ) - kr.2 = 0 := by omega
      have hkr' : Complex.exp (((-θ₀ : ℝ) : ℂ) * Complex.I) ^ (kr.2 : ℕ) *
          Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) ^ 0 = (c : ℂ) := by
        rw [← h0]; exact hkr
      have hrs := s22b_char_real hn kr.2 0 (by omega) c hkr'
      omega
  show α ∈ ⨆ p, hodgeClassesX n J p
  rw [← s22b_sum_deg α]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : Even k
  · obtain ⟨p, rfl⟩ := hk
    rw [← two_mul]
    refine Submodule.mem_iSup_of_mem p ?_
    rw [mem_hodgeClassesX_iff]
    refine ⟨s22b_deg_mem _ _, ?_⟩
    rw [← s22b_deg_bcS]
    exact s22b_deg_pp_even hpp p
  · have h0 : bcS ℚ ℂ n (s22b_deg k α) = 0 := by
      rw [← s22b_deg_bcS]; exact s22b_deg_pp_odd hpp k hk
    have : s22b_deg k α = 0 := s22b_bcS_injective (F' := ℂ) (by rw [h0, map_zero])
    rw [this]
    exact Submodule.zero_mem _

/-! ## Lemma 2.2.6 -/

/-- **Lemma 2.2.6** (`lemma-decomposition-into-4-direct-summands`): if `P` is contained in the Hodge
ring of `X`, then `W₁^{1,0} := W_{1,ℂ} ∩ V^{1,0}` and `W₂^{1,0} := W_{2,ℂ} ∩ V^{1,0}` are both
`n`-dimensional. Here `V^{1,0}` is the `i`-eigenspace of the complex structure of `X × X̂`. Standing
hypotheses: `P` non-isotropic (not used by the proof), `K` imaginary quadratic.

Departure from the paper (in the proof only): the paper gets `dim W_i^{1,0} = dim W_i^{0,1}` from
Chevalley's `φ` being an isomorphism of Hodge structures with `φ(ℓ̃_i ⊗ ℓ̃_i) = ⋀^{2n} W_i`
([Chevalley, III.3.1, III.3.2]). Those statements (`WeilClasses.External.Chevalley.Sec2_2`) import
this file, so they cannot be cited here. We use the same fact in the form [Chevalley, III.3.2,
III.4.5] (`chevalley_III_3_2_III_4_5`: if `ρ(g)` preserves `W = ker m_u` then `g u = c u` with
`c² = det(ρ(g)|_W)`). It is applied to the spin lift `g` of `⋀T`, where `T` acts by `2` on `H^{1,0}`
and by `1/2` on `H^{0,1}`. This `g` is an element of the complexified circle of the Hodge structure
(`KSecant.s22b_core`). It fixes the classes of type `(p, p)`, so it fixes `u_i ∈ P_K`. Hence
`c = 1`, and `det(ρ(g)|_{W_i}) = 2^{dim W_i^{0,1} - dim W_i^{1,0}} = 1`. -/
theorem _root_.WeilClasses.lemma2_2_6 (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    Module.finrank ℂ (P.W₁ℂ ⊓ V10 n (productStructure n J) : Submodule ℂ (V ℂ n)) = n ∧
      Module.finrank ℂ (P.W₂ℂ ⊓ V10 n (productStructure n J) : Submodule ℂ (V ℂ n)) = n := by
  have _ := hd
  have _ := hP
  have hn := P.s22b_n_pos
  rw [KSecant.s22b_W₁ℂ_eq P hn, KSecant.s22b_W₂ℂ_eq P hn]
  exact ⟨(P.s22b_core J hJ hPJ P.u₁ P.isPure (Submodule.subset_span (by simp))).2.1,
    (P.s22b_core J hJ hPJ P.u₂ P.isPure₂ (Submodule.subset_span (by simp))).2.1⟩

/-- **Lemma 2.2.6** (`lemma-decomposition-into-4-direct-summands`), the equivalent form: if `P` is
contained in the Hodge ring, then `W₁^{0,1} := W_{1,ℂ} ∩ V^{0,1}` and
`W₂^{0,1} := W_{2,ℂ} ∩ V^{0,1}` are both `n`-dimensional. -/
theorem _root_.WeilClasses.lemma2_2_6_V01 (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    Module.finrank ℂ (P.W₁ℂ ⊓ V01 n (productStructure n J) : Submodule ℂ (V ℂ n)) = n ∧
      Module.finrank ℂ (P.W₂ℂ ⊓ V01 n (productStructure n J) : Submodule ℂ (V ℂ n)) = n := by
  have _ := hd
  have _ := hP
  have hn := P.s22b_n_pos
  rw [KSecant.s22b_W₁ℂ_eq P hn, KSecant.s22b_W₂ℂ_eq P hn]
  exact ⟨(P.s22b_core J hJ hPJ P.u₁ P.isPure (Submodule.subset_span (by simp))).2.2,
    (P.s22b_core J hJ hPJ P.u₂ P.isPure₂ (Submodule.subset_span (by simp))).2.2⟩

/-- The decomposition proved in Lemma 2.2.6 (`lemma-decomposition-into-4-direct-summands`): if `P`
is contained in the Hodge ring, then `W_{i,ℂ}` is invariant under the circle action of the Hodge
structure, so `W_{i,ℂ} = (W_{i,ℂ} ∩ V^{1,0}) ⊕ (W_{i,ℂ} ∩ V^{0,1})` for `i = 1, 2`. Used in §2.4
("`I` commutes with `f`, by Lemma 2.2.6") and in §§3–4.

Proof: the `U(1)`-equivariance of `m_{λ_i}` is used through the element `g` of the complexified
circle described at `lemma2_2_6`. `ρ(g)` acts by `1/2` on `V^{1,0}` and by `2` on `V^{0,1}`. It
fixes `u_i`, so it preserves `W_{i,ℂ} = ker m_{u_i}`, and `W_{i,ℂ}` splits into its eigenspaces. -/
theorem _root_.WeilClasses.lemma2_2_6_decomp (hd : 0 < d) (hP : ¬ P.IsIsotropic)
    (J : Module.End ℝ (H1 ℝ n)) (hJ : IsComplexStructure J) (hPJ : P.Pℚ ≤ hodgeRingX n J) :
    P.W₁ℂ =
        P.W₁ℂ ⊓ V10 n (productStructure n J) ⊔ P.W₁ℂ ⊓ V01 n (productStructure n J) ∧
      P.W₂ℂ =
        P.W₂ℂ ⊓ V10 n (productStructure n J) ⊔ P.W₂ℂ ⊓ V01 n (productStructure n J) := by
  have _ := hd
  have _ := hP
  have hn := P.s22b_n_pos
  rw [KSecant.s22b_W₁ℂ_eq P hn, KSecant.s22b_W₂ℂ_eq P hn]
  exact ⟨(P.s22b_core J hJ hPJ P.u₁ P.isPure (Submodule.subset_span (by simp))).1,
    (P.s22b_core J hJ hPJ P.u₂ P.isPure₂ (Submodule.subset_span (by simp))).1⟩

end KSecant

end WeilClasses
