module

public import WeilClasses.Spinor.Integral
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The Clifford groups `G(V_F)`, `G(V)` and the lines `⋀^{2n} W ⊆ C(V_F)` (paper §§2.1–2.2)

Definitions of the paper's §§2.1–2.2 that the statements of the cited results of [Chevalley] use:
the Clifford group `G(V_F)` ([III.2.1], `WeilClasses.External.Chevalley.Sec2_1`) and `⋀^{2n} W` as
a subspace of `C(V_F)` ([III.3.2], `WeilClasses.External.Chevalley.Sec2_2`); the integral Clifford
group `G(V)` is defined next to `G(V_F)`. They live here, upstream of both, so that the files of
§§2.1–2.2 (`WeilClasses.PureSpinor.Sec2_1`, `WeilClasses.PureSpinor.Lemma2_2_1`,
`WeilClasses.PureSpinor.Lemma2_2_6`) can import those cited results and use them where the paper
cites them.

## Main definitions

* `WeilClasses.cliffordGroup F n`: the Clifford group `G(V_F) = {x ∈ C(V_F)ˣ : x V x⁻¹ ⊆ V}` of
  §2.1 (untwisted, as in the paper);
* `WeilClasses.cliffordGroupZ n`: the integral Clifford group `G(V) = {x ∈ C(V)ˣ : x V x⁻¹ ⊆ V}` of
  §2.1, inside `C(V_ℚ)ˣ`;
* `WeilClasses.cliffordTopPiece F n W`: `⋀^{2n} W` regarded as a subspace of `C(V_F)` (proof of
  Lemma 2.2.6, and [Chevalley, III.3.2]).

They were moved here unchanged from `WeilClasses.PureSpinor.Sec2_1` (`cliffordGroup`,
`cliffordGroupZ`) and `WeilClasses.PureSpinor.Lemma2_2_6` (`cliffordTopPiece`), together with the
helper lemmas (prefix `s21_`, prover P02) that the proofs of their fields use. The helper
`s21_pairing_eq_of_conj_ι` is the claim `WeilClasses.pairing_eq_of_conj_ι` of §2.1 (`ρ` takes values
in `O(V)`), which is stated, and proved from it, in `WeilClasses.PureSpinor.Sec2_1`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ### Helpers (prefix `s21_`): coordinates on `V_F` -/

section HelpersField

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s21_f_e (i j : Fin (2 * n)) : f F n i (e F n j) = if i = j then 1 else 0 := by
  simp only [f, e, LinearMap.proj_apply, Pi.single_apply]

omit [CharZero F] in
theorem s21_polar_apply (v w : V F n) : QuadraticMap.polar (Q F n) v w = v.1 w.2 + w.1 v.2 :=
  TauCeti.polar_dualProd v w

omit [CharZero F] in
/-- `v = Σᵢ v₁(eᵢ) fᵢ + Σᵢ v₂(i) eᵢ` in the basis `fᵢ = (fᵢ, 0)`, `eᵢ = (0, eᵢ)` of `V_F`. -/
theorem s21_V_decomp (v : V F n) :
    v = ∑ i, v.1 (e F n i) • ((f F n i, 0) : V F n) + ∑ i, v.2 i • ((0, e F n i) : V F n) := by
  obtain ⟨θ, w⟩ := v
  have hθ : θ = ∑ i, θ (e F n i) • f F n i := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro j
    rw [LinearMap.sum_apply, Finset.sum_eq_single j]
    · rw [LinearMap.smul_apply, Pi.basisFun_apply,
        show (Pi.single j (1 : F) : H1 F n) = e F n j from rfl, s21_f_e]
      simp
    · intro i _ hij
      rw [LinearMap.smul_apply, Pi.basisFun_apply,
        show (Pi.single j (1 : F) : H1 F n) = e F n j from rfl, s21_f_e]
      simp [hij]
    · simp
  have hw : w = ∑ i, w i • e F n i := by
    ext j
    simp [e, Pi.single_apply]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
      add_zero]
    exact hθ
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
      zero_add]
    exact hw

end HelpersField

/-! ### The Clifford group `G(V_F)` -/

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- If `x V_F x⁻¹ ⊆ V_F` then `x⁻¹ V_F x ⊆ V_F`: `v ↦ x v x⁻¹` is an injective endomorphism of the
finite-dimensional space `V_F`, hence onto. -/
theorem s21_inv_conj_mem {x : (C F n)ˣ}
    (hx : ∀ v : V F n, ∃ u : V F n, (x : C F n) * ι (Q F n) v * ((x⁻¹ : (C F n)ˣ) : C F n) =
      ι (Q F n) u) (v : V F n) :
    ∃ u : V F n, ((x⁻¹ : (C F n)ˣ) : C F n) * ι (Q F n) v * (((x⁻¹)⁻¹ : (C F n)ˣ) : C F n) =
      ι (Q F n) u := by
  let φ : V F n →ₗ[F] V F n := ιInv (Q F n) ∘ₗ
    (LinearMap.mulLeft F (x : C F n) ∘ₗ LinearMap.mulRight F ((x⁻¹ : (C F n)ˣ) : C F n)) ∘ₗ
      ι (Q F n)
  have hφ : ∀ w, ι (Q F n) (φ w) = (x : C F n) * ι (Q F n) w * ((x⁻¹ : (C F n)ˣ) : C F n) := by
    intro w
    obtain ⟨u, hu⟩ := hx w
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, ← mul_assoc, hu, ιInv_ι]
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg (ι (Q F n)) hab
    rw [hφ, hφ] at h
    have h' : ι (Q F n) a = ι (Q F n) b :=
      (Units.mul_right_inj x).mp ((Units.mul_left_inj x⁻¹).mp h)
    exact ι_injective (Q F n) h'
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj v
  refine ⟨w, ?_⟩
  have h := hφ w
  rw [hw] at h
  rw [inv_inv, h]
  simp only [← mul_assoc, Units.inv_mul, one_mul]
  rw [mul_assoc, Units.inv_mul, mul_one]

/-- The Clifford group `G(V_F) = {x ∈ C(V_F)ˣ : x V_F x⁻¹ ⊆ V_F}` of §2.1 (the untwisted Clifford
group, the paper's convention), as a subgroup of the units of `C(V_F)`. -/
def cliffordGroup : Subgroup (C F n)ˣ where
  carrier := {x | ∀ v : V F n, ∃ u : V F n,
    (x : C F n) * ι (Q F n) v * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u}
  one_mem' := fun v => ⟨v, by simp⟩
  mul_mem' := by
    intro x y hx hy v
    obtain ⟨u, hu⟩ := hy v
    obtain ⟨u', hu'⟩ := hx u
    refine ⟨u', ?_⟩
    rw [← hu', ← hu]
    simp only [mul_inv_rev, Units.val_mul, mul_assoc]
  inv_mem' := fun {_} hx v => s21_inv_conj_mem F n hx v

/-- Conjugation by a unit preserves the pairing: if `x v₁ x⁻¹ = u₁` and `x v₂ x⁻¹ = u₂` in
`C(V_F)`, then `(u₁, u₂)_V = (v₁, v₂)_V`. This is the claim `pairing_eq_of_conj_ι` of §2.1
(`ρ : G(V_F) → O(V_F)`), used here for the inverse in `cliffordGroupZ`. -/
theorem s21_pairing_eq_of_conj_ι (x : (C F n)ˣ) (v₁ v₂ u₁ u₂ : V F n)
    (h₁ : (x : C F n) * ι (Q F n) v₁ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₁)
    (h₂ : (x : C F n) * ι (Q F n) v₂ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₂) :
    pairing F n u₁ u₂ = pairing F n v₁ v₂ := by
  have key : ι (Q F n) u₁ * ι (Q F n) u₂ + ι (Q F n) u₂ * ι (Q F n) u₁ =
      (x : C F n) * (ι (Q F n) v₁ * ι (Q F n) v₂ + ι (Q F n) v₂ * ι (Q F n) v₁) *
        ((x⁻¹ : (C F n)ˣ) : C F n) := by
    rw [← h₁, ← h₂]
    simp only [mul_add, add_mul, mul_assoc, Units.inv_mul_cancel_left]
  rw [ι_mul_ι_add_swap, ι_mul_ι_add_swap, ← Algebra.commutes, mul_assoc, Units.mul_inv,
    mul_one] at key
  exact algebraMap_injective (Q F n) key

end Field

/-! ### Helpers (prefix `s21_`): the lattice `V` -/

section HelpersIntegral

variable {n : ℕ}

theorem s21_e_mem_VZ (i : Fin (2 * n)) : ((0, e ℚ n i) : V ℚ n) ∈ VZ n := by
  refine ⟨fun j => ⟨0, by simp⟩, fun j => ?_⟩
  by_cases hij : j = i
  · exact ⟨1, by simp [e, hij]⟩
  · exact ⟨0, by simp [e, hij]⟩

theorem s21_f_mem_VZ (i : Fin (2 * n)) : ((f ℚ n i, 0) : V ℚ n) ∈ VZ n := by
  refine ⟨fun j => ?_, fun j => ⟨0, by simp⟩⟩
  by_cases hij : i = j
  · exact ⟨1, by simp [e, f, hij]⟩
  · exact ⟨0, by simp [e, f, hij]⟩

/-- The lattice `V` spans `V_ℚ`: a subspace containing `V` is everything. -/
theorem s21_eq_top_of_VZ (P : Submodule ℚ (V ℚ n)) (hP : ∀ v ∈ VZ n, v ∈ P) : P = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  rw [s21_V_decomp v]
  exact P.add_mem (P.sum_mem fun i _ => P.smul_mem _ (hP _ (s21_f_mem_VZ i)))
    (P.sum_mem fun i _ => P.smul_mem _ (hP _ (s21_e_mem_VZ i)))

/-- If `a v b ∈ V_ℚ` for all `v ∈ V`, then for all `v ∈ V_ℚ` (`V` spans `V_ℚ`). -/
theorem s21_forall_of_VZ (a b : C ℚ n)
    (h : ∀ v ∈ VZ n, ∃ u, a * ι (Q ℚ n) v * b = ι (Q ℚ n) u) (w : V ℚ n) :
    ∃ u, a * ι (Q ℚ n) w * b = ι (Q ℚ n) u := by
  let φ : V ℚ n →ₗ[ℚ] C ℚ n := (LinearMap.mulLeft ℚ a ∘ₗ LinearMap.mulRight ℚ b) ∘ₗ ι (Q ℚ n)
  have hφ : ∀ v, φ v = a * ι (Q ℚ n) v * b := fun v => by
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, mul_assoc]
  have hP := s21_eq_top_of_VZ ((LinearMap.range (ι (Q ℚ n))).comap φ) fun v hv => by
    obtain ⟨u, hu⟩ := h v hv
    exact ⟨u, by rw [hφ, hu]⟩
  have hw : w ∈ (LinearMap.range (ι (Q ℚ n))).comap φ := hP ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := hw
  exact ⟨u, by rw [← hφ, hu]⟩

/-- `θ(w) = Σᵢ θ(eᵢ) wᵢ`. -/
theorem s21_dual_apply (θ : Module.Dual ℚ (H1 ℚ n)) (w : H1 ℚ n) :
    θ w = ∑ i, θ (e ℚ n i) * w i := by
  conv_lhs => rw [show w = ∑ i, w i • e ℚ n i by ext j; simp [e, Pi.single_apply]]
  simp [map_sum, mul_comm]

/-- The pairing (1.2.2) is integral on `V`. -/
theorem s21_pairing_VZ {v y : V ℚ n} (hv : v ∈ VZ n) (hy : y ∈ VZ n) :
    ∃ z : ℤ, pairing ℚ n v y = z := by
  have hR : pairing ℚ n v y ∈ (Int.castRingHom ℚ).range := by
    rw [pairing, QuadraticMap.polarBilin_apply_apply, s21_polar_apply, s21_dual_apply,
      s21_dual_apply]
    refine Subring.add_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_)
      (Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_)
    · obtain ⟨z, hz⟩ := hv.1 i; exact ⟨z, by simp [hz]⟩
    · obtain ⟨z, hz⟩ := hy.2 i; exact ⟨z, by simp [hz]⟩
    · obtain ⟨z, hz⟩ := hy.1 i; exact ⟨z, by simp [hz]⟩
    · obtain ⟨z, hz⟩ := hv.2 i; exact ⟨z, by simp [hz]⟩
  obtain ⟨z, hz⟩ := hR
  exact ⟨z, by simpa using hz.symm⟩

/-- `V` is unimodular: a vector of `V_ℚ` with integral pairing against `V` lies in `V`. -/
theorem s21_mem_VZ_of_pairing (u : V ℚ n)
    (h : ∀ y ∈ VZ n, ∃ z : ℤ, pairing ℚ n u y = z) : u ∈ VZ n := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨z, hz⟩ := h _ (s21_e_mem_VZ i)
    refine ⟨z, ?_⟩
    rw [← hz, pairing, QuadraticMap.polarBilin_apply_apply, s21_polar_apply]
    simp
  · obtain ⟨z, hz⟩ := h _ (s21_f_mem_VZ i)
    refine ⟨z, ?_⟩
    rw [← hz, pairing, QuadraticMap.polarBilin_apply_apply, s21_polar_apply]
    simp [f]

end HelpersIntegral

/-! ### The integral Clifford group `G(V)` -/

section Integral

variable (n : ℕ)

/-- If `x V x⁻¹ ⊆ V` (integrally) then `x⁻¹ V x ⊆ V`: by unimodularity of `V`, since
`v ↦ x v x⁻¹` is an isometry of `V_ℚ` (`s21_pairing_eq_of_conj_ι`). -/
theorem s21_inv_conj_mem_VZ {x : (C ℚ n)ˣ}
    (hx : ∀ v ∈ VZ n, ∃ u ∈ VZ n,
      (x : C ℚ n) * ι (Q ℚ n) v * ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) = ι (Q ℚ n) u)
    (v : V ℚ n) (hv : v ∈ VZ n) :
    ∃ u ∈ VZ n, ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) * ι (Q ℚ n) v * (((x⁻¹)⁻¹ : (C ℚ n)ˣ) : C ℚ n) =
      ι (Q ℚ n) u := by
  have hxQ : ∀ w : V ℚ n, ∃ u, (x : C ℚ n) * ι (Q ℚ n) w * ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) =
      ι (Q ℚ n) u :=
    s21_forall_of_VZ _ _ fun w hw => (hx w hw).imp fun u hu => hu.2
  obtain ⟨u, hu⟩ := s21_inv_conj_mem ℚ n hxQ v
  refine ⟨u, ?_, hu⟩
  apply s21_mem_VZ_of_pairing
  intro y hy
  obtain ⟨y', hy', hyy'⟩ := hx y hy
  have hv' : (x : C ℚ n) * ι (Q ℚ n) u * ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) = ι (Q ℚ n) v := by
    rw [← hu, inv_inv]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  rw [← s21_pairing_eq_of_conj_ι ℚ n x u y v y' hv' hyy']
  exact s21_pairing_VZ hv hy'

/-- The integral Clifford group `G(V) = {x ∈ C(V)ˣ : x V x⁻¹ ⊆ V}` of §2.1, inside `C(V_ℚ)ˣ`: the
units `x` of `C(V_ℚ)` with `x, x⁻¹ ∈ C(V)` (`CZ n`) and `x V x⁻¹ ⊆ V` (`VZ n`). -/
noncomputable def cliffordGroupZ : Subgroup (C ℚ n)ˣ where
  carrier := {x | (x : C ℚ n) ∈ CZ n ∧ ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) ∈ CZ n ∧
    ∀ v ∈ VZ n, ∃ u ∈ VZ n, (x : C ℚ n) * ι (Q ℚ n) v * ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) = ι (Q ℚ n) u}
  one_mem' := ⟨Subring.one_mem _, by simp, fun v hv => ⟨v, hv, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx', hxV⟩ ⟨hy, hy', hyV⟩
    refine ⟨?_, ?_, fun v hv => ?_⟩
    · rw [Units.val_mul]; exact Subring.mul_mem _ hx hy
    · rw [mul_inv_rev, Units.val_mul]; exact Subring.mul_mem _ hy' hx'
    · obtain ⟨u, hu, huv⟩ := hyV v hv
      obtain ⟨u', hu', hu'v⟩ := hxV u hu
      refine ⟨u', hu', ?_⟩
      rw [← hu'v, ← huv]
      simp only [mul_inv_rev, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro x ⟨hx, hx', hxV⟩
    exact ⟨hx', by rw [inv_inv]; exact hx, fun v hv => s21_inv_conj_mem_VZ n hxV v hv⟩

end Integral

/-! ### `⋀^{2n} W` as a subspace of `C(V_F)` -/

section TopPiece

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The top exterior power `⋀^{2n} W` of a subspace `W ⊆ V_F`, "considered as a one-dimensional
subspace of `C(V)`" (proof of Lemma 2.2.6): the span of the products `w₁ ⋯ w_{2n}` in `C(V_F)` of
`2n` vectors of `W`. For `W` isotropic of dimension `2n` it is a line. -/
noncomputable def cliffordTopPiece (W : Submodule F (V F n)) : Submodule F (C F n) :=
  Submodule.span F
    {x | ∃ w : Fin (2 * n) → V F n, (∀ i, w i ∈ W) ∧ x = (List.ofFn fun i => ι (Q F n) (w i)).prod}

end TopPiece

end WeilClasses
