module

public import WeilClasses.PureSpinor.Defs
public import WeilClasses.PureSpinor.Sec2_1
import WeilClasses.External.Chevalley.Sec2_1
import WeilClasses.External.Chevalley.Sec2_2
import WeilClasses.PureSpinor.CM
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

/-!
# Pure spinors, rational `K`-secants, and Lemma 2.2.1 (paper §2.2, first part)

The definitions of pure spinors, of rational `K`-secants (`WeilClasses.KSecant`), of `W₁`, `W₂`,
`P_K` and `P` are in `WeilClasses.PureSpinor.Defs`. This file states the claims of §2.2 up to and
including the paragraph following Lemma 2.2.1:

* `ann_m_spin`: `ker m_{g s} = ρ(g)(ker m_s)`, so `W ↦ [s]` is a `Spin(V)`-equivariant embedding
  `IGr₊(2n, V_ℂ) → ℙ(S⁺_ℂ)` (together with [Chevalley, III.1.4–1.5], stated in
  `WeilClasses.External.Chevalley.Sec2_2`); `finrank_Splus`: `ℙ(S⁺_ℂ) ≅ ℙ^{2^{2n-1}-1}`. The
  isotropic Grassmannian `IGr(2n, V_ℂ)` itself (its dimension `2n² - n` and its two connected
  components) is not modeled;
* basic facts on a `K`-secant `P`: `u₁ ≠ 0`, `u₂` is pure, `W₂ = σ(W₁)` ("`W₂` is the complex
  conjugate of `W₁`"), `P_K` is defined over `ℚ` and `P ⊆ S⁺_ℚ` is a plane;
* `mukai_swap_of_mem_Splus`: `(t, s)_S = (-1)^n (s, t)_S` on `S⁺` (§1.2 says the Mukai pairing is
  symmetric for even `n` and antisymmetric for odd `n`);
* **Lemma 2.2.1**, corrected as decided with the project owner (`lemma2_2_1`, `lemma2_2_1_even`,
  `lemma2_2_1_odd`), and its consequence `KSecant.isCompl_of_not_isIsotropic`
  (`V_K = W₁ ⊕ W₂` when `P` is non-isotropic);
* `KSecant.isEvenPureSpinor_iff_of_mem_span`: when `W₁ ∩ W₂ = 0` and `n > 1`, the line `ℙ(P_ℂ)`
  meets the spinor variety exactly in `{ℓ₁, ℓ₂}` [Chevalley, III.1.12].

## Representation choices

`K = ℚ(√-d) = Kd d ⊆ ℂ`. A `K`-point of `S` or `V` is a vector of `S (Kd d) n` or `V (Kd d) n`
(coordinates in `K`), a complex point one of `S ℂ n`, `V ℂ n`; the change of coefficients is
`bcS`/`bcV` (coordinatewise). The paper's `√-1` in the proof of Lemma 2.2.1 stands for `√-d`.

## Proofs

The proofs cite [Chevalley, III.2.4] (`chevalley_III_2_4`, `chevalley_III_2_4_self`) and
[Chevalley, III.1.12] (`chevalley_III_1_12`) from `WeilClasses.External.Chevalley.Sec2_2`, where the
paper cites them. The helpers of the sections `S22aPure` (`Spin`-invariance of the Mukai pairing,
[Chevalley, III.2.1]) and `S22aFock` (the number operator, `s22a_ann_combo_eq_bot`) are used by
`WeilClasses.PureSpinor.Stabilizer`. The helpers on change of coefficients and Galois conjugation
are adapted from those of prover P08 (`WeilClasses.Hermitian.Defs`, downstream of this file).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prover P03, prefix `s22a_`): the spin representation, the pairing, `τ`, `∫` -/

section S22aGeneral

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem s22a_m_ι_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) (x : S F n) :
    m F n (ι (Q F n) (θ, w)) x = ExteriorAlgebra.ι F w * x + D F n θ x := by
  simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, L, LinearMap.mul_apply']

theorem s22a_mem_ann {u : S F n} {v : V F n} :
    v ∈ ann F n u ↔ m F n (ι (Q F n) v) u = 0 := Iff.rfl

theorem s22a_m_inv_m (g : Spin F n) (s : S F n) :
    m F n ((g⁻¹ : Spin F n) : C F n) (m F n (g : C F n) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    map_one, Module.End.one_apply]

theorem s22a_m_m_inv (g : Spin F n) (s : S F n) :
    m F n (g : C F n) (m F n ((g⁻¹ : Spin F n) : C F n) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    map_one, Module.End.one_apply]

theorem s22a_rho_mul (g h : Spin F n) (v : V F n) :
    rho F n (g * h) v = rho F n g (rho F n h v) := by
  simp only [rho, spinVectorAction_mul, LinearEquiv.mul_apply]

theorem s22a_rho_one (v : V F n) : rho F n 1 v = v := by
  simp only [rho, spinVectorAction_one, LinearEquiv.refl_apply]

theorem s22a_rho_inv_rho (g : Spin F n) (v : V F n) : rho F n g⁻¹ (rho F n g v) = v := by
  rw [← s22a_rho_mul, inv_mul_cancel, s22a_rho_one]

theorem s22a_rho_rho_inv (g : Spin F n) (v : V F n) : rho F n g (rho F n g⁻¹ v) = v := by
  rw [← s22a_rho_mul, mul_inv_cancel, s22a_rho_one]

/-- `ρ(g)(ker m_u) ⊆ ker m_{g u}`. -/
theorem s22a_rho_mem_ann (g : Spin F n) {u : S F n} {v : V F n} (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n (m F n (g : C F n) u) := by
  show m F n (ι (Q F n) (rho F n g v)) (m F n (g : C F n) u) = 0
  have h1 : m F n (star (g : C F n)) (m F n (g : C F n) u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, spinGroup.star_mul_self_of_mem g.2, map_one,
      Module.End.one_apply]
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  rw [ι_rho, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1, hv', map_zero]

/-- The Clifford relation for `m`: `m_v m_w + m_w m_v = (v, w)_V`. -/
theorem s22a_m_anticomm (v w : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) + m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) =
      pairing F n v w • s := by
  have h := congrArg (fun x => m F n x s) (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q F n) v w)
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, AlgHom.commutes,
    Module.algebraMap_end_apply] at h
  rw [h, QuadraticMap.polarBilin_apply_apply]

/-- `ann(u)` is totally isotropic when `u ≠ 0`. -/
theorem s22a_Q_of_mem_ann {u : S F n} (hu : u ≠ 0) {v : V F n} (hv : v ∈ ann F n u) :
    Q F n v = 0 := by
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  have h : m F n (ι (Q F n) v * ι (Q F n) v) u = Q F n v • u := by
    rw [ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]
  rw [map_mul, Module.End.mul_apply, hv', map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hu

theorem s22a_pairing_of_mem_ann {u : S F n} (hu : u ≠ 0) {v w : V F n} (hv : v ∈ ann F n u)
    (hw : w ∈ ann F n u) : pairing F n v w = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, s22a_Q_of_mem_ann hu hv,
    s22a_Q_of_mem_ann hu hw, s22a_Q_of_mem_ann hu (Submodule.add_mem _ hv hw)]
  simp

omit [CharZero F] in
theorem s22a_finrank_V : Module.finrank F (V F n) = 2 * n + 2 * n := by
  rw [Module.finrank_eq_card_basis (basisV F n), Fintype.card_fin]

omit [CharZero F] in
theorem s22a_pairing_comm (x y : V F n) : pairing F n x y = pairing F n y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

omit [CharZero F] in
theorem s22a_pairing_sepLeft (x : V F n) (hx : ∀ y, pairing F n x y = 0) : x = 0 := by
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

omit [CharZero F] in
theorem s22a_pairing_nondegenerate : (pairing F n).Nondegenerate :=
  ⟨fun x hx => s22a_pairing_sepLeft x hx,
    fun y hy => s22a_pairing_sepLeft y fun x => by rw [s22a_pairing_comm]; exact hy x⟩

/-- `ρ(g)` is an isometry of `(·,·)_V`. -/
theorem s22a_pairing_rho (g : Spin F n) (x y : V F n) :
    pairing F n (rho F n g x) (rho F n g y) = pairing F n x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, rho, ← map_add,
    spinVectorAction_map_app]

omit [CharZero F] in
/-- An isotropic subspace of `V_F` has dimension at most `2n`. -/
theorem s22a_finrank_le_of_isotropic {W : Submodule F (V F n)}
    (hW : ∀ a ∈ W, ∀ b ∈ W, pairing F n a b = 0) : Module.finrank F W ≤ 2 * n := by
  have hle : W ≤ (pairing F n).orthogonal W := fun x hx y hy => hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal s22a_pairing_nondegenerate, s22a_finrank_V] at h1
  omega

omit [CharZero F] in
theorem s22a_mukai_apply (s t : S F n) : mukai F n s t = integral F n (tau F n s * t) := rfl

omit [CharZero F] in
/-- `τ` acts on `⋀^k` by `(-1)^{k(k-1)/2}`: on a product of `k` vectors. -/
theorem s22a_tau_ιMulti {k : ℕ} (v : Fin k → H1 F n) :
    tau F n (ExteriorAlgebra.ιMulti F k v) =
      (-1 : F) ^ k.choose 2 • ExteriorAlgebra.ιMulti F k v := by
  have hl : (List.ofFn v).Pairwise (0 : QuadraticForm F (H1 F n)).IsOrtho :=
    List.pairwise_of_forall fun a b => by simp [QuadraticMap.IsOrtho]
  have h := CliffordAlgebra.reverse_prod_map_ι_of_pairwise_isOrtho (Q := (0 : QuadraticForm F (H1 F n))) hl
  rw [List.length_ofFn, List.map_ofFn] at h
  rw [ExteriorAlgebra.ιMulti_apply]
  exact h

omit [CharZero F] in
theorem s22a_tau_of_mem {k : ℕ} {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n)) :
    tau F n x = (-1 : F) ^ k.choose 2 • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact s22a_tau_ιMulti v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

omit [CharZero F] in
theorem s22a_basisS_mem (K : Finset (Fin (2 * n))) : basisS F n K ∈ ⋀[F]^K.card (H1 F n) := by
  rw [basisS, ExteriorAlgebra.basis_apply, exteriorPower.ιMulti_family_eq_coe_comp]
  exact (exteriorPower.ιMulti_family F _ _ _).2

omit [CharZero F] in
/-- `∫_X τ(x) = (-1)^n ∫_X x` (`τ` acts on `H^{2n}` by `(-1)^{2n(2n-1)/2} = (-1)^n`). -/
theorem s22a_integral_tau (x : S F n) :
    integral F n (tau F n x) = (-1 : F) ^ n * integral F n x := by
  have h : integral F n ∘ₗ tau F n = ((-1 : F) ^ n) • integral F n := by
    refine (basisS F n).ext fun K => ?_
    rw [LinearMap.comp_apply, s22a_tau_of_mem (s22a_basisS_mem K), map_smul, LinearMap.smul_apply]
    simp only [integral, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs with hK
    · subst hK
      rw [Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have h2 : 2 * n * (2 * n - 1) / 2 = n * (2 * n - 1) := by
          rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]
        have hodd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
        rw [h2, pow_mul', hodd.neg_one_pow]
    · simp
  exact LinearMap.congr_fun h x

omit [CharZero F] in
/-- `(t, s)_S = (-1)^n (s, t)_S` for all `s, t ∈ S`. -/
theorem s22a_mukai_swap (s t : S F n) : mukai F n t s = (-1 : F) ^ n * mukai F n s t := by
  rw [s22a_mukai_apply, s22a_mukai_apply]
  have h : tau F n t * s = tau F n (tau F n s * t) := by
    simp only [tau, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_reverse]
  rw [h, s22a_integral_tau]

end S22aGeneral

/-! ## Helpers (prover P03): the Mukai pairing is `Spin(V_F)`-invariant

The proof of Lemma 2.2.1 cites [Chevalley, III.2.4] (`chevalley_III_2_4`,
`chevalley_III_2_4_self`). The invariance below ([Chevalley, III.2.1]) is used by
`WeilClasses.PureSpinor.Stabilizer` (`χ₁ χ₂ = 1`). -/

section S22aPure

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `(m_g s, m_g t)_S = (s, t)_S` for `g ∈ Spin(V_F)`: [Chevalley, III.2.1] (`chevalley_III_2_1`),
as `g ∈ G(V_F)` with `N(g) = g τ(g) = g g* = 1` (`g` is even). -/
theorem s22a_mukai_spin (g : Spin F n) (s t : S F n) :
    mukai F n (m F n (g : C F n) s) (m F n (g : C F n) t) = mukai F n s t := by
  let x : (C F n)ˣ := ⟨g, star (g : C F n), spinGroup.mul_star_self_of_mem g.2,
    spinGroup.star_mul_self_of_mem g.2⟩
  have hx : x ∈ cliffordGroup F n := fun v => ⟨rho F n g v, (ι_rho F n g v).symm⟩
  have hN : (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) 1 := by
    show (g : C F n) * reverse (g : C F n) = algebraMap F (C F n) 1
    rw [map_one, ← spinGroup.mul_star_self_of_mem g.2, CliffordAlgebra.star_def,
      spinGroup.involute_eq g.2]
  have h := chevalley_III_2_1 F n x hx 1 hN s t
  rw [one_mul] at h
  exact h

end S22aPure


section General

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **`Spin(V)`-equivariance of the pure spinor embedding** (§2.2): for `g ∈ Spin(V_F)` and a spinor
`s`, `ker m_{g s} = ρ(g)(ker m_s)`. Hence `W = ker m_s ↦ [s]` is a `Spin(V)`-equivariant map
`IGr₊(2n, V) → ℙ(S⁺)`; it is injective by [Chevalley, III.1.4]
(`WeilClasses.chevalley_III_1_4_unique`). -/
theorem ann_m_spin (g : Spin F n) (s : S F n) :
    ann F n (m F n (g : C F n) s) = (ann F n s).map (rho F n g).toLinearMap := by
  ext v
  constructor
  · intro hv
    refine ⟨rho F n g⁻¹ v, ?_, s22a_rho_rho_inv g v⟩
    have h := s22a_rho_mem_ann g⁻¹ hv
    rwa [s22a_m_inv_m] at h
  · rintro ⟨w, hw, rfl⟩
    exact s22a_rho_mem_ann g hw

/-- `dim S⁺ = 2^{2n-1}`, so that `ℙ(S⁺_ℂ) ≅ ℙ^{2^{2n-1}-1}` (§2.2, first paragraph). (With the
truncated subtraction of `ℕ` the formula also holds for `n = 0`.) -/
theorem finrank_Splus : Module.finrank F (Splus F n) = 2 ^ (2 * n - 1) := by
  have : Module.Finite F (S F n) := Module.Finite.of_basis (basisS F n)
  have hS : Module.finrank F (S F n) = 2 ^ (2 * n) := by
    rw [Module.finrank_eq_card_basis (basisS F n), Fintype.card_finset, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm F (H1 F n)))
  have hS' : Module.finrank F (Splus F n) + Module.finrank F (Sminus F n) = 2 ^ (2 * n) := by
    rw [← hS]; exact hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `S = F` is spanned by `1 ∈ S⁺`.
    have h1 : (1 : S F 0) ∈ Splus F 0 :=
      CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hpos : 0 < Module.finrank F (Splus F 0) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨1, h1⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩
    simp only [mul_zero, pow_zero, Nat.zero_sub] at hS' ⊢
    omega
  · -- `m_v`, `(v, v)_V = 2`, exchanges `S⁺` and `S⁻` and squares to `1`.
    set v : V F n := (f F n ⟨0, by omega⟩, e F n ⟨0, by omega⟩) with hv
    have hQv : Q F n v = 1 := by
      simp [hv, QuadraticForm.dualProd_apply, f, e]
    have hsq : ∀ s, m F n (ι (Q F n) v) (m F n (ι (Q F n) v) s) = s := by
      intro s
      rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, hQv, map_one, map_one,
        Module.End.one_apply]
    let T₁ : Splus F n →ₗ[F] Sminus F n :=
      { toFun := fun s => ⟨m F n (ι (Q F n) v) s,
          m_mem_Sminus_of_odd F n _ (CliffordAlgebra.ι_mem_evenOdd_one _ _) _ s.2⟩
        map_add' := fun a b => by ext; simp
        map_smul' := fun c a => by ext; simp }
    let T₂ : Sminus F n →ₗ[F] Splus F n :=
      { toFun := fun s => ⟨m F n (ι (Q F n) v) s,
          m_mem_Splus_of_odd F n _ (CliffordAlgebra.ι_mem_evenOdd_one _ _) _ s.2⟩
        map_add' := fun a b => by ext; simp
        map_smul' := fun c a => by ext; simp }
    have hT₁ : Function.Injective T₁ := by
      intro a b hab
      have := congrArg (fun x : Sminus F n => m F n (ι (Q F n) v) (x : S F n)) hab
      simp only [T₁, LinearMap.coe_mk, AddHom.coe_mk, hsq] at this
      exact Subtype.ext this
    have hT₂ : Function.Injective T₂ := by
      intro a b hab
      have := congrArg (fun x : Splus F n => m F n (ι (Q F n) v) (x : S F n)) hab
      simp only [T₂, LinearMap.coe_mk, AddHom.coe_mk, hsq] at this
      exact Subtype.ext this
    have h1 := LinearMap.finrank_le_finrank_of_injective hT₁
    have h2 := LinearMap.finrank_le_finrank_of_injective hT₂
    have h3 : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- A pure spinor is nonzero when `n ≥ 1` (`ker m_0 = V` has dimension `4n ≠ 2n`). -/
theorem IsEvenPureSpinor.ne_zero {F : Type*} [Field F] [CharZero F] {n : ℕ} (hn : 0 < n)
    {w : S F n} (hw : IsEvenPureSpinor F n w) : w ≠ 0 := by
  rintro rfl
  have h := hw.2.2
  have htop : ann F n 0 = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    exact s22a_mem_ann.mpr (map_zero _)
  rw [htop, finrank_top, s22a_finrank_V] at h
  omega

/-- **The Mukai pairing on `S⁺` is `(-1)^n`-symmetric**: `(t, s)_S = (-1)^n (s, t)_S` for
`s, t ∈ S⁺` (in fact for all `s, t ∈ S`). For odd `n` it is alternating on `S⁺`. This is the reason
for the correction of the second sentence of Lemma 2.2.1 (see `lemma2_2_1_odd`). -/
theorem mukai_swap_of_mem_Splus (s t : S F n) :
    mukai F n t s = (-1) ^ n * mukai F n s t :=
  s22a_mukai_swap s t

end General

/-! ## Helpers (prover P03): dual bases, the number operator

The paper cites [Chevalley, III.1.12] after Lemma 2.2.1 and in Remark 2.2.3; this file and
`WeilClasses.PureSpinor.Stabilizer` cite `chevalley_III_1_12`
(`WeilClasses.External.Chevalley.Sec2_2`). The helpers below are used by
`WeilClasses.PureSpinor.Stabilizer` for the departures of Remark 2.2.3 ("`w` determines `P`", "the
unique secant"), which the paper does not prove in detail. For dual bases `xᵢ` of `W₁ = ker m_{u₁}`
and `yᵢ` of `W₂ = ker m_{u₂}`, the number operator `N = Σᵢ m_{xᵢ} m_{yᵢ}` satisfies
`[N, m_x] = m_x`, `[N, m_y] = -m_y`, `N u₁ = 2n u₁`, `N u₂ = 0`; so for
`v = x + y ∈ ker m_{a u₁ + b u₂}` the vectors `m_y u₁` and `m_x u₂` are eigenvectors of `N` with the
distinct eigenvalues `2n - 1` and `1` (for `n > 1`) and must vanish (`s22a_ann_combo_eq_bot`). -/

section S22aFock

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `m_w m_v = (v, w)_V - m_v m_w`. -/
theorem s22a_m_swap (v w : V F n) (s : S F n) :
    m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) =
      pairing F n v w • s - m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) := by
  rw [← s22a_m_anticomm v w s]
  abel

omit [CharZero F] in
/-- Dual bases of two complementary isotropic subspaces of dimension `2n` of `V_F`. -/
theorem s22a_dual_bases {W₁ W₂ : Submodule F (V F n)}
    (i₂ : ∀ a ∈ W₂, ∀ b ∈ W₂, pairing F n a b = 0)
    (d₁ : Module.finrank F W₁ = 2 * n) (d₂ : Module.finrank F W₂ = 2 * n) (hC : IsCompl W₁ W₂) :
    ∃ x y : Fin (2 * n) → V F n, (∀ i, x i ∈ W₁) ∧ (∀ i, y i ∈ W₂) ∧
      (∀ i j, pairing F n (x i) (y j) = if i = j then 1 else 0) ∧
      (∀ v ∈ W₁, v = ∑ i, pairing F n v (y i) • x i) ∧
      (∀ w ∈ W₂, w = ∑ i, pairing F n (x i) w • y i) := by
  let ψ : W₂ →ₗ[F] Module.Dual F W₁ := ((pairing F n).compl₁₂ W₁.subtype W₂.subtype).flip
  have hψ : ∀ (w : W₂) (v : W₁), ψ w v = pairing F n v w := fun _ _ => rfl
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply Subtype.ext
    apply s22a_pairing_sepLeft
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : pairing F n a w = 0 := by
      rw [← hψ w ⟨a, ha⟩, hw, LinearMap.zero_apply]
    rw [s22a_pairing_comm, map_add, LinearMap.add_apply, h1, i₂ _ hb _ w.2, add_zero]
  have hbij : Function.Bijective ψ := by
    refine ⟨hinj, ?_⟩
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Subspace.dual_finrank_eq, d₁, d₂]
  let e := LinearEquiv.ofBijective ψ hbij
  let bx := Module.finBasisOfFinrankEq F W₁ d₁
  have hey : ∀ j, ψ (e.symm (bx.coord j)) = bx.coord j := fun j => e.apply_symm_apply _
  refine ⟨fun i => (bx i : V F n), fun j => (e.symm (bx.coord j) : V F n), fun i => (bx i).2,
    fun j => (e.symm _).2, ?_, ?_, ?_⟩
  · intro i j
    rw [← hψ, hey, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  · intro v hv
    have h := bx.sum_repr ⟨v, hv⟩
    have h' := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    conv_lhs => rw [← h']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hψ _ ⟨v, hv⟩, hey, Module.Basis.coord_apply]
  · intro w hw
    have h := bx.sum_dual_apply_smul_coord (ψ ⟨w, hw⟩)
    have h' := congrArg (fun f => ((e.symm f : W₂) : V F n)) h
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h'
    have hw' : ((e.symm (ψ ⟨w, hw⟩) : W₂) : V F n) = w := by
      show ((e.symm (e ⟨w, hw⟩) : W₂) : V F n) = w
      rw [e.symm_apply_apply]
    rw [hw'] at h'
    conv_lhs => rw [← h']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ]

/-- The number operator `N = Σᵢ m_{xᵢ} m_{yᵢ}` satisfies `N m_v = m_v N + m_v` for `v ∈ W₁`. -/
theorem s22a_numOp_W₁ {W₁ : Submodule F (V F n)} (i₁ : ∀ a ∈ W₁, ∀ b ∈ W₁, pairing F n a b = 0)
    {x y : Fin (2 * n) → V F n} (hx : ∀ i, x i ∈ W₁) (ex₁ : ∀ v ∈ W₁, v = ∑ i, pairing F n v (y i) • x i)
    {v : V F n} (hv : v ∈ W₁) (s : S F n) :
    ∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (m F n (ι (Q F n) v) s)) =
      m F n (ι (Q F n) v) (∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s)) +
        m F n (ι (Q F n) v) s := by
  have key : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (m F n (ι (Q F n) v) s)) =
      pairing F n v (y i) • m F n (ι (Q F n) (x i)) s +
        m F n (ι (Q F n) v) (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s)) := by
    intro i
    rw [s22a_m_swap v (y i), map_sub, map_smul, s22a_m_swap v (x i), i₁ v hv (x i) (hx i),
      zero_smul, zero_sub, sub_neg_eq_add]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, map_sum, add_comm]
  congr 1
  conv_rhs => rw [ex₁ v hv]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- `N m_w = m_w N - m_w` for `w ∈ W₂`. -/
theorem s22a_numOp_W₂ {W₂ : Submodule F (V F n)} (i₂ : ∀ a ∈ W₂, ∀ b ∈ W₂, pairing F n a b = 0)
    {x y : Fin (2 * n) → V F n} (hy : ∀ i, y i ∈ W₂) (ex₂ : ∀ w ∈ W₂, w = ∑ i, pairing F n (x i) w • y i)
    {w : V F n} (hw : w ∈ W₂) (s : S F n) :
    ∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (m F n (ι (Q F n) w) s)) =
      m F n (ι (Q F n) w) (∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s)) -
        m F n (ι (Q F n) w) s := by
  have key : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (m F n (ι (Q F n) w) s)) =
      m F n (ι (Q F n) w) (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s)) -
        pairing F n (x i) w • m F n (ι (Q F n) (y i)) s := by
    intro i
    rw [s22a_m_swap w (y i), i₂ w hw (y i) (hy i), zero_smul, zero_sub, map_neg,
      s22a_m_swap w (x i), s22a_pairing_comm w (x i)]
    abel
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, map_sum]
  congr 1
  conv_rhs => rw [ex₂ w hw]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- For a transversal pair of even pure spinors and `n > 1`, `a u₁ + b u₂` with `a, b ≠ 0` has
`ker m_{a u₁ + b u₂} = 0`. This is stronger than [Chevalley, III.1.12] as stated
(`chevalley_III_1_12`: `a u₁ + b u₂` is not pure); the computation is the one of its proof
(`sa_ann_one_add_pt`, in the frame `(1, [pt])`), here in dual bases of `W₁, W₂`. Used only for the
departure in `KSecant.remark2_2_3_unique_secant`, which needs `ker m_x ∩ ker m_y = 0` for any secant
`ℂx + ℂy` through `w`. -/
theorem s22a_ann_combo_eq_bot (hn : 1 < n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) : ann F n (a • u₁ + b • u₂) = ⊥ := by
  have hu₁ : u₁ ≠ 0 := IsEvenPureSpinor.ne_zero (by omega) h₁
  have hu₂ : u₂ ≠ 0 := IsEvenPureSpinor.ne_zero (by omega) h₂
  have i₁ : ∀ a ∈ ann F n u₁, ∀ b ∈ ann F n u₁, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₁ ha hb
  have i₂ : ∀ a ∈ ann F n u₂, ∀ b ∈ ann F n u₂, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₂ ha hb
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (ann F n u₁) (ann F n u₂)
  rw [hW, finrank_bot, h₁.2.2, h₂.2.2, add_zero] at h3
  have hC : IsCompl (ann F n u₁) (ann F n u₂) := by
    refine ⟨disjoint_iff.mpr hW, codisjoint_iff.mpr ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    rw [h3, s22a_finrank_V]
  obtain ⟨x, y, hx, hy, hxy, ex₁, ex₂⟩ := s22a_dual_bases i₂ h₁.2.2 h₂.2.2 hC
  -- The number operator `N = Σᵢ m_{xᵢ} m_{yᵢ}`: `N u₂ = 0`, `N u₁ = 2n u₁`.
  set N : S F n → S F n := fun s => ∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s)
    with hN
  have hNu₂ : N u₂ = 0 := by
    simp only [hN]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show m F n (ι (Q F n) (y i)) u₂ = 0 from hy i, map_zero]
  have hNu₁ : N u₁ = (2 * n : F) • u₁ := by
    have h1 : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₁) = u₁ := by
      intro i
      rw [s22a_m_swap (y i) (x i), show m F n (ι (Q F n) (x i)) u₁ = 0 from hx i, map_zero,
        sub_zero, s22a_pairing_comm, hxy]
      simp
    simp only [hN, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul F]
    push_cast
    rfl
  have hNlin : ∀ (c₁ c₂ : F) (s₁ s₂ : S F n), N (c₁ • s₁ + c₂ • s₂) = c₁ • N s₁ + c₂ • N s₂ := by
    intro c₁ c₂ s₁ s₂
    simp only [hN, map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨x', hx', y', hy', rfl⟩ :=
    Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hv' : m F n (ι (Q F n) (x' + y')) (a • u₁ + b • u₂) = 0 := hv
  have hx'u₁ : m F n (ι (Q F n) x') u₁ = 0 := hx'
  have hy'u₂ : m F n (ι (Q F n) y') u₂ = 0 := hy'
  -- `A = m_{y'} u₁`, `B = m_{x'} u₂`.
  have e0 : a • m F n (ι (Q F n) y') u₁ + b • m F n (ι (Q F n) x') u₂ = 0 := by
    have h := hv'
    simp only [map_add, LinearMap.add_apply, map_smul, hx'u₁, hy'u₂, zero_add, add_zero] at h
    exact h
  -- `N A = (2n - 1) A`, `N B = B`.
  have hNA : N (m F n (ι (Q F n) y') u₁) = ((2 * n : F) - 1) • m F n (ι (Q F n) y') u₁ := by
    have := s22a_numOp_W₂ i₂ hy ex₂ hy' u₁
    simp only [hN] at hNu₁ ⊢
    rw [this, hNu₁, map_smul, sub_smul, one_smul]
  have hNB : N (m F n (ι (Q F n) x') u₂) = m F n (ι (Q F n) x') u₂ := by
    have := s22a_numOp_W₁ i₁ hx ex₁ hx' u₂
    simp only [hN] at hNu₂ ⊢
    rw [this, hNu₂, map_zero, zero_add]
  have e1 : a • (((2 * n : F) - 1) • m F n (ι (Q F n) y') u₁) +
      b • m F n (ι (Q F n) x') u₂ = 0 := by
    rw [← hNA, ← hNB, ← hNlin, e0]
    simp only [hN, map_zero, Finset.sum_const_zero]
  have hn1 : (n : F) ≠ 1 := by exact_mod_cast (show n ≠ 1 by omega)
  have hA : m F n (ι (Q F n) y') u₁ = 0 := by
    have h2 : (a * (2 * ((n : F) - 1))) • m F n (ι (Q F n) y') u₁ = 0 := by
      have : (a * (2 * ((n : F) - 1))) • m F n (ι (Q F n) y') u₁ =
          (a • (((2 * n : F) - 1) • m F n (ι (Q F n) y') u₁) + b • m F n (ι (Q F n) x') u₂) -
          (a • m F n (ι (Q F n) y') u₁ + b • m F n (ι (Q F n) x') u₂) := by module
      rw [this, e1, e0, sub_self]
    refine (smul_eq_zero.mp h2).resolve_left ?_
    exact mul_ne_zero ha (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hn1))
  have hB : m F n (ι (Q F n) x') u₂ = 0 := by
    rw [hA, smul_zero, zero_add] at e0
    exact (smul_eq_zero.mp e0).resolve_left hb
  have hy'0 : y' = 0 := by
    have : y' ∈ ann F n u₁ ⊓ ann F n u₂ := ⟨hA, hy'⟩
    rw [hW] at this
    exact this
  have hx'0 : x' = 0 := by
    have : x' ∈ ann F n u₁ ⊓ ann F n u₂ := ⟨hx', hB⟩
    rw [hW] at this
    exact this
  rw [hx'0, hy'0, add_zero]

/-- A nonzero multiple of an even pure spinor is an even pure spinor. -/
theorem s22a_isEvenPureSpinor_smul {u : S F n} (hu : IsEvenPureSpinor F n u) {c : F}
    (hc : c ≠ 0) : IsEvenPureSpinor F n (c • u) := by
  have hann : ann F n (c • u) = ann F n u := by
    ext v
    rw [s22a_mem_ann, s22a_mem_ann, map_smul, smul_eq_zero, or_iff_right hc]
  exact ⟨Submodule.smul_mem _ c hu.1, by rw [hann]; exact hu.2⟩

end S22aFock

/-! ## Helpers (prover P03): the field `K`, change of coefficients, Galois conjugation

Adapted from the helpers of prover P08 (`WeilClasses.Hermitian.Defs`, which imports this file). -/

section S22aField

variable {d : ℚ}

theorem s22a_coe_algebraMap (q : ℚ) : ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := by simp

theorem s22a_sqrtNeg_mul_self (hd : 0 < d) :
    Kd.sqrtNeg d * Kd.sqrtNeg d = -algebraMap ℚ (Kd d) d := by
  apply Subtype.ext
  have h := sqrtNeg_sq hd.le
  rw [pow_two] at h
  simp only [Subfield.coe_mul, Subfield.coe_neg, s22a_coe_algebraMap]
  exact h

theorem s22a_σ_sqrtNeg : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp only [Kd.coe_σ, Subfield.coe_neg]
  show (starRingEnd ℂ) (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) =
    -(Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))
  simp

theorem s22a_σ_algebraMap (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp only [Kd.coe_σ, s22a_coe_algebraMap]
  simp

theorem s22a_sqrtNeg_ne_zero (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := s22a_sqrtNeg_mul_self hd
  rw [h, zero_mul, eq_comm, neg_eq_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at this
  exact hd.ne' this

end S22aField

section S22aBaseChange

variable {n : ℕ}

theorem s22a_bcDual_apply_e {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (θ : Module.Dual F (H1 F n)) (i : Fin (2 * n)) :
    bcDual F F' n θ (e F' n i) = algebraMap F F' (θ (e F n i)) := by
  simp [bcDual, f, e, Pi.single_apply, Algebra.algebraMap_eq_smul_one]

theorem s22a_basisV_inl (F : Type*) [Field F] (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inl i)) = (f F n i, 0) := by
  simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
    Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl]
  congr 1
  ext x
  simp [f, Pi.basisFun_repr]

theorem s22a_basisV_inr (F : Type*) [Field F] (i : Fin (2 * n)) :
    basisV F n (finSumFinEquiv (Sum.inr i)) = (0, e F n i) := by
  simp only [basisV, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_apply,
    Sum.elim_inr, Function.comp_apply, LinearMap.coe_inr]
  simp [e, Pi.basisFun_apply]

theorem s22a_bcDual_f (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']
    (i : Fin (2 * n)) : bcDual F F' n (f F n i) = f F' n i := by
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp [f, e]
  · intro j _ hj
    simp [f, e, hj]
  · simp

theorem s22a_bcH1_e (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (i : Fin (2 * n)) :
    bcH1 F F' n (e F n i) = e F' n i := by
  ext j
  simp [bcH1, e, Pi.single_apply]

/-- Change of coefficients maps the basis `basisV` to the basis `basisV`. -/
theorem s22a_bcV_basisV (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] (i : Fin (2 * n + 2 * n)) : bcV F F' n (basisV F n i) = basisV F' n i := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [s22a_basisV_inl, s22a_basisV_inl]
    simp [bcV, s22a_bcDual_f]
  · rw [s22a_basisV_inr, s22a_basisV_inr]
    simp [bcV, s22a_bcH1_e]


end S22aBaseChange

section S22aCoord

/-- Coordinates of the image of a vector under a map sending a basis to a basis. -/
theorem s22a_repr_map_basis {F F' ι M M' : Type*} [Field F] [Field F'] [Algebra F F'] [Fintype ι]
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

theorem s22a_injective_map_basis {F F' ι M M' : Type*} [Field F] [Field F'] [Algebra F F'] [Fintype ι]
    [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F' M'] [Module F M']
    [IsScalarTower F F' M'] (b : Module.Basis ι F M) (b' : Module.Basis ι F' M')
    (φ : M →ₗ[F] M') (hφ : ∀ i, φ (b i) = b' i) : Function.Injective φ := by
  intro x y hxy
  apply b.repr.injective
  ext i
  have := congrArg (fun z => b'.repr z i) hxy
  simp only [s22a_repr_map_basis b b' φ hφ] at this
  exact (algebraMap F F').injective this

/-- A linear map whose matrix is fixed by a ring automorphism `c` commutes with the
`c`-semilinear map acting on coordinates. -/
theorem s22a_conj_comm {K ι M : Type*} [Field K] [Fintype ι] [AddCommGroup M] [Module K M]
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


end S22aCoord

section S22aClifford

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

theorem s22a_bcC_ι (v : V F n) : bcC F F' n (ι (Q F n) v) = ι (Q F' n) (bcV F F' n v) := by
  simp [bcC]

theorem s22a_bcC_star_spin (g : Spin F n) :
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
theorem s22a_rho_bcV (g : Spin F n) (v : V F n) :
    rho F' n (bcSpin F F' n g) (bcV F F' n v) = bcV F F' n (rho F n g v) := by
  apply CliffordAlgebra.ι_injective (Q F' n)
  rw [ι_rho, ← s22a_bcC_ι, ← s22a_bcC_ι, ι_rho]
  show bcC F F' n (g : C F n) * bcC F F' n (ι (Q F n) v) * star (bcC F F' n (g : C F n)) = _
  rw [← s22a_bcC_star_spin, ← map_mul, ← map_mul]

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_ι (w : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F w) = ExteriorAlgebra.ι F' (bcH1 F F' n w) := by
  exact ExteriorAlgebra.lift_ι_apply F _ _ w

theorem s22a_bcDual_bcH1 (θ : Module.Dual F (H1 F n)) (w : H1 F n) :
    bcDual F F' n θ (bcH1 F F' n w) = algebraMap F F' (θ w) := by
  have hw : w = ∑ i, w i • e F n i := by
    ext j; simp [e, Pi.single_apply]
  conv_rhs => rw [hw]
  simp only [bcDual, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul, map_mul]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [f, bcH1, Algebra.smul_def, mul_comm]

/-- Contraction commutes with change of coefficients. -/
theorem s22a_bcS_D (θ : Module.Dual F (H1 F n)) (s : S F n) :
    bcS F F' n (D F n θ s) = D F' n (bcDual F F' n θ) (bcS F F' n s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [D, contractLeft_algebraMap, map_zero, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x w hx =>
    simp only [D] at hx ⊢
    rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, map_mul, s22a_bcS_ι, contractLeft_ι_mul, hx,
      s22a_bcDual_bcH1, algebraMap_smul]

/-- The spin representation commutes with change of coefficients. -/
theorem s22a_m_bcC (x : C F n) (s : S F n) :
    m F' n (bcC F F' n x) (bcS F F' n s) = bcS F F' n (m F n x s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n),
      AlgHom.commutes]
    simp only [Module.algebraMap_end_apply, map_smul, algebraMap_smul]
  | ι v =>
    rw [s22a_bcC_ι]
    simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, map_add]
    obtain ⟨θ, w⟩ := v
    simp only [bcV, LinearMap.prodMap_apply, L, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mul_apply', map_mul, s22a_bcS_ι, s22a_bcS_D]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, hb, ha]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_ιMulti {k : ℕ} (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact s22a_bcS_ι F F' (v i)

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_basisS (K : Finset (Fin (2 * n))) :
    bcS F F' n (basisS F n K) = basisS F' n K := by
  simp only [basisS, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [s22a_bcS_ιMulti]
  congr 1
  ext i j
  simp [bcH1, Pi.basisFun_apply, Pi.single_apply]


end S22aClifford

section S22aConj

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_repr (s : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n s) K = algebraMap F F' ((basisS F n).repr s K) :=
  s22a_repr_map_basis (basisS F n) (basisS F' n) (bcS F F' n).toLinearMap
    (s22a_bcS_basisS F F') s K

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_injective : Function.Injective (bcS F F' n) :=
  s22a_injective_map_basis (basisS F n) (basisS F' n) (bcS F F' n).toLinearMap (s22a_bcS_basisS F F')

theorem s22a_bcV_repr (v : V F n) (i : Fin (2 * n + 2 * n)) :
    (basisV F' n).repr (bcV F F' n v) i = algebraMap F F' ((basisV F n).repr v i) :=
  s22a_repr_map_basis (basisV F n) (basisV F' n) (bcV F F' n) (s22a_bcV_basisV F F') v i

theorem s22a_bcV_injective : Function.Injective (bcV F F' n) :=
  s22a_injective_map_basis (basisV F n) (basisV F' n) (bcV F F' n) (s22a_bcV_basisV F F')

variable {F'}

theorem s22a_conjS_eq (c : F' ≃+* F') (s : S F' n) :
    conjS c n s = ∑ K, c ((basisS F' n).repr s K) • basisS F' n K := rfl

theorem s22a_conjS_smul (c : F' ≃+* F') (a : F') (s : S F' n) :
    conjS c n (a • s) = c a • conjS c n s := by
  simp only [s22a_conjS_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    smul_smul]

/-- The spin representation of a rational (resp. real) element commutes with the conjugation of
coordinates. -/
theorem s22a_m_bcC_conjS (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (x : C F n) (s : S F' n) :
    m F' n (bcC F F' n x) (conjS c n s) = conjS c n (m F' n (bcC F F' n x) s) := by
  rw [s22a_conjS_eq, s22a_conjS_eq]
  apply s22a_conj_comm
  intro i j
  rw [← s22a_bcS_basisS F F', s22a_m_bcC, s22a_bcS_repr, hc]

omit [CharZero F'] in
theorem s22a_basisV_repr_inl (v : V F' n) (i : Fin (2 * n)) :
    (basisV F' n).repr v (finSumFinEquiv (Sum.inl i)) = v.1 (e F' n i) := by
  simp only [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inl, Module.Basis.dualBasis_repr, Pi.basisFun_apply, e]

omit [CharZero F'] in
theorem s22a_basisV_repr_inr (v : V F' n) (i : Fin (2 * n)) :
    (basisV F' n).repr v (finSumFinEquiv (Sum.inr i)) = v.2 i := by
  simp only [basisV, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.prod_repr_inr, Pi.basisFun_repr]

/-- `conjV` acts on the coordinates in the basis `basisV`. -/
theorem s22a_conjV_eq (c : F' ≃+* F') (v : V F' n) :
    conjV c n v = ∑ j, c ((basisV F' n).repr v j) • basisV F' n j := by
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [s22a_basisV_repr_inl, s22a_basisV_repr_inr, s22a_basisV_inl, s22a_basisV_inr]
  ext x
  · simp only [conjV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add, Prod.fst_sum,
      Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero]
  · simp only [conjV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_add, Prod.snd_sum,
      Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Function.comp_apply]
    simp [e, Pi.single_apply]

theorem s22a_conjV_smul (c : F' ≃+* F') (a : F') (v : V F' n) :
    conjV c n (a • v) = c a • conjV c n v := by
  simp only [s22a_conjV_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    smul_smul]

/-- `m` is defined over `F`: `m_{c(v)}(c(s)) = c(m_v(s))`. -/
theorem s22a_m_ι_conj (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (v : V F' n) (s : S F' n) :
    m F' n (ι (Q F' n) (conjV c n v)) (conjS c n s) = conjS c n (m F' n (ι (Q F' n) v) s) := by
  have hv : v = ∑ j, (basisV F' n).repr v j • bcV F F' n (basisV F n j) := by
    simp only [s22a_bcV_basisV]; exact ((basisV F' n).sum_repr v).symm
  rw [s22a_conjV_eq]
  conv_rhs => rw [hv]
  simp only [← s22a_bcV_basisV F F', map_sum, map_smul, ← s22a_bcC_ι, LinearMap.sum_apply,
    LinearMap.smul_apply, s22a_conjS_smul, s22a_m_bcC_conjS F c hc]

omit [CharZero F] in
theorem s22a_conjS_bcS (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (t : S F n) : conjS c n (bcS F F' n t) = bcS F F' n t := by
  rw [s22a_conjS_eq]
  simp only [s22a_bcS_repr, hc]
  conv_rhs => rw [← (basisS F' n).sum_repr (bcS F F' n t)]
  simp only [s22a_bcS_repr]

omit [CharZero F] in
theorem s22a_conjS_ι (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (w : H1 F' n) : conjS c n (ExteriorAlgebra.ι F' w) = ExteriorAlgebra.ι F' (conjH1 c n w) := by
  have hw : ∀ w : H1 F' n, w = ∑ i, w i • e F' n i := by
    intro w
    ext j; simp [e, Pi.single_apply]
  have h1 : ExteriorAlgebra.ι F' w = ∑ i, w i • bcS F F' n (ExteriorAlgebra.ι F (e F n i)) := by
    conv_lhs => rw [hw w]
    simp only [map_sum, map_smul, s22a_bcS_ι, s22a_bcH1_e]
  have h2 : conjH1 c n w = ∑ i, c (w i) • e F' n i := by
    rw [hw (conjH1 c n w)]
    rfl
  rw [h1, h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s22a_conjS_smul, s22a_conjS_bcS F c hc, s22a_bcS_ι, s22a_bcH1_e, map_smul]

theorem s22a_conjS_algebraMap (c : F' ≃+* F') (r : F') :
    conjS c n (algebraMap F' (S F' n) r) = algebraMap F' (S F' n) (c r) := by
  rw [Algebra.algebraMap_eq_smul_one, s22a_conjS_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

omit [CharZero F] in
/-- The conjugation of coordinates preserves `S⁺`. -/
theorem s22a_conjS_Splus (c : F' ≃+* F') (hc : ∀ q : F, c (algebraMap F F' q) = algebraMap F F' q)
    (s : S F' n) (hs : s ∈ Splus F' n) : conjS c n s ∈ Splus F' n := by
  induction s, hs using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_zero, pow_zero] at hv
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hv
    rw [s22a_conjS_algebraMap]
    exact CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨_, rfl⟩)
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul]
    erw [s22a_conjS_ι F c hc, s22a_conjS_ι F c hc]
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm F' (H1 F' n)) (conjH1 c n m₁)
        (conjH1 c n m₂)) ih
    simp only [add_zero] at h
    exact h


end S22aConj

section S22aEven

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
/-- Change of coefficients preserves `S⁺`. -/
theorem s22a_bcS_Splus (s : S F n) (hs : s ∈ Splus F n) : bcS F F' n s ∈ Splus F' n := by
  induction s, hs using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_zero, pow_zero] at hv
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hv
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n)]
    exact CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.mem_one.mpr ⟨_, rfl⟩)
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul]
    erw [s22a_bcS_ι F F', s22a_bcS_ι F F']
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm F' (H1 F' n)) (bcH1 F F' n m₁)
        (bcH1 F F' n m₂)) ih
    simp only [add_zero] at h
    exact h

omit [CharZero F] [CharZero F'] in
/-- Change of coefficients preserves `S⁻`. -/
theorem s22a_bcS_Sminus (s : S F n) (hs : s ∈ Sminus F n) : bcS F F' n s ∈ Sminus F' n := by
  induction s, hs using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    simp only [ZMod.val_one, pow_one] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [show (ι (0 : QuadraticForm F (H1 F n)) w : S F n) = ExteriorAlgebra.ι F w from rfl,
      s22a_bcS_ι]
    exact CliffordAlgebra.ι_mem_evenOdd_one _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul]
    erw [s22a_bcS_ι F F', s22a_bcS_ι F F']
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm F' (H1 F' n)) (bcH1 F F' n m₁)
        (bcH1 F F' n m₂)) ih
    simp only [zero_add] at h
    exact h

end S22aEven

section S22aMukaiBc

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

omit [CharZero F] [CharZero F'] in
theorem s22a_bcS_tau (s : S F n) : bcS F F' n (tau F n s) = tau F' n (bcS F F' n s) := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    simp only [tau, CliffordAlgebra.reverse.commutes, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), CliffordAlgebra.reverse.commutes]
  | ι w =>
    simp only [tau, CliffordAlgebra.reverse_ι]
    rw [show (ι (0 : QuadraticForm F (H1 F n)) w : S F n) = ExteriorAlgebra.ι F w from rfl,
      s22a_bcS_ι]
    exact (CliffordAlgebra.reverse_ι _).symm
  | mul a b ha hb =>
    simp only [tau, CliffordAlgebra.reverse.map_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit [CharZero F] [CharZero F'] in
theorem s22a_integral_bcS (s : S F n) :
    integral F' n (bcS F F' n s) = algebraMap F F' (integral F n s) := by
  simp only [integral, Module.Basis.coord_apply]
  exact s22a_bcS_repr F F' s Finset.univ

omit [CharZero F] [CharZero F'] in
/-- The Mukai pairing commutes with change of coefficients. -/
theorem s22a_mukai_bcS (s t : S F n) :
    mukai F' n (bcS F F' n s) (bcS F F' n t) = algebraMap F F' (mukai F n s t) := by
  rw [s22a_mukai_apply, s22a_mukai_apply, ← s22a_bcS_tau, ← map_mul, s22a_integral_bcS]

theorem s22a_bcC_reverse (x : C F n) :
    bcC F F' n (CliffordAlgebra.reverse x) = CliffordAlgebra.reverse (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.reverse.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (C F' n), CliffordAlgebra.reverse.commutes]
  | ι v => rw [CliffordAlgebra.reverse_ι, s22a_bcC_ι, CliffordAlgebra.reverse_ι]
  | mul a b ha hb => rw [CliffordAlgebra.reverse.map_mul, map_mul, map_mul, ha, hb,
      CliffordAlgebra.reverse.map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]


end S22aMukaiBc

section S22aTrans

variable (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Field F'']
  [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F''] {n : ℕ}

omit [CharZero F] [CharZero F'] [CharZero F''] in
theorem s22a_bcH1_trans (w : H1 F n) :
    bcH1 F' F'' n (bcH1 F F' n w) = bcH1 F F'' n w := by
  ext i
  simp [bcH1, ← IsScalarTower.algebraMap_apply]

theorem s22a_bcDual_trans (θ : Module.Dual F (H1 F n)) :
    bcDual F' F'' n (bcDual F F' n θ) = bcDual F F'' n θ := by
  show (∑ i, algebraMap F' F'' ((bcDual F F' n θ) (e F' n i)) • f F'' n i) =
    ∑ i, algebraMap F F'' (θ (e F n i)) • f F'' n i
  simp only [s22a_bcDual_apply_e, ← IsScalarTower.algebraMap_apply]

theorem s22a_bcV_trans (v : V F n) : bcV F' F'' n (bcV F F' n v) = bcV F F'' n v := by
  simp only [bcV, LinearMap.prodMap_apply, s22a_bcDual_trans, s22a_bcH1_trans]

omit [CharZero F] [CharZero F'] [CharZero F''] in
theorem s22a_bcS_trans (s : S F n) : bcS F' F'' n (bcS F F' n s) = bcS F F'' n s := by
  induction s using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (S F' n),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι w =>
    rw [show (ι (0 : QuadraticForm F (H1 F n)) w : S F n) = ExteriorAlgebra.ι F w from rfl,
      s22a_bcS_ι, s22a_bcS_ι, s22a_bcS_ι, s22a_bcH1_trans]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]


end S22aTrans

section S22aSigma

variable {n : ℕ} {d : ℚ}

theorem s22a_d_pos (P : KSecant n d) : 0 < d := by
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
theorem s22a_σ_σ (z : Kd d) : Kd.σ d (Kd.σ d z) = z := by
  apply Subtype.ext; simp

theorem s22a_σS_σS (s : S (Kd d) n) : σS n d (σS n d s) = s := by
  show conjS (Kd.σ d) n (conjS (Kd.σ d) n s) = s
  rw [s22a_conjS_eq (n := n) (Kd.σ d) (conjS (Kd.σ d) n s)]
  conv_rhs => rw [← (basisS (Kd d) n).sum_repr s]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s22a_conjS_eq, (basisS (Kd d) n).repr_sum_self, s22a_σ_σ]

theorem s22a_σV_σV (v : V (Kd d) n) : σV n d (σV n d v) = v := by
  show conjV (Kd.σ d) n (conjV (Kd.σ d) n v) = v
  rw [s22a_conjV_eq (n := n) (Kd.σ d) (conjV (Kd.σ d) n v)]
  conv_rhs => rw [← (basisV (Kd d) n).sum_repr v]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [s22a_conjV_eq, (basisV (Kd d) n).repr_sum_self, s22a_σ_σ]

theorem s22a_conjS_repr {F' : Type*} [Field F'] [CharZero F'] (c : F' ≃+* F') (s : S F' n)
    (K : Finset (Fin (2 * n))) : (basisS F' n).repr (conjS c n s) K = c ((basisS F' n).repr s K) := by
  rw [s22a_conjS_eq, (basisS F' n).repr_sum_self]

/-- `σ`-fixed elements of `K` are rational. -/
private theorem s22a_eq_algebraMap_of_σ_eq (hd : 0 < d) (z : Kd d) (hz : Kd.σ d z = z) :
    z = algebraMap ℚ (Kd d) (Kd.ratPart d z) := by
  have h := Kd.eq_ratPart_add_sqrtNegCoeff hd z
  have h' := congrArg (Kd.σ d) h
  rw [hz, map_add, map_mul, s22a_σ_algebraMap, s22a_σ_algebraMap, s22a_σ_sqrtNeg] at h'
  have h2 : algebraMap ℚ (Kd d) (2 * Kd.sqrtNegCoeff d z) * Kd.sqrtNeg d = 0 := by
    rw [map_mul, map_ofNat]; linear_combination h' - h
  rcases mul_eq_zero.mp h2 with h2 | h2
  · rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at h2
    have : Kd.sqrtNegCoeff d z = 0 := by linarith
    rw [this, map_zero, zero_mul, add_zero] at h
    exact h
  · exact absurd h2 (s22a_sqrtNeg_ne_zero hd)

/-- `σ`-fixed spinors are rational (Galois descent). -/
theorem s22a_exists_bcS_of_σS_eq (hd : 0 < d) (t : S (Kd d) n) (ht : σS n d t = t) :
    ∃ p : S ℚ n, bcS ℚ (Kd d) n p = t := by
  refine ⟨∑ K, Kd.ratPart d ((basisS (Kd d) n).repr t K) • basisS ℚ n K, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (basisS (Kd d) n).sum_repr t]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, s22a_bcS_basisS ℚ (Kd d), ← algebraMap_smul (Kd d)]
  congr 1
  have hK : Kd.σ d ((basisS (Kd d) n).repr t K) = (basisS (Kd d) n).repr t K := by
    have h1 : (basisS (Kd d) n).repr (σS n d t) K = Kd.σ d ((basisS (Kd d) n).repr t K) :=
      s22a_conjS_repr (Kd.σ d) t K
    rw [← h1, ht]
  exact (s22a_eq_algebraMap_of_σ_eq hd _ hK).symm

theorem s22a_σhc (q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  simp

/-- A rational `K`-secant needs `n > 0` (`S_K` has dimension `2^{2n}`). -/
theorem s22a_n_pos (P : KSecant n d) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have : Module.Finite (Kd d) (S (Kd d) 0) := Module.Finite.of_basis (basisS (Kd d) 0)
  have h := P.linIndep.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis (basisS (Kd d) 0)] at h
  simp at h

namespace KSecant

variable (P : KSecant n d)

theorem s22a_u₁_ne_zero : P.u₁ ≠ 0 := by
  have := P.linIndep.ne_zero 0
  simpa using this

theorem s22a_u₂_ne_zero : P.u₂ ≠ 0 := by
  have := P.linIndep.ne_zero 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  exact this

theorem s22a_σS_u₂ : σS n d P.u₂ = P.u₁ := s22a_σS_σS P.u₁

/-- `σ(W₁) ⊆ W₂`. -/
theorem s22a_σV_mem_W₂ {v : V (Kd d) n} (hv : v ∈ P.W₁) : σV n d v ∈ P.W₂ := by
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) (conjS (Kd.σ d) n P.u₁) = 0
  rw [s22a_m_ι_conj ℚ (Kd.σ d) s22a_σhc]
  have hv' : m (Kd d) n (ι (Q (Kd d) n) v) P.u₁ = 0 := hv
  rw [hv', map_zero]

/-- `σ(W₂) ⊆ W₁`. -/
theorem s22a_σV_mem_W₁ {v : V (Kd d) n} (hv : v ∈ P.W₂) : σV n d v ∈ P.W₁ := by
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) P.u₁ = 0
  rw [← P.s22a_σS_u₂]
  show m (Kd d) n (ι (Q (Kd d) n) (conjV (Kd.σ d) n v)) (conjS (Kd.σ d) n P.u₂) = 0
  rw [s22a_m_ι_conj ℚ (Kd.σ d) s22a_σhc]
  have hv' : m (Kd d) n (ι (Q (Kd d) n) v) P.u₂ = 0 := hv
  rw [hv', map_zero]

theorem s22a_mem_Pℚ_iff (p : S ℚ n) : p ∈ P.Pℚ ↔ bcS ℚ (Kd d) n p ∈ P.PK := by
  simp [Pℚ]

/-- The rational points `p₁ = u₁ + u₂`, `p₂ = √-d (u₁ - u₂)` of `P_K` (`P_K` is defined over `ℚ`). -/
theorem s22a_exists_Pℚ : ∃ p₁ p₂ : S ℚ n, p₁ ∈ P.Pℚ ∧ p₂ ∈ P.Pℚ ∧
    bcS ℚ (Kd d) n p₁ = P.u₁ + P.u₂ ∧ bcS ℚ (Kd d) n p₂ = Kd.sqrtNeg d • (P.u₁ - P.u₂) := by
  have hd := s22a_d_pos P
  obtain ⟨p₁, hp₁⟩ := s22a_exists_bcS_of_σS_eq hd (P.u₁ + P.u₂) (by
    rw [map_add, P.s22a_σS_u₂, add_comm]; rfl)
  obtain ⟨p₂, hp₂⟩ := s22a_exists_bcS_of_σS_eq hd (Kd.sqrtNeg d • (P.u₁ - P.u₂)) (by
    show conjS (Kd.σ d) n (Kd.sqrtNeg d • (P.u₁ - P.u₂)) = _
    rw [s22a_conjS_smul, s22a_σ_sqrtNeg, map_sub]
    show -Kd.sqrtNeg d • (σS n d P.u₁ - σS n d P.u₂) = _
    rw [P.s22a_σS_u₂]
    show -Kd.sqrtNeg d • (P.u₂ - P.u₁) = _
    rw [neg_smul, ← smul_neg, neg_sub])
  have hu₁ : P.u₁ ∈ P.PK := Submodule.subset_span (Set.mem_insert _ _)
  have hu₂ : P.u₂ ∈ P.PK := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  refine ⟨p₁, p₂, ?_, ?_, hp₁, hp₂⟩
  · rw [s22a_mem_Pℚ_iff, hp₁]; exact Submodule.add_mem _ hu₁ hu₂
  · rw [s22a_mem_Pℚ_iff, hp₂]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu₁ hu₂)



end KSecant

end S22aSigma

section S22aBcPure

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {n : ℕ}

theorem s22a_bcV_mem_ann {u : S F n} {v : V F n} (hv : v ∈ ann F n u) :
    bcV F F' n v ∈ ann F' n (bcS F F' n u) := by
  show m F' n (ι (Q F' n) (bcV F F' n v)) (bcS F F' n u) = 0
  rw [← s22a_bcC_ι, s22a_m_bcC]
  have hv' : m F n (ι (Q F n) v) u = 0 := hv
  rw [hv', map_zero]

theorem s22a_span_bcV_sup {W₁ W₂ : Submodule F (V F n)} (h : W₁ ⊔ W₂ = ⊤) :
    Submodule.span F' (bcV F F' n '' W₁) ⊔ Submodule.span F' (bcV F F' n '' W₂) = ⊤ := by
  rw [eq_top_iff, ← (basisV F' n).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← s22a_bcV_basisV F F']
  obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ :=
    Submodule.mem_sup.mp (h ▸ Submodule.mem_top (x := basisV F n i))
  rw [← hv, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨v₁, hv₁, rfl⟩)
    (Submodule.subset_span ⟨v₂, hv₂, rfl⟩)

/-- A transversal pair of even pure spinors stays a transversal pair of even pure spinors after
change of coefficients (`ker m_{uᵢ}` spans `ker m_{uᵢ ⊗ F'}`, and isotropic subspaces have dimension
at most `2n`). -/
theorem s22a_bc_pure_pair (hn : 0 < n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) :
    IsEvenPureSpinor F' n (bcS F F' n u₁) ∧ IsEvenPureSpinor F' n (bcS F F' n u₂) ∧
      ann F' n (bcS F F' n u₁) ⊓ ann F' n (bcS F F' n u₂) = ⊥ := by
  have hu₁ : bcS F F' n u₁ ≠ 0 := fun h =>
    IsEvenPureSpinor.ne_zero hn h₁ (s22a_bcS_injective F F' (h.trans (map_zero _).symm))
  have hu₂ : bcS F F' n u₂ ≠ 0 := fun h =>
    IsEvenPureSpinor.ne_zero hn h₂ (s22a_bcS_injective F F' (h.trans (map_zero _).symm))
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (ann F n u₁) (ann F n u₂)
  rw [hW, finrank_bot, h₁.2.2, h₂.2.2, add_zero] at h3
  have hsup : ann F n u₁ ⊔ ann F n u₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h3, s22a_finrank_V]
  have hsup' : ann F' n (bcS F F' n u₁) ⊔ ann F' n (bcS F F' n u₂) = ⊤ := by
    refine eq_top_iff.mpr (le_trans (s22a_span_bcV_sup F F' hsup).ge (sup_le_sup ?_ ?_))
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact s22a_bcV_mem_ann F F' hv
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact s22a_bcV_mem_ann F F' hv
  have i₁ := s22a_finrank_le_of_isotropic (W := ann F' n (bcS F F' n u₁))
    fun a ha b hb => s22a_pairing_of_mem_ann hu₁ ha hb
  have i₂ := s22a_finrank_le_of_isotropic (W := ann F' n (bcS F F' n u₂))
    fun a ha b hb => s22a_pairing_of_mem_ann hu₂ ha hb
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (ann F' n (bcS F F' n u₁))
    (ann F' n (bcS F F' n u₂))
  rw [hsup', finrank_top, s22a_finrank_V] at h4
  refine ⟨⟨s22a_bcS_Splus F F' _ h₁.1, ⟨fun v hv => s22a_Q_of_mem_ann hu₁ hv, by omega⟩⟩,
    ⟨s22a_bcS_Splus F F' _ h₂.1, ⟨fun v hv => s22a_Q_of_mem_ann hu₂ hv, by omega⟩⟩, ?_⟩
  exact Submodule.finrank_eq_zero.mp (by omega)

end S22aBcPure


/-! ## Definite and nondegenerate restrictions of a rational bilinear form -/

section Forms

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- The restriction of a rational bilinear form `B` to a subspace `P` is *definite*:
`B(a, a) > 0` for all nonzero `a ∈ P`, or `B(a, a) < 0` for all nonzero `a ∈ P`. -/
def BilinDefiniteOn (B : LinearMap.BilinForm ℚ M) (P : Submodule ℚ M) : Prop :=
  (∀ a ∈ P, a ≠ 0 → 0 < B a a) ∨ (∀ a ∈ P, a ≠ 0 → B a a < 0)

/-- The restriction of a bilinear form `B` to a subspace `P` is *nondegenerate*: the only `a ∈ P`
with `B(a, b) = 0` for all `b ∈ P` is `a = 0`. -/
def BilinNondegOn (B : LinearMap.BilinForm ℚ M) (P : Submodule ℚ M) : Prop :=
  ∀ a ∈ P, (∀ b ∈ P, B a b = 0) → a = 0

end Forms

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-! ## Basic facts on a rational `K`-secant -/

/-- The pure spinor `u₁` spanning `ℓ̃₁` is nonzero. -/
theorem u₁_ne_zero : P.u₁ ≠ 0 := P.s22a_u₁_ne_zero

/-- The conjugate `u₂ = σ(u₁)` is an even pure spinor (§2.2: `ℓ₁, ℓ₂` are conjugate points of the
spinor variety). -/
theorem isPure₂ : IsEvenPureSpinor (Kd d) n P.u₂ := by
  refine ⟨s22a_conjS_Splus ℚ (Kd.σ d) s22a_σhc _ P.isPure.1,
    fun v hv => s22a_Q_of_mem_ann P.s22a_u₂_ne_zero hv, ?_⟩
  -- `σ` is a `σ`-semilinear bijection `W₁ → W₂`, so `dim W₂ = dim W₁ = 2n`.
  let j : P.W₁ ≃+ P.W₂ :=
    { toFun := fun v => ⟨σV n d v, P.s22a_σV_mem_W₂ v.2⟩
      invFun := fun w => ⟨σV n d w, P.s22a_σV_mem_W₁ w.2⟩
      left_inv := fun v => Subtype.ext (s22a_σV_σV _)
      right_inv := fun w => Subtype.ext (s22a_σV_σV _)
      map_add' := fun a b => Subtype.ext (map_add (σV n d) _ _) }
  have hrank := rank_eq_of_equiv_equiv (Kd.σ d) j (Kd.σ d).bijective
    (fun c v => Subtype.ext (s22a_conjV_smul (Kd.σ d) c (v : V (Kd d) n)))
  have h1 : Module.finrank (Kd d) P.W₁ = 2 * n := P.isPure.2.2
  show Module.finrank (Kd d) P.W₂ = 2 * n
  exact (show Module.finrank (Kd d) P.W₂ = Module.finrank (Kd d) P.W₁ from
    (congrArg Cardinal.toNat hrank).symm).trans h1

/-- "**`W₂` is the complex conjugate of `W₁`**" (§2.2): `σ(v) ∈ W₂ ↔ v ∈ W₁`. -/
theorem σV_mem_W₂_iff (v : V (Kd d) n) : σV n d v ∈ P.W₂ ↔ v ∈ P.W₁ := by
  refine ⟨fun h => ?_, fun h => P.s22a_σV_mem_W₂ h⟩
  have := P.s22a_σV_mem_W₁ h
  rwa [s22a_σV_σV] at this

/-- "**`P_K` is defined over `ℚ`**" (§2.2): `P_K` is spanned over `K` by the rational plane `P`. -/
theorem span_bcS_Pℚ :
    Submodule.span (Kd d) (bcS ℚ (Kd d) n '' (P.Pℚ : Set (S ℚ n))) = P.PK := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact (P.s22a_mem_Pℚ_iff p).mp hp
  · obtain ⟨p₁, p₂, hp₁, hp₂, h₁, h₂⟩ := P.s22a_exists_Pℚ
    have hs := s22a_sqrtNeg_ne_zero (s22a_d_pos P)
    set N := Submodule.span (Kd d) (bcS ℚ (Kd d) n '' (P.Pℚ : Set (S ℚ n)))
    have hb₁ : P.u₁ + P.u₂ ∈ N := Submodule.subset_span ⟨p₁, hp₁, h₁⟩
    have hb₂ : P.u₁ - P.u₂ ∈ N := by
      have := Submodule.smul_mem N (Kd.sqrtNeg d)⁻¹
        (Submodule.subset_span (s := bcS ℚ (Kd d) n '' (P.Pℚ : Set (S ℚ n))) ⟨p₂, hp₂, h₂⟩)
      rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
    have h2 : (2 : Kd d) ≠ 0 := two_ne_zero
    rw [PK, Submodule.span_le]
    rintro x (rfl | rfl)
    · have := Submodule.smul_mem N (2 : Kd d)⁻¹ (Submodule.add_mem N hb₁ hb₂)
      rwa [show P.u₁ + P.u₂ + (P.u₁ - P.u₂) = (2 : Kd d) • P.u₁ by module, smul_smul,
        inv_mul_cancel₀ h2, one_smul] at this
    · have := Submodule.smul_mem N (2 : Kd d)⁻¹ (Submodule.sub_mem N hb₁ hb₂)
      rwa [show P.u₁ + P.u₂ - (P.u₁ - P.u₂) = (2 : Kd d) • P.u₂ by module, smul_smul,
        inv_mul_cancel₀ h2, one_smul] at this

/-- The rational basis `p₁ = u₁ + u₂`, `p₂ = √-d (u₁ - u₂)` of the plane `P` (the paper's
`λ₁ = a + √-d b` with `a = p₁ / 2`, `b = -p₂ / (2d)`). -/
theorem s22a_Pℚ_basis : ∃ p₁ p₂ : S ℚ n,
    bcS ℚ (Kd d) n p₁ = P.u₁ + P.u₂ ∧ bcS ℚ (Kd d) n p₂ = Kd.sqrtNeg d • (P.u₁ - P.u₂) ∧
    LinearIndependent ℚ ![p₁, p₂] ∧ P.Pℚ = Submodule.span ℚ {p₁, p₂} := by
  obtain ⟨p₁, p₂, hp₁, hp₂, h₁, h₂⟩ := P.s22a_exists_Pℚ
  have hd := s22a_d_pos P
  have hs := s22a_sqrtNeg_ne_zero hd
  have hli2 := P.linIndep
  rw [LinearIndependent.pair_iff] at hli2
  -- `a p₁ + b p₂ ↦ (a + b√-d) u₁ + (a - b√-d) u₂`
  have hbc : ∀ a b : ℚ, bcS ℚ (Kd d) n (a • p₁ + b • p₂) =
      (algebraMap ℚ (Kd d) a + algebraMap ℚ (Kd d) b * Kd.sqrtNeg d) • P.u₁ +
        (algebraMap ℚ (Kd d) a - algebraMap ℚ (Kd d) b * Kd.sqrtNeg d) • P.u₂ := by
    intro a b
    rw [map_add, map_smul, map_smul, h₁, h₂, ← algebraMap_smul (Kd d) a,
      ← algebraMap_smul (Kd d) b]
    simp only [u₂] at *
    module
  have hli : LinearIndependent ℚ ![p₁, p₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h := hbc a b
    rw [hab, map_zero] at h
    obtain ⟨h1, h2⟩ := hli2 _ _ h.symm
    have ha : algebraMap ℚ (Kd d) a = 0 := by linear_combination (h1 + h2) / 2
    have hb : algebraMap ℚ (Kd d) b * Kd.sqrtNeg d = 0 := by linear_combination (h1 - h2) / 2
    rw [map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at ha
    rcases mul_eq_zero.mp hb with hb | hb
    · exact ⟨ha, (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp hb⟩
    · exact absurd hb hs
  have hspan : P.Pℚ = Submodule.span ℚ (Set.range ![p₁, p₂]) := by
    apply le_antisymm
    · intro p hp
      have hpK : bcS ℚ (Kd d) n p ∈ P.PK := (P.s22a_mem_Pℚ_iff p).mp hp
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hpK
      -- `σ`-invariance of `bcS p` forces `β = σ α`.
      have hσ : σS n d (bcS ℚ (Kd d) n p) = bcS ℚ (Kd d) n p :=
        s22a_conjS_bcS ℚ (Kd.σ d) s22a_σhc p
      rw [← hαβ] at hσ
      have hσ' : σS n d (α • P.u₁ + β • P.u₂) = Kd.σ d β • P.u₁ + Kd.σ d α • P.u₂ := by
        rw [map_add]
        show conjS (Kd.σ d) n (α • P.u₁) + conjS (Kd.σ d) n (β • P.u₂) = _
        rw [s22a_conjS_smul, s22a_conjS_smul]
        show Kd.σ d α • σS n d P.u₁ + Kd.σ d β • σS n d P.u₂ = _
        rw [P.s22a_σS_u₂]
        simp only [u₂]
        abel
      rw [hσ'] at hσ
      have hli2' : ∀ s t : Kd d, s • P.u₁ + t • P.u₂ = 0 → s = 0 ∧ t = 0 := hli2
      have hβ : β = Kd.σ d α := by
        have := hli2' (Kd.σ d β - α) (Kd.σ d α - β)
          (by rw [sub_smul, sub_smul, sub_add_sub_comm, hσ, sub_self])
        linear_combination -this.2
      obtain ⟨a, b, hab⟩ := (Kd.mem_iff d).mp α.2
      have hα : α = algebraMap ℚ (Kd d) a + algebraMap ℚ (Kd d) b * Kd.sqrtNeg d := by
        apply Subtype.ext
        simp only [Subfield.coe_add, Subfield.coe_mul, s22a_coe_algebraMap]
        exact hab
      have hσα : Kd.σ d α = algebraMap ℚ (Kd d) a - algebraMap ℚ (Kd d) b * Kd.sqrtNeg d := by
        rw [hα, map_add, map_mul, s22a_σ_algebraMap, s22a_σ_algebraMap, s22a_σ_sqrtNeg]
        ring
      have hp' : p = a • p₁ + b • p₂ := by
        apply s22a_bcS_injective ℚ (Kd d)
        rw [hbc, ← hαβ, hβ, hσα, ← hα]
      rw [hp']
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hp₁
      · exact hp₂
  refine ⟨p₁, p₂, h₁, h₂, hli, ?_⟩
  rw [hspan, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]


/-- The rational points `P` of `P_K` form a plane (§2.2). -/
theorem finrank_Pℚ : Module.finrank ℚ P.Pℚ = 2 := by
  obtain ⟨p₁, p₂, -, -, hli, hspan⟩ := P.s22a_Pℚ_basis
  rw [hspan, show ({p₁, p₂} : Set (S ℚ n)) = Set.range ![p₁, p₂] by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union], finrank_span_eq_card hli]
  simp

/-- The rational plane `P` lies in `S⁺_ℚ` (§2.2). -/
theorem Pℚ_le_Splus : P.Pℚ ≤ Splus ℚ n := by
  intro p hp
  have hPK : P.PK ≤ Splus (Kd d) n := by
    rw [PK, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact P.isPure.1
    · exact P.isPure₂.1
  have hK : bcS ℚ (Kd d) n p ∈ Splus (Kd d) n := hPK ((P.s22a_mem_Pℚ_iff p).mp hp)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm ℚ (H1 ℚ n))).sup_eq_top ▸
      Submodule.mem_top (x := p))
  have hbK : bcS ℚ (Kd d) n b ∈ Splus (Kd d) n := by
    have := Submodule.sub_mem _ hK (s22a_bcS_Splus ℚ (Kd d) a ha)
    rwa [map_add, add_sub_cancel_left] at this
  have hbK' : bcS ℚ (Kd d) n b ∈ Sminus (Kd d) n := s22a_bcS_Sminus ℚ (Kd d) b hb
  have h0 : bcS ℚ (Kd d) n b = 0 :=
    Submodule.disjoint_def.mp
      (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm (Kd d) (H1 (Kd d) n))).disjoint _ hbK hbK'
  have hb0 : b = 0 := s22a_bcS_injective ℚ (Kd d) (h0.trans (map_zero _).symm)
  rw [hb0, add_zero]
  exact ha

/-- When `W₁ ∩ W₂ = 0`, `V_K = W₁ ⊕ W₂` (both have dimension `2n`, and `dim V_K = 4n`). -/
theorem isCompl_of_inf_eq_bot (hW : P.W₁ ⊓ P.W₂ = ⊥) : IsCompl P.W₁ P.W₂ := by
  have h1 : Module.finrank (Kd d) P.W₁ = 2 * n := P.isPure.2.2
  have h2 : Module.finrank (Kd d) P.W₂ = 2 * n := P.isPure₂.2.2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq P.W₁ P.W₂
  rw [hW, finrank_bot, h1, h2, add_zero] at h3
  refine ⟨disjoint_iff.mpr hW, codisjoint_iff.mpr ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [h3, s22a_finrank_V]

/-! ## Lemma 2.2.1 -/

/-- `(λ₁, λ₁)_S = 0` ([Chevalley, III.2.4], `chevalley_III_2_4_self`). -/
theorem s22a_mukai_u₁_u₁ : mukai (Kd d) n P.u₁ P.u₁ = 0 :=
  chevalley_III_2_4_self (Kd d) n (s22a_n_pos P) _ P.isPure

/-- `(λ₂, λ₂)_S = 0` ([Chevalley, III.2.4], `chevalley_III_2_4_self`). -/
theorem s22a_mukai_u₂_u₂ : mukai (Kd d) n P.u₂ P.u₂ = 0 :=
  chevalley_III_2_4_self (Kd d) n (s22a_n_pos P) _ P.isPure₂

/-- `(λ₁, λ₂)_S = 0 ↔ W₁ ∩ W₂ ≠ 0` ([Chevalley, III.2.4], `chevalley_III_2_4`). -/
theorem s22a_mukai_u₁_u₂_eq_zero_iff : mukai (Kd d) n P.u₁ P.u₂ = 0 ↔ P.W₁ ⊓ P.W₂ ≠ ⊥ :=
  chevalley_III_2_4 (Kd d) n (s22a_n_pos P) _ _ P.isPure P.isPure₂

/-- The pairing on `P` in the basis `p₁ = λ₁ + λ₂`, `p₂ = √-d (λ₁ - λ₂)` (the computation of the
proof of Lemma 2.2.1): with `c = (λ₁, λ₂)_S`, `c' = (λ₂, λ₁)_S` and `(λᵢ, λᵢ)_S = 0`,
`(p₁, p₁) = c + c'`, `(p₁, p₂) = √-d (c' - c)`, `(p₂, p₁) = √-d (c - c')`, `(p₂, p₂) = d (c + c')`. -/
theorem s22a_gram {p₁ p₂ : S ℚ n} (h₁ : bcS ℚ (Kd d) n p₁ = P.u₁ + P.u₂)
    (h₂ : bcS ℚ (Kd d) n p₂ = Kd.sqrtNeg d • (P.u₁ - P.u₂)) :
    algebraMap ℚ (Kd d) (mukai ℚ n p₁ p₁) =
        mukai (Kd d) n P.u₁ P.u₂ + mukai (Kd d) n P.u₂ P.u₁ ∧
      algebraMap ℚ (Kd d) (mukai ℚ n p₁ p₂) =
        Kd.sqrtNeg d * (mukai (Kd d) n P.u₂ P.u₁ - mukai (Kd d) n P.u₁ P.u₂) ∧
      algebraMap ℚ (Kd d) (mukai ℚ n p₂ p₁) =
        Kd.sqrtNeg d * (mukai (Kd d) n P.u₁ P.u₂ - mukai (Kd d) n P.u₂ P.u₁) ∧
      algebraMap ℚ (Kd d) (mukai ℚ n p₂ p₂) =
        algebraMap ℚ (Kd d) d * (mukai (Kd d) n P.u₁ P.u₂ + mukai (Kd d) n P.u₂ P.u₁) := by
  have hsq := s22a_sqrtNeg_mul_self (s22a_d_pos P)
  have h11 := P.s22a_mukai_u₁_u₁
  have h22 := P.s22a_mukai_u₂_u₂
  rw [← s22a_mukai_bcS ℚ (Kd d), ← s22a_mukai_bcS ℚ (Kd d), ← s22a_mukai_bcS ℚ (Kd d),
    ← s22a_mukai_bcS ℚ (Kd d), h₁, h₂]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, h11, h22]
  refine ⟨by ring, by ring, by ring, ?_⟩
  linear_combination (-mukai (Kd d) n P.u₁ P.u₂ - mukai (Kd d) n P.u₂ P.u₁) * hsq

theorem s22a_mukai_pair (p₁ p₂ : S ℚ n) (r s r' s' : ℚ) :
    mukai ℚ n (r • p₁ + s • p₂) (r' • p₁ + s' • p₂) =
      r * r' * mukai ℚ n p₁ p₁ + r * s' * mukai ℚ n p₁ p₂ + s * r' * mukai ℚ n p₂ p₁ +
        s * s' * mukai ℚ n p₂ p₂ := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), first sentence,
as printed (true for all `n`): `P` is isotropic with respect to the Mukai pairing (1.2.3) (the
pairing vanishes identically on `P`) if and only if `W₁ ∩ W₂ ≠ 0`. The hypothesis `0 < d` is the
paper's "`K` purely imaginary" (it is implied by the existence of `P`).

Proof (the paper's): `(λᵢ, λᵢ)_S = 0` and `(λ₁, λ₂)_S = 0 ↔ W₁ ∩ W₂ ≠ 0` by [Chevalley, III.2.4]
(`chevalley_III_2_4_self`, `chevalley_III_2_4`), and the paper's computation of the pairing on `P`
from `(λ₁, λ₂)_S`, in the rational basis `p₁ = λ₁ + λ₂`, `p₂ = √-d (λ₁ - λ₂)` of `P` (the paper's
`λ₁ = a + ib` with `i = √-d`, `a = p₁/2`, `b = -p₂/(2d)`).

Gap in the paper (filled): the displayed computation `(λ₁, λ₁) = (a, a) - (b, b) + 2i(a, b)`,
`(λ₁, λ₂) = (a, a) + (b, b)` and the conclusion "`(a, a) = 0` iff `W₁ ∩ W₂ ≠ 0`" use a symmetric
pairing. For odd `n` the pairing is alternating on `S⁺` (`(t, s)_S = (-1)ⁿ (s, t)_S`,
`mukai_swap_of_mem_Splus`): then `(λ₁, λ₂) = -2i (a, b)_S`, `(a, a) = 0` always, and the stated
conclusion fails, although the first sentence is still true. Here the Gram matrix of `P`
(`s22a_gram`) keeps `c = (λ₁, λ₂)_S` and
`c' = (λ₂, λ₁)_S = (-1)ⁿ c` apart: `(p₁, p₁) = c + c'` and `(p₁, p₂) = √-d (c' - c)`, so `P` is
isotropic iff `c + c' = c' - c = 0` iff `c = 0`, for both parities. -/
theorem _root_.WeilClasses.lemma2_2_1 (hd : 0 < d) : P.IsIsotropic ↔ P.W₁ ⊓ P.W₂ ≠ ⊥ := by
  -- The paper's proof: `(λᵢ, λᵢ) = 0` and `(λ₁, λ₂) = 0 ↔ W₁ ∩ W₂ ≠ 0` [Chevalley, III.2.4], and the
  -- pairing on `P` is computed from `(λ₁, λ₂)` (`s22a_gram`).
  obtain ⟨p₁, p₂, h₁, h₂, hli, hspan⟩ := P.s22a_Pℚ_basis
  obtain ⟨g11, g12, g21, g22⟩ := P.s22a_gram h₁ h₂
  have hs := s22a_sqrtNeg_ne_zero hd
  rw [← P.s22a_mukai_u₁_u₂_eq_zero_iff]
  have hp₁ : p₁ ∈ P.Pℚ := hspan ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hp₂ : p₂ ∈ P.Pℚ := hspan ▸ Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · intro hiso
    have e11 := hiso p₁ hp₁ p₁ hp₁
    have e12 := hiso p₁ hp₁ p₂ hp₂
    rw [e11, map_zero] at g11
    rw [e12, map_zero] at g12
    have h' : mukai (Kd d) n P.u₂ P.u₁ - mukai (Kd d) n P.u₁ P.u₂ = 0 :=
      (mul_eq_zero.mp g12.symm).resolve_left hs
    linear_combination (-g11 - h') / 2
  · intro hc
    have hc' : mukai (Kd d) n P.u₂ P.u₁ = 0 := by
      rw [s22a_mukai_swap, hc, mul_zero]
    rw [hc, hc'] at g11 g12 g21 g22
    simp only [add_zero, sub_zero, mul_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective]
      at g11 g12 g21 g22
    intro x hx y hy
    rw [hspan] at hx hy
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨r', s', rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [s22a_mukai_pair, g11, g12, g21, g22]
    ring

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), second sentence,
for even `n` (as printed): the restriction of `(·,·)_S` to `P` is definite if and only if
`W₁ ∩ W₂ = 0`.

Correction of the paper: the second sentence is false for odd n because (·,·)_S is alternating on
S⁺ ((t,s) = (−1)ⁿ(s,t)); see REPORT.md. For odd `n` see `lemma2_2_1_odd`.

Proof (the paper's): [Chevalley, III.2.4] (`chevalley_III_2_4`) and the computation of
`lemma2_2_1`. -/
theorem _root_.WeilClasses.lemma2_2_1_even (hd : 0 < d) (hn : Even n) :
    BilinDefiniteOn (mukai ℚ n) P.Pℚ ↔ P.W₁ ⊓ P.W₂ = ⊥ := by
  obtain ⟨p₁, p₂, h₁, h₂, hli, hspan⟩ := P.s22a_Pℚ_basis
  obtain ⟨g11, g12, g21, g22⟩ := P.s22a_gram h₁ h₂
  -- `n` even: the pairing is symmetric, `c' = c`.
  have hc' : mukai (Kd d) n P.u₂ P.u₁ = mukai (Kd d) n P.u₁ P.u₂ := by
    rw [s22a_mukai_swap, hn.neg_one_pow, one_mul]
  rw [hc', sub_self, mul_zero] at g12 g21
  rw [hc'] at g11 g22
  rw [← g11] at g22
  have hB : mukai ℚ n p₁ p₂ = 0 := (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g12
  have hB' : mukai ℚ n p₂ p₁ = 0 := (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g21
  have hD : mukai ℚ n p₂ p₂ = d * mukai ℚ n p₁ p₁ := by
    apply (algebraMap ℚ (Kd d)).injective
    rw [g22, map_mul]
  -- `(r p₁ + s p₂, r p₁ + s p₂) = A (r² + d s²)` with `A = (p₁, p₁) = 2 (λ₁, λ₂)`.
  have hquad : ∀ r s : ℚ, mukai ℚ n (r • p₁ + s • p₂) (r • p₁ + s • p₂) =
      mukai ℚ n p₁ p₁ * (r ^ 2 + d * s ^ 2) := by
    intro r s
    rw [s22a_mukai_pair, hB, hB', hD]
    ring
  have hAc : mukai ℚ n p₁ p₁ = 0 ↔ mukai (Kd d) n P.u₁ P.u₂ = 0 := by
    constructor
    · intro h
      rw [h, map_zero] at g11
      have : (2 : Kd d) * mukai (Kd d) n P.u₁ P.u₂ = 0 := by rw [two_mul]; exact g11.symm
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    · intro h
      rw [h, add_zero] at g11
      exact (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g11
  have hA : mukai ℚ n p₁ p₁ ≠ 0 ↔ P.W₁ ⊓ P.W₂ = ⊥ := by
    rw [ne_eq, hAc, P.s22a_mukai_u₁_u₂_eq_zero_iff, not_not]
  have hp₁0 : p₁ ≠ 0 := hli.ne_zero 0
  have hp₁ : p₁ ∈ P.Pℚ := hspan ▸ Submodule.subset_span (Set.mem_insert _ _)
  rw [← hA]
  constructor
  · rintro (h | h)
    · exact (h p₁ hp₁ hp₁0).ne'
    · exact (h p₁ hp₁ hp₁0).ne
  · intro hA0
    have hpos : ∀ x ∈ P.Pℚ, x ≠ 0 → ∃ r s : ℚ, x = r • p₁ + s • p₂ ∧ 0 < r ^ 2 + d * s ^ 2 := by
      intro x hx hx0
      rw [hspan] at hx
      obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
      refine ⟨r, s, rfl, ?_⟩
      by_contra hle
      have h1 : r ^ 2 + d * s ^ 2 ≤ 0 := not_lt.mp hle
      have h2 : 0 ≤ d * s ^ 2 := mul_nonneg hd.le (sq_nonneg s)
      have hr2 : r ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg r)
      have hs2 : d * s ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg r]) h2
      have hr : r = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hr2
      have hs : s = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp
        ((mul_eq_zero.mp hs2).resolve_left hd.ne')
      apply hx0
      rw [hr, hs, zero_smul, zero_smul, add_zero]
    rcases lt_or_gt_of_ne hA0 with hneg | hpos'
    · right
      intro x hx hx0
      obtain ⟨r, s, rfl, hrs⟩ := hpos x hx hx0
      rw [hquad]
      exact mul_neg_of_neg_of_pos hneg hrs
    · left
      intro x hx hx0
      obtain ⟨r, s, rfl, hrs⟩ := hpos x hx hx0
      rw [hquad]
      exact mul_pos hpos' hrs

/-- **Lemma 2.2.1** (`lemma-P-is-non-isotropic-iff-W-1-and-W-2-are-transversal`), second sentence,
corrected for odd `n` (decided with the project owner): `(·,·)_S` is alternating on `S⁺`, and its
restriction to `P` is nondegenerate if and only if `W₁ ∩ W₂ = 0`.

Correction of the paper: the second sentence is false for odd n because (·,·)_S is alternating on
S⁺ ((t,s) = (−1)ⁿ(s,t)); see REPORT.md. (The paper's proof writes `λ₁ = a + ib` and uses the
symmetry of the pairing; for odd `n`, `(λ₁, λ₂) = -2√-d (a, b)_S` instead.)

Proof: [Chevalley, III.2.4] (`chevalley_III_2_4`) and the computation of `lemma2_2_1`. -/
theorem _root_.WeilClasses.lemma2_2_1_odd (hd : 0 < d) (hn : Odd n) :
    (∀ s ∈ Splus ℚ n, mukai ℚ n s s = 0) ∧
      (BilinNondegOn (mukai ℚ n) P.Pℚ ↔ P.W₁ ⊓ P.W₂ = ⊥) := by
  refine ⟨fun s _ => ?_, ?_⟩
  · have h := s22a_mukai_swap s s
    rw [hn.neg_one_pow, neg_one_mul] at h
    linarith
  obtain ⟨p₁, p₂, h₁, h₂, hli, hspan⟩ := P.s22a_Pℚ_basis
  obtain ⟨g11, g12, g21, g22⟩ := P.s22a_gram h₁ h₂
  have hs := s22a_sqrtNeg_ne_zero hd
  -- `n` odd: the pairing is alternating, `c' = -c`.
  have hc' : mukai (Kd d) n P.u₂ P.u₁ = -mukai (Kd d) n P.u₁ P.u₂ := by
    rw [s22a_mukai_swap, hn.neg_one_pow, neg_one_mul]
  rw [hc', add_neg_cancel] at g11 g22
  rw [hc'] at g12 g21
  rw [mul_zero] at g22
  have hA : mukai ℚ n p₁ p₁ = 0 := (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g11
  have hD : mukai ℚ n p₂ p₂ = 0 := (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g22
  have hB' : mukai ℚ n p₂ p₁ = -mukai ℚ n p₁ p₂ := by
    apply (algebraMap ℚ (Kd d)).injective
    rw [g21, map_neg, g12]
    ring
  have hBc : mukai ℚ n p₁ p₂ = 0 ↔ mukai (Kd d) n P.u₁ P.u₂ = 0 := by
    constructor
    · intro h
      rw [h, map_zero] at g12
      have : Kd.sqrtNeg d * (-2 * mukai (Kd d) n P.u₁ P.u₂) = 0 := by
        linear_combination -g12
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hs
      · exact (mul_eq_zero.mp h').resolve_left (by norm_num)
    · intro h
      rw [h, neg_zero, sub_zero, mul_zero] at g12
      exact (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp g12
  have hB : mukai ℚ n p₁ p₂ ≠ 0 ↔ P.W₁ ⊓ P.W₂ = ⊥ := by
    rw [ne_eq, hBc, P.s22a_mukai_u₁_u₂_eq_zero_iff, not_not]
  rw [← hB]
  have hp₁ : p₁ ∈ P.Pℚ := hspan ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hp₂ : p₂ ∈ P.Pℚ := hspan ▸ Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · intro hnd hB0
    have : p₁ = 0 := by
      apply hnd p₁ hp₁
      intro y hy
      rw [hspan] at hy
      obtain ⟨r', s', rfl⟩ := Submodule.mem_span_pair.mp hy
      have := s22a_mukai_pair p₁ p₂ 1 0 r' s'
      rw [one_smul, zero_smul, add_zero] at this
      rw [this, hA, hB0, hB', hD]
      ring
    exact hli.ne_zero 0 this
  · intro hB0 x hx hxy
    rw [hspan] at hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
    have e1 := hxy p₁ hp₁
    have e2 := hxy p₂ hp₂
    have k1 := s22a_mukai_pair p₁ p₂ r s 1 0
    have k2 := s22a_mukai_pair p₁ p₂ r s 0 1
    rw [one_smul, zero_smul, add_zero] at k1
    rw [one_smul, zero_smul, zero_add] at k2
    rw [k1, hA, hB', hD] at e1
    rw [k2, hA, hD] at e2
    have hs0 : s = 0 := by
      have : s * mukai ℚ n p₁ p₂ = 0 := by linear_combination -e1
      exact (mul_eq_zero.mp this).resolve_right hB0
    have hr0 : r = 0 := by
      have : r * mukai ℚ n p₁ p₂ = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_right hB0
    rw [hr0, hs0, zero_smul, zero_smul, add_zero]

/-- If `P` is non-isotropic, then `V_K = W₁ ⊕ W₂` (§2.2, before Lemma 2.2.4: "The vanishing
`W₁ ∩ W₂ = (0)` holds, by Lemma 2.2.1"). -/
theorem isCompl_of_not_isIsotropic (hd : 0 < d) (hP : ¬ P.IsIsotropic) : IsCompl P.W₁ P.W₂ :=
  P.isCompl_of_inf_eq_bot (not_not.mp fun h => hP ((lemma2_2_1 P hd).mpr h))

/-! ## The secant line meets the spinor variety in two points -/

/-- **The line `ℙ(P)` meets the spinor variety in `{ℓ₁, ℓ₂}`** (§2.2, after Lemma 2.2.1, by
[Chevalley, III.1.12]): if `W₁ ∩ W₂ = 0` and `n > 1`, then a vector `w` of the complex plane
`P_ℂ = ℂ u₁ + ℂ u₂` is an even pure spinor if and only if it is a nonzero multiple of `u₁` or of
`u₂`; that is, the set-theoretic intersection of `IGr₊(2n, V_ℂ)` (the spinor variety in
`ℙ(S⁺_ℂ)`) with the line through `ℓ₁` and `ℓ₂` is `{ℓ₁, ℓ₂}`.

Proof (the paper's): [Chevalley, III.1.12] (`chevalley_III_1_12`), applied over `ℂ` to the base
change of `u₁, u₂` (`s22a_bc_pure_pair`). -/
theorem isEvenPureSpinor_iff_of_mem_span (hn : 1 < n) (hW : P.W₁ ⊓ P.W₂ = ⊥)
    (w : S ℂ n) (hw : w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁, bcS (Kd d) ℂ n P.u₂}) :
    IsEvenPureSpinor ℂ n w ↔
      w ≠ 0 ∧ (w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁} ∨
        w ∈ Submodule.span ℂ {bcS (Kd d) ℂ n P.u₂}) := by
  -- `u₁, u₂` stay a transversal pair of even pure spinors over `ℂ`; then [Chevalley, III.1.12].
  obtain ⟨p₁, p₂, hW'⟩ := s22a_bc_pure_pair (Kd d) ℂ (by omega) P.isPure P.isPure₂ hW
  constructor
  · intro hpure
    refine ⟨IsEvenPureSpinor.ne_zero (by omega) hpure, ?_⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    rcases chevalley_III_1_12 ℂ n hn _ _ p₁ p₂ hW' a b hpure with rfl | rfl
    · right
      rw [zero_smul, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · left
      rw [zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro ⟨hw0, h | h⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
      exact s22a_isEvenPureSpinor_smul p₁ (left_ne_zero_of_smul hw0)
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
      exact s22a_isEvenPureSpinor_smul p₂ (left_ne_zero_of_smul hw0)

end KSecant

end WeilClasses
