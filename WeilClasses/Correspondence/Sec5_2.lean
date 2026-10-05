module

public import WeilClasses.Correspondence.Defs
public import WeilClasses.External.Chevalley.Sec2_1
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# §5.2: `Spin(V)`-equivariance of convolutions

Statements of the paper's §5.2 (TeX lines 1994–2123): the conjugate representation `m†` (5.2.1),
the invariance (5.2.2), (5.2.3) of the Poincaré pairing `∫_X s ∪ t` under `m† ⊗ m` and `m ⊗ m†`,
the behaviour of `PD` under `m`, Lemma 5.2.1 (with (5.2.4)), Corollary 5.2.2 and Remark 5.2.3.

**Model.** `H*(X × Y) = H*(X) ⊗ H*(Y)` and `γ_*` is `corr` (see
`WeilClasses.Correspondence.Defs`). The paper takes `X`, `Y`, `Z` to be abelian varieties of the
same
dimension `n` (§5.1); the statements and proofs of §5.2 do not use this, and we allow dimensions
`nX`, `nY`, `nZ`. Coefficients: a field `F` of characteristic `0` (the paper: `ℚ`).

**Left out (sheaf-theoretic, §5.1).** The integral functors `Φ_F`, `Ψ_F`, convolution of kernels,
Grothendieck–Verdier duality (5.1.1), the exact sequence (5.1.2) of [GLO, Prop. 4.3.7, Cor. 4.3.8],
the cohomological identity (5.1.3) `φ_{G_R} = τ φ_G τ`, the GRR formula for `ch(F ∗ G)`, and in
Remark 5.2.3 the fact `ch(F^∨) = τ(ch(F))`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section OneVariety

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- **(5.2.1)** (`eq-m-dagger`) `m†_g = τ m_g τ` (the foundation's `mDagger`, defined on all of
`C(V)`). -/
theorem equation5_2_1 (g : Spin F n) :
    mDagger F n (g : C F n) = tau F n ∘ₗ m F n (g : C F n) ∘ₗ tau F n := rfl

omit [CharZero F] in
/-- (5.2.1) `m† : Spin(V) → GL(S)` is a homomorphism (`τ² = 1`). -/
theorem mDagger_mul (x y : C F n) : mDagger F n (x * y) = mDagger F n x ∘ₗ mDagger F n y := by
  refine LinearMap.ext fun s => ?_
  simp [mDagger, map_mul, tau_tau]

omit [CharZero F] in
theorem mDagger_one : mDagger F n 1 = LinearMap.id := by
  refine LinearMap.ext fun s => ?_
  simp [mDagger, tau_tau]

/-- The `Spin(V)`-invariance of the Mukai pairing (1.2.3) (§1.2), from [Chevalley, III.2.1]:
an element `g` of `Spin(V_F)` lies in the Clifford group and has norm `g τ(g) = g g* = 1`. -/
theorem s23_mukai_m_spin (g : Spin F n) (s t : S F n) :
    mukai F n (m F n (g : C F n) s) (m F n (g : C F n) t) = mukai F n s t := by
  have hx : spinGroup.toUnits g ∈ cliffordGroup F n := fun v =>
    ⟨rho F n g v, by
      rw [ι_rho]
      rfl⟩
  have hc : ((spinGroup.toUnits g : (C F n)ˣ) : C F n) *
      reverse ((spinGroup.toUnits g : (C F n)ˣ) : C F n) = algebraMap F (C F n) 1 := by
    have hrev : reverse (g : C F n) = star (g : C F n) := by
      rw [star_def, spinGroup.involute_eq g.2]
    change (g : C F n) * reverse (g : C F n) = _
    rw [hrev, spinGroup.mul_star_self_of_mem g.2, map_one]
  simpa using chevalley_III_2_1 F n (spinGroup.toUnits g) hx 1 hc s t

/-- **(5.2.2)** (`eq-invariance-of-Poincare-pairing`)
`∫_X m†_g(s) ∪ m_g(t) = (m_g(τ(s)), m_g(t))_S = (τ(s), t)_S = ∫_X s ∪ t`
for all `s, t ∈ S` and `g ∈ Spin(V)` (the second equality is the `Spin(V)`-invariance of the Mukai
pairing (1.2.3)). -/
theorem equation5_2_2 (g : Spin F n) (s t : S F n) :
    integral F n (mDagger F n (g : C F n) s * m F n (g : C F n) t) =
        mukai F n (m F n (g : C F n) (tau F n s)) (m F n (g : C F n) t) ∧
      mukai F n (m F n (g : C F n) (tau F n s)) (m F n (g : C F n) t) = mukai F n (tau F n s) t ∧
      mukai F n (tau F n s) t = integral F n (s * t) := by
  refine ⟨rfl, s23_mukai_m_spin F n g _ _, ?_⟩
  simp [mukai, tau_tau]

/-! ### Parity (used in the proof of (5.2.3)) -/

omit [CharZero F] in
/-- `m_g` preserves the parity of a class, for `g ∈ Spin(V)` (an even element of `C(V)`): the
grading involution of `S` commutes with `m_x` up to the grading involution of `x`. -/
private theorem involute_m (x : C F n) (s : S F n) :
    involute (m F n x s) = m F n (involute x) (involute s) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r => simp [Algebra.smul_def]
  | ι v =>
    obtain ⟨θ, w⟩ := v
    simp only [m, lift_ι_apply, involute_ι, map_neg, cliffordOp, L, D, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.mul_apply',
      LinearMap.neg_apply, map_add, map_mul, involute_contractLeft]
    have hι : (ExteriorAlgebra.ι F w : S F n) =
        CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w := rfl
    rw [hι]
    simp only [neg_mul]
    abel
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- A class fixed (resp. negated) by the grading involution is even (resp. odd). -/
private theorem mem_evenOdd_zero_of_involute {M : Type*} [AddCommGroup M] [Module F M]
    {Q : QuadraticForm F M} {x : CliffordAlgebra Q} (hx : involute x = x) : x ∈ evenOdd Q 0 := by
  have hmem : x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [(evenOdd_isCompl Q).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  rw [map_add, involute_eq_of_mem_even ha, involute_eq_of_mem_odd hb] at hx
  have hb0 : b = 0 := by
    have h2 : (2 : F) • b = (a + b) - (a + -b) := by rw [two_smul]; abel
    rw [← hx, sub_self] at h2
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hb0, add_zero]
  exact ha

private theorem mem_evenOdd_one_of_involute {M : Type*} [AddCommGroup M] [Module F M]
    {Q : QuadraticForm F M} {x : CliffordAlgebra Q} (hx : involute x = -x) :
    x ∈ evenOdd Q 1 := by
  have hmem : x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [(evenOdd_isCompl Q).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  rw [map_add, involute_eq_of_mem_even ha, involute_eq_of_mem_odd hb] at hx
  have ha0 : a = 0 := by
    have h2 : (2 : F) • a = (a + -b) + (a + b) := by rw [two_smul]; abel
    rw [hx, neg_add_cancel] at h2
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [ha0, zero_add]
  exact hb

private theorem m_spin_mem_evenOdd (g : Spin F n) {i : ZMod 2} {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    m F n (g : C F n) s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i := by
  have hg : involute (g : C F n) = g := spinGroup.involute_eq g.2
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
  · apply mem_evenOdd_zero_of_involute F
    rw [involute_m, hg, involute_eq_of_mem_even hs]
  · apply mem_evenOdd_one_of_involute F
    rw [involute_m, hg, involute_eq_of_mem_odd hs, map_neg]

omit [CharZero F] in
private theorem tau_mem_evenOdd {i : ZMod 2} {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    tau F n s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i :=
  (reverse_mem_evenOdd_iff _).2 hs

private theorem mDagger_spin_mem_evenOdd (g : Spin F n) {i : ZMod 2} {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    mDagger F n (g : C F n) s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i :=
  tau_mem_evenOdd F n (m_spin_mem_evenOdd F n g (tau_mem_evenOdd F n hs))

omit [CharZero F] in
private theorem coe_mul_coe_inv (h : Spin F n) :
    (h : C F n) * ((h⁻¹ : Spin F n) : C F n) = 1 := by
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]

omit [CharZero F] in
private theorem coe_inv_mul_coe (h : Spin F n) :
    ((h⁻¹ : Spin F n) : C F n) * (h : C F n) = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]

omit [CharZero F] in
private theorem mem_even_or_odd (s : S F n) :
    ∃ s₀ ∈ Splus F n, ∃ s₁ ∈ Sminus F n, s = s₀ + s₁ := by
  have hmem : s ∈ Splus F n ⊔ Sminus F n := by
    rw [Splus, Sminus, (evenOdd_isCompl _).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  exact ⟨a, ha, b, hb, rfl⟩

/-- **(5.2.3)** (`eq-second-invariance-of-Poincare-pairing`)
`∫_X m_g(s) ∪ m†_g(t) = ∫_X s ∪ t` for all `s, t ∈ H*(X)` and `g ∈ Spin(V)`. -/
theorem equation5_2_3 (g : Spin F n) (s t : S F n) :
    integral F n (m F n (g : C F n) s * mDagger F n (g : C F n) t) = integral F n (s * t) := by
  -- The paper's case distinction according to the parities of `s` and `t`.
  obtain ⟨s₀, hs₀, s₁, hs₁, rfl⟩ := mem_even_or_odd F n s
  obtain ⟨t₀, ht₀, t₁, ht₁, rfl⟩ := mem_even_or_odd F n t
  have h22 : ∀ a b : S F n,
      integral F n (mDagger F n (g : C F n) a * m F n (g : C F n) b) = integral F n (a * b) :=
    fun a b => (equation5_2_2 F n g a b).1.trans
      ((equation5_2_2 F n g a b).2.1.trans (equation5_2_2 F n g a b).2.2)
  -- both even: the Poincaré pairing is symmetric on even classes
  have hee : integral F n (m F n (g : C F n) s₀ * mDagger F n (g : C F n) t₀) =
      integral F n (s₀ * t₀) := by
    rw [s23_mul_comm_of_mem_even (m_spin_mem_evenOdd F n g hs₀), h22,
      s23_mul_comm_of_mem_even ht₀]
  -- both odd: the Poincaré pairing is antisymmetric on odd classes
  have hoo : integral F n (m F n (g : C F n) s₁ * mDagger F n (g : C F n) t₁) =
      integral F n (s₁ * t₁) := by
    rw [s23_mul_eq_involute_mul_of_mem_odd (m_spin_mem_evenOdd F n g hs₁),
      involute_eq_of_mem_odd (mDagger_spin_mem_evenOdd F n g ht₁), neg_mul, map_neg, h22,
      s23_mul_eq_involute_mul_of_mem_odd ht₁, involute_eq_of_mem_odd hs₁, neg_mul, map_neg,
      neg_neg]
  -- mixed parities: both sides vanish
  have hodd : ∀ {a b : S F n}, a ∈ Splus F n → b ∈ Sminus F n →
      integral F n (a * b) = 0 ∧ integral F n (b * a) = 0 := by
    intro a b ha hb
    refine ⟨s23_integral_of_mem_odd F n ?_, s23_integral_of_mem_odd F n ?_⟩
    · have h := SetLike.mul_mem_graded ha hb
      rw [zero_add] at h
      exact h
    · have h := SetLike.mul_mem_graded hb ha
      rw [add_zero] at h
      exact h
  have heo : integral F n (m F n (g : C F n) s₀ * mDagger F n (g : C F n) t₁) =
      integral F n (s₀ * t₁) := by
    rw [(hodd (m_spin_mem_evenOdd F n g hs₀) (mDagger_spin_mem_evenOdd F n g ht₁)).1,
      (hodd hs₀ ht₁).1]
  have hoe : integral F n (m F n (g : C F n) s₁ * mDagger F n (g : C F n) t₀) =
      integral F n (s₁ * t₀) := by
    rw [(hodd (mDagger_spin_mem_evenOdd F n g ht₀) (m_spin_mem_evenOdd F n g hs₁)).2,
      (hodd ht₀ hs₁).2]
  simp only [map_add, add_mul, mul_add]
  rw [hee, hoo, heo, hoe]

/-- (§5.2, TeX line 2049) `PD(m_h(s)) = PD(s) ∘ m†_{h⁻¹}` for all `h ∈ Spin(V)`, where
`PD(s) = ∫_X (• ∪ s)`. -/
theorem PD_m (h : Spin F n) (s : S F n) :
    PD F n (m F n (h : C F n) s) = PD F n s ∘ₗ mDagger F n ((h⁻¹ : Spin F n) : C F n) := by
  refine LinearMap.ext fun r => ?_
  -- (5.2.2) for `g = h`, applied to `m†_{h⁻¹}(r)` and `s`
  have h22 := (equation5_2_2 F n h (mDagger F n ((h⁻¹ : Spin F n) : C F n) r) s)
  have hr : mDagger F n (h : C F n) (mDagger F n ((h⁻¹ : Spin F n) : C F n) r) = r := by
    rw [← LinearMap.comp_apply, ← mDagger_mul, coe_mul_coe_inv, mDagger_one, LinearMap.id_apply]
  rw [hr] at h22
  simp only [PD, pdOf_apply, LinearMap.comp_apply]
  exact h22.1.trans (h22.2.1.trans h22.2.2)

/-- `PD(m†_h(s)) = PD(s) ∘ m_{h⁻¹}`, the analogue of `PD_m` given by (5.2.3) (used for (5.2.4)). -/
private theorem PD_mDagger (h : Spin F n) (s : S F n) :
    PD F n (mDagger F n (h : C F n) s) = PD F n s ∘ₗ m F n ((h⁻¹ : Spin F n) : C F n) := by
  refine LinearMap.ext fun r => ?_
  have h23 := equation5_2_3 F n h (m F n ((h⁻¹ : Spin F n) : C F n) r) s
  have hr : m F n (h : C F n) (m F n ((h⁻¹ : Spin F n) : C F n) r) = r := by
    rw [← Module.End.mul_apply, ← map_mul, coe_mul_coe_inv, map_one, Module.End.one_apply]
  rw [hr] at h23
  simp only [PD, pdOf_apply, LinearMap.comp_apply]
  exact h23

set_option linter.unusedVariables false in
omit [CharZero F] in
/-- **Remark 5.2.3** (`rem-invariance-of-w-vee`), the cohomological claim: for `w ∈ S⁺`, the class
`w^∨ = τ(w)` is `Spin(V)_w`-invariant with respect to the `m†`-action. (The geometric input, that
`τ(ch(F)) = ch(F^∨)` for an object `F` of `Dᵇ(X)`, is left out.) -/
theorem remark5_2_3 (w : S F n) (hw : w ∈ Splus F n) (g : Spin F n) (hg : m F n (g : C F n) w = w) :
    mDagger F n (g : C F n) (tau F n w) = tau F n w := by
  simp only [mDagger, LinearMap.comp_apply, tau_tau, hg]

end OneVariety

/-! ### Correspondences -/

section CorrGeneric

/-- `[(1 ⊗ f)(γ)]_* = f ∘ γ_*` ("evident", proof of Lemma 5.2.1). -/
private theorem corr_map_id_left {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A]
    [AddCommGroup B] [Module F B] (intA : A →ₗ[F] F) (f : B →ₗ[F] B) (γ : A ⊗[F] B) :
    corr intA (TensorProduct.map LinearMap.id f γ) = f ∘ₗ corr intA γ := by
  induction γ using TensorProduct.inductionOn with
  | tmul u v =>
    refine LinearMap.ext fun s => ?_
    simp [corr_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.comp_add]

/-- `[(f ⊗ 1)(γ)]_* = γ_* ∘ f'` when `PD(f(u)) = PD(u) ∘ f'` for all `u` (proof of
Lemma 5.2.1, with `γ = Σ aᵢⱼ uᵢ ⊗ vⱼ` and `γ_* = Σ aᵢⱼ PD(uᵢ) ⊗ vⱼ`). -/
private theorem corr_map_id_right {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A]
    [AddCommGroup B] [Module F B] (intA : A →ₗ[F] F) (f f' : A →ₗ[F] A)
    (hf : ∀ u, pdOf intA (f u) = pdOf intA u ∘ₗ f') (γ : A ⊗[F] B) :
    corr intA (TensorProduct.map f LinearMap.id γ) = corr intA γ ∘ₗ f' := by
  induction γ using TensorProduct.inductionOn with
  | tmul u v =>
    refine LinearMap.ext fun s => ?_
    have := congrArg (fun φ : Module.Dual F A => φ s) (hf u)
    simp only [pdOf_apply, LinearMap.comp_apply] at this
    simp [corr_tmul, this]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp]

end CorrGeneric

section Correspondences

variable (F : Type*) [Field F] [CharZero F] (nX nY nZ : ℕ)

/-- **Lemma 5.2.1** (`lemma-action-of-m-h-tensor-1`), first equality: for `γ ∈ H*(X × Y)`,
`h ∈ Spin(V_X)` and `g ∈ Spin(V_Y)`, `[(m_h ⊗ m†_g)(γ)]_* = m†_g ∘ γ_* ∘ m†_{h⁻¹}`. -/
theorem lemma5_2_1_1 (h : Spin F nX) (g : Spin F nY) (γ : S F nX ⊗[F] S F nY) :
    corr (integral F nX) (TensorProduct.map (m F nX (h : C F nX)) (mDagger F nY (g : C F nY)) γ) =
      mDagger F nY (g : C F nY) ∘ₗ corr (integral F nX) γ ∘ₗ
        mDagger F nX ((h⁻¹ : Spin F nX) : C F nX) := by
  -- `(m_h ⊗ m†_g) = (1 ⊗ m†_g) ∘ (m_h ⊗ 1)`
  have hsplit : TensorProduct.map (m F nX (h : C F nX)) (mDagger F nY (g : C F nY)) γ =
      TensorProduct.map LinearMap.id (mDagger F nY (g : C F nY))
        (TensorProduct.map (m F nX (h : C F nX)) LinearMap.id γ) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  rw [hsplit, corr_map_id_left,
    corr_map_id_right _ _ (mDagger F nX ((h⁻¹ : Spin F nX) : C F nX)) (PD_m F nX h)]

/-- **Lemma 5.2.1** (`lemma-action-of-m-h-tensor-1`), second equality **(5.2.4)**
(`eq-equivariance-of-mapping-correspondence-to-homomorphism`): for `γ ∈ H*(X × Y)`,
`h ∈ Spin(V_X)` and `g ∈ Spin(V_Y)`, `[(m†_h ⊗ m_g)(γ)]_* = m_g ∘ γ_* ∘ m_{h⁻¹}`. -/
theorem lemma5_2_1_2 (h : Spin F nX) (g : Spin F nY) (γ : S F nX ⊗[F] S F nY) :
    corr (integral F nX) (TensorProduct.map (mDagger F nX (h : C F nX)) (m F nY (g : C F nY)) γ) =
      m F nY (g : C F nY) ∘ₗ corr (integral F nX) γ ∘ₗ m F nX ((h⁻¹ : Spin F nX) : C F nX) := by
  have hsplit : TensorProduct.map (mDagger F nX (h : C F nX)) (m F nY (g : C F nY)) γ =
      TensorProduct.map LinearMap.id (m F nY (g : C F nY))
        (TensorProduct.map (mDagger F nX (h : C F nX)) LinearMap.id γ) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  rw [hsplit, corr_map_id_left,
    corr_map_id_right _ _ (m F nX ((h⁻¹ : Spin F nX) : C F nX)) (PD_mDagger F nX h)]

/-- **Corollary 5.2.2** (`cor-Spin-V-Y-invariance`), first equality: for `γ ∈ H*(X × Y)`,
`δ ∈ H*(Y × Z)` and `h ∈ Spin(V_Y)`, `[(m_h ⊗ 1)(δ)]_* ∘ [(1 ⊗ m†_h)(γ)]_* = δ_* ∘ γ_*`. -/
theorem corollary5_2_2_1 (h : Spin F nY) (γ : S F nX ⊗[F] S F nY) (δ : S F nY ⊗[F] S F nZ) :
    corr (integral F nY) (TensorProduct.map (m F nY (h : C F nY)) LinearMap.id δ) ∘ₗ
        corr (integral F nX) (TensorProduct.map LinearMap.id (mDagger F nY (h : C F nY)) γ) =
      corr (integral F nY) δ ∘ₗ corr (integral F nX) γ := by
  -- Lemma 5.2.1 with `g = 1` (for `δ`) and with `h = 1` (for `γ`).
  have hδ := lemma5_2_1_1 F nY nZ h 1 δ
  have hγ := lemma5_2_1_1 F nX nY 1 h γ
  simp only [OneMemClass.coe_one, inv_one, mDagger_one, map_one, Module.End.one_eq_id] at hδ hγ
  rw [hδ, hγ]
  refine LinearMap.ext fun s => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← LinearMap.comp_apply (mDagger F nY ((h⁻¹ : Spin F nY) : C F nY)), ← mDagger_mul,
    coe_inv_mul_coe, mDagger_one, LinearMap.id_apply]

/-- **Corollary 5.2.2** (`cor-Spin-V-Y-invariance`), second equality: for `γ ∈ H*(X × Y)`,
`δ ∈ H*(Y × Z)` and `h ∈ Spin(V_Y)`, `[(m†_h ⊗ 1)(δ)]_* ∘ [(1 ⊗ m_h)(γ)]_* = δ_* ∘ γ_*`. -/
theorem corollary5_2_2_2 (h : Spin F nY) (γ : S F nX ⊗[F] S F nY) (δ : S F nY ⊗[F] S F nZ) :
    corr (integral F nY) (TensorProduct.map (mDagger F nY (h : C F nY)) LinearMap.id δ) ∘ₗ
        corr (integral F nX) (TensorProduct.map LinearMap.id (m F nY (h : C F nY)) γ) =
      corr (integral F nY) δ ∘ₗ corr (integral F nX) γ := by
  -- (5.2.4) with `g = 1` (for `δ`) and with `h = 1` (for `γ`).
  have hδ := lemma5_2_1_2 F nY nZ h 1 δ
  have hγ := lemma5_2_1_2 F nX nY 1 h γ
  simp only [OneMemClass.coe_one, inv_one, mDagger_one, map_one, Module.End.one_eq_id] at hδ hγ
  rw [hδ, hγ]
  refine LinearMap.ext fun s => ?_
  simp only [LinearMap.comp_apply]
  rw [← Module.End.mul_apply (m F nY ((h⁻¹ : Spin F nY) : C F nY)), ← map_mul,
    coe_inv_mul_coe, map_one, Module.End.one_apply, LinearMap.id_apply, LinearMap.id_apply]

end Correspondences

end WeilClasses
