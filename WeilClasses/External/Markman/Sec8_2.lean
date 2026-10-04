module

public import WeilClasses.Secant.Sec8_1
import WeilClasses.External.Chevalley.Sec2_1

/-!
# Markman [M2], Proposition 1.7, as used in Example 8.2.2

[M2] E. Markman, *The monodromy of generalized Kummer varieties and algebraic cycles on their
intermediate Jacobians*, J. Eur. Math. Soc. (JEMS) 25 (2023), no. 1, 231–321 (arXiv:1805.11574;
the paper's reference `markman-generalized-kummers`), Proposition 1.7 (= Proposition 12.6 and
Corollary 12.9 there).

**The result in [M2].** `X` is an abelian surface, `V = H¹(X, ℤ) ⊕ H¹(X, ℤ)^*`,
`S⁺ = H^{ev}(X, ℤ)` with minus the Mukai pairing (unimodular, of signature `(4, 4)`), and `w ∈ S⁺`
is the Chern character of the ideal sheaf of a subscheme of length `n + 1`, `n ≥ 2`. If `h ∈ S⁺`
satisfies `(h, w) = 0` and `(h, h) < 0`, and `d := (w, w)(h, h)/4`, then the universal torus over the
periods orthogonal to `w` and `h` is a complete family of polarized abelian fourfolds of Weil type of
discriminant `1` with complex multiplication by `ℚ(√-d)`. There the complex multiplication is
`m_w m_h`, whose square on `V` is `-(w, w)(h, h)/4 = -d` (`V ⊕ S⁻` is a module over `C(S⁺)`,
triality for `Spin(8)`).

**The form used here.** Example 8.2.2 (TeX lines 3773–3775): "Then `span_ℚ{w, h}` is a secant to
the spinor variety inducing complex multiplication by the imaginary quadratic number field
`ℚ(√-d)`, where `d = (w, w)(h, h)/4`, by [M2, Prop. 1.7]". This is the special case stated here
(`markmanM2_prop1_7`): for `w, h ∈ S⁺_ℚ` with `(w, w)_S < 0`, `(h, h)_S < 0` and `(w, h)_S = 0`,
`span_ℚ{w, h}` is the rational plane of a `K`-secant (`KSecant`), `K = ℚ(√-d)`. Only the
cohomological core of Prop. 1.7 is used (the line `ℙ(span{w, h})` meets the spinor variety in two
conjugate points defined over `ℚ(√-d)`), for any rational `w` with `(w, w)_S < 0` in place of
`ch(I_Z)`; the family of abelian fourfolds plays no role. The paper's pairing
`(x, y)_S = ∫_X τ(x) y` (`mukai`) is the pairing of [M2] (`τ` is `-1` on `H²` and `1` on `H⁰ ⊕ H⁴`,
so it is minus the Mukai pairing), and the sign conditions are those of [M2].

**Proof.** For `n = 2` the even pure spinors are exactly the non-zero isotropic vectors of `S⁺`
(`s8_isEvenPureSpinor_two`): an isotropic `u = a + ω + b[pt]` with `a ≠ 0` is `a exp(ω/a)`
(`(u, u)_S = 2ab - ∫ω²`), whose annihilator is `ρ(exp(jω/a))(H¹(X̂) × 0)`; if `a = 0` and
`ω ≠ 0`, an Eichler transvection `s ↦ s + D_{y'} D_y s` in `Spin(V)` makes the degree-`0` part
non-zero; if `a = ω = 0`, then `ker m_{[pt]} = 0 × H¹(X)`. The vector `u₁ = w + c h`,
`c = 2√-d/(h, h)_S`, is isotropic (`(u₁, u₁)_S = (w, w)_S + c² (h, h)_S = 0`), hence a pure
spinor; `u₂ = σ(u₁) = w - c h` is independent of `u₁` because `w` and `h` are (their Gram matrix is
`diag((w, w)_S, (h, h)_S)`); and the rational points of `span_K{u₁, u₂} = span_K{w, h}` are
`span_ℚ{w, h}`. The proof uses no result of the paper: only helpers of `WeilClasses.Secant.Defs` and
`WeilClasses.Secant.Sec8_1`, and [Chevalley, III.2.2] (`chevalley_III_2_2`: `D_z` is self-adjoint
for the Mukai pairing).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## For `n = 2`, isotropic even spinors are pure (helpers, prefix `s8_`)

An isotropic `u = a + ω + b[pt] ∈ S⁺` with `a ≠ 0` is `a exp(ω/a)` (`(u, u)_S = 2ab - ∫ω²`), whose
annihilator is `ρ(exp(jω/a))(H¹(X̂) × 0)`; if `a = 0` and `ω ≠ 0`, an Eichler transvection
`s ↦ s + D_{y'} D_y s` in `Spin(V)` makes the degree-`0` part nonzero; if `a = ω = 0`,
`ker m_{[pt]} = 0 × H¹(X)`. -/

section S8Pure

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- Vectors killing a nonzero spinor are isotropic (`m_v² = Q(v)`). -/
theorem s8_Q_of_mem_ann {s : S F n} (hs : s ≠ 0) {v : V F n} (hv : v ∈ ann F n s) :
    Q F n v = 0 := by
  have h1 : mOf F n s v = 0 := hv
  have h2 : cliffordOp F n v (cliffordOp F n v s) = Q F n v • s := by
    rw [← Module.End.mul_apply, cliffordOp_mul_self, Module.algebraMap_end_apply]
  have h3 : cliffordOp F n v s = mOf F n s v := by
    simp [mOf, m]
  rw [h3, h1, map_zero] at h2
  exact (smul_eq_zero.mp h2.symm).resolve_right hs

/-- `ker m_{c s} = ker m_s` for `c ≠ 0`. -/
theorem s8_ann_smul {c : F} (hc : c ≠ 0) (s : S F n) : ann F n (c • s) = ann F n s := by
  ext v
  rw [s8_mem_ann_iff, s8_mem_ann_iff, mul_smul_comm, map_smul, ← smul_add, smul_eq_zero,
    or_iff_right hc]

/-- `ker m_1 = H¹(X̂) × 0`. -/
theorem s8_ann_one_eq :
    ann F n 1 = LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) := by
  ext ⟨y, x⟩
  rw [s8_mem_ann_iff, LinearMap.mem_range]
  simp only [mul_one, D, CliffordAlgebra.contractLeft_one, add_zero, LinearMap.inl_apply,
    Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨y, rfl, ((ExteriorAlgebra.ι_inj F x 0).mp (by rw [h, map_zero])).symm⟩
  · rintro ⟨y', -, rfl⟩
    exact map_zero _

theorem s8_finrank_ann_one : Module.finrank F (ann F n 1) = 2 * n := by
  rw [s8_ann_one_eq, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    Subspace.dual_finrank_eq, Module.finrank_fin_fun]

/-- `dim ker m_{g s} = dim ker m_s` for `g ∈ Spin(V)` (`WeilClasses.ann_m_spin`). -/
theorem s8_finrank_ann_m (g : Spin F n) (s : S F n) :
    Module.finrank F (ann F n (m F n (g : C F n) s)) = Module.finrank F (ann F n s) := by
  rw [ann_m_spin]
  exact LinearEquiv.finrank_map_eq (rho F n g) (ann F n s)

/-- `exp(ω)` (`ω ∈ ⋀²`) is a pure spinor: `exp(ω) = m_{exp(jω)}(1)`. -/
theorem s8_finrank_ann_exp {ω : S F n} (hω : ω ∈ ⋀[F]^2 (H1 F n)) :
    Module.finrank F (ann F n (IsNilpotent.exp ω)) = 2 * n := by
  have h := s8_finrank_ann_m (s8_expSpin ω hω) 1
  rw [s8_m_expSpin, mul_one, s8_finrank_ann_one] at h
  exact h

theorem s8_ι_mul_pt (x : H1 F n) : ExteriorAlgebra.ι F x * pt F n = 0 :=
  s8_mem_bot_of_lt F n (by omega : 2 * n < 1 + 2 * n)
    (SetLike.mul_mem_graded (by simp : ExteriorAlgebra.ι F x ∈ ⋀[F]^1 (H1 F n)) (s8_pt_mem F n))

/-- `y ⌋ [pt] = 0` only for `y = 0`: `x ∧ (y ⌋ [pt]) = y(x) [pt]`. -/
theorem s8_eq_zero_of_D_pt {y : Module.Dual F (H1 F n)} (h : D F n y (pt F n) = 0) : y = 0 := by
  refine LinearMap.ext fun x => ?_
  have h2 := congrArg (D F n y) (s8_ι_mul_pt x)
  rw [D, contractLeft_ι_mul] at h2
  change y x • pt F n - ExteriorAlgebra.ι F x * D F n y (pt F n) = _ at h2
  rw [h, mul_zero, sub_zero, map_zero] at h2
  have hpt : pt F n ≠ 0 := (basisS F n).ne_zero _
  simpa using (smul_eq_zero.mp h2).resolve_right hpt

/-- `ker m_{[pt]} = 0 × H¹(X)`. -/
theorem s8_ann_pt_eq :
    ann F n (pt F n) = LinearMap.range (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) := by
  ext ⟨y, x⟩
  rw [s8_mem_ann_iff, LinearMap.mem_range]
  simp only [s8_ι_mul_pt, zero_add, LinearMap.inr_apply, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨x, (s8_eq_zero_of_D_pt h).symm, rfl⟩
  · rintro ⟨x', rfl, -⟩
    simp [D]

theorem s8_finrank_ann_pt : Module.finrank F (ann F n (pt F n)) = 2 * n := by
  rw [s8_ann_pt_eq, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
    Module.finrank_fin_fun]

omit [CharZero F] in
/-- `⋀^k ⊆ S⁺` for `k` even. -/
theorem s8_mem_Splus_of_mem {k : ℕ} (hk : Even k) {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n)) :
    x ∈ Splus F n :=
  Submodule.mem_iSup_of_mem (⟨k, (ZMod.natCast_eq_zero_iff_even).mpr hk⟩ :
    { j : ℕ // (j : ZMod 2) = 0 }) hx

omit [CharZero F] in
/-- The odd graded pieces of an even spinor vanish. -/
theorem s8_proj_odd_eq_zero {u : S F n} (hu : u ∈ Splus F n) {k : ℕ} (hk : Odd k) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k u = 0 := by
  refine Submodule.iSup_induction
    (motive := fun x => GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) k x = 0) _ hu ?_ ?_ ?_
  · rintro ⟨j, hj⟩ x hx
    have hx' : x ∈ ⋀[F]^j (H1 F n) := hx
    rw [s8_proj_of_mem hx', ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hk) ((ZMod.natCast_eq_zero_iff_even).mp hj)
  · simp
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

omit [CharZero F] in
theorem s8_proj_zero_eq (u : S F n) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) 0 u =
      algebraMap F (S F n) (ExteriorAlgebra.algebraMapInv u) := by
  rw [s8_eq_algebraMap_of_mem_zero (s8_proj_mem u 0)]
  congr 1
  conv_rhs => rw [s8_eq_sum_proj u]
  rw [map_sum, Finset.sum_eq_single 0]
  · intro k _ hk
    exact s8_algebraMapInv_eq_zero_of_mem (Nat.pos_of_ne_zero hk) (s8_proj_mem u k)
  · simp

omit [CharZero F] in
theorem s8_proj_top_eq (u : S F n) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F n)) (2 * n) u = integral F n u • pt F n := by
  rw [s8_eq_smul_pt_of_mem (s8_proj_mem u (2 * n))]
  congr 1
  conv_rhs => rw [s8_eq_sum_proj u]
  rw [map_sum, Finset.sum_eq_single (2 * n)]
  · intro k _ hk
    exact s8_integral_eq_zero_of_mem F n hk (s8_proj_mem u k)
  · simp

/-- `m_{(z, 0)} = D_z`. -/
theorem s8_m_ι_inl (z : Module.Dual F (H1 F n)) (t : S F n) :
    m F n (ι (Q F n) ((z, 0) : V F n)) t = D F n z t := by
  simp [m, cliffordOp, L]

/-- The Eichler transvection `1 + ι(y', 0) ι(y, 0) ∈ Spin(V)` acts on `S` by `s ↦ s + D_{y'} D_y s`. -/
theorem s8_exists_spin_DD (y y' : Module.Dual F (H1 F n)) :
    ∃ g : Spin F n, ∀ s, m F n (g : C F n) s = s + D F n y' (D F n y s) := by
  have hu : Q F n ((y, 0) : V F n) = 0 := by simp [Q]
  have huw : QuadraticMap.polar (Q F n) ((y, 0) : V F n) ((y', 0) : V F n) = 0 := by
    rw [s8_polar_Q]; simp
  refine ⟨CliffordAlgebra.spinTransvection s8_Q_nondegenerate hu huw, fun s => ?_⟩
  rw [CliffordAlgebra.coe_spinTransvection, map_add, map_one, map_mul, LinearMap.add_apply,
    Module.End.one_apply, Module.End.mul_apply, s8_m_ι_inl, s8_m_ι_inl]

/-- `s ↦ s + D_{y'} D_y s` preserves the Mukai pairing ([Chevalley, III.2.2]: `D_z` is
self-adjoint; `D_y D_{y'} = -D_{y'} D_y`, `D_{y'}² = 0`). -/
theorem s8_mukai_DD (y y' : Module.Dual F (H1 F n)) (s t : S F n) :
    mukai F n (s + D F n y' (D F n y s)) (t + D F n y' (D F n y t)) = mukai F n s t := by
  have hadj : ∀ (z : Module.Dual F (H1 F n)) (p q : S F n),
      mukai F n (D F n z p) q = mukai F n p (D F n z q) := by
    intro z p q
    have := chevalley_III_2_2 F n ((z, 0) : V F n) p q
    rwa [s8_m_ι_inl, s8_m_ι_inl] at this
  have h1 : mukai F n (D F n y' (D F n y s)) t = -mukai F n s (D F n y' (D F n y t)) := by
    rw [hadj y', hadj y, ← map_neg]
    congr 1
    exact contractLeft_comm _ _ _
  have h2 : mukai F n (D F n y' (D F n y s)) (D F n y' (D F n y t)) = 0 := by
    rw [hadj y']
    have : D F n y' (D F n y' (D F n y t)) = 0 := contractLeft_contractLeft _ _
    rw [this, map_zero]
  simp only [map_add, LinearMap.add_apply, h1, h2]
  ring

/-- A nonzero `ω ∈ ⋀²` has a nonzero double contraction `⟪ω, y ∧ y'⟫`. -/
theorem s8_exists_DD_ne_zero {ω : S F n} (hω : ω ∈ ⋀[F]^2 (H1 F n)) (h0 : ω ≠ 0) :
    ∃ y y' : Module.Dual F (H1 F n), ExteriorAlgebra.algebraMapInv (D F n y' (D F n y ω)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  refine s8_eq_zero_of_contractLeft (Pi.basisFun F (Fin (2 * n))) (by norm_num : 0 < 2) hω
    fun y => ?_
  have hDy : contractLeft (Q := 0) y ω ∈ ⋀[F]^1 (H1 F n) := s8_contractLeft_mem y hω
  refine s8_eq_zero_of_contractLeft (Pi.basisFun F (Fin (2 * n))) (by norm_num : 0 < 1) hDy
    fun y' => ?_
  have hDDy : contractLeft (Q := 0) y' (contractLeft (Q := 0) y ω) ∈ ⋀[F]^0 (H1 F n) :=
    s8_contractLeft_mem y' hDy
  rw [s8_eq_algebraMap_of_mem_zero hDDy]
  have := hcon y y'
  change ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) y' (contractLeft (Q := 0) y ω)) = 0
    at this
  rw [this, map_zero]

end S8Pure

section S8PureTwo

variable {F : Type*} [Field F] [CharZero F]

/-- `τ[pt] = [pt]` for `n = 2` (`[pt] = Θ²/2`, `τ(Θ) = -Θ`). -/
theorem s8_tau_pt_two : tau F 2 (pt F 2) = pt F 2 := by
  have hT := s8_ThetaStd_mem F 2
  have h2 : tau F 2 (ThetaStd F 2 ^ 2) = ThetaStd F 2 ^ 2 := by rw [s8_tau_pow F 2 hT, neg_sq]
  rw [ThetaStd_pow, map_smul] at h2
  exact smul_right_injective _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 2)) h2

omit [CharZero F] in
/-- For `n = 2` an even spinor is `a + ω + b [pt]`. -/
theorem s8_Splus_two {u : S F 2} (hu : u ∈ Splus F 2) :
    u = algebraMap F (S F 2) (ExteriorAlgebra.algebraMapInv u) +
      GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u + integral F 2 u • pt F 2 := by
  have h := s8_eq_sum_proj u
  have h4 := s8_proj_top_eq (n := 2) u
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [s8_proj_odd_eq_zero hu (by decide : Odd 1), s8_proj_odd_eq_zero hu (by decide : Odd 3),
    s8_proj_zero_eq, h4, add_zero, add_zero] at h
  exact h

/-- `(a + ω + b[pt], a + ω + b[pt])_S = 2ab - ∫ω²` (`n = 2`). -/
theorem s8_mukai_two (a b : F) {ω : S F 2} (hω : ω ∈ ⋀[F]^2 (H1 F 2)) :
    mukai F 2 (algebraMap F (S F 2) a + ω + b • pt F 2)
        (algebraMap F (S F 2) a + ω + b • pt F 2) =
      2 * a * b - integral F 2 (ω * ω) := by
  have hωω : ω * ω = integral F 2 (ω * ω) • pt F 2 :=
    s8_eq_smul_pt_of_mem (SetLike.mul_mem_graded hω hω)
  have hωpt : ω * pt F 2 = 0 :=
    s8_mem_bot_of_lt F 2 (by norm_num) (SetLike.mul_mem_graded hω (s8_pt_mem F 2))
  have hptω : pt F 2 * ω = 0 :=
    s8_mem_bot_of_lt F 2 (by norm_num) (SetLike.mul_mem_graded (s8_pt_mem F 2) hω)
  have hptpt : pt F 2 * pt F 2 = 0 :=
    s8_mem_bot_of_lt F 2 (by norm_num) (SetLike.mul_mem_graded (s8_pt_mem F 2) (s8_pt_mem F 2))
  have h1 : integral F 2 (1 : S F 2) = 0 :=
    s8_integral_eq_zero_of_mem F 2 (by norm_num) (by simp : (1 : S F 2) ∈ ⋀[F]^0 (H1 F 2))
  have hω0 : integral F 2 ω = 0 := s8_integral_eq_zero_of_mem F 2 (by norm_num) hω
  simp only [mukai, LinearMap.compr₂_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul_apply']
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [map_add, map_smul, s8_tau_one, s8_tau_of_mem_two F 2 hω, s8_tau_pt_two]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, neg_mul,
    hωpt, hptω, hptpt, smul_zero]
  rw [hωω]
  simp only [map_add, map_neg, map_smul, map_zero, h1, hω0, s8_integral_pt, smul_eq_mul]
  ring

/-- `exp(tω) = 1 + tω + (t²/2) ω²` (`n = 2`). -/
theorem s8_exp_two {ω : S F 2} (hω : ω ∈ ⋀[F]^2 (H1 F 2)) (t : F) :
    IsNilpotent.exp (t • ω) = 1 + t • ω + (t ^ 2 / 2) • (ω * ω) := by
  have hq : ∀ (q : ℚ) (x : S F 2), q • x = (q : F) • x := fun q x =>
    (Rat.cast_smul_eq_qsmul F q x).symm
  rw [IsNilpotent.exp_eq_sum (s8_pow_eq_zero F 2 (Submodule.smul_mem _ t hω) (by norm_num : 2 < 3))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hq, smul_pow]
  norm_num
  rw [smul_smul, sq ω]
  congr 2
  ring

/-- An isotropic even spinor with nonzero degree-`0` part is `a exp(ω/a)` (`n = 2`). -/
theorem s8_eq_smul_exp_two {u : S F 2} (hu : u ∈ Splus F 2)
    (ha : ExteriorAlgebra.algebraMapInv u ≠ 0) (hiso : mukai F 2 u u = 0) :
    u = ExteriorAlgebra.algebraMapInv u • IsNilpotent.exp ((ExteriorAlgebra.algebraMapInv u)⁻¹ •
      GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u) := by
  have hω : GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u ∈ ⋀[F]^2 (H1 F 2) :=
    s8_proj_mem u 2
  have hdec := s8_Splus_two hu
  have hm := s8_mukai_two (ExteriorAlgebra.algebraMapInv u) (integral F 2 u) hω
  rw [← hdec, hiso] at hm
  have hωω := s8_eq_smul_pt_of_mem (SetLike.mul_mem_graded hω hω)
  rw [s8_exp_two hω, hωω]
  conv_lhs => rw [hdec]
  rw [Algebra.algebraMap_eq_smul_one]
  generalize ExteriorAlgebra.algebraMapInv u = a at ha hm ⊢
  generalize integral F 2 u = b at hm ⊢
  generalize integral F 2 (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u *
    GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u) = c at hm ⊢
  have hb : b = a * ((a⁻¹) ^ 2 / 2 * c) := by
    field_simp
    linear_combination -hm
  rw [hb]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- **For `n = 2`, isotropic even spinors are pure** ([M2, Prop. 1.7], cited in Example 8.2.2):
`ker m_u` has dimension `4`. -/
theorem s8_finrank_ann_two {u : S F 2} (hu : u ∈ Splus F 2) (hu0 : u ≠ 0)
    (hiso : mukai F 2 u u = 0) : Module.finrank F (ann F 2 u) = 2 * 2 := by
  -- the case `a ≠ 0`: `u = a exp(ω/a)`
  have key : ∀ u : S F 2, u ∈ Splus F 2 → ExteriorAlgebra.algebraMapInv u ≠ 0 →
      mukai F 2 u u = 0 → Module.finrank F (ann F 2 u) = 2 * 2 := by
    intro u hu ha hiso
    rw [s8_eq_smul_exp_two hu ha hiso, s8_ann_smul ha]
    exact s8_finrank_ann_exp (Submodule.smul_mem _ _ (s8_proj_mem u 2))
  by_cases ha : ExteriorAlgebra.algebraMapInv u = 0
  · have hdec := s8_Splus_two hu
    rw [ha, map_zero, zero_add] at hdec
    by_cases hω : GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u = 0
    · -- `u = b [pt]`
      rw [hω, zero_add] at hdec
      have hb : integral F 2 u ≠ 0 := fun hb => hu0 (by rw [hdec, hb, zero_smul])
      rw [hdec, s8_ann_smul hb, s8_finrank_ann_pt]
    · -- an Eichler transvection makes the degree-`0` part nonzero
      have hω2 := s8_proj_mem (F := F) (n := 2) u 2
      obtain ⟨y, y', hyy'⟩ := s8_exists_DD_ne_zero hω2 hω
      obtain ⟨g, hg⟩ := s8_exists_spin_DD (n := 2) y y'
      have hDD : D F 2 y' (D F 2 y u) =
          D F 2 y' (D F 2 y (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u)) +
            integral F 2 u • D F 2 y' (D F 2 y (pt F 2)) := by
        conv_lhs => rw [hdec]
        rw [map_add, map_add, map_smul, map_smul]
      have hpt2 : D F 2 y' (D F 2 y (pt F 2)) ∈ ⋀[F]^2 (H1 F 2) :=
        s8_contractLeft_mem y' (s8_contractLeft_mem y (s8_pt_mem F 2))
      have hω0 : D F 2 y' (D F 2 y (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (H1 F 2)) 2 u)) ∈
          ⋀[F]^0 (H1 F 2) :=
        s8_contractLeft_mem y' (s8_contractLeft_mem y hω2)
      rw [← s8_finrank_ann_m g u, hg]
      refine key _ ?_ ?_ ?_
      · rw [hDD]
        exact add_mem hu (add_mem (s8_mem_Splus_of_mem (by decide : Even 0) hω0)
          (Submodule.smul_mem _ _ (s8_mem_Splus_of_mem even_two hpt2)))
      · rw [hDD, map_add, map_add, map_smul, ha, s8_algebraMapInv_eq_zero_of_mem two_pos hpt2,
          smul_zero, add_zero, zero_add]
        exact hyy'
      · rw [s8_mukai_DD]
        exact hiso
  · exact key u hu ha hiso

/-- **For `n = 2` the pure spinors in `S⁺` are its nonzero isotropic vectors** ([M2, Prop. 1.7]). -/
theorem s8_isEvenPureSpinor_two {u : S F 2} (hu : u ∈ Splus F 2) (hu0 : u ≠ 0)
    (hiso : mukai F 2 u u = 0) : IsEvenPureSpinor F 2 u :=
  ⟨hu, fun _ hv => s8_Q_of_mem_ann hu0 hv, s8_finrank_ann_two hu hu0 hiso⟩

end S8PureTwo

section S8Secant

/-- `bcS` commutes with `τ`. -/
theorem s8_bcS_tau {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F']
    {n : ℕ} (x : S F n) : bcS F F' n (tau F n x) = tau F' n (bcS F F' n x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp only [tau, AlgHom.commutes, CliffordAlgebra.reverse.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), CliffordAlgebra.reverse.commutes]
  | ι w =>
    change bcS F F' n (reverse (CliffordAlgebra.ι 0 w)) =
      reverse (bcS F F' n (CliffordAlgebra.ι 0 w))
    rw [CliffordAlgebra.reverse_ι]
    change bcS F F' n (ExteriorAlgebra.ι F w) = reverse (bcS F F' n (ExteriorAlgebra.ι F w))
    rw [s8_bcS_ι]
    exact (CliffordAlgebra.reverse_ι _).symm
  | mul x y hx hy => rw [s8_tau_mul, map_mul, map_mul, hx, hy, s8_tau_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `(x_K, y_K)_S = (x, y)_S` (extension of scalars). -/
theorem s8_mukai_bcS {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    [Algebra F F'] {n : ℕ} (x y : S F n) :
    mukai F' n (bcS F F' n x) (bcS F F' n y) = algebraMap F F' (mukai F n x y) := by
  simp only [mukai, LinearMap.compr₂_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mul_apply']
  rw [← s8_bcS_tau, ← map_mul, s8_integral_bcS]

/-- `bcS` maps `S⁺_ℚ` into `S⁺_K`. -/
theorem s8_bcS_Splus {n : ℕ} (d : ℚ) {x : S ℚ n} (hx : x ∈ Splus ℚ n) :
    bcS ℚ (Kd d) n x ∈ Splus (Kd d) n := by
  refine Submodule.iSup_induction (motive := fun x => bcS ℚ (Kd d) n x ∈ Splus (Kd d) n) _ hx
    ?_ ?_ ?_
  · rintro ⟨j, hj⟩ x hx
    have hx' : x ∈ ⋀[ℚ]^j (H1 ℚ n) := hx
    exact Submodule.mem_iSup_of_mem (⟨j, hj⟩ : { j : ℕ // (j : ZMod 2) = 0 }) (s8_bcS_mem hx')
  · simp
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

theorem s8_σ_sqrtNeg (d : ℚ) : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp [Kd.coe_σ, Kd.sqrtNeg, sqrtNeg, Complex.conj_ofReal]

theorem s8_σ_algebraMap (d q : ℚ) : Kd.σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  rw [Kd.coe_σ, s8_coe_algebraMap]
  simp

/-- `σ(x + c y) = x + σ(c) y` for rational `x, y`. -/
theorem s8_σS_bcS_add_smul {n : ℕ} (d : ℚ) (x y : S ℚ n) (c : Kd d) :
    σS n d (bcS ℚ (Kd d) n x + c • bcS ℚ (Kd d) n y) =
      bcS ℚ (Kd d) n x + Kd.σ d c • bcS ℚ (Kd d) n y := by
  apply (basisS (Kd d) n).repr.injective
  refine Finsupp.ext fun K => ?_
  change (basisS (Kd d) n).repr (∑ L, Kd.σ d ((basisS (Kd d) n).repr
    (bcS ℚ (Kd d) n x + c • bcS ℚ (Kd d) n y) L) • basisS (Kd d) n L) K = _
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_add, Finsupp.add_apply, s8_repr_bcS, map_mul,
    s8_σ_algebraMap]

/-- Rational vectors independent over `ℚ` stay independent over `K` (real and imaginary parts). -/
theorem s8_bcS_pair_indep {n : ℕ} {d : ℚ} (hd : 0 < d) {w h : S ℚ n}
    (hind : ∀ p q : ℚ, p • w + q • h = 0 → p = 0 ∧ q = 0) (x y : Kd d)
    (hxy : x • bcS ℚ (Kd d) n w + y • bcS ℚ (Kd d) n h = 0) : x = 0 ∧ y = 0 := by
  have hre := congrArg (reS n d) hxy
  have him := congrArg (imS n d) hxy
  rw [map_add, s8_reS_smul_bcS, s8_reS_smul_bcS, map_zero] at hre
  rw [map_add, s8_imS_smul_bcS, s8_imS_smul_bcS, map_zero] at him
  obtain ⟨h1, h2⟩ := hind _ _ hre
  obtain ⟨h3, h4⟩ := hind _ _ him
  constructor
  · rw [Kd.eq_ratPart_add_sqrtNegCoeff hd x, h1, h3]; simp
  · rw [Kd.eq_ratPart_add_sqrtNegCoeff hd y, h2, h4]; simp

/-- **[M2, Prop. 1.7]** (E. Markman, *The monodromy of generalized Kummer varieties and algebraic
cycles on their intermediate Jacobians*, JEMS 25 (2023), 231–321; Proposition 12.6 and
Corollary 12.9 there), in the form used in Example 8.2.2 (TeX lines 3773–3775, `example8_2_2`): on
an abelian surface (`n = 2`), if `w, h ∈ S⁺_ℚ = H^{ev}(X, ℚ)` satisfy `(w, w)_S < 0`,
`(h, h)_S < 0` and `(w, h)_S = 0`, then `span_ℚ{w, h}` is a secant to the spinor variety inducing
complex multiplication by `ℚ(√-d)`, `d = (w, w)_S (h, h)_S / 4`: it is the rational plane of a
`K`-secant.

Special case: [M2] states Prop. 1.7 for `w = ch(I_Z)` (`Z` a subscheme of length `n + 1`) and an
integral `h`, as the statement that the abelian fourfolds over the periods orthogonal to `w` and `h`
are of Weil type with complex multiplication by `ℚ(√-d)`; Example 8.2.2 uses its cohomological core
(the secant `span{w, h}` and its field), for any rational `w` with `(w, w)_S < 0`. -/
theorem markmanM2_prop1_7 (w h : S ℚ 2) (hw : w ∈ Splus ℚ 2) (hh : h ∈ Splus ℚ 2)
    (hww : mukai ℚ 2 w w < 0) (hhh : mukai ℚ 2 h h < 0) (hwh : mukai ℚ 2 w h = 0) :
    ∃ P : KSecant 2 (mukai ℚ 2 w w * mukai ℚ 2 h h / 4), P.Pℚ = Submodule.span ℚ {w, h} := by
  -- The line `ℙ(span_K{w, h})` meets the quadric of isotropic vectors, which for `n = 2` is the
  -- spinor variety (`s8_isEvenPureSpinor_two`), in the conjugate points `w ± c h`,
  -- `c = 2√-d/(h, h)`.
  set A := mukai ℚ 2 w w with hA
  set B := mukai ℚ 2 h h with hB
  set d := A * B / 4 with hd_def
  have hd : 0 < d := by
    have := mul_pos_of_neg_of_neg hww hhh
    rw [hd_def]; positivity
  have hhw : mukai ℚ 2 h w = 0 := by
    rw [mukai_swap_of_mem_Splus ℚ 2 w h hw hh, hwh, mul_zero]
  -- `w, h` are linearly independent over `ℚ`
  have hind : ∀ p q : ℚ, p • w + q • h = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    have h1 := congrArg (fun z => mukai ℚ 2 z w) hpq
    have h2 := congrArg (fun z => mukai ℚ 2 z h) hpq
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply, hhw, hwh] at h1 h2
    constructor
    · have : p * A = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hww.ne
    · have : q * B = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hhh.ne
  -- `u₁ = w + c h`, `c = 2√-d/(h, h)`, `c² = -(w, w)/(h, h)`
  set s := Kd.sqrtNeg d with hs_def
  have hs : s * s = algebraMap ℚ (Kd d) (-d) := s8_sqrtNeg_mul_self hd.le
  set c : Kd d := algebraMap ℚ (Kd d) (2 / B) * s with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by simp [hhh.ne]) (s8_sqrtNeg_ne_zero hd)
  have hB0 : B ≠ 0 := hhh.ne
  have hcc : c * c * algebraMap ℚ (Kd d) B = -algebraMap ℚ (Kd d) A := by
    have e : c * c * algebraMap ℚ (Kd d) B =
        algebraMap ℚ (Kd d) (2 / B * (2 / B) * (-d) * B) := by
      rw [hc, map_mul, map_mul, map_mul, ← hs]
      ring
    rw [e, ← map_neg]
    congr 1
    rw [hd_def]
    field_simp
    ring
  set u₁ := bcS ℚ (Kd d) 2 w + c • bcS ℚ (Kd d) 2 h with hu₁
  have hσc : Kd.σ d c = -c := by
    rw [hc, map_mul, s8_σ_algebraMap, s8_σ_sqrtNeg, mul_neg]
  have hu₂ : σS 2 d u₁ = bcS ℚ (Kd d) 2 w - c • bcS ℚ (Kd d) 2 h := by
    rw [hu₁, s8_σS_bcS_add_smul, hσc, neg_smul, ← sub_eq_add_neg]
  -- `u₁` is an isotropic, hence pure, spinor
  have hpure : IsEvenPureSpinor (Kd d) 2 u₁ := by
    refine s8_isEvenPureSpinor_two ?_ ?_ ?_
    · exact add_mem (s8_bcS_Splus d hw) (Submodule.smul_mem _ _ (s8_bcS_Splus d hh))
    · intro h0
      have := congrArg (reS 2 d) h0
      have hrc : Kd.ratPart d c = 0 := by
        rw [hc, ← Algebra.smul_def, map_smul, s8_ratPart_sqrtNeg, smul_zero]
      rw [hu₁, map_add, s8_reS_bcS, s8_reS_smul_bcS, map_zero, hrc, zero_smul, add_zero] at this
      exact hww.ne (by simp [hA, this])
    · rw [hu₁]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        s8_mukai_bcS, hwh, hhw, map_zero]
      linear_combination hcc
  have hlin : LinearIndependent (Kd d) ![u₁, σS 2 d u₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rw [hu₂, hu₁] at hab
    have h' : (a + b) • bcS ℚ (Kd d) 2 w + ((a - b) * c) • bcS ℚ (Kd d) 2 h = 0 := by
      rw [← hab]
      module
    obtain ⟨h1, h2⟩ := s8_bcS_pair_indep hd hind _ _ h'
    have h3 : a - b = 0 := (mul_eq_zero.mp h2).resolve_right hc0
    constructor
    · linear_combination (h1 + h3) / 2
    · linear_combination (h1 - h3) / 2
  refine ⟨⟨u₁, hpure, hlin⟩, ?_⟩
  -- the rational plane `P = span_ℚ{w, h}`
  ext x
  simp only [KSecant.Pℚ, KSecant.PK, KSecant.u₂, Submodule.mem_comap,
    Submodule.restrictScalars_mem, AlgHom.toLinearMap_apply]
  rw [hu₂, Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨α, β, hαβ⟩
    refine ⟨Kd.ratPart d (α + β), Kd.ratPart d ((α - β) * c), ?_⟩
    have e : α • u₁ + β • (bcS ℚ (Kd d) 2 w - c • bcS ℚ (Kd d) 2 h) =
        (α + β) • bcS ℚ (Kd d) 2 w + ((α - β) * c) • bcS ℚ (Kd d) 2 h := by
      rw [hu₁]
      module
    have := congrArg (reS 2 d) hαβ
    rw [e, map_add, s8_reS_smul_bcS, s8_reS_smul_bcS, s8_reS_bcS] at this
    exact this
  · rintro ⟨p, q, hpq⟩
    refine ⟨(algebraMap ℚ (Kd d) p + algebraMap ℚ (Kd d) q * c⁻¹) / 2,
      (algebraMap ℚ (Kd d) p - algebraMap ℚ (Kd d) q * c⁻¹) / 2, ?_⟩
    rw [← hpq, map_add, map_smul, map_smul, hu₁, ← algebraMap_smul (Kd d) p,
      ← algebraMap_smul (Kd d) q]
    match_scalars <;> field_simp <;> ring

end S8Secant

end WeilClasses
