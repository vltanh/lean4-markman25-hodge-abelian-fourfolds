module

public import WeilClasses.Spinor.Integral
public import WeilClasses.PureSpinor.Groups
public import WeilClasses.External.GolyshevLuntsOrlov.Sec2_1
import WeilClasses.External.Chevalley.Sec2_1
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegralLattice

/-!
# The Clifford algebra and the spin group (paper §2.1)

The paper's §2.1 recalls the Clifford algebra `C(V)` (relation (2.1.1)), the spin representation
`m : C(V) → End(S)` ((2.1.2)–(2.1.3)), the main anti-automorphism `τ`, the main involution `α`, the
conjugation `x* = τ(α(x))`, the integral Clifford group `G(V)`, the integral spin group
`Spin(V)`, the standard representation `ρ(x)(v) = x v x⁻¹`, the norm character `N(g) = g τ(g)`, and
a list of facts. Everything is then repeated over a field `K` ("the same definitions above
yield ...").

The objects `C(V_F)`, `m`, `τ`, `S^±`, the Mukai pairing, `Spin(V_F)` (Mathlib's `spinGroup`),
`ρ` on `Spin(V_F)`, and the integral `C(V)` (`CZ`) and `Spin(V)` (`SpinZ`) are in
`WeilClasses.Spinor.Defs` and `WeilClasses.Spinor.Integral`. In Mathlib's language `τ` is
`CliffordAlgebra.reverse`, `α` is `CliffordAlgebra.involute`, and `x* = τ(α(x))` is `star x`.

## Main definitions

* `WeilClasses.mEquiv`: the isomorphism (2.1.3) `m : C(V_F) ≅ End(S_F)` over a field
  ([GLO, Prop. 3.2.1(e)], `WeilClasses.glo_prop3_2_1_e_field`).

The Clifford group `G(V_F) = {x ∈ C(V_F)ˣ : x V x⁻¹ ⊆ V}` (`WeilClasses.cliffordGroup F n`,
untwisted, as in the paper) and the integral Clifford group `G(V)` (`WeilClasses.cliffordGroupZ n`,
inside `C(V_ℚ)ˣ`) are defined in `WeilClasses.PureSpinor.Groups`, upstream of the statements of the
cited results of [Chevalley] (`WeilClasses.External.Chevalley.Sec2_1`), which use `G(V_F)`.

## Statements (claims of §2.1)

* `m_ι_injective`, `m_ι_mul_add_mul_swap`: `m : V → End(S)` is an embedding (2.1.2) satisfying the
  analogue of the Clifford relation (2.1.1); `pairing_eq_of_conj_ι`: `ρ : G(V) → O(V)`.
* `mem_spin_iff`, `mem_SpinZ_iff`: the paper's definitions of `Spin(V_F)` and of the integral
  `Spin(V)` agree with the model (`spinGroup`, `SpinZ`).
* `exists_mul_reverse_eq_algebraMap`, `mul_reverse_eq_one_or_neg_one_of_mem_cliffordGroupZ`: the
  norm `N(g) = g τ(g)` is a scalar on `G(V_F)`, and is `±1` on the integral `G(V)`.
* `spinZ_relIndex_cliffordGroupZ`: `Spin(V)` has index four in `G(V)`.
* `exists_unit_ι_mem_cliffordGroup`, `neg_conj_ι_eq_reflection`: for `(v,v)_V = ±2`, `v ∈ G(V)`
  and `-ρ(v)` is the reflection in `v^⊥`.
* `exists_spinZ_eq_ι_mul_ι`, `spinZ_eq_closure`: `v₁ v₂ ∈ Spin(V)` when
  `(v₁,v₁)_V = (v₂,v₂)_V = ±2`, and these elements generate `Spin(V)`.
* `m_mem_Sminus_of_odd`, `m_mem_Splus_of_odd`: odd elements of `C(V)` swap `S⁺` and `S⁻`;
  `m_ι_rho_m`: the maps `V ⊗ S^± → S^∓` are `Spin(V)`-equivariant.
* `ι_mul_reverse_ι_of_pairing_eq_two`, `mukai_m_ι_m_ι_of_pairing_eq_two`,
  `m_ι_mul_m_ι_of_pairing_eq_two`, `m_ι_mem_Sminus_of_pairing_eq_two`,
  `m_ι_mem_Splus_of_pairing_eq_two`, `exists_mem_cliffordGroupZ_of_pairing_eq_two`: for
  `(v,v)_V = 2`: `v ∈ G(V)`, `N(v) = 1`, `m_v` is an isometry of `(·,·)_S` interchanging `S⁺` and
  `S⁻`, and `m_v² = 1`.

The cited facts `(m_v s, t)_S = (s, m_v t)_S` [Chevalley, III.2.2] and
`(g s, g t)_S = N(g)(s,t)_S` [Chevalley, III.2.1] are in `WeilClasses.External.Chevalley.Sec2_1`;
the isomorphism `m` over `ℤ` and over a field [GLO, Prop. 3.2.1(e)] is in
`WeilClasses.External.GolyshevLuntsOrlov.Sec2_1`.

Facts stated over a field `F` of characteristic zero imply the paper's integral statements, since
`C(V) ⊆ C(V_ℚ)`; the paper itself repeats them over fields at the end of §2.1.

## Proofs

Most claims are direct computations in `C(V)` (`ι v ι l ι v = (v, l) v - Q(v) l`, the Clifford
relation, the parity of `L_w` and `D_θ`). The facts used without proof in §2.1 are proved here:

* the centre of `C(V_F)` is `F` (`dim V_F = 4n` is even; via the volume element,
  `s21_eq_algebraMap_of_commute`), so `N(g) = g τ(g)` is a scalar on `G(V_F)` and the elements of
  `G(V_F)` are even or odd (`s21_involute_eq_or_neg`);
* `C(V) ∩ ℚ = ℤ` (`m(C(V))` preserves `S = H*(X, ℤ)`, Tau Ceti's integral lattice), so `N = ±1`
  on `G(V)`; `Spin(V)` is the kernel of `(parity, N) : G(V) → {±1}²`, which is onto, hence of
  index four;
* the generation of `Spin(V)` by the `v₁ v₂`, by the Euclidean algorithm on the hyperbolic lattice
  `V = U^{⊕ 2n}` with Eichler transformations (section `Generation` below).

As in the paper, the isometry property of `m_v` for `(v, v)_V = 2` is [Chevalley, III.2.1]
(`chevalley_III_2_1`) applied to `g = v ∈ G(V)` with `N(v) = 1`
(`mukai_m_ι_m_ι_of_pairing_eq_two`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ### Helpers for the field statements (prefix `s21_`) -/

section HelpersField

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `m_{(θ, w)} = L_w + D_θ`. -/
theorem s21_m_ι_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) (x : S F n) :
    m F n (ι (Q F n) (θ, w)) x = ExteriorAlgebra.ι F w * x + D F n θ x := by
  simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, L, LinearMap.mul_apply']

omit [CharZero F] in
/-- `(v, v)_V = 2 Q(v)`. -/
theorem s21_pairing_self (v : V F n) : pairing F n v v = 2 * Q F n v := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
    Nat.cast_ofNat]

omit [CharZero F] in
/-- `(v₁, v₂)_V = (v₂, v₁)_V`. -/
theorem s21_pairing_comm (v₁ v₂ : V F n) : pairing F n v₁ v₂ = pairing F n v₂ v₁ := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm]

/-- If `(v, v)_V = 2` then `Q(v) = 1`. -/
theorem s21_Q_eq_one {v : V F n} (hv : pairing F n v v = 2) : Q F n v = 1 := by
  rw [s21_pairing_self] at hv
  exact mul_left_cancel₀ (two_ne_zero (α := F)) (hv.trans (mul_one 2).symm)

/-- If `(v, v)_V = -2` then `Q(v) = -1`. -/
theorem s21_Q_eq_neg_one {v : V F n} (hv : pairing F n v v = -2) : Q F n v = -1 := by
  rw [s21_pairing_self] at hv
  exact mul_left_cancel₀ (two_ne_zero (α := F)) (hv.trans (by ring))

/-- If `(v, v)_V = ±2` then `Q(v) = ±1`. -/
theorem s21_Q_of_pairing (v : V F n) (hv : pairing F n v v = 2 ∨ pairing F n v v = -2) :
    Q F n v = 1 ∨ Q F n v = -1 :=
  hv.imp s21_Q_eq_one s21_Q_eq_neg_one

omit [CharZero F] in
/-- The pairing (1.2.2) is nondegenerate. -/
theorem s21_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

omit [CharZero F] in
/-- Uniqueness of the decomposition into even and odd parts. -/
theorem s21_evenOdd_unique {M : Type*} [AddCommGroup M] [Module F M] {q : QuadraticForm F M}
    {a₀ b₀ a₁ b₁ : CliffordAlgebra q} (ha₀ : a₀ ∈ evenOdd q 0) (hb₀ : b₀ ∈ evenOdd q 0)
    (ha₁ : a₁ ∈ evenOdd q 1) (hb₁ : b₁ ∈ evenOdd q 1) (h : a₀ + a₁ = b₀ + b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  have hd := Submodule.disjoint_def.mp (evenOdd_isCompl q).disjoint
  have h0 : a₀ - b₀ = b₁ - a₁ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm b₁, h, add_comm]
  have hz : a₀ - b₀ = 0 :=
    hd _ (Submodule.sub_mem _ ha₀ hb₀) (h0 ▸ Submodule.sub_mem _ hb₁ ha₁)
  refine ⟨sub_eq_zero.mp hz, ?_⟩
  rw [hz] at h0
  exact (sub_eq_zero.mp h0.symm).symm

/-- If `involute x = x` then `x` is even (characteristic zero). -/
theorem s21_mem_even_of_involute_eq {M : Type*} [AddCommGroup M] [Module F M]
    {q : QuadraticForm F M} {x : CliffordAlgebra q} (hx : involute x = x) : x ∈ evenOdd q 0 := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩, hsum, -⟩ :=
    Submodule.existsUnique_add_of_isCompl (evenOdd_isCompl q) x
  simp only at hsum
  have hinv : involute x = x₀ - x₁ := by
    rw [← hsum, map_add, involute_eq_of_mem_even hx₀, involute_eq_of_mem_odd hx₁, sub_eq_add_neg]
  have h2 : (2 : F) • x₁ = 0 := by
    have h' : x₀ + x₁ = x₀ - x₁ := by rw [hsum, ← hinv, hx]
    rw [two_smul]
    calc x₁ + x₁ = (x₀ + x₁) - (x₀ - x₁) := by abel
      _ = 0 := by rw [h', sub_self]
  have hx₁0 : x₁ = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rw [← hsum, hx₁0, add_zero]
  exact hx₀

/-- `ι v` as a unit of `C(V_F)` when `Q(v) ≠ 0`, with inverse `Q(v)⁻¹ v`. -/
noncomputable def s21_unitι (v : V F n) (hv : Q F n v ≠ 0) : (C F n)ˣ where
  val := ι (Q F n) v
  inv := (Q F n v)⁻¹ • ι (Q F n) v
  val_inv := by
    rw [mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hv, map_one]
  inv_val := by
    rw [smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hv, map_one]

omit [CharZero F] in
theorem s21_inv_eq_of_val_eq_ι {x : (C F n)ˣ} {v : V F n} (hx : (x : C F n) = ι (Q F n) v)
    (hv : Q F n v ≠ 0) : ((x⁻¹ : (C F n)ˣ) : C F n) = (Q F n v)⁻¹ • ι (Q F n) v :=
  Units.inv_eq_of_mul_eq_one_right (by
    rw [hx, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hv, map_one])

omit [CharZero F] in
/-- `v l v⁻¹ = Q(v)⁻¹ ((v, l)_V v - Q(v) l)`. -/
theorem s21_conj_ι {x : (C F n)ˣ} {v : V F n} (hx : (x : C F n) = ι (Q F n) v)
    (hv : Q F n v ≠ 0) (l : V F n) :
    (x : C F n) * ι (Q F n) l * ((x⁻¹ : (C F n)ˣ) : C F n) =
      ι (Q F n) ((Q F n v)⁻¹ • (QuadraticMap.polar (Q F n) v l • v - Q F n v • l)) := by
  rw [s21_inv_eq_of_val_eq_ι hx hv, hx, mul_smul_comm, ι_mul_ι_mul_ι, ← map_smul]

/-- `m_v` shifts the parity of `S`. -/
theorem s21_m_ι_mem_evenOdd (v : V F n) {i : ZMod 2} {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    m F n (ι (Q F n) v) s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) (i + 1) := by
  obtain ⟨θ, w⟩ := v
  rw [s21_m_ι_apply]
  refine Submodule.add_mem _ ?_ (contractLeft_mem_evenOdd θ hs)
  have := evenOdd_mul_le (0 : QuadraticForm F (H1 F n)) 1 i
    (Submodule.mul_mem_mul (ι_mem_evenOdd_one _ w) hs)
  rwa [add_comm] at this

/-- An odd element of `C(V_F)` shifts the parity of `S`. -/
theorem s21_m_mem_evenOdd_of_odd (x : C F n) (hx : x ∈ evenOdd (Q F n) 1) (i : ZMod 2)
    (s : S F n) (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) i) :
    m F n x s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) (i + 1) := by
  induction x, hx using odd_induction generalizing i s with
  | ι v => exact s21_m_ι_mem_evenOdd v hs
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (hx i s hs) (hy i s hs)
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have h3 := s21_m_ι_mem_evenOdd m₁ (s21_m_ι_mem_evenOdd m₂ (hx i s hs))
    have e : i + 1 + 1 + 1 = i + 1 := by
      rw [add_assoc (i + 1), show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]
    rwa [e] at h3

end HelpersField

/-! ### The volume element and the centre of `C(V_F)` -/

section Volume

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The orthogonal basis `(f_i, e_i), (-f_i, e_i)` of `V_F` (squares `1` and `-1`). -/
noncomputable def s21_volList (F : Type*) [Field F] [CharZero F] (n : ℕ) : List (V F n) :=
  (List.finRange (2 * n)).map (fun i => ((f F n i, e F n i) : V F n)) ++
    (List.finRange (2 * n)).map (fun i => ((-f F n i, e F n i) : V F n))

theorem s21_volList_pairwise : (s21_volList F n).Pairwise (Q F n).IsOrtho := by
  have hO : ∀ v w : V F n, v.1 w.2 + w.1 v.2 = 0 → (Q F n).IsOrtho v w := fun v w h => by
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply, s21_polar_apply, h]
  rw [s21_volList, List.pairwise_append, List.pairwise_map, List.pairwise_map]
  refine ⟨(List.nodup_finRange _).imp fun {i j} hij => hO _ _ ?_,
    (List.nodup_finRange _).imp fun {i j} hij => hO _ _ ?_, ?_⟩
  · simp [s21_f_e, hij, Ne.symm hij]
  · simp [s21_f_e, hij, Ne.symm hij]
  · intro a ha b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    apply hO
    simp only [LinearMap.neg_apply, s21_f_e]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

theorem s21_volList_length : Even (s21_volList F n).length := by
  simp [s21_volList]

theorem s21_volList_span : Submodule.span F {x : V F n | x ∈ s21_volList F n} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨θ, w⟩ -
  set P := Submodule.span F {x : V F n | x ∈ s21_volList F n}
  have hp : ∀ i, ((f F n i, e F n i) : V F n) ∈ P := fun i =>
    Submodule.subset_span (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  have hm : ∀ i, ((-f F n i, e F n i) : V F n) ∈ P := fun i =>
    Submodule.subset_span (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  have hfi : ∀ i, ((f F n i, 0) : V F n) ∈ P := fun i => by
    have h := P.smul_mem (2⁻¹ : F) (P.sub_mem (hp i) (hm i))
    have heq : (2⁻¹ : F) • (((f F n i, e F n i) : V F n) - (-f F n i, e F n i)) =
        (f F n i, 0) := by
      rw [Prod.mk_sub_mk, sub_neg_eq_add, sub_self, Prod.smul_mk, smul_zero,
        ← two_smul F (f F n i), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rwa [heq] at h
  have hei : ∀ i, ((0, e F n i) : V F n) ∈ P := fun i => by
    have h := P.smul_mem (2⁻¹ : F) (P.add_mem (hp i) (hm i))
    have heq : (2⁻¹ : F) • (((f F n i, e F n i) : V F n) + (-f F n i, e F n i)) =
        (0, e F n i) := by
      rw [Prod.mk_add_mk, add_neg_cancel, Prod.smul_mk, smul_zero,
        ← two_smul F (e F n i), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rwa [heq] at h
  rw [s21_V_decomp (θ, w)]
  exact P.add_mem (P.sum_mem fun i _ => P.smul_mem _ (hfi i))
    (P.sum_mem fun i _ => P.smul_mem _ (hei i))

/-- The volume element `ω`. -/
noncomputable def s21_vol (F : Type*) [Field F] [CharZero F] (n : ℕ) : C F n :=
  ((s21_volList F n).map (ι (Q F n))).prod

theorem s21_vol_anticomm (v : V F n) :
    s21_vol F n * ι (Q F n) v = -(ι (Q F n) v * s21_vol F n) :=
  prod_map_ι_mul_ι_of_even_length s21_volList_pairwise s21_volList_length
    (s21_volList_span.ge Submodule.mem_top)

theorem s21_vol_involute : involute (s21_vol F n) = s21_vol F n := by
  rw [s21_vol, involute_prod_map_ι, s21_volList_length.neg_one_pow, one_smul]

theorem s21_vol_isUnit : IsUnit (s21_vol F n) := by
  apply isUnit_prod_map_ι
  rw [isUnit_iff_ne_zero]
  simp only [s21_volList, List.map_append, List.map_map, List.prod_append]
  refine mul_ne_zero ?_ ?_ <;> refine List.prod_ne_zero ?_ <;> intro h0 <;>
    obtain ⟨i, -, hi⟩ := List.mem_map.mp h0 <;>
    simp [Function.comp, QuadraticForm.dualProd_apply, s21_f_e] at hi

/-- **The centre of `C(V_F)` is `F`** (`dim V_F = 4n` is even): an element commuting with every
vector is a scalar. Its even part graded-commutes with the vectors (Tau Ceti), and its odd part
`z₁` is `0`: `z₁ ω` graded-commutes with the vectors, so it is a scalar, and it is odd. -/
theorem s21_eq_algebraMap_of_commute (z : C F n)
    (hz : ∀ v : V F n, z * ι (Q F n) v = ι (Q F n) v * z) :
    ∃ c : F, z = algebraMap F (C F n) c := by
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩, hsum, -⟩ :=
    Submodule.existsUnique_add_of_isCompl (evenOdd_isCompl (Q F n)) z
  simp only at hsum
  have hcomm : ∀ v, z₀ * ι (Q F n) v = ι (Q F n) v * z₀ ∧ z₁ * ι (Q F n) v = ι (Q F n) v * z₁ := by
    intro v
    have h := hz v
    rw [← hsum, add_mul, mul_add] at h
    have hv := ι_mem_evenOdd_one (Q F n) v
    have e1 : z₀ * ι (Q F n) v ∈ evenOdd (Q F n) 1 := by
      simpa using evenOdd_mul_le (Q F n) 0 1 (Submodule.mul_mem_mul hz₀ hv)
    have e2 : z₁ * ι (Q F n) v ∈ evenOdd (Q F n) 0 := by
      have := evenOdd_mul_le (Q F n) 1 1 (Submodule.mul_mem_mul hz₁ hv)
      rwa [show (1 + 1 : ZMod 2) = 0 from rfl] at this
    have e3 : ι (Q F n) v * z₀ ∈ evenOdd (Q F n) 1 := by
      simpa using evenOdd_mul_le (Q F n) 1 0 (Submodule.mul_mem_mul hv hz₀)
    have e4 : ι (Q F n) v * z₁ ∈ evenOdd (Q F n) 0 := by
      have := evenOdd_mul_le (Q F n) 1 1 (Submodule.mul_mem_mul hv hz₁)
      rwa [show (1 + 1 : ZMod 2) = 0 from rfl] at this
    rw [add_comm (z₀ * _), add_comm (ι (Q F n) v * z₀)] at h
    obtain ⟨h1, h2⟩ := s21_evenOdd_unique e2 e4 e1 e3 h
    exact ⟨h2, h1⟩
  have hQ := s21_Q_nondegenerate (F := F) (n := n)
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul (Q F n) hQ z₀ fun v => by
    rw [involute_eq_of_mem_even hz₀, (hcomm v).1]
  -- the odd part vanishes
  have hz₁0 : z₁ = 0 := by
    obtain ⟨d, hd⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul (Q F n) hQ
      (z₁ * s21_vol F n) fun v => by
        rw [map_mul, involute_eq_of_mem_odd hz₁, s21_vol_involute, mul_assoc, s21_vol_anticomm,
          neg_mul, mul_neg, neg_neg, ← mul_assoc, (hcomm v).2, mul_assoc]
    have hinv := congrArg involute hd
    rw [map_mul, involute_eq_of_mem_odd hz₁, s21_vol_involute, AlgHom.commutes, neg_mul, hd]
      at hinv
    have hd0 : d = 0 := by
      have h2 : algebraMap F (C F n) (2 * d) = 0 := by
        rw [map_mul, map_ofNat, two_mul]
        nth_rewrite 1 [← hinv]
        exact neg_add_cancel _
      have := (algebraMap_injective (Q F n)) (h2.trans (map_zero _).symm)
      simpa using this
    rw [hd0, map_zero] at hd
    obtain ⟨u, hu⟩ := s21_vol_isUnit (F := F) (n := n)
    have := congrArg (· * ((u⁻¹ : (C F n)ˣ) : C F n)) hd
    simpa [← hu, mul_assoc] using this
  exact ⟨c, by rw [← hsum, hz₁0, add_zero, hc]⟩

end Volume

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The isomorphism (2.1.3) `m : C(V_F) ≅ End(S_F)` over a field, extending
`m_{(θ, w)} = L_w + D_θ` ([GLO, Prop. 3.2.1(e)]; end of §2.1 for `V_K`). -/
noncomputable def mEquiv : C F n ≃ₐ[F] Module.End F (S F n) :=
  AlgEquiv.ofBijective (m F n) (glo_prop3_2_1_e_field F n)

theorem mEquiv_apply (x : C F n) : mEquiv F n x = m F n x :=
  congrFun (AlgEquiv.coe_ofBijective _ _) x

/-- "**We get the embedding `m : V → End(S)`**" (2.1.2): `v ↦ m_v` is injective. -/
theorem m_ι_injective : Function.Injective fun v : V F n => m F n (ι (Q F n) v) := by
  -- `m_{(θ, w)}(1) = w` and `m_{(θ, w)}(e_i) = w ∧ e_i + θ(e_i)`.
  suffices key : ∀ x : V F n, m F n (ι (Q F n) x) = 0 → x = 0 by
    intro v v' h
    refine sub_eq_zero.mp (key _ ?_)
    simp only at h
    rw [map_sub, map_sub, h, sub_self]
  rintro ⟨θ, w⟩ hx
  have h1 := congrArg (fun A : Module.End F (S F n) => A 1) hx
  simp only [s21_m_ι_apply, mul_one, LinearMap.zero_apply] at h1
  have hD1 : D F n θ 1 = 0 := contractLeft_one _ θ
  rw [hD1, add_zero, ExteriorAlgebra.ι_eq_zero_iff] at h1
  subst h1
  have hθ : θ = 0 := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro i
    have h2 := congrArg
      (fun A : Module.End F (S F n) => A (ExteriorAlgebra.ι F (Pi.basisFun F _ i))) hx
    simp only [s21_m_ι_apply, map_zero, zero_mul, zero_add, LinearMap.zero_apply] at h2
    have h3 : D F n θ (ExteriorAlgebra.ι F (Pi.basisFun F _ i)) =
        algebraMap F (S F n) (θ (Pi.basisFun F _ i)) := contractLeft_ι _ θ _
    rw [h3] at h2
    simpa using h2
  rw [hθ]
  rfl

/-- The analogue `m_{v₁} ∘ m_{v₂} + m_{v₂} ∘ m_{v₁} = (v₁, v₂)_V · id_S` of the Clifford relation
(2.1.1) (§2.1). -/
theorem m_ι_mul_add_mul_swap (v₁ v₂ : V F n) :
    m F n (ι (Q F n) v₁) * m F n (ι (Q F n) v₂) + m F n (ι (Q F n) v₂) * m F n (ι (Q F n) v₁) =
      algebraMap F (Module.End F (S F n)) (pairing F n v₁ v₂) := by
  rw [← map_mul (m F n), ← map_mul (m F n), ← map_add (m F n), ι_mul_ι_add_swap,
    AlgHom.commutes]
  rfl

/-- **The spin group over a field** (§2.1, end): the paper's
`Spin(V_F) = {x ∈ C(V_F)^even : x x* = 1, x V_F x* ⊆ V_F}` is Mathlib's `spinGroup (Q F n)`
(Tau Ceti: `CliffordAlgebra.mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι`). Here
`x* = τ(α(x))` is `star x`. For `n = 0` the two differ (`spinGroup` of the zero form is `{1}`),
hence `0 < n`. This is the bridge referred to as `WeilClasses.mem_spin_iff` in
`WeilClasses.Spinor.Defs`. -/
theorem mem_spin_iff (hn : 0 < n) (x : C F n) :
    x ∈ spinGroup (Q F n) ↔
      x ∈ evenOdd (Q F n) 0 ∧ x * star x = 1 ∧
        ∀ v : V F n, ∃ u : V F n, x * ι (Q F n) v * star x = ι (Q F n) u := by
  have hv : ∃ v, IsUnit (Q F n v) :=
    ⟨(f F n ⟨0, by omega⟩, e F n ⟨0, by omega⟩), by
      rw [isUnit_iff_ne_zero, QuadraticForm.dualProd_apply, s21_f_e, ite_eq_left rfl]
      exact one_ne_zero⟩
  rw [mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι (Q F n) s21_Q_nondegenerate hv]
  have heven : x ∈ even (Q F n) ↔ x ∈ evenOdd (Q F n) 0 := by
    rw [← even_toSubmodule]; rfl
  constructor
  · rintro ⟨hu, he, hact⟩
    have he' := heven.mp he
    refine ⟨he', Unitary.mul_star_self_of_mem hu, fun v => ?_⟩
    obtain ⟨u, hu'⟩ := hact v
    rw [involute_eq_of_mem_even he'] at hu'
    exact ⟨u, hu'.symm⟩
  · rintro ⟨he, hxs, hact⟩
    -- `x x* = 1` implies `x* x = 1` in the finite-dimensional algebra `C(V_F)`.
    have hsx : star x * x = 1 := by
      have hsurj : Function.Surjective (LinearMap.mulLeft F x) := fun y =>
        ⟨star x * y, by rw [LinearMap.mulLeft_apply, ← mul_assoc, hxs, one_mul]⟩
      have hinj := LinearMap.injective_iff_surjective.mpr hsurj
      apply hinj
      simp only [LinearMap.mulLeft_apply, ← mul_assoc, hxs, one_mul, mul_one]
    refine ⟨Unitary.mem_iff.mpr ⟨hsx, hxs⟩, heven.mpr he, fun v => ?_⟩
    obtain ⟨u, hu⟩ := hact v
    rw [involute_eq_of_mem_even he]
    exact ⟨u, hu.symm⟩

/-- **The standard representation `ρ : G(V_F) → O(V_F)`**, `ρ(x)(v) = x v x⁻¹` (§2.1), takes values
in the orthogonal group: if `x v₁ x⁻¹ = u₁` and `x v₂ x⁻¹ = u₂` in `C(V_F)`, then
`(u₁, u₂)_V = (v₁, v₂)_V`. (The computation, from the Clifford relation, is
`s21_pairing_eq_of_conj_ι` in `WeilClasses.PureSpinor.Groups`, where `cliffordGroupZ` uses it.) -/
theorem pairing_eq_of_conj_ι (x : (C F n)ˣ) (v₁ v₂ u₁ u₂ : V F n)
    (h₁ : (x : C F n) * ι (Q F n) v₁ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₁)
    (h₂ : (x : C F n) * ι (Q F n) v₂ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₂) :
    pairing F n u₁ u₂ = pairing F n v₁ v₂ :=
  s21_pairing_eq_of_conj_ι F n x v₁ v₂ u₁ u₂ h₁ h₂

/-- The norm character `N(g) = g τ(g)` (§2.1) takes scalar values on the Clifford group: for
`g ∈ G(V_F)`, `g τ(g)` is a scalar. -/
theorem exists_mul_reverse_eq_algebraMap (x : (C F n)ˣ) (hx : x ∈ cliffordGroup F n) :
    ∃ c : F, (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) c := by
  -- `τ(x) x` commutes with `V`: apply `τ` to `x v x⁻¹ = u`.
  have h1 : reverse (x : C F n) * reverse ((x⁻¹ : (C F n)ˣ) : C F n) = 1 := by
    rw [← reverse.map_mul, Units.inv_mul, reverse.map_one]
  have hcomm : ∀ v : V F n, (reverse (x : C F n) * x) * ι (Q F n) v =
      ι (Q F n) v * (reverse (x : C F n) * x) := by
    intro v
    obtain ⟨u, hu⟩ := hx v
    have hu' : reverse ((x⁻¹ : (C F n)ˣ) : C F n) * ι (Q F n) v * reverse (x : C F n) =
        ι (Q F n) u := by
      have := congrArg reverse hu
      simpa only [reverse.map_mul, reverse_ι, mul_assoc] using this
    calc reverse (x : C F n) * x * ι (Q F n) v
        = reverse (x : C F n) * ((x : C F n) * ι (Q F n) v * ((x⁻¹ : (C F n)ˣ) : C F n)) *
            (x : C F n) := by
          simp only [mul_assoc, Units.inv_mul, mul_one]
      _ = reverse (x : C F n) * (reverse ((x⁻¹ : (C F n)ˣ) : C F n) * ι (Q F n) v *
            reverse (x : C F n)) * (x : C F n) := by rw [hu, hu']
      _ = ι (Q F n) v * (reverse (x : C F n) * x) := by
          simp only [← mul_assoc, h1, one_mul]
  obtain ⟨c, hc⟩ := s21_eq_algebraMap_of_commute _ hcomm
  refine ⟨c, ?_⟩
  calc (x : C F n) * reverse (x : C F n)
      = (x : C F n) * (reverse (x : C F n) * x) * ((x⁻¹ : (C F n)ˣ) : C F n) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = algebraMap F (C F n) c := by
        rw [hc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/-- If `(v, v)_V = ±2`, then `v` is invertible in `C(V_F)` and belongs to the Clifford group
`G(V_F)` (§2.1; implicit in "`-ρ(v)` is the reflection"). -/
theorem exists_unit_ι_mem_cliffordGroup (v : V F n)
    (hv : pairing F n v v = 2 ∨ pairing F n v v = -2) :
    ∃ x : (C F n)ˣ, (x : C F n) = ι (Q F n) v ∧ x ∈ cliffordGroup F n := by
  have hQv : Q F n v ≠ 0 := by
    rcases s21_Q_of_pairing v hv with h | h <;> rw [h] <;> norm_num
  exact ⟨s21_unitι v hQv, rfl, fun l => ⟨_, s21_conj_ι rfl hQv l⟩⟩

/-- **`-ρ(v)` is a reflection** (§2.1): if `(v, v)_V = ±2`, then
`-ρ(v)(λ) = λ - 2 (λ, v)_V / (v, v)_V · v` for all `λ ∈ V`, where `ρ(v)(λ) = v λ v⁻¹` is the
standard (untwisted) representation of the Clifford group. Here `x` is `v` as a unit of `C(V_F)`. -/
theorem neg_conj_ι_eq_reflection (v : V F n)
    (hv : pairing F n v v = 2 ∨ pairing F n v v = -2)
    (x : (C F n)ˣ) (hx : (x : C F n) = ι (Q F n) v) (l : V F n) :
    -((x : C F n) * ι (Q F n) l * ((x⁻¹ : (C F n)ˣ) : C F n)) =
      ι (Q F n) (l - (2 * pairing F n l v / pairing F n v v) • v) := by
  have hQv : Q F n v ≠ 0 := by
    rcases s21_Q_of_pairing v hv with h | h <;> rw [h] <;> norm_num
  rw [s21_conj_ι hx hQv l, ← map_neg]
  congr 1
  rw [s21_pairing_self, s21_pairing_comm l v, pairing, QuadraticMap.polarBilin_apply_apply,
    smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hQv, one_smul, neg_sub]
  congr 2
  field_simp

/-- **Odd elements swap the half-spin representations** (§2.1): an element `x ∈ C(V)^odd` maps `S⁺`
to `S⁻` under `m`. -/
theorem m_mem_Sminus_of_odd (x : C F n) (hx : x ∈ evenOdd (Q F n) 1) (s : S F n)
    (hs : s ∈ Splus F n) : m F n x s ∈ Sminus F n := by
  have := s21_m_mem_evenOdd_of_odd x hx 0 s hs
  rwa [zero_add] at this

/-- **Odd elements swap the half-spin representations** (§2.1): an element `x ∈ C(V)^odd` maps `S⁻`
to `S⁺` under `m`. -/
theorem m_mem_Splus_of_odd (x : C F n) (hx : x ∈ evenOdd (Q F n) 1) (s : S F n)
    (hs : s ∈ Sminus F n) : m F n x s ∈ Splus F n := by
  have := s21_m_mem_evenOdd_of_odd x hx 1 s hs
  rwa [show (1 + 1 : ZMod 2) = 0 from rfl] at this

/-- The homomorphisms `V ⊗ S⁺ → S⁻` and `V ⊗ S⁻ → S⁺`, `v ⊗ s ↦ m_v(s)`, are
`Spin(V)`-equivariant (§2.1): `m_{ρ(g)v}(g s) = g (m_v s)`. -/
theorem m_ι_rho_m (g : Spin F n) (v : V F n) (s : S F n) :
    m F n (ι (Q F n) (rho F n g v)) (m F n (g : C F n) s) =
      m F n (g : C F n) (m F n (ι (Q F n) v) s) := by
  rw [ι_rho, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    mul_assoc ((g : C F n) * ι (Q F n) v), spinGroup.star_mul_self_of_mem g.2, mul_one]

/-- If `(v, v)_V = 2` then `N(v) = v τ(v) = 1` (§2.1). -/
theorem ι_mul_reverse_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) :
    ι (Q F n) v * reverse (ι (Q F n) v) = 1 := by
  have hQ : Q F n v = 1 := s21_Q_eq_one hv
  rw [reverse_ι, ι_sq_scalar, hQ, map_one]

/-- If `(v, v)_V = 2` then `m_v : S → S` is an isometry of the Mukai pairing (§2.1).

Proof (the paper's): `v` belongs to `G(V)` (`exists_unit_ι_mem_cliffordGroup`) with
`N(v) = v τ(v) = 1` (`ι_mul_reverse_ι_of_pairing_eq_two`), so
`(m_v s, m_v t)_S = N(v) (s, t)_S = (s, t)_S` by [Chevalley, III.2.1] (`chevalley_III_2_1`). -/
theorem mukai_m_ι_m_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) (m F n (ι (Q F n) v) t) = mukai F n s t := by
  obtain ⟨x, hx, hxG⟩ := exists_unit_ι_mem_cliffordGroup F n v (Or.inl hv)
  have hN : (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) 1 := by
    rw [hx, ι_mul_reverse_ι_of_pairing_eq_two F n v hv, map_one]
  have h := chevalley_III_2_1 F n x hxG 1 hN s t
  rwa [hx, one_mul] at h

/-- If `(v, v)_V = 2` then `m_v² = 1_S` (§2.1). -/
theorem m_ι_mul_m_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) :
    m F n (ι (Q F n) v) * m F n (ι (Q F n) v) = 1 := by
  have hQ : Q F n v = 1 := s21_Q_eq_one hv
  rw [← map_mul, ι_sq_scalar, hQ, map_one, map_one]

/-- If `(v, v)_V = 2` then `m_v` maps `S⁺` to `S⁻` (§2.1). -/
theorem m_ι_mem_Sminus_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s : S F n)
    (hs : s ∈ Splus F n) : m F n (ι (Q F n) v) s ∈ Sminus F n :=
  m_mem_Sminus_of_odd F n _ (ι_mem_evenOdd_one _ v) s hs

/-- If `(v, v)_V = 2` then `m_v` maps `S⁻` to `S⁺` (§2.1). -/
theorem m_ι_mem_Splus_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s : S F n)
    (hs : s ∈ Sminus F n) : m F n (ι (Q F n) v) s ∈ Splus F n :=
  m_mem_Splus_of_odd F n _ (ι_mem_evenOdd_one _ v) s hs

end Field

/-! ### Helpers for the integral statements (prefix `s21_`) -/

section HelpersIntegral

variable {n : ℕ}

theorem s21_intCast_smul_mem_VZ {v : V ℚ n} (hv : v ∈ VZ n) (z : ℤ) : (z : ℚ) • v ∈ VZ n := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hv z

/-- The reflection formula: if `v ∈ V`, `Q(v) = ±1` and `l ∈ V`, then
`(v, l) v - Q(v) l ∈ V`. -/
theorem s21_refl_mem_VZ {v l : V ℚ n} (hv : v ∈ VZ n) (hl : l ∈ VZ n)
    (hQ : Q ℚ n v = 1 ∨ Q ℚ n v = -1) :
    QuadraticMap.polar (Q ℚ n) v l • v - Q ℚ n v • l ∈ VZ n := by
  obtain ⟨z, hz⟩ := s21_pairing_VZ hv hl
  have hp : QuadraticMap.polar (Q ℚ n) v l = z := hz
  rw [hp]
  refine sub_mem (s21_intCast_smul_mem_VZ hv z) ?_
  rcases hQ with h | h <;> rw [h]
  · rw [one_smul]; exact hl
  · rw [neg_one_smul]; exact neg_mem hl

theorem s21_ι_mem_CZ {v : V ℚ n} (hv : v ∈ VZ n) : ι (Q ℚ n) v ∈ CZ n :=
  Subring.subset_closure ⟨v, hv, rfl⟩

/-- `C(V)` is stable under `τ`. -/
theorem s21_reverse_mem_CZ {x : C ℚ n} (hx : x ∈ CZ n) : reverse x ∈ CZ n := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [reverse_ι]
      exact Subring.subset_closure ⟨v, hv, rfl⟩
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | one => rw [reverse.map_one]; exact Subring.one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact Subring.neg_mem _ hx
  | mul x y _ _ hx hy => rw [reverse.map_mul]; exact Subring.mul_mem _ hy hx

/-- `S = H*(X, ℤ)` is Tau Ceti's coordinate integral lattice of `⋀• ℚ^{2n}`. -/
private theorem s21_mem_SZ_iff {s : S ℚ n} :
    s ∈ SZ n ↔ s ∈ TauCeti.ExteriorAlgebra.integralLattice (Pi.basisFun ℚ (Fin (2 * n))) := by
  rw [TauCeti.ExteriorAlgebra.mem_integralLattice_iff]
  constructor
  · intro h K
    obtain ⟨z, hz⟩ := h K
    exact ⟨z, hz.symm⟩
  · intro h K
    obtain ⟨z, hz⟩ := h K
    exact ⟨z, hz.symm⟩

/-- `m_v = L_w + D_θ` preserves `S = H*(X, ℤ)` for `v = (θ, w) ∈ V`. -/
theorem s21_m_ι_mem_SZ {v : V ℚ n} (hv : v ∈ VZ n) {s : S ℚ n} (hs : s ∈ SZ n) :
    m ℚ n (ι (Q ℚ n) v) s ∈ SZ n := by
  obtain ⟨θ, w⟩ := v
  rw [s21_mem_SZ_iff] at hs ⊢
  rw [s21_m_ι_apply]
  set b := Pi.basisFun ℚ (Fin (2 * n))
  refine Submodule.add_mem _ ?_ ?_
  · have hw : w = ∑ i, w i • b i := by
      ext j
      simp [b, Pi.single_apply]
    rw [hw, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨z, hz⟩ := hv.2 i
    have hz' : w i = z := hz
    rw [map_smul, smul_mul_assoc, hz', Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ z (TauCeti.ExteriorAlgebra.ι_basis_mul_mem_integralLattice b i hs)
  · have hθ : θ = ∑ i, θ (e ℚ n i) • b.coord i := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, b,
        Pi.basisFun_repr]
      conv_lhs => rw [show x = ∑ i, x i • e ℚ n i by ext j; simp [e, Pi.single_apply]]
      simp [map_sum, mul_comm]
    have hD : D ℚ n θ s = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ (H1 ℚ n))) θ s :=
      rfl
    rw [hD, hθ, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨z, hz⟩ := hv.1 i
    have hz' : θ (e ℚ n i) = z := hz
    rw [map_smul, LinearMap.smul_apply, hz', Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ z
      (TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice b i hs)

/-- The homomorphism `m : C(V) → End(S)` over `ℤ` (§2.1, before (2.1.3)): `m(C(V))` preserves
`S = H*(X, ℤ)`. -/
theorem s21_m_mem_SZ {x : C ℚ n} (hx : x ∈ CZ n) {s : S ℚ n} (hs : s ∈ SZ n) :
    m ℚ n x s ∈ SZ n := by
  induction hx using Subring.closure_induction generalizing s with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact s21_m_ι_mem_SZ hv hs
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | one => rw [map_one, Module.End.one_apply]; exact hs
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact add_mem (hx hs) (hy hs)
  | neg x _ hx => rw [map_neg, LinearMap.neg_apply]; exact neg_mem (hx hs)
  | mul x y _ _ hx hy => rw [map_mul, Module.End.mul_apply]; exact hx (hy hs)

/-- `C(V) ∩ ℚ = ℤ`: `m(c) = c · id` preserves `S = H*(X, ℤ)` (`s21_m_mem_SZ`), and `c · 1 ∈ S`
gives `c ∈ ℤ`. -/
theorem s21_int_of_algebraMap_mem_CZ {c : ℚ} (h : algebraMap ℚ (C ℚ n) c ∈ CZ n) :
    ∃ z : ℤ, c = z := by
  have hb : basisS ℚ n ∅ = 1 := by
    rw [basisS, ExteriorAlgebra.basis_apply_ofCard _ (rfl : (∅ : Finset (Fin (2 * n))).card = 0)]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  have hrepr : (basisS ℚ n).repr 1 = Finsupp.single ∅ 1 := by
    rw [← hb, Module.Basis.repr_self]
  have h1 : (1 : S ℚ n) ∈ SZ n := by
    intro K
    rw [hrepr, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have h2 := s21_m_mem_SZ h h1
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at h2
  obtain ⟨z, hz⟩ := h2 ∅
  refine ⟨z, ?_⟩
  rw [← hz, map_smul, Finsupp.smul_apply, hrepr, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem s21_nontrivial : Nontrivial (C ℚ n) := (algebraMap_injective (Q ℚ n)).nontrivial

theorem s21_ne_neg_of_isUnit {x : C ℚ n} (hx : IsUnit x) : x ≠ -x := by
  have := s21_nontrivial (n := n)
  intro h
  have h2 : (2 : ℚ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact hx.ne_zero h'

/-- The parity `±1` of a homogeneous unit (`involute x = ±x`). -/
noncomputable def s21_par (x : C ℚ n) : ℤˣ := by
  classical exact if involute x = x then 1 else -1

/-- The norm `x τ(x) = ±1`. -/
noncomputable def s21_nrm (x : C ℚ n) : ℤˣ := by
  classical exact if x * reverse x = 1 then 1 else -1

theorem s21_par_of (z : C ℚ n) (hz : IsUnit z) (u : ℤˣ)
    (h : involute z = ((u : ℤ) : ℚ) • z) : s21_par z = u := by
  classical
  rcases Int.units_eq_one_or u with rfl | rfl
  · have h' : involute z = z := by simpa using h
    simp [s21_par, h']
  · have h' : involute z = -z := by simpa using h
    have : ¬ involute z = z := by rw [h']; exact (s21_ne_neg_of_isUnit hz).symm
    simp [s21_par, this]

theorem s21_nrm_of (z : C ℚ n) (u : ℤˣ)
    (h : z * reverse z = algebraMap ℚ (C ℚ n) ((u : ℤ) : ℚ)) : s21_nrm z = u := by
  classical
  rcases Int.units_eq_one_or u with rfl | rfl
  · have h' : z * reverse z = 1 := by simpa using h
    simp [s21_nrm, h']
  · have h' : z * reverse z = -1 := by simpa using h
    have : ¬ z * reverse z = 1 := by
      rw [h']
      exact (s21_ne_neg_of_isUnit isUnit_one).symm
    simp [s21_nrm, this]

end HelpersIntegral

section Integral

variable (n : ℕ)

/-- **The integral spin group** (§2.1): the paper's
`Spin(V) = {x ∈ C(V)^even : x x* = 1, x V x* ⊆ V}` is the model's `SpinZ n` (elements of
`Spin(V_ℚ)` lying in `CZ n` and preserving the lattice `VZ n`). For `n = 0` the model's `Spin(V_ℚ)`
is `{1}`, hence `0 < n`. -/
theorem mem_SpinZ_iff (hn : 0 < n) (x : C ℚ n) :
    (∃ g ∈ SpinZ n, (g : C ℚ n) = x) ↔
      x ∈ CZ n ∧ x ∈ evenOdd (Q ℚ n) 0 ∧ x * star x = 1 ∧
        ∀ v ∈ VZ n, ∃ u ∈ VZ n, x * ι (Q ℚ n) v * star x = ι (Q ℚ n) u := by
  constructor
  · rintro ⟨g, ⟨hgC, hgV⟩, rfl⟩
    obtain ⟨he, hs, -⟩ := (mem_spin_iff ℚ n hn g).mp g.2
    exact ⟨hgC, he, hs, fun v hv => ⟨rho ℚ n g v, hgV v hv, (ι_rho ℚ n g v).symm⟩⟩
  · rintro ⟨hC, he, hs, hV⟩
    have hspin : x ∈ spinGroup (Q ℚ n) := (mem_spin_iff ℚ n hn x).mpr
      ⟨he, hs, s21_forall_of_VZ _ _ fun v hv => (hV v hv).imp fun u hu => hu.2⟩
    refine ⟨⟨x, hspin⟩, ⟨hC, fun v hv => ?_⟩, rfl⟩
    obtain ⟨u, hu, hxu⟩ := hV v hv
    have h : ι (Q ℚ n) (rho ℚ n ⟨x, hspin⟩ v) = ι (Q ℚ n) u := by
      rw [ι_rho]
      exact hxu
    rw [ι_injective (Q ℚ n) h]
    exact hu

/-- The integral Clifford group lies in the rational one. -/
theorem s21_mem_cliffordGroup_of_Z {x : (C ℚ n)ˣ} (hx : x ∈ cliffordGroupZ n) :
    x ∈ cliffordGroup ℚ n :=
  s21_forall_of_VZ _ _ fun v hv => (hx.2.2 v hv).imp fun _ hu => hu.2

/-- **The norm character `N : G(V) → {±1}`** (§2.1): for `g` in the integral Clifford group,
`N(g) = g τ(g) = ±1`. -/
theorem mul_reverse_eq_one_or_neg_one_of_mem_cliffordGroupZ (x : (C ℚ n)ˣ)
    (hx : x ∈ cliffordGroupZ n) :
    (x : C ℚ n) * reverse (x : C ℚ n) = 1 ∨ (x : C ℚ n) * reverse (x : C ℚ n) = -1 := by
  -- `N(x) = c` and `N(x⁻¹) = c'` are scalars (`exists_mul_reverse_eq_algebraMap`), with `c' c = 1`;
  -- both lie in `C(V) ∩ ℚ = ℤ`, so `c = ±1`.
  obtain ⟨c, hc⟩ := exists_mul_reverse_eq_algebraMap ℚ n x (s21_mem_cliffordGroup_of_Z n hx)
  have hxi : x⁻¹ ∈ cliffordGroupZ n := inv_mem hx
  obtain ⟨c', hc'⟩ :=
    exists_mul_reverse_eq_algebraMap ℚ n x⁻¹ (s21_mem_cliffordGroup_of_Z n hxi)
  have hcc : algebraMap ℚ (C ℚ n) (c' * c) = 1 := by
    rw [map_mul, ← hc, ← mul_assoc, Algebra.commutes, ← hc', Units.mul_inv_cancel_left,
      ← reverse.map_mul, Units.mul_inv, reverse.map_one]
  have hcc' : c' * c = 1 := algebraMap_injective (Q ℚ n) (hcc.trans (map_one _).symm)
  obtain ⟨z, hz⟩ := s21_int_of_algebraMap_mem_CZ (n := n)
    (hc ▸ Subring.mul_mem _ hx.1 (s21_reverse_mem_CZ hx.1))
  obtain ⟨z', hz'⟩ := s21_int_of_algebraMap_mem_CZ (n := n)
    (hc' ▸ Subring.mul_mem _ hxi.1 (s21_reverse_mem_CZ hxi.1))
  have hzz : z * z' = 1 := by
    have : ((z * z' : ℤ) : ℚ) = 1 := by rw [Int.cast_mul, ← hz, ← hz', mul_comm, hcc']
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hzz with h | h
  · left; rw [hc, hz, h, Int.cast_one, map_one]
  · right; rw [hc, hz, h, Int.cast_neg, Int.cast_one, map_neg, map_one]

/-- For `x` in the Clifford group `G(V_F)`, `x⁻¹ α(x)` commutes with `V`, hence is a scalar
`c` with `c² = 1`: elements of `G(V_F)` are even or odd. -/
theorem s21_involute_eq_or_neg {F : Type*} [Field F] [CharZero F] {n : ℕ} (x : (C F n)ˣ)
    (hx : x ∈ cliffordGroup F n) :
    involute (x : C F n) = x ∨ involute (x : C F n) = -x := by
  have hinvinv : involute ((x⁻¹ : (C F n)ˣ) : C F n) * involute (x : C F n) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hcomm : ∀ v : V F n, (((x⁻¹ : (C F n)ˣ) : C F n) * involute (x : C F n)) * ι (Q F n) v =
      ι (Q F n) v * (((x⁻¹ : (C F n)ˣ) : C F n) * involute (x : C F n)) := by
    intro v
    obtain ⟨u, hu⟩ := hx v
    have hu' : involute (x : C F n) * ι (Q F n) v * involute ((x⁻¹ : (C F n)ˣ) : C F n) =
        ι (Q F n) u := by
      have := congrArg involute hu
      rw [map_mul, map_mul, involute_ι, involute_ι] at this
      simpa only [mul_neg, neg_mul, neg_inj] using this
    calc ((x⁻¹ : (C F n)ˣ) : C F n) * involute (x : C F n) * ι (Q F n) v
        = ((x⁻¹ : (C F n)ˣ) : C F n) * (involute (x : C F n) * ι (Q F n) v *
            involute ((x⁻¹ : (C F n)ˣ) : C F n)) * involute (x : C F n) := by
          simp only [mul_assoc, hinvinv, mul_one]
      _ = ((x⁻¹ : (C F n)ˣ) : C F n) * ((x : C F n) * ι (Q F n) v *
            ((x⁻¹ : (C F n)ˣ) : C F n)) * involute (x : C F n) := by rw [hu', hu]
      _ = ι (Q F n) v * (((x⁻¹ : (C F n)ˣ) : C F n) * involute (x : C F n)) := by
          simp only [← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨c, hc⟩ := s21_eq_algebraMap_of_commute _ hcomm
  have h1 : involute (x : C F n) = algebraMap F (C F n) c * x := by
    rw [Algebra.commutes, ← hc, Units.mul_inv_cancel_left]
  have h2 : (x : C F n) = algebraMap F (C F n) (c * c) * x := by
    have := congrArg involute h1
    rw [involute_involute, map_mul, AlgHom.commutes, h1, ← mul_assoc, ← map_mul] at this
    exact this
  have h3 : algebraMap F (C F n) (c * c) = 1 := by
    have := congrArg (· * ((x⁻¹ : (C F n)ˣ) : C F n)) h2
    simp only [mul_assoc, Units.mul_inv, mul_one] at this
    exact this.symm
  have h4 : c * c = 1 := algebraMap_injective (Q F n) (h3.trans (map_one _).symm)
  rcases mul_self_eq_one_iff.mp h4 with h | h
  · left; rw [h1, h, map_one, one_mul]
  · right; rw [h1, h, map_neg, map_one, neg_one_mul]

/-- `ι v` lies in the integral Clifford group if `v ∈ V` and `Q(v) = ±1`. -/
theorem s21_unitι_mem_cliffordGroupZ {v : V ℚ n} (hvZ : v ∈ VZ n)
    (hv : Q ℚ n v = 1 ∨ Q ℚ n v = -1) (hQv : Q ℚ n v ≠ 0) :
    s21_unitι v hQv ∈ cliffordGroupZ n := by
  refine ⟨s21_ι_mem_CZ hvZ, ?_, fun l hl => ?_⟩
  · show (Q ℚ n v)⁻¹ • ι (Q ℚ n) v ∈ CZ n
    rcases hv with h | h <;> rw [h]
    · rw [inv_one, one_smul]; exact s21_ι_mem_CZ hvZ
    · rw [inv_neg, inv_one, neg_one_smul]; exact Subring.neg_mem _ (s21_ι_mem_CZ hvZ)
  · refine ⟨_, ?_, s21_conj_ι rfl hQv l⟩
    have hrefl := s21_refl_mem_VZ hvZ hl hv
    rcases hv with h | h <;> rw [h] at hrefl ⊢
    · rw [inv_one, one_smul]; exact hrefl
    · rw [inv_neg, inv_one, neg_one_smul]; exact neg_mem hrefl

theorem s21_involute_eq_par {x : (C ℚ n)ˣ} (hx : x ∈ cliffordGroup ℚ n) :
    involute (x : C ℚ n) = (((s21_par (x : C ℚ n)) : ℤ) : ℚ) • (x : C ℚ n) := by
  rcases s21_involute_eq_or_neg x hx with h | h
  · rw [s21_par_of _ x.isUnit 1 (by simpa using h)]
    simpa using h
  · rw [s21_par_of _ x.isUnit (-1) (by simpa using h)]
    simpa using h

theorem s21_mul_reverse_eq_nrm {x : (C ℚ n)ˣ} (hx : x ∈ cliffordGroupZ n) :
    (x : C ℚ n) * reverse (x : C ℚ n) =
      algebraMap ℚ (C ℚ n) (((s21_nrm (x : C ℚ n)) : ℤ) : ℚ) := by
  rcases mul_reverse_eq_one_or_neg_one_of_mem_cliffordGroupZ n x hx with h | h
  · rw [s21_nrm_of _ 1 (by simpa using h)]
    simpa using h
  · rw [s21_nrm_of _ (-1) (by simpa using h)]
    simpa using h

/-- The parity and the norm character: `G(V) → {±1} × {±1}`. -/
noncomputable def s21_sign : cliffordGroupZ n →* ℤˣ × ℤˣ where
  toFun x := (s21_par ((x : (C ℚ n)ˣ) : C ℚ n), s21_nrm ((x : (C ℚ n)ˣ) : C ℚ n))
  map_one' := by
    have h1 : s21_par (1 : C ℚ n) = 1 := s21_par_of _ isUnit_one 1 (by simp)
    have h2 : s21_nrm (1 : C ℚ n) = 1 := s21_nrm_of _ 1 (by simp)
    simp only [OneMemClass.coe_one, Units.val_one, h1, h2, Prod.mk_one_one]
  map_mul' x y := by
    have hxG := s21_mem_cliffordGroup_of_Z n x.2
    have hyG := s21_mem_cliffordGroup_of_Z n y.2
    refine Prod.ext ?_ ?_
    · show s21_par (((x * y : cliffordGroupZ n) : (C ℚ n)ˣ) : C ℚ n) =
        s21_par ((x : (C ℚ n)ˣ) : C ℚ n) * s21_par ((y : (C ℚ n)ˣ) : C ℚ n)
      apply s21_par_of _ ((x * y : cliffordGroupZ n) : (C ℚ n)ˣ).isUnit
      rw [Subgroup.coe_mul, Units.val_mul, map_mul, s21_involute_eq_par n hxG,
        s21_involute_eq_par n hyG, smul_mul_smul_comm, Units.val_mul, Int.cast_mul]
    · show s21_nrm (((x * y : cliffordGroupZ n) : (C ℚ n)ˣ) : C ℚ n) =
        s21_nrm ((x : (C ℚ n)ˣ) : C ℚ n) * s21_nrm ((y : (C ℚ n)ˣ) : C ℚ n)
      apply s21_nrm_of
      rw [Subgroup.coe_mul, Units.val_mul, reverse.map_mul,
        show ((x : (C ℚ n)ˣ) : C ℚ n) * ((y : (C ℚ n)ˣ) : C ℚ n) *
            (reverse ((y : (C ℚ n)ˣ) : C ℚ n) * reverse ((x : (C ℚ n)ˣ) : C ℚ n)) =
          ((x : (C ℚ n)ˣ) : C ℚ n) * (((y : (C ℚ n)ˣ) : C ℚ n) *
            reverse ((y : (C ℚ n)ˣ) : C ℚ n)) * reverse ((x : (C ℚ n)ˣ) : C ℚ n) by
          simp only [mul_assoc],
        s21_mul_reverse_eq_nrm n y.2, ← Algebra.commutes, mul_assoc,
        s21_mul_reverse_eq_nrm n x.2, ← map_mul, Units.val_mul, Int.cast_mul]
      congr 1
      ring

theorem s21_sign_ker (hn : 0 < n) :
    (s21_sign n).ker =
      ((SpinZ n).map (spinGroup.toUnits (Q := Q ℚ n))).subgroupOf (cliffordGroupZ n) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hxG := s21_mem_cliffordGroup_of_Z n x.2
  have hpar := s21_involute_eq_par n hxG
  have hnrm := s21_mul_reverse_eq_nrm n x.2
  constructor
  · intro h
    have h1 : s21_par ((x : (C ℚ n)ˣ) : C ℚ n) = 1 := congrArg Prod.fst h
    have h2 : s21_nrm ((x : (C ℚ n)ˣ) : C ℚ n) = 1 := congrArg Prod.snd h
    rw [h1] at hpar
    rw [h2] at hnrm
    simp only [Units.val_one, Int.cast_one, one_smul] at hpar
    simp only [Units.val_one, Int.cast_one, map_one] at hnrm
    have heven := s21_mem_even_of_involute_eq hpar
    have hstar : star ((x : (C ℚ n)ˣ) : C ℚ n) = reverse ((x : (C ℚ n)ˣ) : C ℚ n) := by
      rw [star_def, hpar]
    have hinv : ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) = reverse ((x : (C ℚ n)ˣ) : C ℚ n) :=
      Units.inv_eq_of_mul_eq_one_right hnrm
    obtain ⟨g, hg, hgx⟩ := (mem_SpinZ_iff n hn _).mpr ⟨x.2.1, heven, by rw [hstar, hnrm],
      fun v hv => by
        obtain ⟨u, hu, huv⟩ := x.2.2.2 v hv
        exact ⟨u, hu, by rw [hstar, ← hinv]; exact huv⟩⟩
    exact ⟨g, hg, Units.ext hgx⟩
  · rintro ⟨g, hg, hgx⟩
    have hgx' : (g : C ℚ n) = ((x : (C ℚ n)ˣ) : C ℚ n) := by rw [← hgx]; rfl
    have hev : (g : C ℚ n) ∈ evenOdd (Q ℚ n) 0 := ((mem_spin_iff ℚ n hn g).mp g.2).1
    have hs : (g : C ℚ n) * star (g : C ℚ n) = 1 := spinGroup.mul_star_self_of_mem g.2
    rw [star_def, involute_eq_of_mem_even hev] at hs
    have h1 : s21_par ((x : (C ℚ n)ˣ) : C ℚ n) = 1 :=
      s21_par_of _ (x : (C ℚ n)ˣ).isUnit 1 (by rw [← hgx', involute_eq_of_mem_even hev]; simp)
    have h2 : s21_nrm ((x : (C ℚ n)ˣ) : C ℚ n) = 1 :=
      s21_nrm_of _ 1 (by rw [← hgx', hs]; simp)
    show (s21_par _, s21_nrm _) = 1
    rw [h1, h2]
    rfl

theorem s21_sign_surjective (hn : 0 < n) : Function.Surjective (s21_sign n) := by
  set i₀ : Fin (2 * n) := ⟨0, by omega⟩
  set a : V ℚ n := (f ℚ n i₀, e ℚ n i₀)
  set b : V ℚ n := (-f ℚ n i₀, e ℚ n i₀)
  have ha : Q ℚ n a = 1 := by
    simp [a, QuadraticForm.dualProd_apply, s21_f_e]
  have hb : Q ℚ n b = -1 := by
    simp [b, QuadraticForm.dualProd_apply, s21_f_e]
  have haZ : a ∈ VZ n := by
    have : a = (f ℚ n i₀, 0) + (0, e ℚ n i₀) := by simp [a]
    rw [this]
    exact add_mem (s21_f_mem_VZ i₀) (s21_e_mem_VZ i₀)
  have hbZ : b ∈ VZ n := by
    have : b = -(f ℚ n i₀, 0) + (0, e ℚ n i₀) := by simp [b]
    rw [this]
    exact add_mem (neg_mem (s21_f_mem_VZ i₀)) (s21_e_mem_VZ i₀)
  have ha0 : Q ℚ n a ≠ 0 := by rw [ha]; exact one_ne_zero
  have hb0 : Q ℚ n b ≠ 0 := by rw [hb]; norm_num
  let A : cliffordGroupZ n := ⟨s21_unitι a ha0, s21_unitι_mem_cliffordGroupZ n haZ (Or.inl ha) ha0⟩
  let B : cliffordGroupZ n := ⟨s21_unitι b hb0, s21_unitι_mem_cliffordGroupZ n hbZ (Or.inr hb) hb0⟩
  have hA : s21_sign n A = (-1, 1) := by
    show (s21_par (ι (Q ℚ n) a), s21_nrm (ι (Q ℚ n) a)) = (-1, 1)
    rw [s21_par_of (ι (Q ℚ n) a) (s21_unitι a ha0).isUnit (-1) (by simp),
      s21_nrm_of _ 1 (by rw [reverse_ι, ι_sq_scalar, ha]; simp)]
  have hB : s21_sign n B = (-1, -1) := by
    show (s21_par (ι (Q ℚ n) b), s21_nrm (ι (Q ℚ n) b)) = (-1, -1)
    rw [s21_par_of (ι (Q ℚ n) b) (s21_unitι b hb0).isUnit (-1) (by simp),
      s21_nrm_of _ (-1) (by rw [reverse_ι, ι_sq_scalar, hb]; simp)]
  rintro ⟨u, w⟩
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or w with rfl | rfl
  · exact ⟨1, map_one _⟩
  · refine ⟨A * B, ?_⟩
    rw [map_mul, hA, hB]
    exact Prod.ext (by simp) (by simp)
  · exact ⟨A, hA⟩
  · exact ⟨B, hB⟩

/-- "**The integral spin group is its index four subgroup**" (§2.1): `Spin(V)` (embedded in
`C(V_ℚ)ˣ`) has index `4` in `G(V)`. For `n = 0` there are no vectors with `(v, v)_V = ±2` and the
index is `1`, hence `0 < n`. -/
theorem spinZ_relIndex_cliffordGroupZ (hn : 0 < n) :
    ((SpinZ n).map (spinGroup.toUnits (Q := Q ℚ n))).relIndex (cliffordGroupZ n) = 4 := by
  -- `Spin(V)` is the kernel of `(parity, N) : G(V) → {±1} × {±1}`, which is onto.
  rw [Subgroup.relIndex, ← s21_sign_ker n hn, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (s21_sign_surjective n hn), Subgroup.card_top, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- If `v ∈ V` (integral) and `(v, v)_V = ±2`, then `v` belongs to the integral Clifford group
`G(V)` (§2.1; stated in the paper for `(v, v)_V = 2`, and implicit for `-2` in "`-ρ(v)` is the
reflection with respect to `v^⊥`"). -/
theorem exists_mem_cliffordGroupZ_of_pairing_eq_two (v : V ℚ n) (hvZ : v ∈ VZ n)
    (hv : pairing ℚ n v v = 2 ∨ pairing ℚ n v v = -2) :
    ∃ x ∈ cliffordGroupZ n, (x : C ℚ n) = ι (Q ℚ n) v := by
  have hQ := s21_Q_of_pairing v hv
  have hQv : Q ℚ n v ≠ 0 := by rcases hQ with h | h <;> rw [h] <;> norm_num
  exact ⟨s21_unitι v hQv, s21_unitι_mem_cliffordGroupZ n hvZ hQ hQv, rfl⟩

/-- If `(v₁, v₁)_V = (v₂, v₂)_V = 2`, or `(v₁, v₁)_V = (v₂, v₂)_V = -2` (with `v₁, v₂` integral),
then `v₁ · v₂` belongs to the integral `Spin(V)` (§2.1). -/
theorem exists_spinZ_eq_ι_mul_ι (v₁ v₂ : V ℚ n) (h₁ : v₁ ∈ VZ n) (h₂ : v₂ ∈ VZ n)
    (h : (pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
      (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2)) :
    ∃ g ∈ SpinZ n, (g : C ℚ n) = ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂ := by
  have hQ : (Q ℚ n v₁ = 1 ∧ Q ℚ n v₂ = 1) ∨ (Q ℚ n v₁ = -1 ∧ Q ℚ n v₂ = -1) :=
    h.imp (fun h => ⟨s21_Q_eq_one h.1, s21_Q_eq_one h.2⟩)
      (fun h => ⟨s21_Q_eq_neg_one h.1, s21_Q_eq_neg_one h.2⟩)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `V = 0` for `n = 0`
    exfalso
    obtain ⟨θ, w⟩ := v₁
    have hw : w = 0 := funext fun i => absurd i.isLt (by omega)
    rcases hQ with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      simp [hw, QuadraticForm.dualProd_apply] at h1
  have hQ₁ : Q ℚ n v₁ = 1 ∨ Q ℚ n v₁ = -1 := hQ.imp (fun h => h.1) (fun h => h.1)
  have hQ₂ : Q ℚ n v₂ = 1 ∨ Q ℚ n v₂ = -1 := hQ.imp (fun h => h.2) (fun h => h.2)
  have hprod : Q ℚ n v₂ * Q ℚ n v₁ = 1 := by
    rcases hQ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hstar : star (ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂) = ι (Q ℚ n) v₂ * ι (Q ℚ n) v₁ := by
    rw [star_mul, star_ι, star_ι, neg_mul_neg]
  rw [mem_SpinZ_iff n hn]
  refine ⟨Subring.mul_mem _ (s21_ι_mem_CZ h₁) (s21_ι_mem_CZ h₂),
    ι_mul_ι_mem_evenOdd_zero _ _ _, ?_, fun l hl => ?_⟩
  · rw [hstar, mul_assoc, ← mul_assoc (ι (Q ℚ n) v₂), ι_sq_scalar, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, ι_sq_scalar, ← map_mul, hprod, map_one]
  · rw [hstar]
    have e1 : ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂ * ι (Q ℚ n) l * (ι (Q ℚ n) v₂ * ι (Q ℚ n) v₁) =
        ι (Q ℚ n) v₁ * (ι (Q ℚ n) v₂ * ι (Q ℚ n) l * ι (Q ℚ n) v₂) * ι (Q ℚ n) v₁ := by
      simp only [mul_assoc]
    rw [e1, ι_mul_ι_mul_ι, ι_mul_ι_mul_ι]
    exact ⟨_, s21_refl_mem_VZ h₁ (s21_refl_mem_VZ h₂ hl hQ₂) hQ₁, rfl⟩

/-! ### Generation of the integral spin group (helpers, prefix `s21_`)

`Spin(V)` is generated by the products `v₁ v₂` with `(v₁,v₁)_V = (v₂,v₂)_V = ±2`. The paper states
this without proof; we prove it for the hyperbolic lattice `V = U^{⊕ 2n}`, `n ≥ 2`, by the
Euclidean algorithm (in the style of the proof of Wall's theorem). With `ρ(v₁ v₂) = M_{v₁} M_{v₂}`,
`M_u(x) = (u, x) u - Q(u) x`, the realizable isometries contain

* the Eichler transformations `E(eⱼ, a)`, `a ∈ V`, `a ⊥ eⱼ` (`s21_Real_eich_E`), since
  `E(e, u) = M_{u - Q(u) e} M_u` for `Q(u) = ±1` and `a ↦ E(e, a)` is additive;
* the swap `eⱼ ↔ fⱼ`, `e_l ↔ f_l` and the negation of two planes (`s21_swap`, `s21_negE`).

Phase `k` (`s21_phase`) moves `ρ(g) e_k` to `e_k` by the Euclidean algorithm on its coordinates
(`s21_euclid`) and then `ρ(g) f_k` to `f_k` by an Eichler transformation, fixing the planes `< k`.
After the phases `0, …, 2n - 2`, `ρ(g)` acts on the last plane only, where it is the identity
(`s21_final`): the other possibilities (`-1`, the swap, minus the swap) do not lift to `Spin`. -/

section Generation

variable {n}

/-- `e_i ∈ V`. -/
noncomputable def s21_E (i : Fin (2 * n)) : V ℚ n := (0, e ℚ n i)

/-- `f_i ∈ V`. -/
noncomputable def s21_F (i : Fin (2 * n)) : V ℚ n := (f ℚ n i, 0)

@[simp] theorem s21_E_fst (i : Fin (2 * n)) : (s21_E i : V ℚ n).1 = 0 := rfl

@[simp] theorem s21_E_snd (i : Fin (2 * n)) : (s21_E i : V ℚ n).2 = e ℚ n i := rfl

@[simp] theorem s21_F_fst (i : Fin (2 * n)) : (s21_F i : V ℚ n).1 = f ℚ n i := rfl

@[simp] theorem s21_F_snd (i : Fin (2 * n)) : (s21_F i : V ℚ n).2 = 0 := rfl

attribute [local simp] s21_f_e

theorem s21_pairing_E (x : V ℚ n) (i : Fin (2 * n)) :
    pairing ℚ n x (s21_E i) = x.1 (e ℚ n i) := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, s21_polar_apply]
  simp [s21_E]

theorem s21_pairing_F (x : V ℚ n) (i : Fin (2 * n)) : pairing ℚ n x (s21_F i) = x.2 i := by
  rw [pairing, QuadraticMap.polarBilin_apply_apply, s21_polar_apply]
  simp [s21_F, f]

theorem s21_F_pairing (x : V ℚ n) (i : Fin (2 * n)) : pairing ℚ n (s21_F i) x = x.2 i := by
  rw [s21_pairing_comm, s21_pairing_F]

@[simp] theorem s21_E_E (i j : Fin (2 * n)) : pairing ℚ n (s21_E i) (s21_E j) = 0 := by
  rw [s21_pairing_E]; simp [s21_E]

@[simp] theorem s21_F_F (i j : Fin (2 * n)) : pairing ℚ n (s21_F i) (s21_F j) = 0 := by
  rw [s21_pairing_F]; simp [s21_F]

@[simp] theorem s21_E_F (i j : Fin (2 * n)) :
    pairing ℚ n (s21_E i) (s21_F j) = if i = j then 1 else 0 := by
  rw [s21_pairing_F]
  simp only [s21_E, e, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

@[simp] theorem s21_F_E (i j : Fin (2 * n)) :
    pairing ℚ n (s21_F i) (s21_E j) = if i = j then 1 else 0 := by
  rw [s21_pairing_E]
  exact s21_f_e i j

@[simp] theorem s21_Q_E (i : Fin (2 * n)) : Q ℚ n (s21_E i) = 0 := by
  simp [s21_E, QuadraticForm.dualProd_apply]

@[simp] theorem s21_Q_F (i : Fin (2 * n)) : Q ℚ n (s21_F i) = 0 := by
  simp [s21_F, QuadraticForm.dualProd_apply]

theorem s21_E_mem (i : Fin (2 * n)) : s21_E i ∈ VZ n := s21_e_mem_VZ i

theorem s21_F_mem (i : Fin (2 * n)) : s21_F i ∈ VZ n := s21_f_mem_VZ i

/-- `Q(v) = (v, v)_V / 2`. -/
theorem s21_Q_eq_half (v : V ℚ n) : Q ℚ n v = pairing ℚ n v v / 2 := by
  rw [s21_pairing_self]; ring

/-- `Q(a + b) = Q(a) + Q(b) + (a, b)_V`. -/
theorem s21_Q_add (a b : V ℚ n) : Q ℚ n (a + b) = Q ℚ n a + Q ℚ n b + pairing ℚ n a b := by
  rw [s21_Q_eq_half, s21_Q_eq_half a, s21_Q_eq_half b]
  simp only [map_add, LinearMap.add_apply]
  rw [s21_pairing_comm b a]
  ring

/-- The coordinates: `v = Σ (v, eᵢ) fᵢ + Σ (v, fᵢ) eᵢ`. -/
theorem s21_decomp (v : V ℚ n) :
    v = ∑ i, pairing ℚ n v (s21_E i) • s21_F i + ∑ i, pairing ℚ n v (s21_F i) • s21_E i := by
  simp only [s21_pairing_E, s21_pairing_F]
  exact s21_V_decomp v

theorem s21_linearMap_ext {σ τ : V ℚ n →ₗ[ℚ] V ℚ n} (hE : ∀ i, σ (s21_E i) = τ (s21_E i))
    (hF : ∀ i, σ (s21_F i) = τ (s21_F i)) : σ = τ := by
  refine LinearMap.ext fun v => ?_
  rw [s21_decomp v]
  simp only [map_add, map_sum, map_smul, hE, hF]

theorem s21_coord_E_int {x : V ℚ n} (hx : x ∈ VZ n) (i : Fin (2 * n)) :
    ∃ z : ℤ, pairing ℚ n x (s21_E i) = z := by
  rw [s21_pairing_E]; exact hx.1 i

theorem s21_coord_F_int {x : V ℚ n} (hx : x ∈ VZ n) (i : Fin (2 * n)) :
    ∃ z : ℤ, pairing ℚ n x (s21_F i) = z := by
  rw [s21_pairing_F]; exact hx.2 i

/-! #### The action `ρ` -/

theorem s21_rho_mul (g h : Spin ℚ n) (x : V ℚ n) :
    rho ℚ n (g * h) x = rho ℚ n g (rho ℚ n h x) := by
  simp [rho, spinVectorAction_mul]

theorem s21_rho_one (x : V ℚ n) : rho ℚ n 1 x = x := by
  simp [rho, spinVectorAction_one]

theorem s21_pairing_rho (g : Spin ℚ n) (a b : V ℚ n) :
    pairing ℚ n (rho ℚ n g a) (rho ℚ n g b) = pairing ℚ n a b := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, rho, ← map_add,
    spinVectorAction_map_app]

/-! #### Realizable isometries -/

/-- The generating set of the statement. -/
def s21_T (n : ℕ) : Set (Spin ℚ n) :=
  {g : Spin ℚ n | ∃ v₁ ∈ VZ n, ∃ v₂ ∈ VZ n,
      ((pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
        (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2)) ∧
      (g : C ℚ n) = ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂}

theorem s21_closure_le : Subgroup.closure (s21_T n) ≤ SpinZ n := by
  rw [Subgroup.closure_le]
  rintro g ⟨v₁, h₁, v₂, h₂, h, hg⟩
  obtain ⟨g', hg', hg'eq⟩ := exists_spinZ_eq_ι_mul_ι n v₁ v₂ h₁ h₂ h
  have : g = g' := Subtype.ext (hg.trans hg'eq.symm)
  rw [this]
  exact hg'

/-- `σ` is realized by an element of the subgroup generated by the `v₁ v₂`. -/
def s21_Real (σ : V ℚ n →ₗ[ℚ] V ℚ n) : Prop :=
  ∃ h ∈ Subgroup.closure (s21_T n), ∀ x, rho ℚ n h x = σ x

theorem s21_Real.mem_VZ {σ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) {x : V ℚ n}
    (hx : x ∈ VZ n) : σ x ∈ VZ n := by
  obtain ⟨h, hh, hσ⟩ := hσ
  rw [← hσ]
  exact (s21_closure_le hh).2 x hx

theorem s21_Real.pairing_eq {σ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) (x y : V ℚ n) :
    pairing ℚ n (σ x) (σ y) = pairing ℚ n x y := by
  obtain ⟨h, hh, hσ⟩ := hσ
  rw [← hσ, ← hσ]
  exact s21_pairing_rho h x y

theorem s21_Real.Q_eq {σ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) (x : V ℚ n) :
    Q ℚ n (σ x) = Q ℚ n x := by
  rw [s21_Q_eq_half, s21_Q_eq_half x, hσ.pairing_eq]

theorem s21_Real_id : s21_Real (LinearMap.id : V ℚ n →ₗ[ℚ] V ℚ n) :=
  ⟨1, one_mem _, fun x => s21_rho_one x⟩

theorem s21_Real.comp {σ τ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) (hτ : s21_Real τ) :
    s21_Real (σ ∘ₗ τ) := by
  obtain ⟨g, hg, hgσ⟩ := hσ
  obtain ⟨h, hh, hhτ⟩ := hτ
  exact ⟨g * h, mul_mem hg hh, fun x => by rw [s21_rho_mul, hhτ, hgσ]; rfl⟩

theorem s21_Real.inv {σ τ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) (hστ : ∀ x, τ (σ x) = x) :
    s21_Real τ := by
  obtain ⟨g, hg, hgσ⟩ := hσ
  refine ⟨g⁻¹, inv_mem hg, fun x => ?_⟩
  have h1 : rho ℚ n g (rho ℚ n g⁻¹ x) = x := by
    rw [← s21_rho_mul, mul_inv_cancel, s21_rho_one]
  calc rho ℚ n g⁻¹ x = τ (σ (rho ℚ n g⁻¹ x)) := (hστ _).symm
    _ = τ x := by rw [← hgσ, h1]

/-- `M_u(x) = (u, x) u - Q(u) x`, so that `ι u ι x ι u = ι (M_u x)`. -/
noncomputable def s21_M (u : V ℚ n) : V ℚ n →ₗ[ℚ] V ℚ n :=
  LinearMap.smulRight (pairing ℚ n u) u - Q ℚ n u • LinearMap.id

theorem s21_M_apply (u x : V ℚ n) : s21_M u x = pairing ℚ n u x • u - Q ℚ n u • x := by
  simp [s21_M]

theorem s21_ι_M (u x : V ℚ n) :
    ι (Q ℚ n) u * ι (Q ℚ n) x * ι (Q ℚ n) u = ι (Q ℚ n) (s21_M u x) := by
  rw [ι_mul_ι_mul_ι, s21_M_apply, pairing, QuadraticMap.polarBilin_apply_apply]

theorem s21_M_of_perp {u x : V ℚ n} (h : pairing ℚ n u x = 0) : s21_M u x = -(Q ℚ n u) • x := by
  rw [s21_M_apply, h, zero_smul, zero_sub, neg_smul]

/-- The generators act by `M_{v₁} M_{v₂}`. -/
theorem s21_Real_gen {v₁ v₂ : V ℚ n} (h₁ : v₁ ∈ VZ n) (h₂ : v₂ ∈ VZ n)
    (hq : (Q ℚ n v₁ = 1 ∧ Q ℚ n v₂ = 1) ∨ (Q ℚ n v₁ = -1 ∧ Q ℚ n v₂ = -1)) :
    s21_Real (s21_M v₁ ∘ₗ s21_M v₂) := by
  have hp : (pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
      (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2) := by
    rw [s21_pairing_self, s21_pairing_self]
    rcases hq with ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [a, b]; norm_num
    · right; rw [a, b]; norm_num
  obtain ⟨g, -, hgeq⟩ := exists_spinZ_eq_ι_mul_ι n v₁ v₂ h₁ h₂ hp
  refine ⟨g, Subgroup.subset_closure ⟨v₁, h₁, v₂, h₂, hp, hgeq⟩, fun x => ?_⟩
  apply ι_injective (Q ℚ n)
  rw [ι_rho, hgeq, star_mul, star_ι, star_ι, neg_mul_neg, LinearMap.comp_apply, ← s21_ι_M,
    ← s21_ι_M]
  simp only [mul_assoc]

/-! #### Eichler transformations -/

/-- The Eichler transformation `E(e, a)(x) = x + (x, e) a - (x, a) e - Q(a) (x, e) e`. -/
noncomputable def s21_eich (e a : V ℚ n) : V ℚ n →ₗ[ℚ] V ℚ n :=
  LinearMap.id + LinearMap.smulRight ((pairing ℚ n).flip e) a -
    LinearMap.smulRight ((pairing ℚ n).flip a) e -
      Q ℚ n a • LinearMap.smulRight ((pairing ℚ n).flip e) e

theorem s21_eich_apply (e a x : V ℚ n) : s21_eich e a x =
    x + pairing ℚ n x e • a - pairing ℚ n x a • e - (Q ℚ n a * pairing ℚ n x e) • e := by
  simp [s21_eich, mul_smul]

theorem s21_eich_of_perp {e a x : V ℚ n} (he : pairing ℚ n x e = 0) (ha : pairing ℚ n x a = 0) :
    s21_eich e a x = x := by
  rw [s21_eich_apply, he, ha]
  simp

/-- `E(e, u) = M_{u - Q(u) e} M_u` for `u ⊥ e` with `Q(u) = ±1`, `e` isotropic. -/
theorem s21_eich_eq_M {e u : V ℚ n} (he : Q ℚ n e = 0) (hue : pairing ℚ n u e = 0)
    (hq : Q ℚ n u = 1 ∨ Q ℚ n u = -1) :
    s21_M (u - Q ℚ n u • e) ∘ₗ s21_M u = s21_eich e u := by
  have hee : pairing ℚ n e e = 0 := by rw [s21_pairing_self, he, mul_zero]
  have heu : pairing ℚ n e u = 0 := by rw [s21_pairing_comm, hue]
  have huu : pairing ℚ n u u = 2 * Q ℚ n u := s21_pairing_self u
  have hQ' : Q ℚ n (u - Q ℚ n u • e) = Q ℚ n u := by
    rw [s21_Q_eq_half, s21_Q_eq_half u]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee,
      hue, heu]
    ring
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, s21_M_apply, s21_M_apply, hQ', s21_eich_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    heu, huu]
  rw [s21_pairing_comm e x, s21_pairing_comm u x]
  rcases hq with h | h <;> rw [h] <;> module

theorem s21_eich_comp {e a b : V ℚ n} (he : Q ℚ n e = 0) (ha : pairing ℚ n a e = 0)
    (hb : pairing ℚ n b e = 0) : s21_eich e a ∘ₗ s21_eich e b = s21_eich e (a + b) := by
  have hee : pairing ℚ n e e = 0 := by rw [s21_pairing_self, he, mul_zero]
  have hea : pairing ℚ n e a = 0 := by rw [s21_pairing_comm, ha]
  have heb : pairing ℚ n e b = 0 := by rw [s21_pairing_comm, hb]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, s21_eich_apply, s21_eich_apply, s21_eich_apply, s21_Q_add]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hee, hb, hea]
  rw [s21_pairing_comm b a]
  module

theorem s21_eich_zero (e : V ℚ n) : s21_eich e 0 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [s21_eich_apply]

theorem s21_Q_sub_smul {e u : V ℚ n} (he : Q ℚ n e = 0) (hue : pairing ℚ n u e = 0) (c : ℚ) :
    Q ℚ n (u - c • e) = Q ℚ n u := by
  have hee : pairing ℚ n e e = 0 := by rw [s21_pairing_self, he, mul_zero]
  have heu : pairing ℚ n e u = 0 := by rw [s21_pairing_comm, hue]
  rw [s21_Q_eq_half, s21_Q_eq_half u]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee,
    hue, heu]
  ring

/-- The `a ⊥ e` with `E(e, a)` realizable form an additive subgroup. -/
def s21_Lam (e : V ℚ n) (he : Q ℚ n e = 0) : AddSubgroup (V ℚ n) where
  carrier := {a | pairing ℚ n a e = 0 ∧ s21_Real (s21_eich e a)}
  add_mem' := by
    rintro a b ⟨ha, hRa⟩ ⟨hb, hRb⟩
    refine ⟨by rw [map_add, LinearMap.add_apply, ha, hb, add_zero], ?_⟩
    rw [← s21_eich_comp he ha hb]
    exact hRa.comp hRb
  zero_mem' := ⟨by simp, by rw [s21_eich_zero]; exact s21_Real_id⟩
  neg_mem' := by
    rintro a ⟨ha, hRa⟩
    have hna : pairing ℚ n (-a) e = 0 := by rw [map_neg, LinearMap.neg_apply, ha, neg_zero]
    refine ⟨hna, hRa.inv fun x => ?_⟩
    have := congrArg (fun φ : V ℚ n →ₗ[ℚ] V ℚ n => φ x) (s21_eich_comp he hna ha)
    simp only [LinearMap.comp_apply, neg_add_cancel, s21_eich_zero, LinearMap.id_apply] at this
    exact this

theorem s21_exists_third (hn : 2 ≤ n) (i j : Fin (2 * n)) : ∃ p : Fin (2 * n), p ≠ i ∧ p ≠ j := by
  by_cases h0 : i.val ≠ 0 ∧ j.val ≠ 0
  · exact ⟨⟨0, by omega⟩, fun h => h0.1 (by rw [← h]), fun h => h0.2 (by rw [← h])⟩
  by_cases h1 : i.val ≠ 1 ∧ j.val ≠ 1
  · exact ⟨⟨1, by omega⟩, fun h => h1.1 (by rw [← h]), fun h => h1.2 (by rw [← h])⟩
  refine ⟨⟨2, by omega⟩, fun h => ?_, fun h => ?_⟩
  · have := congrArg Fin.val h
    simp only at this
    omega
  · have := congrArg Fin.val h
    simp only at this
    omega

theorem s21_unit_mem_Lam {j : Fin (2 * n)} {u : V ℚ n} (hu : u ∈ VZ n)
    (hue : pairing ℚ n u (s21_E j) = 0) (hq : Q ℚ n u = 1 ∨ Q ℚ n u = -1) :
    u ∈ s21_Lam (s21_E j) (s21_Q_E j) := by
  refine ⟨hue, ?_⟩
  rw [← s21_eich_eq_M (s21_Q_E j) hue hq]
  have hmem : u - Q ℚ n u • s21_E j ∈ VZ n := by
    rcases hq with h | h <;> rw [h]
    · rw [one_smul]; exact sub_mem hu (s21_E_mem j)
    · rw [neg_one_smul, sub_neg_eq_add]; exact add_mem hu (s21_E_mem j)
  have hQ' := s21_Q_sub_smul (s21_Q_E j) hue (Q ℚ n u)
  refine s21_Real_gen hmem hu ?_
  rw [hQ']
  rcases hq with h | h
  · exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, h⟩

/-- **The Eichler transformations `E(eⱼ, a)`, `a ∈ V`, `a ⊥ eⱼ`, are realized** by products of
the generators (here `2n ≥ 3` is used: `eᵢ = (eᵢ + e_p + f_p) - (e_p + f_p)`). -/
theorem s21_Real_eich_E (hn : 2 ≤ n) (j : Fin (2 * n)) {a : V ℚ n} (ha : a ∈ VZ n)
    (haj : pairing ℚ n a (s21_E j) = 0) : s21_Real (s21_eich (s21_E j) a) := by
  set Λ := s21_Lam (s21_E j) (s21_Q_E j)
  suffices h : a ∈ Λ from h.2
  have hQEF : ∀ p : Fin (2 * n), Q ℚ n (s21_E p + s21_F p) = 1 := fun p => by
    simp
  have hEF : ∀ p, p ≠ j → s21_E p + s21_F p ∈ Λ := fun p hpj =>
    s21_unit_mem_Lam (add_mem (s21_E_mem p) (s21_F_mem p)) (by simp [hpj]) (Or.inl (hQEF p))
  have hE : ∀ i, s21_E i ∈ Λ := fun i => by
    obtain ⟨p, hpi, hpj⟩ := s21_exists_third hn i j
    have h1 : s21_E i + (s21_E p + s21_F p) ∈ Λ :=
      s21_unit_mem_Lam (add_mem (s21_E_mem i) (add_mem (s21_E_mem p) (s21_F_mem p)))
        (by simp [hpj]) (Or.inl (by rw [s21_Q_add, hQEF]; simp [hpi]))
    simpa using sub_mem h1 (hEF p hpj)
  have hF : ∀ i, i ≠ j → s21_F i ∈ Λ := fun i hij => by
    obtain ⟨p, hpi, hpj⟩ := s21_exists_third hn i j
    have h1 : s21_F i + (s21_E p + s21_F p) ∈ Λ :=
      s21_unit_mem_Lam (add_mem (s21_F_mem i) (add_mem (s21_E_mem p) (s21_F_mem p)))
        (by simp [hij, hpj]) (Or.inl (by rw [s21_Q_add, hQEF]; simp [Ne.symm hpi]))
    simpa using sub_mem h1 (hEF p hpj)
  rw [s21_decomp a]
  refine add_mem (AddSubgroup.sum_mem _ fun i _ => ?_) (AddSubgroup.sum_mem _ fun i _ => ?_)
  · by_cases hij : i = j
    · subst hij
      rw [haj, zero_smul]
      exact zero_mem _
    · obtain ⟨z, hz⟩ := s21_coord_E_int ha i
      rw [hz, Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hF i hij) z
  · obtain ⟨z, hz⟩ := s21_coord_F_int ha i
    rw [hz, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (hE i) z

/-! #### Fixing the first `k` hyperbolic planes -/

/-- `σ` fixes `eᵢ, fᵢ` for `i < k`. -/
def s21_Fixes (σ : V ℚ n → V ℚ n) (k : ℕ) : Prop :=
  ∀ i : Fin (2 * n), i.val < k → σ (s21_E i) = s21_E i ∧ σ (s21_F i) = s21_F i

theorem s21_Fixes.comp {σ τ : V ℚ n →ₗ[ℚ] V ℚ n} {k : ℕ} (hσ : s21_Fixes σ k)
    (hτ : s21_Fixes τ k) : s21_Fixes (σ ∘ₗ τ) k := fun i hi => by
  simp only [LinearMap.comp_apply, (hτ i hi).1, (hτ i hi).2, (hσ i hi).1, (hσ i hi).2, and_self]

/-- `x ⊥ eᵢ, fᵢ` for `i < k`. -/
def s21_Perp (x : V ℚ n) (k : ℕ) : Prop :=
  ∀ i : Fin (2 * n), i.val < k → pairing ℚ n x (s21_E i) = 0 ∧ pairing ℚ n x (s21_F i) = 0

theorem s21_Fixes_eich {e a : V ℚ n} {k : ℕ} (he : s21_Perp e k) (ha : s21_Perp a k) :
    s21_Fixes (s21_eich e a) k := fun i hi =>
  ⟨s21_eich_of_perp (by rw [s21_pairing_comm]; exact (he i hi).1)
      (by rw [s21_pairing_comm]; exact (ha i hi).1),
    s21_eich_of_perp (by rw [s21_pairing_comm]; exact (he i hi).2)
      (by rw [s21_pairing_comm]; exact (ha i hi).2)⟩

theorem s21_Fixes_MM {u₁ u₂ : V ℚ n} {k : ℕ} (h₁ : s21_Perp u₁ k) (h₂ : s21_Perp u₂ k)
    (hq : Q ℚ n u₁ * Q ℚ n u₂ = 1) : s21_Fixes (s21_M u₁ ∘ₗ s21_M u₂) k := fun i hi => by
  have hq' : -Q ℚ n u₂ * -Q ℚ n u₁ = 1 := by rw [neg_mul_neg, mul_comm, hq]
  simp only [LinearMap.comp_apply]
  rw [s21_M_of_perp (h₂ i hi).1, map_smul, s21_M_of_perp (h₁ i hi).1, smul_smul,
    s21_M_of_perp (h₂ i hi).2, map_smul, s21_M_of_perp (h₁ i hi).2, smul_smul, hq', one_smul,
    one_smul]
  exact ⟨rfl, rfl⟩

theorem s21_Perp_E {j : Fin (2 * n)} {k : ℕ} (hj : k ≤ j.val) : s21_Perp (s21_E j) k :=
  fun i hi => by
    have hij : j ≠ i := fun h => by rw [h] at hj; omega
    simp [Ne.symm hij]

theorem s21_Perp_F {j : Fin (2 * n)} {k : ℕ} (hj : k ≤ j.val) : s21_Perp (s21_F j) k :=
  fun i hi => by
    have hij : j ≠ i := fun h => by rw [h] at hj; omega
    simp [hij]

theorem s21_Perp.add {x y : V ℚ n} {k : ℕ} (hx : s21_Perp x k) (hy : s21_Perp y k) :
    s21_Perp (x + y) k := fun i hi => by
  simp only [map_add, LinearMap.add_apply, (hx i hi).1, (hx i hi).2, (hy i hi).1, (hy i hi).2,
    add_zero, and_self]

theorem s21_Perp.smul {x : V ℚ n} {k : ℕ} (hx : s21_Perp x k) (c : ℚ) : s21_Perp (c • x) k :=
  fun i hi => by
    simp only [map_smul, LinearMap.smul_apply, (hx i hi).1, (hx i hi).2, smul_zero, and_self]

theorem s21_Perp.neg {x : V ℚ n} {k : ℕ} (hx : s21_Perp x k) : s21_Perp (-x) k := by
  simpa using hx.smul (-1)

theorem s21_Perp.sub {x y : V ℚ n} {k : ℕ} (hx : s21_Perp x k) (hy : s21_Perp y k) :
    s21_Perp (x - y) k := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem s21_Perp_of_Fixes {σ : V ℚ n →ₗ[ℚ] V ℚ n} (hσ : s21_Real σ) {k : ℕ}
    (hfix : s21_Fixes σ k) {x : V ℚ n} (hx : s21_Perp x k) : s21_Perp (σ x) k := fun i hi => by
  rw [← (hfix i hi).1, ← (hfix i hi).2, hσ.pairing_eq, hσ.pairing_eq]
  exact hx i hi

/-! #### The moves `S` (swap `eⱼ ↔ fⱼ`, `e_l ↔ f_l`) and `P` -/

@[simp] theorem s21_Q_E_sub_F (j : Fin (2 * n)) : Q ℚ n (s21_E j - s21_F j) = -1 := by
  simp [s21_E, s21_F, QuadraticForm.dualProd_apply, s21_f_e]

@[simp] theorem s21_Q_E_add_F (j : Fin (2 * n)) : Q ℚ n (s21_E j + s21_F j) = 1 := by
  simp

theorem s21_M_sub_E (j : Fin (2 * n)) : s21_M (s21_E j - s21_F j) (s21_E j) = s21_F j := by
  rw [s21_M_apply]; simp

theorem s21_M_sub_F (j : Fin (2 * n)) : s21_M (s21_E j - s21_F j) (s21_F j) = s21_E j := by
  rw [s21_M_apply]; simp

theorem s21_M_add_E (j : Fin (2 * n)) : s21_M (s21_E j + s21_F j) (s21_E j) = s21_F j := by
  rw [s21_M_apply]; simp

theorem s21_M_add_F (j : Fin (2 * n)) : s21_M (s21_E j + s21_F j) (s21_F j) = s21_E j := by
  rw [s21_M_apply]; simp

theorem s21_M_sub_of_ne {j i : Fin (2 * n)} (h : j ≠ i) :
    s21_M (s21_E j - s21_F j) (s21_E i) = s21_E i ∧
      s21_M (s21_E j - s21_F j) (s21_F i) = s21_F i := by
  constructor <;> rw [s21_M_of_perp (by simp [h, Ne.symm h])] <;> simp

theorem s21_M_add_of_ne {j i : Fin (2 * n)} (h : j ≠ i) :
    s21_M (s21_E j + s21_F j) (s21_E i) = -s21_E i ∧
      s21_M (s21_E j + s21_F j) (s21_F i) = -s21_F i := by
  constructor <;> rw [s21_M_of_perp (by simp [h, Ne.symm h])] <;> simp

/-- The swap of the planes `j` and `l`. -/
theorem s21_swap (j l : Fin (2 * n)) (hjl : j ≠ l) {k : ℕ} (hj : k ≤ j.val) (hl : k ≤ l.val) :
    ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ (s21_E j) = s21_F j ∧ σ (s21_F j) = s21_E j := by
  have hm : ∀ p : Fin (2 * n), s21_E p - s21_F p ∈ VZ n := fun p =>
    sub_mem (s21_E_mem p) (s21_F_mem p)
  have hperp : ∀ p : Fin (2 * n), k ≤ p.val → s21_Perp (s21_E p - s21_F p) k := fun p hp =>
    (s21_Perp_E hp).sub (s21_Perp_F hp)
  refine ⟨s21_M (s21_E j - s21_F j) ∘ₗ s21_M (s21_E l - s21_F l),
    s21_Real_gen (hm j) (hm l) (Or.inr ⟨by simp, by simp⟩),
    s21_Fixes_MM (hperp j hj) (hperp l hl) (by simp), ?_, ?_⟩
  · rw [LinearMap.comp_apply, (s21_M_sub_of_ne (Ne.symm hjl)).1, s21_M_sub_E]
  · rw [LinearMap.comp_apply, (s21_M_sub_of_ne (Ne.symm hjl)).2, s21_M_sub_F]

/-- `-eⱼ ↦ eⱼ`. -/
theorem s21_negE (j l : Fin (2 * n)) (hjl : j ≠ l) {k : ℕ} (hj : k ≤ j.val) (hl : k ≤ l.val) :
    ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ (-s21_E j) = s21_E j := by
  obtain ⟨S, hRS, hFS, hSE, hSF⟩ := s21_swap j l hjl hj hl
  have hm : ∀ p : Fin (2 * n), s21_E p + s21_F p ∈ VZ n := fun p =>
    add_mem (s21_E_mem p) (s21_F_mem p)
  have hperp : ∀ p : Fin (2 * n), k ≤ p.val → s21_Perp (s21_E p + s21_F p) k := fun p hp =>
    (s21_Perp_E hp).add (s21_Perp_F hp)
  refine ⟨S ∘ₗ (s21_M (s21_E j + s21_F j) ∘ₗ s21_M (s21_E l + s21_F l)),
    hRS.comp (s21_Real_gen (hm j) (hm l) (Or.inl ⟨by simp, by simp⟩)),
    hFS.comp (s21_Fixes_MM (hperp j hj) (hperp l hl) (by simp)), ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_neg (s21_M (s21_E l + s21_F l)),
    (s21_M_add_of_ne (Ne.symm hjl)).1, neg_neg, s21_M_add_E, hSF]

/-- `eⱼ ↦ e_k` for `j ≠ k`, by two Eichler transformations. -/
theorem s21_moveE (hn : 2 ≤ n) (j k' : Fin (2 * n)) (hjk : j ≠ k') {k : ℕ} (hj : k ≤ j.val)
    (hk : k ≤ k'.val) :
    ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ (s21_E j) = s21_E k' := by
  refine ⟨s21_eich (s21_E j) (s21_F k') ∘ₗ s21_eich (s21_E k') (-s21_F j),
    (s21_Real_eich_E hn j (s21_F_mem k') (by simp [Ne.symm hjk])).comp
      (s21_Real_eich_E hn k' (neg_mem (s21_F_mem j)) (by simp [hjk])),
    (s21_Fixes_eich (s21_Perp_E hj) (s21_Perp_F hk)).comp
      (s21_Fixes_eich (s21_Perp_E hk) (s21_Perp_F hj).neg), ?_⟩
  rw [LinearMap.comp_apply, s21_eich_apply, s21_eich_apply]
  simp [Ne.symm hjk]

/-- **Finishing**: `±fⱼ ↦ e_k` (`j ≥ k`, using a second plane `l ≥ k`). -/
theorem s21_finish (hn : 2 ≤ n) {k : ℕ} (hk : k + 1 < 2 * n) (j : Fin (2 * n)) (hj : k ≤ j.val)
    (s : ℚ) (hs : s = 1 ∨ s = -1) :
    ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ (s • s21_F j) = s21_E ⟨k, by omega⟩ := by
  obtain ⟨l, hlk, hlj⟩ : ∃ l : Fin (2 * n), k ≤ l.val ∧ l ≠ j := by
    by_cases h : j.val = k
    · exact ⟨⟨k + 1, hk⟩, by simp, fun h' => by rw [← h'] at h; simp at h⟩
    · exact ⟨⟨k, by omega⟩, le_refl _, fun h' => h (by rw [← h'])⟩
  obtain ⟨S, hRS, hFS, -, hSF⟩ := s21_swap j l (Ne.symm hlj) hj hlk
  -- `s fⱼ ↦ eⱼ`
  have step1 : ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ (s • s21_F j) = s21_E j := by
    rcases hs with rfl | rfl
    · exact ⟨S, hRS, hFS, by rw [one_smul, hSF]⟩
    · obtain ⟨N, hRN, hFN, hN⟩ := s21_negE j l (Ne.symm hlj) hj hlk
      exact ⟨N ∘ₗ S, hRN.comp hRS, hFN.comp hFS, by
        rw [LinearMap.comp_apply, map_smul, hSF, neg_one_smul, hN]⟩
  obtain ⟨σ₁, hR₁, hF₁, h₁⟩ := step1
  by_cases hjk : j = ⟨k, by omega⟩
  · exact ⟨σ₁, hR₁, hF₁, by rw [h₁, hjk]⟩
  · obtain ⟨σ₂, hR₂, hF₂, h₂⟩ := s21_moveE hn j ⟨k, by omega⟩ hjk hj (le_refl k)
    exact ⟨σ₂ ∘ₗ σ₁, hR₂.comp hR₁, hF₂.comp hF₁, by rw [LinearMap.comp_apply, h₁, h₂]⟩

/-! #### The Euclidean algorithm on a unimodular isotropic vector -/

/-- The vector with coordinates `(x, fᵢ) = αᵢ`, `(x, eᵢ) = βᵢ`. -/
noncomputable def s21_ofCoord (α β : Fin (2 * n) → ℚ) : V ℚ n :=
  ∑ i, β i • s21_F i + ∑ i, α i • s21_E i

theorem s21_ofCoord_E (α β : Fin (2 * n) → ℚ) (j : Fin (2 * n)) :
    pairing ℚ n (s21_ofCoord α β) (s21_E j) = β j := by
  simp [s21_ofCoord, map_sum]

theorem s21_ofCoord_F (α β : Fin (2 * n) → ℚ) (j : Fin (2 * n)) :
    pairing ℚ n (s21_ofCoord α β) (s21_F j) = α j := by
  simp [s21_ofCoord, map_sum]

theorem s21_ofCoord_mem {α β : Fin (2 * n) → ℚ} (hα : ∀ i, ∃ z : ℤ, α i = z)
    (hβ : ∀ i, ∃ z : ℤ, β i = z) : s21_ofCoord α β ∈ VZ n := by
  refine add_mem (sum_mem fun i _ => ?_) (sum_mem fun i _ => ?_)
  · obtain ⟨z, hz⟩ := hβ i
    rw [hz, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (s21_F_mem i) z
  · obtain ⟨z, hz⟩ := hα i
    rw [hz, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (s21_E_mem i) z

theorem s21_eich_E_coord (j i : Fin (2 * n)) (a x : V ℚ n) :
    pairing ℚ n (s21_eich (s21_E j) a x) (s21_E i) =
      pairing ℚ n x (s21_E i) + pairing ℚ n x (s21_E j) * pairing ℚ n a (s21_E i) := by
  rw [s21_eich_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, s21_E_E, mul_zero, sub_zero]

theorem s21_eich_F_coord {j i : Fin (2 * n)} (hij : i ≠ j) (a x : V ℚ n) :
    pairing ℚ n (s21_eich (s21_E j) a x) (s21_F i) =
      pairing ℚ n x (s21_F i) + pairing ℚ n x (s21_E j) * pairing ℚ n a (s21_F i) := by
  rw [s21_eich_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, s21_E_F, ite_eq_right (Ne.symm hij), mul_zero, sub_zero]

theorem s21_exists_other {k : ℕ} (hk : k + 1 < 2 * n) (j : Fin (2 * n)) :
    ∃ l : Fin (2 * n), k ≤ l.val ∧ l ≠ j := by
  by_cases h : j.val = k
  · exact ⟨⟨k + 1, hk⟩, by simp, fun h' => by rw [← h'] at h; simp at h⟩
  · exact ⟨⟨k, by omega⟩, le_refl _, fun h' => h (by rw [← h'])⟩

/-- **One Euclidean step**: if `c = (x, eⱼ) ≠ 0`, an Eichler transformation `E(eⱼ, a)` reduces all
the other coordinates of `x` modulo `c`. -/
theorem s21_euclid_step (hn : 2 ≤ n) {k : ℕ} {x : V ℚ n} (hx : x ∈ VZ n) (hperp : s21_Perp x k)
    (j : Fin (2 * n)) (hj : k ≤ j.val) (hc : pairing ℚ n x (s21_E j) ≠ 0) :
    ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧
      pairing ℚ n (σ x) (s21_E j) = pairing ℚ n x (s21_E j) ∧
      ∀ i : Fin (2 * n), i ≠ j →
        |pairing ℚ n (σ x) (s21_E i)| < |pairing ℚ n x (s21_E j)| ∧
        |pairing ℚ n (σ x) (s21_F i)| < |pairing ℚ n x (s21_E j)| := by
  classical
  choose zb hzb using s21_coord_E_int hx
  choose za hza using s21_coord_F_int hx
  have hcQ : pairing ℚ n x (s21_E j) = (zb j : ℚ) := hzb j
  have hc' : zb j ≠ 0 := by
    intro h
    apply hc
    rw [hcQ, h, Int.cast_zero]
  set c : ℤ := zb j with hcdef
  let S : Fin (2 * n) → Prop := fun i => k ≤ i.val ∧ i ≠ j
  let α : Fin (2 * n) → ℚ := fun i => if S i then -((za i / c : ℤ) : ℚ) else 0
  let β : Fin (2 * n) → ℚ := fun i => if S i then -((zb i / c : ℤ) : ℚ) else 0
  have hαZ : ∀ i, ∃ z : ℤ, α i = z := fun i => by
    by_cases h : S i
    · exact ⟨-(za i / c), by simp [α, h]⟩
    · exact ⟨0, by simp [α, h]⟩
  have hβZ : ∀ i, ∃ z : ℤ, β i = z := fun i => by
    by_cases h : S i
    · exact ⟨-(zb i / c), by simp [β, h]⟩
    · exact ⟨0, by simp [β, h]⟩
  set a := s21_ofCoord α β
  have haE : ∀ i, pairing ℚ n a (s21_E i) = β i := s21_ofCoord_E α β
  have haF : ∀ i, pairing ℚ n a (s21_F i) = α i := s21_ofCoord_F α β
  have haZ : a ∈ VZ n := s21_ofCoord_mem hαZ hβZ
  have hSj : ¬ S j := fun h => h.2 rfl
  have haj : pairing ℚ n a (s21_E j) = 0 := by rw [haE]; simp [β, hSj]
  have hPa : s21_Perp a k := fun i hi => by
    have hSi : ¬ S i := fun h => by have := h.1; omega
    rw [haE, haF]
    simp [α, β, hSi]
  have key : ∀ (z : ℤ) (w : ℚ), w = z → |w + (c : ℚ) * (-((z / c : ℤ) : ℚ))| < |(c : ℚ)| := by
    intro z w hw
    rw [hw, show (z : ℚ) + (c : ℚ) * (-((z / c : ℤ) : ℚ)) = ((z % c : ℤ) : ℚ) by
      rw [Int.emod_def]; push_cast; ring]
    rw [← Int.cast_abs, ← Int.cast_abs, Int.cast_lt, abs_of_nonneg (Int.emod_nonneg z hc')]
    exact Int.emod_lt_abs z hc'
  have hc0 : (0 : ℚ) < |(c : ℚ)| := abs_pos.mpr (by exact_mod_cast hc')
  refine ⟨s21_eich (s21_E j) a, s21_Real_eich_E hn j haZ haj,
    s21_Fixes_eich (s21_Perp_E hj) hPa, ?_, fun i hij => ?_⟩
  · rw [s21_eich_E_coord, haj, mul_zero, add_zero]
  · rw [hcQ]
    by_cases hS : S i
    · constructor
      · rw [s21_eich_E_coord, haE, hcQ]
        simp only [β, ite_eq_left hS]
        exact key (zb i) _ (hzb i)
      · rw [s21_eich_F_coord hij, haF, hcQ]
        simp only [α, ite_eq_left hS]
        exact key (za i) _ (hza i)
    · have hik : i.val < k := by
        by_contra h
        exact hS ⟨by omega, hij⟩
      constructor
      · rw [s21_eich_E_coord, haE, (hperp i hik).1]
        simpa [β, hS] using hc0
      · rw [s21_eich_F_coord hij, haF, (hperp i hik).2]
        simpa [α, hS] using hc0

theorem s21_abs_le_of_lt {w : ℚ} (hw : ∃ z : ℤ, w = z) {c : ℚ} {M : ℕ} (h1 : |w| < |c|)
    (h2 : |c| ≤ ((M + 1 : ℕ) : ℚ)) : |w| ≤ M := by
  obtain ⟨z, rfl⟩ := hw
  have h3 : |(z : ℚ)| < (M : ℚ) + 1 := by push_cast at h2; linarith
  rw [← Int.cast_abs] at h3 ⊢
  have h4 : |z| < (M : ℤ) + 1 := by exact_mod_cast h3
  have h5 : |z| ≤ (M : ℤ) := Int.lt_add_one_iff.mp h4
  exact_mod_cast h5

/-- **The Euclidean algorithm**: a unimodular isotropic `x ∈ V`, orthogonal to the first `k`
hyperbolic planes, is moved to `e_k` by a realizable isometry fixing those planes. Induction on a
bound `M` for some nonzero coordinate. -/
theorem s21_euclid (hn : 2 ≤ n) {k : ℕ} (hk : k + 1 < 2 * n) (M : ℕ) :
    ∀ x : V ℚ n, x ∈ VZ n → Q ℚ n x = 0 → s21_Perp x k → (∃ y ∈ VZ n, pairing ℚ n x y = 1) →
      (∃ i : Fin (2 * n), (pairing ℚ n x (s21_E i) ≠ 0 ∧ |pairing ℚ n x (s21_E i)| ≤ M) ∨
        (pairing ℚ n x (s21_F i) ≠ 0 ∧ |pairing ℚ n x (s21_F i)| ≤ M)) →
      ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ x = s21_E ⟨k, by omega⟩ := by
  induction M with
  | zero =>
    rintro x - - - - ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact absurd (abs_nonpos_iff.mp (by exact_mod_cast h2)) h1
    · exact absurd (abs_nonpos_iff.mp (by exact_mod_cast h2)) h1
  | succ M ih =>
    -- the case of a nonzero coordinate `(x, eⱼ)`
    have bcase : ∀ x : V ℚ n, x ∈ VZ n → Q ℚ n x = 0 → s21_Perp x k →
        (∃ y ∈ VZ n, pairing ℚ n x y = 1) → ∀ j : Fin (2 * n), pairing ℚ n x (s21_E j) ≠ 0 →
        |pairing ℚ n x (s21_E j)| ≤ ((M + 1 : ℕ) : ℚ) →
        ∃ σ, s21_Real σ ∧ s21_Fixes σ k ∧ σ x = s21_E ⟨k, by omega⟩ := by
      intro x hx hQ hperp hy j hc hcM
      have hj : k ≤ j.val := by
        by_contra h
        exact hc (hperp j (by omega)).1
      obtain ⟨σ₀, hR₀, hF₀, hcj, hlt⟩ := s21_euclid_step hn hx hperp j hj hc
      have hx' : σ₀ x ∈ VZ n := hR₀.mem_VZ hx
      have hQ' : Q ℚ n (σ₀ x) = 0 := by rw [hR₀.Q_eq, hQ]
      have hperp' : s21_Perp (σ₀ x) k := s21_Perp_of_Fixes hR₀ hF₀ hperp
      have hy' : ∃ y ∈ VZ n, pairing ℚ n (σ₀ x) y = 1 := by
        obtain ⟨y, hy, hxy⟩ := hy
        exact ⟨σ₀ y, hR₀.mem_VZ hy, by rw [hR₀.pairing_eq, hxy]⟩
      by_cases hall : ∀ i, i ≠ j →
          pairing ℚ n (σ₀ x) (s21_E i) = 0 ∧ pairing ℚ n (σ₀ x) (s21_F i) = 0
      · -- then `σ₀ x = ± fⱼ`
        obtain ⟨α, hα⟩ : ∃ α, pairing ℚ n (σ₀ x) (s21_F j) = α := ⟨_, rfl⟩
        obtain ⟨β, hβ⟩ : ∃ β, pairing ℚ n (σ₀ x) (s21_E j) = β := ⟨_, rfl⟩
        have hx'eq : σ₀ x = α • s21_E j + β • s21_F j := by
          rw [s21_decomp (σ₀ x)]
          rw [Finset.sum_eq_single j (fun i _ hij => by rw [(hall i hij).1, zero_smul])
              (by simp),
            Finset.sum_eq_single j (fun i _ hij => by rw [(hall i hij).2, zero_smul]) (by simp),
            hα, hβ, add_comm]
        have hβ0 : β ≠ 0 := by rw [← hβ, hcj]; exact hc
        have hQx' : Q ℚ n (σ₀ x) = α * β := by
          rw [hx'eq, s21_Q_add, QuadraticMap.map_smul, QuadraticMap.map_smul]
          simp only [s21_Q_E, s21_Q_F, smul_eq_mul, mul_zero, zero_add, map_smul,
            LinearMap.smul_apply, s21_E_F, ite_true]
          ring
        have hα0 : α = 0 := by
          rw [hQ'] at hQx'
          rcases mul_eq_zero.mp hQx'.symm with h | h
          · exact h
          · exact absurd h hβ0
        rw [hα0, zero_smul, zero_add] at hx'eq
        obtain ⟨y', hy'Z, hxy'⟩ := hy'
        rw [hx'eq, map_smul, LinearMap.smul_apply, s21_F_pairing, smul_eq_mul] at hxy'
        obtain ⟨zβ, hzβ⟩ : ∃ z : ℤ, β = z := by rw [← hβ]; exact s21_coord_E_int hx' j
        obtain ⟨zy, hzy⟩ := hy'Z.2 j
        have hzz : zβ * zy = 1 := by
          rw [hzβ, hzy] at hxy'
          exact_mod_cast hxy'
        have hs : β = 1 ∨ β = -1 := by
          rcases Int.eq_one_or_neg_one_of_mul_eq_one hzz with h | h
          · left; rw [hzβ, h, Int.cast_one]
          · right; rw [hzβ, h, Int.cast_neg, Int.cast_one]
        obtain ⟨σ₁, hR₁, hF₁, h₁⟩ := s21_finish hn hk j hj β hs
        exact ⟨σ₁ ∘ₗ σ₀, hR₁.comp hR₀, hF₁.comp hF₀, by rw [LinearMap.comp_apply, hx'eq, h₁]⟩
      · -- a smaller nonzero coordinate
        push Not at hall
        obtain ⟨i, hij, hi⟩ := hall
        have hb : ∃ i' : Fin (2 * n),
            (pairing ℚ n (σ₀ x) (s21_E i') ≠ 0 ∧ |pairing ℚ n (σ₀ x) (s21_E i')| ≤ M) ∨
            (pairing ℚ n (σ₀ x) (s21_F i') ≠ 0 ∧ |pairing ℚ n (σ₀ x) (s21_F i')| ≤ M) := by
          refine ⟨i, ?_⟩
          by_cases hEi : pairing ℚ n (σ₀ x) (s21_E i) = 0
          · exact Or.inr ⟨hi hEi,
              s21_abs_le_of_lt (s21_coord_F_int hx' i) (hlt i hij).2 hcM⟩
          · exact Or.inl ⟨hEi,
              s21_abs_le_of_lt (s21_coord_E_int hx' i) (hlt i hij).1 hcM⟩
        obtain ⟨σ₁, hR₁, hF₁, h₁⟩ := ih (σ₀ x) hx' hQ' hperp' hy' hb
        exact ⟨σ₁ ∘ₗ σ₀, hR₁.comp hR₀, hF₁.comp hF₀, by rw [LinearMap.comp_apply, h₁]⟩
    rintro x hx hQ hperp hy ⟨i, ⟨hc, hcM⟩ | ⟨hc, hcM⟩⟩
    · exact bcase x hx hQ hperp hy i hc hcM
    · -- a nonzero coordinate `(x, fᵢ)`: swap the planes `i` and `l` first
      have hi : k ≤ i.val := by
        by_contra h
        exact hc (hperp i (by omega)).2
      obtain ⟨l, hlk, hli⟩ := s21_exists_other hk i
      obtain ⟨S, hRS, hFS, -, hSF⟩ := s21_swap i l (Ne.symm hli) hi hlk
      have hcoord : pairing ℚ n (S x) (s21_E i) = pairing ℚ n x (s21_F i) := by
        rw [← hSF, hRS.pairing_eq]
      obtain ⟨σ, hR, hF, hσ⟩ := bcase (S x) (hRS.mem_VZ hx) (by rw [hRS.Q_eq, hQ])
        (s21_Perp_of_Fixes hRS hFS hperp)
        (by
          obtain ⟨y, hy, hxy⟩ := hy
          exact ⟨S y, hRS.mem_VZ hy, by rw [hRS.pairing_eq, hxy]⟩)
        i (by rw [hcoord]; exact hc) (by rw [hcoord]; exact hcM)
      exact ⟨σ ∘ₗ S, hR.comp hRS, hF.comp hFS, by rw [LinearMap.comp_apply, hσ]⟩

/-! #### One hyperbolic plane at a time -/

/-- `E(e_k, -z)` sends `y = f_k + c e_k + z` (`z ⊥ e_k, f_k`, `y` isotropic) to `f_k`. -/
theorem s21_eich_fix_F (k' : Fin (2 * n)) {y z : V ℚ n} {c : ℚ}
    (hy : y = s21_F k' + c • s21_E k' + z) (hzE : pairing ℚ n z (s21_E k') = 0)
    (hzF : pairing ℚ n z (s21_F k') = 0) (hQy : Q ℚ n y = 0) :
    s21_eich (s21_E k') (-z) y = s21_F k' := by
  have hEz : pairing ℚ n (s21_E k') z = 0 := by rw [s21_pairing_comm, hzE]
  have hFz : pairing ℚ n (s21_F k') z = 0 := by rw [s21_pairing_comm, hzF]
  have hzz : pairing ℚ n z z = 2 * Q ℚ n z := s21_pairing_self z
  have hQ : Q ℚ n y = c + Q ℚ n z := by
    rw [hy, s21_Q_add, s21_Q_add, QuadraticMap.map_smul]
    simp only [s21_Q_F, s21_Q_E, smul_eq_mul, mul_zero, zero_add, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, s21_F_E, ite_true, hFz, hEz]
    ring
  have hc : c = -Q ℚ n z := by rw [hQy] at hQ; linear_combination -hQ
  rw [s21_eich_apply, QuadraticMap.map_neg, hy]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, s21_F_E, s21_E_E, ite_true, hzE, hFz, hEz, hzz]
  rw [hc]
  module

/-- **Phase `k`**: an element of `Spin(V)` fixing the first `k` planes is multiplied by an element
of the subgroup generated by the `v₁ v₂` so as to fix also the plane `k`. -/
theorem s21_phase (hn : 2 ≤ n) {k : ℕ} (hk : k + 1 < 2 * n) (g : Spin ℚ n) (hg : g ∈ SpinZ n)
    (hfix : s21_Fixes (rho ℚ n g) k) :
    ∃ h ∈ Subgroup.closure (s21_T n), s21_Fixes (rho ℚ n (h * g)) (k + 1) := by
  set kk : Fin (2 * n) := ⟨k, by omega⟩
  have hpair := s21_pairing_rho g
  have hne : ∀ i : Fin (2 * n), i.val < k → kk ≠ i := fun i hi h => by
    have := congrArg Fin.val h
    simp [kk] at this
    omega
  -- Step 1: move `x = ρ(g) e_k` to `e_k`.
  set x := rho ℚ n g (s21_E kk) with hxdef
  have hx : x ∈ VZ n := hg.2 _ (s21_E_mem kk)
  have hQx : Q ℚ n x = 0 := by rw [s21_Q_eq_half, hpair, ← s21_Q_eq_half, s21_Q_E]
  have hperp : s21_Perp x k := fun i hi => by
    rw [← (hfix i hi).1, ← (hfix i hi).2, hpair, hpair]
    simp [Ne.symm (hne i hi)]
  have hy : ∃ y ∈ VZ n, pairing ℚ n x y = 1 :=
    ⟨rho ℚ n g (s21_F kk), hg.2 _ (s21_F_mem kk), by rw [hpair]; simp⟩
  obtain ⟨i, hi⟩ : ∃ i, pairing ℚ n x (s21_E i) ≠ 0 ∨ pairing ℚ n x (s21_F i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, -, hxy⟩ := hy
    have hx0 : x = 0 := by
      rw [s21_decomp x]
      simp [hcon]
    rw [hx0, map_zero, LinearMap.zero_apply] at hxy
    exact zero_ne_one hxy
  obtain ⟨M, hM⟩ : ∃ M : ℕ,
      (pairing ℚ n x (s21_E i) ≠ 0 ∧ |pairing ℚ n x (s21_E i)| ≤ M) ∨
      (pairing ℚ n x (s21_F i) ≠ 0 ∧ |pairing ℚ n x (s21_F i)| ≤ M) := by
    rcases hi with h | h
    · obtain ⟨z, hz⟩ := s21_coord_E_int hx i
      refine ⟨z.natAbs, Or.inl ⟨h, ?_⟩⟩
      rw [hz, ← Int.cast_abs, Int.abs_eq_natAbs]
      simp
    · obtain ⟨z, hz⟩ := s21_coord_F_int hx i
      refine ⟨z.natAbs, Or.inr ⟨h, ?_⟩⟩
      rw [hz, ← Int.cast_abs, Int.abs_eq_natAbs]
      simp
  obtain ⟨σ₁, hR₁, hF₁, h₁⟩ := s21_euclid hn hk M x hx hQx hperp hy ⟨i, hM⟩
  obtain ⟨h₁', hh₁', hσ₁⟩ := hR₁
  set g₁ := h₁' * g with hg₁def
  have hg₁ : g₁ ∈ SpinZ n := mul_mem (s21_closure_le hh₁') hg
  have hpair₁ := s21_pairing_rho g₁
  have hfix₁ : s21_Fixes (rho ℚ n g₁) k := fun i hi => by
    simp only [g₁, s21_rho_mul, (hfix i hi).1, (hfix i hi).2, hσ₁, (hF₁ i hi).1, (hF₁ i hi).2,
      and_self]
  have hE₁ : rho ℚ n g₁ (s21_E kk) = s21_E kk := by
    simp only [g₁, s21_rho_mul, hσ₁]
    exact h₁
  -- Step 2: fix `f_k` by an Eichler transformation `E(e_k, -z)`.
  set y₁ := rho ℚ n g₁ (s21_F kk) with hy₁def
  set c := pairing ℚ n y₁ (s21_F kk)
  set z := y₁ - s21_F kk - c • s21_E kk with hzdef
  have hy₁Z : y₁ ∈ VZ n := hg₁.2 _ (s21_F_mem kk)
  have hy₁E : pairing ℚ n y₁ (s21_E kk) = 1 := by
    rw [← hE₁, hpair₁]; simp
  have hzE : pairing ℚ n z (s21_E kk) = 0 := by
    simp only [z, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy₁E,
      s21_F_E, s21_E_E, ite_true, smul_eq_mul, mul_zero, sub_self]
  have hzF : pairing ℚ n z (s21_F kk) = 0 := by
    simp only [z, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, s21_F_F,
      s21_E_F, ite_true, smul_eq_mul, mul_one, sub_zero, sub_self, c]
  have hy₁perp : s21_Perp y₁ k := fun i hi => by
    rw [← (hfix₁ i hi).1, ← (hfix₁ i hi).2, hpair₁, hpair₁]
    simp [hne i hi]
  have hzperp : s21_Perp z k :=
    (hy₁perp.sub (s21_Perp_F (le_refl k))).sub ((s21_Perp_E (le_refl k)).smul c)
  have hzZ : z ∈ VZ n := by
    obtain ⟨zc, hzc⟩ := s21_coord_F_int hy₁Z kk
    refine sub_mem (sub_mem hy₁Z (s21_F_mem kk)) ?_
    rw [show c = (zc : ℚ) from hzc, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (s21_E_mem kk) zc
  have hQy₁ : Q ℚ n y₁ = 0 := by rw [s21_Q_eq_half, hpair₁, ← s21_Q_eq_half, s21_Q_F]
  have hR₂ : s21_Real (s21_eich (s21_E kk) (-z)) :=
    s21_Real_eich_E hn kk (neg_mem hzZ) (by rw [map_neg, LinearMap.neg_apply, hzE, neg_zero])
  have hF₂ : s21_Fixes (s21_eich (s21_E kk) (-z)) k :=
    s21_Fixes_eich (s21_Perp_E (le_refl k)) hzperp.neg
  have h₂E : s21_eich (s21_E kk) (-z) (s21_E kk) = s21_E kk :=
    s21_eich_of_perp (by simp) (by rw [s21_pairing_comm, map_neg, LinearMap.neg_apply, hzE,
      neg_zero])
  have h₂F : s21_eich (s21_E kk) (-z) y₁ = s21_F kk :=
    s21_eich_fix_F kk (by rw [hzdef]; abel) hzE hzF hQy₁
  obtain ⟨h₂', hh₂', hσ₂⟩ := hR₂
  refine ⟨h₂' * h₁', mul_mem hh₂' hh₁', fun i hi => ?_⟩
  have hρ : ∀ v, rho ℚ n (h₂' * h₁' * g) v = s21_eich (s21_E kk) (-z) (rho ℚ n g₁ v) :=
    fun v => by rw [mul_assoc, s21_rho_mul, hσ₂]
  rw [hρ, hρ]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · rw [(hfix₁ i hi).1, (hfix₁ i hi).2, (hF₂ i hi).1, (hF₂ i hi).2]
    exact ⟨rfl, rfl⟩
  · have hik : i = kk := Fin.ext hi
    subst hik
    exact ⟨by rw [hE₁, h₂E], h₂F⟩

theorem s21_iterate (hn : 2 ≤ n) (g : Spin ℚ n) (hg : g ∈ SpinZ n) (k : ℕ) (hk : k < 2 * n) :
    ∃ h ∈ Subgroup.closure (s21_T n), s21_Fixes (rho ℚ n (h * g)) k := by
  induction k with
  | zero => exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨h, hh, hfix⟩ := ih (by omega)
    obtain ⟨h', hh', hfix'⟩ :=
      s21_phase hn hk (h * g) (mul_mem (s21_closure_le hh) hg) hfix
    exact ⟨h' * h, mul_mem hh' hh, by rw [mul_assoc]; exact hfix'⟩

/-! #### The last plane -/

/-- If `ρ(g)` is the identity, `g = ±1` lies in the subgroup generated by the `v₁ v₂`. -/
theorem s21_mem_closure_of_rho_eq_id (hn : 0 < n) (g : Spin ℚ n)
    (h : ∀ v, rho ℚ n g v = v) : g ∈ Subgroup.closure (s21_T n) := by
  have hcomm : ∀ v, Commute (g : C ℚ n) (ι (Q ℚ n) v) := fun v => by
    have h1 : (g : C ℚ n) * ι (Q ℚ n) v * star (g : C ℚ n) = ι (Q ℚ n) v := by
      rw [← ι_rho, h]
    have h2 := congrArg (· * (g : C ℚ n)) h1
    simp only [mul_assoc, spinGroup.star_mul_self_of_mem g.2, mul_one] at h2
    exact h2
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_mem_even_of_commute (Q ℚ n) s21_Q_nondegenerate
    (g : C ℚ n) (spinGroup.mem_even g.2) hcomm
  have hc2 : c * c = 1 := by
    have := spinGroup.mul_star_self_of_mem g.2
    rw [hc, star_algebraMap, ← map_mul] at this
    exact algebraMap_injective (Q ℚ n) (this.trans (map_one _).symm)
  rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
  · have : g = 1 := Subtype.ext (by rw [hc, h1, map_one]; rfl)
    rw [this]
    exact one_mem _
  · apply Subgroup.subset_closure
    set u : V ℚ n := s21_E ⟨0, by omega⟩ + s21_F ⟨0, by omega⟩
    have hu : u ∈ VZ n := add_mem (s21_E_mem _) (s21_F_mem _)
    have hpu : pairing ℚ n u u = 2 := by rw [s21_pairing_self, s21_Q_E_add_F]; norm_num
    have hpu' : pairing ℚ n (-u) (-u) = 2 := by
      rw [← hpu]
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
    refine ⟨u, hu, -u, neg_mem hu, Or.inl ⟨hpu, hpu'⟩, ?_⟩
    rw [hc, h1, map_neg, map_one, map_neg, mul_neg, ι_sq_scalar, s21_Q_E_add_F, map_one]

/-- `ρ(g)` is never `-Q(u) M_u` (minus the reflection in `u`) for `g ∈ Spin` and `Q(u) = ±1`. -/
theorem s21_false_of_rho_eq_refl (g : Spin ℚ n) {u : V ℚ n} (hq : Q ℚ n u = 1 ∨ Q ℚ n u = -1)
    (h : ∀ v, rho ℚ n g v = -(Q ℚ n u • s21_M u v)) : False := by
  have hqq : Q ℚ n u * Q ℚ n u = 1 := by rcases hq with h | h <;> rw [h] <;> norm_num
  have hsg : star (g : C ℚ n) * (g : C ℚ n) = 1 := spinGroup.star_mul_self_of_mem g.2
  have hgs : (g : C ℚ n) * star (g : C ℚ n) = 1 := spinGroup.mul_star_self_of_mem g.2
  -- `g v g⁻¹ ι u = -(ι u v)`
  have key : ∀ v, (g : C ℚ n) * ι (Q ℚ n) v * star (g : C ℚ n) * ι (Q ℚ n) u =
      -(ι (Q ℚ n) u * ι (Q ℚ n) v) := fun v => by
    rw [← ι_rho, h, map_neg, map_smul, ← s21_ι_M, neg_mul, smul_mul_assoc,
      mul_assoc (ι (Q ℚ n) u * ι (Q ℚ n) v) (ι (Q ℚ n) u) (ι (Q ℚ n) u), ι_sq_scalar,
      ← Algebra.commutes, ← Algebra.smul_def, smul_smul, hqq, one_smul]
  set z := star (g : C ℚ n) * ι (Q ℚ n) u
  have hz : ∀ v, involute z * ι (Q ℚ n) v = ι (Q ℚ n) v * z := fun v => by
    have hinv : involute z = -z := by
      simp only [z, map_mul, involute_ι, mul_neg,
        spinGroup.involute_eq (spinGroup.star_mem g.2)]
    rw [hinv, neg_mul]
    calc -(star (g : C ℚ n) * ι (Q ℚ n) u * ι (Q ℚ n) v)
        = star (g : C ℚ n) * -(ι (Q ℚ n) u * ι (Q ℚ n) v) := by rw [mul_neg, mul_assoc]
      _ = star (g : C ℚ n) * ((g : C ℚ n) * ι (Q ℚ n) v * star (g : C ℚ n) * ι (Q ℚ n) u) := by
          rw [key]
      _ = ι (Q ℚ n) v * z := by simp only [z, ← mul_assoc, hsg, one_mul]
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul (Q ℚ n)
    s21_Q_nondegenerate z hz
  have hc0 : c = 0 := by
    have h1 : involute z = -z := by
      simp only [z, map_mul, involute_ι, mul_neg,
        spinGroup.involute_eq (spinGroup.star_mem g.2)]
    rw [hc, AlgHom.commutes] at h1
    have h2 : algebraMap ℚ (C ℚ n) (2 * c) = 0 := by
      rw [map_mul, map_ofNat, two_mul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    have := algebraMap_injective (Q ℚ n) (h2.trans (map_zero _).symm)
    simpa using this
  have hu0 : ι (Q ℚ n) u = 0 := by
    have : (g : C ℚ n) * z = ι (Q ℚ n) u := by simp only [z, ← mul_assoc, hgs, one_mul]
    rw [← this, hc, hc0, map_zero, mul_zero]
  have : Q ℚ n u = 0 := by
    have := ι_sq_scalar (Q ℚ n) u
    rw [hu0, mul_zero] at this
    exact algebraMap_injective (Q ℚ n) (this.symm.trans (map_zero _).symm)
  rcases hq with h | h <;> rw [h] at this <;> norm_num at this

/-- `ρ(g)` is never `-M_{u₁} M_{u₂}` for `g ∈ Spin` and `Q(u₁) Q(u₂) = -1`. -/
theorem s21_false_of_rho_eq_negpair (g : Spin ℚ n) {u₁ u₂ : V ℚ n}
    (hq : Q ℚ n u₁ * Q ℚ n u₂ = -1) (h : ∀ v, rho ℚ n g v = -(s21_M u₁ (s21_M u₂ v))) : False := by
  have hsg : star (g : C ℚ n) * (g : C ℚ n) = 1 := spinGroup.star_mul_self_of_mem g.2
  have hgs : (g : C ℚ n) * star (g : C ℚ n) = 1 := spinGroup.mul_star_self_of_mem g.2
  set y := ι (Q ℚ n) u₁ * ι (Q ℚ n) u₂
  set w := ι (Q ℚ n) u₂ * ι (Q ℚ n) u₁
  have hwy : w * y = -1 := by
    rw [show w * y = ι (Q ℚ n) u₂ * (ι (Q ℚ n) u₁ * ι (Q ℚ n) u₁) * ι (Q ℚ n) u₂ by
      simp only [w, y, mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar,
      ← map_mul, hq, map_neg, map_one]
  have hyw : y * w = -1 := by
    rw [show y * w = ι (Q ℚ n) u₁ * (ι (Q ℚ n) u₂ * ι (Q ℚ n) u₂) * ι (Q ℚ n) u₁ by
      simp only [w, y, mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar,
      ← map_mul, mul_comm (Q ℚ n u₂), hq, map_neg, map_one]
  have key : ∀ v, (g : C ℚ n) * ι (Q ℚ n) v * star (g : C ℚ n) = -(y * ι (Q ℚ n) v * w) :=
    fun v => by
      rw [← ι_rho, h, map_neg, ← s21_ι_M, ← s21_ι_M]
      simp only [y, w, mul_assoc]
  set z := star (g : C ℚ n) * y
  have hz : ∀ v, involute z * ι (Q ℚ n) v = ι (Q ℚ n) v * z := fun v => by
    have hzeven : involute z = z := by
      simp only [z, y, map_mul, involute_ι, neg_mul_neg,
        spinGroup.involute_eq (spinGroup.star_mem g.2)]
    rw [hzeven]
    calc z * ι (Q ℚ n) v = star (g : C ℚ n) * (y * ι (Q ℚ n) v) := by simp only [z, mul_assoc]
      _ = star (g : C ℚ n) * (-(y * ι (Q ℚ n) v * w) * y) := by
          rw [neg_mul, mul_assoc (y * ι (Q ℚ n) v), hwy, mul_neg_one, neg_neg]
      _ = star (g : C ℚ n) * ((g : C ℚ n) * ι (Q ℚ n) v * star (g : C ℚ n) * y) := by rw [key]
      _ = ι (Q ℚ n) v * z := by simp only [z, ← mul_assoc, hsg, one_mul]
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul (Q ℚ n)
    s21_Q_nondegenerate z hz
  have hyg : y = (g : C ℚ n) * algebraMap ℚ (C ℚ n) c := by
    rw [← hc]; simp only [z, ← mul_assoc, hgs, one_mul]
  have hstar : y * star y = -1 := by
    rw [show star y = w by simp only [y, w, star_mul, star_ι, neg_mul_neg]]
    exact hyw
  rw [hyg, star_mul, star_algebraMap, mul_assoc, ← mul_assoc (algebraMap ℚ (C ℚ n) c),
    ← map_mul, Algebra.commutes, ← mul_assoc, hgs, one_mul] at hstar
  have : c * c = -1 := algebraMap_injective (Q ℚ n) (by rw [hstar, map_neg, map_one])
  nlinarith [mul_self_nonneg c]

/-- **The last plane**: an element of `Spin(V)` fixing the planes `0, …, 2n - 2` is `±1`
(`ρ(g)` acts on the last plane `U` as `1`; `-1_U`, the swap and minus the swap do not lift to
`Spin(V_ℚ)`: `s21_false_of_rho_eq_negpair`, `s21_false_of_rho_eq_refl`). -/
theorem s21_final (hn : 2 ≤ n) (g : Spin ℚ n) (hg : g ∈ SpinZ n)
    (hfix : s21_Fixes (rho ℚ n g) (2 * n - 1)) : g ∈ Subgroup.closure (s21_T n) := by
  set p : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hlast : ∀ i : Fin (2 * n), i ≠ p → i.val < 2 * n - 1 := fun i hi => by
    have h1 : i.val ≠ 2 * n - 1 := fun h => hi (Fin.ext h)
    have h2 := i.isLt
    omega
  have hpair := s21_pairing_rho g
  set x := rho ℚ n g (s21_E p) with hxdef
  set y := rho ℚ n g (s21_F p) with hydef
  have hxE : ∀ i, i ≠ p → pairing ℚ n x (s21_E i) = 0 := fun i hi => by
    rw [← (hfix i (hlast i hi)).1, hpair]; simp
  have hxF : ∀ i, i ≠ p → pairing ℚ n x (s21_F i) = 0 := fun i hi => by
    rw [← (hfix i (hlast i hi)).2, hpair]; simp [hi]
  have hyE : ∀ i, i ≠ p → pairing ℚ n y (s21_E i) = 0 := fun i hi => by
    rw [← (hfix i (hlast i hi)).1, hpair]; simp [Ne.symm hi]
  have hyF : ∀ i, i ≠ p → pairing ℚ n y (s21_F i) = 0 := fun i hi => by
    rw [← (hfix i (hlast i hi)).2, hpair]; simp
  have hdec : ∀ w : V ℚ n, (∀ i, i ≠ p → pairing ℚ n w (s21_E i) = 0) →
      (∀ i, i ≠ p → pairing ℚ n w (s21_F i) = 0) →
      w = pairing ℚ n w (s21_F p) • s21_E p + pairing ℚ n w (s21_E p) • s21_F p :=
    fun w hE hF => by
      conv_lhs => rw [s21_decomp w]
      rw [Finset.sum_eq_single p (fun i _ hi => by rw [hE i hi, zero_smul]) (by simp),
        Finset.sum_eq_single p (fun i _ hi => by rw [hF i hi, zero_smul]) (by simp), add_comm]
  have hQ2 : ∀ a b : ℚ, Q ℚ n (a • s21_E p + b • s21_F p) = a * b := fun a b => by
    rw [s21_Q_add, QuadraticMap.map_smul, QuadraticMap.map_smul]
    simp only [s21_Q_E, s21_Q_F, smul_eq_mul, mul_zero, zero_add, map_smul,
      LinearMap.smul_apply, s21_E_F, ite_true]
    ring
  have hP2 : ∀ a b c d : ℚ, pairing ℚ n (a • s21_E p + b • s21_F p) (c • s21_E p + d • s21_F p) =
      a * d + b * c := fun a b c d => by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      s21_E_E, s21_E_F, s21_F_E, s21_F_F, ite_true]
    ring
  have hx := hdec x hxE hxF
  have hy := hdec y hyE hyF
  obtain ⟨za, hza⟩ := s21_coord_F_int (hg.2 _ (s21_E_mem p)) p
  obtain ⟨zb, hzb⟩ := s21_coord_E_int (hg.2 _ (s21_E_mem p)) p
  obtain ⟨zc, hzc⟩ := s21_coord_F_int (hg.2 _ (s21_F_mem p)) p
  obtain ⟨zd, hzd⟩ := s21_coord_E_int (hg.2 _ (s21_F_mem p)) p
  rw [hza, hzb] at hx
  rw [hzc, hzd] at hy
  have h1 : za * zb = 0 := by
    have : Q ℚ n x = 0 := by rw [s21_Q_eq_half, hpair, ← s21_Q_eq_half, s21_Q_E]
    rw [hx, hQ2] at this
    exact_mod_cast this
  have h2 : zc * zd = 0 := by
    have : Q ℚ n y = 0 := by rw [s21_Q_eq_half, hpair, ← s21_Q_eq_half, s21_Q_F]
    rw [hy, hQ2] at this
    exact_mod_cast this
  have h3 : za * zd + zb * zc = 1 := by
    have : pairing ℚ n x y = 1 := by rw [hpair]; simp
    rw [hx, hy, hP2] at this
    exact_mod_cast this
  have hcases : (za = 1 ∧ zb = 0 ∧ zc = 0 ∧ zd = 1) ∨ (za = -1 ∧ zb = 0 ∧ zc = 0 ∧ zd = -1) ∨
      (za = 0 ∧ zb = 1 ∧ zc = 1 ∧ zd = 0) ∨ (za = 0 ∧ zb = -1 ∧ zc = -1 ∧ zd = 0) := by
    by_cases ha : za = 0
    · have hbc : zb * zc = 1 := by rw [ha] at h3; simpa using h3
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · have hd : zd = 0 := by rw [hc] at h2; simpa using h2
        exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc, hd⟩))
      · have hd : zd = 0 := by rw [hc] at h2; simpa using h2
        exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, hd⟩))
    · have hb : zb = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h ha
        · exact h
      have had : za * zd = 1 := by rw [hb] at h3; simpa using h3
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha', hd⟩ | ⟨ha', hd⟩
      · have hc : zc = 0 := by rw [hd] at h2; simpa using h2
        exact Or.inl ⟨ha', hb, hc, hd⟩
      · have hc : zc = 0 := by rw [hd] at h2; simpa using h2
        exact Or.inr (Or.inl ⟨ha', hb, hc, hd⟩)
  -- `ρ(g)` is determined by `x, y`
  have hext : ∀ L : V ℚ n →ₗ[ℚ] V ℚ n,
      (∀ i, i ≠ p → L (s21_E i) = s21_E i ∧ L (s21_F i) = s21_F i) →
      L (s21_E p) = x → L (s21_F p) = y → ∀ v, rho ℚ n g v = L v := by
    intro L hL hLx hLy v
    have hρL : (rho ℚ n g : V ℚ n →ₗ[ℚ] V ℚ n) = L := by
      refine s21_linearMap_ext (fun i => ?_) (fun i => ?_)
      · by_cases hi : i = p
        · rw [hi, hLx]; rfl
        · rw [(hL i hi).1]; exact (hfix i (hlast i hi)).1
      · by_cases hi : i = p
        · rw [hi, hLy]; rfl
        · rw [(hL i hi).2]; exact (hfix i (hlast i hi)).2
    exact congrArg (fun φ : V ℚ n →ₗ[ℚ] V ℚ n => φ v) hρL
  rcases hcases with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · -- `ρ(g) = 1`
    apply s21_mem_closure_of_rho_eq_id (by omega) g
    refine hext LinearMap.id (fun i _ => ⟨rfl, rfl⟩) ?_ ?_
    · rw [hx, ha, hb]; simp
    · rw [hy, hc, hd]; simp
  · -- `ρ(g) = -1` on the last plane: not in `Spin`
    exfalso
    refine s21_false_of_rho_eq_negpair g (u₁ := s21_E p + s21_F p) (u₂ := s21_E p - s21_F p)
      (by rw [s21_Q_E_add_F, s21_Q_E_sub_F]; norm_num) fun v => ?_
    have := hext (-(s21_M (s21_E p + s21_F p) ∘ₗ s21_M (s21_E p - s21_F p)))
      (fun i hi => by
        simp only [LinearMap.neg_apply, LinearMap.comp_apply]
        rw [(s21_M_sub_of_ne (Ne.symm hi)).1, (s21_M_sub_of_ne (Ne.symm hi)).2,
          (s21_M_add_of_ne (Ne.symm hi)).1, (s21_M_add_of_ne (Ne.symm hi)).2, neg_neg, neg_neg]
        exact ⟨rfl, rfl⟩)
      (by
        simp only [LinearMap.neg_apply, LinearMap.comp_apply]
        rw [s21_M_sub_E, s21_M_add_F, hx, ha, hb]
        simp)
      (by
        simp only [LinearMap.neg_apply, LinearMap.comp_apply]
        rw [s21_M_sub_F, s21_M_add_E, hy, hc, hd]
        simp) v
    rw [this]
    rfl
  · -- `ρ(g)` swaps `e_p, f_p`: not in `Spin`
    exfalso
    refine s21_false_of_rho_eq_refl g (u := s21_E p - s21_F p) (Or.inr (s21_Q_E_sub_F p))
      fun v => ?_
    have := hext (s21_M (s21_E p - s21_F p))
      (fun i hi => s21_M_sub_of_ne (Ne.symm hi))
      (by rw [s21_M_sub_E, hx, ha, hb]; simp)
      (by rw [s21_M_sub_F, hy, hc, hd]; simp) v
    rw [this, s21_Q_E_sub_F, neg_one_smul, neg_neg]
  · -- `ρ(g)` is minus the swap: not in `Spin`
    exfalso
    refine s21_false_of_rho_eq_refl g (u := s21_E p + s21_F p) (Or.inl (s21_Q_E_add_F p))
      fun v => ?_
    have := hext (-s21_M (s21_E p + s21_F p))
      (fun i hi => by
        simp only [LinearMap.neg_apply]
        rw [(s21_M_add_of_ne (Ne.symm hi)).1, (s21_M_add_of_ne (Ne.symm hi)).2, neg_neg, neg_neg]
        exact ⟨rfl, rfl⟩)
      (by
        simp only [LinearMap.neg_apply]
        rw [s21_M_add_E, hx, ha, hb]
        simp)
      (by
        simp only [LinearMap.neg_apply]
        rw [s21_M_add_F, hy, hc, hd]
        simp) v
    rw [this, s21_Q_E_add_F, one_smul]
    rfl

theorem s21_spinZ_le_closure (hn : 2 ≤ n) : SpinZ n ≤ Subgroup.closure (s21_T n) := by
  intro g hg
  obtain ⟨h, hh, hfix⟩ := s21_iterate hn g hg (2 * n - 1) (by omega)
  have hhg := s21_final hn (h * g) (mul_mem (s21_closure_le hh) hg) hfix
  have : g = h⁻¹ * (h * g) := by group
  rw [this]
  exact mul_mem (inv_mem hh) hhg

end Generation

/-- **`Spin(V)` is generated by the products `v₁ v₂` with `(v₁,v₁)_V = (v₂,v₂)_V = ±2`** (§2.1,
stated without reference in the paper; it follows from the generation of `O(V)`, for the even
unimodular lattice `V = U^{⊕ 2n}`, by reflections in vectors of square `±2` (Wall)). We assume the
paper's standing hypothesis `n ≥ 2`: for `n = 0` the paper's `Spin(V) = {±1}` has no such
generators, and the case `n = 1` was not checked.

Proof (the paper gives none): the generators lie in `Spin(V)` (`exists_spinZ_eq_ι_mul_ι`);
conversely an element of `Spin(V)` is reduced, one hyperbolic plane at a time, by the Euclidean
algorithm with Eichler transformations, to `±1` (`s21_spinZ_le_closure`, section `Generation`). -/
theorem spinZ_eq_closure (hn : 2 ≤ n) :
    SpinZ n = Subgroup.closure {g : Spin ℚ n | ∃ v₁ ∈ VZ n, ∃ v₂ ∈ VZ n,
      ((pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
        (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2)) ∧
      (g : C ℚ n) = ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂} :=
  le_antisymm (s21_spinZ_le_closure hn) s21_closure_le

end Integral

end WeilClasses
