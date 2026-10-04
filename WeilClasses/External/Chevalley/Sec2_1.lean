module

public import WeilClasses.PureSpinor.Sec2_1
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Chevalley, *The algebraic theory of spinors*, III.2.1 and III.2.2, as used in §2.1 of the paper

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954, Chapter III, §2:
the bilinear form `β` on spinors. For the spin representation `S = ⋀• H¹(X)` of
`V = H¹(X̂) ⊕ H¹(X)`, Chevalley's form is the Mukai pairing (1.2.3) `(s, t)_S = ∫_X τ(s) ∪ t`.

The paper uses, in §2.1:

* [III.2.2] `(m_v(s), t)_S = (s, m_v(t))_S` for `v ∈ V`, `s, t ∈ S` (so `m_{v,+-}` and `m_{v,-+}`
  are adjoint);
* [III.2.1] `(g(s), g(t))_S = N(g) (s, t)_S` for `g` in the Clifford group `G(V)`, with
  `N(g) = g τ(g)`.

Both are stated over a field `F` of characteristic zero; the integral statements of the paper follow
since `C(V) ⊆ C(V_ℚ)` and `G(V) ⊆ G(V_ℚ)`.

## Proofs

III.2.2 is proved in the model: `m_{(θ, w)} = L_w + D_θ`, the reversal `τ` turns left
multiplication by `w` into right multiplication, and `∫_X τ(D_θ s) t = ∫_X τ(s) D_θ t` because
`D_θ` is an antiderivation and `∫_X ∘ D_θ = 0` (a contraction has no top-degree component).
Induction on `x ∈ C(V)` then gives the general adjunction `(m_x s, t)_S = (s, m_{τ(x)} t)_S`
(`sa_mukai_m_reverse`), from which III.2.1 follows: `τ(g) g = N(g)` is a scalar.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ### Helpers (prefix `sa_`) -/

section Helpers

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `m_{(θ, w)} = L_w + D_θ`. -/
theorem sa_m_ι_apply (θ : Module.Dual F (H1 F n)) (w : H1 F n) (x : S F n) :
    m F n (ι (Q F n) (θ, w)) x = ExteriorAlgebra.ι F w * x + D F n θ x := by
  simp only [m, CliffordAlgebra.lift_ι_apply, cliffordOp, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, L, LinearMap.mul_apply']

omit [CharZero F] in
/-- The coordinate functional `f_i` is the `i`-th coordinate of the standard basis. -/
theorem sa_f_eq_coord (i : Fin (2 * n)) : f F n i = (Pi.basisFun F (Fin (2 * n))).coord i := by
  ext x
  simp [f]

omit [CharZero F] in
/-- `∫_X D_θ z = 0`: a contraction has no top-degree component. -/
theorem sa_integral_D (θ : Module.Dual F (H1 F n)) (z : S F n) :
    integral F n (D F n θ z) = 0 := by
  have hθ : θ = ∑ i, θ (e F n i) • (Pi.basisFun F (Fin (2 * n))).coord i := by
    apply (Pi.basisFun F (Fin (2 * n))).ext
    intro j
    rw [LinearMap.sum_apply, Finset.sum_eq_single j]
    · simp [e]
    · intro i _ hij
      simp [Pi.basisFun_apply, Ne.symm hij]
    · simp
  conv_lhs => rw [← (basisS F n).sum_repr z]
  simp only [map_sum, map_smul]
  refine Finset.sum_eq_zero fun K _ => ?_
  refine smul_eq_zero_of_right _ ?_
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
      show (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra (K.erase i) = basisS F n (K.erase i)
        from rfl, h0, smul_zero]
  · simp

omit [CharZero F] in
/-- `∫_X τ(D_θ s) t = ∫_X τ(s) D_θ t`. -/
theorem sa_integral_tau_D (θ : Module.Dual F (H1 F n)) (s t : S F n) :
    integral F n (tau F n (D F n θ s) * t) = integral F n (tau F n s * D F n θ t) := by
  induction s using CliffordAlgebra.left_induction generalizing t with
  | algebraMap r =>
    have h0 : D F n θ (algebraMap F (S F n) r) = 0 :=
      contractLeft_algebraMap (Q := (0 : QuadraticForm F (H1 F n))) θ r
    have h1 : tau F n (algebraMap F (S F n) r) = algebraMap F (S F n) r :=
      CliffordAlgebra.reverse.commutes r
    rw [h0, map_zero, zero_mul, map_zero, h1, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, map_smul, sa_integral_D, smul_zero]
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

/-- `m_v` is self-adjoint for the Mukai pairing: `(m_v s, t)_S = (s, m_v t)_S`. -/
theorem sa_mukai_m_ι (v : V F n) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) t = mukai F n s (m F n (ι (Q F n) v) t) := by
  obtain ⟨θ, w⟩ := v
  show integral F n (tau F n _ * t) = integral F n (tau F n s * _)
  rw [sa_m_ι_apply, sa_m_ι_apply, map_add, add_mul, map_add, mul_add, map_add,
    sa_integral_tau_D]
  congr 1
  simp only [tau, CliffordAlgebra.reverse.map_mul]
  rw [show (ExteriorAlgebra.ι F w : S F n) = ι (0 : QuadraticForm F (H1 F n)) w from rfl,
    CliffordAlgebra.reverse_ι, mul_assoc]

/-- **The adjoint of `m_x` is `m_{τ(x)}`**: `(m_x s, t)_S = (s, m_{τ(x)} t)_S` for every
`x ∈ C(V_F)`, by induction on `x` from `sa_mukai_m_ι`. -/
theorem sa_mukai_m_reverse (x : C F n) (s t : S F n) :
    mukai F n (m F n x s) t = mukai F n s (m F n (reverse x) t) := by
  induction x using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, LinearMap.smul_apply, map_smul]
  | ι v => rw [reverse_ι, sa_mukai_m_ι]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, reverse.map_mul, map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, ha, hb, map_add, map_add,
      LinearMap.add_apply, map_add]

end Helpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, III.2.2]**, special case used in §2.1: each `m_v`, `v ∈ V_F`, is self-adjoint for
the Mukai pairing: `(m_v(s), t)_S = (s, m_v(t))_S` for all `s, t ∈ S_F`. In particular
`m_{v,+-} : S⁺ → S⁻` and `m_{v,-+} : S⁻ → S⁺` are adjoint. -/
theorem chevalley_III_2_2 (v : V F n) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) t = mukai F n s (m F n (ι (Q F n) v) t) := by
  exact sa_mukai_m_ι v s t

/-- **[Chevalley, III.2.1]**, special case used in §2.1: for `g` in the Clifford group `G(V_F)` with
norm `N(g) = g τ(g) = c` (a scalar, `WeilClasses.exists_mul_reverse_eq_algebraMap`),
`(g(s), g(t))_S = N(g) (s, t)_S` for all `s, t ∈ S_F`. -/
theorem chevalley_III_2_1 (x : (C F n)ˣ) (hx : x ∈ cliffordGroup F n) (c : F)
    (hc : (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) c) (s t : S F n) :
    mukai F n (m F n (x : C F n) s) (m F n (x : C F n) t) = c * mukai F n s t := by
  -- `τ(x) = x⁻¹ c`, hence `τ(x) x = c` (membership in the Clifford group is not needed).
  have _ := hx
  have hrev : reverse (x : C F n) * (x : C F n) = algebraMap F (C F n) c := by
    have h1 : reverse (x : C F n) = ((x⁻¹ : (C F n)ˣ) : C F n) * algebraMap F (C F n) c := by
      rw [← hc, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h1, mul_assoc, Algebra.commutes, Units.inv_mul_cancel_left]
  rw [sa_mukai_m_reverse, ← Module.End.mul_apply, ← map_mul, hrev, AlgHom.commutes,
    Module.algebraMap_end_apply, map_smul, smul_eq_mul]

end WeilClasses
