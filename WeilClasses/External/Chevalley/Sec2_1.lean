module

public import WeilClasses.PureSpinor.Sec2_1

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
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, III.2.2]**, special case used in §2.1: each `m_v`, `v ∈ V_F`, is self-adjoint for
the Mukai pairing: `(m_v(s), t)_S = (s, m_v(t))_S` for all `s, t ∈ S_F`. In particular
`m_{v,+-} : S⁺ → S⁻` and `m_{v,-+} : S⁻ → S⁺` are adjoint. -/
theorem chevalley_III_2_2 (v : V F n) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) t = mukai F n s (m F n (ι (Q F n) v) t) := by
  sorry

/-- **[Chevalley, III.2.1]**, special case used in §2.1: for `g` in the Clifford group `G(V_F)` with
norm `N(g) = g τ(g) = c` (a scalar, `WeilClasses.exists_mul_reverse_eq_algebraMap`),
`(g(s), g(t))_S = N(g) (s, t)_S` for all `s, t ∈ S_F`. -/
theorem chevalley_III_2_1 (x : (C F n)ˣ) (hx : x ∈ cliffordGroup F n) (c : F)
    (hc : (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) c) (s t : S F n) :
    mukai F n (m F n (x : C F n) s) (m F n (x : C F n) t) = c * mukai F n s t := by
  sorry

end WeilClasses
