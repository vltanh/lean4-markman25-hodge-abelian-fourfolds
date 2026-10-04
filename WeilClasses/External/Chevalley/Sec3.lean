module

public import WeilClasses.PureSpinor.Defs
public import WeilClasses.External.Chevalley.Sec2_1
public import WeilClasses.External.Chevalley.Sec2_4
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Chevalley, *The algebraic theory of spinors*, III.3.2 and III.4.5 (as used in §3.1 of the paper)

C. Chevalley, *The algebraic theory of spinors*, Columbia University Press (1954), III.3.2 and
III.4.5: there is a `Spin(V)`-equivariant homomorphism `⋀^{2n}_+ V → Sym²(S⁺)`, defined on the
span of the lines `⋀^{2n} W` of the maximal isotropic subspaces `W` (of the family of `S⁺`), which
maps `⋀^{2n} W` onto the line spanned by `u²`, `u` the even pure spinor with `ker m_u = W`.

The paper uses it in the proof of Lemma 3.1.1 (TeX lines 1481–1486) in the following form: if
`g ∈ Spin(V)` preserves `W = ker m_u`, then `g` acts on the line of `u²` as `⋀^{2n} ρ(g)` acts on
`⋀^{2n} W`, i.e. by `det(ρ(g)|_W)`; so `g u = c u` with `c² = det(ρ(g)|_W)` (in particular
`c = ±1` when `det(ρ(g)|_W) = 1`). This is also the relation `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ` of §2.2. We state
this consequence over a field `F` of characteristic `0`.

## The theory of pure spinors used here (and in `WeilClasses.External.Chevalley.Sec2_2`)

This file also develops, in the Fock model `S = ⋀ H`, `V = H* × H`, the part of Chevalley's
Chapter III that the statements of `WeilClasses.External.Chevalley.Sec2_2` and the statement below
need (helpers prefixed `sa_`), without orbit or transitivity theorems from outside:

* *intertwiners* (`sa_Inter`): pin elements `y` with their conjugation action `σ` on `V`; they
  transport annihilators, `ker m_{y s} = σ(ker m_s)`, and the spaces `K(W)` of spinors killed by
  `W` (`sa_kill`), `K(σ W) = m_y K(W)`;
* `K(H* × 0) = F·1` and `K(0 × H) = F·[pt]`, by coordinates (Tau Ceti's exterior basis calculus);
* **normal form** (`sa_normal_form`): every maximal isotropic `W` is `σ_y(H* × 0)` for a product
  `y` of vectors of norm `-1` and an element `exp(J B)`, `B ∈ ⋀² H`
  (`WeilClasses.External.Chevalley.Sec2_4`). By induction on `dim (W ∩ (0 × H))`: a reflection in
  `(-b*, b)`, `(0, b) ∈ W`, lowers it, and when it is `0`, `W` is the graph of an alternating map
  `H* → H`, which is `exp(J B)(H* × 0)`. Hence `K(W)` is a line spanned by an even or odd spinor;
* **pairs** (`sa_pair`): complementary `W₁, W₂` with `W₁` in the even family are
  `ρ(g)(H* × 0), ρ(g)(0 × H)` for some `g ∈ Spin(V)` (the second step uses `exp(J β)`,
  `β ∈ ⋀² H*`, which fixes `H* × 0`);
* the left ideal `C(V)·[pt_X̂] ≅ S` (`sa_mul_iotaX_mul_ptHatC`: `y · s[pt_X̂] = (m_y s)[pt_X̂]`,
  and its mirror `sa_ptHatC_mul_iotaX_mul`), which gives the equivariance of Chevalley's `φ`
  (`sa_varphi_equivariant`); `[pt_X̂] ≠ 0` (`sa_ptHatC_ne_zero`);
* the top products `w₁ ⋯ w_{2n}` of a maximal isotropic `W` (`sa_topMap`, an alternating map),
  which transform by `det` (`sa_topMap_comp`), and `φ(u ⊗ u) = c · w₁ ⋯ w_{2n} ≠ 0` for a nonzero
  even pure spinor `u` with `ker m_u = W` (`sa_varphi_self`).

The statement below follows: `ker m_{g u} = ρ(g) W = W`, so `g u = c u` by uniqueness (III.1.4),
and `c² φ(u ⊗ u) = φ(g u ⊗ g u) = g φ(u ⊗ u) g* = det(ρ(g)|_W) φ(u ⊗ u)`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

section Core

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-! ### Intertwiners -/

/-- An element `y` of the pin group of `V_F`, together with its (untwisted) conjugation action
`σ` on `V_F`: `y x y* = σ(x)`. -/
structure sa_Inter (F : Type*) [Field F] [CharZero F] (n : ℕ) where
  /-- The element of `C(V_F)`. -/
  y : C F n
  /-- Its conjugation action on `V_F`. -/
  σ : V F n ≃ₗ[F] V F n
  pin : y ∈ pinGroup (Q F n)
  conj : ∀ x, y * ι (Q F n) x * star y = ι (Q F n) (σ x)

namespace sa_Inter

theorem mul_star (a : sa_Inter F n) : a.y * star a.y = 1 := pinGroup.mul_star_self_of_mem a.pin

theorem star_mul (a : sa_Inter F n) : star a.y * a.y = 1 := pinGroup.star_mul_self_of_mem a.pin

theorem m_star_m (a : sa_Inter F n) (s : S F n) : m F n (star a.y) (m F n a.y s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, a.star_mul, map_one, Module.End.one_apply]

theorem m_m_star (a : sa_Inter F n) (s : S F n) : m F n a.y (m F n (star a.y) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, a.mul_star, map_one, Module.End.one_apply]

theorem m_injective (a : sa_Inter F n) : Function.Injective (m F n a.y) :=
  Function.LeftInverse.injective a.m_star_m

theorem m_ι_σ (a : sa_Inter F n) (x : V F n) (s : S F n) :
    m F n (ι (Q F n) (a.σ x)) (m F n a.y s) = m F n a.y (m F n (ι (Q F n) x) s) := by
  rw [← a.conj, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, a.m_star_m]

/-- The action `σ` preserves the quadratic form. -/
theorem Q_σ (a : sa_Inter F n) (x : V F n) : Q F n (a.σ x) = Q F n x := by
  apply algebraMap_injective (Q F n)
  rw [← ι_sq_scalar, ← ι_sq_scalar, ← a.conj]
  calc a.y * ι (Q F n) x * star a.y * (a.y * ι (Q F n) x * star a.y)
      = a.y * ι (Q F n) x * (star a.y * a.y) * ι (Q F n) x * star a.y := by
        simp only [mul_assoc]
    _ = a.y * (ι (Q F n) x * ι (Q F n) x) * star a.y := by
        rw [a.star_mul, mul_one, mul_assoc a.y]
    _ = ι (Q F n) x * ι (Q F n) x := by
        rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, a.mul_star, mul_one]

/-- Conjugating a product of vectors. -/
theorem conj_prod (a : sa_Inter F n) (l : List (V F n)) :
    a.y * (l.map (ι (Q F n))).prod * star a.y = (l.map (fun x => ι (Q F n) (a.σ x))).prod := by
  induction l with
  | nil => simp [a.mul_star]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← a.conj]
    calc a.y * (ι (Q F n) x * (l.map (ι (Q F n))).prod) * star a.y
        = a.y * ι (Q F n) x * (star a.y * a.y) * (l.map (ι (Q F n))).prod * star a.y := by
          rw [a.star_mul, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

/-- Composition of intertwiners. -/
noncomputable def comp (a b : sa_Inter F n) : sa_Inter F n where
  y := a.y * b.y
  σ := b.σ.trans a.σ
  pin := mul_mem a.pin b.pin
  conj x := by
    rw [StarMul.star_mul, LinearEquiv.trans_apply, ← a.conj, ← b.conj]
    simp only [mul_assoc]

/-- A spin element as an intertwiner. -/
noncomputable def ofSpin (g : Spin F n) : sa_Inter F n where
  y := g
  σ := rho F n g
  pin := spinGroup.mem_pin g.2
  conj x := (ι_rho F n g x).symm

/-- `x ↦ -x - (v, x)_V v`, the conjugation by a vector `v` with `Q(v) = -1`. -/
noncomputable def reflAux (v : V F n) : V F n →ₗ[F] V F n :=
  -LinearMap.id - (QuadraticMap.polarBilin (Q F n) v).smulRight v

omit [CharZero F] in
theorem reflAux_apply (v x : V F n) :
    reflAux v x = -x - QuadraticMap.polar (Q F n) v x • v := rfl

omit [CharZero F] in
theorem reflAux_reflAux {v : V F n} (hv : Q F n v = -1) (x : V F n) :
    reflAux v (reflAux v x) = x := by
  have hvv : QuadraticMap.polar (Q F n) v v = -2 := by
    rw [QuadraticMap.polar_self, hv]; norm_num
  rw [reflAux_apply, reflAux_apply, QuadraticMap.polar_sub_right, QuadraticMap.polar_neg_right,
    QuadraticMap.polar_smul_right, hvv]
  module

/-- The intertwiner of a vector `v` with `Q(v) = -1`. -/
noncomputable def ofVec (v : V F n) (hv : Q F n v = -1) : sa_Inter F n where
  y := ι (Q F n) v
  σ := LinearEquiv.ofInvolutive (reflAux v) (reflAux_reflAux hv)
  pin := ι_mem_pinGroup hv
  conj x := by
    rw [star_ι, mul_neg, ι_mul_ι_mul_ι, hv]
    show _ = ι (Q F n) (reflAux v x)
    rw [reflAux_apply, ← map_neg]
    congr 1
    module

theorem ofVec_mem_odd (v : V F n) (hv : Q F n v = -1) :
    (ofVec v hv).y ∈ evenOdd (Q F n) 1 := ι_mem_evenOdd_one _ v

end sa_Inter

/-! ### Annihilators and the spinors killed by a subspace -/

theorem sa_mOf_apply (s : S F n) (v : V F n) : mOf F n s v = m F n (ι (Q F n) v) s := rfl

theorem sa_mem_ann (s : S F n) (v : V F n) : v ∈ ann F n s ↔ m F n (ι (Q F n) v) s = 0 :=
  Iff.rfl

/-- `ker m_{y s} = σ(ker m_s)`. -/
theorem sa_ann_m (a : sa_Inter F n) (s : S F n) :
    ann F n (m F n a.y s) = (ann F n s).map (a.σ : V F n →ₗ[F] V F n) := by
  ext v
  rw [sa_mem_ann, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨a.σ.symm v, ?_, by simp⟩
    rw [sa_mem_ann]
    have h' := a.m_ι_σ (a.σ.symm v) s
    rw [LinearEquiv.apply_symm_apply, h] at h'
    exact a.m_injective (by rw [← h', map_zero])
  · rintro ⟨x, hx, rfl⟩
    rw [sa_mem_ann] at hx
    rw [LinearEquiv.coe_coe, a.m_ι_σ, hx, map_zero]

/-- The spinors killed by every vector of a subspace `W ⊆ V_F`. -/
noncomputable def sa_kill (W : Submodule F (V F n)) : Submodule F (S F n) where
  carrier := {s | ∀ v ∈ W, m F n (ι (Q F n) v) s = 0}
  add_mem' {a b} ha hb v hv := by rw [map_add, ha v hv, hb v hv, add_zero]
  zero_mem' _ _ := map_zero _
  smul_mem' c a ha v hv := by rw [map_smul, ha v hv, smul_zero]

theorem sa_mem_kill_iff (W : Submodule F (V F n)) (s : S F n) :
    s ∈ sa_kill W ↔ W ≤ ann F n s :=
  ⟨fun h v hv => h v hv, fun h _ hv => h hv⟩

/-- `K(σ W) = m_y K(W)`. -/
theorem sa_kill_map (a : sa_Inter F n) (W : Submodule F (V F n)) :
    sa_kill (W.map (a.σ : V F n →ₗ[F] V F n)) = (sa_kill W).map (m F n a.y) := by
  ext s
  constructor
  · intro hs
    refine ⟨m F n (star a.y) s, fun x hx => ?_, a.m_m_star s⟩
    have h := hs (a.σ x) ⟨x, hx, rfl⟩
    rw [← a.m_m_star s, a.m_ι_σ] at h
    exact a.m_injective (by rw [h, map_zero])
  · rintro ⟨t, ht, rfl⟩ v ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, a.m_ι_σ, ht x hx, map_zero]

/-- A subspace's image under an intertwiner is maximal isotropic if the subspace is. -/
theorem sa_isMaxIsotropic_map (a : sa_Inter F n) {W : Submodule F (V F n)}
    (hW : IsMaxIsotropic F n W) : IsMaxIsotropic F n (W.map (a.σ : V F n →ₗ[F] V F n)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, a.Q_σ, hW.1 x hx]
  · rw [LinearEquiv.finrank_map_eq]
    exact hW.2

/-! ### Parity -/

theorem sa_m_ι_mem_evenOdd (v : V F n) {j : ZMod 2} {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) j) :
    m F n (ι (Q F n) v) s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) (j + 1) := by
  obtain ⟨θ, w⟩ := v
  rw [sa_m_ι_apply]
  refine Submodule.add_mem _ ?_ (contractLeft_mem_evenOdd θ hs)
  have := SetLike.mul_mem_graded (ι_mem_evenOdd_one (0 : QuadraticForm F (H1 F n)) w) hs
  rwa [add_comm] at this

/-- `m` respects the `ℤ/2`-gradings of `C(V)` and `S`. -/
theorem sa_m_mem_evenOdd {i j : ZMod 2} {x : C F n} (hx : x ∈ evenOdd (Q F n) i) {s : S F n}
    (hs : s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) j) :
    m F n x s ∈ evenOdd (0 : QuadraticForm F (H1 F n)) (i + j) := by
  have hi : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases hi i with rfl | rfl
  · induction x, hx using even_induction generalizing j s with
    | algebraMap r =>
      rw [AlgHom.commutes, Module.algebraMap_end_apply, zero_add]
      exact Submodule.smul_mem _ r hs
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hx hs) (hy hs)
    | ι_mul_ι_mul m₁ m₂ x _ hx =>
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have h := sa_m_ι_mem_evenOdd m₁ (sa_m_ι_mem_evenOdd m₂ (hx hs))
      rw [add_assoc (0 + j), show (1 + 1 : ZMod 2) = 0 from rfl, add_zero] at h
      exact h
  · induction x, hx using odd_induction generalizing j s with
    | ι v =>
      rw [add_comm]
      exact sa_m_ι_mem_evenOdd v hs
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hx hs) (hy hs)
    | ι_mul_ι_mul m₁ m₂ x _ hx =>
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have h := sa_m_ι_mem_evenOdd m₁ (sa_m_ι_mem_evenOdd m₂ (hx hs))
      rw [add_assoc (1 + j), show (1 + 1 : ZMod 2) = 0 from rfl, add_zero] at h
      exact h

omit [CharZero F] in
theorem sa_one_mem_Splus : (1 : S F n) ∈ evenOdd (0 : QuadraticForm F (H1 F n)) 0 := by
  exact SetLike.one_mem_graded (evenOdd (0 : QuadraticForm F (H1 F n)))


/-! ### The standard maximal isotropic subspaces `H* × 0` and `0 × H` -/

variable (F n) in
/-- `H¹(X̂, F) × 0 = H* × 0 = ker m_1`. -/
noncomputable def sa_W0 : Submodule F (V F n) :=
  LinearMap.ker (LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n))

variable (F n) in
/-- `0 × H¹(X, F) = 0 × H = ker m_{[pt]}`. -/
noncomputable def sa_W0' : Submodule F (V F n) :=
  LinearMap.ker (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n))

omit [CharZero F] in
theorem sa_mem_W0 (v : V F n) : v ∈ sa_W0 F n ↔ v.2 = 0 := Iff.rfl

omit [CharZero F] in
theorem sa_mem_W0' (v : V F n) : v ∈ sa_W0' F n ↔ v.1 = 0 := Iff.rfl

omit [CharZero F] in
theorem sa_W0_inf_W0' : sa_W0 F n ⊓ sa_W0' F n = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨θ, w⟩ ⟨h1, h2⟩
  rw [SetLike.mem_coe, sa_mem_W0] at h1
  rw [SetLike.mem_coe, sa_mem_W0'] at h2
  simp only at h1 h2
  rw [h1, h2, Submodule.mem_bot]
  rfl

omit [CharZero F] in
theorem sa_e_eq (i : Fin (2 * n)) : e F n i = Pi.basisFun F (Fin (2 * n)) i := by
  simp [e]

omit [CharZero F] in
theorem sa_basisS_eq : basisS F n = (Pi.basisFun F (Fin (2 * n))).ExteriorAlgebra := rfl

omit [CharZero F] in
theorem sa_basisS_empty : basisS F n ∅ = 1 := by
  rw [sa_basisS_eq, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_empty),
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_zero_apply]

theorem sa_m_ι_one (v : V F n) : m F n (ι (Q F n) v) 1 = ExteriorAlgebra.ι F v.2 := by
  obtain ⟨θ, w⟩ := v
  rw [sa_m_ι_apply, mul_one,
    show D F n θ 1 = 0 from contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) θ, add_zero]

/-- `ker m_1 = H* × 0`. -/
theorem sa_ann_one : ann F n 1 = sa_W0 F n := by
  ext v
  rw [sa_mem_ann, sa_m_ι_one, sa_mem_W0, ← map_zero (ExteriorAlgebra.ι F),
    ExteriorAlgebra.ι_inj]

omit [CharZero F] in
/-- `w ∧ [pt] = 0`. -/
theorem sa_ι_mul_pt (w : H1 F n) : ExteriorAlgebra.ι F w * pt F n = 0 := by
  have hw : w = ∑ i, w i • Pi.basisFun F (Fin (2 * n)) i := by
    conv_lhs => rw [← (Pi.basisFun F (Fin (2 * n))).sum_repr w]
    simp only [Pi.basisFun_repr]
  rw [hw, map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_mul_assoc, pt, sa_basisS_eq, TauCeti.ExteriorAlgebra.ι_mul_basis,
    ite_eq_left (Finset.mem_univ i), smul_zero]

omit [CharZero F] in
theorem sa_pt_ne_zero : pt F n ≠ 0 := (basisS F n).ne_zero _

omit [CharZero F] in
/-- `D_θ [pt] = 0` only for `θ = 0`. -/
theorem sa_D_pt_eq_zero_iff (θ : Module.Dual F (H1 F n)) : D F n θ (pt F n) = 0 ↔ θ = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero, LinearMap.zero_apply]⟩
  apply (Pi.basisFun F (Fin (2 * n))).ext
  intro j
  have key : ExteriorAlgebra.ι F (e F n j) * D F n θ (pt F n) = θ (e F n j) • pt F n := by
    have h2 : D F n θ (ExteriorAlgebra.ι F (e F n j) * pt F n) =
        θ (e F n j) • pt F n - ExteriorAlgebra.ι F (e F n j) * D F n θ (pt F n) :=
      contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) _ _ _
    rw [sa_ι_mul_pt, map_zero] at h2
    exact (sub_eq_zero.mp h2.symm).symm
  rw [h, mul_zero, eq_comm, smul_eq_zero] at key
  rcases key with h3 | h3
  · rw [← sa_e_eq, h3, LinearMap.zero_apply]
  · exact absurd h3 sa_pt_ne_zero

/-- `ker m_{[pt]} = 0 × H`. -/
theorem sa_ann_pt : ann F n (pt F n) = sa_W0' F n := by
  ext ⟨θ, w⟩
  rw [sa_mem_ann, sa_m_ι_apply, sa_ι_mul_pt, zero_add, sa_D_pt_eq_zero_iff, sa_mem_W0']

omit [CharZero F] in
/-- In the exterior basis, `w_i ∧ D_{f_i}` is the projection onto the basis vectors `e_K` with
`i ∈ K`. -/
theorem sa_repr_proj (i : Fin (2 * n)) (s : S F n) (K : Finset (Fin (2 * n))) :
    (basisS F n).repr (ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s) K =
      if i ∈ K then (basisS F n).repr s K else 0 := by
  have h : ∀ K' : Finset (Fin (2 * n)),
      ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) (basisS F n K') =
        if i ∈ K' then basisS F n K' else 0 := by
    intro K'
    rw [sa_f_eq_coord, sa_e_eq, sa_basisS_eq]
    exact TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis _ i K'
  conv_lhs => rw [← (basisS F n).sum_repr s]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm, h]
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single K]
  · split_ifs with hK
    · simp
    · simp
  · intro K' _ hK'
    split_ifs with hK''
    · simp [hK']
    · simp
  · simp

/-- `K(H* × 0) = F·1`. -/
theorem sa_kill_W0 : sa_kill (sa_W0 F n) = Submodule.span F {1} := by
  apply le_antisymm
  · intro s hs
    have hD : ∀ i, D F n (f F n i) s = 0 := by
      intro i
      have h := hs (f F n i, 0) (by rw [sa_mem_W0])
      rwa [sa_m_ι_apply, map_zero, zero_mul, zero_add] at h
    have hc : ∀ K, K ≠ ∅ → (basisS F n).repr s K = 0 := by
      intro K hK
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hK
      have h := sa_repr_proj i s K
      rw [hD i, mul_zero, map_zero, Finsupp.zero_apply, ite_eq_left hi] at h
      exact h.symm
    rw [← (basisS F n).sum_repr s, Finset.sum_eq_single ∅ (fun K _ hK => by rw [hc K hK, zero_smul])
      (by simp), sa_basisS_empty]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    intro v hv
    rw [sa_m_ι_one, (sa_mem_W0 v).mp hv, map_zero]

/-- `K(0 × H) = F·[pt]`. -/
theorem sa_kill_W0' : sa_kill (sa_W0' F n) = Submodule.span F {pt F n} := by
  apply le_antisymm
  · intro s hs
    have hL : ∀ i, ExteriorAlgebra.ι F (e F n i) * s = 0 := by
      intro i
      have h := hs (0, e F n i) (by rw [sa_mem_W0'])
      rwa [sa_m_ι_apply, map_zero, LinearMap.zero_apply, add_zero] at h
    have hc : ∀ K, K ≠ Finset.univ → (basisS F n).repr s K = 0 := by
      intro K hK
      obtain ⟨i, hi⟩ : ∃ i, i ∉ K :=
        not_forall.mp fun h => hK (Finset.eq_univ_iff_forall.mpr h)
      have h1 : D F n (f F n i) (ExteriorAlgebra.ι F (e F n i) * s) =
          f F n i (e F n i) • s - ExteriorAlgebra.ι F (e F n i) * D F n (f F n i) s :=
        contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) _ _ _
      rw [hL i, map_zero, show f F n i (e F n i) = 1 by simp [f, e], one_smul, eq_comm,
        sub_eq_zero] at h1
      have h := sa_repr_proj i s K
      rw [← h1, ite_eq_right hi] at h
      exact h
    rw [← (basisS F n).sum_repr s, Finset.sum_eq_single Finset.univ
      (fun K _ hK => by rw [hc K hK, zero_smul]) (by simp)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    rintro ⟨θ, w⟩ hv
    rw [sa_mem_W0'] at hv
    simp only at hv
    rw [hv, sa_m_ι_apply, sa_ι_mul_pt, map_zero, LinearMap.zero_apply, add_zero]

omit [CharZero F] in
theorem sa_finrank_H1 : Module.finrank F (H1 F n) = 2 * n := by simp

omit [CharZero F] in
theorem sa_W0_isMax : IsMaxIsotropic F n (sa_W0 F n) := by
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [sa_mem_W0] at hv
    rw [QuadraticForm.dualProd_apply, hv, map_zero]
  · rw [sa_W0, LinearMap.ker_snd, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
      Subspace.dual_finrank_eq, sa_finrank_H1]

omit [CharZero F] in
theorem sa_W0'_isMax : IsMaxIsotropic F n (sa_W0' F n) := by
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [sa_mem_W0'] at hv
    rw [QuadraticForm.dualProd_apply, hv, LinearMap.zero_apply]
  · rw [sa_W0', LinearMap.ker_fst, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
      sa_finrank_H1]

/-! ### Graphs of alternating maps -/

omit [CharZero F] in
/-- Vectors of an isotropic subspace are orthogonal. -/
theorem sa_polar_of_isotropic {W : Submodule F (V F n)} (hW : ∀ v ∈ W, Q F n v = 0) {x y : V F n}
    (hx : x ∈ W) (hy : y ∈ W) : QuadraticMap.polar (Q F n) x y = 0 := by
  rw [QuadraticMap.polar, hW _ (W.add_mem hx hy), hW x hx, hW y hy, sub_zero, sub_zero]

omit [CharZero F] in
theorem sa_polar_apply (x y : V F n) : QuadraticMap.polar (Q F n) x y = x.1 y.2 + y.1 x.2 :=
  TauCeti.polar_dualProd x y

omit [CharZero F] in
/-- A maximal isotropic `W` with `W ∩ (0 × H) = 0` is the graph `{(θ, A θ)}` of an alternating map
`A : H* → H`. -/
theorem sa_graph_upper (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W)
    (h0 : W ⊓ sa_W0' F n = ⊥) :
    ∃ A : Module.Dual F (H1 F n) →ₗ[F] H1 F n, (∀ θ : Module.Dual F (H1 F n), θ (A θ) = 0) ∧
      ∀ v : V F n, v ∈ W ↔ v.2 = A v.1 := by
  let π : W →ₗ[F] Module.Dual F (H1 F n) :=
    (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n)).comp W.subtype
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hmem : (x : V F n) ∈ W ⊓ sa_W0' F n := ⟨x.2, hx⟩
    rw [h0, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact Subtype.ext hmem
  have hsurj : Function.Surjective π := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [hW.2, Subspace.dual_finrank_eq, sa_finrank_H1]
  let eW := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
  let A : Module.Dual F (H1 F n) →ₗ[F] H1 F n :=
    (LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n)).comp (W.subtype.comp eW.symm.toLinearMap)
  have hfst : ∀ θ, ((eW.symm θ : W) : V F n).1 = θ := by
    intro θ
    have := eW.apply_symm_apply θ
    exact this
  have hgraph : ∀ θ, ((θ, A θ) : V F n) = (eW.symm θ : W) := by
    intro θ
    exact Prod.ext (hfst θ).symm rfl
  refine ⟨A, fun θ => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · have h := hW.1 _ (hgraph θ ▸ (eW.symm θ).2)
    rwa [QuadraticForm.dualProd_apply] at h
  · have h1 : eW.symm (π ⟨v, hv⟩) = ⟨v, hv⟩ := eW.symm_apply_apply ⟨v, hv⟩
    have h2 : π ⟨v, hv⟩ = v.1 := rfl
    show v.2 = ((eW.symm v.1 : W) : V F n).2
    rw [← h2, h1]
  · have : v = ((v.1, A v.1) : V F n) := Prod.ext rfl hv
    rw [this, hgraph]
    exact (eW.symm v.1).2

omit [CharZero F] in
/-- A maximal isotropic `W` with `W ∩ (H* × 0) = 0` is the graph `{(A w, w)}` of an alternating
map `A : H → H*`. -/
theorem sa_graph_lower (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W)
    (h0 : W ⊓ sa_W0 F n = ⊥) :
    ∃ A : H1 F n →ₗ[F] Module.Dual F (H1 F n), (∀ w : H1 F n, A w w = 0) ∧
      ∀ v : V F n, v ∈ W ↔ v.1 = A v.2 := by
  let π : W →ₗ[F] H1 F n := (LinearMap.snd F (Module.Dual F (H1 F n)) (H1 F n)).comp W.subtype
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hmem : (x : V F n) ∈ W ⊓ sa_W0 F n := ⟨x.2, hx⟩
    rw [h0, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact Subtype.ext hmem
  have hsurj : Function.Surjective π := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [hW.2, sa_finrank_H1]
  let eW := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
  let A : H1 F n →ₗ[F] Module.Dual F (H1 F n) :=
    (LinearMap.fst F (Module.Dual F (H1 F n)) (H1 F n)).comp (W.subtype.comp eW.symm.toLinearMap)
  have hsnd : ∀ w, ((eW.symm w : W) : V F n).2 = w := by
    intro w
    have := eW.apply_symm_apply w
    exact this
  have hgraph : ∀ w, ((A w, w) : V F n) = (eW.symm w : W) := by
    intro w
    exact Prod.ext rfl (hsnd w).symm
  refine ⟨A, fun w => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · have h := hW.1 _ (hgraph w ▸ (eW.symm w).2)
    rwa [QuadraticForm.dualProd_apply] at h
  · have h1 : eW.symm (π ⟨v, hv⟩) = ⟨v, hv⟩ := eW.symm_apply_apply ⟨v, hv⟩
    have h2 : π ⟨v, hv⟩ = v.2 := rfl
    show v.1 = ((eW.symm v.2 : W) : V F n).1
    rw [← h2, h1]
  · have : v = ((A v.2, v.2) : V F n) := Prod.ext hv rfl
    rw [this, hgraph]
    exact (eW.symm v.2).2

/-! ### The two kinds of `B`-field elements of `Spin(V_F)` -/

omit [CharZero F] in
theorem sa_inl_isotropic (θ : Module.Dual F (H1 F n)) :
    Q F n (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n) θ) = 0 := by
  simp

omit [CharZero F] in
theorem sa_ell_inr (v : V F n) :
    sa_ell (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) v = v.1 := by
  refine LinearMap.ext fun w => ?_
  rw [sa_ell_apply, sa_polar_apply]
  simp

omit [CharZero F] in
theorem sa_ell_inl (v : V F n) :
    sa_ell (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) v =
      Module.Dual.eval F (H1 F n) v.2 := by
  refine LinearMap.ext fun θ => ?_
  rw [sa_ell_apply, sa_polar_apply]
  simp

omit [CharZero F] in
theorem sa_mul_mem_two {M : Type*} [AddCommGroup M] [Module F M] (a b : M) :
    ExteriorAlgebra.ι F a * ExteriorAlgebra.ι F b ∈ ⋀[F]^2 M := by
  rw [ExteriorAlgebra.exteriorPower, pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ a) (LinearMap.mem_range_self _ b)

omit [CharZero F] in
/-- The contraction of `Σ aᵢ ∧ bᵢ`. -/
theorem sa_contractLeft_sum {M : Type*} [AddCommGroup M] [Module F M] {ι' : Type*}
    (t : Finset ι') (d : Module.Dual F M) (a b : ι' → M) :
    contractLeft (Q := (0 : QuadraticForm F M)) d
        (∑ i ∈ t, ExteriorAlgebra.ι F (a i) * ExteriorAlgebra.ι F (b i)) =
      ExteriorAlgebra.ι F (∑ i ∈ t, (d (a i) • b i - d (b i) • a i)) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (ExteriorAlgebra.ι F (a i) : ExteriorAlgebra F M) = ι (0 : QuadraticForm F M) (a i)
    from rfl, show (ExteriorAlgebra.ι F (b i) : ExteriorAlgebra F M) = ι (0 : QuadraticForm F M) (b i)
    from rfl, contractLeft_ι_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def,
    map_sub, map_smul, map_smul]

omit [CharZero F] in
theorem sa_sum_coord_smul (θ : Module.Dual F (H1 F n)) :
    ∑ i, θ (e F n i) • f F n i = θ := by
  conv_rhs => rw [← (Pi.basisFun F (Fin (2 * n))).sum_dual_apply_smul_coord θ]
  simp only [sa_e_eq, sa_f_eq_coord]

omit [CharZero F] in
theorem sa_sum_smul_e (w : H1 F n) : ∑ i, f F n i w • e F n i = w := by
  conv_rhs => rw [← (Pi.basisFun F (Fin (2 * n))).sum_repr w]
  simp only [sa_e_eq, Pi.basisFun_repr, f, LinearMap.proj_apply]

/-- **Upper `B`-field**: for an alternating `A : H* → H` there is `g ∈ Spin(V_F)` with
`ρ(g)(θ, w) = (θ, w + A θ)` (namely `exp(J B)`, `B = -½ Σ eᵢ ∧ A fᵢ`). -/
theorem sa_bfield_upper (A : Module.Dual F (H1 F n) →ₗ[F] H1 F n)
    (hA : ∀ θ : Module.Dual F (H1 F n), θ (A θ) = 0) :
    ∃ g : Spin F n, ∀ v, rho F n g v = (v.1, v.2 + A v.1) := by
  have hskew : ∀ θ φ : Module.Dual F (H1 F n), θ (A φ) = -φ (A θ) := by
    intro θ φ
    have h := hA (θ + φ)
    simp only [map_add, LinearMap.add_apply, hA θ, hA φ] at h
    linear_combination h
  let B : S F n := (-(1 / 2 : F)) •
    ∑ i, ExteriorAlgebra.ι F (e F n i) * ExteriorAlgebra.ι F (A (f F n i))
  have hB : B ∈ ⋀[F]^2 (H1 F n) :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => sa_mul_mem_two _ _)
  have hc : ∀ v : V F n, ExteriorAlgebra.ι F (-A v.1) =
      contractLeft (Q := (0 : QuadraticForm F (H1 F n)))
        (sa_ell (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) v) B := by
    intro v
    rw [sa_ell_inr, map_smul, sa_contractLeft_sum, ← map_smul]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [hskew v.1 (f F n _), neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add]
    have h1 : ∑ x, v.1 (e F n x) • A (f F n x) = A v.1 := by
      conv_rhs => rw [← sa_sum_coord_smul v.1]
      rw [map_sum]
      simp only [map_smul]
    rw [h1, sa_sum_smul_e]
    module
  refine ⟨⟨_, sa_exp_J_mem_spinGroup _ (sa_inr_isotropic F n) B hB⟩, fun v => ?_⟩
  rw [sa_rho_exp_J _ (sa_inr_isotropic F n) B hB v _ (hc v)]
  ext <;> simp

/-- **Lower `B`-field**: for an alternating `A : H → H*` there is `g ∈ Spin(V_F)` with
`ρ(g)(θ, w) = (θ + A w, w)` (namely `exp(J β)`, `β = -½ Σ fᵢ ∧ A eᵢ ∈ ⋀² H*`). -/
theorem sa_bfield_lower (A : H1 F n →ₗ[F] Module.Dual F (H1 F n)) (hA : ∀ w, A w w = 0) :
    ∃ g : Spin F n, ∀ v, rho F n g v = (v.1 + A v.2, v.2) := by
  have hskew : ∀ w w' : H1 F n, A w w' = -A w' w := by
    intro w w'
    have h := hA (w + w')
    simp only [map_add, LinearMap.add_apply, hA w, hA w'] at h
    linear_combination h
  let β : ExteriorAlgebra F (Module.Dual F (H1 F n)) := (-(1 / 2 : F)) •
    ∑ i, ExteriorAlgebra.ι F (f F n i) * ExteriorAlgebra.ι F (A (e F n i))
  have hβ : β ∈ ⋀[F]^2 (Module.Dual F (H1 F n)) :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => sa_mul_mem_two _ _)
  have hc : ∀ v : V F n, ExteriorAlgebra.ι F (-A v.2) =
      contractLeft (Q := (0 : QuadraticForm F (Module.Dual F (H1 F n))))
        (sa_ell (LinearMap.inl F (Module.Dual F (H1 F n)) (H1 F n)) v) β := by
    intro v
    rw [sa_ell_inl, map_smul, sa_contractLeft_sum, ← map_smul]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [Module.Dual.eval_apply, hskew (e F n _) v.2, neg_smul, Finset.sum_neg_distrib,
      sub_neg_eq_add]
    have h1 : ∑ x, f F n x v.2 • A (e F n x) = A v.2 := by
      conv_rhs => rw [← sa_sum_smul_e v.2]
      rw [map_sum]
      simp only [map_smul]
    rw [h1, sa_sum_coord_smul]
    module
  refine ⟨⟨_, sa_exp_J_mem_spinGroup _ (sa_inl_isotropic (F := F) (n := n)) β hβ⟩, fun v => ?_⟩
  rw [sa_rho_exp_J _ (sa_inl_isotropic (F := F) (n := n)) β hβ v _ (hc v)]
  ext <;> simp

/-! ### Normal form of a maximal isotropic subspace -/

namespace sa_Inter

/-- An even intertwiner is a spin element. -/
theorem mem_spinGroup (a : sa_Inter F n) (h : a.y ∈ evenOdd (Q F n) 0) :
    a.y ∈ spinGroup (Q F n) := by
  refine Submonoid.mem_inf.mpr ⟨a.pin, ?_⟩
  rw [← even_toSubmodule, Subalgebra.mem_toSubmodule] at h
  exact h

/-- The spin element of an even intertwiner. -/
noncomputable def toSpin (a : sa_Inter F n) (h : a.y ∈ evenOdd (Q F n) 0) : Spin F n :=
  ⟨a.y, a.mem_spinGroup h⟩

theorem rho_toSpin (a : sa_Inter F n) (h : a.y ∈ evenOdd (Q F n) 0) (x : V F n) :
    rho F n (a.toSpin h) x = a.σ x :=
  ι_injective (Q F n) (by rw [ι_rho]; exact a.conj x)

theorem m_one_ne_zero (a : sa_Inter F n) : m F n a.y 1 ≠ 0 := by
  intro h
  have := a.m_star_m 1
  rw [h, map_zero] at this
  exact one_ne_zero this.symm

end sa_Inter

omit [CharZero F] in
theorem sa_spin_mem_evenOdd (g : Spin F n) : (g : C F n) ∈ evenOdd (Q F n) 0 := by
  rw [← even_toSubmodule, Subalgebra.mem_toSubmodule]
  exact spinGroup.mem_even g.2

/-- The comap of a maximal isotropic subspace by an intertwiner is maximal isotropic. -/
theorem sa_isMaxIsotropic_comap (a : sa_Inter F n) {W : Submodule F (V F n)}
    (hW : IsMaxIsotropic F n W) : IsMaxIsotropic F n (W.comap (a.σ : V F n →ₗ[F] V F n)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [← a.Q_σ]
    exact hW.1 _ hx
  · rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact hW.2

/-- Reflection step of the normal form: for `(0, b) ∈ W` and `b*(b) = 1`, the reflection in
`v = (-b*, b)` maps `W` to `W'` with `W' ∩ (0 × H) = (W ∩ (0 × H)) ∩ ker b*`. -/
theorem sa_comap_inr_refl (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) {b : H1 F n}
    (hb : ((0, b) : V F n) ∈ W) {bs : Module.Dual F (H1 F n)} (hbs : bs b = 1)
    (hv : Q F n ((-bs, b) : V F n) = -1) :
    (W.map ((sa_Inter.ofVec ((-bs, b) : V F n) hv).σ : V F n →ₗ[F] V F n)).comap
        (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) =
      W.comap (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) ⊓ LinearMap.ker bs := by
  set r := sa_Inter.ofVec ((-bs, b) : V F n) hv
  have hr : ∀ x, r.σ (r.σ x) = x := sa_Inter.reflAux_reflAux hv
  have hr0 : ∀ y : H1 F n, r.σ ((0, y) : V F n) = (-(bs y • bs), bs y • b - y) := by
    intro y
    show sa_Inter.reflAux _ _ = _
    rw [sa_Inter.reflAux_apply, sa_polar_apply]
    ext <;> simp [sub_eq_add_neg, add_comm]
  ext y
  simp only [Submodule.mem_comap, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.inr_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hx' : r.σ ((0, y) : V F n) ∈ W := by rw [← hxy, hr]; exact hx
    rw [hr0] at hx'
    have hpol := sa_polar_of_isotropic hW.1 hb hx'
    rw [sa_polar_apply] at hpol
    simp only [LinearMap.zero_apply, zero_add, LinearMap.neg_apply, LinearMap.smul_apply,
      hbs, smul_eq_mul, mul_one, neg_eq_zero] at hpol
    refine ⟨?_, hpol⟩
    rw [hpol, zero_smul, neg_zero, zero_smul, zero_sub] at hx'
    have := W.neg_mem hx'
    simpa using this
  · rintro ⟨hy, hby⟩
    refine ⟨r.σ ((0, y) : V F n), ?_, hr _⟩
    rw [hr0, hby, zero_smul, neg_zero, zero_smul, zero_sub]
    have := W.neg_mem hy
    simpa using this

/-- **Normal form**: every maximal isotropic subspace is `σ_y(H* × 0)` for an intertwiner `y`
(a product of vectors of norm `-1` and of a `B`-field element), homogeneous of some parity. -/
theorem sa_normal_form (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) :
    ∃ (a : sa_Inter F n) (i : ZMod 2), W = (sa_W0 F n).map (a.σ : V F n →ₗ[F] V F n) ∧
      a.y ∈ evenOdd (Q F n) i := by
  suffices h : ∀ k : ℕ, ∀ W : Submodule F (V F n), IsMaxIsotropic F n W →
      Module.finrank F (W.comap (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n))) = k →
      ∃ (a : sa_Inter F n) (i : ZMod 2), W = (sa_W0 F n).map (a.σ : V F n →ₗ[F] V F n) ∧
        a.y ∈ evenOdd (Q F n) i from h _ W hW rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hW hk
  by_cases h0 : W.comap (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) = ⊥
  · -- `W` is a graph over `H*`: an upper `B`-field.
    have hinf : W ⊓ sa_W0' F n = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨θ, w⟩ ⟨hx, hx'⟩
      rw [SetLike.mem_coe, sa_mem_W0'] at hx'
      simp only at hx'
      subst hx'
      have hw : w ∈ W.comap (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n)) := hx
      rw [h0, Submodule.mem_bot] at hw
      rw [hw]
      exact Submodule.zero_mem _
    obtain ⟨A, hA, hWA⟩ := sa_graph_upper W hW hinf
    obtain ⟨g, hg⟩ := sa_bfield_upper A hA
    refine ⟨sa_Inter.ofSpin g, 0, ?_, sa_spin_mem_evenOdd g⟩
    ext v
    rw [Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨(v.1, 0), (sa_mem_W0 _).mpr rfl, ?_⟩
      show rho F n g (v.1, 0) = v
      rw [hg]
      exact Prod.ext rfl (by simp [(hWA v).mp hv])
    · rintro ⟨x, hx, rfl⟩
      rw [hWA]
      show (rho F n g x).2 = A (rho F n g x).1
      rw [hg]
      simp [(sa_mem_W0 x).mp hx]
  · -- a reflection lowers `dim (W ∩ (0 × H))`.
    obtain ⟨b, hb₀, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hb : ((0, b) : V F n) ∈ W := hb₀
    obtain ⟨bs, hbs⟩ := Module.Projective.exists_dual_eq_one F hb0
    have hv : Q F n ((-bs, b) : V F n) = -1 := by
      rw [QuadraticForm.dualProd_apply, LinearMap.neg_apply, hbs]
    set r := sa_Inter.ofVec ((-bs, b) : V F n) hv
    have hW' := sa_isMaxIsotropic_map r hW
    have hlt : Module.finrank F ((W.map (r.σ : V F n →ₗ[F] V F n)).comap
        (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n))) < k := by
      rw [sa_comap_inr_refl W hW (b := b) hb hbs hv, ← hk]
      apply Submodule.finrank_lt_finrank_of_lt
      refine inf_lt_left.mpr fun hle => ?_
      have := (hle hb₀ : b ∈ LinearMap.ker bs)
      rw [LinearMap.mem_ker, hbs] at this
      exact one_ne_zero this
    obtain ⟨a, i, hWa, ha⟩ := ih _ hlt _ hW' rfl
    refine ⟨r.comp a, 1 + i, ?_, SetLike.mul_mem_graded (sa_Inter.ofVec_mem_odd _ hv) ha⟩
    have hr : ∀ x, r.σ (r.σ x) = x := sa_Inter.reflAux_reflAux hv
    have hWW : (W.map (r.σ : V F n →ₗ[F] V F n)).map (r.σ : V F n →ₗ[F] V F n) = W := by
      rw [← Submodule.map_comp]
      conv_rhs => rw [← Submodule.map_id W]
      congr 1
      exact LinearMap.ext fun x => hr x
    rw [← hWW, hWa, ← Submodule.map_comp]
    rfl

/-- For `W = σ_y(H* × 0)`: `K(W) = F·(y·1)`. -/
theorem sa_kill_map_W0 (a : sa_Inter F n) :
    sa_kill ((sa_W0 F n).map (a.σ : V F n →ₗ[F] V F n)) = Submodule.span F {m F n a.y 1} := by
  rw [sa_kill_map, sa_kill_W0, Submodule.map_span, Set.image_singleton]

/-- For `W = σ_y(0 × H)`: `K(W) = F·(y·[pt])`. -/
theorem sa_kill_map_W0' (a : sa_Inter F n) :
    sa_kill ((sa_W0' F n).map (a.σ : V F n →ₗ[F] V F n)) =
      Submodule.span F {m F n a.y (pt F n)} := by
  rw [sa_kill_map, sa_kill_W0', Submodule.map_span, Set.image_singleton]

theorem sa_ann_m_one (a : sa_Inter F n) :
    ann F n (m F n a.y 1) = (sa_W0 F n).map (a.σ : V F n →ₗ[F] V F n) := by
  rw [sa_ann_m, sa_ann_one]

/-- **[III.1.4] existence**, homogeneous form: a maximal isotropic `W` is `ker m_w` for a nonzero
`w ∈ S⁺ ∪ S⁻`, and `K(W) = F w`. -/
theorem sa_exists_pure (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) :
    ∃ w : S F n, w ≠ 0 ∧ (w ∈ Splus F n ∨ w ∈ Sminus F n) ∧ ann F n w = W ∧
      sa_kill W = Submodule.span F {w} := by
  obtain ⟨a, i, hWa, ha⟩ := sa_normal_form W hW
  refine ⟨m F n a.y 1, a.m_one_ne_zero, ?_, by rw [sa_ann_m_one, hWa], by rw [hWa, sa_kill_map_W0]⟩
  have hpar := sa_m_mem_evenOdd ha sa_one_mem_Splus
  rw [add_zero] at hpar
  have hi : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases hi i with rfl | rfl
  · exact Or.inl hpar
  · exact Or.inr hpar

/-- **[III.1.4] uniqueness**: if `ker m_w` is maximal isotropic, `w ≠ 0`, and
`ker m_{w'} = ker m_w`, then `w' ∈ F w`. -/
theorem sa_unique (w w' : S F n) (hw : w ≠ 0) (hmax : IsMaxIsotropic F n (ann F n w))
    (h : ann F n w' = ann F n w) : w' ∈ Submodule.span F {w} := by
  obtain ⟨s, -, -, -, hK⟩ := sa_exists_pure _ hmax
  have hws : w ∈ sa_kill (ann F n w) := (sa_mem_kill_iff _ _).mpr le_rfl
  have hw's : w' ∈ sa_kill (ann F n w) := (sa_mem_kill_iff _ _).mpr h.symm.le
  rw [hK, Submodule.mem_span_singleton] at hws hw's
  obtain ⟨c, rfl⟩ := hws
  obtain ⟨c', rfl⟩ := hw's
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw (zero_smul F s)
  rw [Submodule.mem_span_singleton]
  exact ⟨c' / c, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩

omit [CharZero F] in
theorem sa_Splus_inf_Sminus : Splus F n ⊓ Sminus F n = ⊥ :=
  (evenOdd_isCompl (0 : QuadraticForm F (H1 F n))).disjoint.eq_bot

/-- A nonzero even spinor killed by `W = σ_y(H* × 0)` forces `y` to be even, and is a multiple
of `y·1`. -/
theorem sa_normal_form_even (W : Submodule F (V F n)) (hW : IsMaxIsotropic F n W) (u : S F n)
    (hu : u ∈ Splus F n) (hu0 : u ≠ 0) (huW : W ≤ ann F n u) :
    ∃ (a : sa_Inter F n) (c : F), W = (sa_W0 F n).map (a.σ : V F n →ₗ[F] V F n) ∧
      a.y ∈ evenOdd (Q F n) 0 ∧ c ≠ 0 ∧ u = c • m F n a.y 1 := by
  obtain ⟨a, i, hWa, ha⟩ := sa_normal_form W hW
  have huK : u ∈ sa_kill W := (sa_mem_kill_iff _ _).mpr huW
  rw [hWa, sa_kill_map_W0, Submodule.mem_span_singleton] at huK
  obtain ⟨c, hc⟩ := huK
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hu0 hc.symm
  refine ⟨a, c, hWa, ?_, hc0, hc.symm⟩
  have hpar := sa_m_mem_evenOdd ha sa_one_mem_Splus
  rw [add_zero] at hpar
  have hi : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases hi i with rfl | rfl
  · exact ha
  · exfalso
    have hmem : m F n a.y 1 ∈ Splus F n ⊓ Sminus F n := by
      refine ⟨?_, hpar⟩
      have := Submodule.smul_mem (Splus F n) c⁻¹ hu
      rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    rw [sa_Splus_inf_Sminus, Submodule.mem_bot] at hmem
    exact a.m_one_ne_zero hmem

/-! ### Pairs of complementary maximal isotropic subspaces -/

/-- **Pairs**: if `W₁, W₂` are complementary maximal isotropic subspaces and `W₁` is killed by a
nonzero even spinor, then some `g ∈ Spin(V_F)` maps `(H* × 0, 0 × H)` to `(W₁, W₂)`. -/
theorem sa_pair (W₁ W₂ : Submodule F (V F n)) (h₁ : IsMaxIsotropic F n W₁)
    (h₂ : IsMaxIsotropic F n W₂) (h12 : W₁ ⊓ W₂ = ⊥) (u : S F n) (hu : u ∈ Splus F n)
    (hu0 : u ≠ 0) (huW : W₁ ≤ ann F n u) :
    ∃ g : Spin F n, (sa_W0 F n).map (rho F n g : V F n →ₗ[F] V F n) = W₁ ∧
      (sa_W0' F n).map (rho F n g : V F n →ₗ[F] V F n) = W₂ := by
  obtain ⟨a, c, hWa, ha, -, -⟩ := sa_normal_form_even W₁ h₁ u hu hu0 huW
  set g₁ := a.toSpin ha
  have hρ₁ : (rho F n g₁ : V F n →ₗ[F] V F n) = (a.σ : V F n →ₗ[F] V F n) :=
    LinearMap.ext fun x => a.rho_toSpin ha x
  set W₂' := W₂.comap (a.σ : V F n →ₗ[F] V F n)
  have hW₂' : IsMaxIsotropic F n W₂' := sa_isMaxIsotropic_comap a h₂
  have hinf : W₂' ⊓ sa_W0 F n = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx2, hx0⟩
    have h1 : a.σ x ∈ W₁ := by
      rw [hWa]
      exact ⟨x, hx0, rfl⟩
    have hmem : a.σ x ∈ W₁ ⊓ W₂ := ⟨h1, hx2⟩
    rw [h12, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact a.σ.map_eq_zero_iff.mp hmem
  obtain ⟨A, hA, hWA⟩ := sa_graph_lower W₂' hW₂' hinf
  obtain ⟨g₂, hg₂⟩ := sa_bfield_lower A hA
  refine ⟨g₁ * g₂, ?_, ?_⟩
  · have hmap : (sa_W0 F n).map (rho F n g₂ : V F n →ₗ[F] V F n) = sa_W0 F n := by
      ext v
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [sa_mem_W0] at hx ⊢
        show (rho F n g₂ x).2 = 0
        rw [hg₂]
        exact hx
      · intro hv
        refine ⟨v, hv, ?_⟩
        show rho F n g₂ v = v
        rw [hg₂]
        exact Prod.ext (by rw [(sa_mem_W0 v).mp hv, map_zero, add_zero]) rfl
    rw [show (rho F n (g₁ * g₂) : V F n →ₗ[F] V F n) =
        (rho F n g₁ : V F n →ₗ[F] V F n).comp (rho F n g₂ : V F n →ₗ[F] V F n) from
      LinearMap.ext fun x => by simp [rho], Submodule.map_comp, hmap, hρ₁, hWa]
  · have hmap : (sa_W0' F n).map (rho F n g₂ : V F n →ₗ[F] V F n) = W₂' := by
      ext v
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [sa_mem_W0'] at hx
        rw [hWA]
        show (rho F n g₂ x).1 = A (rho F n g₂ x).2
        rw [hg₂]
        simp [hx]
      · intro hv
        refine ⟨(0, v.2), (sa_mem_W0' _).mpr rfl, ?_⟩
        show rho F n g₂ (0, v.2) = v
        rw [hg₂]
        exact Prod.ext (by simp [(hWA v).mp hv]) rfl
    rw [show (rho F n (g₁ * g₂) : V F n →ₗ[F] V F n) =
        (rho F n g₁ : V F n →ₗ[F] V F n).comp (rho F n g₂ : V F n →ₗ[F] V F n) from
      LinearMap.ext fun x => by simp [rho], Submodule.map_comp, hmap, hρ₁]
    exact Submodule.map_comap_eq_of_surjective a.σ.surjective W₂

/-! ### The left ideal `C(V)·[pt_X̂]` and Chevalley's `φ` -/

omit [CharZero F] in
theorem sa_iotaXHat_eq :
    iotaXHat F n = sa_J (LinearMap.inl F _ _) (sa_inl_isotropic (F := F) (n := n)) := rfl

omit [CharZero F] in
theorem sa_iotaX_ι (w : H1 F n) :
    iotaX F n (ExteriorAlgebra.ι F w) = ι (Q F n) ((0, w) : V F n) := by
  rw [sa_iotaX_eq, sa_J_ι]
  rfl

omit [CharZero F] in
theorem sa_iotaXHat_ι (θ : Module.Dual F (H1 F n)) :
    iotaXHat F n (ExteriorAlgebra.ι F θ) = ι (Q F n) ((θ, 0) : V F n) := by
  rw [sa_iotaXHat_eq, sa_J_ι]
  rfl

omit [CharZero F] in
theorem sa_dualBasis_eq (i : Fin (2 * n)) :
    (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
  ext x
  simp [f]

omit [CharZero F] in
theorem sa_ptHat_eq : ptHat F n = ExteriorAlgebra.ιMulti F (2 * n) (fun i => f F n i) := by
  have hcard : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by simp
  rw [ptHat, basisSHat, ExteriorAlgebra.basis_apply_ofCard _ hcard, ExteriorAlgebra.ιMulti_family]
  congr 1
  funext i
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rw [← sa_dualBasis_eq]
  congr 1
  have h := Finset.orderEmbOfFin_unique
    (s := ((Set.powersetCard.ofCard hcard : Set.powersetCard (Fin (2 * n)) (2 * n)) :
      Finset (Fin (2 * n))))
    (Set.powersetCard.ofCard hcard).prop (f := id) (fun x => Finset.mem_univ x) strictMono_id
  exact (congrFun h i).symm

omit [CharZero F] in
/-- `[pt_X̂] = f₁ ⋯ f_{2n}` in `C(V)`. -/
theorem sa_ptHatC_eq :
    ptHatC F n = ((List.ofFn fun i : Fin (2 * n) => ((f F n i, 0) : V F n)).map
      (ι (Q F n))).prod := by
  rw [ptHatC, sa_ptHat_eq, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn,
    List.map_ofFn]
  simp only [Function.comp_def, sa_iotaXHat_ι]

omit [CharZero F] in
theorem sa_ι_mul_ptHat (θ : Module.Dual F (H1 F n)) : ExteriorAlgebra.ι F θ * ptHat F n = 0 := by
  rw [← sa_sum_coord_smul θ, map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_mul_assoc, ptHat, basisSHat, ← sa_dualBasis_eq,
    TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_left (Finset.mem_univ i), smul_zero]

omit [CharZero F] in
theorem sa_ι_mul_ptHatC (θ : Module.Dual F (H1 F n)) :
    ι (Q F n) ((θ, 0) : V F n) * ptHatC F n = 0 := by
  rw [← sa_iotaXHat_ι, ptHatC, ← map_mul, sa_ι_mul_ptHat, map_zero]

/-- `v · s[pt_X̂] = (m_v s)[pt_X̂]`. -/
theorem sa_ι_mul_iotaX_mul_ptHatC (x : V F n) (s : S F n) :
    ι (Q F n) x * iotaX F n s * ptHatC F n = iotaX F n (m F n (ι (Q F n) x) s) * ptHatC F n := by
  obtain ⟨θ, w⟩ := x
  have hx : ((θ, w) : V F n) = (θ, 0) + (0, w) := by simp
  have h1 : ι (Q F n) ((θ, 0) : V F n) * iotaX F n s * ptHatC F n =
      iotaX F n (D F n θ s) * ptHatC F n := by
    have h := sa_ι_mul_J (LinearMap.inr F (Module.Dual F (H1 F n)) (H1 F n))
      (sa_inr_isotropic F n) ((θ, 0) : V F n) s
    rw [← sa_iotaX_eq, sa_ell_inr] at h
    rw [h, add_mul, mul_assoc, sa_ι_mul_ptHatC, mul_zero, add_zero]
    rfl
  have h2 : ι (Q F n) ((0, w) : V F n) * iotaX F n s = iotaX F n (ExteriorAlgebra.ι F w * s) := by
    rw [map_mul, sa_iotaX_ι]
  conv_lhs => rw [hx, map_add, add_mul, add_mul]
  rw [h1, h2, sa_m_ι_apply, map_add, add_mul, add_comm]

/-- `y · s[pt_X̂] = (m_y s)[pt_X̂]` for every `y ∈ C(V)`: the left ideal `C(V)·[pt_X̂]` is the spin
representation. -/
theorem sa_mul_iotaX_mul_ptHatC (y : C F n) (s : S F n) :
    y * iotaX F n s * ptHatC F n = iotaX F n (m F n y s) * ptHatC F n := by
  induction y using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    rw [AlgHom.commutes, Module.algebraMap_end_apply, map_smul, ← Algebra.smul_def,
      smul_mul_assoc]
  | ι x => exact sa_ι_mul_iotaX_mul_ptHatC x s
  | mul a b ha hb =>
    rw [mul_assoc a b, mul_assoc a, hb, ← mul_assoc, ha, map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    rw [add_mul, add_mul, ha, hb, map_add, LinearMap.add_apply, map_add, add_mul]

omit [CharZero F] in
theorem sa_reverse_iotaX (s : S F n) : reverse (iotaX F n s) = iotaX F n (tau F n s) := by
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, reverse.commutes, tau, reverse.commutes, AlgHom.commutes]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | ι_mul s w hs =>
    rw [map_mul, reverse.map_mul, hs, tau, reverse.map_mul, reverse_ι, map_mul]
    rw [show iotaX F n (ι (0 : QuadraticForm F (H1 F n)) w) = ι (Q F n) ((0, w) : V F n) from
      sa_iotaX_ι w, reverse_ι]

omit [CharZero F] in
theorem sa_reverse_ptHatC :
    reverse (ptHatC F n) = ((-1 : F) ^ (List.ofFn fun i : Fin (2 * n) =>
      ((f F n i, 0) : V F n)).length.choose 2) • ptHatC F n := by
  rw [sa_ptHatC_eq, reverse_prod_map_ι_of_pairwise_isOrtho]
  rw [List.pairwise_ofFn]
  intro i j _
  show Q F n _ = Q F n _ + Q F n _
  simp [QuadraticForm.dualProd_apply]

/-- The right-hand version: `[pt_X̂]τ(t) · y = [pt_X̂]τ(m_{τ(y)} t)`. -/
theorem sa_ptHatC_mul_iotaX_mul (t : S F n) (y : C F n) :
    ptHatC F n * iotaX F n (tau F n t) * y =
      ptHatC F n * iotaX F n (tau F n (m F n (reverse y) t)) := by
  have h := congrArg reverse (sa_mul_iotaX_mul_ptHatC (reverse y) t)
  rw [reverse.map_mul, reverse.map_mul, reverse_reverse, sa_reverse_iotaX, reverse.map_mul,
    sa_reverse_iotaX, sa_reverse_ptHatC] at h
  have hε : ((-1 : F) ^ (List.ofFn fun i : Fin (2 * n) =>
      ((f F n i, 0) : V F n)).length.choose 2) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [smul_mul_assoc, smul_mul_assoc] at h
  rw [mul_assoc]
  exact smul_right_injective _ hε h

omit [CharZero F] in
theorem sa_varphi_tmul (s t : S F n) :
    varphi F n (s ⊗ₜ t) = iotaX F n s * ptHatC F n * iotaX F n (tau F n t) := by
  simp [varphi]

/-- **`φ` is `Spin`-equivariant**: `φ(g s ⊗ g t) = g φ(s ⊗ t) g*`. -/
theorem sa_varphi_equivariant (g : Spin F n) (s t : S F n) :
    varphi F n (m F n (g : C F n) s ⊗ₜ m F n (g : C F n) t) =
      (g : C F n) * varphi F n (s ⊗ₜ t) * star (g : C F n) := by
  rw [sa_varphi_tmul, sa_varphi_tmul]
  have hrev : reverse (star (g : C F n)) = g := by
    rw [star_def, reverse_reverse, involute_eq_of_mem_even (sa_spin_mem_evenOdd g)]
  calc iotaX F n (m F n g s) * ptHatC F n * iotaX F n (tau F n (m F n g t))
      = iotaX F n (m F n g s) * (ptHatC F n *
          iotaX F n (tau F n (m F n (reverse (star (g : C F n))) t))) := by
        rw [hrev, mul_assoc]
    _ = iotaX F n (m F n g s) * (ptHatC F n * iotaX F n (tau F n t) * star (g : C F n)) := by
        rw [sa_ptHatC_mul_iotaX_mul]
    _ = ((g : C F n) * iotaX F n s * ptHatC F n) * iotaX F n (tau F n t) * star (g : C F n) := by
        rw [sa_mul_iotaX_mul_ptHatC]
        simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-! ### `[pt_X̂] ≠ 0` -/

omit [CharZero F] in
theorem sa_D_f_prod_e (a : Fin (2 * n)) (L : List (Fin (2 * n))) (ha : a ∉ L) :
    D F n (f F n a) ((L.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) = 0 := by
  induction L with
  | nil => exact contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) _
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons]
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    have h1 : D F n (f F n a) (ExteriorAlgebra.ι F (e F n b) *
        (L.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) =
        f F n a (e F n b) • (L.map fun i => ExteriorAlgebra.ι F (e F n i)).prod -
          ExteriorAlgebra.ι F (e F n b) *
            D F n (f F n a) ((L.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) :=
      contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) _ _ _
    rw [h1, ih (fun h => ha (List.mem_cons_of_mem _ h)), mul_zero, sub_zero]
    simp [f, e, hab]

omit [CharZero F] in
theorem sa_D_prod (L : List (Fin (2 * n))) (hL : L.Nodup) :
    ((L.map fun i => D F n (f F n i)).prod)
      ((L.reverse.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) = 1 := by
  induction L using List.reverseRec with
  | nil => simp
  | append_singleton L a ih =>
    have hL' : L.Nodup := hL.sublist (List.sublist_append_left L [a])
    have ha : a ∉ L := by
      intro h
      rw [List.nodup_append] at hL
      exact hL.2.2 a h a (List.mem_singleton_self a) rfl
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
      List.prod_cons, Module.End.mul_apply]
    have h1 : D F n (f F n a) (ExteriorAlgebra.ι F (e F n a) *
        (L.reverse.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) =
        f F n a (e F n a) • (L.reverse.map fun i => ExteriorAlgebra.ι F (e F n i)).prod -
          ExteriorAlgebra.ι F (e F n a) *
            D F n (f F n a) ((L.reverse.map fun i => ExteriorAlgebra.ι F (e F n i)).prod) :=
      contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) _ _ _
    rw [h1, sa_D_f_prod_e a L.reverse (by simpa using ha), mul_zero, sub_zero,
      show f F n a (e F n a) = 1 by simp [f, e], one_smul, ih hL']

theorem sa_m_ι_inl (θ : Module.Dual F (H1 F n)) : m F n (ι (Q F n) ((θ, 0) : V F n)) = D F n θ :=
  LinearMap.ext fun s => by rw [sa_m_ι_apply, map_zero, zero_mul, zero_add]

/-- `[pt_X̂] ≠ 0` in `C(V)`: `m([pt_X̂])` maps `e_{2n} ∧ ⋯ ∧ e₁` to `1`. -/
theorem sa_ptHatC_ne_zero : ptHatC F n ≠ 0 := by
  intro h
  have hm : m F n (ptHatC F n) = ((List.finRange (2 * n)).map fun i => D F n (f F n i)).prod := by
    rw [sa_ptHatC_eq, map_list_prod, List.map_map, List.ofFn_eq_map, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    exact sa_m_ι_inl (f F n i)
  have := sa_D_prod (F := F) (List.finRange (2 * n)) (List.nodup_finRange _)
  rw [← hm, h, map_zero, LinearMap.zero_apply] at this
  exact zero_ne_one this

/-! ### Top products of an isotropic subspace -/

/-- The alternating map `(w₁, …, w_k) ↦ w₁ ⋯ w_k ∈ C(V)` of an isotropic subspace `W`. -/
noncomputable def sa_topMap (W : Submodule F (V F n)) (hW : ∀ v ∈ W, Q F n v = 0) (k : ℕ) :
    W [⋀^Fin k]→ₗ[F] C F n :=
  (sa_J W.subtype (fun x => hW x x.2)).toLinearMap.compAlternatingMap (ExteriorAlgebra.ιMulti F k)

omit [CharZero F] in
theorem sa_topMap_apply (W : Submodule F (V F n)) (hW : ∀ v ∈ W, Q F n v = 0) (k : ℕ)
    (x : Fin k → W) :
    sa_topMap W hW k x = ((List.ofFn fun i => (x i : V F n)).map (ι (Q F n))).prod := by
  rw [sa_topMap, LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, List.map_ofFn]
  exact congrArg (fun g : Fin k → C F n => (List.ofFn g).prod)
    (funext fun i => sa_J_ι W.subtype (fun x => hW x x.2) (x i))

omit [CharZero F] in
/-- Every top product of `W` is a multiple of the top product of a basis: the alternating map
`(w₁, …, w_k) ↦ w₁ ⋯ w_k` is `b.det · (b₁ ⋯ b_k)` for `k = dim W`. -/
theorem sa_topMap_eq_det_smul (W : Submodule F (V F n)) (hW : ∀ v ∈ W, Q F n v = 0) {k : ℕ}
    (hk : Module.finrank F W = k) (y : Fin k → W) :
    sa_topMap W hW k y = (Module.finBasisOfFinrankEq F W hk).det y •
      sa_topMap W hW k (Module.finBasisOfFinrankEq F W hk) := by
  set b := Module.finBasisOfFinrankEq F W hk
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff F]
  intro φ
  have h := AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (sa_topMap W hW k))
  have h' := congrArg (fun A => A y) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h'
  rw [map_sub, map_smul, h', smul_eq_mul, mul_comm, sub_self]

omit [CharZero F] in
/-- Top products transform by the determinant: `T w₁ ⋯ T w_k = det(T) w₁ ⋯ w_k` for
`k = dim W`. -/
theorem sa_topMap_comp (W : Submodule F (V F n)) (hW : ∀ v ∈ W, Q F n v = 0) {k : ℕ}
    (hk : Module.finrank F W = k) (T : W →ₗ[F] W) (x : Fin k → W) :
    sa_topMap W hW k (T ∘ x) = LinearMap.det T • sa_topMap W hW k x := by
  rw [sa_topMap_eq_det_smul W hW hk, sa_topMap_eq_det_smul W hW hk x, Module.Basis.det_comp,
    mul_smul]

/-! ### `φ(u ⊗ u)` for an even pure spinor -/

omit [CharZero F] in
theorem sa_varphi_one : varphi F n (1 ⊗ₜ 1) = ptHatC F n := by
  rw [sa_varphi_tmul, map_one, tau, reverse.map_one, map_one, one_mul, mul_one]

/-- For a nonzero even pure spinor `u`, `φ(u ⊗ u)` is a nonzero top product of `ker m_u`. -/
theorem sa_varphi_self (u : S F n) (hu : IsEvenPureSpinor F n u) (hu0 : u ≠ 0) :
    ∃ (c : F) (z : Fin (2 * n) → ann F n u),
      varphi F n (u ⊗ₜ u) = c • sa_topMap (ann F n u) hu.2.1 (2 * n) z ∧
        varphi F n (u ⊗ₜ u) ≠ 0 := by
  obtain ⟨a, c, hWa, ha, hc0, huc⟩ := sa_normal_form_even (ann F n u) hu.2 u hu.1 hu0 le_rfl
  set g := a.toSpin ha
  have hφ : varphi F n (u ⊗ₜ u) = (c * c) • ((g : C F n) * ptHatC F n * star (g : C F n)) := by
    rw [huc, TensorProduct.smul_tmul_smul, map_smul, ← sa_varphi_one]
    congr 1
    exact sa_varphi_equivariant g 1 1
  have hz : ∀ i, a.σ ((f F n i, 0) : V F n) ∈ ann F n u := by
    intro i
    rw [hWa]
    exact ⟨_, (sa_mem_W0 _).mpr rfl, rfl⟩
  refine ⟨c * c, fun i => ⟨a.σ (f F n i, 0), hz i⟩, ?_, ?_⟩
  · rw [hφ, sa_topMap_apply]
    congr 1
    rw [sa_ptHatC_eq]
    refine (a.conj_prod _).trans ?_
    rw [List.map_ofFn, List.map_ofFn]
    rfl
  · rw [hφ]
    refine smul_ne_zero (mul_ne_zero hc0 hc0) fun h => sa_ptHatC_ne_zero (F := F) (n := n) ?_
    have h' : star (g : C F n) * ((g : C F n) * ptHatC F n * star (g : C F n)) * (g : C F n) =
        ptHatC F n := by
      rw [← mul_assoc, ← mul_assoc, spinGroup.star_mul_self_of_mem g.2, one_mul, mul_assoc,
        spinGroup.star_mul_self_of_mem g.2, mul_one]
    rw [← h', h, mul_zero, zero_mul]

end Core

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **[Chevalley, *The algebraic theory of spinors*, III.3.2 and III.4.5]**, in the form used in
the proof of Lemma 3.1.1: for an even pure spinor `u ∈ S⁺_F` with maximal isotropic
`W = ker m_u`, and `g ∈ Spin(V_F)` with `ρ(g)(W) ⊆ W`, we have `m(g) u = c u` for a scalar `c` with
`c² = det(ρ(g)|_W)`. -/
theorem chevalley_III_3_2_III_4_5 (u : S F n) (hu : IsEvenPureSpinor F n u) (g : Spin F n)
    (hg : ∀ v ∈ ann F n u, rho F n g v ∈ ann F n u) :
    ∃ c : F, m F n (g : C F n) u = c • u ∧
      c ^ 2 = LinearMap.det ((rho F n g : V F n →ₗ[F] V F n).restrict hg) := by
  by_cases hu0 : u = 0
  · refine ⟨1, by rw [hu0, map_zero, smul_zero], ?_⟩
    have hann : ann F n u = ⊤ := by
      rw [hu0, eq_top_iff]
      intro v _
      rw [sa_mem_ann, map_zero]
    have hfin : Module.finrank F (ann F n u) = 0 := by
      have h1 := hu.2.2
      have h2 : Module.finrank F (V F n) = 2 * n + 2 * n := by
        rw [Module.finrank_prod, Subspace.dual_finrank_eq, sa_finrank_H1]
      rw [hann, finrank_top] at h1
      rw [hann, finrank_top]
      omega
    rw [one_pow, LinearMap.det_eq_one_of_finrank_eq_zero hfin]
  · obtain ⟨c₀, z, hφ, hφ0⟩ := sa_varphi_self u hu hu0
    have hann : ann F n (m F n (g : C F n) u) = ann F n u := by
      have h := sa_ann_m (sa_Inter.ofSpin g) u
      refine h.trans (Submodule.eq_of_le_of_finrank_eq ?_ ?_)
      · rintro _ ⟨x, hx, rfl⟩
        exact hg x hx
      · exact LinearEquiv.finrank_map_eq _ _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sa_unique u _ hu0 hu.2 hann)
    refine ⟨c, hc.symm, ?_⟩
    set T := (rho F n g : V F n →ₗ[F] V F n).restrict hg
    have h1 : varphi F n (m F n (g : C F n) u ⊗ₜ m F n (g : C F n) u) =
        (c ^ 2) • varphi F n (u ⊗ₜ u) := by
      rw [← hc, TensorProduct.smul_tmul_smul, map_smul, sq]
    have h3 : (g : C F n) * sa_topMap (ann F n u) hu.2.1 (2 * n) z * star (g : C F n) =
        sa_topMap (ann F n u) hu.2.1 (2 * n) (T ∘ z) := by
      rw [sa_topMap_apply, sa_topMap_apply]
      refine ((sa_Inter.ofSpin g).conj_prod _).trans ?_
      rw [List.map_ofFn, List.map_ofFn]
      rfl
    have h2 := sa_varphi_equivariant g u u
    rw [hφ, mul_smul_comm, smul_mul_assoc, h3, sa_topMap_comp _ _ hu.2.2 T z, smul_comm,
      ← hφ, h1] at h2
    exact smul_left_injective F hφ0 h2


end WeilClasses
