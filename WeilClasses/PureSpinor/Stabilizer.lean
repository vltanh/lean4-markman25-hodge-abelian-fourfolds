module

public import WeilClasses.PureSpinor.Lemma2_2_1
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import WeilClasses.External.Igusa.Sec2_2
import WeilClasses.External.Chevalley.Sec2_2
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# Stabilizers of `K`-secants: `Spin(V_K)_{ℓ₁,ℓ₂}`, `Spin(V_K)_P`, Lemma 2.2.2 and Remark 2.2.3

Paper §2.2, from "Assume that `W₁ ∩ W₂` is the zero subspace" to Remark 2.2.3. Throughout, the
standing hypothesis of the paper `W₁ ∩ W₂ = 0` is an explicit hypothesis `hW`, and `0 < d` is the
paper's "`K` purely imaginary".

## Main definitions

* `WeilClasses.KSecant.restrictW₁`: `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}` (the map
  `WeilClasses.pairRestrict` of [Igusa, Lemma 1], defined in `WeilClasses.PureSpinor.Defs`), and
  `KSecant.restrictW₁P`, its restriction to `Spin(V_K)_P`.
* `WeilClasses.KSecant.pairingW₂`: the identification `W₂ → W₁*` given by the pairing of `V_K`.

## Statements

* The claims attributed to [Igusa, Lemma 1] (`KSecant.restrictW₁_eq_one_iff`,
  `KSecant.range_restrictW₁` (corrected, see below),
  `KSecant.rho_eq_one_iff`, `KSecant.pairingW₂_bijective`, `KSecant.pairingW₂_rho`),
  `KSecant.det₂_eq_inv` (`det₂ = det₁⁻¹`), `KSecant.χ₁_sq`, `KSecant.χ₂_sq` (`ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`).
* **Lemma 2.2.2** with the misprint `SL_n(K)` corrected to `SL_{2n}(K)` (`lemma2_2_2`,
  `lemma2_2_2_restrict`).
* **Remark 2.2.3** ([Igusa, Lemma 2] and the remark after it): `remark2_2_3_not_pure`,
  `remark2_2_3_odd`, `remark2_2_3_even`, `remark2_2_3_determines`, `remark2_2_3_unique_secant`.

## A false claim of the paper

The paper says "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`". At the
level of `K`-points this contradicts the paper's own `ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁` (`χ₁² = det₁`): `det₁` only
takes square values, so the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)` is the subgroup of
endomorphisms with square determinant. For instance, if `x ∈ W₂`, `y ∈ W₁`, `(x, y)_V = 1`, the
element of `SO(V_K)` acting by `a ∉ K^{×2}` on `y`, by `a⁻¹` on `x` and trivially on the
orthogonal of `x, y` is not in `ρ(Spin(V_K))`: its two lifts `±(√a⁻¹ x y + √a y x)` to
`Spin(V_{K̄})` are not `K`-rational. The isomorphism holds for the algebraic groups (over `K̄`). We
state the corrected claim (`KSecant.range_restrictW₁`), as agreed with the project owner.
Lemma 2.2.2 is unaffected.

## Proofs

The paper cites [Igusa, Lemma 1] for the claims after Lemma 2.2.1 (used in the proof of
Lemma 2.2.2) and [Igusa, Lemma 2] for Remark 2.2.3. The proofs cite the statements of record at these
places: `igusa_lemma1_ker`, `igusa_lemma1_range`, `igusa_lemma1_dual`, `igusa_lemma1_sq`,
`igusa_lemma2_stab_odd` and `igusa_lemma2_stab_even` (`WeilClasses.External.Igusa.Sec2_2`, stated for
any field of characteristic zero; here `F = K`). "`w` is not a pure spinor, as commented above"
cites [Chevalley, III.1.12] (`chevalley_III_1_12`). The helpers of the section `S22aFix` (the
infinitesimal stabilizer of `w`, with [Chevalley, III.1.4] cited as `chevalley_III_1_4_unique`)
serve only the documented departure in `remark2_2_3_determines` and `remark2_2_3_unique_secant`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prover P03, prefix `s22a_`): the kernel of `ρ` -/

section S22aKernel

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem s22a_Q_nondegenerate : (Q F n).Nondegenerate :=
  TauCeti.nondegenerate_dualProd (Module.eval_apply_injective F)

omit [CharZero F] in
theorem s22a_nontrivial_V (hn : 0 < n) : Nontrivial (V F n) :=
  ⟨⟨(0, 0), (0, e F n ⟨0, by omega⟩), by
    intro h
    have := congrFun (congrArg Prod.snd h) ⟨0, by omega⟩
    simp [e] at this⟩⟩

/-- The kernel of `ρ : Spin(V_F) → SO(V_F)` is `{±1}` (Tau Ceti). -/
theorem s22a_rho_eq_one_iff (hn : 0 < n) (g : Spin F n) :
    rho F n g = 1 ↔ (g : C F n) = 1 ∨ (g : C F n) = -1 := by
  have := s22a_nontrivial_V (F := F) hn
  have hker : rho F n g = 1 ↔ g ∈ MonoidHom.ker (spinToOrthogonal (Q F n)) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rw [coe_spinToOrthogonal_apply]
      exact LinearEquiv.congr_fun h v
    · intro h
      apply LinearEquiv.ext
      intro v
      have := congrArg
        (fun x : TauCeti.QuadraticMap.orthogonalGroup (Q F n) => (x : V F n ≃ₗ[F] V F n) v) h
      show spinVectorAction (Q F n) g v = v
      simpa using this
  rw [hker, mem_ker_spinToOrthogonal_iff (Q F n) s22a_Q_nondegenerate g]
  constructor
  · rintro (rfl | rfl)
    · left; rfl
    · right; exact spinGroup.coe_negOne _ _
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; apply Subtype.ext; rw [h, spinGroup.coe_negOne]

end S22aKernel

/-! ## Helpers (prover P03): the infinitesimal stabilizer of `a u₁ + b u₂`

Used only for the departure in `remark2_2_3_determines` and `remark2_2_3_unique_secant` ("`w`
determines `P`"). Let `Λ = span {ι p ι q} ⊆ C(V)` (scalars and `so(V)`). For a transversal pair of
even pure spinors and `w = a u₁ + b u₂`, `a, b ≠ 0`, `n ≥ 3`, the joint kernel of
`{ξ ∈ Λ : m_ξ w = 0}` is `F u₁ + F u₂` (`s22a_fix_iff`). (With the number operator `N`: `m_ξ uᵢ`
decomposes into `N`-eigenvectors of eigenvalues `2n, 2n - 2` (for `u₁`) and `0, 2` (for `u₂`),
distinct for `n ≥ 3`.) -/

section S22aFix

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- `Λ = span {ι p ι q} ⊆ C(V_F)`. -/
noncomputable def s22a_Λ (F : Type*) [Field F] [CharZero F] (n : ℕ) : Submodule F (C F n) :=
  Submodule.span F (Set.range fun pq : V F n × V F n => ι (Q F n) pq.1 * ι (Q F n) pq.2)

theorem s22a_ι_mul_ι_mem_Λ (p q : V F n) : ι (Q F n) p * ι (Q F n) q ∈ s22a_Λ F n :=
  Submodule.subset_span ⟨(p, q), rfl⟩

omit [CharZero F] in
/-- Separation of eigenvectors for four distinct eigenvalues. -/
theorem s22a_eigen_first {M : Type*} [AddCommGroup M] [Module F M] (N : M →ₗ[F] M)
    {z₁ z₂ z₃ z₄ : M} {l₁ l₂ l₃ l₄ : F} (h₁ : N z₁ = l₁ • z₁) (h₂ : N z₂ = l₂ • z₂)
    (h₃ : N z₃ = l₃ • z₃) (h₄ : N z₄ = l₄ • z₄) (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃) (h14 : l₁ ≠ l₄)
    (hs : z₁ + z₂ + z₃ + z₄ = 0) : z₁ = 0 := by
  -- apply `(N - l₄)`, then `(N - l₃)`, then `(N - l₂)`
  have e1 : (l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃ = 0 := by
    have := congrArg N hs
    rw [map_add, map_add, map_add, h₁, h₂, h₃, h₄, map_zero] at this
    calc (l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃
        = (l₁ • z₁ + l₂ • z₂ + l₃ • z₃ + l₄ • z₄) - l₄ • (z₁ + z₂ + z₃ + z₄) := by module
      _ = 0 := by rw [this, hs, smul_zero, sub_zero]
  have e2 : ((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂ = 0 := by
    have := congrArg N e1
    rw [map_add, map_add, map_smul, map_smul, map_smul, h₁, h₂, h₃, map_zero] at this
    calc ((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂
        = ((l₁ - l₄) • l₁ • z₁ + (l₂ - l₄) • l₂ • z₂ + (l₃ - l₄) • l₃ • z₃) -
          l₃ • ((l₁ - l₄) • z₁ + (l₂ - l₄) • z₂ + (l₃ - l₄) • z₃) := by module
      _ = 0 := by rw [this, e1, smul_zero, sub_zero]
  have e3 : ((l₁ - l₄) * (l₁ - l₃) * (l₁ - l₂)) • z₁ = 0 := by
    have := congrArg N e2
    rw [map_add, map_smul, map_smul, h₁, h₂, map_zero] at this
    calc ((l₁ - l₄) * (l₁ - l₃) * (l₁ - l₂)) • z₁
        = (((l₁ - l₄) * (l₁ - l₃)) • l₁ • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • l₂ • z₂) -
          l₂ • (((l₁ - l₄) * (l₁ - l₃)) • z₁ + ((l₂ - l₄) * (l₂ - l₃)) • z₂) := by module
      _ = 0 := by rw [this, e2, smul_zero, sub_zero]
  refine (smul_eq_zero.mp e3).resolve_left ?_
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h14) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h12)

/-- The number operator `N = Σ m_{xᵢ} m_{yᵢ}` of dual bases, as an endomorphism of `S`. -/
theorem s22a_numOp_apply (x y : Fin (2 * n) → V F n) (r : S F n) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r =
      ∑ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) r) := by
  rw [LinearMap.sum_apply]
  rfl

theorem s22a_numOp_u₁ {u₁ : S F n} {x y : Fin (2 * n) → V F n} (hx : ∀ i, x i ∈ ann F n u₁)
    (hxy : ∀ i j, pairing F n (x i) (y j) = if i = j then 1 else 0) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) u₁ = (2 * n : F) • u₁ := by
  have h1 : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₁) = u₁ := by
    intro i
    rw [s22a_m_swap (y i) (x i), show m F n (ι (Q F n) (x i)) u₁ = 0 from hx i, map_zero,
      sub_zero, s22a_pairing_comm, hxy]
    simp
  rw [s22a_numOp_apply]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul F]
  push_cast
  rfl

theorem s22a_numOp_u₂ {u₂ : S F n} {x y : Fin (2 * n) → V F n} (hy : ∀ i, y i ∈ ann F n u₂) :
    (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) u₂ = 0 := by
  rw [s22a_numOp_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show m F n (ι (Q F n) (y i)) u₂ = 0 from hy i, map_zero]

/-- For `ξ ∈ Λ`: `m_ξ u₁ = c₁ u₁ + r₁` with `N r₁ = (2n - 2) r₁`, and `m_ξ u₂ = c₂ u₂ + r₂` with
`N r₂ = 2 r₂` (`N` the number operator of dual bases of `W₁ = ker m_{u₁}`, `W₂ = ker m_{u₂}`). -/
theorem s22a_decomp {u₁ u₂ : S F n} {x y : Fin (2 * n) → V F n}
    (hx : ∀ i, x i ∈ ann F n u₁) (hy : ∀ i, y i ∈ ann F n u₂)
    (hxy : ∀ i j, pairing F n (x i) (y j) = if i = j then 1 else 0)
    (ex₁ : ∀ v ∈ ann F n u₁, v = ∑ i, pairing F n v (y i) • x i)
    (ex₂ : ∀ w ∈ ann F n u₂, w = ∑ i, pairing F n (x i) w • y i)
    (i₁ : ∀ a ∈ ann F n u₁, ∀ b ∈ ann F n u₁, pairing F n a b = 0)
    (i₂ : ∀ a ∈ ann F n u₂, ∀ b ∈ ann F n u₂, pairing F n a b = 0)
    (hsup : ann F n u₁ ⊔ ann F n u₂ = ⊤) {ξ : C F n} (hξ : ξ ∈ s22a_Λ F n) :
    ∃ (c₁ c₂ : F) (r₁ r₂ : S F n), m F n ξ u₁ = c₁ • u₁ + r₁ ∧
      (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r₁ = ((2 * n : F) - 2) • r₁ ∧
      m F n ξ u₂ = c₂ • u₂ + r₂ ∧
      (∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))) r₂ = (2 : F) • r₂ := by
  set N : Module.End F (S F n) := ∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i))
    with hN
  have hN₁ : ∀ {v : V F n}, v ∈ ann F n u₁ → ∀ r : S F n,
      N (m F n (ι (Q F n) v) r) = m F n (ι (Q F n) v) (N r) + m F n (ι (Q F n) v) r := by
    intro v hv r
    rw [hN, s22a_numOp_apply, s22a_numOp_apply]
    exact s22a_numOp_W₁ i₁ hx ex₁ hv r
  have hN₂ : ∀ {v : V F n}, v ∈ ann F n u₂ → ∀ r : S F n,
      N (m F n (ι (Q F n) v) r) = m F n (ι (Q F n) v) (N r) - m F n (ι (Q F n) v) r := by
    intro v hv r
    rw [hN, s22a_numOp_apply, s22a_numOp_apply]
    exact s22a_numOp_W₂ i₂ hy ex₂ hv r
  have hNu₁ : N u₁ = (2 * n : F) • u₁ := s22a_numOp_u₁ hx hxy
  have hNu₂ : N u₂ = 0 := s22a_numOp_u₂ hy
  induction hξ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hz
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := p))
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := q))
    have hq₁u : m F n (ι (Q F n) q₁) u₁ = 0 := hq₁
    have hq₂u : m F n (ι (Q F n) q₂) u₂ = 0 := hq₂
    have hp₁u : m F n (ι (Q F n) p₁) u₁ = 0 := hp₁
    have hp₂u : m F n (ι (Q F n) p₂) u₂ = 0 := hp₂
    refine ⟨pairing F n q₂ p₁, pairing F n q₁ p₂,
      m F n (ι (Q F n) p₂) (m F n (ι (Q F n) q₂) u₁),
      m F n (ι (Q F n) p₁) (m F n (ι (Q F n) q₁) u₂), ?_, ?_, ?_, ?_⟩
    · simp only [map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply, hq₁u, zero_add]
      rw [s22a_m_swap q₂ p₁, hp₁u, map_zero, sub_zero]
    · rw [hN₂ hp₂, hN₂ hq₂, hNu₁, map_sub, map_smul, map_smul]
      module
    · simp only [map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply, hq₂u, add_zero]
      rw [s22a_m_swap q₁ p₂, hp₂u, map_zero, sub_zero, add_comm]
    · rw [hN₁ hp₁, hN₁ hq₁, hNu₂, map_zero, zero_add]
      module
  | zero =>
    exact ⟨0, 0, 0, 0, by simp, by simp, by simp, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := hz
    obtain ⟨c₁', c₂', r₁', r₂', e₁', f₁', e₂', f₂'⟩ := hz'
    refine ⟨c₁ + c₁', c₂ + c₂', r₁ + r₁', r₂ + r₂', ?_, ?_, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, e₁, e₁', add_smul]; abel
    · rw [map_add, f₁, f₁', smul_add]
    · rw [map_add, LinearMap.add_apply, e₂, e₂', add_smul]; abel
    · rw [map_add, f₂, f₂', smul_add]
  | smul c z _ hz =>
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := hz
    refine ⟨c * c₁, c * c₂, c • r₁, c • r₂, ?_, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, e₁, smul_add, smul_smul]
    · rw [map_smul, f₁, smul_comm]
    · rw [map_smul, LinearMap.smul_apply, e₂, smul_add, smul_smul]
    · rw [map_smul, f₂, smul_comm]

theorem s22a_m_swap0 {v w : V F n} (h : pairing F n v w = 0) (s : S F n) :
    m F n (ι (Q F n) w) (m F n (ι (Q F n) v) s) = -m F n (ι (Q F n) v) (m F n (ι (Q F n) w) s) := by
  rw [s22a_m_swap, h, zero_smul, zero_sub]

theorem s22a_m_sq (v : V F n) (s : S F n) :
    m F n (ι (Q F n) v) (m F n (ι (Q F n) v) s) = Q F n v • s := by
  rw [← Module.End.mul_apply, ← map_mul, ι_sq_scalar, AlgHom.commutes, Module.algebraMap_end_apply]

/-- A spinor `s` with `ker m_u ⊆ ker m_s`, for `u ≠ 0` with `ker m_u` maximal isotropic, is a
multiple of `u`: for `s ≠ 0`, `ker m_s` is isotropic (`s22a_pairing_of_mem_ann`), so it equals the
maximal isotropic `ker m_u`, and [Chevalley, III.1.4] (`chevalley_III_1_4_unique`) applies. -/
theorem s22a_mem_span_of_le_ann {u s : S F n} (hu : u ≠ 0) (hmax : IsMaxIsotropic F n (ann F n u))
    (hs : ann F n u ≤ ann F n s) : s ∈ F ∙ u := by
  rcases eq_or_ne s 0 with rfl | hs0
  · exact Submodule.zero_mem _
  refine chevalley_III_1_4_unique F n u s hu hmax (Submodule.eq_of_le_of_finrank_le hs ?_).symm
  rw [hmax.2]
  exact s22a_finrank_le_of_isotropic fun a ha b hb => s22a_pairing_of_mem_ann hs0 ha hb

/-- **The joint kernel of the infinitesimal stabilizer of `w = a u₁ + b u₂`** (`n ≥ 3`, `a, b ≠ 0`,
`u₁, u₂` a transversal pair of even pure spinors) is `F u₁ + F u₂`. A vector `s` of the joint kernel
splits as `t + (s - t)` with `ker m_{u₁} ⊆ ker m_t`, `ker m_{u₂} ⊆ ker m_{s - t}`, and
[Chevalley, III.1.4] (`s22a_mem_span_of_le_ann`) gives `t ∈ F u₁`, `s - t ∈ F u₂`. -/
theorem s22a_fix_iff (hn : 3 ≤ n) {u₁ u₂ : S F n} (h₁ : IsEvenPureSpinor F n u₁)
    (h₂ : IsEvenPureSpinor F n u₂) (hW : ann F n u₁ ⊓ ann F n u₂ = ⊥) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (s : S F n) :
    (∀ ξ ∈ s22a_Λ F n, m F n ξ (a • u₁ + b • u₂) = 0 → m F n ξ s = 0) ↔
      s ∈ Submodule.span F {u₁, u₂} := by
  have hn0 : 0 < n := by omega
  have hu₁ : u₁ ≠ 0 := IsEvenPureSpinor.ne_zero hn0 h₁
  have hu₂ : u₂ ≠ 0 := IsEvenPureSpinor.ne_zero hn0 h₂
  have i₁ : ∀ a ∈ ann F n u₁, ∀ b ∈ ann F n u₁, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₁ ha hb
  have i₂ : ∀ a ∈ ann F n u₂, ∀ b ∈ ann F n u₂, pairing F n a b = 0 :=
    fun _ ha _ hb => s22a_pairing_of_mem_ann hu₂ ha hb
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (ann F n u₁) (ann F n u₂)
  rw [hW, finrank_bot, h₁.2.2, h₂.2.2, add_zero] at h3
  have hsup : ann F n u₁ ⊔ ann F n u₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h3, s22a_finrank_V]
  have hC : IsCompl (ann F n u₁) (ann F n u₂) := ⟨disjoint_iff.mpr hW, codisjoint_iff.mpr hsup⟩
  obtain ⟨x, y, hx, hy, hxy, ex₁, ex₂⟩ := s22a_dual_bases i₂ h₁.2.2 h₂.2.2 hC
  set N : Module.End F (S F n) := ∑ i, m F n (ι (Q F n) (x i)) * m F n (ι (Q F n) (y i)) with hN
  have hNu₁ : N u₁ = (2 * n : F) • u₁ := s22a_numOp_u₁ hx hxy
  have hNu₂ : N u₂ = 0 := s22a_numOp_u₂ hy
  have hn1 : (n : F) ≠ 1 := by exact_mod_cast (show n ≠ 1 by omega)
  have hn2 : (n : F) ≠ 2 := by exact_mod_cast (show n ≠ 2 by omega)
  have hn0' : (n : F) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  -- Elements of the infinitesimal stabilizer of `w` kill `u₁` and `u₂`.
  have hkill : ∀ ξ ∈ s22a_Λ F n, m F n ξ (a • u₁ + b • u₂) = 0 →
      m F n ξ u₁ = 0 ∧ m F n ξ u₂ = 0 := by
    intro ξ hξ hw
    obtain ⟨c₁, c₂, r₁, r₂, e₁, f₁, e₂, f₂⟩ := s22a_decomp hx hy hxy ex₁ ex₂ i₁ i₂ hsup hξ
    rw [map_add, map_smul, map_smul, e₁, e₂] at hw
    have hs4 : (a * c₁) • u₁ + a • r₁ + (b * c₂) • u₂ + b • r₂ = 0 := by
      rw [← hw]
      module
    have g₁ : N ((a * c₁) • u₁) = (2 * n : F) • ((a * c₁) • u₁) := by
      rw [map_smul, hNu₁, smul_comm]
    have g₂ : N (a • r₁) = ((2 * n : F) - 2) • (a • r₁) := by
      rw [map_smul, f₁, smul_comm]
    have g₃ : N ((b * c₂) • u₂) = (0 : F) • ((b * c₂) • u₂) := by
      rw [map_smul, hNu₂, smul_zero, zero_smul]
    have g₄ : N (b • r₂) = (2 : F) • (b • r₂) := by
      rw [map_smul, f₂, smul_comm]
    have d12 : (2 * n : F) ≠ 2 * n - 2 := by
      intro h
      exact two_ne_zero (by linear_combination h : (2 : F) = 0)
    have d13 : (2 * n : F) ≠ 0 := mul_ne_zero two_ne_zero hn0'
    have d14 : (2 * n : F) ≠ 2 := fun h => hn1 (by linear_combination h / 2)
    have d23 : (2 * n : F) - 2 ≠ 0 := fun h => hn1 (by linear_combination h / 2)
    have d24 : (2 * n : F) - 2 ≠ 2 := fun h => hn2 (by linear_combination h / 2)
    have d34 : (0 : F) ≠ 2 := two_ne_zero.symm
    have z₁ := s22a_eigen_first N g₁ g₂ g₃ g₄ d12 d13 d14 hs4
    have z₂ := s22a_eigen_first N g₂ g₁ g₃ g₄ d12.symm d23 d24 (by rw [← hs4]; abel)
    have z₃ := s22a_eigen_first N g₃ g₁ g₂ g₄ d13.symm d23.symm d34 (by rw [← hs4]; abel)
    have z₄ := s22a_eigen_first N g₄ g₁ g₂ g₃ d14.symm d24.symm d34.symm (by rw [← hs4]; abel)
    have hc₁ : c₁ = 0 := by
      rcases smul_eq_zero.mp z₁ with h | h
      · exact (mul_eq_zero.mp h).resolve_left ha
      · exact absurd h hu₁
    have hc₂ : c₂ = 0 := by
      rcases smul_eq_zero.mp z₃ with h | h
      · exact (mul_eq_zero.mp h).resolve_left hb
      · exact absurd h hu₂
    have hr₁ : r₁ = 0 := (smul_eq_zero.mp z₂).resolve_left ha
    have hr₂ : r₂ = 0 := (smul_eq_zero.mp z₄).resolve_left hb
    exact ⟨by rw [e₁, hc₁, hr₁, zero_smul, add_zero], by rw [e₂, hc₂, hr₂, zero_smul, add_zero]⟩
  constructor
  · intro hs
    have hQx : ∀ i, Q F n (x i) = 0 := fun i => s22a_Q_of_mem_ann hu₁ (hx i)
    have hQy : ∀ i, Q F n (y i) = 0 := fun i => s22a_Q_of_mem_ann hu₂ (hy i)
    -- `nᵢ = m_{xᵢ} m_{yᵢ}`: commuting idempotents, `nᵢ u₁ = u₁`, `nᵢ u₂ = 0`.
    have hn_u₁ : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₁) = u₁ := by
      intro i
      rw [s22a_m_swap (y i) (x i), show m F n (ι (Q F n) (x i)) u₁ = 0 from hx i, map_zero,
        sub_zero, s22a_pairing_comm, hxy]
      simp
    have hn_u₂ : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) u₂) = 0 := by
      intro i
      rw [show m F n (ι (Q F n) (y i)) u₂ = 0 from hy i, map_zero]
    have hyfix : ∀ i z, m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z)) = m F n (ι (Q F n) (y i)) z := by
      intro i z
      rw [s22a_m_swap (x i) (y i), hxy, ite_eq_left rfl, one_smul, s22a_m_sq, hQy, zero_smul,
        map_zero, sub_zero]
    have hxkill : ∀ i z, m F n (ι (Q F n) (x i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z)) = 0 := by
      intro i z
      rw [s22a_m_sq, hQx, zero_smul]
    have hidem : ∀ i z, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z))) =
          m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z) := by
      intro i z
      rw [hyfix]
    have hcomm : ∀ i j z, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i))
        (m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j)) z))) =
          m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j))
            (m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) z))) := by
      intro i j z
      by_cases hij : i = j
      · subst hij; rfl
      have p1 : pairing F n (x j) (y i) = 0 := by rw [hxy, ite_eq_right (Ne.symm hij)]
      have p2 : pairing F n (x j) (x i) = 0 := i₁ _ (hx j) _ (hx i)
      have p3 : pairing F n (y j) (y i) = 0 := i₂ _ (hy j) _ (hy i)
      have p4 : pairing F n (y j) (x i) = 0 := by rw [s22a_pairing_comm, hxy, ite_eq_right hij]
      rw [s22a_m_swap0 p1, map_neg, s22a_m_swap0 p2, neg_neg, s22a_m_swap0 p3, map_neg, map_neg,
        s22a_m_swap0 p4, map_neg, neg_neg]
    -- `s ∈ Fix` forces `nᵢ s = nⱼ s`.
    have heq : ∀ i j, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) s) =
        m F n (ι (Q F n) (x j)) (m F n (ι (Q F n) (y j)) s) := by
      intro i j
      have hξ : ι (Q F n) (x i) * ι (Q F n) (y i) - ι (Q F n) (x j) * ι (Q F n) (y j) ∈
          s22a_Λ F n := Submodule.sub_mem _ (s22a_ι_mul_ι_mem_Λ _ _) (s22a_ι_mul_ι_mem_Λ _ _)
      have hw : m F n (ι (Q F n) (x i) * ι (Q F n) (y i) - ι (Q F n) (x j) * ι (Q F n) (y j))
          (a • u₁ + b • u₂) = 0 := by
        simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, map_add,
          map_smul, hn_u₁, hn_u₂, smul_zero, add_zero, sub_self]
      have := hs _ hξ hw
      simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply] at this
      exact sub_eq_zero.mp this
    set k₀ : Fin (2 * n) := ⟨0, by omega⟩
    set t := m F n (ι (Q F n) (x k₀)) (m F n (ι (Q F n) (y k₀)) s) with ht_def
    have ht : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) t) = t := by
      intro i
      rw [ht_def, hcomm, heq i k₀, hidem]
    have hst : ∀ i, m F n (ι (Q F n) (x i)) (m F n (ι (Q F n) (y i)) (s - t)) = 0 := by
      intro i
      rw [map_sub, map_sub, ht, heq i k₀, ← ht_def, sub_self]
    have ht₁ : t ∈ F ∙ u₁ := by
      refine s22a_mem_span_of_le_ann hu₁ h₁.2 fun v hv => ?_
      rw [s22a_mem_ann, ex₁ v hv, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, ← ht i, hxkill, smul_zero]
    have ht₂ : s - t ∈ F ∙ u₂ := by
      refine s22a_mem_span_of_le_ann hu₂ h₂.2 fun w hw => ?_
      rw [s22a_mem_ann, ex₂ w hw, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, ← hyfix, hst, map_zero, smul_zero]
    have hle₁ : (F ∙ u₁) ≤ Submodule.span F {u₁, u₂} :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    have hle₂ : (F ∙ u₂) ≤ Submodule.span F {u₁, u₂} :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have h12 := Submodule.add_mem _ (hle₁ ht₁) (hle₂ ht₂)
    rwa [add_sub_cancel] at h12
  · intro hs ξ hξ hw
    obtain ⟨k₁, k₂, rfl⟩ := Submodule.mem_span_pair.mp hs
    obtain ⟨h1, h2⟩ := hkill ξ hξ hw
    rw [map_add, map_smul, map_smul, h1, h2, smul_zero, smul_zero, add_zero]

end S22aFix

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- The homomorphism `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}` (§2.2). -/
noncomputable def restrictW₁ : P.spinL₁L₂ →* (Module.End (Kd d) P.W₁)ˣ :=
  pairRestrict (Kd d) n P.u₁ P.u₂

/-- `det₁` is the determinant of `restrictW₁`. -/
theorem det_restrictW₁ (g : P.spinL₁L₂) :
    LinearMap.det ((P.restrictW₁ g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) =
      P.det₁ g :=
  rfl

/-- The pairing of `V_K` identifies `W₂` with `W₁*`: `y ↦ (x ↦ (x, y)_V)` (§2.2). -/
noncomputable def pairingW₂ : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁ :=
  ((pairing (Kd d) n).compl₁₂ P.W₁.subtype P.W₂.subtype).flip

theorem s22a_restrictW₁_apply (g : P.spinL₁L₂) (x : P.W₁) :
    (((P.restrictW₁ g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) x : V (Kd d) n) =
      rho (Kd d) n g x := rfl

theorem s22a_restrictW₁_inv_apply (g : P.spinL₁L₂) (x : P.W₁) :
    ((((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) x :
        V (Kd d) n) = rho (Kd d) n ((g : Spin (Kd d) n)⁻¹) x := by
  rw [← map_inv]
  rfl

theorem s22a_pairingW₂_apply (y : P.W₂) (x : P.W₁) :
    P.pairingW₂ y x = pairing (Kd d) n (x : V (Kd d) n) (y : V (Kd d) n) := rfl

/-- `W₂` is isotropic for `(·,·)_V`. -/
theorem s22a_pairing_W₂ {y y' : V (Kd d) n} (hy : y ∈ P.W₂) (hy' : y' ∈ P.W₂) :
    pairing (Kd d) n y y' = 0 :=
  s22a_pairing_of_mem_ann P.s22a_u₂_ne_zero hy hy'

/-- A vector of `W₂` orthogonal to `W₁` is zero (when `V_K = W₁ ⊕ W₂`). -/
theorem s22a_eq_zero_of_W₂ (hW : P.W₁ ⊓ P.W₂ = ⊥) {y : V (Kd d) n} (hy : y ∈ P.W₂)
    (h : ∀ x ∈ P.W₁, pairing (Kd d) n x y = 0) : y = 0 := by
  have hC := P.isCompl_of_inf_eq_bot hW
  apply s22a_pairing_sepLeft
  intro v
  obtain ⟨x, hx, w, hw, rfl⟩ :=
    Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, s22a_pairing_comm, h x hx, P.s22a_pairing_W₂ hy hw, zero_add]

/-- **[Igusa, Lemma 1]** as used in §2.2 (kernel): the kernel of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)` is
`{±1}`, so that `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` embeds in `GL(W₁)`.

Proof: the statement of record `igusa_lemma1_ker`, for `F = K` (`restrictW₁` is
`pairRestrict K n u₁ u₂`). -/
theorem restrictW₁_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.restrictW₁ g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 :=
  igusa_lemma1_ker (Kd d) n P.u₁ P.u₂ P.isPure P.isPure₂ hW g

theorem s22a_mukai_u₁_u₂_ne_zero (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    mukai (Kd d) n P.u₁ P.u₂ ≠ 0 := fun h => (P.s22a_mukai_u₁_u₂_eq_zero_iff.mp h) hW

theorem s22a_χ₁_spec (g : P.spinL₁L₂) :
    m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.χ₁ g • P.u₁ :=
  Classical.choose_spec ((Subgroup.mem_inf.mp g.2).1)

theorem s22a_χ₂_spec (g : P.spinL₁L₂) :
    m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₂ = P.χ₂ g • P.u₂ :=
  Classical.choose_spec ((Subgroup.mem_inf.mp g.2).2)

/-- `χ₁ χ₂ = 1`: `g` is an isometry of `(·,·)_S` and `(λ₁, λ₂)_S ≠ 0`. -/
theorem s22a_χ₁_mul_χ₂ (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) : P.χ₁ g * P.χ₂ g = 1 := by
  have h := s22a_mukai_spin (g : Spin (Kd d) n) P.u₁ P.u₂
  rw [P.s22a_χ₁_spec, P.s22a_χ₂_spec] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [mul_comm (P.χ₂ g)] at h
  have hc := P.s22a_mukai_u₁_u₂_ne_zero hW
  calc P.χ₁ g * P.χ₂ g = P.χ₁ g * P.χ₂ g * mukai (Kd d) n P.u₁ P.u₂ / mukai (Kd d) n P.u₁ P.u₂ := by
        field_simp
    _ = 1 := by rw [h, div_self hc]

/-- The claim "`Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to `GL(W₁)`, and so to `GL_{2n}(K)`" (§2.2,
[Igusa, Lemma 1]), on `K`-points: the image of `Spin(V_K)_{ℓ₁,ℓ₂} → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`,
consists of the automorphisms whose determinant is a square in `K` (it contains `SL(W₁)`, and
`det₁ = χ₁²`); with `restrictW₁_eq_one_iff`, `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to that subgroup.

Correction of the paper (agreed with the project owner; REPORT.md): the paper says the quotient is
isomorphic to `GL(W₁)`. That holds for the algebraic groups (over `K̄`, as in Igusa's lemma) but not
for `K`-points: `diag(a, 1, …, 1)` with `a ∉ K^{×2}` is not in the image (its lifts
`±(√a⁻¹ x y + √a y x)` are not `K`-rational). Lemma 2.2.2 and the rest of the paper are unaffected.

Proof: [Igusa, Lemma 1] in its form for `F`-points (`igusa_lemma1_range`), for `F = K`
(`restrictW₁` is `pairRestrict K n u₁ u₂`). -/
theorem range_restrictW₁ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) =
      {A : (Module.End (Kd d) P.W₁)ˣ |
        IsSquare (LinearMap.det (A : Module.End (Kd d) P.W₁))} :=
  igusa_lemma1_range (Kd d) n P.u₁ P.u₂ P.isPure P.isPure₂ hW

/-- "**The quotient maps injectively into `SO⁺(V_K)`**" (§2.2, [Igusa, Lemma 1]): an element of
`Spin(V_K)_{ℓ₁,ℓ₂}` acting trivially on `V_K` is `±1`.

Proof: the kernel of `ρ : Spin(V_K) → SO(V_K)` is `{±1}` (library: Tau Ceti,
`mem_ker_spinToOrthogonal_iff`). -/
theorem rho_eq_one_iff (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    rho (Kd d) n g = 1 ↔
      ((g : Spin (Kd d) n) : C (Kd d) n) = 1 ∨ ((g : Spin (Kd d) n) : C (Kd d) n) = -1 :=
  s22a_rho_eq_one_iff (s22a_n_pos P) _

/-- "**`W₂` is identified with `W₁*` via the bilinear pairing of `V_K`**" (§2.2): when
`W₁ ∩ W₂ = 0`, `y ↦ (·, y)_V|_{W₁}` is an isomorphism `W₂ ≅ W₁*`. -/
theorem pairingW₂_bijective (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Bijective P.pairingW₂ := by
  have hinj : Function.Injective P.pairingW₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    apply P.s22a_eq_zero_of_W₂ hW y.2
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    rwa [P.s22a_pairingW₂_apply] at this
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Subspace.dual_finrank_eq]
  exact P.isPure₂.2.2.trans P.isPure.2.2.symm

/-- "**The element of `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` corresponding to `g ∈ GL(W₁)` acts on `W₂` via
`(g*)⁻¹`**, where `W₂` is identified with `W₁*` via the bilinear pairing of `V_K`" (§2.2,
[Igusa, Lemma 1]): under `pairingW₂`, `ρ(g)|_{W₂}` is the inverse transpose of `ρ(g)|_{W₁}`.

Proof: [Igusa, Lemma 1] (`igusa_lemma1_dual`: `(ρ(h) x, ρ(h) y)_V = (x, y)_V` for `x ∈ W₁`,
`y ∈ W₂`), applied to `h = g⁻¹`, `x`, `ρ(g) y`. -/
theorem pairingW₂_rho (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) (y : V (Kd d) n)
    (hy : y ∈ P.W₂) :
    P.pairingW₂ ⟨rho (Kd d) n g y, P.rho_mem_W₂ g y hy⟩ =
      LinearMap.dualMap
        (((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁)
        (P.pairingW₂ ⟨y, hy⟩) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.dualMap_apply, P.s22a_pairingW₂_apply, P.s22a_pairingW₂_apply,
    P.s22a_restrictW₁_inv_apply]
  have h := igusa_lemma1_dual (Kd d) n P.u₁ P.u₂ g⁻¹ (x : V (Kd d) n) (rho (Kd d) n g y) x.2
    (P.rho_mem_W₂ g y hy)
  calc pairing (Kd d) n (x : V (Kd d) n) (rho (Kd d) n g y)
      = pairing (Kd d) n (rho (Kd d) n ((g : Spin (Kd d) n)⁻¹) x)
          (rho (Kd d) n ((g : Spin (Kd d) n)⁻¹) (rho (Kd d) n g y)) := h.symm
    _ = pairing (Kd d) n (rho (Kd d) n ((g : Spin (Kd d) n)⁻¹) x) y := by rw [s22a_rho_inv_rho]

/-- "**`det₂(s) = det₁(s)⁻¹`**" (§2.2), for `s ∈ Spin(V_K)_{ℓ₁,ℓ₂}`. -/
theorem det₂_eq_inv (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.det₂ g = (P.det₁ g)⁻¹ := by
  set e := LinearEquiv.ofBijective P.pairingW₂ (P.pairingW₂_bijective hd hW) with he
  set B : Module.End (Kd d) P.W₁ :=
    (((P.restrictW₁ g)⁻¹ : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) with hB
  have hconj : (rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
      (fun v hv => P.rho_mem_W₂ g v hv) =
      (e.symm : Module.Dual (Kd d) P.W₁ →ₗ[Kd d] P.W₂) ∘ₗ B.dualMap ∘ₗ
        (e.symm.symm : P.W₂ →ₗ[Kd d] Module.Dual (Kd d) P.W₁) := by
    apply LinearMap.ext
    intro y
    apply e.injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    rw [he, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hB]
    exact P.pairingW₂_rho hd hW g y y.2
  have hdet : P.det₂ g = LinearMap.det B := by
    show LinearMap.det ((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
      (fun v hv => P.rho_mem_W₂ g v hv)) = _
    rw [hconj, LinearMap.det_conj, LinearMap.det_dualMap]
  rw [hdet, hB, ← P.det_restrictW₁ g]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

/-- "**`ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁`**" (§2.2, by the proof of [Igusa, Lemma 1] and [Chevalley, III.3.2]): the
character `χ₁` of `Spin(V_K)_{ℓ₁,ℓ₂}` on `ℓ̃₁` satisfies `χ₁² = det₁`. Used again in §6.4
("`ℓ̃ᵢ²` is the character `⋀^{2n} Wᵢ ≅ detᵢ`").

Proof: `igusa_lemma1_sq` (the statement of record of the cited proof of [Igusa, Lemma 1]). -/
theorem χ₁_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₁ g ^ 2 = P.det₁ g :=
  igusa_lemma1_sq (Kd d) n P.u₁ P.isPure P.u₁_ne_zero g (Subgroup.mem_inf.mp g.2).1 (P.χ₁ g)
    (P.s22a_χ₁_spec g)

/-- "**`ℓ̃₂ ⊗ ℓ̃₂ ≅ det₂`**" (§2.2): `χ₂² = det₂` (`igusa_lemma1_sq`). -/
theorem χ₂_sq (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    P.χ₂ g ^ 2 = P.det₂ g :=
  igusa_lemma1_sq (Kd d) n P.u₂ P.isPure₂ P.s22a_u₂_ne_zero g (Subgroup.mem_inf.mp g.2).2 (P.χ₂ g)
    (P.s22a_χ₂_spec g)

/-! ## Lemma 2.2.2 -/

/-- `Spin(V_K)_P ⊆ Spin(V_K)_{ℓ₁,ℓ₂}`: an element fixing `P_K` pointwise fixes `u₁` and `u₂`. -/
theorem spinPK_le_spinL₁L₂ : P.spinPK ≤ P.spinL₁L₂ := by
  intro g hg
  refine Subgroup.mem_inf.mpr ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
  · rw [one_smul]
    exact hg P.u₁ (Submodule.subset_span (Set.mem_insert _ _))
  · rw [one_smul]
    exact hg P.u₂ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

/-- An element fixing `u₁` and `u₂` fixes `P_K` pointwise. -/
theorem s22a_mem_spinPK {g : Spin (Kd d) n}
    (h₁ : m (Kd d) n (g : C (Kd d) n) P.u₁ = P.u₁) (h₂ : m (Kd d) n (g : C (Kd d) n) P.u₂ = P.u₂) :
    g ∈ P.spinPK := by
  intro p hp
  have hle : P.PK ≤ LinearMap.eqLocus (m (Kd d) n (g : C (Kd d) n)) LinearMap.id := by
    rw [PK, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  exact hle hp

/-- The scalar `-1 ∈ Spin(V_K)`. -/
noncomputable def s22a_negOne : Spin (Kd d) n :=
  ⟨-1, by
    have := s22a_nontrivial_V (F := Kd d) (s22a_n_pos P)
    exact neg_one_mem_spinGroup (Q (Kd d) n) s22a_Q_nondegenerate.ne_zero⟩

theorem s22a_coe_negOne : ((P.s22a_negOne : Spin (Kd d) n) : C (Kd d) n) = -1 := rfl

theorem s22a_rho_negOne_mul (g : Spin (Kd d) n) (v : V (Kd d) n) :
    rho (Kd d) n (P.s22a_negOne * g) v = rho (Kd d) n g v := by
  rw [s22a_rho_mul]
  have h1 : rho (Kd d) n P.s22a_negOne = 1 :=
    (s22a_rho_eq_one_iff (s22a_n_pos P) _).mpr (Or.inr P.s22a_coe_negOne)
  rw [h1]
  rfl

theorem s22a_m_negOne_mul (g : Spin (Kd d) n) (s : S (Kd d) n) :
    m (Kd d) n ((P.s22a_negOne * g : Spin (Kd d) n) : C (Kd d) n) s =
      -m (Kd d) n (g : C (Kd d) n) s := by
  rw [Submonoid.coe_mul, P.s22a_coe_negOne, neg_one_mul, map_neg, LinearMap.neg_apply]

/-- The homomorphism `Spin(V_K)_P → GL(W₁)`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def restrictW₁P : P.spinPK →* (Module.End (Kd d) P.W₁)ˣ :=
  P.restrictW₁.comp (Subgroup.inclusion P.spinPK_le_spinL₁L₂)

/-- Every `A ∈ SL(W₁)` is `ρ(g)|_{W₁}` for some `g ∈ Spin(V_K)_P`: by [Igusa, Lemma 1]
(`range_restrictW₁`; `det A = 1 = 1²`), `A = ρ(g₀)|_{W₁}` with `g₀ ∈ Spin(V_K)_{ℓ₁,ℓ₂}`; then
`χ₁(g₀)² = det₁(g₀) = 1` and `χ₁ χ₂ = 1`, so `g₀` or `-g₀` fixes `u₁` and `u₂`. -/
theorem s22a_exists_spinPK (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (A : Module.End (Kd d) P.W₁)
    (hA : LinearMap.det A = 1) :
    ∃ g : P.spinPK, ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) = A := by
  have hAu : IsUnit A := (LinearMap.isUnit_iff_isUnit_det A).mpr (by rw [hA]; exact isUnit_one)
  have hmem : hAu.unit ∈ (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) := by
    rw [P.range_restrictW₁ hd hW]
    show IsSquare (LinearMap.det ((hAu.unit : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁))
    rw [IsUnit.unit_spec, hA]
    exact ⟨1, (one_mul 1).symm⟩
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hmem
  have hg₀A : ∀ v : P.W₁, rho (Kd d) n g₀ v = A v := fun v => by
    have := congrArg (fun B : (Module.End (Kd d) P.W₁)ˣ =>
      (((B : Module.End (Kd d) P.W₁) v : P.W₁) : V (Kd d) n)) hg₀
    simpa only [P.s22a_restrictW₁_apply, IsUnit.unit_spec] using this
  have hdet₁ : P.det₁ g₀ = 1 := by
    rw [← P.det_restrictW₁ g₀, hg₀, IsUnit.unit_spec, hA]
  have hsq : P.χ₁ g₀ ^ 2 = 1 := by rw [P.χ₁_sq hd hW, hdet₁]
  have hχχ := P.s22a_χ₁_mul_χ₂ hW g₀
  have hres : ∀ g' : Spin (Kd d) n, (∀ v, rho (Kd d) n g' v = rho (Kd d) n g₀ v) →
      (m (Kd d) n (g' : C (Kd d) n) P.u₁ = P.u₁) → (m (Kd d) n (g' : C (Kd d) n) P.u₂ = P.u₂) →
      ∃ g : P.spinPK, ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁) = A := by
    intro g' hρ h₁ h₂
    refine ⟨⟨g', P.s22a_mem_spinPK h₁ h₂⟩, ?_⟩
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show rho (Kd d) n g' v = _
    rw [hρ, hg₀A v]
  rw [sq] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · have h' : P.χ₂ g₀ = 1 := by rw [h, one_mul] at hχχ; exact hχχ
    refine hres g₀ (fun v => rfl) ?_ ?_
    · rw [P.s22a_χ₁_spec, h, one_smul]
    · rw [P.s22a_χ₂_spec, h', one_smul]
  · have h' : P.χ₂ g₀ = -1 := by
      rw [h, neg_one_mul, neg_eq_iff_eq_neg] at hχχ
      exact hχχ
    refine hres (P.s22a_negOne * g₀) (fun v => P.s22a_rho_negOne_mul g₀ v) ?_ ?_
    · rw [P.s22a_m_negOne_mul, P.s22a_χ₁_spec, h, neg_one_smul, neg_neg]
    · rw [P.s22a_m_negOne_mul, P.s22a_χ₂_spec, h', neg_one_smul, neg_neg]

/-- The proof of Lemma 2.2.2 (see `WeilClasses.lemma2_2_2_restrict`). -/
theorem s22a_restrict_aux (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Injective P.restrictW₁P ∧
      P.restrictW₁P.range = specialLinearUnits (Kd d) P.W₁ := by
  -- The proof of the paper: `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is identified with a subgroup of `GL(W₁)`
  -- containing `SL(W₁)` ([Igusa, Lemma 1]: `restrictW₁_eq_one_iff`, `range_restrictW₁`),
  -- `det₁ = χ₁²` and `χ₁ χ₂ = 1`; so `Spin(V_K)_P` maps onto `SL(W₁)`, injectively since
  -- `-1 ∉ Spin(V_K)_P`.
  have hu₁ := P.u₁_ne_zero
  have hfix₁ : ∀ g : P.spinPK, m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.u₁ :=
    fun g => g.2 P.u₁ (Submodule.subset_span (Set.mem_insert _ _))
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    rcases (P.restrictW₁_eq_one_iff hd hW (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g)).mp hg
      with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exfalso
      have h1 := hfix₁ g
      have h2 : ((g : Spin (Kd d) n) : C (Kd d) n) = -1 := h
      rw [h2, map_neg, map_one, LinearMap.neg_apply, Module.End.one_apply] at h1
      have : (2 : Kd d) • P.u₁ = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        exact neg_add_cancel _
      exact hu₁ ((smul_eq_zero.mp this).resolve_left two_ne_zero)
  · ext A
    constructor
    · rintro ⟨g, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      have hχ : P.χ₁ (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g) = 1 :=
        smul_left_injective (Kd d) hu₁
          ((P.s22a_χ₁_spec _).symm.trans ((hfix₁ g).trans (one_smul _ _).symm))
      have h := P.χ₁_sq hd hW (Subgroup.inclusion P.spinPK_le_spinL₁L₂ g)
      rw [hχ, one_pow] at h
      simp only [Units.coe_map, Units.val_one]
      exact h.symm
    · intro hA
      have hdetA : LinearMap.det (A : Module.End (Kd d) P.W₁) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.mp hA)
        simpa using this
      obtain ⟨g, hg⟩ := P.s22a_exists_spinPK hd hW (A : Module.End (Kd d) P.W₁) hdetA
      exact ⟨g, Units.ext hg⟩

/-- `det(ρ(g)|_{W₁}) = 1` for `g ∈ Spin(V_K)_P` (`lemma2_2_2_restrict`). -/
theorem s22a_det_restrictW₁P (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinPK) :
    LinearMap.det ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁) = 1 := by
  have hmem : P.restrictW₁P g ∈ specialLinearUnits (Kd d) P.W₁ :=
    (P.s22a_restrict_aux hd hW).2 ▸ ⟨g, rfl⟩
  have := congrArg Units.val (MonoidHom.mem_ker.mp hmem)
  simpa using this

/-- `g ↦` the matrix of `ρ(g)|_{W₁}` in a basis `B` of `W₁`, a homomorphism
`Spin(V_K)_P → SL_{2n}(K)` (`s22a_det_restrictW₁P`). -/
noncomputable def s22a_toSL (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥)
    (B : Module.Basis (Fin (2 * n)) (Kd d) P.W₁) :
    P.spinPK →* Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d) where
  toFun g := ⟨LinearMap.toMatrix B B
      ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) : Module.End (Kd d) P.W₁),
    by rw [LinearMap.det_toMatrix, P.s22a_det_restrictW₁P hd hW]⟩
  map_one' := by
    apply Subtype.ext
    show LinearMap.toMatrix B B ((P.restrictW₁P 1 : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁) = 1
    rw [MonoidHom.map_one, Units.val_one, LinearMap.toMatrix_one]
  map_mul' := by
    intro g h
    apply Subtype.ext
    show LinearMap.toMatrix B B ((P.restrictW₁P (g * h) : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁) =
      LinearMap.toMatrix B B ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁) *
      LinearMap.toMatrix B B ((P.restrictW₁P h : (Module.End (Kd d) P.W₁)ˣ) :
        Module.End (Kd d) P.W₁)
    rw [MonoidHom.map_mul, Units.val_mul, LinearMap.toMatrix_mul]

/-- `s22a_toSL` is bijective (`lemma2_2_2_restrict` and `LinearMap.toMatrix`). -/
theorem s22a_toSL_bijective (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥)
    (B : Module.Basis (Fin (2 * n)) (Kd d) P.W₁) : Function.Bijective (P.s22a_toSL hd hW B) := by
  refine ⟨fun g h hgh => (P.s22a_restrict_aux hd hW).1 ?_, fun M => ?_⟩
  · apply Units.ext
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d) =>
      (A : Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d))) hgh
    exact (LinearMap.toMatrix B B).injective h1
  · -- `M ∈ SL_{2n}(K)` is the matrix of an endomorphism of `W₁` of determinant `1`
    have hA : LinearMap.det (Matrix.toLin B B (M : Matrix (Fin (2 * n)) (Fin (2 * n)) (Kd d))) =
        1 := by
      rw [LinearMap.det_toLin]
      exact M.2
    obtain ⟨g, hg⟩ := P.s22a_exists_spinPK hd hW _ hA
    refine ⟨g, Subtype.ext ?_⟩
    show LinearMap.toMatrix B B ((P.restrictW₁P g : (Module.End (Kd d) P.W₁)ˣ) :
      Module.End (Kd d) P.W₁) = _
    rw [hg]
    exact LinearMap.toMatrix_toLin B B _

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint corrected: the group `Spin(V_K)_P` is
isomorphic to `SL_{2n}(K)`. The paper prints `SL_n(K)`; this is an obvious misprint, since `W₁` has
dimension `2n` and the text just before says `GL(W₁) ≅ GL_{2n}(K)`. Standing hypothesis:
`W₁ ∩ W₂ = 0`. See `lemma2_2_2_restrict` for the isomorphism itself and the proof (here composed
with the matrix in a basis of `W₁`). -/
theorem _root_.WeilClasses.lemma2_2_2 (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Nonempty (P.spinPK ≃* Matrix.SpecialLinearGroup (Fin (2 * n)) (Kd d)) := by
  obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (2 * n)) (Kd d) P.W₁) :=
    ⟨Module.finBasisOfFinrankEq (Kd d) P.W₁ P.isPure.2.2⟩
  exact ⟨MulEquiv.ofBijective (P.s22a_toSL hd hW B) (P.s22a_toSL_bijective hd hW B)⟩

/-- **Lemma 2.2.2** (`lemma-Spin-V-K-is-SL-n-K`), misprint `SL_n(K)` corrected to `SL_{2n}(K)`,
in the form of its proof: `g ↦ ρ(g)|_{W₁}` maps `Spin(V_K)_P` isomorphically onto `SL(W₁)`.

Proof (the paper's): by [Igusa, Lemma 1], `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` embeds in `GL(W₁)`
(`restrictW₁_eq_one_iff`, `igusa_lemma1_ker`) with image the automorphisms of square determinant
(`range_restrictW₁`, `igusa_lemma1_range`), which contain `SL(W₁)`; `det₁ = χ₁²` (`χ₁_sq`); and
`-1 ∉ Spin(V_K)_P`.

Gap in the paper (filled): the proof says "`Spin(V_K)_P` is the kernel of `det₁` in
`Spin(V_K)_{ℓ₁,ℓ₂}`", but `-1 ∈ ker det₁ ∖ Spin(V_K)_P`. Here: `χ₁ χ₂ = 1` (`s22a_χ₁_mul_χ₂`), so
`Spin(V_K)_P` is the kernel of `χ₁`, and the kernel of `det₁ = χ₁²` is `{±1} · Spin(V_K)_P`; as
`-1 ∉ Spin(V_K)_P`, `Spin(V_K)_P` maps isomorphically onto the image `SL(W₁)` of `ker det₁`
(`s22a_exists_spinPK`). -/
theorem _root_.WeilClasses.lemma2_2_2_restrict (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) :
    Function.Injective P.restrictW₁P ∧
      P.restrictW₁P.range = specialLinearUnits (Kd d) P.W₁ :=
  P.s22a_restrict_aux hd hW

/-! ## Remark 2.2.3 -/

/-- A vector of `P_K` on neither line is `a u₁ + b u₂` with `a, b ≠ 0`. -/
theorem s22a_coeffs {w : S (Kd d) n} (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    ∃ a b : Kd d, a ≠ 0 ∧ b ≠ 0 ∧ w = a • P.u₁ + b • P.u₂ := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hwP
  refine ⟨a, b, ?_, ?_, rfl⟩
  · rintro rfl
    apply hw₂
    rw [zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro rfl
    apply hw₁
    rw [zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), first claim:
for `n ≥ 3`, a vector `w ∈ P_K` on neither `ℓ̃₁` nor `ℓ̃₂` is not a pure spinor ("as commented
above", i.e. by [Chevalley, III.1.12]). Reading: `w` is a `K`-point of the plane (`w ∈ P_K`); this
includes the nonzero rational points of `P`.

Proof (the paper's): [Chevalley, III.1.12] (`chevalley_III_1_12`), as in the comment after
Lemma 2.2.1 (`isEvenPureSpinor_iff_of_mem_span`), here for the `K`-points `u₁, u₂`. -/
theorem _root_.WeilClasses.remark2_2_3_not_pure (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    ¬ IsEvenPureSpinor (Kd d) n w := by
  intro hpure
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hwP
  rcases chevalley_III_1_12 (Kd d) n (by omega) _ _ P.isPure P.isPure₂ hW a b hpure with rfl | rfl
  · apply hw₂
    rw [zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply hw₁
    rw [zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` odd
([Igusa, Lemma 2] and the remark after it): for `n ≥ 3` odd and `w ∈ P_K` on neither `ℓ̃₁` nor
`ℓ̃₂`, the stabilizer of `w` in `Spin(V_K)` is `Spin(V_K)_P`.

Proof (the paper's): `w = a u₁ + b u₂` with `a, b ≠ 0` (`s22a_coeffs`), and [Igusa, Lemma 2] and
the remark following it (`igusa_lemma2_stab_odd`, for `F = K`). -/
theorem _root_.WeilClasses.remark2_2_3_odd (hd : 0 < d) (hn : 3 ≤ n) (hodd : Odd n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) = P.spinPK := by
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  exact igusa_lemma2_stab_odd (Kd d) n hn hodd P.u₁ P.u₂ P.isPure P.isPure₂ hW a b ha hb

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), `n` even
([Igusa, Lemma 2] and the remark after it): "the stabilizer has two connected components and the
identity component is `Spin(V_K)_P`". Reading for the group of `K`-points: `Spin(V_K)_P` is a normal
subgroup of index `2` of the stabilizer of `w` in `Spin(V_K)` (the non-identity component, the
elements exchanging `ℓ₁` and `ℓ₂`, has `K`-points).

Proof (the paper's): `w = a u₁ + b u₂` with `a, b ≠ 0` (`s22a_coeffs`), and [Igusa, Lemma 2] and
the remark following it (`igusa_lemma2_stab_even`, for `F = K`). -/
theorem _root_.WeilClasses.remark2_2_3_even (hd : 0 < d) (hn : 3 ≤ n) (heven : Even n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂}) :
    P.spinPK ≤ fixingSpin (Kd d) n (Submodule.span (Kd d) {w}) ∧
      (P.spinPK.subgroupOf (fixingSpin (Kd d) n (Submodule.span (Kd d) {w}))).Normal ∧
      P.spinPK.relIndex (fixingSpin (Kd d) n (Submodule.span (Kd d) {w})) = 2 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  exact igusa_lemma2_stab_even (Kd d) n hn heven P.u₁ P.u₂ P.isPure P.isPure₂ hW a b ha hb

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "in particular,
`w` determines `P`": any `K`-secant `P'` with `W₁' ∩ W₂' = 0` whose plane contains `w` has the same
plane `P'_K = P_K` (hence the same rational plane).

Departure from the paper (reason 2): the paper derives this from the description of the stabilizer
of `w` ([Igusa, Lemma 2]: its identity component is `Spin(V_K)_P`). Identity components of algebraic
groups are not available, and on `K`-points two subgroups of index `2` of the stabilizer need not
coincide a priori. Here `P_K` is the joint kernel of the infinitesimal stabilizer of `w`
(`s22a_fix_iff`), which depends only on `w`. -/
theorem _root_.WeilClasses.remark2_2_3_determines (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (P' : KSecant n d) (hW' : P'.W₁ ⊓ P'.W₂ = ⊥) (hwP' : w ∈ P'.PK) :
    P'.PK = P.PK := by
  -- `P_K` is the joint kernel of the infinitesimal stabilizer of `w` (`s22a_fix_iff`), which
  -- depends only on `w`.
  have hnp := remark2_2_3_not_pure P hd hn hW w hwP hw₁ hw₂
  have hw0 : w ≠ 0 := fun h => hw₁ (h ▸ Submodule.zero_mem _)
  have hline : ∀ {u : S (Kd d) n}, IsEvenPureSpinor (Kd d) n u →
      w ∉ Submodule.span (Kd d) {u} := by
    intro u hu h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw0 hc.symm
    apply hnp
    rw [← hc]
    exact s22a_isEvenPureSpinor_smul hu hc0
  obtain ⟨a, b, ha, hb, hab⟩ := P.s22a_coeffs hwP hw₁ hw₂
  obtain ⟨a', b', ha', hb', hab'⟩ := P'.s22a_coeffs hwP' (hline P'.isPure) (hline P'.isPure₂)
  ext s
  show s ∈ Submodule.span (Kd d) {P'.u₁, P'.u₂} ↔ s ∈ Submodule.span (Kd d) {P.u₁, P.u₂}
  rw [← s22a_fix_iff hn P'.isPure P'.isPure₂ hW' ha' hb', ← hab', hab,
    s22a_fix_iff hn P.isPure P.isPure₂ hW ha hb]

/-- **Remark 2.2.3** (`remark-stabilizer-of-w-may-have-two-connected-components`), "`ℙ(P)` is the
unique secant to the spinor variety through `w`": if `w` lies on the line through two distinct
points `[x], [y]` of the (complex) even spinor variety, then that line is `ℙ(P_ℂ)`.

Departure from the paper (reason 2): as for `remark2_2_3_determines`, over `ℂ`. `ker m_w = 0`
(`s22a_ann_combo_eq_bot`, the computation of the proof of [Chevalley, III.1.12]) forces `x, y` to be
transversal with nonzero coefficients, and both `P_ℂ` and `ℂx + ℂy` are the joint kernel of the
infinitesimal stabilizer of `w` (`s22a_fix_iff`). -/
theorem _root_.WeilClasses.remark2_2_3_unique_secant (hd : 0 < d) (hn : 3 ≤ n)
    (hW : P.W₁ ⊓ P.W₂ = ⊥) (w : S (Kd d) n) (hwP : w ∈ P.PK)
    (hw₁ : w ∉ Submodule.span (Kd d) {P.u₁}) (hw₂ : w ∉ Submodule.span (Kd d) {P.u₂})
    (x y : S ℂ n) (hx : IsEvenPureSpinor ℂ n x) (hy : IsEvenPureSpinor ℂ n y)
    (hxy : LinearIndependent ℂ ![x, y]) (hw : bcS (Kd d) ℂ n w ∈ Submodule.span ℂ {x, y}) :
    Submodule.span ℂ {x, y} =
      Submodule.span ℂ {bcS (Kd d) ℂ n P.u₁, bcS (Kd d) ℂ n P.u₂} := by
  -- Over `ℂ`, `w` lies on the secant `ℙ(P_ℂ)` only, since the joint kernel of its infinitesimal
  -- stabilizer is `P_ℂ` and also the plane of any secant through `w` (`s22a_fix_iff`).
  obtain ⟨a, b, ha, hb, rfl⟩ := P.s22a_coeffs hwP hw₁ hw₂
  obtain ⟨p₁, p₂, hW'⟩ := s22a_bc_pure_pair (Kd d) ℂ (by omega) P.isPure P.isPure₂ hW
  have ha' : algebraMap (Kd d) ℂ a ≠ 0 := (map_ne_zero _).mpr ha
  have hb' : algebraMap (Kd d) ℂ b ≠ 0 := (map_ne_zero _).mpr hb
  have hwC : bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂) =
      algebraMap (Kd d) ℂ a • bcS (Kd d) ℂ n P.u₁ + algebraMap (Kd d) ℂ b • bcS (Kd d) ℂ n P.u₂ := by
    rw [map_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]
  have hann : ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) = ⊥ := by
    rw [hwC]
    exact s22a_ann_combo_eq_bot (by omega) p₁ p₂ hW' ha' hb'
  have hw0 : bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂) ≠ 0 := by
    intro h0
    have : ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) = ⊤ := by
      rw [h0]
      ext v
      simp only [Submodule.mem_top, iff_true]
      exact s22a_mem_ann.mpr (map_zero _)
    rw [hann] at this
    have hV : Module.finrank ℂ (⊥ : Submodule ℂ (V ℂ n)) = Module.finrank ℂ (V ℂ n) := by
      rw [this, finrank_top]
    rw [finrank_bot, s22a_finrank_V] at hV
    omega
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw
  have hnotpure : ¬ IsEvenPureSpinor ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) := by
    intro hp
    have := hp.2.2
    rw [hann, finrank_bot] at this
    omega
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hαβ
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hαβ
      exact hw0 hαβ.symm
    exact hnotpure (hαβ ▸ s22a_isEvenPureSpinor_smul hy hβ0)
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hαβ
    exact hnotpure (hαβ ▸ s22a_isEvenPureSpinor_smul hx hα)
  have hinf : ann ℂ n x ⊓ ann ℂ n y = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvx, hvy⟩
    have : v ∈ ann ℂ n (bcS (Kd d) ℂ n (a • P.u₁ + b • P.u₂)) := by
      rw [← hαβ, s22a_mem_ann, map_add, map_smul, map_smul, s22a_mem_ann.mp hvx,
        s22a_mem_ann.mp hvy, smul_zero, smul_zero, add_zero]
    rw [hann] at this
    exact this
  ext s
  rw [← s22a_fix_iff hn hx hy hinf hα hβ, hαβ, hwC, s22a_fix_iff hn p₁ p₂ hW' ha' hb']

end KSecant

end WeilClasses
