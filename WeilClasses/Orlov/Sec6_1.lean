module

public import WeilClasses.Orlov.Defs
public import WeilClasses.Orlov.Basis
public import WeilClasses.Spinor.Integral
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.Orlov.Sec6_3
public import WeilClasses.External.Orlov.Sec6_1
public import WeilClasses.External.Huybrechts.Sec6_1

/-!
# §6.1: `Spin(V)`-equivariance properties of Orlov's equivalence

Statements of the paper's §6.1 (TeX lines 2139–2348), in the model where Orlov's cohomological
isomorphism `φ` (6.1.3) is the composite `(id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*` (`phiOrlov`, see
`WeilClasses.Orlov.Defs`):

* `φ` is an isomorphism (`phiOrlov_bijective`), integrally (`phiOrlov_image_SZZ`); (6.1.4) as
  printed (`rhoPrime_eq_phiOrlov_conj`);
* Lemma 6.1.1 (`lemma6_1_1`) is stated in `WeilClasses.Orlov.Sec6_3`, next to Lemma 6.3.1, as the
  paper proves it in §6.3;
* `ρ'_g` preserves the decreasing filtration (6.1.5) with associated graded action `ρ`
  (`rhoPrime_mem_extFiltGE`, `rhoPrime_projDeg`);
* (6.1.8) (`equation6_1_8`, `equation6_1_8_integral`; [Orlov, Th. 2.10]) and the cocycle identity
  (6.1.9) (`equation6_1_9`; [Huybrechts, Ex. 9.41]);
* Proposition 6.1.2 = (6.1.10) (`proposition6_1_2`). The integrality of `½[c₁(𝒫) - ρ_g(c₁(𝒫))]`
  remarked after it (TeX lines 2277–2279; `c1P_pairing_mod_two`, `half_c1P_sub_rho_mem_ExtZ`) is
  stated in `WeilClasses.Orlov.Sec6_3`, upstream of the cited [Orlov, Th. 2.10], whose proof in the
  model uses it for the integrality of `c₁(N_g)`.

**Reading (coefficients).** The paper states Proposition 6.1.2, (6.1.8) and (6.1.9) for `g` in the
integral group `Spin(V)`. It applies Proposition 6.1.2 also to `K`-points (Lemma 6.2.6 uses
`Spin(V_K)_{ℓ₁,ℓ₂}`, TeX lines 2648–2654), and (6.1.8), (6.1.9) only to integral `g` (TeX lines
2451–2456 and 2566–2570). The identities are algebraic, and we state them for `g : Spin F n` over
every field `F` of characteristic `0`, the integrality claim separately for the integral group
`SpinZ n` (`equation6_1_8_integral`).

**Left out (sheaf-theoretic).** The derived equivalences (6.1.1), (6.1.2) themselves, the
intertwining of the actions of `Aut(Dᵇ(X))` ([Huybrechts, Cor. 9.37]), the identification of `φ`
with the Chern character of Orlov's kernel (GRR), the existence of the line bundles `N_g` (only
their classes `c₁(N_g) ∈ H²(X × X̂)` appear), the identity `φ_{𝒢^∨[n]} = τ φ_𝒢 τ`, the group
cohomology interpretation of (6.1.9), and the reduction of Proposition 6.1.2 to abelian surfaces
(its proof; replaced by an algebraic proof, see `notes/design.md`).

**Proofs.** Lemma 6.1.1 is the paper's (Lemma 6.3.1 and `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`; stated and proved
in `WeilClasses.Orlov.Sec6_3`). Proposition 6.1.2 is proved by the authorized algebraic argument
(`s61_proposition6_1_2`, see the docstring of `proposition6_1_2`): the computation
`sd_rhoPrime_of_lemma6_1_1` (`WeilClasses.Orlov.Sec6_3`) applied to Lemma 6.1.1; its two inputs
are the `Spin(V)`-equivariance of `Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = ±PD` (`s61_PiMap_rhoExt`, from
Lemma 6.3.2) and the operator form of Remark 2.3.1 (`PiMap_changeB0bar`,
`WeilClasses.Chevalley.Sec2_3`). As in the paper, (6.1.8) is [Orlov, Th. 2.10]
(`orlov_theorem2_10`; its integral clause gives `equation6_1_8_integral`) and (6.1.9) is
[Huybrechts, Ex. 9.41] (`huybrechts_ex9_41`); these cited results are proved in
`WeilClasses.External` (in the model, from the computation behind Proposition 6.1.2, which does not
use them, with the integrality of `½[c₁(𝒫) - ρ_g(c₁(𝒫))]`, resp. from `ρ'` being a representation).
The filtration claims are proved from Proposition 6.1.2, the paper's own justification of them in
§6.4 (TeX line 2873: "The induced action of `ρ'(g)` on the graded summands agrees with that of
`ρ(g)`, by Proposition 6.1.2"); in §6.1 the paper cites for them [GLO, Prop. 4.3.7, Cor. 4.3.8]
(`glo_prop4_3_7`, proved in `WeilClasses.External`) "and more directly" Lemma 6.1.1, an argument the
visible paper does not spell out.
The helpers of this section (prefix `s61_`) not listed below are in `WeilClasses.Orlov.Basis` and
`WeilClasses.Orlov.Sec6_3`.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P10) -/

section S61Int

variable (n : ℕ)

theorem s61_neg_one_pow_mem_int (k : ℕ) : (-1 : ℚ) ^ k ∈ (Int.castRingHom ℚ).range :=
  ⟨(-1) ^ k, by simp⟩

theorem s61_epsSign_mem_int (K L : Finset (Fin (2 * n))) :
    epsSign ℚ n K L ∈ (Int.castRingHom ℚ).range := by
  rw [s61_epsSign_eq]
  split_ifs
  · exact s61_neg_one_pow_mem_int _
  · exact zero_mem _

theorem s61_smul_mem_ExtZ {q : ℚ} (hq : q ∈ (Int.castRingHom ℚ).range) {x : ExtV ℚ n}
    (hx : x ∈ ExtZ n) : q • x ∈ ExtZ n := by
  obtain ⟨z, rfl⟩ := hq
  rw [eq_intCast, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem s61_smul_mem_SZZ {q : ℚ} (hq : q ∈ (Int.castRingHom ℚ).range)
    {x : S ℚ n ⊗[ℚ] S ℚ n} (hx : x ∈ SZZ n) : q • x ∈ SZZ n := by
  obtain ⟨z, rfl⟩ := hq
  rw [eq_intCast, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem s61_basisExt_mem_ExtZ (M : Finset (Fin (2 * n + 2 * n))) : basisExt ℚ n M ∈ ExtZ n := by
  intro K
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s61_basisS_mem_SZ (K : Finset (Fin (2 * n))) : basisS ℚ n K ∈ SZ n := by
  intro L
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem s61_tmul_mem_SZZ (K L : Finset (Fin (2 * n))) :
    basisS ℚ n K ⊗ₜ[ℚ] basisS ℚ n L ∈ SZZ n :=
  AddSubgroup.subset_closure ⟨_, s61_basisS_mem_SZ n K, _, s61_basisS_mem_SZ n L, rfl⟩

theorem s61_pullX_mul_pullXHat_mem_ExtZ (I J : Finset (Fin (2 * n))) :
    pullX ℚ n (basisS ℚ n I) * pullXHat ℚ n (basisSHat ℚ n J) ∈ ExtZ n := by
  rw [s61_pullX_basisS, s61_pullXHat_basisSHat, basisExt, s61_basis_mul_basis]
  split_ifs
  · exact s61_smul_mem_ExtZ n (s61_neg_one_pow_mem_int _) (s61_basisExt_mem_ExtZ n _)
  · exact zero_mem _

theorem s61_phiOrlov_basis_mem_ExtZ (K L : Finset (Fin (2 * n))) :
    phiOrlov ℚ n (basisS ℚ n K ⊗ₜ[ℚ] basisS ℚ n L) ∈ ExtZ n := by
  rw [phiOrlov, LinearMap.comp_apply, LinearMap.comp_apply, muStar_basis, map_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun I _ => ?_
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis,
    TensorProduct.tmul_smul, map_smul, LinearEquiv.coe_coe, kunnethXHat_tmul]
  exact s61_smul_mem_ExtZ n (Subring.mul_mem _ (s61_epsSign_mem_int n _ _)
    (s61_epsSign_mem_int n _ _)) (s61_smul_mem_ExtZ n (Subring.mul_mem _
      (s61_neg_one_pow_mem_int _) (s61_epsSign_mem_int n _ _))
        (s61_pullX_mul_pullXHat_mem_ExtZ n _ _))

theorem s61_phiOrlov_tmul_mem_ExtZ {s t : S ℚ n} (hs : s ∈ SZ n) (ht : t ∈ SZ n) :
    phiOrlov ℚ n (s ⊗ₜ[ℚ] t) ∈ ExtZ n := by
  rw [← (basisS ℚ n).sum_repr s, ← (basisS ℚ n).sum_repr t, TensorProduct.sum_tmul, map_sum]
  refine AddSubgroup.sum_mem _ fun K _ => ?_
  rw [TensorProduct.tmul_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun L _ => ?_
  rw [TensorProduct.smul_tmul_smul, map_smul]
  obtain ⟨z₁, hz₁⟩ := hs K
  obtain ⟨z₂, hz₂⟩ := ht L
  rw [hz₁, hz₂]
  exact s61_smul_mem_ExtZ n ⟨z₁ * z₂, by simp⟩ (s61_phiOrlov_basis_mem_ExtZ n K L)

theorem s61_phiOrlovInv_basisExt_mem_SZZ (M : Finset (Fin (2 * n + 2 * n))) :
    phiOrlovInv ℚ n (basisExt ℚ n M) ∈ SZZ n := by
  obtain ⟨L, K, -, hM⟩ := s61_basisExt_eq_beta ℚ n M
  have hcomm : pullXHat ℚ n (basisSHat ℚ n L) * pullX ℚ n (basisS ℚ n K) =
      (-1 : ℚ) ^ (L.card * K.card) • (pullX ℚ n (basisS ℚ n K) * pullXHat ℚ n (basisSHat ℚ n L)) :=
    s61_mul_comm_of_mem (s61_map_mem _ (s61_basis_mem _ L)) (s61_map_mem _ (s61_basis_mem _ K))
  rw [hM, hcomm, ← kunnethXHat_tmul, map_smul, phiOrlovInv, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, s61_phiP_basisSHat, TensorProduct.tmul_smul,
    map_smul, s61_muStarInv_basis]
  refine s61_smul_mem_SZZ n (s61_neg_one_pow_mem_int _) (s61_smul_mem_SZZ n ?_ ?_)
  · exact Subring.mul_mem _ (Subring.mul_mem _ (s61_neg_one_pow_mem_int _)
      (s61_neg_one_pow_mem_int _)) (s61_neg_one_pow_mem_int _)
  · refine AddSubgroup.sum_mem _ fun I _ => s61_smul_mem_SZZ n ?_ (s61_tmul_mem_SZZ n _ _)
    exact Subring.mul_mem _ (s61_neg_one_pow_mem_int _)
      (Subring.mul_mem _ (s61_epsSign_mem_int n _ _) (s61_epsSign_mem_int n _ _))

end S61Int

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- (6.1.3) Orlov's cohomological map `φ : S ⊗ S → ⋀•V` is an isomorphism. -/
theorem phiOrlov_bijective : Function.Bijective (phiOrlov F n) :=
  Function.bijective_iff_has_inverse.mpr ⟨phiOrlovInv F n,
    fun y => LinearMap.congr_fun (phiOrlovInv_comp_phiOrlov F n) y,
    fun x => LinearMap.congr_fun (phiOrlov_comp_phiOrlovInv F n) x⟩

/-- (6.1.3) over the integers: `φ` maps `H*(X × X, ℤ) = S_ℤ ⊗ S_ℤ` onto `H*(X × X̂, ℤ) = ⋀•V_ℤ` (the
paper's `φ` is the correspondence isomorphism of an equivalence of derived categories, between
integral cohomology groups; checked numerically for `n = 1, 2`). -/
theorem phiOrlov_image_SZZ (n : ℕ) :
    phiOrlov ℚ n '' (SZZ n : Set (S ℚ n ⊗[ℚ] S ℚ n)) = (ExtZ n : Set (ExtV ℚ n)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, hs, t, ht, rfl⟩ := hy
      exact s61_phiOrlov_tmul_mem_ExtZ n hs ht
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro hx
    refine ⟨phiOrlovInv ℚ n x, ?_, LinearMap.congr_fun (phiOrlov_comp_phiOrlovInv ℚ n) x⟩
    have hx' : x ∈ ExtZ n := hx
    rw [← (basisExt ℚ n).sum_repr x, map_sum]
    refine AddSubgroup.sum_mem _ fun M _ => ?_
    obtain ⟨z, hz⟩ := hx' M
    rw [map_smul, hz]
    exact s61_smul_mem_SZZ n ⟨z, by simp⟩ (s61_phiOrlovInv_basisExt_mem_SZZ n M)

/-- **(6.1.4)** (`rho-prime-g`) as printed: `ρ'_g = φ (m_g × m†_g) φ⁻¹`. -/
theorem rhoPrime_eq_phiOrlov_conj (g : Spin F n) :
    rhoPrime F n g =
      phiOrlov F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (mDagger F n (g : C F n)) ∘ₗ
        phiOrlovInv F n := by
  have h : tauTensor F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) ∘ₗ
      tauTensor F n = TensorProduct.map (m F n (g : C F n)) (mDagger F n (g : C F n)) := by
    refine TensorProduct.ext' fun u v => ?_
    simp [tauTensor, mDagger]
  rw [rhoPrime, phiPrime, phiPrimeInv, ← h]
  simp only [LinearMap.comp_assoc]

/-- The proof of Proposition 6.1.2 (`proposition6_1_2`, stated below), by the authorized algebraic
argument (see its docstring): `φ' = φ ∘ (id ⊗ τ) = Π ∘ E_{B̄₀} ∘ φ̃_sym` (Lemma 6.1.1, Lemma 6.3.1,
Remark 2.3.1); `φ̃_sym` is `Spin(V)`-equivariant (Trautman), `Π E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` (operator
form of Remark 2.3.1) and `Π = ±PD` commutes with `⋀ρ_g` (Lemma 6.3.2, `ρ_g ∈ SO(V)`). The
computation is `sd_rhoPrime_of_lemma6_1_1` (`WeilClasses.Orlov.Sec6_3`), applied to Lemma 6.1.1. -/
theorem s61_proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x :=
  sd_rhoPrime_of_lemma6_1_1 F n (lemma6_1_1 F n) g x

/-- (§6.1, TeX lines 2224–2231; again §6.4, TeX lines 2869–2873) `ρ'_g` preserves the decreasing
filtration `F_k(⋀•V) = ⊕_{i ≥ k} ⋀^i V` (6.1.5).
Proof: by Proposition 6.1.2 (`s61_proposition6_1_2`), `ρ'_g = exp(β) ∪ ρ_g` with `β ∈ ⋀²V`. This is
the paper's own justification of the claim in §6.4 (TeX line 2873: "The induced action of `ρ'(g)` on
the graded summands agrees with that of `ρ(g)`, by Proposition 6.1.2"). In §6.1 the paper cites
[GLO, Prop. 4.3.7, Cor. 4.3.8] (`glo_prop4_3_7`, proved in `WeilClasses.External`) "and more
directly" Lemma 6.1.1, whose argument the visible paper does not spell out. -/
theorem rhoPrime_mem_extFiltGE (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    rhoPrime F n g x ∈ extFiltGE F n k := by
  have h1 := s61_exp_sub_one_mem F n (s61_beta_mem F n g)
  have h2 := s61_rhoExt_mem_extFiltGE F n g hx
  rw [s61_proposition6_1_2, ← sub_add_cancel (IsNilpotent.exp _) 1, add_mul, one_mul]
  exact add_mem (s61_extFiltGE_mono F n (by omega) (s61_mul_mem_extFiltGE F n h1 h2)) h2

/-- (§6.1, TeX lines 2224–2231; again §6.4, TeX lines 2869–2873) The graded action induced by
`ρ'_g` on `F_k / F_{k+1} = ⋀^k V` is `⋀^k ρ_g`, induced from `ρ : Spin(V) → SO(V)`.
Proof: by Proposition 6.1.2 (`s61_proposition6_1_2`), `ρ'_g = exp(β) ∪ ρ_g` with `β ∈ ⋀²V`, and
`exp(β) - 1 ∈ F_2`; this is the paper's own justification in §6.4 (TeX line 2873, "by
Proposition 6.1.2"). In §6.1 the paper cites [GLO, Prop. 4.3.7, Cor. 4.3.8] (`glo_prop4_3_7`) "and
more directly" Lemma 6.1.1 (see `rhoPrime_mem_extFiltGE`). -/
theorem rhoPrime_projDeg (g : Spin F n) (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltGE F n k) :
    projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  have h1 := s61_exp_sub_one_mem F n (s61_beta_mem F n g)
  have h2 := s61_rhoExt_mem_extFiltGE F n g hx
  rw [s61_proposition6_1_2, ← sub_add_cancel (IsNilpotent.exp _) 1, add_mul, one_mul, map_add,
    s61_projDeg_eq_zero_of_mem_extFiltGE F n
      (s61_extFiltGE_mono F n (by omega) (s61_mul_mem_extFiltGE F n h1 h2)),
    zero_add, s61_projDeg_rhoExt]

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10], [Huybrechts, Prop. 9.39]) For every `g ∈ Spin(V)`
there is a (topological) line bundle `N_g` on `X × X̂` with `ρ'_g = ch(N_g) ∪ ρ_g`. In the model:
there is a class `c = c₁(N_g) ∈ H²(X × X̂) = ⋀²V` with `ρ'_g = exp(c) ∪ ρ_g`.
Reading: stated over every field; the paper uses integral `g`. The paper states (6.1.8) for `g` in
the integral group `Spin(V)` and uses it only for such `g` (TeX lines 2451–2456, `g ∈ Spin(V)_P`;
TeX lines 2566–2570, `g ∈ Γ ⊆ Spin(V)`); the identity is algebraic, and it is stated here for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`. The integral version (`c₁(N_g)`
integral for integral `g`, `N_g` being a line bundle) is `equation6_1_8_integral`.
Proof: [Orlov, Th. 2.10] (`orlov_theorem2_10`, the paper's citation). -/
theorem equation6_1_8 (g : Spin F n) :
    ∃ c ∈ ⋀[F]^2 (V F n), ∀ x : ExtV F n,
      rhoPrime F n g x = IsNilpotent.exp c * rhoExt F n g x :=
  (orlov_theorem2_10 F n).1 g

/-- **(6.1.9)** (`eq-1-cocycle-identity`; [Huybrechts, Ex. 9.41]) The cocycle identity
`c₁(N_{g₁g₂}) = c₁(N_{g₁}) + ρ_{g₁}(c₁(N_{g₂}))`, for all `g₁, g₂ ∈ Spin(V)`, where `c₁(N_g)` is
any class satisfying (6.1.8) for `g` (it is unique: `exp(c) = ρ'_g(1)`).
Reading: stated over every field; the paper uses integral `g`. The paper states (6.1.9) for
`g₁, g₂` in the integral group `Spin(V)` and uses it only for such elements (TeX lines 2566–2570,
the subgroup `Γ ⊆ Spin(V)`); the identity is algebraic, and it is stated here for
`g₁, g₂ ∈ Spin(V_F)` over every field `F` of characteristic `0`.
Proof: [Huybrechts, Ex. 9.41] (`huybrechts_ex9_41`, the paper's citation). -/
theorem equation6_1_9 (g₁ g₂ : Spin F n) (c₁ c₂ c₁₂ : ExtV F n)
    (hc₁ : c₁ ∈ ⋀[F]^2 (V F n)) (hc₂ : c₂ ∈ ⋀[F]^2 (V F n)) (hc₁₂ : c₁₂ ∈ ⋀[F]^2 (V F n))
    (h₁ : ∀ x, rhoPrime F n g₁ x = IsNilpotent.exp c₁ * rhoExt F n g₁ x)
    (h₂ : ∀ x, rhoPrime F n g₂ x = IsNilpotent.exp c₂ * rhoExt F n g₂ x)
    (h₁₂ : ∀ x, rhoPrime F n (g₁ * g₂) x = IsNilpotent.exp c₁₂ * rhoExt F n (g₁ * g₂) x) :
    c₁₂ = c₁ + rhoExt F n g₁ c₂ :=
  huybrechts_ex9_41 F n g₁ g₂ c₁ c₂ c₁₂ hc₁ hc₂ hc₁₂ h₁ h₂ h₁₂

/-- **Proposition 6.1.2**
(`prop-extension-class-of-decreasing-filtration-of-spin-V-representations`),
equation **(6.1.10)** (`eq-relating-rho-and-rho-prime`):
`ρ'_g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g`.
Reading: the paper states this for `g` in the integral group `Spin(V)` but applies it to
`K`-points (Lemma 6.2.6, `Spin(V_K)_{ℓ₁,ℓ₂}`); the identity is algebraic, and it is stated for
`g ∈ Spin(V_F)` over every field `F` of characteristic `0`. (Checked numerically for `n = 1, 2`
with the sign convention of `c1P`;
it fails for the opposite sign.)

Departure from the paper (authorized by the project owner; `notes/proof-plans.md`): the paper
reduces the statement to abelian surfaces (Lemma 6.2.5, via Orlov's Th. 2.10, Verbitsky's Zariski
density and Obata's Th. B), which needs sheaves and algebraic groups not available here. The proof
(`s61_proposition6_1_2`) is the algebraic argument through the symmetric Chevalley isomorphism of
Remark 2.3.1: by Lemma 6.1.1 and Lemma 6.3.1, `φ' = φ ∘ (id ⊗ τ) = Π ∘ ψ ∘ φ_Chev` with
`Π = φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}`, and `ψ = E_{B̄₀} ∘ ψ_sym` (`psi_eq_changeB0bar_comp_psiSym`). The symmetric
`φ̃_sym = ψ_sym ∘ φ_Chev` is `Spin(V)`-equivariant ([Trautman, Th. 1(i)],
`remark2_3_1_sym_equivariant`); `Π ∘ E_{B̄₀} = exp(½c₁(𝒫)) ∪ Π` (the operator form of Remark 2.3.1,
`PiMap_changeB0bar`, proved from `E_{B̄₀} = ∏ᵢ (1 + ½ ∂_{f_i} ∂_{e_i})` and
`Π ∘ ∂_{f_i} ∂_{e_i} = (e_i ∧ f_i) ∪ Π`); and `Π = ±PD` (Lemma 6.3.2) commutes with `⋀ρ_g` because
`ρ_g ∈ SO(V)` preserves the pairing and the volume form (`s61_PiMap_rhoExt`). Hence
`ρ'_g = exp(½c₁(𝒫)) ∪ ⋀ρ_g ∘ exp(-½c₁(𝒫)) ∪ = exp(½[c₁(𝒫) - ρ_g c₁(𝒫)]) ∪ ρ_g`. -/
theorem proposition6_1_2 (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g x =
      IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n))) * rhoExt F n g x :=
  s61_proposition6_1_2 F n g x

end Field

section Integral

variable (n : ℕ)

/-- **(6.1.8)** (`eq-N-g`; [Orlov, Th. 2.10]) for the integral group, as the paper uses it: for
`g ∈ Spin(V)` there is a line bundle `N_g` on `X × X̂` with `ρ'_g = ch(N_g) ∪ ρ_g`; in the model, a
class `c = c₁(N_g) ∈ H²(X × X̂, ℤ)` (integral, `N_g` being a line bundle) with
`ρ'_g = exp(c) ∪ ρ_g`.
Proof: [Orlov, Th. 2.10] (`orlov_theorem2_10`, its integral clause; the paper's citation). -/
theorem equation6_1_8_integral (g : Spin ℚ n) (hg : g ∈ SpinZ n) :
    ∃ c ∈ ⋀[ℚ]^2 (V ℚ n), c ∈ ExtZ n ∧ ∀ x : ExtV ℚ n,
      rhoPrime ℚ n g x = IsNilpotent.exp c * rhoExt ℚ n g x :=
  (orlov_theorem2_10 ℚ n).2 g hg

end Integral

end WeilClasses
