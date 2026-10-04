module

public import WeilClasses.Secant.Defs
public import WeilClasses.Orlov.Sec6_1
public import WeilClasses.Orlov.Sec6_3
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.PureSpinor.Lemma2_2_7
public import WeilClasses.Hermitian.ComplexStructures

/-!
# §6.4: Hodge–Weil classes on `X × X̂` from tensor squares of even pure spinors

Statements of the paper's §6.4 (TeX lines 2856–2985), for a `K`-secant `P` satisfying
Assumption 2.4.1, with `ℓ̃ᵢ = K uᵢ` (`u₂ = σ(u₁)`) and `Wᵢ = ker m_{uᵢ}`.

## Definitions

* `WeilClasses.HasWeight F n U k`: the subspace `U ⊆ ⋀• V_F` has *weight* `k`: `k` is the maximal
  integer with `U ⊆ F_k = ⊕_{i ≥ k} ⋀^i V` (`extFiltGE`, (6.1.5)), i.e. `U ⊆ F_k` and `U ⊄ F_{k+1}`.
  (The paper's `k(U)`; for a reducible `U` all of whose irreducible subrepresentations have the same
  weight `k₀`, the paper sets `k(U) = k₀`; for the representations below this is the same `k`, see
  `proposition6_4_1_1`.) The projection `Û` is `U.map (projDeg F n k)`.
* `WeilClasses.bcSS n d : S_ℚ ⊗_ℚ S_ℚ → S_K ⊗_K S_K`, the base change of `H*(X × X)`.
* `WeilClasses.KSecant.HWP`: the rational plane `HW_P ⊆ S⁺_ℚ ⊗ S⁺_ℚ` whose base change is
  `HW_{P_K} = ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}`. Writing `u₁ = p₁ + √-d p₂` with `p₁ = Re(u₁)`, `p₂ = Im(u₁)/√d`
  rational (`reS`, `imS`), `u₁ ⊗ u₁ = (p₁ ⊗ p₁ - d p₂ ⊗ p₂) + √-d (p₁ ⊗ p₂ + p₂ ⊗ p₁)` and
  `u₂ ⊗ u₂` is its conjugate, so `HW_P = span_ℚ{p₁ ⊗ p₁ - d p₂ ⊗ p₂, p₁ ⊗ p₂ + p₂ ⊗ p₁}` (this does
  not depend on the choice of `u₁` in `ℓ̃₁`); `KSecant.span_bcSS_HWP` is the defining property.

## Statements

* The decomposition of `P ⊗ P` (§6.4, first paragraph): trivial for `Spin(V_ℚ)_P`
  (`KSecant.map_m_tmul_of_mem_Pℚ`), and the characters `det₁`, `det₂`, `1`, `1` of
  `Spin(V_K)_{ℓ₁,ℓ₂}` on `ℓ̃₁^{⊗2}`, `ℓ̃₂^{⊗2}`, `ℓ̃₁ ⊗ ℓ̃₂`, `ℓ̃₂ ⊗ ℓ̃₁`
  (`KSecant.map_m_u₁_tmul_u₁`, `…_u₂_tmul_u₂`, `…_u₁_tmul_u₂`), `det₁` non-trivial and `≠ det₂`
  (`KSecant.exists_det₁_ne`).
* The weight discussion (`hasWeight_inf_eq_bot_of_irreducible`).
* **Proposition 6.4.1(1)** (`proposition6_4_1_1`, and for each line `proposition6_4_1_1_line₁`,
  `…_line₂`: `φ̂'(ℓ̃ᵢ²) = ⋀^{2n} Wᵢ`).
* **Proposition 6.4.1(2)** (`proposition6_4_1_2_even`, `proposition6_4_1_2_odd`), with the
  claims of the proof: invariance of the weight under `ρ'` (`HasWeight.map_rhoPrime`), the weights of
  `φ'(1 ⊗ [pt] ∓ [pt] ⊗ 1)` (`phiPrime_one_pt_hasWeight`), and `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` maps `F^k` into
  `F_{4n-k}` (`PiMap_mem_extFiltGE`).

All explicit claims were checked numerically (exact arithmetic in `ℚ(√-d)`) for `P = P_Θ`,
`Θ = ThetaStd`, `n = 1, 2, 3`, `d = 1, 2, 3`: `φ'(uᵢ ⊗ uᵢ)` has lowest degree `2n` with degree-`2n`
part exactly `⋀_i (f_i ∓ √-d θ(f_i))`, and the weights of `φ'(u₁ ⊗ u₂ ∓ u₂ ⊗ u₁)` are as stated.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Weights -/

section Weight

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- **The weight** (§6.4): `U ⊆ H*(X × X̂, F)` has weight `k` if `k` is the maximal integer with
`U ⊆ F_k H*(X × X̂, F) = ⊕_{i ≥ k} H^i` ((6.1.5)): `U ⊆ F_k` and `U ⊄ F_{k+1}`. -/
def HasWeight (U : Submodule F (ExtV F n)) (k : ℕ) : Prop :=
  U ≤ extFiltGE F n k ∧ ¬ U ≤ extFiltGE F n (k + 1)

/-- (§6.4, TeX line 2867) "Both [`ρ` and `ρ'`] factor through the image `SO⁺(V)` of `Spin(V)`":
`ρ'_g` depends only on `ρ(g)` (`ρ` on `⋀•V` is `⋀ρ(g)` by definition). -/
theorem rhoPrime_factors (g g' : Spin F n) (h : rho F n g = rho F n g') :
    rhoPrime F n g = rhoPrime F n g' := by
  sorry

/-- (§6.4, TeX lines 2891–2895) Let `U` be an irreducible representation of a subgroup
`G ⊆ Spin(V_F)` acting by `ρ'`, of weight `k`. Then `U ∩ F_{k+1} = 0` (a proper subrepresentation of
`U`), so `U` projects injectively and `G`-equivariantly (for the `ρ`-action) into `H^k`. -/
theorem hasWeight_inf_eq_bot_of_irreducible (G : Subgroup (Spin F n)) (U : Submodule F (ExtV F n))
    (hU : ∀ g ∈ G, ∀ x ∈ U, rhoPrime F n g x ∈ U)
    (hirr : ∀ U' : Submodule F (ExtV F n), U' ≤ U → (∀ g ∈ G, ∀ x ∈ U', rhoPrime F n g x ∈ U') →
      U' = ⊥ ∨ U' = U)
    (k : ℕ) (hk : HasWeight F n U k) :
    U ⊓ extFiltGE F n (k + 1) = ⊥ ∧ Set.InjOn (projDeg F n k) U ∧
      ∀ g ∈ G, ∀ x ∈ U, projDeg F n k (rhoPrime F n g x) = rhoExt F n g (projDeg F n k x) := by
  sorry

/-- (Proof of Proposition 6.4.1(2), TeX line 2969) "The weight is invariant under the
`Spin(V_K)`-action": if `U` has weight `k`, so has `ρ'_g(U)`. -/
theorem HasWeight.map_rhoPrime {U : Submodule F (ExtV F n)} {k : ℕ} (hk : HasWeight F n U k)
    (g : Spin F n) : HasWeight F n (U.map (rhoPrime F n g)) k := by
  sorry

/-- (Proof of Proposition 6.4.1(2), TeX lines 2975–2976, by Lemma 6.3.2) `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` sends
`F^k(⋀• V) = ⊕_{i ≤ k} ⋀^i V` into `F_{4n-k}(⋀• V) = ⊕_{i ≥ 4n-k} ⋀^i V` (it maps `⋀^i V` to
`⋀^{4n-i} V`). -/
theorem PiMap_mem_extFiltGE (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltLE F n k) :
    PiMap F n x ∈ extFiltGE F n (4 * n - k) := by
  sorry

/-- (Proof of Proposition 6.4.1(2), TeX lines 2968–2977, from Lemma 2.3.2, Lemma 6.1.1 and
Lemma 6.3.2) For the pure spinors `1` and `[pt_X]` (with `ker m_1 = H¹(X̂)`, `ker m_{[pt]} = H¹(X)`
complementary): `φ'([pt] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt])` has weight `2` and `φ'([pt] ⊗ 1 + (-1)ⁿ 1 ⊗ [pt])`
has weight `0`. (`1 ≤ n`, implied by the standing assumption `n ≥ 2`.) -/
theorem phiPrime_one_pt_hasWeight (hn : 1 ≤ n) :
    HasWeight F n (Submodule.span F
        {phiPrime F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n))}) 2 ∧
      HasWeight F n (Submodule.span F
        {phiPrime F n (pt F n ⊗ₜ[F] (1 : S F n) + (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n))}) 0 := by
  sorry

end Weight

/-! ## `HW_P` and the decomposition of `P ⊗ P` -/

section HW

variable (n : ℕ) (d : ℚ)

/-- The base change `H*(X × X, ℚ) = S_ℚ ⊗_ℚ S_ℚ → S_K ⊗_K S_K = H*(X × X, K)`. -/
noncomputable def bcSS : S ℚ n ⊗[ℚ] S ℚ n →ₗ[ℚ] S (Kd d) n ⊗[Kd d] S (Kd d) n :=
  TensorProduct.lift
    (((TensorProduct.mk (Kd d) (S (Kd d) n) (S (Kd d) n)).restrictScalars₁₂ ℚ ℚ).compl₁₂
      (bcS ℚ (Kd d) n).toLinearMap (bcS ℚ (Kd d) n).toLinearMap)

theorem bcSS_tmul (x y : S ℚ n) :
    bcSS n d (x ⊗ₜ[ℚ] y) = bcS ℚ (Kd d) n x ⊗ₜ[Kd d] bcS ℚ (Kd d) n y := by
  simp [bcSS]

namespace KSecant

variable {n d} (P : KSecant n d)

/-- **`HW_P`** (§6.4): the rational plane of `S⁺_ℚ ⊗ S⁺_ℚ` corresponding to
`HW_{P_K} = ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}`: with `p₁ = Re(u₁)`, `p₂ = Im(u₁)/√d`,
`HW_P = span_ℚ{p₁ ⊗ p₁ - d p₂ ⊗ p₂, p₁ ⊗ p₂ + p₂ ⊗ p₁}` (the real and imaginary parts of `u₁ ⊗ u₁`;
see the module docstring). -/
noncomputable def HWP : Submodule ℚ (S ℚ n ⊗[ℚ] S ℚ n) :=
  Submodule.span ℚ
    {reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ - d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁),
      reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁}

/-- "The `2`-dimensional subspace `HW_{P_K} := ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}` of `S⁺_K ⊗_K S⁺_K` is defined over
`ℚ`" (§6.4): it is the `K`-span of the base change of `HW_P`. -/
theorem span_bcSS_HWP (hd : 0 < d) :
    Submodule.span (Kd d) (bcSS n d '' P.HWP) =
      Submodule.span (Kd d) {P.u₁ ⊗ₜ[Kd d] P.u₁, P.u₂ ⊗ₜ[Kd d] P.u₂} := by
  sorry

/-- `HW_P` is `2`-dimensional (§6.4). -/
theorem finrank_HWP (hd : 0 < d) : Module.finrank ℚ P.HWP = 2 := by
  sorry

/-- (§6.4, TeX lines 2862–2863) "The subspace `P ⊗ P` of `S⁺_ℚ ⊗ S⁺_ℚ` is a trivial
`Spin(V_ℚ)_P`-subrepresentation" (for the action `m ⊗ m`, the one intertwined with `ρ'` by `φ'`). -/
theorem map_m_tmul_of_mem_Pℚ (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) (p q : S ℚ n) (hp : p ∈ P.Pℚ)
    (hq : q ∈ P.Pℚ) :
    TensorProduct.map (m ℚ n (g : C ℚ n)) (m ℚ n (g : C ℚ n)) (p ⊗ₜ[ℚ] q) = p ⊗ₜ[ℚ] q := by
  sorry

/-- (§6.4, TeX lines 2863–2865; §2.2 "`ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁`") `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `ℓ̃₁^{⊗2}` by the
character `det₁`. -/
theorem map_m_u₁_tmul_u₁ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₁ ⊗ₜ[Kd d] P.u₁) =
      P.det₁ g • (P.u₁ ⊗ₜ[Kd d] P.u₁) := by
  sorry

/-- (§6.4) `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `ℓ̃₂^{⊗2}` by the character `det₂`. -/
theorem map_m_u₂_tmul_u₂ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₂ ⊗ₜ[Kd d] P.u₂) =
      P.det₂ g • (P.u₂ ⊗ₜ[Kd d] P.u₂) := by
  sorry

/-- (§6.4, TeX lines 2864–2865) `ℓ̃₁ ⊗ ℓ̃₂` and `ℓ̃₂ ⊗ ℓ̃₁` (hence `ℓ̃₁ ∧ ℓ̃₂ ⊆ ⋀² S⁺` and
`ℓ̃₁ ℓ̃₂ ⊆ Sym² S⁺`) are trivial characters of `Spin(V_K)_{ℓ₁,ℓ₂}` (`χ₁ χ₂ = 1`, since the Mukai
pairing is invariant and `(u₁, u₂)_S ≠ 0` for non-isotropic `P`). -/
theorem map_m_u₁_tmul_u₂ (hd : 0 < d) (hP : ¬ P.IsIsotropic) (g : P.spinL₁L₂) :
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₁ ⊗ₜ[Kd d] P.u₂) =
      P.u₁ ⊗ₜ[Kd d] P.u₂ ∧
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₂ ⊗ₜ[Kd d] P.u₁) =
      P.u₂ ⊗ₜ[Kd d] P.u₁ := by
  sorry

/-- (§6.4, TeX line 2864) "the two non-trivial distinct ... characters `ℓ̃₁^{⊗2}`, `ℓ̃₂^{⊗2}`":
`det₁` is non-trivial on `Spin(V_K)_{ℓ₁,ℓ₂}` and differs from `det₂`. -/
theorem exists_det₁_ne (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    (∃ g : P.spinL₁L₂, P.det₁ g ≠ 1) ∧ ∃ g : P.spinL₁L₂, P.det₁ g ≠ P.det₂ g := by
  sorry

end KSecant

end HW

/-! ## Proposition 6.4.1 -/

section Prop641

variable {n : ℕ} {d : ℚ}

/-- **Proposition 6.4.1(1)**, for each line (proof, TeX lines 2930–2931): `φ'(ℓ̃₁ ⊗ ℓ̃₁)` lies in
`F_{2n} = ⊕_{k ≥ 2n} H^k(X × X̂, K)` and its projection to `H^{2n}(X × X̂, K)` is `⋀^{2n} W₁`
("`\widehat{φ'(ℓ̃ᵢ²)}` is equal to `⋀^{2n} Wᵢ`"); `φ' = φ ∘ (id ⊗ τ)` (`phiPrime`). In particular
`φ'(ℓ̃₁²)` has weight `2n` (`⋀^{2n} W₁ ≠ 0`). Setting of §6.4: Assumption 2.4.1. -/
theorem proposition6_4_1_1_line₁ (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁) ∈ extFiltGE (Kd d) n (2 * n) ∧
      (Submodule.span (Kd d) {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁)}).map
          (projDeg (Kd d) n (2 * n)) = topWedge P.W₁ (2 * n) := by
  sorry

/-- **Proposition 6.4.1(1)**, for the line `ℓ̃₂`: `φ'(ℓ̃₂ ⊗ ℓ̃₂) ∈ F_{2n}` and its projection to
`H^{2n}` is `⋀^{2n} W₂`. -/
theorem proposition6_4_1_1_line₂ (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂) ∈ extFiltGE (Kd d) n (2 * n) ∧
      (Submodule.span (Kd d) {phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)}).map
          (projDeg (Kd d) n (2 * n)) = topWedge P.W₂ (2 * n) := by
  sorry

/-- **Proposition 6.4.1(1)** (`prop-the-orlov-image-of-HW-P-projects-into-the-3-dimensional-space-of-HW-classes`).
The isomorphism `φ'` maps `HW_P = ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}` into a weight `2n` `Spin(V)_P`-subrepresentation
of `H*(X × X̂, ℚ)` via `ρ'`, and the projection `ĤW_P` of `φ'(HW_P)` is the rational subspace of
`H^{2n}(X × X̂, ℚ)` corresponding to `⋀^{2n} W₁ ⊕ ⋀^{2n} W₂` (`KSecant.hwPlane`).

Stated: `φ'(HW_P)` is stable under `ρ'_g`, `g ∈ Spin(V)_P` (the integral group); it has weight `2n`
(`HasWeight`), and every non-zero element has non-zero degree-`2n` part (`φ'(HW_P) ∩ F_{2n+1} = 0`:
"each irreducible subrepresentation has weight `2n`", so that `φ'(HW_P) → ĤW_P` is an isomorphism);
its projection to `⋀^{2n} V_ℚ` is `hwPlane`. Setting of §6.4: Assumption 2.4.1. -/
theorem proposition6_4_1_1 (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    (∀ g ∈ P.spinPZ, ∀ x ∈ P.HWP.map (phiPrime ℚ n),
        rhoPrime ℚ n g x ∈ P.HWP.map (phiPrime ℚ n)) ∧
      HasWeight ℚ n (P.HWP.map (phiPrime ℚ n)) (2 * n) ∧
      P.HWP.map (phiPrime ℚ n) ⊓ extFiltGE ℚ n (2 * n + 1) = ⊥ ∧
      (P.HWP.map (phiPrime ℚ n)).map (projDeg ℚ n (2 * n)) = P.hwPlane := by
  sorry

/-- **Proposition 6.4.1(2)** (`prop-the-orlov-image-of-HW-P-projects-into-the-3-dimensional-space-of-HW-classes`),
`n` even: the weight of `φ'(ℓ₁ ∧ ℓ₂)` is `2` and the weight of `φ'(ℓ₁ · ℓ₂)` is `0`.

Here `ℓ₁ ∧ ℓ₂` is spanned by `u₁ ⊗ u₂ - u₂ ⊗ u₁ ∈ ⋀² S⁺_K` and `ℓ₁ · ℓ₂` by
`u₁ ⊗ u₂ + u₂ ⊗ u₁ ∈ Sym² S⁺_K` (both lines are defined over `ℚ` and fixed by `Spin(V)_P`). Setting
of §6.4: Assumption 2.4.1. -/
theorem proposition6_4_1_2_even (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (hn : Even n) :
    HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ - P.u₂ ⊗ₜ[Kd d] P.u₁)}) 2 ∧
      HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ + P.u₂ ⊗ₜ[Kd d] P.u₁)}) 0 := by
  sorry

/-- **Proposition 6.4.1(2)** (`prop-the-orlov-image-of-HW-P-projects-into-the-3-dimensional-space-of-HW-classes`),
`n` odd: the weight of `φ'(ℓ₁ · ℓ₂)` is `2` and the weight of `φ'(ℓ₁ ∧ ℓ₂)` is `0`. -/
theorem proposition6_4_1_2_odd (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (hn : Odd n) :
    HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ + P.u₂ ⊗ₜ[Kd d] P.u₁)}) 2 ∧
      HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ - P.u₂ ⊗ₜ[Kd d] P.u₁)}) 0 := by
  sorry

end Prop641

end WeilClasses
