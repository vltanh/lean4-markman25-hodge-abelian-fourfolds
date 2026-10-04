module

public import WeilClasses.Secant.Defs
public import WeilClasses.Orlov.Sec6_1
public import WeilClasses.Orlov.Sec6_3
public import WeilClasses.Chevalley.Sec2_3
public import WeilClasses.PureSpinor.Lemma2_2_7
public import WeilClasses.Hermitian.ComplexStructures
public import WeilClasses.Orlov.Sec6_2
public import WeilClasses.External.Chevalley.Sec2_2

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

omit [CharZero F] in
/-- `x ∈ F_k = ⊕_{i ≥ k} ⋀^i V` iff the components of `x` of degree `< k` vanish. -/
theorem s62_mem_extFiltGE_iff (k : ℕ) (x : ExtV F n) :
    x ∈ extFiltGE F n k ↔ ∀ i < k, projDeg F n i x = 0 := by
  constructor
  · intro hx i hi
    have hle : extFiltGE F n k ≤ LinearMap.ker (projDeg F n i) := iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, s62_projDeg_ne F n hy (by omega)]
    exact hle hx
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : k ≤ i
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hik
        (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x i).2)
    · have h0 : ((DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x i : ⋀[F]^i (V F n)) :
          ExtV F n) = 0 := by
        rw [← GradedAlgebra.proj_apply]; exact hx i (by omega)
      rw [h0]; exact zero_mem _

/-- `ρ'_{gh} = ρ'_g ρ'_h`. -/
theorem s62_rhoPrime_mul (g h : Spin F n) (x : ExtV F n) :
    rhoPrime F n (g * h) x = rhoPrime F n g (rhoPrime F n h x) := by
  have hinv : ∀ y, phiPrimeInv F n (phiPrime F n y) = y := fun y => by
    rw [← LinearMap.comp_apply (phiPrimeInv F n) (phiPrime F n) y, phiPrimeInv_comp_phiPrime,
      LinearMap.id_apply]
  have hm : m F n ((g * h : Spin F n) : C F n) = m F n (g : C F n) * m F n (h : C F n) := by
    rw [Submonoid.coe_mul, map_mul]
  simp only [rhoPrime, LinearMap.comp_apply]
  rw [hinv, hm, TensorProduct.map_mul, Module.End.mul_apply]

theorem s62_rhoPrime_one (x : ExtV F n) : rhoPrime F n 1 x = x := by
  have h1 : m F n ((1 : Spin F n) : C F n) = LinearMap.id := by
    rw [OneMemClass.coe_one, map_one]; rfl
  simp only [rhoPrime, h1, TensorProduct.map_id, LinearMap.id_comp]
  rw [phiPrime_comp_phiPrimeInv, LinearMap.id_apply]

/-- `ρ'_{g⁻¹} ρ'_g = id`. -/
theorem s62_rhoPrime_inv (g : Spin F n) (x : ExtV F n) :
    rhoPrime F n g⁻¹ (rhoPrime F n g x) = x := by
  rw [← s62_rhoPrime_mul, inv_mul_cancel, s62_rhoPrime_one]

omit [CharZero F] in
theorem s62_basisExt_mem (S : Finset (Fin (2 * n + 2 * n))) :
    basisExt F n S ∈ ⋀[F]^S.card (V F n) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard (b := basisV F n) (rfl : S.card = S.card)]
  exact ExteriorAlgebra.ιMulti_range F _ ⟨_, rfl⟩

omit [CharZero F] in
/-- `∫_{X̂ × X}` vanishes outside the top degree `4n`. -/
theorem s62_integralExt_projDeg (m : ℕ) (hm : m ≠ 4 * n) (x : ExtV F n) :
    integralExt F n (projDeg F n m x) = 0 := by
  have : (integralExt F n) ∘ₗ (projDeg F n m) = 0 := by
    refine (basisExt F n).ext fun S => ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, s62_projDeg_of_mem F n (s62_basisExt_mem F n S)]
    split_ifs with h
    · rw [integralExt, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right]
      rintro rfl
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    · rw [map_zero]
  exact LinearMap.congr_fun this x

omit [CharZero F] in
theorem s62_integralExt_of_mem {m : ℕ} {z : ExtV F n} (hz : z ∈ ⋀[F]^m (V F n)) (hm : m ≠ 4 * n) :
    integralExt F n z = 0 := by
  rw [← s62_projDeg_self F n hz]; exact s62_integralExt_projDeg F n m hm z

omit [CharZero F] in
theorem s62_coe_projDegSub (k : ℕ) (x : ExtV F n) :
    (projDegSub F n k x : ExtV F n) = projDeg F n k x := by
  rw [projDeg, GradedAlgebra.proj_apply]; rfl

omit [CharZero F] in
/-- On `⋀^j V`, the pairing `extPairing` is the determinant pairing of degree `j`. -/
theorem s62_extPairing_of_mem (y : ExtV F n) {j : ℕ} (hj : j ≤ 4 * n) {β : ExtV F n}
    (hβ : β ∈ ⋀[F]^j (V F n)) :
    extPairing F n y β = ((pairing F n).exteriorPower j) (projDegSub F n j y) ⟨β, hβ⟩ := by
  have hβj : projDegSub F n j β = ⟨β, hβ⟩ :=
    Subtype.ext (by rw [s62_coe_projDegSub, s62_projDeg_self F n hβ])
  have hβk : ∀ k, k ≠ j → projDegSub F n k β = 0 := fun k hk =>
    Subtype.ext (by rw [s62_coe_projDegSub, s62_projDeg_ne F n hβ (Ne.symm hk)]; rfl)
  simp only [extPairing, LinearMap.sum_apply, LinearMap.compl₁₂_apply]
  rw [Finset.sum_eq_single j]
  · rw [hβj]
  · intro k _ hk; rw [hβk k hk, map_zero]
  · intro h; simp at h; omega

omit [CharZero F] in
/-- A class whose components vanish outside degree `m` lies in `⋀^m V`. -/
theorem s62_mem_of_projDeg (m : ℕ) (y : ExtV F n) (h : ∀ j, j ≠ m → projDeg F n j y = 0) :
    y ∈ ⋀[F]^m (V F n) := by
  classical
  rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) y]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases him : i = m
  · subst him; exact (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) y i).2
  · have h0 : ((DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) y i : ⋀[F]^i (V F n)) :
        ExtV F n) = 0 := by
      rw [← GradedAlgebra.proj_apply]; exact h i him
    rw [h0]; exact zero_mem _

/-- By Lemma 6.3.2, `φ_𝒫 ⊗ ψ_{𝒫⁻¹}` maps `⋀^d V` to `⋀^{4n-d} V`: the pairing of `(φ_𝒫 ⊗ ψ_{𝒫⁻¹})(α)`
with `⋀^j V` is `± ∫ α ∧ (•)`, which vanishes for `j ≠ 4n - d`. -/
theorem s62_PiMap0_mem {d' : ℕ} {α : ExtV F n} (hα : α ∈ ⋀[F]^d' (V F n)) :
    PiMap0 F n α ∈ ⋀[F]^(4 * n - d') (V F n) := by
  have hB : Function.Bijective (pairing F n) :=
    ⟨s62_pairing_injective F n, fun φ => s62_pairing_surjective F n φ⟩
  refine s62_mem_of_projDeg F n _ _ fun j hj => ?_
  by_cases hj4 : j ≤ 4 * n
  · have h : ((pairing F n).exteriorPower j) (projDegSub F n j (PiMap0 F n α)) = 0 := by
      refine LinearMap.ext fun ⟨β, hβ⟩ => ?_
      rw [LinearMap.zero_apply, ← s62_extPairing_of_mem F n _ hj4 hβ, lemma6_3_2 F n d' hα β,
        s62_integralExt_of_mem F n (SetLike.mul_mem_graded hα hβ) (by omega), mul_zero]
    have h0 : projDegSub F n j (PiMap0 F n α) = 0 :=
      (LinearMap.BilinForm.bijective_exteriorPower (pairing F n) j hB).1 (by rw [h, map_zero])
    rw [← s62_coe_projDegSub, h0]; rfl
  · have := s62_projDeg_mem F n j (PiMap0 F n α)
    rw [s62_exteriorPower_eq_bot F n (by omega)] at this
    exact (Submodule.mem_bot F).mp this

/-- `ψ_{𝒫⁻¹[n]} = (-1)ⁿ ψ_{𝒫⁻¹}`, hence `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = (-1)ⁿ φ_𝒫 ⊗ ψ_{𝒫⁻¹}`. -/
theorem s62_PiMap_eq : PiMap F n = (-1 : F) ^ n • PiMap0 F n := by
  have hψ : psiPinvShift F n = (-1 : F) ^ n • psiPinv F n := by
    simp only [psiPinvShift, psiPinv, chPinvShift, map_smul]
  simp only [PiMap, PiMap0, hψ, TensorProduct.map_smul_right, LinearMap.smul_comp,
    LinearMap.comp_smul]

omit [CharZero F] in
/-- `x ∈ F^k = ⊕_{i ≤ k} ⋀^i V` iff the components of `x` of degree `> k` vanish. -/
theorem s62_mem_extFiltLE_iff (k : ℕ) (x : ExtV F n) :
    x ∈ extFiltLE F n k ↔ ∀ i, k < i → projDeg F n i x = 0 := by
  constructor
  · intro hx i hi
    have hle : extFiltLE F n k ≤ LinearMap.ker (projDeg F n i) := iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, s62_projDeg_ne F n hy (by omega)]
    exact hle hx
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i ≤ k
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hik
        (DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x i).2)
    · have h0 : ((DirectSum.decompose (fun i : ℕ => ⋀[F]^i (V F n)) x i : ⋀[F]^i (V F n)) :
          ExtV F n) = 0 := by
        rw [← GradedAlgebra.proj_apply]; exact hx i (by omega)
      rw [h0]; exact zero_mem _

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` maps `⋀^i V` to `⋀^{4n-i} V` (Lemma 6.3.2). -/
theorem s62_PiMap_mem {i : ℕ} {y : ExtV F n} (hy : y ∈ ⋀[F]^i (V F n)) :
    PiMap F n y ∈ ⋀[F]^(4 * n - i) (V F n) := by
  rw [s62_PiMap_eq, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (s62_PiMap0_mem F n hy)

/-- Degree reversal: `(φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]})(y)_{4n-j} = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]})(y_j)`. -/
theorem s62_projDeg_PiMap {j : ℕ} (hj : j ≤ 4 * n) (y : ExtV F n) :
    projDeg F n (4 * n - j) (PiMap F n y) = PiMap F n (projDeg F n j y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[F]^i (V F n)) with
  | zero => simp
  | @homogeneous i y =>
    obtain ⟨y, hy⟩ := y
    show projDeg F n (4 * n - j) (PiMap F n y) = PiMap F n (projDeg F n j y)
    by_cases hi : i ≤ 4 * n
    · rw [s62_projDeg_of_mem F n (s62_PiMap_mem F n hy), s62_projDeg_of_mem F n hy]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right (by omega), ite_eq_right hij, map_zero]
    · obtain rfl : y = 0 := (Submodule.mem_bot F).mp
        (by rwa [s62_exteriorPower_eq_bot F n (by omega)] at hy)
      simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

/-- `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` is injective (`φ_𝒫` and `ψ_{𝒫⁻¹[n]}` are mutually inverse). -/
theorem s62_PiMap_injective : Function.Injective (PiMap F n) := by
  have hinv : ∀ x, kunnethHatX F n (TensorProduct.map (psiPinvShift F n) (phiP F n)
      ((kunnethXHat F n).symm (PiMap F n x))) = x := by
    intro x
    have hP : PiMap F n x = kunnethXHat F n (TensorProduct.map (phiP F n) (psiPinvShift F n)
        ((kunnethHatX F n).symm x)) := rfl
    rw [hP, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
      ← TensorProduct.map_comp, psiPinvShift_comp_phiP, phiP_comp_psiPinvShift,
      TensorProduct.map_id, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  intro x y hxy
  rw [← hinv x, ← hinv y, hxy]

/-- `φ' = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ φ̃` (Lemma 6.1.1, `τ² = 1`). -/
theorem s62_phiPrime_eq : phiPrime F n = PiMap F n ∘ₗ varphiTilde F n := by
  rw [phiPrime, lemma6_1_1, LinearMap.comp_assoc, LinearMap.comp_assoc, tauTensor_comp_tauTensor,
    LinearMap.comp_id]

/-- (§6.4, TeX line 2867) "Both [`ρ` and `ρ'`] factor through the image `SO⁺(V)` of `Spin(V)`":
`ρ'_g` depends only on `ρ(g)` (`ρ` on `⋀•V` is `⋀ρ(g)` by definition). -/
theorem rhoPrime_factors (g g' : Spin F n) (h : rho F n g = rho F n g') :
    rhoPrime F n g = rhoPrime F n g' := by
  -- by Proposition 6.1.2, `ρ'_g = exp(½[c₁(𝒫) - ρ_g c₁(𝒫)]) ∪ ρ_g` only depends on `ρ_g = ⋀ρ(g)`
  have hρ : rhoExt F n g = rhoExt F n g' := by simp only [rhoExt, h]
  refine LinearMap.ext fun x => ?_
  rw [proposition6_1_2, proposition6_1_2, hρ]

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
  -- `U ∩ F_{k+1}` is a `G`-subrepresentation of `U`, proper since `U ⊄ F_{k+1}`
  have h1 : U ⊓ extFiltGE F n (k + 1) = ⊥ := by
    rcases hirr (U ⊓ extFiltGE F n (k + 1)) inf_le_left
        (fun g hg x hx => ⟨hU g hg x hx.1, rhoPrime_mem_extFiltGE F n g (k + 1) hx.2⟩) with h | h
    · exact h
    · exact absurd (by rw [← h]; exact inf_le_right) hk.2
  refine ⟨h1, ?_, fun g _ x hx => rhoPrime_projDeg F n g k (hk.1 hx)⟩
  -- hence `U` projects injectively to `H^k`
  intro x hx y hy hxy
  have hmem : x - y ∈ U ⊓ extFiltGE F n (k + 1) := by
    refine ⟨Submodule.sub_mem _ hx hy, (s62_mem_extFiltGE_iff F n _ _).mpr fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · exact (s62_mem_extFiltGE_iff F n k _).mp (hk.1 (Submodule.sub_mem _ hx hy)) i hik
    · obtain rfl : i = k := by omega
      rw [map_sub, hxy, sub_self]
  rw [h1, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- (Proof of Proposition 6.4.1(2), TeX line 2969) "The weight is invariant under the
`Spin(V_K)`-action": if `U` has weight `k`, so has `ρ'_g(U)`. -/
theorem HasWeight.map_rhoPrime {U : Submodule F (ExtV F n)} {k : ℕ} (hk : HasWeight F n U k)
    (g : Spin F n) : HasWeight F n (U.map (rhoPrime F n g)) k := by
  refine ⟨Submodule.map_le_iff_le_comap.mpr fun x hx => rhoPrime_mem_extFiltGE F n g k (hk.1 hx),
    fun h => hk.2 fun x hx => ?_⟩
  rw [← s62_rhoPrime_inv F n g x]
  exact rhoPrime_mem_extFiltGE F n g⁻¹ (k + 1) (h (Submodule.mem_map_of_mem hx))

/-- (Proof of Proposition 6.4.1(2), TeX lines 2975–2976, by Lemma 6.3.2) `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` sends
`F^k(⋀• V) = ⊕_{i ≤ k} ⋀^i V` into `F_{4n-k}(⋀• V) = ⊕_{i ≥ 4n-k} ⋀^i V` (it maps `⋀^i V` to
`⋀^{4n-i} V`). -/
theorem PiMap_mem_extFiltGE (k : ℕ) {x : ExtV F n} (hx : x ∈ extFiltLE F n k) :
    PiMap F n x ∈ extFiltGE F n (4 * n - k) := by
  have hle : extFiltLE F n k ≤ (extFiltGE F n (4 * n - k)).comap (PiMap F n) :=
    iSup₂_le fun i hi z hz => by
      rw [Submodule.mem_comap, s62_PiMap_eq, LinearMap.smul_apply]
      refine Submodule.smul_mem _ _ ?_
      by_cases hi4 : i ≤ 4 * n
      · exact Submodule.mem_iSup_of_mem (4 * n - i)
          (Submodule.mem_iSup_of_mem (by omega) (s62_PiMap0_mem F n hz))
      · rw [s62_exteriorPower_eq_bot F n (by omega)] at hz
        rw [(Submodule.mem_bot F).mp hz, map_zero]
        exact zero_mem _
  exact hle hx

/-- (Proof of Proposition 6.4.1(2), TeX lines 2968–2977, from Lemma 2.3.2, Lemma 6.1.1 and
Lemma 6.3.2) For the pure spinors `1` and `[pt_X]` (with `ker m_1 = H¹(X̂)`, `ker m_{[pt]} = H¹(X)`
complementary): `φ'([pt] ⊗ 1 - (-1)ⁿ 1 ⊗ [pt])` has weight `2` and `φ'([pt] ⊗ 1 + (-1)ⁿ 1 ⊗ [pt])`
has weight `0`. (`1 ≤ n`, implied by the standing assumption `n ≥ 2`.) -/
theorem phiPrime_one_pt_hasWeight (hn : 1 ≤ n) :
    HasWeight F n (Submodule.span F
        {phiPrime F n (pt F n ⊗ₜ[F] (1 : S F n) - (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n))}) 2 ∧
      HasWeight F n (Submodule.span F
        {phiPrime F n (pt F n ⊗ₜ[F] (1 : S F n) + (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n))}) 0 := by
  -- `φ' = (φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}) ∘ φ̃` (Lemma 6.1.1), and `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]}` sends `F^k` into
  -- `F_{4n-k}` (Lemma 6.3.2), injectively and reversing degrees
  rw [s62_phiPrime_eq, LinearMap.comp_apply, LinearMap.comp_apply]
  obtain ⟨h1, h2⟩ := lemma2_3_2_1 F n hn
  have h3 := lemma2_3_2_2 F n hn
  constructor
  · refine ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr ?_, ?_⟩
    · have := PiMap_mem_extFiltGE F n (4 * n - 2) h1
      rwa [show 4 * n - (4 * n - 2) = 2 by omega] at this
    · rw [Submodule.span_singleton_le_iff_mem, s62_mem_extFiltGE_iff]
      intro hall
      apply h2
      rw [s62_mem_extFiltLE_iff]
      intro i hi
      by_cases hi2 : i = 4 * n - 2
      · subst hi2
        apply s62_PiMap_injective F n
        rw [← s62_projDeg_PiMap F n (by omega), show 4 * n - (4 * n - 2) = 2 by omega,
          hall 2 (by omega), map_zero]
      · exact (s62_mem_extFiltLE_iff F n _ _).mp h1 i (by omega)
  · refine ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr ?_, ?_⟩
    · exact (s62_mem_extFiltGE_iff F n 0 _).mpr fun i hi => absurd hi (Nat.not_lt_zero i)
    · rw [Submodule.span_singleton_le_iff_mem, s62_mem_extFiltGE_iff]
      intro hall
      apply h3
      rw [s62_mem_extFiltLE_iff]
      intro i hi
      by_cases hi4 : i = 4 * n
      · subst hi4
        apply s62_PiMap_injective F n
        rw [← s62_projDeg_PiMap F n le_rfl, Nat.sub_self, hall 0 (by omega), map_zero]
      · have := s62_projDeg_mem F n i (varphiTilde F n (pt F n ⊗ₜ[F] (1 : S F n) +
          (-1 : F) ^ n • ((1 : S F n) ⊗ₜ[F] pt F n)))
        rw [s62_exteriorPower_eq_bot F n (by omega)] at this
        exact (Submodule.mem_bot F).mp this

end Weight

/-! ## Helpers: change of coefficients `ℚ → K` -/

section BC

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)


omit [CharZero F] [CharZero F'] in
theorem s62_bcS_ιMulti (k : ℕ) (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun j => s62_bcS_ι F F' n (v j)))

omit [CharZero F] [CharZero F'] in
theorem s62_bcS_basisS (S : Finset (Fin (2 * n))) : bcS F F' n (basisS F n S) = basisS F' n S := by
  rw [basisS, basisS, ExteriorAlgebra.basis_apply_ofCard (b := Pi.basisFun F _) rfl,
    ExteriorAlgebra.basis_apply_ofCard (b := Pi.basisFun F' _) rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_family, s62_bcS_ιMulti]
  congr 1; funext j
  simp only [Function.comp_apply, Pi.basisFun_apply]
  exact s62_bcH1_e F F' n _

omit [CharZero F] [CharZero F'] in
theorem s62_bcS_eq_sum (x : S F n) :
    bcS F F' n x = ∑ T, algebraMap F F' ((basisS F n).repr x T) • basisS F' n T := by
  conv_lhs => rw [← (basisS F n).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_smul, s62_bcS_basisS, algebraMap_smul]

omit [CharZero F] [CharZero F'] in
theorem s62_repr_bcS (x : S F n) (T : Finset (Fin (2 * n))) :
    (basisS F' n).repr (bcS F F' n x) T = algebraMap F F' ((basisS F n).repr x T) := by
  rw [s62_bcS_eq_sum, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

omit [CharZero F] [CharZero F'] in
theorem s62_epsSign_bc (A B : Finset (Fin (2 * n))) :
    epsSign F' n A B = algebraMap F F' (epsSign F n A B) := by
  rw [epsSign, epsSign, ← s62_repr_bcS, map_mul (bcS F F' n), s62_bcS_basisS, s62_bcS_basisS]


/-- Change of coefficients on `H*(X̂) = ⋀• H¹(X)*`. -/
noncomputable def s62_bcSHat : SHat F n →ₐ[F] SHat F' n :=
  ExteriorAlgebra.lift F
    ⟨((ExteriorAlgebra.ι F' : Module.Dual F' (H1 F' n) →ₗ[F'] SHat F' n).restrictScalars F) ∘ₗ
        bcDual F F' n,
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

theorem s62_bcSHat_ι (θ : Module.Dual F (H1 F n)) :
    s62_bcSHat F F' n (ExteriorAlgebra.ι F θ) = ExteriorAlgebra.ι F' (bcDual F F' n θ) :=
  ExteriorAlgebra.lift_ι_apply F _ _ θ

theorem s62_bcSHat_basisSHat (T : Finset (Fin (2 * n))) :
    s62_bcSHat F F' n (basisSHat F n T) = basisSHat F' n T := by
  rw [basisSHat, basisSHat, ExteriorAlgebra.basis_apply_ofCard (b := (Pi.basisFun F _).dualBasis) rfl,
    ExteriorAlgebra.basis_apply_ofCard (b := (Pi.basisFun F' _).dualBasis) rfl,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  simp only [Function.comp_apply, s62_bcSHat_ι, s62_dualBasis_eq_f, s62_bcDual_f]

theorem s62_bcExt_pullX (x : S F n) : bcExt F F' n (pullX F n x) = pullX F' n (bcS F F' n x) := by
  have : (bcExt F F' n).comp (pullX F n) = ((pullX F' n).restrictScalars F).comp (bcS F F' n) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun w => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply, pullX,
        ExteriorAlgebra.map_apply_ι, s62_bcExt_ι, s62_bcS_ι, AlgHom.restrictScalars_apply,
        LinearMap.inr_apply, bcV, LinearMap.prodMap_apply, map_zero])
  exact congrArg (fun φ : S F n →ₐ[F] ExtV F' n => φ x) this

theorem s62_bcExt_pullXHat (a : SHat F n) :
    bcExt F F' n (pullXHat F n a) = pullXHat F' n (s62_bcSHat F F' n a) := by
  have : (bcExt F F' n).comp (pullXHat F n) =
      ((pullXHat F' n).restrictScalars F).comp (s62_bcSHat F F' n) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun θ => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply, pullXHat,
        ExteriorAlgebra.map_apply_ι, s62_bcExt_ι, s62_bcSHat_ι, AlgHom.restrictScalars_apply,
        LinearMap.inl_apply, bcV, LinearMap.prodMap_apply, map_zero])
  exact congrArg (fun φ : SHat F n →ₐ[F] ExtV F' n => φ a) this

omit [CharZero F] [CharZero F'] in
theorem s62_bcS_tau (x : S F n) : bcS F F' n (tau F n x) = tau F' n (bcS F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    simp only [tau, CliffordAlgebra.reverse.commutes, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' n), CliffordAlgebra.reverse.commutes]
  | ι w =>
    show bcS F F' n (tau F n (ExteriorAlgebra.ι F w)) = tau F' n (bcS F F' n (ExteriorAlgebra.ι F w))
    rw [s62_bcS_ι]
    exact (congrArg (bcS F F' n) (CliffordAlgebra.reverse_ι _)).trans
      ((s62_bcS_ι F F' n w).trans (CliffordAlgebra.reverse_ι _).symm)
  | mul a b ha hb =>
    simp only [tau] at ha hb ⊢
    rw [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb, map_mul, CliffordAlgebra.reverse.map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]


/-- `φ(e_K ⊗ e_L)` in the basis (from `μ^*` and `ψ_{𝒫⁻¹[n]}` on the basis, §6.3). -/
theorem s62_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L) =
      ∑ I ∈ K.powerset, (epsSign F n I (K \ I) * epsSign F n (K \ I) L *
        ((-1 : F) ^ (((K \ I) ∪ L).card * (((K \ I) ∪ L).card + 3) / 2) *
          epsSign F n ((K \ I) ∪ L) ((K \ I) ∪ L)ᶜ)) •
        (pullX F n (basisS F n I) * pullXHat F n (basisSHat F n ((K \ I) ∪ L)ᶜ)) := by
  simp only [phiOrlov, LinearMap.comp_apply, muStar_basis, map_sum, map_smul,
    TensorProduct.map_tmul, LinearMap.id_apply, psiPinvShift_basis, TensorProduct.tmul_smul,
    smul_smul, LinearEquiv.coe_coe, kunnethXHat_tmul]

theorem s62_bcExt_phiOrlov_basis (K L : Finset (Fin (2 * n))) :
    bcExt F F' n (phiOrlov F n (basisS F n K ⊗ₜ[F] basisS F n L)) =
      phiOrlov F' n (basisS F' n K ⊗ₜ[F'] basisS F' n L) := by
  rw [s62_phiOrlov_basis, s62_phiOrlov_basis, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_smul, map_mul, s62_bcExt_pullX, s62_bcExt_pullXHat, s62_bcS_basisS,
    s62_bcSHat_basisSHat, algebra_compatible_smul F', map_mul, map_mul, map_mul, map_pow, map_neg,
    map_one, ← s62_epsSign_bc, ← s62_epsSign_bc, ← s62_epsSign_bc]

end BC


/-! ## Helpers: the pure spinors `1` and `[pt_X]` -/

section PureOnePt

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s62_finrank_H1 : Module.finrank F (H1 F n) = 2 * n := Module.finrank_fin_fun F

omit [CharZero F] in
theorem s62_pt_mem : pt F n ∈ ⋀[F]^(2 * n) (H1 F n) := by
  have h := ExteriorAlgebra.basis_apply_ofCard (b := Pi.basisFun F (Fin (2 * n)))
    (show (Finset.univ : Finset (Fin (2 * n))).card = 2 * n by simp)
  rw [pt, basisS, h]
  exact ExteriorAlgebra.ιMulti_range F _ ⟨_, rfl⟩

omit [CharZero F] in
theorem s62_ι_mul_pt (w : H1 F n) : ExteriorAlgebra.ι F w * pt F n = 0 := by
  have hι : ExteriorAlgebra.ι F w ∈ ⋀[F]^1 (H1 F n) := by
    rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ w
  have h := SetLike.mul_mem_graded (A := fun i : ℕ => ⋀[F]^i (H1 F n)) hι (s62_pt_mem F n)
  have hbot : ⋀[F]^(1 + 2 * n) (H1 F n) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [exteriorPower.finrank_eq, s62_finrank_H1]
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [hbot] at h
  exact (Submodule.mem_bot F).mp h

omit [CharZero F] in
theorem s62_pt_ne_zero : pt F n ≠ 0 := (basisS F n).ne_zero _

omit [CharZero F] in
theorem s62_D_pt_eq_zero_iff (θ : Module.Dual F (H1 F n)) : D F n θ (pt F n) = 0 ↔ θ = 0 := by
  refine ⟨fun h => LinearMap.ext fun w => ?_, fun h => by rw [h, map_zero, LinearMap.zero_apply]⟩
  have h1 := contractLeft_ι_mul (Q := (0 : QuadraticForm F (H1 F n))) θ w (pt F n)
  have h2 : ExteriorAlgebra.ι F w * pt F n = 0 := s62_ι_mul_pt F n w
  change contractLeft (Q := (0 : QuadraticForm F (H1 F n))) θ (pt F n) = 0 at h
  rw [show CliffordAlgebra.ι (0 : QuadraticForm F (H1 F n)) w * pt F n = 0 from h2, map_zero, h,
    mul_zero, sub_zero] at h1
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h1.symm).resolve_right (s62_pt_ne_zero F n)

theorem s62_ann_one : ann F n 1 = LinearMap.range (LinearMap.inl F (Module.Dual F (H1 F n))
    (H1 F n)) := by
  ext v
  rw [ann, LinearMap.mem_ker, s62_mOf_apply, mul_one, show D F n v.1 1 = 0 from
    contractLeft_one (Q := (0 : QuadraticForm F (H1 F n))) _, add_zero, LinearMap.mem_range]
  constructor
  · intro h
    exact ⟨v.1, Prod.ext rfl ((ExteriorAlgebra.ι_eq_zero_iff v.2).mp h).symm⟩
  · rintro ⟨θ, rfl⟩
    simp

theorem s62_ann_pt : ann F n (pt F n) = LinearMap.range (LinearMap.inr F (Module.Dual F (H1 F n))
    (H1 F n)) := by
  ext v
  rw [ann, LinearMap.mem_ker, s62_mOf_apply, s62_ι_mul_pt, zero_add, s62_D_pt_eq_zero_iff,
    LinearMap.mem_range]
  constructor
  · intro h
    exact ⟨v.2, Prod.ext h.symm rfl⟩
  · rintro ⟨w, rfl⟩
    rfl

theorem s62_isEvenPureSpinor_one : IsEvenPureSpinor F n 1 := by
  refine ⟨CliffordAlgebra.one_le_evenOdd_zero _ (Submodule.one_le.mp le_rfl), ?_, ?_⟩
  · intro v hv
    rw [s62_ann_one] at hv
    obtain ⟨θ, rfl⟩ := hv
    simp
  · rw [s62_ann_one, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
      Subspace.dual_finrank_eq, s62_finrank_H1]

theorem s62_isEvenPureSpinor_pt : IsEvenPureSpinor F n (pt F n) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := s62_pt_mem F n
    rw [ExteriorAlgebra.exteriorPower] at h
    exact Submodule.mem_iSup_of_mem (⟨2 * n, by rw [Nat.cast_mul]; exact mul_eq_zero_of_left rfl _⟩ :
      {j : ℕ // (j : ZMod 2) = 0}) h
  · intro v hv
    rw [s62_ann_pt] at hv
    obtain ⟨w, rfl⟩ := hv
    simp
  · rw [s62_ann_pt, LinearMap.finrank_range_of_inj LinearMap.inr_injective, s62_finrank_H1]

theorem s62_ann_pt_inf_ann_one : ann F n (pt F n) ⊓ ann F n 1 = ⊥ := by
  rw [s62_ann_pt, s62_ann_one, eq_bot_iff]
  rintro v ⟨⟨w, rfl⟩, ⟨θ, hθ⟩⟩
  have h2 := congrArg Prod.snd hθ
  simp only [LinearMap.inl_apply, LinearMap.inr_apply] at h2
  rw [← h2]; simp

/-- `φ'` intertwines `m_g ⊗ m_g` with `ρ'_g` ((6.1.4)). -/
theorem s62_phiPrime_map (g : Spin F n) (z : S F n ⊗[F] S F n) :
    phiPrime F n (TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) z) =
      rhoPrime F n g (phiPrime F n z) := by
  simp only [rhoPrime, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (phiPrimeInv F n) (phiPrime F n) z, phiPrimeInv_comp_phiPrime,
    LinearMap.id_apply]

end PureOnePt


/-! ## Helpers: real and imaginary parts on `⋀• V_K` -/

section ReIm

variable {n : ℕ} (d : ℚ)

/-- The real part `⋀• V_K → ⋀• V_ℚ` (coefficientwise `a + b√-d ↦ a`). -/
noncomputable def s62_reExt : ExtV (Kd d) n →ₗ[ℚ] ExtV ℚ n :=
  (basisExt ℚ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun T => Kd.ratPart d ∘ₗ ((basisExt (Kd d) n).coord T).restrictScalars ℚ)

/-- `Im/√d : ⋀• V_K → ⋀• V_ℚ` (coefficientwise `a + b√-d ↦ b`). -/
noncomputable def s62_imExt : ExtV (Kd d) n →ₗ[ℚ] ExtV ℚ n :=
  (basisExt ℚ n).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun T => Kd.sqrtNegCoeff d ∘ₗ ((basisExt (Kd d) n).coord T).restrictScalars ℚ)

theorem s62_repr_reExt (v : ExtV (Kd d) n) (T : Finset (Fin (2 * n + 2 * n))) :
    (basisExt ℚ n).repr (s62_reExt d v) T = Kd.ratPart d ((basisExt (Kd d) n).repr v T) := by
  simp [s62_reExt, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

theorem s62_repr_imExt (v : ExtV (Kd d) n) (T : Finset (Fin (2 * n + 2 * n))) :
    (basisExt ℚ n).repr (s62_imExt d v) T = Kd.sqrtNegCoeff d ((basisExt (Kd d) n).repr v T) := by
  simp [s62_imExt, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

/-- `v = Re(v) + √-d Im(v)/√d` on `⋀• V_K`. -/
theorem s62_bcExt_reExt_add_imExt (hd : 0 < d) (v : ExtV (Kd d) n) :
    bcExt ℚ (Kd d) n (s62_reExt d v) + Kd.sqrtNeg d • bcExt ℚ (Kd d) n (s62_imExt d v) = v := by
  apply (basisExt (Kd d) n).repr.injective
  ext T
  rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s62_repr_bcExt, s62_repr_bcExt,
    s62_repr_reExt, s62_repr_imExt, smul_eq_mul, mul_comm (Kd.sqrtNeg d)]
  exact congrArg Subtype.val (Kd.eq_ratPart_add_sqrtNegCoeff hd _).symm

/-- `a + b√-d = 0` with `a, b ∈ ℚ` forces `a = b = 0`. -/
theorem s62_rat_add_sqrtNeg_eq_zero (hd : 0 < d) (a b : ℚ)
    (h : algebraMap ℚ (Kd d) a + Kd.sqrtNeg d * algebraMap ℚ (Kd d) b = 0) : a = 0 ∧ b = 0 := by
  have h' := congrArg (fun z : Kd d => (z : ℂ)) h
  have hc : ∀ q : ℚ, ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := fun q => by
    rw [← map_ratCast (Kd d).subtype q]; simp
  simp only [Subfield.coe_add, Subfield.coe_mul, Subfield.coe_zero, hc, Kd.sqrtNeg,
    sqrtNeg] at h'
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  simp at hre him
  refine ⟨by exact_mod_cast hre, ?_⟩
  rcases him with h1 | h1
  · exact absurd h1 hsd.ne'
  · exact_mod_cast h1

/-- `bc(a) + √-d bc(b) = 0` with `a, b` rational forces `a = b = 0`. -/
theorem s62_bcExt_add_sqrtNeg_eq_zero (hd : 0 < d) {a b : ExtV ℚ n}
    (h : bcExt ℚ (Kd d) n a + Kd.sqrtNeg d • bcExt ℚ (Kd d) n b = 0) : a = 0 ∧ b = 0 := by
  have hT : ∀ T, (basisExt ℚ n).repr a T = 0 ∧ (basisExt ℚ n).repr b T = 0 := fun T => by
    have := congrArg (fun z => (basisExt (Kd d) n).repr z T) h
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, s62_repr_bcExt,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact s62_rat_add_sqrtNeg_eq_zero d hd _ _ this
  exact ⟨(basisExt ℚ n).repr.injective (Finsupp.ext fun T => by simp [(hT T).1]),
    (basisExt ℚ n).repr.injective (Finsupp.ext fun T => by simp [(hT T).2])⟩

end ReIm

namespace KSecant

variable {n : ℕ} {d : ℚ} (P : KSecant n d)

/-- Lemma 2.2.7 over `K`: outside the middle degree, the `Spin(V)_P`-invariants of `⋀^k V_K` are a
trivial representation of `Spin(V_K)_{ℓ₁,ℓ₂}` (they are spanned by rational invariants, which are
trivial characters by Lemma 2.2.7). -/
theorem s62_invK_trivial (hd : 0 < d) (hP : ¬ P.IsIsotropic) {k : ℕ} (hk : k ≠ 2 * n)
    {v : ExteriorAlgebra (Kd d) (V (Kd d) n)} (hv : v ∈ P.invK k) (h : P.spinL₁L₂) :
    rhoExt (Kd d) n h v = v := by
  have hdec := s62_bcExt_reExt_add_imExt d hd v
  set a := s62_reExt d v
  set b := s62_imExt d v
  -- the real and imaginary parts are rational `Spin(V)_P`-invariants of degree `k`
  have hdeg : ∀ j, j ≠ k → projDeg ℚ n j a = 0 ∧ projDeg ℚ n j b = 0 := fun j hj => by
    apply s62_bcExt_add_sqrtNeg_eq_zero d hd
    rw [← s62_projDeg_bcExt, ← s62_projDeg_bcExt, ← map_smul, ← map_add, hdec,
      s62_projDeg_ne _ n hv.1 (Ne.symm hj)]
  have hinv : ∀ g ∈ P.spinPZ, rhoExt ℚ n g a = a ∧ rhoExt ℚ n g b = b := fun g hg => by
    have h1 := hv.2 (bcSpin ℚ (Kd d) n g) ⟨g, hg, rfl⟩
    rw [← hdec, map_add, map_smul, s62_rhoExt_bcExt, s62_rhoExt_bcExt] at h1
    have h2 := s62_bcExt_add_sqrtNeg_eq_zero d hd (a := rhoExt ℚ n g a - a)
      (b := rhoExt ℚ n g b - b) (by rw [map_sub, map_sub, smul_sub, sub_add_sub_comm, h1,
        sub_self])
    exact ⟨sub_eq_zero.mp h2.1, sub_eq_zero.mp h2.2⟩
  have ha : a ∈ P.invQ k := ⟨s62_mem_of_projDeg ℚ n k a fun j hj => (hdeg j hj).1,
    fun g hg => (hinv g hg).1⟩
  have hb : b ∈ P.invQ k := ⟨s62_mem_of_projDeg ℚ n k b fun j hj => (hdeg j hj).2,
    fun g hg => (hinv g hg).2⟩
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
  · rw [← two_mul] at ha hb hk hv
    by_cases hj2 : j ≤ 2 * n
    · rw [← hdec, map_add, map_smul, lemma2_2_7_trivial P hd hP j (by omega) hj2 a ha h,
        lemma2_2_7_trivial P hd hP j (by omega) hj2 b hb h]
    · have hbot := s62_exteriorPower_eq_bot (Kd d) n (k := 2 * j) (by omega)
      have hv0 : v = 0 := by
        have := hv.1; rw [hbot] at this; exact (Submodule.mem_bot _).mp this
      rw [hv0, map_zero]
  · have : Module.Finite ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
    have hfr := lemma2_2_7_odd P hd hP k hodd
    have hbot : P.invQ k = ⊥ := Submodule.finrank_eq_zero.mp hfr
    rw [hbot, Submodule.mem_bot] at ha hb
    rw [← hdec, ha, hb]
    simp only [map_zero, smul_zero, add_zero]

end KSecant



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

/-- "**The homomorphism `φ'` is defined over `ℚ`**" (proof of Proposition 6.4.1(1)). -/
theorem s62_bcExt_phiPrime (y : S ℚ n ⊗[ℚ] S ℚ n) :
    bcExt ℚ (Kd d) n (phiPrime ℚ n y) = phiPrime (Kd d) n (bcSS n d y) := by
  have h : (TensorProduct.mk ℚ (S ℚ n) (S ℚ n)).compr₂
      ((bcExt ℚ (Kd d) n).toLinearMap ∘ₗ phiOrlov ℚ n) =
      (TensorProduct.mk ℚ (S ℚ n) (S ℚ n)).compr₂
        (((phiOrlov (Kd d) n).restrictScalars ℚ) ∘ₗ bcSS n d) := by
    refine (basisS ℚ n).ext fun K => (basisS ℚ n).ext fun L => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, bcSS_tmul, s62_bcS_basisS, LinearMap.restrictScalars_apply]
    exact s62_bcExt_phiOrlov_basis ℚ (Kd d) n K L
  have h' := TensorProduct.ext h
  have key : ∀ z, bcExt ℚ (Kd d) n (phiOrlov ℚ n z) = phiOrlov (Kd d) n (bcSS n d z) :=
    fun z => LinearMap.congr_fun h' z
  have htau : ∀ z : S ℚ n ⊗[ℚ] S ℚ n,
      bcSS n d (tauTensor ℚ n z) = tauTensor (Kd d) n (bcSS n d z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x w =>
      simp only [tauTensor, TensorProduct.map_tmul, LinearMap.id_apply, bcSS_tmul, s62_bcS_tau]
    | add a b ha hb => simp only [map_add, ha, hb]
  show bcExt ℚ (Kd d) n (phiOrlov ℚ n (tauTensor ℚ n y)) =
    phiOrlov (Kd d) n (tauTensor (Kd d) n (bcSS n d y))
  rw [key, htau]


/-- The Galois involution `σ` of `S_K` is `σ`-semilinear. -/
theorem s62_conjS_smul (c : Kd d ≃+* Kd d) (k : Kd d) (x : S (Kd d) n) :
    conjS c n (k • x) = c k • conjS c n x := by
  simp only [conjS, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_smul,
    Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_smul]

/-- `σ` fixes the rational classes. -/
theorem s62_conjS_bcS (c : Kd d ≃+* Kd d) (x : S ℚ n) :
    conjS c n (bcS ℚ (Kd d) n x) = bcS ℚ (Kd d) n x := by
  rw [s62_bcS_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hc : ∀ q : ℚ, c (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q :=
    fun q => RingHom.map_rat_algebraMap (c : Kd d →+* Kd d) q
  rw [s62_conjS_smul, hc]
  congr 1
  simp only [conjS, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Module.Basis.repr_self,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single T]
  · simp
  · intro K _ hK; rw [ite_eq_right_iff.mpr (fun h => absurd h (Ne.symm hK)), map_zero, zero_smul]
  · simp

/-- `σ(√-d) = -√-d`. -/
theorem s62_σ_sqrtNeg : Kd.σ d (Kd.sqrtNeg d) = -Kd.sqrtNeg d := by
  apply Subtype.ext
  simp [Kd.sqrtNeg, sqrtNeg, Complex.conj_ofReal]

theorem s62_sqrtNeg_sq (hd : 0 < d) : Kd.sqrtNeg d * Kd.sqrtNeg d = -algebraMap ℚ (Kd d) d := by
  apply Subtype.ext
  have := sqrtNeg_sq hd.le
  rw [sq] at this
  simpa [Kd.sqrtNeg] using this

theorem s62_sqrtNeg_ne_zero (hd : 0 < d) : Kd.sqrtNeg d ≠ 0 := by
  intro h
  have := s62_sqrtNeg_sq d hd
  rw [h, mul_zero, eq_comm, neg_eq_zero, map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective] at this
  exact hd.ne' this

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

/-- `u₂ = σ(u₁) = Re(u₁) - √-d Im(u₁)/√d`. -/
theorem s62_u₂_eq (hd : 0 < d) :
    P.u₂ = bcS ℚ (Kd d) n (reS n d P.u₁) - Kd.sqrtNeg d • bcS ℚ (Kd d) n (imS n d P.u₁) := by
  rw [KSecant.u₂]
  conv_lhs => rw [← bcS_reS_add_imS n d hd P.u₁]
  rw [map_add, s62_conjS_bcS, s62_conjS_smul, s62_conjS_bcS, s62_σ_sqrtNeg, neg_smul,
    ← sub_eq_add_neg]

/-- The base change of the two generators of `HW_P`, in terms of `u₁ ⊗ u₁` and `u₂ ⊗ u₂`:
`u₁ ⊗ u₁ = G₁ + √-d G₂` and `u₂ ⊗ u₂ = G₁ - √-d G₂`. -/
theorem s62_tmul_u (hd : 0 < d) :
    P.u₁ ⊗ₜ[Kd d] P.u₁ = bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ -
        d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁)) +
      Kd.sqrtNeg d • bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁) ∧
    P.u₂ ⊗ₜ[Kd d] P.u₂ = bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ -
        d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁)) -
      Kd.sqrtNeg d • bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁) := by
  set a := bcS ℚ (Kd d) n (reS n d P.u₁)
  set b := bcS ℚ (Kd d) n (imS n d P.u₁)
  have hs := s62_sqrtNeg_sq d hd
  have h1 : P.u₁ = a + Kd.sqrtNeg d • b := (bcS_reS_add_imS n d hd P.u₁).symm
  have h2 : P.u₂ = a - Kd.sqrtNeg d • b := P.s62_u₂_eq hd
  have hG : bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ - d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁)) =
      a ⊗ₜ[Kd d] a - algebraMap ℚ (Kd d) d • (b ⊗ₜ[Kd d] b) := by
    rw [map_sub, map_smul, bcSS_tmul, bcSS_tmul, algebraMap_smul]
  have hG' : bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁) =
      a ⊗ₜ[Kd d] b + b ⊗ₜ[Kd d] a := by
    rw [map_add, bcSS_tmul, bcSS_tmul]
  rw [hG, hG', h1, h2]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub, TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_add, smul_sub,
    smul_smul, hs, neg_smul]
  constructor <;> abel

/-- "The `2`-dimensional subspace `HW_{P_K} := ℓ̃₁^{⊗2} ⊕ ℓ̃₂^{⊗2}` of `S⁺_K ⊗_K S⁺_K` is defined over
`ℚ`" (§6.4): it is the `K`-span of the base change of `HW_P`. -/
theorem span_bcSS_HWP (hd : 0 < d) :
    Submodule.span (Kd d) (bcSS n d '' P.HWP) =
      Submodule.span (Kd d) {P.u₁ ⊗ₜ[Kd d] P.u₁, P.u₂ ⊗ₜ[Kd d] P.u₂} := by
  obtain ⟨h1, h2⟩ := P.s62_tmul_u hd
  have hs0 := s62_sqrtNeg_ne_zero d hd
  rw [HWP, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower,
    Set.image_pair]
  set G₁ := bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ - d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁))
  set G₂ := bcSS n d (reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁)
  -- `G₁ = ½(u₁ ⊗ u₁ + u₂ ⊗ u₂)`, `G₂ = (u₁ ⊗ u₁ - u₂ ⊗ u₂)/(2√-d)`
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · refine Submodule.mem_span_pair.mpr ⟨2⁻¹, 2⁻¹, ?_⟩
      rw [h1, h2]; module
    · refine Submodule.mem_span_pair.mpr ⟨(2 * Kd.sqrtNeg d)⁻¹, -(2 * Kd.sqrtNeg d)⁻¹, ?_⟩
      rw [h1, h2]
      have hc : (2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d = 2⁻¹ := by field_simp
      calc (2 * Kd.sqrtNeg d)⁻¹ • (G₁ + Kd.sqrtNeg d • G₂) +
            -(2 * Kd.sqrtNeg d)⁻¹ • (G₁ - Kd.sqrtNeg d • G₂)
          = ((2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d + (2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d) • G₂ := by
            module
        _ = G₂ := by rw [hc, ← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.mem_span_pair.mpr ⟨1, Kd.sqrtNeg d, by rw [h1, one_smul]⟩
    · exact Submodule.mem_span_pair.mpr ⟨1, -Kd.sqrtNeg d, by rw [h2, one_smul, neg_smul,
        ← sub_eq_add_neg]⟩

/-- `HW_P` is `2`-dimensional (§6.4). -/
theorem finrank_HWP (hd : 0 < d) : Module.finrank ℚ P.HWP = 2 := by
  obtain ⟨h1, h2⟩ := P.s62_tmul_u hd
  have hs0 := s62_sqrtNeg_ne_zero d hd
  set g₁ := reS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁ - d • (imS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁)
  set g₂ := reS n d P.u₁ ⊗ₜ[ℚ] imS n d P.u₁ + imS n d P.u₁ ⊗ₜ[ℚ] reS n d P.u₁
  -- `u₁ ⊗ u₁` and `u₂ ⊗ u₂` are linearly independent
  have hU : LinearIndependent (Kd d) ![P.u₁ ⊗ₜ[Kd d] P.u₁, P.u₂ ⊗ₜ[Kd d] P.u₂] := by
    have := (P.linIndep.tmul_of_isDomain P.linIndep).comp (fun i : Fin 2 => (i, i))
      (fun i j h => (Prod.ext_iff.mp h).1)
    convert this using 1
    funext i; fin_cases i <;> rfl
  -- hence so are the two generators of `HW_P`
  have hg : LinearIndependent ℚ ![g₁, g₂] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have h := congrArg (bcSS n d) hαβ
    rw [map_add, map_smul, map_smul, map_zero, ← algebraMap_smul (Kd d) α,
      ← algebraMap_smul (Kd d) β] at h
    have hc : (2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d = 2⁻¹ := by field_simp
    have h' : (algebraMap ℚ (Kd d) α * 2⁻¹ + algebraMap ℚ (Kd d) β * (2 * Kd.sqrtNeg d)⁻¹) •
        (P.u₁ ⊗ₜ[Kd d] P.u₁) + (algebraMap ℚ (Kd d) α * 2⁻¹ -
          algebraMap ℚ (Kd d) β * (2 * Kd.sqrtNeg d)⁻¹) • (P.u₂ ⊗ₜ[Kd d] P.u₂) = 0 := by
      rw [h1, h2, ← h]
      have e : ∀ (a b : Kd d) (x y : S (Kd d) n ⊗[Kd d] S (Kd d) n),
          (a * 2⁻¹ + b * (2 * Kd.sqrtNeg d)⁻¹) • (x + Kd.sqrtNeg d • y) +
            (a * 2⁻¹ - b * (2 * Kd.sqrtNeg d)⁻¹) • (x - Kd.sqrtNeg d • y) =
          a • x + (b * (2 * ((2 * Kd.sqrtNeg d)⁻¹ * Kd.sqrtNeg d))) • y := by
        intro a b x y; module
      rw [e, hc, mul_inv_cancel₀ two_ne_zero, mul_one]
    obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hU _ _ h'
    have hα : algebraMap ℚ (Kd d) α = 0 := by linear_combination ha + hb
    have hβ : algebraMap ℚ (Kd d) β * (2 * Kd.sqrtNeg d)⁻¹ = 0 := by linear_combination (ha - hb) / 2
    refine ⟨(map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp hα, ?_⟩
    rcases mul_eq_zero.mp hβ with h | h
    · exact (map_eq_zero_iff _ (algebraMap ℚ (Kd d)).injective).mp h
    · exact absurd h (inv_ne_zero (mul_ne_zero two_ne_zero hs0))
  have hrange : ({g₁, g₂} : Set (S ℚ n ⊗[ℚ] S ℚ n)) = Set.range ![g₁, g₂] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [HWP, hrange, finrank_span_eq_card hg, Fintype.card_fin]

include P in
/-- A rational `K`-secant needs `n ≥ 1`: `S_K` has dimension `1` for `n = 0`. -/
theorem s62_n_pos : 0 < n := by
  by_contra h
  obtain rfl : n = 0 := by omega
  have : Module.Finite (Kd d) (S (Kd d) 0) := Module.Finite.of_basis (basisS (Kd d) 0)
  have hle := P.linIndep.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis (basisS (Kd d) 0), Fintype.card_fin, Fintype.card_finset,
    Fintype.card_fin] at hle
  norm_num at hle

/-- `χ₁ χ₂ = 1` on `Spin(V_K)_{ℓ₁,ℓ₂}`: the Mukai pairing is invariant and `(u₁, u₂)_S ≠ 0` for
non-isotropic `P` ([Chevalley, III.2.4]). -/
theorem s62_χ₁_mul_χ₂ (hd : 0 < d) (hP : ¬ P.IsIsotropic) (g : P.spinL₁L₂) :
    P.χ₁ g * P.χ₂ g = 1 := by
  have h1 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.χ₁ g • P.u₁ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).1)
  have h2 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₂ = P.χ₂ g • P.u₂ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).2)
  -- the Mukai pairing is `Spin(V)`-invariant ((5.2.2))
  have hinv := (equation5_2_2 (Kd d) n g (tau (Kd d) n P.u₁) P.u₂).2.1
  rw [tau_tau, h1, h2] at hinv
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hinv
  -- `(u₁, u₂)_S ≠ 0` ([Chevalley, III.2.4]): `W₁ ∩ W₂ = 0`
  have hne : mukai (Kd d) n P.u₁ P.u₂ ≠ 0 := by
    rw [Ne, chevalley_III_2_4 (Kd d) n P.s62_n_pos P.u₁ P.u₂ P.isPure P.isPure₂, not_not]
    exact (P.isCompl_of_not_isIsotropic hd hP).inf_eq_bot
  rw [← mul_assoc, mul_comm (P.χ₂ g)] at hinv
  exact mul_right_cancel₀ hne (hinv.trans (one_mul _).symm)

/-- (§6.4, TeX lines 2862–2863) "The subspace `P ⊗ P` of `S⁺_ℚ ⊗ S⁺_ℚ` is a trivial
`Spin(V_ℚ)_P`-subrepresentation" (for the action `m ⊗ m`, the one intertwined with `ρ'` by `φ'`). -/
theorem map_m_tmul_of_mem_Pℚ (g : Spin ℚ n) (hg : g ∈ P.spinPℚ) (p q : S ℚ n) (hp : p ∈ P.Pℚ)
    (hq : q ∈ P.Pℚ) :
    TensorProduct.map (m ℚ n (g : C ℚ n)) (m ℚ n (g : C ℚ n)) (p ⊗ₜ[ℚ] q) = p ⊗ₜ[ℚ] q := by
  rw [TensorProduct.map_tmul, hg p hp, hg q hq]

/-- (§6.4, TeX lines 2863–2865; §2.2 "`ℓ̃₁ ⊗ ℓ̃₁ ≅ det₁`") `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `ℓ̃₁^{⊗2}` by the
character `det₁`. -/
theorem map_m_u₁_tmul_u₁ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₁ ⊗ₜ[Kd d] P.u₁) =
      P.det₁ g • (P.u₁ ⊗ₜ[Kd d] P.u₁) := by
  -- `ℓ̃₁ ⊗ ℓ̃₁ ≅ χ₁² = det₁`
  have h1 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.χ₁ g • P.u₁ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).1)
  rw [TensorProduct.map_tmul, h1, TensorProduct.smul_tmul_smul, ← P.χ₁_sq hd hW g, sq]

/-- (§6.4) `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `ℓ̃₂^{⊗2}` by the character `det₂`. -/
theorem map_m_u₂_tmul_u₂ (hd : 0 < d) (hW : P.W₁ ⊓ P.W₂ = ⊥) (g : P.spinL₁L₂) :
    TensorProduct.map (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n))
        (m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n)) (P.u₂ ⊗ₜ[Kd d] P.u₂) =
      P.det₂ g • (P.u₂ ⊗ₜ[Kd d] P.u₂) := by
  have h2 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₂ = P.χ₂ g • P.u₂ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).2)
  rw [TensorProduct.map_tmul, h2, TensorProduct.smul_tmul_smul, ← P.χ₂_sq hd hW g, sq]

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
  have h1 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₁ = P.χ₁ g • P.u₁ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).1)
  have h2 : m (Kd d) n ((g : Spin (Kd d) n) : C (Kd d) n) P.u₂ = P.χ₂ g • P.u₂ :=
    Classical.choose_spec ((Subgroup.mem_inf.mp g.2).2)
  have h12 := P.s62_χ₁_mul_χ₂ hd hP g
  refine ⟨?_, ?_⟩
  · rw [TensorProduct.map_tmul, h1, h2, TensorProduct.smul_tmul_smul, h12, one_smul]
  · rw [TensorProduct.map_tmul, h1, h2, TensorProduct.smul_tmul_smul, mul_comm (P.χ₂ g), h12,
      one_smul]

/-- (§6.4, TeX line 2864) "the two non-trivial distinct ... characters `ℓ̃₁^{⊗2}`, `ℓ̃₂^{⊗2}`":
`det₁` is non-trivial on `Spin(V_K)_{ℓ₁,ℓ₂}` and differs from `det₂`. -/
theorem exists_det₁_ne (hd : 0 < d) (hP : ¬ P.IsIsotropic) :
    (∃ g : P.spinL₁L₂, P.det₁ g ≠ 1) ∧ ∃ g : P.spinL₁L₂, P.det₁ g ≠ P.det₂ g := by
  -- `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` maps onto the automorphisms of `W₁` of square determinant
  -- ([Igusa, Lemma 1], §2.2); take the preimage of `2 · id_{W₁}`
  have hW := (P.isCompl_of_not_isIsotropic hd hP).inf_eq_bot
  have hn := P.s62_n_pos
  have hfr : Module.finrank (Kd d) P.W₁ = 2 * n := P.isPure.2.2
  let A : (Module.End (Kd d) P.W₁)ˣ :=
    Units.map (algebraMap (Kd d) (Module.End (Kd d) P.W₁)).toMonoidHom (Units.mk0 2 two_ne_zero)
  have hdetA : LinearMap.det (A : Module.End (Kd d) P.W₁) = 2 ^ (2 * n) := by
    simp only [A, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_mk0,
      Algebra.algebraMap_eq_smul_one, LinearMap.det_smul, hfr, map_one, mul_one]
  have hA : A ∈ (P.restrictW₁.range : Set (Module.End (Kd d) P.W₁)ˣ) := by
    rw [P.range_restrictW₁ hd hW]
    show IsSquare (LinearMap.det (A : Module.End (Kd d) P.W₁))
    rw [hdetA]
    exact ⟨2 ^ n, by ring⟩
  obtain ⟨g, hg⟩ := hA
  have hdet₁ : P.det₁ g = 2 ^ (2 * n) := by rw [← P.det_restrictW₁ g, hg, hdetA]
  have h1 : (2 : Kd d) ^ (2 * n) ≠ 1 := by
    have : (2 : ℕ) ^ (2 * n) ≠ 1 := (Nat.one_lt_two_pow (by omega)).ne'
    exact_mod_cast this
  refine ⟨⟨g, by rw [hdet₁]; exact h1⟩, ⟨g, ?_⟩⟩
  rw [P.det₂_eq_inv hd hW g, hdet₁]
  intro h
  have h2 : (2 : Kd d) ^ (2 * n) * 2 ^ (2 * n) = 1 := by
    nth_rewrite 2 [h]; exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
  rw [← pow_add] at h2
  have : (2 : ℕ) ^ (2 * n + 2 * n) ≠ 1 := (Nat.one_lt_two_pow (by omega)).ne'
  exact this (by exact_mod_cast h2)

end KSecant

end HW

/-! ## Helpers for Proposition 6.4.1(2) -/

section Transport

variable {n : ℕ} {d : ℚ}

/-- `m_g` is injective for `g ∈ Spin(V_F)`. -/
theorem s62_m_injective {F : Type*} [Field F] [CharZero F] (g : Spin F n) :
    Function.Injective (m F n (g : C F n)) := by
  intro x y hxy
  have h : ∀ z, m F n ((g⁻¹ : Spin F n) : C F n) (m F n (g : C F n) z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel,
      OneMemClass.coe_one, map_one, Module.End.one_apply]
  rw [← h x, ← h y, hxy]

/-- (Proof of Proposition 6.4.1(2)) "The group `Spin(V_K)` acts transitively on the set of ordered
pairs of complementary maximally isotropic subspaces of `V_K`. The weight is invariant under the
`Spin(V_K)`-action": the weight of `φ'(u₁ ⊗ u₂ - c u₂ ⊗ u₁)` is that of
`φ'([pt] ⊗ 1 - c 1 ⊗ [pt])`. -/
theorem s62_weight_transport (P : KSecant n d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) (c : Kd d)
    (k : ℕ)
    (h : HasWeight (Kd d) n (Submodule.span (Kd d) {phiPrime (Kd d) n (pt (Kd d) n ⊗ₜ[Kd d]
      (1 : S (Kd d) n) - c • ((1 : S (Kd d) n) ⊗ₜ[Kd d] pt (Kd d) n))}) k) :
    HasWeight (Kd d) n (Submodule.span (Kd d)
      {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ - c • (P.u₂ ⊗ₜ[Kd d] P.u₁))}) k := by
  -- some `g ∈ Spin(V_K)` maps `(ker m_{[pt]}, ker m_1)` to `(W₁, W₂)` ([Chevalley, §3.3, Lemma 1])
  obtain ⟨g, hg₁, hg₂⟩ := chevalley_sec3_3_lemma1 (Kd d) n (pt (Kd d) n) 1 P.u₁ P.u₂
    (s62_isEvenPureSpinor_pt _ n) (s62_isEvenPureSpinor_one _ n) P.isPure P.isPure₂
    (s62_ann_pt_inf_ann_one _ n) (P.isCompl_of_not_isIsotropic hd hP).inf_eq_bot
  -- hence `m_g [pt] ∈ ℓ̃₁` and `m_g 1 ∈ ℓ̃₂` ([Chevalley, III.1.4])
  have ha := chevalley_III_1_4_unique (Kd d) n P.u₁ (m (Kd d) n (g : C (Kd d) n) (pt (Kd d) n))
    P.u₁_ne_zero P.isPure.2 (by rw [ann_m_spin, hg₁])
  have hb := chevalley_III_1_4_unique (Kd d) n P.u₂ (m (Kd d) n (g : C (Kd d) n) 1)
    (P.isPure₂.ne_zero P.s62_n_pos) P.isPure₂.2 (by rw [ann_m_spin, hg₂])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact s62_pt_ne_zero _ n (s62_m_injective g (by rw [← ha, map_zero]))
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact one_ne_zero (s62_m_injective g (by rw [← hb, map_zero]))
  -- `(m_g ⊗ m_g)([pt] ⊗ 1 - c 1 ⊗ [pt]) = ab (u₁ ⊗ u₂ - c u₂ ⊗ u₁)`
  have hz : TensorProduct.map (m (Kd d) n (g : C (Kd d) n)) (m (Kd d) n (g : C (Kd d) n))
      (pt (Kd d) n ⊗ₜ[Kd d] (1 : S (Kd d) n) - c • ((1 : S (Kd d) n) ⊗ₜ[Kd d] pt (Kd d) n)) =
      (a * b) • (P.u₁ ⊗ₜ[Kd d] P.u₂ - c • (P.u₂ ⊗ₜ[Kd d] P.u₁)) := by
    rw [map_sub, map_smul, TensorProduct.map_tmul, TensorProduct.map_tmul, ← ha, ← hb,
      TensorProduct.smul_tmul_smul, TensorProduct.smul_tmul_smul, mul_comm b a, smul_comm c,
      ← smul_sub]
  have key : phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ - c • (P.u₂ ⊗ₜ[Kd d] P.u₁)) =
      (a * b)⁻¹ • rhoPrime (Kd d) n g (phiPrime (Kd d) n (pt (Kd d) n ⊗ₜ[Kd d] (1 : S (Kd d) n) -
        c • ((1 : S (Kd d) n) ⊗ₜ[Kd d] pt (Kd d) n))) := by
    rw [← s62_phiPrime_map, hz, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero ha0 hb0),
      one_smul]
  rw [key, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (mul_ne_zero ha0 hb0))),
    ← Set.image_singleton, ← Submodule.map_span]
  exact h.map_rhoPrime (Kd d) n g

end Transport

/-! ## Helpers for Proposition 6.4.1(1) -/

section Line

variable {n : ℕ} {d : ℚ}

theorem s62_pqPiece_zero_right {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (p : ℕ) : pqPiece A B p 0 = topWedge A p := by
  unfold pqPiece topWedge
  congr 1
  ext x
  constructor
  · rintro ⟨a, b, ha, -, rfl⟩
    exact ⟨a, ha, by rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, Fin.elim0, hv, fun j => j.elim0, by rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]⟩

theorem s62_pqPiece_zero_left {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (q : ℕ) : pqPiece A B 0 q = topWedge B q := by
  unfold pqPiece topWedge
  congr 1
  ext x
  constructor
  · rintro ⟨a, b, -, hb, rfl⟩
    exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Fin.elim0, v, fun j => j.elim0, hv, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul]⟩

/-- In an independent family of three submodules, `x + y = 0` with `x ∈ p 1`, `y ∈ p 2` forces
`x = y = 0`. -/
theorem s62_indep_three {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Fin 3 → Submodule R M} (hp : iSupIndep p) {i j : Fin 3} (hij : i ≠ j) {x y : M}
    (hx : x ∈ p i) (hy : y ∈ p j) (h : x + y = 0) : x = 0 ∧ y = 0 := by
  have hx' : x ∈ p i ⊓ ⨆ k ≠ i, p k := by
    refine ⟨hx, ?_⟩
    rw [eq_neg_of_add_eq_zero_left h]
    exact neg_mem (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm hij) hy))
  have hx0 : x = 0 := by rw [(hp i).eq_bot] at hx'; exact (Submodule.mem_bot R).mp hx'
  exact ⟨hx0, by rw [hx0, zero_add] at h; exact h⟩

/-- The lowest-degree analysis of `φ'(u ⊗ u)` for a line `ℓ̃ = K u ⊆ P_K` on which
`Spin(V_K)_{ℓ₁,ℓ₂}` acts on `ℓ̃^{⊗2}` by a non-trivial character `χ` (proof of Proposition 6.4.1(1)):
`φ'(u ⊗ u) ∈ F_{2n}`, and its degree-`2n` part is a non-zero `Spin(V)_P`-invariant on which
`Spin(V_K)_{ℓ₁,ℓ₂}` acts by `χ`. -/
theorem s62_line (P : KSecant n d) (hd : 0 < d) (hP : ¬ P.IsIsotropic) {u : S (Kd d) n}
    (hu : u ∈ P.PK) (hu0 : u ⊗ₜ[Kd d] u ≠ 0) (χ : P.spinL₁L₂ → Kd d)
    (hχ : ∀ h : P.spinL₁L₂, TensorProduct.map (m (Kd d) n ((h : Spin (Kd d) n) : C (Kd d) n))
      (m (Kd d) n ((h : Spin (Kd d) n) : C (Kd d) n)) (u ⊗ₜ[Kd d] u) = χ h • (u ⊗ₜ[Kd d] u))
    (hχ1 : ∃ h, χ h ≠ 1) :
    phiPrime (Kd d) n (u ⊗ₜ[Kd d] u) ∈ extFiltGE (Kd d) n (2 * n) ∧
      projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (u ⊗ₜ[Kd d] u)) ∈ P.invK (2 * n) ∧
      projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (u ⊗ₜ[Kd d] u)) ≠ 0 ∧
      ∀ h : P.spinL₁L₂, rhoExt (Kd d) n h
          (projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (u ⊗ₜ[Kd d] u))) =
        χ h • projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (u ⊗ₜ[Kd d] u)) := by
  obtain ⟨x, hxdef⟩ : ∃ x, phiPrime (Kd d) n (u ⊗ₜ[Kd d] u) = x := ⟨_, rfl⟩
  rw [hxdef]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hu0
    have h1 : phiPrimeInv (Kd d) n x = u ⊗ₜ[Kd d] u := by
      rw [← hxdef, ← LinearMap.comp_apply (phiPrimeInv (Kd d) n) (phiPrime (Kd d) n),
        phiPrimeInv_comp_phiPrime, LinearMap.id_apply]
    rw [← h1, h0, map_zero]
  -- the lowest degree `k` of `x`
  have hex : ∃ k, projDeg (Kd d) n k x ≠ 0 := by
    by_contra h
    push Not at h
    have hx := s62_mem_of_projDeg (Kd d) n 0 x fun j _ => h j
    exact hx0 (by rw [← s62_projDeg_self (Kd d) n hx, h 0])
  classical
  set k := Nat.find hex
  have hk : projDeg (Kd d) n k x ≠ 0 := Nat.find_spec hex
  have hlow : ∀ j < k, projDeg (Kd d) n j x = 0 := fun j hj => not_not.mp (Nat.find_min hex hj)
  have hxk : x ∈ extFiltGE (Kd d) n k := (s62_mem_extFiltGE_iff (Kd d) n k x).mpr hlow
  -- `Spin(V_K)_{ℓ₁,ℓ₂}` acts on `x_k` by `χ`
  have hchar : ∀ h : P.spinL₁L₂, rhoExt (Kd d) n h (projDeg (Kd d) n k x) =
      χ h • projDeg (Kd d) n k x := fun h => by
    rw [← rhoPrime_projDeg _ _ _ k hxk, ← hxdef, ← s62_phiPrime_map, hχ h, map_smul, map_smul]
  -- `x_k` is `Spin(V)_P`-invariant
  have hinv : projDeg (Kd d) n k x ∈ P.invK k := by
    refine ⟨s62_projDeg_mem _ _ k x, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    rw [← rhoPrime_projDeg _ _ _ k hxk, ← hxdef, ← s62_phiPrime_map, TensorProduct.map_tmul,
      s62_m_fix P g hg hu]
  -- the weight is `2n`: below the middle degree the invariants are trivial characters
  have hk2 : k = 2 * n := by
    by_contra hk2
    obtain ⟨h, hh⟩ := hχ1
    have h1 := P.s62_invK_trivial hd hP hk2 hinv h
    rw [hchar h] at h1
    have h2 : (χ h - 1) • projDeg (Kd d) n k x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact hk ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hh))
  rw [hk2] at hk hxk hchar hinv
  exact ⟨hxk, hinv, hk, hchar⟩

end Line

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
  have hd := hP.pos
  have hP' := hP.nonIsotropic
  have hW := (P.isCompl_of_not_isIsotropic hd hP').inf_eq_bot
  have hu0 : P.u₁ ⊗ₜ[Kd d] P.u₁ ≠ 0 := (P.linIndep.tmul_of_isDomain P.linIndep).ne_zero (0, 0)
  obtain ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩ := P.exists_det₁_ne hd hP'
  -- `φ'(ℓ̃₁²)` has weight `2n`; its projection `v` is invariant and transforms by `det₁`
  obtain ⟨hF, hinv, hne, hchar⟩ := s62_line P hd hP'
    (Submodule.subset_span (Set.mem_insert _ _)) hu0 P.det₁
    (fun h => P.map_m_u₁_tmul_u₁ hd hW h) ⟨h₁, hh₁⟩
  refine ⟨hF, ?_⟩
  -- `(⋀^{2n} V_K)^{Spin(V)_P} = det₁ ⊕ det₂ ⊕ 1` (Lemma 2.2.7): `v` lies in `⋀^{2n} W₁`
  have hv := hinv
  rw [lemma2_2_7_K_eq P hd hP'] at hv
  obtain ⟨y, hy, l, hl, hyl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := Submodule.mem_sup.mp hy
  have hind := lemma2_2_7_K_indep P hd hP'
  have key : ∀ h, (P.det₂ h - P.det₁ h) • a₂ + (1 - P.det₁ h) • l = 0 := by
    intro h
    have e1 := hchar h
    rw [← hyl, ← ha, map_add, map_add, lemma2_2_7_K_det₁ P hd hP' h a₁ ha₁,
      lemma2_2_7_K_det₂ P hd hP' h a₂ ha₂, lemma2_2_7_K_trivial P hd hP' h l hl] at e1
    calc (P.det₂ h - P.det₁ h) • a₂ + (1 - P.det₁ h) • l
        = (P.det₁ h • a₁ + P.det₂ h • a₂ + l) - P.det₁ h • (a₁ + a₂ + l) := by module
      _ = 0 := by rw [e1, sub_self]
  have hl0 : l = 0 := by
    have := (s62_indep_three hind (i := 1) (j := 2) (by decide)
      (Submodule.smul_mem _ _ ha₂) (Submodule.smul_mem _ _ hl) (key h₁)).2
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hh₁))
  have ha₂0 : a₂ = 0 := by
    have := (s62_indep_three hind (i := 1) (j := 2) (by decide)
      (Submodule.smul_mem _ _ ha₂) (Submodule.smul_mem _ _ hl) (key h₂)).1
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hh₂))
  have hv1 : projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁)) ∈
      pqPiece P.W₁ P.W₂ (2 * n) 0 := by
    rw [← hyl, ← ha, ha₂0, hl0, add_zero, add_zero]; exact ha₁
  -- `⋀^{2n} W₁` is a line, spanned by `v ≠ 0`
  have : Module.Finite (Kd d) (ExtV (Kd d) n) := Module.Finite.of_basis (basisExt (Kd d) n)
  rw [Submodule.map_span, Set.image_singleton, ← s62_pqPiece_zero_right _ P.W₂]
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hv1)
  rw [finrank_span_singleton hne, (lemma2_2_7_K_finrank P hd hP').1]

/-- **Proposition 6.4.1(1)**, for the line `ℓ̃₂`: `φ'(ℓ̃₂ ⊗ ℓ̃₂) ∈ F_{2n}` and its projection to
`H^{2n}` is `⋀^{2n} W₂`. -/
theorem proposition6_4_1_1_line₂ (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) :
    phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂) ∈ extFiltGE (Kd d) n (2 * n) ∧
      (Submodule.span (Kd d) {phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)}).map
          (projDeg (Kd d) n (2 * n)) = topWedge P.W₂ (2 * n) := by
  have hd := hP.pos
  have hP' := hP.nonIsotropic
  have hW := (P.isCompl_of_not_isIsotropic hd hP').inf_eq_bot
  have hu0 : P.u₂ ⊗ₜ[Kd d] P.u₂ ≠ 0 := (P.linIndep.tmul_of_isDomain P.linIndep).ne_zero (1, 1)
  obtain ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩ := P.exists_det₁_ne hd hP'
  have hh₁' : P.det₂ h₁ ≠ 1 := by
    rw [P.det₂_eq_inv hd hW]; exact fun h => hh₁ (inv_eq_one.mp h)
  -- `φ'(ℓ̃₂²)` has weight `2n`; its projection `v` is invariant and transforms by `det₂`
  obtain ⟨hF, hinv, hne, hchar⟩ := s62_line P hd hP'
    (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hu0 P.det₂
    (fun h => P.map_m_u₂_tmul_u₂ hd hW h) ⟨h₁, hh₁'⟩
  refine ⟨hF, ?_⟩
  have hv := hinv
  rw [lemma2_2_7_K_eq P hd hP'] at hv
  obtain ⟨y, hy, l, hl, hyl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := Submodule.mem_sup.mp hy
  have hind := lemma2_2_7_K_indep P hd hP'
  have key : ∀ h, (P.det₁ h - P.det₂ h) • a₁ + (1 - P.det₂ h) • l = 0 := by
    intro h
    have e1 := hchar h
    rw [← hyl, ← ha, map_add, map_add, lemma2_2_7_K_det₁ P hd hP' h a₁ ha₁,
      lemma2_2_7_K_det₂ P hd hP' h a₂ ha₂, lemma2_2_7_K_trivial P hd hP' h l hl] at e1
    calc (P.det₁ h - P.det₂ h) • a₁ + (1 - P.det₂ h) • l
        = (P.det₁ h • a₁ + P.det₂ h • a₂ + l) - P.det₂ h • (a₁ + a₂ + l) := by module
      _ = 0 := by rw [e1, sub_self]
  have hl0 : l = 0 := by
    have := (s62_indep_three hind (i := 0) (j := 2) (by decide)
      (Submodule.smul_mem _ _ ha₁) (Submodule.smul_mem _ _ hl) (key h₁)).2
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hh₁'))
  have ha₁0 : a₁ = 0 := by
    have := (s62_indep_three hind (i := 0) (j := 2) (by decide)
      (Submodule.smul_mem _ _ ha₁) (Submodule.smul_mem _ _ hl) (key h₂)).1
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hh₂)
  have hv2 : projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)) ∈
      pqPiece P.W₁ P.W₂ 0 (2 * n) := by
    rw [← hyl, ← ha, ha₁0, hl0, zero_add, add_zero]; exact ha₂
  have : Module.Finite (Kd d) (ExtV (Kd d) n) := Module.Finite.of_basis (basisExt (Kd d) n)
  rw [Submodule.map_span, Set.image_singleton, ← s62_pqPiece_zero_left P.W₁]
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hv2)
  rw [finrank_span_singleton hne, (lemma2_2_7_K_finrank P hd hP').2.1]

theorem s62_phiPrime_injective (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    Function.Injective (phiPrime F n) := fun y₁ y₂ h => by
  have := congrArg (phiPrimeInv F n) h
  rwa [← LinearMap.comp_apply (phiPrimeInv F n), ← LinearMap.comp_apply (phiPrimeInv F n),
    phiPrimeInv_comp_phiPrime] at this

/-- `Re(u₁), Im(u₁)/√d ∈ P`. -/
theorem s62_reS_imS_mem (P : KSecant n d) (hd : 0 < d) :
    reS n d P.u₁ ∈ P.Pℚ ∧ imS n d P.u₁ ∈ P.Pℚ := by
  have hs0 := s62_sqrtNeg_ne_zero d hd
  have h1 := bcS_reS_add_imS n d hd P.u₁
  have h2 := P.s62_u₂_eq hd
  have hu₁ : P.u₁ ∈ P.PK := Submodule.subset_span (Set.mem_insert _ _)
  have hu₂ : P.u₂ ∈ P.PK := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨a, ha⟩ : ∃ a, bcS ℚ (Kd d) n (reS n d P.u₁) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, bcS ℚ (Kd d) n (imS n d P.u₁) = b := ⟨_, rfl⟩
  rw [ha, hb] at h1 h2
  constructor
  · show bcS ℚ (Kd d) n (reS n d P.u₁) ∈ P.PK
    have : a = (2 : Kd d)⁻¹ • P.u₁ + (2 : Kd d)⁻¹ • P.u₂ := by
      rw [h2, ← h1]
      module
    rw [ha, this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu₁) (Submodule.smul_mem _ _ hu₂)
  · show bcS ℚ (Kd d) n (imS n d P.u₁) ∈ P.PK
    have : b = (2 * Kd.sqrtNeg d)⁻¹ • P.u₁ - (2 * Kd.sqrtNeg d)⁻¹ • P.u₂ := by
      rw [h2, ← h1, ← smul_sub,
        show a + Kd.sqrtNeg d • b - (a - Kd.sqrtNeg d • b) = (2 * Kd.sqrtNeg d) • b by module,
        smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hs0), one_smul]
    rw [hb, this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu₁) (Submodule.smul_mem _ _ hu₂)

/-- `φ'(HW_P)` is fixed by `Spin(V)_P` (`HW_P ⊆ P ⊗ P`). -/
theorem s62_HWP_stable (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    ∀ g ∈ P.spinPZ, ∀ x ∈ P.HWP.map (phiPrime ℚ n),
      rhoPrime ℚ n g x ∈ P.HWP.map (phiPrime ℚ n) := by
  obtain ⟨hp₁, hp₂⟩ := s62_reS_imS_mem P hP.pos
  intro g hg x hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  rw [← hyx]
  have hg' := (Subgroup.mem_inf.mp hg).2
  have hfix : P.HWP ≤ LinearMap.eqLocus (TensorProduct.map (m ℚ n (g : C ℚ n))
      (m ℚ n (g : C ℚ n))) LinearMap.id := by
    rw [KSecant.HWP, Submodule.span_le]
    rintro _ (rfl | rfl)
    · show TensorProduct.map _ _ _ = _
      rw [map_sub, map_smul, P.map_m_tmul_of_mem_Pℚ g hg' _ _ hp₁ hp₁,
        P.map_m_tmul_of_mem_Pℚ g hg' _ _ hp₂ hp₂]
      rfl
    · show TensorProduct.map _ _ _ = _
      rw [map_add, P.map_m_tmul_of_mem_Pℚ g hg' _ _ hp₁ hp₂,
        P.map_m_tmul_of_mem_Pℚ g hg' _ _ hp₂ hp₁]
      rfl
  rw [← s62_phiPrime_map, show TensorProduct.map (m ℚ n (g : C ℚ n)) (m ℚ n (g : C ℚ n)) y = y
    from hfix hy]
  exact Submodule.mem_map_of_mem hy

/-- The base change of `φ'(y)`, `y ∈ HW_P`, is `c₁ φ'(u₁ ⊗ u₁) + c₂ φ'(u₂ ⊗ u₂)`
("`φ'` is defined over `ℚ`"). -/
theorem s62_HWP_bc (P : KSecant n d) (hd : 0 < d) (y : S ℚ n ⊗[ℚ] S ℚ n) (hy : y ∈ P.HWP) :
    ∃ c₁ c₂ : Kd d, bcExt ℚ (Kd d) n (phiPrime ℚ n y) =
      c₁ • phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁) + c₂ • phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂) := by
  have hmem : bcSS n d y ∈ Submodule.span (Kd d) (bcSS n d '' P.HWP) :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  rw [P.span_bcSS_HWP hd, Submodule.mem_span_pair] at hmem
  obtain ⟨c₁, c₂, hc⟩ := hmem
  exact ⟨c₁, c₂, by rw [s62_bcExt_phiPrime, ← hc, map_add, map_smul, map_smul]⟩

theorem s62_HWP_F (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (y : S ℚ n ⊗[ℚ] S ℚ n) (hy : y ∈ P.HWP) : phiPrime ℚ n y ∈ extFiltGE ℚ n (2 * n) := by
  obtain ⟨hF₁, -⟩ := proposition6_4_1_1_line₁ P J hP
  obtain ⟨hF₂, -⟩ := proposition6_4_1_1_line₂ P J hP
  obtain ⟨c₁, c₂, hc⟩ := s62_HWP_bc P hP.pos y hy
  rw [s62_mem_extFiltGE_iff]
  intro j hj
  apply s62_bcExt_injective ℚ (Kd d) n
  rw [map_zero, ← s62_projDeg_bcExt, hc, map_add, map_smul, map_smul,
    (s62_mem_extFiltGE_iff _ _ _ _).mp hF₁ j hj, (s62_mem_extFiltGE_iff _ _ _ _).mp hF₂ j hj,
    smul_zero, smul_zero, add_zero]

/-- The degree-`2n` parts `v₁, v₂` of `φ'(uᵢ ⊗ uᵢ)` span `⋀^{2n} Wᵢ`. -/
theorem s62_HWP_v (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁)) ∈ topWedge P.W₁ (2 * n) ∧
      projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₁)) ≠ 0 ∧
      projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)) ∈ topWedge P.W₂ (2 * n) ∧
      projDeg (Kd d) n (2 * n) (phiPrime (Kd d) n (P.u₂ ⊗ₜ[Kd d] P.u₂)) ≠ 0 := by
  have hd := hP.pos
  have hP' := hP.nonIsotropic
  obtain ⟨-, hl₁⟩ := proposition6_4_1_1_line₁ P J hP
  obtain ⟨-, hl₂⟩ := proposition6_4_1_1_line₂ P J hP
  rw [Submodule.map_span, Set.image_singleton] at hl₁ hl₂
  refine ⟨hl₁ ▸ Submodule.mem_span_singleton_self _, ?_, hl₂ ▸ Submodule.mem_span_singleton_self _,
    ?_⟩
  · intro h; rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at hl₁
    have := (lemma2_2_7_K_finrank P hd hP').1
    rw [s62_pqPiece_zero_right, ← hl₁, finrank_bot] at this; exact zero_ne_one this
  · intro h; rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at hl₂
    have := (lemma2_2_7_K_finrank P hd hP').2.1
    rw [s62_pqPiece_zero_left, ← hl₂, finrank_bot] at this; exact zero_ne_one this

/-- `φ'(HW_P) ∩ F_{2n+1} = 0`: the degree-`2n` part of `φ'(y)`, `y ∈ HW_P`, vanishes only if
`φ'(y) = 0` (`⋀^{2n} W₁ ∩ ⋀^{2n} W₂ = 0`). -/
theorem s62_HWP_inj (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (y : S ℚ n ⊗[ℚ] S ℚ n) (hy : y ∈ P.HWP) (h0 : projDeg ℚ n (2 * n) (phiPrime ℚ n y) = 0) :
    phiPrime ℚ n y = 0 := by
  have hd := hP.pos
  have hP' := hP.nonIsotropic
  obtain ⟨hv₁, hv₁0, hv₂, hv₂0⟩ := s62_HWP_v P J hP
  have hind := lemma2_2_7_K_indep P hd hP'
  rw [s62_pqPiece_zero_right, s62_pqPiece_zero_left] at hind
  obtain ⟨c₁, c₂, hc⟩ := s62_HWP_bc P hd y hy
  have h1 := congrArg (bcExt ℚ (Kd d) n) h0
  rw [map_zero, ← s62_projDeg_bcExt, hc, map_add, map_smul, map_smul] at h1
  obtain ⟨h₁, h₂⟩ := s62_indep_three hind (i := 0) (j := 1) (by decide)
    (Submodule.smul_mem _ c₁ hv₁) (Submodule.smul_mem _ c₂ hv₂) h1
  have hc₁ := (smul_eq_zero.mp h₁).resolve_right hv₁0
  have hc₂ := (smul_eq_zero.mp h₂).resolve_right hv₂0
  apply s62_bcExt_injective ℚ (Kd d) n
  rw [hc, hc₁, hc₂, zero_smul, zero_smul, add_zero, map_zero]

theorem s62_HWP_inf (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J) :
    P.HWP.map (phiPrime ℚ n) ⊓ extFiltGE ℚ n (2 * n + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hz1
  rw [← hyz] at hz2 ⊢
  exact (Submodule.mem_bot ℚ).mpr (s62_HWP_inj P J hP y hy
    ((s62_mem_extFiltGE_iff _ _ _ _).mp hz2 (2 * n) (by omega)))

/-- The degree-`2n` part of `φ'(y)`, `y ∈ HW_P`, is a Hodge–Weil class. -/
theorem s62_HWP_hw (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n)) (hP : Assumption2_4_1 P J)
    (y : S ℚ n ⊗[ℚ] S ℚ n) (hy : y ∈ P.HWP) :
    projDeg ℚ n (2 * n) (phiPrime ℚ n y) ∈ P.hwPlane := by
  obtain ⟨hv₁, -, hv₂, -⟩ := s62_HWP_v P J hP
  obtain ⟨c₁, c₂, hc⟩ := s62_HWP_bc P hP.pos y hy
  show bcExt ℚ (Kd d) n (projDeg ℚ n (2 * n) (phiPrime ℚ n y)) ∈
    topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n)
  rw [← s62_projDeg_bcExt, hc, map_add, map_smul, map_smul]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hv₁) (Submodule.smul_mem _ _ hv₂)

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
  have hd := hP.pos
  have hfr := P.finrank_HWP hd
  have hbot := s62_HWP_inf P J hP
  refine ⟨s62_HWP_stable P J hP, ⟨Submodule.map_le_iff_le_comap.mpr fun y hy =>
    s62_HWP_F P J hP y hy, fun hle => ?_⟩, hbot, ?_⟩
  · -- `φ'(HW_P) ≠ 0`
    have hbot' : P.HWP.map (phiPrime ℚ n) = ⊥ := by
      rw [← hbot]; exact (inf_eq_left.mpr hle).symm
    have := Submodule.map_injective_of_injective (s62_phiPrime_injective ℚ n)
      (hbot'.trans (Submodule.map_bot _).symm)
    rw [this, finrank_bot] at hfr
    exact absurd hfr (by norm_num)
  · -- the projection is the rational plane of `⋀^{2n} W₁ ⊕ ⋀^{2n} W₂`
    have hQ : Module.Finite ℚ (ExtV ℚ n) := Module.Finite.of_basis (basisExt ℚ n)
    have hle : (P.HWP.map (phiPrime ℚ n)).map (projDeg ℚ n (2 * n)) ≤ P.hwPlane := by
      intro w hw
      obtain ⟨z, hz, hzw⟩ := Submodule.mem_map.mp hw
      obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hz
      rw [← hzw, ← hyz]
      exact s62_HWP_hw P J hP y hy
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [KSecant.finrank_hwPlane P J hP, ← Submodule.map_comp, ← LinearMap.range_domRestrict,
      LinearMap.finrank_range_of_inj, hfr]
    intro y₁ y₂ h
    have h' : projDeg ℚ n (2 * n) (phiPrime ℚ n ((y₁ : S ℚ n ⊗[ℚ] S ℚ n) - y₂)) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr h
    have := s62_HWP_inj P J hP _ (Submodule.sub_mem _ y₁.2 y₂.2) h'
    exact Subtype.ext (sub_eq_zero.mp (s62_phiPrime_injective ℚ n (by rw [this, map_zero])))

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
  obtain ⟨h2, h0⟩ := phiPrime_one_pt_hasWeight (Kd d) n P.s62_n_pos
  have hn1 : (-1 : Kd d) ^ n = 1 := hn.neg_one_pow
  refine ⟨?_, ?_⟩
  · have := s62_weight_transport P hP.pos hP.nonIsotropic _ 2 h2
    rwa [hn1, one_smul] at this
  · rw [← sub_neg_eq_add, ← neg_smul] at h0
    have := s62_weight_transport P hP.pos hP.nonIsotropic _ 0 h0
    rwa [hn1, neg_smul, one_smul, sub_neg_eq_add] at this

/-- **Proposition 6.4.1(2)** (`prop-the-orlov-image-of-HW-P-projects-into-the-3-dimensional-space-of-HW-classes`),
`n` odd: the weight of `φ'(ℓ₁ · ℓ₂)` is `2` and the weight of `φ'(ℓ₁ ∧ ℓ₂)` is `0`. -/
theorem proposition6_4_1_2_odd (P : KSecant n d) (J : Module.End ℝ (H1 ℝ n))
    (hP : Assumption2_4_1 P J) (hn : Odd n) :
    HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ + P.u₂ ⊗ₜ[Kd d] P.u₁)}) 2 ∧
      HasWeight (Kd d) n (Submodule.span (Kd d)
        {phiPrime (Kd d) n (P.u₁ ⊗ₜ[Kd d] P.u₂ - P.u₂ ⊗ₜ[Kd d] P.u₁)}) 0 := by
  obtain ⟨h2, h0⟩ := phiPrime_one_pt_hasWeight (Kd d) n P.s62_n_pos
  have hn1 : (-1 : Kd d) ^ n = -1 := hn.neg_one_pow
  refine ⟨?_, ?_⟩
  · have := s62_weight_transport P hP.pos hP.nonIsotropic _ 2 h2
    rwa [hn1, neg_smul, one_smul, sub_neg_eq_add] at this
  · rw [← sub_neg_eq_add, ← neg_smul] at h0
    have := s62_weight_transport P hP.pos hP.nonIsotropic _ 0 h0
    rwa [hn1, neg_neg, one_smul] at this

end Prop641

end WeilClasses
