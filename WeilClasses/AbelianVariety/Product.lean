module

public import WeilClasses.AbelianVariety.Lemmas

/-!
# Products of abelian varieties and push-forward along the second projection

For abelian varieties `A₁`, `A₂` of dimensions `g₁`, `g₂` (in the model of `WeilClasses.Defs`,
`H¹(Aᵢ, F) = F^{2gᵢ}`), the product has `H¹(A₁ × A₂, F) = H¹(A₁, F) ⊕ H¹(A₂, F) = F^{2(g₁+g₂)}`,
the first `2 g₁` coordinates being those of `A₁`, and `H*(A₁ × A₂, F) = ⋀•(H¹(A₁) ⊕ H¹(A₂))`
(Künneth). This file defines:

* the pullbacks `prodInl = pr₁^*`, `prodInr = pr₂^*` along the two projections, in the coordinates
  `prodEquiv : H¹(A₁ × A₂) ≃ H¹(A₁) × H¹(A₂)` (whose restrictions to the factors `A₁ × 0`, `0 × A₂`
  are `prodFst`, `prodSnd`);
* the product `AbVar.prod A₁ A₂`, with the complex structure `prodJ J₁ J₂ = J₁ × J₂` and the ample
  class `pr₁^*Θ₁ + pr₂^*Θ₂`;
* the projection formula `pr₂,*(pr₁^*a ∪ pr₂^*b) = (∫_{A₁} a) b` for the push-forward `pushSnd` along
  the second projection (`pushSnd_prodInl_mul_prodInr`), with no sign.

`prodEquiv`, `prodFst`, `prodSnd`, `prodJ`, `pushSnd` and the hypothesis `PushforwardClosed`
(push-forward along the projections `A₁ × A₂ → A₂` maps algebraic classes to algebraic classes) are
defined in `WeilClasses.Defs`, since Corollary 1.6.1 states it.

It also proves what the proof of [Schoen, Prop. 10] in `WeilClasses.External.Voisin.Lemma2_9` uses
about products: the pullbacks `prodInl`, `prodInr` are morphisms of Hodge structures, base change
commutes with the coordinates, double contractions of `pr₁^*ξ₁ + pr₂^*ξ₂` split, and eigenspaces of
block-diagonal endomorphisms are products (so the dimensions in the Weil condition add up).
-/

@[expose] public section

namespace WeilClasses

/-! ### Coordinates on `H¹(A₁ × A₂)` -/

section Coordinates

variable (F : Type*) [Field F] (g₁ g₂ : ℕ)

/-- The pullback `pr₁^* : H¹(A₁) → H¹(A₁ × A₂)` along the first projection. -/
noncomputable def prodInl : H1 F g₁ →ₗ[F] H1 F (g₁ + g₂) :=
  (prodEquiv F g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inl F (H1 F g₁) (H1 F g₂)

/-- The pullback `pr₂^* : H¹(A₂) → H¹(A₁ × A₂)` along the second projection. -/
noncomputable def prodInr : H1 F g₂ →ₗ[F] H1 F (g₁ + g₂) :=
  (prodEquiv F g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inr F (H1 F g₁) (H1 F g₂)

end Coordinates

/-! ### The coordinate maps -/

section CoordinatesAPI

variable {F : Type*} [Field F] {g₁ g₂ : ℕ}

@[simp]
theorem vo_prodEquiv_prodInl (x : H1 F g₁) :
    prodEquiv F g₁ g₂ (prodInl F g₁ g₂ x) = (x, 0) := by
  simp [prodInl]

@[simp]
theorem vo_prodEquiv_prodInr (y : H1 F g₂) :
    prodEquiv F g₁ g₂ (prodInr F g₁ g₂ y) = (0, y) := by
  simp [prodInr]

@[simp]
theorem vo_prodFst_prodInl (x : H1 F g₁) : prodFst F g₁ g₂ (prodInl F g₁ g₂ x) = x := by
  simp [prodFst]

@[simp]
theorem vo_prodSnd_prodInl (x : H1 F g₁) : prodSnd F g₁ g₂ (prodInl F g₁ g₂ x) = 0 := by
  simp [prodSnd]

@[simp]
theorem vo_prodFst_prodInr (y : H1 F g₂) : prodFst F g₁ g₂ (prodInr F g₁ g₂ y) = 0 := by
  simp [prodFst]

@[simp]
theorem vo_prodSnd_prodInr (y : H1 F g₂) : prodSnd F g₁ g₂ (prodInr F g₁ g₂ y) = y := by
  simp [prodSnd]

theorem vo_prodInl_add_prodInr (v : H1 F (g₁ + g₂)) :
    prodInl F g₁ g₂ (prodFst F g₁ g₂ v) + prodInr F g₁ g₂ (prodSnd F g₁ g₂ v) = v := by
  apply (prodEquiv F g₁ g₂).injective
  simp [prodFst, prodSnd]

theorem vo_prodFst_comp_prodInl : prodFst F g₁ g₂ ∘ₗ prodInl F g₁ g₂ = LinearMap.id :=
  LinearMap.ext fun x => by simp

theorem vo_prodSnd_comp_prodInl : prodSnd F g₁ g₂ ∘ₗ prodInl F g₁ g₂ = 0 :=
  LinearMap.ext fun x => by simp

theorem vo_prodFst_comp_prodInr : prodFst F g₁ g₂ ∘ₗ prodInr F g₁ g₂ = 0 :=
  LinearMap.ext fun x => by simp

theorem vo_prodSnd_comp_prodInr : prodSnd F g₁ g₂ ∘ₗ prodInr F g₁ g₂ = LinearMap.id :=
  LinearMap.ext fun x => by simp

theorem vo_prodInl_injective : Function.Injective (prodInl F g₁ g₂) := fun x y h => by
  simpa using congrArg (prodFst F g₁ g₂) h

theorem vo_prodInr_injective : Function.Injective (prodInr F g₁ g₂) := fun x y h => by
  simpa using congrArg (prodSnd F g₁ g₂) h

theorem vo_prodEquiv_apply_fst (x : H1 F (g₁ + g₂)) (j : Fin (2 * g₁)) :
    (prodEquiv F g₁ g₂ x).1 j = x ⟨j, by omega⟩ := rfl

theorem vo_prodEquiv_apply_snd (x : H1 F (g₁ + g₂)) (j : Fin (2 * g₂)) :
    (prodEquiv F g₁ g₂ x).2 j = x ⟨2 * g₁ + j, by omega⟩ := rfl

/-- `pr₁^* eᵢ = eᵢ`: the basis of `H¹(A₁)` is the first part of the basis of `H¹(A₁ × A₂)`. -/
theorem vo_prodInl_e (i : Fin (2 * g₁)) :
    prodInl F g₁ g₂ (e F g₁ i) = e F (g₁ + g₂) ⟨i, by omega⟩ := by
  apply (prodEquiv F g₁ g₂).injective
  rw [vo_prodEquiv_prodInl]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · rw [vo_prodEquiv_apply_fst]
    simp only [e, Pi.single_apply, Fin.ext_iff]
  · rw [vo_prodEquiv_apply_snd]
    have h : 2 * g₁ + (j : ℕ) ≠ i := by omega
    simp [e, Fin.ext_iff, h]

/-- `pr₂^* eⱼ = e_{2g₁ + j}`. -/
theorem vo_prodInr_e (j : Fin (2 * g₂)) :
    prodInr F g₁ g₂ (e F g₂ j) = e F (g₁ + g₂) ⟨2 * g₁ + j, by omega⟩ := by
  apply (prodEquiv F g₁ g₂).injective
  rw [vo_prodEquiv_prodInr]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [vo_prodEquiv_apply_fst]
    have h : (k : ℕ) ≠ 2 * g₁ + j := by omega
    simp [e, Fin.ext_iff, h]
  · rw [vo_prodEquiv_apply_snd]
    simp only [e, Pi.single_apply, Fin.ext_iff]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩

/-- A functional on `H¹(A₁ × A₂)` vanishing on both factors is zero. -/
theorem vo_dual_eq_zero {a : Module.Dual F (H1 F (g₁ + g₂))} (h₁ : a ∘ₗ prodInl F g₁ g₂ = 0)
    (h₂ : a ∘ₗ prodInr F g₁ g₂ = 0) : a = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [← vo_prodInl_add_prodInr v, map_add]
  have e₁ := LinearMap.congr_fun h₁ (prodFst F g₁ g₂ v)
  have e₂ := LinearMap.congr_fun h₂ (prodSnd F g₁ g₂ v)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e₁ e₂
  simp [e₁, e₂]

end CoordinatesAPI

/-! ### Block-diagonal endomorphisms -/

section ProdEnd

variable {F : Type*} [Field F] {g₁ g₂ : ℕ}

/-- The endomorphism `φ₁ × φ₂` of `H¹(A₁ × A₂, F)` (block diagonal in the coordinates). -/
noncomputable def vo_prodEnd (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂)) :
    Module.End F (H1 F (g₁ + g₂)) :=
  (prodEquiv F g₁ g₂).symm.conj (φ₁.prodMap φ₂)

theorem vo_prodJ_eq (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂)) :
    prodJ J₁ J₂ = vo_prodEnd J₁ J₂ := rfl

theorem vo_prodEquiv_prodEnd (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂))
    (v : H1 F (g₁ + g₂)) :
    prodEquiv F g₁ g₂ (vo_prodEnd φ₁ φ₂ v) =
      (φ₁ (prodEquiv F g₁ g₂ v).1, φ₂ (prodEquiv F g₁ g₂ v).2) := by
  simp [vo_prodEnd, LinearEquiv.conj_apply]

@[simp]
theorem vo_prodEnd_prodInl (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂))
    (x : H1 F g₁) : vo_prodEnd φ₁ φ₂ (prodInl F g₁ g₂ x) = prodInl F g₁ g₂ (φ₁ x) := by
  apply (prodEquiv F g₁ g₂).injective
  simp [vo_prodEquiv_prodEnd]

@[simp]
theorem vo_prodEnd_prodInr (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂))
    (y : H1 F g₂) : vo_prodEnd φ₁ φ₂ (prodInr F g₁ g₂ y) = prodInr F g₁ g₂ (φ₂ y) := by
  apply (prodEquiv F g₁ g₂).injective
  simp [vo_prodEquiv_prodEnd]

@[simp]
theorem vo_prodFst_prodEnd (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂))
    (v : H1 F (g₁ + g₂)) : prodFst F g₁ g₂ (vo_prodEnd φ₁ φ₂ v) = φ₁ (prodFst F g₁ g₂ v) := by
  simp [prodFst, vo_prodEquiv_prodEnd]

@[simp]
theorem vo_prodSnd_prodEnd (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂))
    (v : H1 F (g₁ + g₂)) : prodSnd F g₁ g₂ (vo_prodEnd φ₁ φ₂ v) = φ₂ (prodSnd F g₁ g₂ v) := by
  simp [prodSnd, vo_prodEquiv_prodEnd]

theorem vo_prodEnd_ext {L L' : Module.End F (H1 F (g₁ + g₂))}
    (h₁ : ∀ x, L (prodInl F g₁ g₂ x) = L' (prodInl F g₁ g₂ x))
    (h₂ : ∀ y, L (prodInr F g₁ g₂ y) = L' (prodInr F g₁ g₂ y)) : L = L' := by
  refine LinearMap.ext fun v => ?_
  rw [← vo_prodInl_add_prodInr v, map_add, map_add, h₁, h₂]

theorem vo_prodEnd_mul (φ₁ ψ₁ : Module.End F (H1 F g₁)) (φ₂ ψ₂ : Module.End F (H1 F g₂)) :
    vo_prodEnd φ₁ φ₂ * vo_prodEnd ψ₁ ψ₂ = vo_prodEnd (φ₁ * ψ₁) (φ₂ * ψ₂) :=
  vo_prodEnd_ext (fun x => by simp) (fun y => by simp)

theorem vo_prodEnd_one : vo_prodEnd (1 : Module.End F (H1 F g₁)) (1 : Module.End F (H1 F g₂)) = 1 :=
  vo_prodEnd_ext (fun x => by simp) (fun y => by simp)

theorem vo_prodEnd_neg (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂)) :
    vo_prodEnd (-φ₁) (-φ₂) = -vo_prodEnd φ₁ φ₂ :=
  vo_prodEnd_ext (fun x => by simp) (fun y => by simp)

/-- `(φ₁, φ₂) ↦ φ₁ × φ₂` as a ring homomorphism. -/
noncomputable def vo_prodEndHom :
    Module.End F (H1 F g₁) × Module.End F (H1 F g₂) →+* Module.End F (H1 F (g₁ + g₂)) where
  toFun φ := vo_prodEnd φ.1 φ.2
  map_one' := vo_prodEnd_one
  map_mul' φ ψ := (vo_prodEnd_mul φ.1 ψ.1 φ.2 ψ.2).symm
  map_zero' := vo_prodEnd_ext (fun x => by simp) (fun y => by simp)
  map_add' φ ψ := vo_prodEnd_ext (fun x => by simp) (fun y => by simp)

@[simp]
theorem vo_prodEndHom_apply (φ : Module.End F (H1 F g₁) × Module.End F (H1 F g₂)) :
    vo_prodEndHom φ = vo_prodEnd φ.1 φ.2 := rfl

end ProdEnd

/-! ### Base change and the coordinates -/

section BaseChange

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] {g₁ g₂ : ℕ}

omit [CharZero F] [CharZero F'] in
theorem vo_prodEquiv_bcH1 (v : H1 F (g₁ + g₂)) :
    prodEquiv F' g₁ g₂ (bcH1 F F' (g₁ + g₂) v) =
      (bcH1 F F' g₁ (prodEquiv F g₁ g₂ v).1, bcH1 F F' g₂ (prodEquiv F g₁ g₂ v).2) := rfl

/-- `bcMap F F' φ = φ'` if `φ'` extends `φ`. -/
theorem vo_bcMap_eq {g g' : ℕ} (φ : H1 F g →ₗ[F] H1 F g') (φ' : H1 F' g →ₗ[F'] H1 F' g')
    (h : ∀ v, φ' (bcH1 F F' g v) = bcH1 F F' g' (φ v)) : bcMap F F' φ = φ' := by
  refine (Pi.basisFun F' (Fin (2 * g))).ext fun i => ?_
  have he : (Pi.basisFun F' (Fin (2 * g))) i = bcH1 F F' g (e F g i) := by
    rw [main_bcH1_e]; simp [e]
  rw [he, main_bcMap_bcH1, h]

theorem vo_bcMap_prodInl : bcMap F F' (prodInl F g₁ g₂) = prodInl F' g₁ g₂ :=
  vo_bcMap_eq _ _ fun v => (prodEquiv F' g₁ g₂).injective (by
    rw [vo_prodEquiv_prodInl, vo_prodEquiv_bcH1, vo_prodEquiv_prodInl, map_zero])

theorem vo_bcMap_prodInr : bcMap F F' (prodInr F g₁ g₂) = prodInr F' g₁ g₂ :=
  vo_bcMap_eq _ _ fun v => (prodEquiv F' g₁ g₂).injective (by
    rw [vo_prodEquiv_prodInr, vo_prodEquiv_bcH1, vo_prodEquiv_prodInr, map_zero])

theorem vo_bcMap_prodFst : bcMap F F' (prodFst F g₁ g₂) = prodFst F' g₁ g₂ :=
  vo_bcMap_eq _ _ fun v => by simp only [prodFst, LinearMap.comp_apply, LinearEquiv.coe_coe,
    vo_prodEquiv_bcH1, LinearMap.fst_apply]

theorem vo_bcMap_prodSnd : bcMap F F' (prodSnd F g₁ g₂) = prodSnd F' g₁ g₂ :=
  vo_bcMap_eq _ _ fun v => by simp only [prodSnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    vo_prodEquiv_bcH1, LinearMap.snd_apply]

theorem vo_bcMap_prodEnd (φ₁ : Module.End F (H1 F g₁)) (φ₂ : Module.End F (H1 F g₂)) :
    bcMap F F' (vo_prodEnd φ₁ φ₂) = vo_prodEnd (bcMap F F' φ₁) (bcMap F F' φ₂) :=
  vo_bcMap_eq _ _ fun v => (prodEquiv F' g₁ g₂).injective (by
    rw [vo_prodEquiv_prodEnd, vo_prodEquiv_bcH1, vo_prodEquiv_bcH1, vo_prodEquiv_prodEnd,
      main_bcMap_bcH1, main_bcMap_bcH1])

theorem vo_complexifyH1_prodJ (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂)) :
    complexifyH1 (g₁ + g₂) (prodJ J₁ J₂) =
      vo_prodEnd (complexifyH1 g₁ J₁) (complexifyH1 g₂ J₂) := by
  rw [main_lef_complexifyH1_eq, main_lef_complexifyH1_eq, main_lef_complexifyH1_eq, vo_prodJ_eq,
    vo_bcMap_prodEnd]

end BaseChange

/-! ### Products of abelian varieties -/

section Product

variable {g₁ g₂ : ℕ}

@[simp]
theorem vo_prodJ_prodInl (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂))
    (x : H1 ℝ g₁) : prodJ J₁ J₂ (prodInl ℝ g₁ g₂ x) = prodInl ℝ g₁ g₂ (J₁ x) :=
  vo_prodEnd_prodInl J₁ J₂ x

@[simp]
theorem vo_prodJ_prodInr (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂))
    (y : H1 ℝ g₂) : prodJ J₁ J₂ (prodInr ℝ g₁ g₂ y) = prodInr ℝ g₁ g₂ (J₂ y) :=
  vo_prodEnd_prodInr J₁ J₂ y

theorem vo_isComplexStructure_prodJ {J₁ : Module.End ℝ (H1 ℝ g₁)} {J₂ : Module.End ℝ (H1 ℝ g₂)}
    (h₁ : IsComplexStructure J₁) (h₂ : IsComplexStructure J₂) :
    IsComplexStructure (prodJ J₁ J₂) := by
  rw [IsComplexStructure, vo_prodJ_eq, vo_prodEnd_mul, h₁, h₂, vo_prodEnd_neg, vo_prodEnd_one]

/-- `pr₁^*` is a morphism of Hodge structures `H¹(A₁) → H¹(A₁ × A₂)`. -/
theorem vo_isHodgeMap_prodInl (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂)) :
    IsHodgeMap J₁ (prodJ J₁ J₂) (prodInl ℚ g₁ g₂) := by
  rw [IsHodgeMap, vo_bcMap_prodInl]
  exact LinearMap.ext fun x => by simp

/-- `pr₂^*` is a morphism of Hodge structures `H¹(A₂) → H¹(A₁ × A₂)`. -/
theorem vo_isHodgeMap_prodInr (J₁ : Module.End ℝ (H1 ℝ g₁)) (J₂ : Module.End ℝ (H1 ℝ g₂)) :
    IsHodgeMap J₂ (prodJ J₁ J₂) (prodInr ℚ g₁ g₂) := by
  rw [IsHodgeMap, vo_bcMap_prodInr]
  exact LinearMap.ext fun x => by simp

/-- `φ₁ × φ₂` is a morphism of Hodge structures if `φ₁` and `φ₂` are. -/
theorem vo_isHodgeMap_prodEnd {J₁ : Module.End ℝ (H1 ℝ g₁)} {J₂ : Module.End ℝ (H1 ℝ g₂)}
    {φ₁ : Module.End ℚ (H1 ℚ g₁)} {φ₂ : Module.End ℚ (H1 ℚ g₂)} (h₁ : IsHodgeMap J₁ J₁ φ₁)
    (h₂ : IsHodgeMap J₂ J₂ φ₂) : IsHodgeMap (prodJ J₁ J₂) (prodJ J₁ J₂) (vo_prodEnd φ₁ φ₂) := by
  rw [IsHodgeMap] at h₁ h₂ ⊢
  rw [vo_bcMap_prodEnd, vo_prodJ_eq, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    vo_prodEnd_mul, vo_prodEnd_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, h₁, h₂]

end Product

/-! ### Double contractions -/

section Eval2

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem vo_eval2_map {n' : ℕ} (φ : H1 F n →ₗ[F] H1 F n') (ξ : S F n)
    (a b : Module.Dual F (H1 F n')) :
    eval2 F n' (ExteriorAlgebra.map φ ξ) a b = eval2 F n ξ (a ∘ₗ φ) (b ∘ₗ φ) := by
  simp only [eval2, D, main_coord_empty, AlgHom.toLinearMap_apply]
  exact main_dc_map φ a b ξ

theorem vo_eval2_add (ξ ξ' : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n (ξ + ξ') a b = eval2 F n ξ a b + eval2 F n ξ' a b := by
  simp only [eval2, map_add]

theorem vo_eval2_smul (c : F) (ξ : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n (c • ξ) a b = c * eval2 F n ξ a b := by
  simp only [eval2, map_smul, smul_eq_mul]

theorem vo_eval2_add_left (ξ : S F n) (a a' b : Module.Dual F (H1 F n)) :
    eval2 F n ξ (a + a') b = eval2 F n ξ a b + eval2 F n ξ a' b := by
  simp only [eval2, map_add, LinearMap.add_apply]

theorem vo_eval2_smul_left (ξ : S F n) (c : F) (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ (c • a) b = c * eval2 F n ξ a b := by
  simp only [eval2, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem vo_eval2_add_right (ξ : S F n) (a b b' : Module.Dual F (H1 F n)) :
    eval2 F n ξ a (b + b') = eval2 F n ξ a b + eval2 F n ξ a b' := by
  simp only [eval2, map_add, LinearMap.add_apply]

theorem vo_eval2_zero_left (ξ : S F n) (b : Module.Dual F (H1 F n)) : eval2 F n ξ 0 b = 0 := by
  simp only [eval2, map_zero, LinearMap.zero_apply]

theorem vo_eval2_zero_right (ξ : S F n) (a : Module.Dual F (H1 F n)) : eval2 F n ξ a 0 = 0 := by
  simp only [eval2, map_zero, LinearMap.zero_apply]

/-- Double contractions of `pr₁^*ξ₁ + pr₂^*ξ₂` split over the factors. -/
theorem vo_eval2_prod {g₁ g₂ : ℕ} (ξ₁ : S F g₁) (ξ₂ : S F g₂)
    (a b : Module.Dual F (H1 F (g₁ + g₂))) :
    eval2 F (g₁ + g₂) (ExteriorAlgebra.map (prodInl F g₁ g₂) ξ₁ +
        ExteriorAlgebra.map (prodInr F g₁ g₂) ξ₂) a b =
      eval2 F g₁ ξ₁ (a ∘ₗ prodInl F g₁ g₂) (b ∘ₗ prodInl F g₁ g₂) +
        eval2 F g₂ ξ₂ (a ∘ₗ prodInr F g₁ g₂) (b ∘ₗ prodInr F g₁ g₂) := by
  rw [vo_eval2_add, vo_eval2_map, vo_eval2_map]

end Eval2

/-! ### The product of two abelian varieties -/

section ProductAmple

variable {g₁ g₂ : ℕ}

/-- `pr₁^*Θ₁ + pr₂^*Θ₂` is ample on `A₁ × A₂` if `Θᵢ` is ample on `Aᵢ`. -/
theorem vo_isAmple_prod {J₁ : Module.End ℝ (H1 ℝ g₁)} {J₂ : Module.End ℝ (H1 ℝ g₂)}
    (hJ₁ : IsComplexStructure J₁) (hJ₂ : IsComplexStructure J₂) {Θ₁ : S ℚ g₁} {Θ₂ : S ℚ g₂}
    (h₁ : IsAmple g₁ J₁ Θ₁) (h₂ : IsAmple g₂ J₂ Θ₂) :
    IsAmple (g₁ + g₂) (prodJ J₁ J₂)
      (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) Θ₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) Θ₂) := by
  have hbc : bcS ℚ ℝ (g₁ + g₂)
      (ExteriorAlgebra.map (prodInl ℚ g₁ g₂) Θ₁ + ExteriorAlgebra.map (prodInr ℚ g₁ g₂) Θ₂) =
      ExteriorAlgebra.map (prodInl ℝ g₁ g₂) (bcS ℚ ℝ g₁ Θ₁) +
        ExteriorAlgebra.map (prodInr ℝ g₁ g₂) (bcS ℚ ℝ g₂ Θ₂) := by
    rw [map_add, main_bcS_map, main_bcS_map, vo_bcMap_prodInl, vo_bcMap_prodInr]
  refine ⟨main_lef_hodge_one_of_map (vo_isComplexStructure_prodJ hJ₁ hJ₂) ?_ ?_, fun a ha => ?_⟩
  · exact Submodule.add_mem _ (main_map_mem_exteriorPower _ 2 h₁.mem_exteriorPower_two)
      (main_map_mem_exteriorPower _ 2 h₂.mem_exteriorPower_two)
  · have e₁ : (prodJ J₁ J₂).comp (prodInl ℝ g₁ g₂) = (prodInl ℝ g₁ g₂).comp J₁ :=
      LinearMap.ext fun x => by simp
    have e₂ : (prodJ J₁ J₂).comp (prodInr ℝ g₁ g₂) = (prodInr ℝ g₁ g₂).comp J₂ :=
      LinearMap.ext fun x => by simp
    rw [hbc, map_add, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
      ExteriorAlgebra.map_comp_map, e₁, e₂, ← ExteriorAlgebra.map_comp_map,
      ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply, AlgHom.comp_apply,
      main_lef_map_bcS_of_hodge h₁.1, main_lef_map_bcS_of_hodge h₂.1]
  · rw [hbc, vo_eval2_prod]
    have e₁ : a ∘ₗ prodJ J₁ J₂ ∘ₗ prodInl ℝ g₁ g₂ = (a ∘ₗ prodInl ℝ g₁ g₂) ∘ₗ J₁ :=
      LinearMap.ext fun x => by simp
    have e₂ : a ∘ₗ prodJ J₁ J₂ ∘ₗ prodInr ℝ g₁ g₂ = (a ∘ₗ prodInr ℝ g₁ g₂) ∘ₗ J₂ :=
      LinearMap.ext fun x => by simp
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, e₁, e₂]
    have hnn₁ : 0 ≤ eval2 ℝ g₁ (bcS ℚ ℝ g₁ Θ₁) (a ∘ₗ prodInl ℝ g₁ g₂)
        ((a ∘ₗ prodInl ℝ g₁ g₂) ∘ₗ J₁) := by
      by_cases h0 : a ∘ₗ prodInl ℝ g₁ g₂ = 0
      · rw [h0, vo_eval2_zero_left]
      · exact (h₁.2 _ h0).le
    have hnn₂ : 0 ≤ eval2 ℝ g₂ (bcS ℚ ℝ g₂ Θ₂) (a ∘ₗ prodInr ℝ g₁ g₂)
        ((a ∘ₗ prodInr ℝ g₁ g₂) ∘ₗ J₂) := by
      by_cases h0 : a ∘ₗ prodInr ℝ g₁ g₂ = 0
      · rw [h0, vo_eval2_zero_left]
      · exact (h₂.2 _ h0).le
    by_cases h0 : a ∘ₗ prodInl ℝ g₁ g₂ = 0
    · have h0' : a ∘ₗ prodInr ℝ g₁ g₂ ≠ 0 := fun h => ha (vo_dual_eq_zero h0 h)
      exact add_pos_of_nonneg_of_pos hnn₁ (h₂.2 _ h0')
    · exact add_pos_of_pos_of_nonneg (h₁.2 _ h0) hnn₂

end ProductAmple

/-- **The product `A₁ × A₂`** of two abelian varieties, with the complex structure `J₁ × J₂` and the
ample class `pr₁^*Θ₁ + pr₂^*Θ₂`. -/
noncomputable def AbVar.prod {g₁ g₂ : ℕ} (A₁ : AbVar g₁) (A₂ : AbVar g₂) : AbVar (g₁ + g₂) where
  J := prodJ A₁.J A₂.J
  isComplex := vo_isComplexStructure_prodJ A₁.isComplex A₂.isComplex
  polarizable := ⟨_, vo_isAmple_prod A₁.isComplex A₂.isComplex A₁.polarizable.choose_spec
    A₂.polarizable.choose_spec⟩

@[simp]
theorem AbVar.prod_J {g₁ g₂ : ℕ} (A₁ : AbVar g₁) (A₂ : AbVar g₂) :
    (A₁.prod A₂).J = prodJ A₁.J A₂.J := rfl

/-! ### Push-forward and the projection formula -/

section Pushforward

variable {F : Type*} [Field F]

theorem vo_D_zero {n : ℕ} : D F n 0 = 0 := map_zero _

/-- `D_θ (x y) = D_θ(x) y` when `D_θ y = 0`. -/
theorem vo_D_mul_of_eq_zero {n : ℕ} (θ : Module.Dual F (H1 F n)) (x : S F n) {y : S F n}
    (hy : D F n θ y = 0) : D F n θ (x * y) = D F n θ x * y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [← Algebra.smul_def, map_smul, hy, smul_zero]
    simp [D]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | ι_mul m x hx =>
    simp only [D] at hx hy ⊢
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul, hx,
      sub_mul, smul_mul_assoc, mul_assoc]

variable {g₁ g₂ : ℕ}

/-- The functional `θᵢ = fᵢ ∘ pr` on `H¹(A₁ × A₂)` used by `pushSnd`. -/
theorem vo_D_prodInr (i : Fin (2 * g₁)) (b : S F g₂) :
    D F (g₁ + g₂) (f F g₁ i ∘ₗ prodFst F g₁ g₂) (ExteriorAlgebra.map (prodInr F g₁ g₂) b) = 0 := by
  simp only [D]
  rw [main_contractLeft_map, LinearMap.comp_assoc, vo_prodFst_comp_prodInr, LinearMap.comp_zero,
    map_zero, LinearMap.zero_apply, map_zero]

theorem vo_D_prodInl (i : Fin (2 * g₁)) (a : S F g₁) :
    D F (g₁ + g₂) (f F g₁ i ∘ₗ prodFst F g₁ g₂) (ExteriorAlgebra.map (prodInl F g₁ g₂) a) =
      ExteriorAlgebra.map (prodInl F g₁ g₂) (D F g₁ (f F g₁ i) a) := by
  simp only [D]
  rw [main_contractLeft_map, LinearMap.comp_assoc, vo_prodFst_comp_prodInl, LinearMap.comp_id]

theorem vo_contract_list_map (l : List (Fin (2 * g₁))) (a : S F g₁) (b : S F g₂) :
    (l.map fun i => D F (g₁ + g₂) (f F g₁ i ∘ₗ prodFst F g₁ g₂)).prod
        (ExteriorAlgebra.map (prodInl F g₁ g₂) a * ExteriorAlgebra.map (prodInr F g₁ g₂) b) =
      ExteriorAlgebra.map (prodInl F g₁ g₂) ((l.map fun i => D F g₁ (f F g₁ i)).prod a) *
        ExteriorAlgebra.map (prodInr F g₁ g₂) b := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    rw [vo_D_mul_of_eq_zero _ _ (vo_D_prodInr i b), vo_D_prodInl]

/-- A composite of contractions lowers degrees: on `⋀^k`, `l.length` contractions land in
`⋀^(k - l.length)`, and give `0` if `k < l.length`. -/
theorem vo_contract_list_mem {n : ℕ} (l : List (Module.Dual F (H1 F n))) {k : ℕ} {x : S F n}
    (hx : x ∈ ⋀[F]^k (H1 F n)) :
    (l.map (D F n)).prod x ∈ ⋀[F]^(k - l.length) (H1 F n) ∧
      (k < l.length → (l.map (D F n)).prod x = 0) := by
  induction l with
  | nil => simpa using hx
  | cons θ l ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    by_cases hk : k < l.length
    · rw [ih₂ hk, map_zero]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · by_cases hk' : k = l.length
      · subst hk'
        rw [Nat.sub_self] at ih₁
        rw [main_lef_D_eq_zero_of_mem_zero θ ih₁]
        exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
      · have heq : k - l.length = (k - (l.length + 1)) + 1 := by omega
        rw [heq] at ih₁
        exact ⟨main_lef_D_mem θ _ ih₁, fun h => absurd h (by omega)⟩

/-- `D_{φ_{n}} ⋯ D_{φ_1} (v₁ ∧ ⋯ ∧ v_n) = 1` (`D_{φ_1}` first) for `φᵢ(vⱼ) = δᵢⱼ`. -/
theorem vo_contract_ιMulti {M : Type*} [AddCommGroup M] [Module F M] :
    ∀ (k : ℕ) (v : Fin k → M) (φ : Fin k → Module.Dual F M),
      (∀ i j, φ i (v j) = if i = j then 1 else 0) →
      (List.ofFn fun i : Fin k =>
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) (φ i.rev)).prod
        (ExteriorAlgebra.ιMulti F k v) = 1 := by
  intro k
  induction k with
  | zero => intro v φ _; simp
  | succ k ih =>
    intro v φ hφ
    -- `φ₀` kills `v₁, …, v_k`
    have hkill : ∀ (j : ℕ) (w : Fin j → M), (∀ i, φ 0 (w i) = 0) →
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) (φ 0)
          (ExteriorAlgebra.ιMulti F j w) = 0 := by
      intro j
      induction j with
      | zero => intro w _; simp
      | succ j ihj =>
        intro w hw
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        erw [CliffordAlgebra.contractLeft_ι_mul]
        rw [hw 0, zero_smul, zero_sub, ihj (Matrix.vecTail w) (fun i => hw _), mul_zero, neg_zero]
    rw [List.ofFn_succ', List.prod_concat, Module.End.mul_apply, ExteriorAlgebra.ιMulti_succ_apply]
    have h0 : Fin.rev (Fin.last k) = 0 := by ext; simp
    rw [h0]
    erw [CliffordAlgebra.contractLeft_ι_mul]
    have h00 : φ 0 (v 0) = 1 := by simp [hφ]
    rw [hkill k (Matrix.vecTail v) (fun i => by simp [Matrix.vecTail, hφ, (Fin.succ_ne_zero i).symm]),
      mul_zero, sub_zero, h00, one_smul]
    have hrev : ∀ i : Fin k, (Fin.castSucc i).rev = (i.rev).succ := fun i => Fin.rev_castSucc i
    simp only [hrev]
    exact ih (Matrix.vecTail v) (fun i => φ i.succ) (fun i j => by
      simp [Matrix.vecTail, hφ, Fin.succ_inj])

/-- `[pt] = e₁ ∧ ⋯ ∧ e_{2n}`. -/
theorem vo_pt_eq (n : ℕ) : pt F n = ExteriorAlgebra.ιMulti F (2 * n) (e F n) := by
  have hcard : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by simp
  have hemb : (fun i => (Finset.univ : Finset (Fin (2 * n))).orderEmbOfFin hcard i) = id :=
    (Finset.orderEmbOfFin_unique hcard (fun _ => Finset.mem_univ _) strictMono_id).symm
  rw [pt, s24b_basisS_apply' F n Finset.univ (2 * n) hcard]
  congr 1
  funext i
  rw [show (Finset.univ : Finset (Fin (2 * n))).orderEmbOfFin hcard i = i from congrFun hemb i]

/-- `∫_X [pt] = 1`. -/
theorem vo_integral_pt (n : ℕ) : integral F n (pt F n) = 1 := by
  rw [integral, pt, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Contracting with all of `f₁, …, f_{2n}` (`f₁` first) and taking the degree-`0` part is
integration `∫ : H*(X) → F`, the coefficient of `[pt] = e₁ ∧ ⋯ ∧ e_{2n}`. -/
theorem vo_contract_all {n : ℕ} (a : S F n) :
    ExteriorAlgebra.algebraMapInv
        ((List.ofFn fun i : Fin (2 * n) => D F n (f F n i.rev)).prod a) = integral F n a := by
  have hlin : (ExteriorAlgebra.algebraMapInv : S F n →ₐ[F] F).toLinearMap ∘ₗ
      (List.ofFn fun i : Fin (2 * n) => D F n (f F n i.rev)).prod = integral F n := by
    refine (basisS F n).ext fun s => ?_
    by_cases hs : s = Finset.univ
    · subst hs
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← pt, vo_integral_pt, vo_pt_eq]
      have := vo_contract_ιMulti (F := F) (M := H1 F n) (2 * n) (e F n) (f F n) (fun i j => by
        simp [f, e, Pi.single_apply])
      simp only [D] at this ⊢
      rw [this, map_one]
    · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, integral, Module.Basis.coord_apply,
        Module.Basis.repr_self, show (Finsupp.single s (1 : F)) Finset.univ = 0 by simp [hs]]
      have hlt : s.card < 2 * n := by
        have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
        simpa using this
      have hmem : basisS F n s ∈ ⋀[F]^s.card (H1 F n) := by
        rw [s24b_basisS_apply]
        exact ExteriorAlgebra.ιMulti_range F s.card ⟨_, rfl⟩
      have h0 := (vo_contract_list_mem (List.ofFn fun i : Fin (2 * n) => f F n i.rev) hmem).2
        (by simpa using hlt)
      rw [List.map_ofFn] at h0
      have h1 : (List.ofFn fun i : Fin (2 * n) => D F n (f F n i.rev)) =
          List.ofFn (D F n ∘ fun i : Fin (2 * n) => f F n i.rev) := rfl
      rw [h1, h0, map_zero]
  exact congrArg (fun L => L a) hlin

/-- **The projection formula** `pr₂,*(pr₁^* a ∪ pr₂^* b) = (∫_{A₁} a) b`. -/
theorem pushSnd_prodInl_mul_prodInr (a : S F g₁) (b : S F g₂) :
    pushSnd F g₁ g₂ (ExteriorAlgebra.map (prodInl F g₁ g₂) a *
      ExteriorAlgebra.map (prodInr F g₁ g₂) b) = integral F g₁ a • b := by
  have hl : (List.ofFn fun i : Fin (2 * g₁) => D F (g₁ + g₂) (f F g₁ i.rev ∘ₗ prodFst F g₁ g₂)) =
      (List.ofFn fun i : Fin (2 * g₁) => i.rev).map
        (fun i => D F (g₁ + g₂) (f F g₁ i ∘ₗ prodFst F g₁ g₂)) := by
    rw [List.map_ofFn]; rfl
  have hl' : (List.ofFn fun i : Fin (2 * g₁) => D F g₁ (f F g₁ i.rev)) =
      (List.ofFn fun i : Fin (2 * g₁) => i.rev).map (fun i => D F g₁ (f F g₁ i)) := by
    rw [List.map_ofFn]; rfl
  rw [pushSnd, LinearMap.comp_apply, hl, vo_contract_list_map, ← hl', AlgHom.toLinearMap_apply,
    map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, vo_prodSnd_comp_prodInl, vo_prodSnd_comp_prodInr,
    ExteriorAlgebra.map_id, AlgHom.id_apply]
  -- `map 0` is the augmentation
  have hzero : ∀ x : S F g₁, ExteriorAlgebra.map (0 : H1 F g₁ →ₗ[F] H1 F g₂) x =
      algebraMap F (S F g₂) (ExteriorAlgebra.algebraMapInv x) := by
    intro x
    have h0 : ExteriorAlgebra.map (0 : H1 F g₁ →ₗ[F] H1 F g₂) =
        (Algebra.ofId F (S F g₂)).comp ExteriorAlgebra.algebraMapInv :=
      ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp [ExteriorAlgebra.algebraMapInv])
    rw [h0]
    rfl
  rw [hzero, vo_contract_all, ← Algebra.smul_def]

end Pushforward

/-! ### Eigenspaces of block-diagonal endomorphisms -/

section Eigenspaces

variable {K : Type*} [Field K] {g₁ g₂ : ℕ}

/-- `p × q ≃ p.prod q`. -/
def vo_prodSubmoduleEquiv {M M' : Type*} [AddCommGroup M] [Module K M] [AddCommGroup M']
    [Module K M'] (p : Submodule K M) (q : Submodule K M') : (p.prod q) ≃ₗ[K] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem vo_eigenspace_prodEnd (φ₁ : Module.End K (H1 K g₁)) (φ₂ : Module.End K (H1 K g₂))
    (μ : K) : Module.End.eigenspace (vo_prodEnd φ₁ φ₂) μ =
      ((Module.End.eigenspace φ₁ μ).prod (Module.End.eigenspace φ₂ μ)).comap
        (prodEquiv K g₁ g₂).toLinearMap := by
  ext v
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_prod,
    LinearEquiv.coe_coe]
  constructor
  · intro h
    have := congrArg (prodEquiv K g₁ g₂) h
    rw [vo_prodEquiv_prodEnd, map_smul] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨h₁, h₂⟩
    apply (prodEquiv K g₁ g₂).injective
    rw [vo_prodEquiv_prodEnd, map_smul, h₁, h₂]
    rfl

/-- **The dimensions in the Weil condition add up on products**: for block-diagonal `φ = φ₁ × φ₂`
and `ψ = ψ₁ × ψ₂`, `dim(ker(φ - μ) ∩ ker(ψ - ν))` is the sum of the dimensions for the factors. -/
theorem vo_finrank_eigenspace_inf_prodEnd (φ₁ ψ₁ : Module.End K (H1 K g₁))
    (φ₂ ψ₂ : Module.End K (H1 K g₂)) (μ ν : K) :
    Module.finrank K ↥(Module.End.eigenspace (vo_prodEnd φ₁ φ₂) μ ⊓
        Module.End.eigenspace (vo_prodEnd ψ₁ ψ₂) ν) =
      Module.finrank K ↥(Module.End.eigenspace φ₁ μ ⊓ Module.End.eigenspace ψ₁ ν) +
        Module.finrank K ↥(Module.End.eigenspace φ₂ μ ⊓ Module.End.eigenspace ψ₂ ν) := by
  rw [vo_eigenspace_prodEnd, vo_eigenspace_prodEnd, ← Submodule.comap_inf, Submodule.prod_inf_prod,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    (vo_prodSubmoduleEquiv _ _).finrank_eq, Module.finrank_prod]

end Eigenspaces

end WeilClasses
