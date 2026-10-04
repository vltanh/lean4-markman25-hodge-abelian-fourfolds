module

public import WeilClasses.Chevalley.Defs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Cohomology of products, Künneth isomorphisms and correspondences (paper §5.2, §6.1, §6.3)

**The model (a representation choice, documented here once).** The cohomology ring of a product
of two abelian varieties `Y × Z` is `⋀•(H¹(Y) ⊕ H¹(Z))`, with cup product the exterior product; the
pullbacks `π_Y^*`, `π_Z^*` are `ExteriorAlgebra.map` of the two inclusions, and the Künneth
isomorphism `H*(Y) ⊗ H*(Z) ≅ H*(Y × Z)` is `u ⊗ v ↦ π_Y^*u ∪ π_Z^*v` (Mathlib's
`ExteriorAlgebra.prodEquivTensor`, whose target is the graded tensor product). Concretely:

* `H*(X̂ × X, F)` and `H*(X × X̂, F)` are both `⋀•V` (`V = H¹(X̂) ⊕ H¹(X)`, dual summand first, the
  same ring); `kunnethHatX : H*(X̂) ⊗ H*(X) ≅ ⋀•V` is `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b` (the Künneth order
  used for `φ̃ : H*(X × X) → H*(X̂ × X)` in §6.3) and `kunnethXHat : H*(X) ⊗ H*(X̂) ≅ ⋀•V` is
  `u ⊗ v ↦ π_X^*u ∪ π_X̂^*v` (the order used for `H*(X × X̂)`, the target of Orlov's `φ`).
* `H*(X × X, F)` is `S ⊗ S` (as in the paper's (2.3.2) and (6.1.3)), `u ⊗ v` standing for
  `π₁^*u ∪ π₂^*v`; the ring `⋀•(H¹(X) ⊕ H¹(X))` is `SXX`, identified with `S ⊗ S` by `kunnethXX`.
* `[pt_{X×Y}] = π_X^*[pt_X] ∪ π_Y^*[pt_Y]` (even degrees, so the order is irrelevant), so that the
  push-forward along `π_Y` is `π_{Y*}(π_X^*a ∪ π_Y^*b) = (∫_X a) b`.
* **Correspondences.** For `γ ∈ H*(X × Y) = H*(X) ⊗ H*(Y)` the paper sets
  `γ_*(s) = π_{Y*}(π_X^*s ∪ γ)`; for `γ = Σ uᵢ ⊗ vᵢ` this is `γ_*(s) = Σ (∫_X s ∪ uᵢ) vᵢ` (proof of
  Lemma 5.2.1), which we take as the definition (`corr`). The cohomological action of an integral
  functor with kernel `𝒢` is `ch(𝒢)_*` (Todd classes of abelian varieties are trivial).
* **The map `μ(x, y) = (x + y, y)`** of `X × X` (§1.3, §6.1, §6.3) acts on `H¹(X × X) = H¹(X) ⊕
  H¹(X)`
  by `μ^*(a, b) = (a, a + b)`, i.e. `μ^*(π₁^*e) = π₁^*e + π₂^*e`, `μ^*(π₂^*e) = π₂^*e`; `μ^*` on
  `H*(X × X)` is the induced ring homomorphism (`muStarXX`, and `muStar` on `S ⊗ S`).
* `PD(s) = ∫_X (• ∪ s)` (§5.2), and `id ⊗ τ` (`tauTensor`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Correspondences (generic) -/

section Generic

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [AddCommGroup B] [Module F B]

theorem pdOf_apply (intA : A →ₗ[F] F) (u s : A) : pdOf intA u s = intA (s * u) := rfl

theorem corr_tmul (intA : A →ₗ[F] F) (u : A) (v : B) (s : A) :
    corr intA (u ⊗ₜ v) s = intA (s * u) • v := by
  simp [corr, pdOf_apply]

end Generic

/-! ## Exterior algebras: graded commutativity, contraction, parity (helpers) -/

section ExteriorHelpers

/-- Graded commutativity in `⋀• M`: `v ∧ x = involute(x) ∧ v` for a vector `v`. -/
theorem s23_ι_mul_eq_involute_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R v * x =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R v := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι w =>
    change ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
      CliffordAlgebra.involute (ExteriorAlgebra.ι R w) * ExteriorAlgebra.ι R v
    rw [show CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ι R w) =
      -ExteriorAlgebra.ι R w from CliffordAlgebra.involute_ι _, neg_mul,
      eq_neg_iff_add_eq_zero, ExteriorAlgebra.ι_add_mul_swap]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

/-- Contraction is an odd derivation of `⋀• M`:
`d ⌋ (x ∧ y) = (d ⌋ x) ∧ y + involute(x) ∧ (d ⌋ y)`. -/
theorem s23_contractLeft_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.Dual R M) (x y : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (x * y) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d x * y +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) x *
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap, zero_mul, zero_add, AlgHom.commutes,
      ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, map_add, add_mul, add_mul]; abel
  | ι_mul x m hx =>
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul,
      map_mul, CliffordAlgebra.involute_ι, sub_mul, mul_add, smul_mul_assoc, neg_mul, neg_mul,
      mul_assoc, mul_assoc]
    abel

/-- Even elements of `⋀• M` are central. -/
theorem s23_mul_comm_of_mem_even {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {x : ExteriorAlgebra R M}
    (hx : x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 0) (y : ExteriorAlgebra R M) :
    x * y = y * x := by
  have hinv := CliffordAlgebra.involute_eq_of_mem_even hx
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r x).symm
  | ι w =>
    change x * ExteriorAlgebra.ι R w = ExteriorAlgebra.ι R w * x
    rw [s23_ι_mul_eq_involute_mul, hinv]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, add_mul]

/-- For odd `x ∈ ⋀• M`, `x ∧ y = involute(y) ∧ x`. -/
theorem s23_mul_eq_involute_mul_of_mem_odd {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {x : ExteriorAlgebra R M}
    (hx : x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 1) (y : ExteriorAlgebra R M) :
    x * y = CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) y * x := by
  induction x, hx using CliffordAlgebra.odd_induction with
  | ι v =>
    exact s23_ι_mul_eq_involute_mul v y
  | add a b _ _ ha hb => rw [add_mul, ha, hb, mul_add]
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    change ExteriorAlgebra.ι R m₁ * ExteriorAlgebra.ι R m₂ * x * y = _
    rw [mul_assoc, hx, ← mul_assoc, mul_assoc (ExteriorAlgebra.ι R m₁),
      s23_ι_mul_eq_involute_mul m₂, ← mul_assoc, s23_ι_mul_eq_involute_mul m₁,
      CliffordAlgebra.involute_involute]
    simp only [mul_assoc]

end ExteriorHelpers

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- Poincaré duality (§5.2) `PD : H*(X, F) → H*(X, F)*`, `PD(s) = ∫_X (• ∪ s)`. -/
noncomputable def PD : S F n →ₗ[F] Module.Dual F (S F n) := pdOf (integral F n)

omit [CharZero F] in
/-- `∫_X` is invariant under the grading involution (`[pt_X]` has even degree `2n`). -/
theorem s23_integral_involute (s : S F n) :
    integral F n (CliffordAlgebra.involute (Q := (0 : QuadraticForm F (H1 F n))) s) =
      integral F n s := by
  have h : integral F n ∘ₗ
      (CliffordAlgebra.involute (Q := (0 : QuadraticForm F (H1 F n)))).toLinearMap =
        integral F n := by
    refine (basisS F n).ext fun K => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisS,
      TauCeti.ExteriorAlgebra.involute_basis, map_smul, integral, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with hK
    · subst hK
      simp [Finset.card_univ, Fintype.card_fin, pow_mul]
    · simp
  exact congrArg (fun φ : S F n →ₗ[F] F => φ s) h

/-- `∫_X` vanishes on odd classes. -/
theorem s23_integral_of_mem_odd {s : S F n} (hs : s ∈ Sminus F n) : integral F n s = 0 := by
  have h := s23_integral_involute F n s
  rw [CliffordAlgebra.involute_eq_of_mem_odd hs, map_neg, neg_eq_iff_add_eq_zero] at h
  have h2 : (2 : F) * integral F n s = 0 := by rw [two_mul]; exact h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-! ## `X̂ × X` and `X × X̂` -/

/-- Künneth for `X̂ × X`: `H*(X̂) ⊗ H*(X) ≅ ⋀•V`, `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b`. -/
noncomputable def kunnethHatX : SHat F n ⊗[F] S F n ≃ₗ[F] ExtV F n :=
  (GradedTensorProduct.of F (fun i : ℕ => ⋀[F]^i (Module.Dual F (H1 F n)))
      (fun i : ℕ => ⋀[F]^i (H1 F n))).trans
    (ExteriorAlgebra.prodEquivTensor F (Module.Dual F (H1 F n)) (H1 F n)).symm.toLinearEquiv

omit [CharZero F] in
theorem kunnethHatX_tmul (a : SHat F n) (b : S F n) :
    kunnethHatX F n (a ⊗ₜ b) = pullXHat F n a * pullX F n b := rfl

set_option linter.unusedSectionVars false in
theorem kunnethXHat_tmul (u : S F n) (v : SHat F n) :
    kunnethXHat F n (u ⊗ₜ v) = pullX F n u * pullXHat F n v := by
  have htop : ∀ (M : Type _) [AddCommGroup M] [Module F M],
      (⨆ i : ℕ, ⋀[F]^i M) = ⊤ := fun M _ _ =>
    (DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[F]^i M)).submodule_iSup_eq_top
  have hu : u ∈ ⨆ i : ℕ, ⋀[F]^i (H1 F n) := by rw [htop]; exact Submodule.mem_top
  have hv : v ∈ ⨆ i : ℕ, ⋀[F]^i (Module.Dual F (H1 F n)) := by rw [htop]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | zero => simp
  | add u u' _ _ ihu ihu' => rw [TensorProduct.add_tmul, map_add, ihu, ihu', map_add, add_mul]
  | mem i u hu =>
    induction hv using Submodule.iSup_induction' with
    | zero => simp
    | add v v' _ _ ihv ihv' => rw [TensorProduct.tmul_add, map_add, ihv, ihv', map_add, mul_add]
    | mem j v hv =>
      have h1 := GradedTensorProduct.comm_coe_tmul_coe (R := F)
        (fun i : ℕ => ⋀[F]^i (H1 F n)) (fun i : ℕ => ⋀[F]^i (Module.Dual F (H1 F n)))
        (⟨u, hu⟩ : ⋀[F]^i (H1 F n)) (⟨v, hv⟩ : ⋀[F]^j (Module.Dual F (H1 F n)))
      have h2 := ExteriorAlgebra.map_inl_inr_anticomm F j i
        (⟨v, hv⟩ : ⋀[F]^j (Module.Dual F (H1 F n))) (⟨u, hu⟩ : ⋀[F]^i (H1 F n))
      simp only at h1 h2
      change (ExteriorAlgebra.prodEquivTensor F (Module.Dual F (H1 F n)) (H1 F n)).symm
        (GradedTensorProduct.comm _ _ (u ᵍ⊗ₜ[F] v)) = _
      rw [h1, Units.smul_def, map_zsmul, ExteriorAlgebra.prodEquivTensor_symm_tmul]
      change _ • (pullXHat F n v * pullX F n u) = _
      change pullXHat F n v * pullX F n u = _ at h2
      rw [h2, smul_smul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_add,
        mul_comm j i, ← two_mul, pow_mul]
      simp only [even_two, Even.neg_pow, one_pow, one_smul]
      rfl

/-! ## `X × X` -/

/-- `π₁^* : H*(X) → H*(X × X)`. -/
noncomputable def pull1 : S F n →ₐ[F] SXX F n :=
  ExteriorAlgebra.map (LinearMap.inl F (H1 F n) (H1 F n))

/-- `π₂^* : H*(X) → H*(X × X)`. -/
noncomputable def pull2 : S F n →ₐ[F] SXX F n :=
  ExteriorAlgebra.map (LinearMap.inr F (H1 F n) (H1 F n))

omit [CharZero F] in
theorem kunnethXX_tmul (u v : S F n) : kunnethXX F n (u ⊗ₜ v) = pull1 F n u * pull2 F n v := rfl

/-- `(μ^{-1})^*` on `H¹(X × X)`: `(a, b) ↦ (a, b - a)`. -/
noncomputable def mu1Inv : (H1 F n × H1 F n) →ₗ[F] (H1 F n × H1 F n) :=
  (LinearMap.fst F (H1 F n) (H1 F n)).prod
    (LinearMap.snd F (H1 F n) (H1 F n) - LinearMap.fst F (H1 F n) (H1 F n))

/-- `μ^* : H*(X × X) → H*(X × X)`, the ring homomorphism induced by `mu1`. -/
noncomputable def muStarXX : SXX F n →ₐ[F] SXX F n := ExteriorAlgebra.map (mu1 F n)

/-- `(μ^*)^{-1} = (μ^{-1})^*` on `H*(X × X) = S ⊗ S`. -/
noncomputable def muStarInv : S F n ⊗[F] S F n →ₗ[F] S F n ⊗[F] S F n :=
  (kunnethXX F n).symm.toLinearMap ∘ₗ (ExteriorAlgebra.map (mu1Inv F n)).toLinearMap ∘ₗ
    (kunnethXX F n).toLinearMap

/-- `id ⊗ τ` on `H*(X × X) = S ⊗ S`. -/
noncomputable def tauTensor : S F n ⊗[F] S F n →ₗ[F] S F n ⊗[F] S F n :=
  TensorProduct.map LinearMap.id (tau F n)

/-! ## Basic API -/

omit [CharZero F] in
/-- `μ^*(π₁^*e) = π₁^*e + π₂^*e` (§6.3). -/
theorem muStarXX_pull1_ι (w : H1 F n) :
    muStarXX F n (pull1 F n (ExteriorAlgebra.ι F w)) =
      pull1 F n (ExteriorAlgebra.ι F w) + pull2 F n (ExteriorAlgebra.ι F w) := by
  simp [muStarXX, pull1, pull2, mu1, ← map_add]

omit [CharZero F] in
/-- `μ^*(π₂^*e) = π₂^*e` (§6.3). -/
theorem muStarXX_pull2_ι (w : H1 F n) :
    muStarXX F n (pull2 F n (ExteriorAlgebra.ι F w)) = pull2 F n (ExteriorAlgebra.ι F w) := by
  simp [muStarXX, pull2, mu1]

omit [CharZero F] in
theorem s23_mu1_comp_mu1Inv : mu1 F n ∘ₗ mu1Inv F n = LinearMap.id := by
  ext x <;> simp [mu1, mu1Inv]

omit [CharZero F] in
theorem s23_mu1Inv_comp_mu1 : mu1Inv F n ∘ₗ mu1 F n = LinearMap.id := by
  ext x <;> simp [mu1, mu1Inv]

set_option linter.unusedSectionVars false in
theorem muStar_comp_muStarInv : muStar F n ∘ₗ muStarInv F n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [muStar, muStarInv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, s23_mu1_comp_mu1Inv,
    ExteriorAlgebra.map_id, AlgHom.id_apply, LinearEquiv.symm_apply_apply]

set_option linter.unusedSectionVars false in
theorem muStarInv_comp_muStar : muStarInv F n ∘ₗ muStar F n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [muStar, muStarInv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, s23_mu1Inv_comp_mu1,
    ExteriorAlgebra.map_id, AlgHom.id_apply, LinearEquiv.symm_apply_apply]

omit [CharZero F] in
theorem tau_tau (s : S F n) : tau F n (tau F n s) = s :=
  CliffordAlgebra.reverse_reverse s

omit [CharZero F] in
theorem tauTensor_comp_tauTensor : tauTensor F n ∘ₗ tauTensor F n = LinearMap.id := by
  ext u v
  simp [tauTensor, tau_tau]

end Defs

end WeilClasses
