module

public import WeilClasses.Main.Jacobian
public import WeilClasses.WeilType.Theta
public import WeilClasses.PureSpinor.Lemma2_2_4
public import WeilClasses.Secant.Defs
public import WeilClasses.PeriodDomain.Defs
public import WeilClasses.External.VanGeemen.Sec3

/-!
# The explicit `X × X̂` and the secant `P_Θ` of §2.4

The statements of Theorem 1.5.1 use the explicit polarized abelian variety of Weil type
`(X × X̂, η, h)` (`fV`, `hV`, `stdStructure` in `WeilClasses.Defs`, `etaV` in
`WeilClasses.Main.Jacobian`), while the paper
constructs it from the oriented `K`-secant `P_Θ` (§2.4: `η` from (2.2.4), `h` the class of `Ξ_P`
(2.4.2), the complex structure `I_{V_ℝ}`). This file states that the two agree for the standard
principal polarization `Θ = ThetaStd`:

* `θ` (2.4.3) is `thetaStd`, and `f = η(√-d)` is `fV`, so `η = etaV`;
* `h = d Θ + Θ̂` is the class of `Ξ_P` under `V ≅ V*` (`(x, ·)_V ↔ x`):
  `⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`;
* the standard complex structure of `X × X̂` is `-I_{V_ℝ}` (`stdStructure_eq_neg`);
* `P_Θ` of §8 (`PJac`) is `PStd`, and `h` is `Ξ_P^♯` (`hClass_PStd`);
* transported to the model by `coordV` (with `I ↦ -I` from the paper's convention to the standard
  one): the Weil-type period domain of `(X × X̂, η, h)` is the image of the paper's `Ω_P` (§4,
  `weilDomain_eq_image_OmegaP`); Hodge classes correspond (`map_mem_hodgeClassesX_iff`); the
  Hodge–Weil classes of `η` are the Hodge–Weil plane of `P_Θ` (Corollary 3.2.2,
  `HWof_eq_map_hwPlane`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Helpers (prefix `s24b_`): transport through `coordV`, eigenspaces, base change of `⋀• V`,
the evaluation `⟪ξ, α ∧ β⟫` of classes of degree `2` (the complex structure `J₀` for which `Θ` is
ample is `s8_J0` of `WeilClasses.Secant.Defs`) -/

section S24bCmpBasic
variable (n : ℕ)

theorem s24b_contractOne_sum {F : Type*} [Field F] [CharZero F] {ι : Type*} (s : Finset ι)
    (ξ : ι → S F n) : contractOne F n (∑ i ∈ s, ξ i) = ∑ i ∈ s, contractOne F n (ξ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s24b_contractOne_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, s24b_contractOne_add, ih]

theorem s24b_sum_fin_two_mul {M : Type*} [AddCommMonoid M] (g : Fin (2 * n) → M) :
    ∑ i, g i = ∑ k : Fin n, (g ⟨2 * k, by omega⟩ + g ⟨2 * k + 1, by omega⟩) := by
  rw [← (finProdFinEquiv.trans (finCongr (mul_comm n 2))).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_two]
  congr 1
  · congr 1
    ext
    simp [finProdFinEquiv]
  · congr 1
    ext
    simp [finProdFinEquiv]
    ring

theorem s24b_ι_anticomm (u v : V ℚ n) :
    ExteriorAlgebra.ι ℚ v * ExteriorAlgebra.ι ℚ u = -(ExteriorAlgebra.ι ℚ u * ExteriorAlgebra.ι ℚ v) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)

theorem s24b_sum_smul_inr (X : H1 ℚ n) :
    ∑ j, (f ℚ n j X) • (((0 : Module.Dual ℚ (H1 ℚ n)), e ℚ n j) : V ℚ n) = (0, X) := by
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · rw [Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact (s24b_H1_eq_sum ℚ n X).symm

theorem s24b_sum_smul_inl (y : Module.Dual ℚ (H1 ℚ n)) :
    ∑ j, (y (e ℚ n j)) • ((f ℚ n j, (0 : H1 ℚ n)) : V ℚ n) = (y, 0) := by
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp only [Prod.smul_fst]
    exact (s24b_dual_eq_sum ℚ n y).symm
  · simp [Prod.snd_sum]

theorem s24b_formToExt2_eq (B : LinearMap.BilinForm ℚ (V ℚ n))
    (hB : ∀ i j, B (vecF ℚ n i) (vecE ℚ n j) = 0) :
    formToExt2 ℚ n B =
      (2 : ℚ)⁻¹ • ∑ i, ExteriorAlgebra.ι ℚ (vecE ℚ n i) *
          ExteriorAlgebra.ι ℚ (∑ j, B (vecF ℚ n i) (vecF ℚ n j) • vecE ℚ n j) +
        (2 : ℚ)⁻¹ • ∑ i, ExteriorAlgebra.ι ℚ (vecF ℚ n i) *
          ExteriorAlgebra.ι ℚ (∑ j, B (vecE ℚ n i) (vecE ℚ n j) • vecF ℚ n j) := by
  simp only [formToExt2, hB, zero_smul, Finset.sum_const_zero, add_zero, map_sum, map_smul,
    Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]

end S24bCmpBasic

section S24bTransport
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s24b_coordV_apply (v : V F n) (k : Fin (2 * (2 * n))) :
    coordV F n v k = (basisV F n).repr v (finCongr (by ring) k) := rfl

theorem s24b_repr_bcV (v : V F n) (k : Fin (2 * n + 2 * n)) :
    (basisV F' n).repr (bcV F F' n v) k = algebraMap F F' ((basisV F n).repr v k) := by
  conv_lhs => rw [← (basisV F n).sum_repr v]
  rw [map_sum, map_sum]
  simp only [map_smul, s24b_bcV_basisV]
  simp only [← algebraMap_smul (A := F') (R := F), map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Algebra.smul_def]

theorem s24b_coordV_bcV (v : V F n) :
    coordV F' n (bcV F F' n v) = bcH1 F F' (2 * n) (coordV F n v) := by
  ext k
  rw [s24b_coordV_apply, s24b_repr_bcV]
  rfl

theorem s24b_coordV_symm_bcH1 (w : H1 F (2 * n)) :
    (coordV F' n).symm (bcH1 F F' (2 * n) w) = bcV F F' n ((coordV F n).symm w) := by
  apply (coordV F' n).injective
  rw [LinearEquiv.apply_symm_apply, s24b_coordV_bcV, LinearEquiv.apply_symm_apply]

theorem s24b_bcEndV_bcV (A : V ℚ n →ₗ[ℚ] V ℚ n) (v : V ℚ n) :
    bcEndV F' n A (bcV ℚ F' n v) = bcV ℚ F' n (A v) :=
  s24b_toLin_map_bc (basisV ℚ n) (basisV F' n) (bcV ℚ F' n) (s24b_bcV_basisV ℚ F' n) A v

omit [CharZero F] [CharZero F'] in
theorem s24b_bcMap_bcH1 {g : ℕ} (φ : H1 F g →ₗ[F] H1 F g) (w : H1 F g) :
    bcMap F F' φ (bcH1 F F' g w) = bcH1 F F' g (φ w) := by
  rw [bcMap, ← Matrix.toLin_eq_toLin', ← LinearMap.toMatrix_eq_toMatrix']
  exact s24b_toLin_map_bc (Pi.basisFun F (Fin (2 * g))) (Pi.basisFun F' (Fin (2 * g)))
    (bcH1 F F' g) (fun i => by rw [← s24b_e_eq, ← s24b_e_eq, s24b_bcH1_e]) φ w

omit [CharZero F] [CharZero F'] in
theorem s24b_H1_ext {g : ℕ} {L L' : H1 F' g →ₗ[F'] H1 F' g}
    (h : ∀ i, L (bcH1 F F' g (e F g i)) = L' (bcH1 F F' g (e F g i))) : L = L' :=
  (Pi.basisFun F' (Fin (2 * g))).ext fun i => by
    rw [← s24b_e_eq, ← s24b_bcH1_e F F' g i]
    exact h i

theorem s24b_bcMap_transportEnd (A : V ℚ n →ₗ[ℚ] V ℚ n) :
    bcMap ℚ F' (transportEnd n A) = transportEnd n (bcEndV F' n A) := by
  apply s24b_H1_ext ℚ F'
  intro i
  rw [s24b_bcMap_bcH1]
  simp only [transportEnd, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [s24b_coordV_symm_bcH1, s24b_bcEndV_bcV, s24b_coordV_bcV]

end S24bTransport

section S24bTransportR
variable (n : ℕ)

theorem s24b_complexifyH1_transportEnd (A : Module.End ℝ (V ℝ n)) :
    complexifyH1 (2 * n) (transportEnd n A) = transportEnd n (complexifyV n A) := by
  apply s24b_H1_ext ℝ ℂ
  intro i
  rw [s24b_complexifyH1_bcH1]
  simp only [transportEnd, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [s24b_coordV_symm_bcH1, s24b_complexifyV_bcV, s24b_coordV_bcV]

theorem s24b_complexifyV_neg (A : Module.End ℝ (V ℝ n)) :
    complexifyV n (-A) = -complexifyV n A := by
  simp [complexifyV, Matrix.map_neg]

end S24bTransportR

section S24bEigen
variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem s24b_eigenspace_conj (e : M ≃ₗ[K] N) (T : Module.End K M) (μ : K) :
    Module.End.eigenspace (e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap) μ =
      (Module.End.eigenspace T μ).map e.toLinearMap := by
  ext v
  simp only [Module.End.mem_eigenspace_iff, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply e.injective
    rw [h, map_smul, e.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [e.symm_apply_apply, hw, map_smul]

theorem s24b_eigenspace_neg (T : Module.End K M) (μ : K) :
    Module.End.eigenspace (-T) μ = Module.End.eigenspace T (-μ) := by
  ext v
  simp only [Module.End.mem_eigenspace_iff, LinearMap.neg_apply, neg_smul]
  constructor
  · intro h
    rw [← neg_neg (T v), h]
  · intro h
    rw [← neg_neg (T v), h]
    simp

end S24bEigen

section S24bExtMap
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem s24b_map_symm_map (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map e.symm.toLinearMap (ExteriorAlgebra.map e.toLinearMap x) = x := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  simp

theorem s24b_map_injective (e : M ≃ₗ[R] N) :
    Function.Injective (ExteriorAlgebra.map e.toLinearMap) :=
  Function.LeftInverse.injective (s24b_map_symm_map e)

theorem s24b_mem_map_iff (e : M ≃ₗ[R] N) (S : Submodule R (ExteriorAlgebra R M))
    (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map e.toLinearMap x ∈ S.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap ↔
      x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← s24b_map_injective e hxy]
  · intro hx
    exact Submodule.mem_map_of_mem hx

theorem s24b_map_mem_exteriorPower (f : M →ₗ[R] N) {k : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) : ExteriorAlgebra.map f x ∈ ⋀[R]^k N := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact ExteriorAlgebra.ιMulti_range R k ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem s24b_map_mem_exteriorPower_iff (e : M ≃ₗ[R] N) {k : ℕ} (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map e.toLinearMap x ∈ ⋀[R]^k N ↔ x ∈ ⋀[R]^k M := by
  constructor
  · intro h
    have := s24b_map_mem_exteriorPower e.symm.toLinearMap h
    rwa [s24b_map_symm_map] at this
  · exact s24b_map_mem_exteriorPower e.toLinearMap

theorem s24b_pqPiece_map (e : M ≃ₗ[R] N) (A B : Submodule R M) (p q : ℕ) :
    pqPiece (A.map e.toLinearMap) (B.map e.toLinearMap) p q =
      (pqPiece A B p q).map (ExteriorAlgebra.map e.toLinearMap).toLinearMap := by
  rw [pqPiece, pqPiece, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine ⟨ExteriorAlgebra.ιMulti R p (e.symm ∘ a) * ExteriorAlgebra.ιMulti R q (e.symm ∘ b),
      ⟨e.symm ∘ a, e.symm ∘ b, fun i => ?_, fun j => ?_, rfl⟩, ?_⟩
    · obtain ⟨y, hy, hy'⟩ := ha i
      simp only [Function.comp_apply, ← hy', LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hy
    · obtain ⟨y, hy, hy'⟩ := hb j
      simp only [Function.comp_apply, ← hy', LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hy
    · simp only [AlgHom.toLinearMap_apply, map_mul, ExteriorAlgebra.map_apply_ιMulti]
      congr 2 <;> ext <;> simp
  · rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    refine ⟨e ∘ a, e ∘ b, fun i => ⟨a i, ha i, rfl⟩, fun j => ⟨b j, hb j, rfl⟩, ?_⟩
    simp only [AlgHom.toLinearMap_apply, map_mul, ExteriorAlgebra.map_apply_ιMulti]
    rfl

theorem s24b_topWedge_map (e : M ≃ₗ[R] N) (W : Submodule R M) (k : ℕ) :
    topWedge (W.map e.toLinearMap) k =
      (topWedge W k).map (ExteriorAlgebra.map e.toLinearMap).toLinearMap := by
  rw [topWedge, topWedge, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨ExteriorAlgebra.ιMulti R k (e.symm ∘ v), ⟨e.symm ∘ v, fun i => ?_, rfl⟩, ?_⟩
    · obtain ⟨y, hy, hy'⟩ := hv i
      simp only [Function.comp_apply, ← hy', LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hy
    · simp only [AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]
      congr 1; ext; simp
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨e ∘ v, fun i => ⟨v i, hv i, rfl⟩, ?_⟩
    simp only [AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]
    rfl

theorem s24b_pqPiece_swap_le (A B : Submodule R M) (p : ℕ) : pqPiece B A p p ≤ pqPiece A B p p := by
  rw [pqPiece, Submodule.span_le]
  rintro _ ⟨b, a, hb, ha, rfl⟩
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R b a]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, b, ha, hb, rfl⟩)

theorem s24b_pqPiece_swap (A B : Submodule R M) (p : ℕ) : pqPiece B A p p = pqPiece A B p p :=
  le_antisymm (s24b_pqPiece_swap_le A B p) (s24b_pqPiece_swap_le B A p)

end S24bExtMap

section S24bBcExt
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s24b_bcExt_ι (v : V F n) :
    bcExt F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcV F F' n v) :=
  ExteriorAlgebra.lift_ι_apply (R := F) _ _ v

theorem s24b_bcS_map_coordV (α : ExtV F n) :
    bcS F F' (2 * n) (ExteriorAlgebra.map (coordV F n).toLinearMap α) =
      ExteriorAlgebra.map (coordV F' n).toLinearMap (bcExt F F' n α) := by
  induction α using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F F' (S F' (2 * n)),
      IsScalarTower.algebraMap_apply F F' (ExtV F' n), AlgHom.commutes]
  | ι v =>
    rw [ExteriorAlgebra.map_apply_ι, s24b_bcS_ι, s24b_bcExt_ι, ExteriorAlgebra.map_apply_ι,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, s24b_coordV_bcV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem s24b_bcExt_ιMulti (k : ℕ) (v : Fin k → V F n) :
    bcExt F F' n (ExteriorAlgebra.ιMulti F k v) = ExteriorAlgebra.ιMulti F' k (bcV F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simp [List.map_ofFn, Function.comp_def, s24b_bcExt_ι]

omit [CharZero F] in
theorem s24b_basisExt_apply (J : Finset (Fin (2 * n + 2 * n))) (k : ℕ) (h : J.card = k) :
    basisExt F n J = ExteriorAlgebra.ιMulti F k (fun i => basisV F n (J.orderEmbOfFin h i)) := by
  rw [basisExt, ExteriorAlgebra.basis_apply_ofCard _ h]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

theorem s24b_bcExt_basisExt (J : Finset (Fin (2 * n + 2 * n))) :
    bcExt F F' n (basisExt F n J) = basisExt F' n J := by
  rw [s24b_basisExt_apply F n J _ rfl, s24b_basisExt_apply F' n J _ rfl, s24b_bcExt_ιMulti]
  congr 1
  ext1 i
  simp [s24b_bcV_basisV]

theorem s24b_repr_bcExt (x : ExtV F n) (J : Finset (Fin (2 * n + 2 * n))) :
    (basisExt F' n).repr (bcExt F F' n x) J = algebraMap F F' ((basisExt F n).repr x J) := by
  conv_lhs => rw [← (basisExt F n).sum_repr x]
  rw [map_sum]
  simp only [map_smul, s24b_bcExt_basisExt]
  rw [map_sum]
  simp only [← algebraMap_smul (A := F') (R := F), map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Algebra.smul_def]

theorem s24b_bcExt_injective : Function.Injective (bcExt F F' n) := by
  intro s t h
  apply (basisExt F n).repr.injective
  ext1 J
  have := congrArg (fun x => (basisExt F' n).repr x J) h
  simp only [s24b_repr_bcExt] at this
  exact (algebraMap F F').injective this

theorem s24b_bcExt_proj (j : ℕ) (x : ExtV F n) :
    bcExt F F' n (GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (V F n)) j x) =
      GradedAlgebra.proj (fun i : ℕ => ⋀[F']^i (V F' n)) j (bcExt F F' n x) := by
  have hx : x ∈ (⊤ : Submodule F (ExtV F n)) := Submodule.mem_top
  rw [← ExteriorAlgebra.ιMulti_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨m, v⟩, rfl⟩ := hy
    have h1 : ExteriorAlgebra.ιMulti F m v ∈ ⋀[F]^m (V F n) :=
      ExteriorAlgebra.ιMulti_range F m ⟨_, rfl⟩
    have h2 : bcExt F F' n (ExteriorAlgebra.ιMulti F m v) ∈ ⋀[F']^m (V F' n) := by
      rw [s24b_bcExt_ιMulti]
      exact ExteriorAlgebra.ιMulti_range F' m ⟨_, rfl⟩
    by_cases hmj : m = j
    · subst hmj
      rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F]^i (V F n)) h1,
        DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[F']^i (V F' n)) h2]
    · rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F]^i (V F n)) h1 hmj,
        DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F']^i (V F' n)) h2 hmj, map_zero]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | smul c y _ hy =>
    rw [map_smul, map_smul, hy, map_smul, ← algebraMap_smul F' c (bcExt F F' n y), map_smul,
      algebraMap_smul]

omit [CharZero F] in
theorem s24b_mem_of_proj (k : ℕ) (x : ExtV F n)
    (h : ∀ j, j ≠ k → GradedAlgebra.proj (fun i : ℕ => ⋀[F]^i (V F n)) j x = 0) :
    x ∈ ⋀[F]^k (V F n) := by
  classical
  rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[F]^i (V F n)) x]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hjk : j = k
  · subst hjk
    exact SetLike.coe_mem _
  · have := h j hjk
    rw [GradedAlgebra.proj_apply] at this
    rw [this]
    exact Submodule.zero_mem _

theorem s24b_mem_exteriorPower_of_bcExt {k : ℕ} {x : ExtV F n}
    (h : bcExt F F' n x ∈ ⋀[F']^k (V F' n)) : x ∈ ⋀[F]^k (V F n) := by
  apply s24b_mem_of_proj F n k x
  intro j hjk
  apply s24b_bcExt_injective F F' n
  rw [s24b_bcExt_proj, map_zero, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[F']^i (V F' n)) h (Ne.symm hjk)]

end S24bBcExt

section S24bEigenK
variable (n : ℕ) (d : ℚ)

theorem s24b_bcEndV_η (hd : 0 < d) (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) (l : Kd d) :
    bcEndV (Kd d) n (P.η hW l) = P.ηK hW l := by
  refine (basisV (Kd d) n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℚ (Kd d) n k, s24b_bcEndV_bcV, P.ηK_bcV hd hW]

theorem s24b_eigenspace_ηK (hd : 0 < d) (P : KSecant n d) (hW : IsCompl P.W₁ P.W₂) :
    Module.End.eigenspace (P.ηK hW (Kd.sqrtNeg d)) (Kd.sqrtNeg d) = P.W₁ ∧
      Module.End.eigenspace (P.ηK hW (Kd.sqrtNeg d)) (-Kd.sqrtNeg d) = P.W₂ := by
  have hs := s24b_sqrtNeg_ne_zero hd
  have h2s : (2 : Kd d) * Kd.sqrtNeg d ≠ 0 := mul_ne_zero two_ne_zero hs
  constructor
  · ext v
    rw [Module.End.mem_eigenspace_iff]
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp (hW.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ P.W₁ ⊔ P.W₂)
    rw [s24b_ηK_add n d P hW _ hw₁ hw₂, s24b_σ_sqrtNeg]
    constructor
    · intro h
      have h' : ((2 : Kd d) * Kd.sqrtNeg d) • w₂ = 0 := by
        rw [mul_smul, two_smul]
        have := congrArg (fun x => Kd.sqrtNeg d • (w₁ + w₂) - x) h
        simp only [sub_self] at this
        rw [← this]
        module
      rw [(smul_eq_zero.mp h').resolve_left h2s, add_zero]
      exact hw₁
    · intro h
      have hw₂' : w₂ ∈ P.W₁ := by
        have := P.W₁.sub_mem h hw₁
        simpa using this
      have hw₂0 : w₂ = 0 := (Submodule.disjoint_def.mp hW.disjoint) w₂ hw₂' hw₂
      rw [hw₂0]
      simp
  · ext v
    rw [Module.End.mem_eigenspace_iff]
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp (hW.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ P.W₁ ⊔ P.W₂)
    rw [s24b_ηK_add n d P hW _ hw₁ hw₂, s24b_σ_sqrtNeg]
    constructor
    · intro h
      have h' : ((2 : Kd d) * Kd.sqrtNeg d) • w₁ = 0 := by
        rw [mul_smul, two_smul]
        have := congrArg (fun x => x - (-Kd.sqrtNeg d) • (w₁ + w₂)) h
        simp only [sub_self] at this
        rw [← this]
        module
      rw [(smul_eq_zero.mp h').resolve_left h2s, zero_add]
      exact hw₂
    · intro h
      have hw₁' : w₁ ∈ P.W₂ := by
        have := P.W₂.sub_mem h hw₂
        simpa using this
      have hw₁0 : w₁ = 0 := (Submodule.disjoint_def.mp hW.disjoint) w₁ hw₁ hw₁'
      rw [hw₁0]
      simp

theorem s24b_topWedge_le {F : Type*} [Field F] [CharZero F] (W : Submodule F (V F n)) (k : ℕ) :
    topWedge W k ≤ ⋀[F]^k (V F n) := by
  rw [topWedge, Submodule.span_le]
  rintro _ ⟨v, -, rfl⟩
  exact ExteriorAlgebra.ιMulti_range F k ⟨_, rfl⟩

end S24bEigenK

section S24bPairing
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

theorem s24b_pairing_bcV (v w : V F n) :
    pairing F' n (bcV F F' n v) (bcV F F' n w) = algebraMap F F' (pairing F n v w) := by
  rw [s24b_pairing_apply, s24b_pairing_apply]
  simp only [bcV, LinearMap.prodMap_apply, s24b_bcDual_bcH1, map_add]

theorem s24b_bcEndV_comp (A B : V ℚ n →ₗ[ℚ] V ℚ n) :
    bcEndV F' n (A ∘ₗ B) = bcEndV F' n A ∘ₗ bcEndV F' n B := by
  refine (basisV F' n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℚ F' n k]
  simp only [LinearMap.comp_apply, s24b_bcEndV_bcV]

theorem s24b_bcEndV_smul_one (c : ℚ) :
    bcEndV F' n (c • LinearMap.id) = (algebraMap ℚ F' c) • LinearMap.id := by
  refine (basisV F' n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℚ F' n k, s24b_bcEndV_bcV, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul, algebraMap_smul]

theorem s24b_bcEndV_neg (A : V ℚ n →ₗ[ℚ] V ℚ n) : bcEndV F' n (-A) = -bcEndV F' n A := by
  refine (basisV F' n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℚ F' n k, s24b_bcEndV_bcV]
  simp [s24b_bcEndV_bcV]

theorem s24b_pairing_nondeg (x : V F n) (h : ∀ y, pairing F n x y = 0) : x = 0 := by
  refine Prod.ext ?_ ?_
  · apply s24b_dual_ext
    intro i
    have := h (0, e F n i)
    rw [s24b_pairing_apply] at this
    simpa using this
  · ext i
    have := h (f F n i, 0)
    rw [s24b_pairing_apply] at this
    simpa [f] using this

theorem s24b_pairing_injective : Function.Injective (pairing F n) := by
  intro x y h
  have := s24b_pairing_nondeg F n (x - y) (fun z => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self])
  exact sub_eq_zero.mp this

theorem s24b_pairing_surjective : Function.Surjective (pairing F n) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp (s24b_pairing_injective F n)

end S24bPairing

section S24bEv
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `⟪ξ, α ∧ β⟫ = β ⌋ (α ⌋ ξ)` (degree-`0` part). -/
noncomputable def s24b_ev (ξ : ExteriorAlgebra R M) (α β : Module.Dual R M) : R :=
  ExteriorAlgebra.algebraMapInv (contractLeft (Q := 0) β (contractLeft (Q := 0) α ξ))

theorem s24b_contractLeft_map (g : M →ₗ[R] N) (α : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := 0) α (ExteriorAlgebra.map g x) =
      ExteriorAlgebra.map g (contractLeft (Q := 0) (α ∘ₗ g) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul, show ExteriorAlgebra.map g (CliffordAlgebra.ι 0 m) = ExteriorAlgebra.ι R (g m) from
      ExteriorAlgebra.map_apply_ι g m]
    erw [contractLeft_ι_mul, contractLeft_ι_mul]
    rw [hx, map_sub, map_smul, map_mul, LinearMap.comp_apply]
    congr 2
    exact (ExteriorAlgebra.map_apply_ι g m).symm

theorem s24b_algebraMapInv_map (g : M →ₗ[R] N) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map g x) = ExteriorAlgebra.algebraMapInv x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.algebraMapInv]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem s24b_ev_map (g : M →ₗ[R] N) (ξ : ExteriorAlgebra R M) (α β : Module.Dual R N) :
    s24b_ev (ExteriorAlgebra.map g ξ) α β = s24b_ev ξ (α ∘ₗ g) (β ∘ₗ g) := by
  rw [s24b_ev, s24b_contractLeft_map, s24b_contractLeft_map, s24b_algebraMapInv_map]
  rfl

theorem s24b_ev_ι_mul_ι' {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (u v : M)
    (α β : Module.Dual R M) :
    s24b_ev (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) α β = α u * β v - α v * β u := by
  have hι : ∀ w : M, ExteriorAlgebra.ι R w = CliffordAlgebra.ι (0 : QuadraticForm R M) w :=
    fun _ => rfl
  have h1 : contractLeft (Q := 0) α (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
      α u • ExteriorAlgebra.ι R v - α v • ExteriorAlgebra.ι R u := by
    rw [hι, hι, contractLeft_ι_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]
  rw [s24b_ev, h1, map_sub, map_smul, map_smul, hι, hι, contractLeft_ι, contractLeft_ι, map_sub,
    map_smul, map_smul, ExteriorAlgebra.algebraMap_leftInverse,
    ExteriorAlgebra.algebraMap_leftInverse, smul_eq_mul, smul_eq_mul]

end S24bEv

section S24bEv2
variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] in
theorem s24b_coord_empty (x : S F n) :
    (basisS F n).coord ∅ x = ExteriorAlgebra.algebraMapInv x := by
  have h : (basisS F n).coord ∅ = (ExteriorAlgebra.algebraMapInv : S F n →ₐ[F] F).toLinearMap := by
    refine (basisS F n).ext fun J => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, AlgHom.toLinearMap_apply]
    by_cases hJ : J = ∅
    · subst hJ
      rw [s24b_basisS_empty]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, J.card = k + 1 :=
        ⟨J.card - 1, by have := Finset.nonempty_iff_ne_empty.mpr hJ; have := this.card_pos; omega⟩
      rw [s24b_basisS_apply' F n J (k + 1) hk, ExteriorAlgebra.ιMulti_succ_apply, map_mul]
      simp [ExteriorAlgebra.algebraMapInv, Ne.symm hJ]
  rw [h]
  rfl

theorem s24b_eval2_map {g : ℕ} (e : V F n →ₗ[F] H1 F g) (ξ : ExtV F n)
    (a b : Module.Dual F (H1 F g)) :
    eval2 F g (ExteriorAlgebra.map e ξ) a b = s24b_ev ξ (a ∘ₗ e) (b ∘ₗ e) := by
  rw [eval2, s24b_coord_empty, ← s24b_ev_map]
  rfl

theorem s24b_contractLeft_bcExt (α : Module.Dual F (V F n)) (α' : Module.Dual F' (V F' n))
    (hα : ∀ v, α' (bcV F F' n v) = algebraMap F F' (α v)) (ξ : ExtV F n) :
    contractLeft (Q := 0) α' (bcExt F F' n ξ) = bcExt F F' n (contractLeft (Q := 0) α ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [contractLeft_algebraMap, AlgHom.commutes, map_zero]
    rw [IsScalarTower.algebraMap_apply F F' (ExtV F' n), contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    have h1 : bcExt F F' n (CliffordAlgebra.ι 0 m * x) =
        ExteriorAlgebra.ι F' (bcV F F' n m) * bcExt F F' n x := by
      rw [map_mul]
      congr 1
      exact s24b_bcExt_ι F F' n m
    rw [h1]
    erw [contractLeft_ι_mul, contractLeft_ι_mul]
    rw [hx, map_sub, map_smul, map_mul, hα, algebraMap_smul]
    congr 2
    exact (s24b_bcExt_ι F F' n m).symm

theorem s24b_algebraMapInv_bcExt (ξ : ExtV F n) :
    ExteriorAlgebra.algebraMapInv (bcExt F F' n ξ) =
      algebraMap F F' (ExteriorAlgebra.algebraMapInv ξ) := by
  induction ξ using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (ExtV F' n)]
    simp
  | ι m => rw [s24b_bcExt_ι]; simp [ExteriorAlgebra.algebraMapInv]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem s24b_ev_bcExt (ξ : ExtV F n) (α β : Module.Dual F (V F n))
    (α' β' : Module.Dual F' (V F' n)) (hα : ∀ v, α' (bcV F F' n v) = algebraMap F F' (α v))
    (hβ : ∀ v, β' (bcV F F' n v) = algebraMap F F' (β v)) :
    s24b_ev (bcExt F F' n ξ) α' β' = algebraMap F F' (s24b_ev ξ α β) := by
  rw [s24b_ev, s24b_contractLeft_bcExt F F' n α α' hα, s24b_contractLeft_bcExt F F' n β β' hβ,
    s24b_algebraMapInv_bcExt]
  rfl

omit [CharZero F] in
theorem s24b_ev_ι_mul_ι (u v : V F n) (α β : Module.Dual F (V F n)) :
    s24b_ev (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v) α β = α u * β v - α v * β u := by
  have hι : ∀ w : V F n, ExteriorAlgebra.ι F w = CliffordAlgebra.ι (0 : QuadraticForm F (V F n)) w :=
    fun _ => rfl
  have h1 : contractLeft (Q := 0) α (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v) =
      α u • ExteriorAlgebra.ι F v - α v • ExteriorAlgebra.ι F u := by
    rw [hι, hι, contractLeft_ι_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]
  rw [s24b_ev, h1, map_sub, map_smul, map_smul, hι, hι, contractLeft_ι, contractLeft_ι, map_sub,
    map_smul, map_smul, ExteriorAlgebra.algebraMap_leftInverse, ExteriorAlgebra.algebraMap_leftInverse,
    smul_eq_mul, smul_eq_mul]

theorem s24b_bcExt_mem_exteriorPower {k : ℕ} {x : ExtV F n} (hx : x ∈ ⋀[F]^k (V F n)) :
    bcExt F F' n x ∈ ⋀[F']^k (V F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [s24b_bcExt_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' k ⟨_, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul, ← algebraMap_smul (A := F')]
    exact Submodule.smul_mem _ _ hy

end S24bEv2

section S24bRecon
variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s24b_ev_add_left (ξ : ExtV F n) (α α' β : Module.Dual F (V F n)) :
    s24b_ev ξ (α + α') β = s24b_ev ξ α β + s24b_ev ξ α' β := by
  simp [s24b_ev, map_add, LinearMap.add_apply]

omit [CharZero F] in
theorem s24b_ev_smul_left (ξ : ExtV F n) (c : F) (α β : Module.Dual F (V F n)) :
    s24b_ev ξ (c • α) β = c • s24b_ev ξ α β := by
  simp [s24b_ev, map_smul, LinearMap.smul_apply]

omit [CharZero F] in
theorem s24b_ev_add_right (ξ : ExtV F n) (α β β' : Module.Dual F (V F n)) :
    s24b_ev ξ α (β + β') = s24b_ev ξ α β + s24b_ev ξ α β' := by
  simp [s24b_ev, map_add, LinearMap.add_apply]

omit [CharZero F] in
theorem s24b_ev_smul_right (ξ : ExtV F n) (c : F) (α β : Module.Dual F (V F n)) :
    s24b_ev ξ α (c • β) = c • s24b_ev ξ α β := by
  simp [s24b_ev, map_smul, LinearMap.smul_apply]

omit [CharZero F] in
theorem s24b_ev_add (ξ η : ExtV F n) (α β : Module.Dual F (V F n)) :
    s24b_ev (ξ + η) α β = s24b_ev ξ α β + s24b_ev η α β := by
  simp [s24b_ev, map_add]

omit [CharZero F] in
theorem s24b_ev_smul (c : F) (ξ : ExtV F n) (α β : Module.Dual F (V F n)) :
    s24b_ev (c • ξ) α β = c • s24b_ev ξ α β := by
  simp [s24b_ev, map_smul]

/-- The bilinear form `(x, y) ↦ ⟪ξ, (x, ·)_V ∧ (y, ·)_V⟫` of a class `ξ`. -/
noncomputable def s24b_evForm (ξ : ExtV F n) : LinearMap.BilinForm F (V F n) :=
  LinearMap.mk₂ F (fun x y => s24b_ev ξ (pairing F n x) (pairing F n y))
    (fun x x' y => by simp only [map_add, s24b_ev_add_left])
    (fun c x y => by simp only [map_smul, s24b_ev_smul_left])
    (fun x y y' => by simp only [map_add, s24b_ev_add_right])
    (fun c x y => by simp only [map_smul, s24b_ev_smul_right])

omit [CharZero F] in
theorem s24b_evForm_apply (ξ : ExtV F n) (x y : V F n) :
    s24b_evForm F n ξ x y = s24b_ev ξ (pairing F n x) (pairing F n y) := rfl

omit [CharZero F] in
theorem s24b_formToExt2_add (B B' : LinearMap.BilinForm F (V F n)) :
    formToExt2 F n (B + B') = formToExt2 F n B + formToExt2 F n B' := by
  simp only [formToExt2, LinearMap.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  abel

theorem s24b_formToExt2_smul (c : F) (B : LinearMap.BilinForm F (V F n)) :
    formToExt2 F n (c • B) = c • formToExt2 F n B := by
  simp only [formToExt2, LinearMap.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring

omit [CharZero F] in
theorem s24b_double_sum {ι A : Type*} [Fintype ι] [Ring A] [Algebra F A] (a b c e : ι → F)
    (X Y : ι → A) :
    ∑ i, ∑ j, (a i * b j - c i * e j) • (X i * Y j) =
      (∑ i, a i • X i) * (∑ j, b j • Y j) - (∑ i, c i • X i) * (∑ j, e j • Y j) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul, smul_mul_smul_comm, smul_mul_smul_comm]

theorem s24b_pairing_vecF (i : Fin (2 * n)) (u : V F n) : pairing F n (vecF F n i) u = u.2 i := by
  rw [s24b_pairing_apply]
  simp [vecF, f]

theorem s24b_pairing_vecE (i : Fin (2 * n)) (u : V F n) :
    pairing F n (vecE F n i) u = u.1 (e F n i) := by
  rw [s24b_pairing_apply]
  simp [vecE]

omit [CharZero F] in
theorem s24b_sum_vecE (u : V F n) : ∑ i, u.2 i • vecE F n i = ((0 : Module.Dual F (H1 F n)), u.2) := by
  refine Prod.ext ?_ ?_
  · simp [vecE, Prod.fst_sum]
  · rw [Prod.snd_sum]
    simp only [vecE, Prod.smul_snd]
    exact (s24b_H1_eq_sum F n u.2).symm

omit [CharZero F] in
theorem s24b_sum_vecF (u : V F n) : ∑ j, u.1 (e F n j) • vecF F n j = (u.1, (0 : H1 F n)) := by
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp only [vecF, Prod.smul_fst]
    exact (s24b_dual_eq_sum F n u.1).symm
  · simp [vecF, Prod.snd_sum]

theorem s24b_formToExt2_ι_mul_ι (u v : V F n) :
    formToExt2 F n (s24b_evForm F n (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v)) =
      ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v := by
  have hιE : ∀ w : V F n, ∑ i, w.2 i • ExteriorAlgebra.ι F (vecE F n i) = ExteriorAlgebra.ι F ((0 : Module.Dual F (H1 F n)), w.2) := by
    intro w
    rw [← s24b_sum_vecE, map_sum]
    simp [map_smul]
  have hιF : ∀ w : V F n, ∑ i, w.1 (e F n i) • ExteriorAlgebra.ι F (vecF F n i) = ExteriorAlgebra.ι F (w.1, (0 : H1 F n)) := by
    intro w
    rw [← s24b_sum_vecF, map_sum]
    simp [map_smul]
  have h1 : ∑ i, ∑ j, ((2 : F)⁻¹ * s24b_evForm F n (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v)
      (vecF F n i) (vecF F n j)) • (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecE F n j)) =
      ∑ i, ∑ j, ((2⁻¹ * u.2 i) * v.2 j - (2⁻¹ * v.2 i) * u.2 j) • (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecE F n j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [s24b_evForm_apply, s24b_ev_ι_mul_ι, s24b_pairing_vecF, s24b_pairing_vecF,
      s24b_pairing_vecF, s24b_pairing_vecF]
    congr 1; ring
  have h2 : ∑ i, ∑ j, s24b_evForm F n (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v)
      (vecF F n i) (vecE F n j) • (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecF F n j)) =
      ∑ i, ∑ j, (u.2 i * v.1 (e F n j) - v.2 i * u.1 (e F n j)) • (ExteriorAlgebra.ι F (vecE F n i) * ExteriorAlgebra.ι F (vecF F n j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [s24b_evForm_apply, s24b_ev_ι_mul_ι, s24b_pairing_vecF, s24b_pairing_vecF,
      s24b_pairing_vecE, s24b_pairing_vecE]
  have h3 : ∑ i, ∑ j, ((2 : F)⁻¹ * s24b_evForm F n (ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v)
      (vecE F n i) (vecE F n j)) • (ExteriorAlgebra.ι F (vecF F n i) * ExteriorAlgebra.ι F (vecF F n j)) =
      ∑ i, ∑ j, ((2⁻¹ * u.1 (e F n i)) * v.1 (e F n j) - (2⁻¹ * v.1 (e F n i)) * u.1 (e F n j)) •
        (ExteriorAlgebra.ι F (vecF F n i) * ExteriorAlgebra.ι F (vecF F n j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [s24b_evForm_apply, s24b_ev_ι_mul_ι, s24b_pairing_vecE, s24b_pairing_vecE,
      s24b_pairing_vecE, s24b_pairing_vecE]
    congr 1; ring
  rw [formToExt2]
  rw [h1, h2, h3, s24b_double_sum, s24b_double_sum, s24b_double_sum]
  simp only [mul_smul, ← Finset.smul_sum, hιE, hιF, smul_mul_assoc]
  set UE := ExteriorAlgebra.ι F (((0 : Module.Dual F (H1 F n)), u.2) : V F n)
  set VE := ExteriorAlgebra.ι F (((0 : Module.Dual F (H1 F n)), v.2) : V F n)
  set UF := ExteriorAlgebra.ι F ((u.1, (0 : H1 F n)) : V F n)
  set VF := ExteriorAlgebra.ι F ((v.1, (0 : H1 F n)) : V F n)
  have hu : ExteriorAlgebra.ι F u = UE + UF := by
    rw [← map_add]; congr 1; ext <;> simp
  have hv : ExteriorAlgebra.ι F v = VE + VF := by
    rw [← map_add]; congr 1; ext <;> simp
  have a1 : VE * UE = -(UE * VE) := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  have a2 : VF * UF = -(UF * VF) := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  have a3 : VE * UF = -(UF * VE) := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [hu, hv, a1, a2, a3, add_mul, mul_add, mul_add]
  module

omit [CharZero F] in
theorem s24b_evForm_add (ξ η : ExtV F n) :
    s24b_evForm F n (ξ + η) = s24b_evForm F n ξ + s24b_evForm F n η := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  simp [s24b_evForm_apply, s24b_ev_add]

omit [CharZero F] in
theorem s24b_evForm_smul (c : F) (ξ : ExtV F n) :
    s24b_evForm F n (c • ξ) = c • s24b_evForm F n ξ := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  simp [s24b_evForm_apply, s24b_ev_smul]

omit [CharZero F] in
theorem s24b_formToExt2_zero : formToExt2 F n 0 = 0 := by
  simp [formToExt2]

theorem s24b_formToExt2_evForm (ξ : ExtV F n) (hξ : ξ ∈ ⋀[F]^2 (V F n)) :
    formToExt2 F n (s24b_evForm F n ξ) = ξ := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hξ
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    exact s24b_formToExt2_ι_mul_ι F n _ _
  | zero =>
    have : s24b_evForm F n 0 = 0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      simp [s24b_evForm_apply, s24b_ev]
    rw [this, s24b_formToExt2_zero]
  | add x y _ _ hx hy => rw [s24b_evForm_add, s24b_formToExt2_add, hx, hy]
  | smul c x _ hx => rw [s24b_evForm_smul, s24b_formToExt2_smul, hx]

theorem s24b_eq_of_ev {ξ η : ExtV F n} (hξ : ξ ∈ ⋀[F]^2 (V F n)) (hη : η ∈ ⋀[F]^2 (V F n))
    (h : ∀ x y, s24b_ev ξ (pairing F n x) (pairing F n y) = s24b_ev η (pairing F n x) (pairing F n y)) :
    ξ = η := by
  have : s24b_evForm F n ξ = s24b_evForm F n η :=
    LinearMap.ext fun x => LinearMap.ext fun y => h x y
  rw [← s24b_formToExt2_evForm F n ξ hξ, ← s24b_formToExt2_evForm F n η hη, this]

end S24bRecon

section S24bTransportAlg
variable (n : ℕ)

theorem s24b_transportEnd_mul {F : Type*} [Field F] [CharZero F] (A B : Module.End F (V F n)) :
    transportEnd n (A * B) = transportEnd n A * transportEnd n B := by
  refine LinearMap.ext fun w => ?_
  simp [transportEnd]

theorem s24b_transportEnd_neg {F : Type*} [Field F] [CharZero F] (A : Module.End F (V F n)) :
    transportEnd n (-A) = -transportEnd n A := by
  refine LinearMap.ext fun w => ?_
  simp [transportEnd]

theorem s24b_transportEnd_one {F : Type*} [Field F] [CharZero F] :
    transportEnd n (1 : Module.End F (V F n)) = 1 := by
  refine LinearMap.ext fun w => ?_
  simp [transportEnd]

theorem s24b_transportEnd_injective {F : Type*} [Field F] [CharZero F] :
    Function.Injective (transportEnd (F := F) n) := by
  intro A B h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h (coordV F n v)
  simpa [transportEnd] using this

/-- The endomorphism of `V_F` corresponding to an endomorphism of the model `F^{4n}`. -/
noncomputable def s24b_untransport {F : Type*} [Field F] [CharZero F]
    (B : Module.End F (H1 F (2 * n))) : Module.End F (V F n) :=
  (coordV F n).symm.toLinearMap ∘ₗ B ∘ₗ (coordV F n).toLinearMap

theorem s24b_transportEnd_untransport {F : Type*} [Field F] [CharZero F]
    (B : Module.End F (H1 F (2 * n))) : transportEnd n (s24b_untransport n B) = B := by
  refine LinearMap.ext fun w => ?_
  simp [transportEnd, s24b_untransport]

theorem s24b_isComplexStructure_transportEnd (I : Module.End ℝ (V ℝ n)) :
    IsComplexStructure (transportEnd n (-I)) ↔ IsComplexStructure I := by
  unfold IsComplexStructure
  rw [← s24b_transportEnd_mul, neg_mul_neg, ← s24b_transportEnd_one, ← s24b_transportEnd_neg]
  exact (s24b_transportEnd_injective n).eq_iff

theorem s24b_pairing_symm {F : Type*} [Field F] [CharZero F] (x y : V F n) :
    pairing F n x y = pairing F n y x := by
  rw [s24b_pairing_apply, s24b_pairing_apply, add_comm]

/-- For an orthogonal complex structure `I`: `(x, I ·)_V = (-I x, ·)_V`. -/
theorem s24b_pairing_comp_I (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (x : V ℝ n) :
    pairing ℝ n x ∘ₗ I = pairing ℝ n (-(I x)) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, ← hIso x (I y), ← Module.End.mul_apply I I y, hI]
  simp

theorem s24b_bcV_bcV (F F' F'' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F']
    [Field F''] [CharZero F''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower F F' F''] (v : V F n) : bcV F' F'' n (bcV F F' n v) = bcV F F'' n v := by
  simp only [bcV, LinearMap.prodMap_apply, s24b_bcDual_bcDual, s24b_bcH1_bcH1]

theorem s24b_complexifyV_mul (A B : Module.End ℝ (V ℝ n)) :
    complexifyV n (A * B) = complexifyV n A * complexifyV n B := by
  refine (basisV ℂ n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℝ ℂ n k, Module.End.mul_apply, s24b_complexifyV_bcV, s24b_complexifyV_bcV,
    s24b_complexifyV_bcV, Module.End.mul_apply]

theorem s24b_complexifyV_one : complexifyV n (1 : Module.End ℝ (V ℝ n)) = 1 := by
  refine (basisV ℂ n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℝ ℂ n k, s24b_complexifyV_bcV]
  rfl

theorem s24b_complexifyV_bcEndV (A : V ℚ n →ₗ[ℚ] V ℚ n) :
    complexifyV n (bcEndV ℝ n A) = bcEndV ℂ n A := by
  refine (basisV ℂ n).ext fun k => ?_
  rw [← s24b_bcV_basisV ℚ ℂ n k, s24b_bcEndV_bcV, ← s24b_bcV_bcV n ℚ ℝ ℂ (basisV ℚ n k),
    s24b_complexifyV_bcV, s24b_bcEndV_bcV, s24b_bcV_bcV]

theorem s24b_bcEndV_tower (d : ℚ) (A : V ℚ n →ₗ[ℚ] V ℚ n) (w : V (Kd d) n) :
    bcEndV ℂ n A (bcV (Kd d) ℂ n w) = bcV (Kd d) ℂ n (bcEndV (Kd d) n A w) := by
  let L1 : V (Kd d) n →ₗ[Kd d] V ℂ n :=
    ((bcEndV ℂ n A).restrictScalars (Kd d)) ∘ₗ bcV (Kd d) ℂ n
  let L2 : V (Kd d) n →ₗ[Kd d] V ℂ n := bcV (Kd d) ℂ n ∘ₗ bcEndV (Kd d) n A
  have h : L1 = L2 := by
    refine (basisV (Kd d) n).ext fun k => ?_
    simp only [L1, L2, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    rw [← s24b_bcV_basisV ℚ (Kd d) n k, s24b_bcV_bcV n ℚ (Kd d) ℂ, s24b_bcEndV_bcV,
      s24b_bcEndV_bcV, s24b_bcV_bcV n ℚ (Kd d) ℂ]
  exact LinearMap.congr_fun h w

theorem s24b_finrank_graph (T : Module.Dual ℂ (H1 ℂ n) →ₗ[ℂ] H1 ℂ n) :
    Module.finrank ℂ (LinearMap.range (LinearMap.prod LinearMap.id T)) = 2 * n := by
  rw [LinearMap.finrank_range_of_inj, Subspace.dual_finrank_eq]
  · simp
  · intro y y' h
    have := congrArg Prod.fst h
    simpa using this

theorem s24b_H10_transport (I : Module.End ℝ (V ℝ n)) :
    H10 (2 * n) (transportEnd n (-I)) = (V01 n I).map (coordV ℂ n).toLinearMap := by
  rw [H10, s24b_complexifyH1_transportEnd, transportEnd, s24b_eigenspace_conj,
    s24b_complexifyV_neg, s24b_eigenspace_neg]
  rfl

theorem s24b_finrank_map_inf (A B : Submodule ℂ (V ℂ n)) :
    Module.finrank ℂ ↥(A.map (coordV ℂ n).toLinearMap ⊓ B.map (coordV ℂ n).toLinearMap) =
      Module.finrank ℂ ↥(A ⊓ B) := by
  rw [← Submodule.map_inf _ (coordV ℂ n).injective]
  exact LinearEquiv.finrank_map_eq (coordV ℂ n) (A ⊓ B)

theorem s24b_complexifyV_sq (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    complexifyV n I * complexifyV n I = -1 := by
  rw [← s24b_complexifyV_mul, hI, s24b_complexifyV_neg, s24b_complexifyV_one]

theorem s24b_V10_inf_V01 (I : Module.End ℝ (V ℝ n)) : V10 n I ⊓ V01 n I = ⊥ := by
  have hne : Complex.I ≠ -Complex.I := by
    intro h
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination h
    exact mul_ne_zero two_ne_zero Complex.I_ne_zero this
  exact ((Module.End.eigenspaces_iSupIndep (complexifyV n I)).pairwiseDisjoint hne).eq_bot

theorem s24b_rho_isometry (g : Spin ℝ n) (u v : V ℝ n) :
    pairing ℝ n (rho ℝ n g u) (rho ℝ n g v) = pairing ℝ n u v := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, rho,
    spinVectorAction_map_app]

end S24bTransportAlg

section S24bDet
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem s24b_det_of_isCompl [FiniteDimensional K M] (T : Module.End K M) (U₁ U₂ : Submodule K M)
    (h : IsCompl U₁ U₂) (a b : K) (h1 : ∀ x ∈ U₁, T x = a • x) (h2 : ∀ x ∈ U₂, T x = b • x) :
    LinearMap.det T = a ^ Module.finrank K U₁ * b ^ Module.finrank K U₂ := by
  set e := Submodule.prodEquivOfIsCompl _ _ h
  have hT : T = e.toLinearMap ∘ₗ
      (LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id)) ∘ₗ e.symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    simp only [Submodule.coe_smul]
    rw [h1 _ y.1.2, h2 _ y.2.2]
  rw [congrArg LinearMap.det hT, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

theorem s24b_det_restrict [FiniteDimensional K M] (T : Module.End K M) (W U₁ U₂ : Submodule K M)
    (hT : ∀ x ∈ W, T x ∈ W) (hU₁ : U₁ ≤ W) (hU₂ : U₂ ≤ W) (hdisj : U₁ ⊓ U₂ = ⊥)
    (hsup : U₁ ⊔ U₂ = W) (a b : K) (h1 : ∀ x ∈ U₁, T x = a • x) (h2 : ∀ x ∈ U₂, T x = b • x) :
    LinearMap.det (T.restrict hT) = a ^ Module.finrank K U₁ * b ^ Module.finrank K U₂ := by
  have hfr : ∀ U : Submodule K M, U ≤ W →
      Module.finrank K (U.comap W.subtype) = Module.finrank K U := by
    intro U hU
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr hU]
  have hc : IsCompl (U₁.comap W.subtype) (U₂.comap W.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, hdisj, Submodule.comap_bot]
      exact Submodule.ker_subtype W
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      have hx : (x : M) ∈ U₁ ⊔ U₂ := hsup ▸ x.2
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      have : x = ⟨y, hU₁ hy⟩ + ⟨z, hU₂ hz⟩ := Subtype.ext (by simp [hyz])
      rw [this]
      exact Submodule.add_mem_sup hy hz
  rw [s24b_det_of_isCompl (T.restrict hT) _ _ hc a b, hfr _ hU₁, hfr _ hU₂]
  · intro x hx
    exact Subtype.ext (by rw [LinearMap.coe_restrict_apply, Submodule.coe_smul]; exact h1 _ hx)
  · intro x hx
    exact Subtype.ext (by rw [LinearMap.coe_restrict_apply, Submodule.coe_smul]; exact h2 _ hx)

end S24bDet

section S24bHodge11
variable (n : ℕ)

theorem s24b_ev_neg_neg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ξ : ExteriorAlgebra R M) (α β : Module.Dual R M) : s24b_ev ξ (-α) (-β) = s24b_ev ξ α β := by
  simp [s24b_ev, map_neg]

theorem s24b_V10_sup_V01 (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) :
    V10 n I ⊔ V01 n I = ⊤ := by
  have hsq' : ∀ x, complexifyV n I (complexifyV n I x) = -x := fun x => by
    have := congrArg (fun T => T x) (s24b_complexifyV_sq n I hI)
    simpa using this
  rw [eq_top_iff]
  intro x _
  have hy : (2 : ℂ)⁻¹ • (x - Complex.I • complexifyV n I x) ∈ V10 n I := by
    rw [V10, Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hsq']
    linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • complexifyV n I x)
  have hz : (2 : ℂ)⁻¹ • (x + Complex.I • complexifyV n I x) ∈ V01 n I := by
    rw [V01, Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hsq']
    linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • complexifyV n I x)
  have : x = (2 : ℂ)⁻¹ • (x - Complex.I • complexifyV n I x) +
      (2 : ℂ)⁻¹ • (x + Complex.I • complexifyV n I x) := by module
  rw [this]
  exact Submodule.add_mem_sup hy hz

/-- A class of degree `2` on `V_ℂ` fixed by `⋀² I` is of type `(1,1)`. -/
theorem s24b_mem_pq11_of_inv (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (h : ExtV ℂ n) (hh : h ∈ ⋀[ℂ]^2 (V ℂ n))
    (hinv : ExteriorAlgebra.map (complexifyV n I) h = h) :
    h ∈ pqPiece (V10 n I) (V01 n I) 1 1 := by
  set Ic := complexifyV n I
  set A := pqPiece (V10 n I) (V01 n I) 2 0
  set B := pqPiece (V10 n I) (V01 n I) 1 1
  set C := pqPiece (V10 n I) (V01 n I) 0 2
  -- `⋀² V_ℂ = A + B + C`
  have hspan : Submodule.span ℂ ((V10 n I : Set (V ℂ n)) ∪ V01 n I) = ⊤ := by
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq, s24b_V10_sup_V01 n I hI]
  have hle : ⋀[ℂ]^2 (V ℂ n) ≤ A ⊔ B ⊔ C := by
    rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top (R := ℂ) (n := 2) (V ℂ n) hspan,
      Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have h0 : a 0 ∈ (V10 n I : Set (V ℂ n)) ∪ V01 n I := ha ⟨0, rfl⟩
    have h1 : a 1 ∈ (V10 n I : Set (V ℂ n)) ∪ V01 n I := ha ⟨1, rfl⟩
    have hx : ExteriorAlgebra.ιMulti ℂ 2 a = ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ι ℂ (a 1) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [SetLike.mem_coe, hx]
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span
        ⟨![a 0, a 1], Fin.elim0, ?_, fun i => i.elim0, ?_⟩))
      · intro i; fin_cases i <;> assumption
      · simp [ExteriorAlgebra.ιMulti_succ_apply]
    · refine Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span
        ⟨![a 0], ![a 1], ?_, ?_, ?_⟩))
      · intro i; fin_cases i; exact h0
      · intro i; fin_cases i; exact h1
      · simp [ExteriorAlgebra.ιMulti_succ_apply]
    · have hswap : ExteriorAlgebra.ι ℂ (a 0) * ExteriorAlgebra.ι ℂ (a 1) =
          -(ExteriorAlgebra.ι ℂ (a 1) * ExteriorAlgebra.ι ℂ (a 0)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [hswap]
      refine Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.neg_mem _
        (Submodule.subset_span ⟨![a 1], ![a 0], ?_, ?_, ?_⟩)))
      · intro i; fin_cases i; exact h1
      · intro i; fin_cases i; exact h0
      · simp [ExteriorAlgebra.ιMulti_succ_apply]
    · refine Submodule.mem_sup_right (Submodule.subset_span
        ⟨Fin.elim0, ![a 0, a 1], fun i => i.elim0, ?_, ?_⟩)
      · intro i; fin_cases i <;> assumption
      · simp [ExteriorAlgebra.ιMulti_succ_apply]
  -- the action of `⋀² I` on the three pieces
  have hIa : ∀ x ∈ V10 n I, Ic x = Complex.I • x := fun x hx => Module.End.mem_eigenspace_iff.mp hx
  have hIb : ∀ x ∈ V01 n I, Ic x = (-Complex.I) • x := fun x hx => Module.End.mem_eigenspace_iff.mp hx
  have hA : ∀ x ∈ A, ExteriorAlgebra.map Ic x = -x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hy
      simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
        map_mul, ExteriorAlgebra.map_apply_ι, Matrix.vecTail, Function.comp_apply]
      rw [hIa _ (ha 0), hIa _ (ha _), map_smul, map_smul, smul_mul_smul_comm, Complex.I_mul_I,
        neg_one_smul]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, neg_add]
    | smul c y _ hy => rw [map_smul, hy, smul_neg]
  have hB : ∀ x ∈ B, ExteriorAlgebra.map Ic x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hy
      simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
        map_mul, ExteriorAlgebra.map_apply_ι, Matrix.vecTail]
      rw [hIa _ (ha 0), hIb _ (hb 0), map_smul, map_smul, smul_mul_smul_comm,
        show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]
  have hC : ∀ x ∈ C, ExteriorAlgebra.map Ic x = -x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hy
      simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, one_mul,
        mul_one, map_mul, ExteriorAlgebra.map_apply_ι, Matrix.vecTail, Function.comp_apply]
      rw [hIb _ (hb 0), hIb _ (hb _), map_smul, map_smul, smul_mul_smul_comm,
        show -Complex.I * -Complex.I = -1 by rw [neg_mul_neg, Complex.I_mul_I], neg_one_smul]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, neg_add]
    | smul c y _ hy => rw [map_smul, hy, smul_neg]
  obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.mp (hle hh)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, hA a ha, hB b hb, hC c hc] at hinv
  have hac : a + c = 0 := by
    have h2 : (2 : ℂ) • (a + c) = 0 := by
      rw [two_smul]
      have := congrArg (fun x => a + b + c - x) hinv
      simp only [sub_self] at this
      rw [← this]
      abel
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [show a + b + c = b + (a + c) by abel, hac, add_zero]
  exact hb

theorem s24b_bcExt_map (A : Module.End ℝ (V ℝ n)) (x : ExtV ℝ n) :
    bcExt ℝ ℂ n (ExteriorAlgebra.map A x) = ExteriorAlgebra.map (complexifyV n A) (bcExt ℝ ℂ n x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (((ExteriorAlgebra.map (complexifyV n A)).restrictScalars ℝ).commutes r).symm
  | ι v =>
    rw [ExteriorAlgebra.map_apply_ι, s24b_bcExt_ι, s24b_bcExt_ι, ExteriorAlgebra.map_apply_ι,
      s24b_complexifyV_bcV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem s24b_bcExt_bcExt (x : ExtV ℚ n) : bcExt ℝ ℂ n (bcExt ℚ ℝ n x) = bcExt ℚ ℂ n x := by
  apply (basisExt ℂ n).repr.injective
  ext1 K
  rw [s24b_repr_bcExt, s24b_repr_bcExt, s24b_repr_bcExt, ← IsScalarTower.algebraMap_apply]

/-- A rational class of degree `2` whose real extension is fixed by `⋀² I` is of type `(1,1)`. -/
theorem s24b_hodgeV_of_inv (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) (α : ExtV ℚ n)
    (hα : α ∈ ⋀[ℚ]^2 (V ℚ n)) (hinv : ExteriorAlgebra.map I (bcExt ℚ ℝ n α) = bcExt ℚ ℝ n α) :
    α ∈ hodgeClassesV n I 1 := by
  rw [mem_hodgeClassesV_iff]
  refine ⟨hα, ?_⟩
  rw [← s24b_bcExt_bcExt]
  apply s24b_mem_pq11_of_inv n I hI
  · exact s24b_bcExt_mem_exteriorPower (F := ℝ) (F' := ℂ) n
      (s24b_bcExt_mem_exteriorPower (F := ℚ) (F' := ℝ) n hα)
  · rw [← s24b_bcExt_map, hinv]

end S24bHodge11

/-! ## `η(k)` maps `h = Ξ_P^♯` to `Nm(k) h` -/

section S24bEtaH

variable {n : ℕ} {d : ℚ}

/-- `η_k = a + b f` for `k = a + b√-d` (`a = ratPart k`, `b = sqrtNegCoeff k`, `f = η_{√-d}`). -/
theorem s24b_η_eq (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂) (k : Kd d) :
    P.η hW k = Kd.ratPart d k • LinearMap.id + Kd.sqrtNegCoeff d k • P.fη hW := by
  have hk := Kd.eq_ratPart_add_sqrtNegCoeff hd k
  have hq : ∀ q : ℚ, P.ηHom hd hW (algebraMap ℚ (Kd d) q) =
      algebraMap ℚ (Module.End ℚ (V ℚ n)) q := fun q => by
    rw [← RingHom.comp_apply]; congr 1; exact RingHom.ext_rat _ _
  have h := congrArg (P.ηHom hd hW) hk
  rw [map_add, map_mul, hq, hq] at h
  rw [show P.η hW k = P.ηHom hd hW k from rfl, h, Algebra.algebraMap_eq_smul_one,
    ← Algebra.smul_def]
  rfl

/-- (§1.3, TeX lines 447–448, from the condition on the polarization in [van Geemen, Def. 4.9]) If
`Ξ_P(f x, f y) = d Ξ_P(x, y)` (the condition checked in the proof of Corollary 3.2.3), then `η(k)`
maps the class `h = Ξ_P^♯` of `Ξ_P` to `Nm(k) h`, `η(k)` acting on `H²(X × X̂, ℚ) = ⋀² V_ℚ` by
`⋀² η_k`. Proof: the adjoint of `η_k = a + b f` for `(·,·)_V` is `a - b f` (`f` is anti-self-dual),
and `Ξ_P(a x - b f x, a y - b f y) = Nm(k) Ξ_P(x, y)` is [van Geemen, Def. 4.9] for `-f`
(`vanGeemen_def4_9`). -/
theorem s24b_map_η_hClass (P : KSecant n d) (hd : 0 < d) (hW : IsCompl P.W₁ P.W₂)
    (hpol : ∀ x y, P.XiQ hW (P.fη hW x) (P.fη hW y) = d * P.XiQ hW x y) (k : Kd d) :
    ExteriorAlgebra.map (P.η hW k) (P.hClass hW) = (Kd.Nm d k : ℚ) • P.hClass hW := by
  have hh : P.hClass hW ∈ ⋀[ℚ]^2 (V ℚ n) := formToExt2_mem ℚ n _
  set a := Kd.ratPart d k
  set b := Kd.sqrtNegCoeff d k
  -- [van Geemen, Def. 4.9] for `-f`: `(-f)² = -d` and `Ξ_P(-f x, -f y) = d Ξ_P(x, y)`
  have hff : (-P.fη hW) ∘ₗ (-P.fη hW) = -(d • LinearMap.id) := by
    rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, P.fη_comp_fη hW]
  have hvg := vanGeemen_def4_9 hd (P.XiQ hW) (-P.fη hW) hff (fun x y => by
    simp only [LinearMap.neg_apply, map_neg, neg_neg]; exact hpol x y) k
  -- the adjoint of `η_k = a + b f` for `(·,·)_V` is `a - b f`
  have hadj : ∀ x, pairing ℚ n x ∘ₗ P.η hW k = pairing ℚ n (a • x + b • (-P.fη hW) x) := fun x =>
    LinearMap.ext fun z => by
      rw [LinearMap.comp_apply, s24b_η_eq P hd hW k]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.neg_apply, map_add, map_smul, map_neg, smul_eq_mul]
      rw [P.pairing_fη_left hW x z]; ring
  refine s24b_eq_of_ev ℚ n (s24b_map_mem_exteriorPower _ hh) (Submodule.smul_mem _ _ hh)
    fun x y => ?_
  rw [s24b_ev_map, hadj, hadj, s24b_ev_smul, s24b_ev, s24b_ev, P.hClass_spec hW,
    P.hClass_spec hW, hvg x y, smul_eq_mul]

end S24bEtaH

variable (n : ℕ)

/-- `Θ = Σ e_{2i} ∧ e_{2i+1}` has degree `2`. -/
theorem ThetaStd_mem : ThetaStd ℚ n ∈ ⋀[ℚ]^2 (H1 ℚ n) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  show _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℚ : H1 ℚ n →ₗ[ℚ] S ℚ n)) ^ 2
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

/-- `Θ ≠ 0` for `n > 0`. -/
theorem ThetaStd_ne_zero (hn : 0 < n) : ThetaStd ℚ n ≠ 0 := by
  intro h
  have h1 := ThetaStd_pow ℚ n
  rw [h, zero_pow hn.ne'] at h1
  have h2 : pt ℚ n ≠ 0 := (basisS ℚ n).ne_zero _
  exact h2 ((smul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast (Nat.factorial_ne_zero n)))

/-- The contraction `θ` (2.4.3) of `Θ = ThetaStd` is `thetaStd`. -/
theorem thetaMap_ThetaStd : thetaMap n (ThetaStd ℚ n) = thetaStd n := by
  ext1 y
  rw [thetaMap, ThetaStd, s24b_contractOne_sum, LinearMap.sum_apply, s24b_thetaStd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s24b_contractOne_ι_mul_ι]

/-- `θ` of `ThetaStd` is an isomorphism, with inverse `thetaStdInv`. -/
theorem thetaStd_bijective : Function.Bijective (thetaMap n (ThetaStd ℚ n)) := by
  rw [thetaMap_ThetaStd]
  refine ⟨fun y y' h => ?_, fun w => ⟨thetaStdInv n w, ?_⟩⟩
  · have h1 := LinearMap.congr_fun (s24b_thetaStdInv_comp_thetaStd n) y
    have h2 := LinearMap.congr_fun (s24b_thetaStdInv_comp_thetaStd n) y'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, h]
  · exact LinearMap.congr_fun (s24b_thetaStd_comp_thetaStdInv n) w

theorem thetaStdInv_comp_thetaStd : thetaStdInv n ∘ₗ thetaStd n = LinearMap.id :=
  s24b_thetaStdInv_comp_thetaStd n

theorem thetaStd_comp_thetaStdInv : thetaStd n ∘ₗ thetaStdInv n = LinearMap.id :=
  s24b_thetaStd_comp_thetaStdInv n

variable (d : ℚ) (hd : 0 < d) (hn : 0 < n)

/-- The oriented `K`-secant `P_Θ` (§2.4) of the standard principal polarization `Θ = ThetaStd`. -/
noncomputable abbrev PStd : KSecant n d :=
  PTheta n d hd (ThetaStd ℚ n) (ThetaStd_mem n) (ThetaStd_ne_zero n hn)

/-- `V_K = W₁ ⊕ W₂` for `P_Θ`. -/
theorem PStd_isCompl : IsCompl (PStd n d hd hn).W₁ (PStd n d hd hn).W₂ :=
  PTheta_isCompl n d hd _ _ _ (thetaStd_bijective n)

/-- `f = η(√-d)` of `P_Θ` is `fV`: `f(y, w) = (-θ⁻¹(w), d θ(y))`. -/
theorem fη_PStd : (PStd n d hd hn).fη (PStd_isCompl n d hd hn) = fV n d := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨y, w⟩ := v
  have h1 := PTheta_fη_inl n d hd (ThetaStd ℚ n) (ThetaStd_mem n) (ThetaStd_ne_zero n hn)
    (thetaStd_bijective n) y
  have h2 := PTheta_fη_inr n d hd (ThetaStd ℚ n) (ThetaStd_mem n) (ThetaStd_ne_zero n hn)
    (thetaStd_bijective n) (thetaStdInv n w)
  rw [thetaMap_ThetaStd] at h1 h2
  have hw : thetaStd n (thetaStdInv n w) = w :=
    LinearMap.congr_fun (s24b_thetaStd_comp_thetaStdInv n) w
  rw [hw] at h2
  have hyw : ((y, w) : V ℚ n) = (y, 0) + (0, w) := by simp
  rw [hyw, map_add, h1, h2]
  simp [fV]

/-- The action `η : K → End(V_ℚ)` (2.2.4) of `P_Θ` is `etaV`. -/
theorem ηHom_PStd : (PStd n d hd hn).ηHom hd (PStd_isCompl n d hd hn) = etaV n d hd := by
  refine RingHom.ext fun k => ?_
  have h1 : (PStd n d hd hn).ηHom hd (PStd_isCompl n d hd hn) (Kd.sqrtNeg d) = fV n d :=
    fη_PStd n d hd hn
  have h2 : etaV n d hd (Kd.sqrtNeg d) = fV n d := by
    show Kd.ratPart d (Kd.sqrtNeg d) • (1 : Module.End ℚ (V ℚ n)) +
      Kd.sqrtNegCoeff d (Kd.sqrtNeg d) • fV n d = fV n d
    rw [s24b_ratPart_sqrtNeg, s24b_sqrtNegCoeff_sqrtNeg hd, zero_smul, one_smul, zero_add]
  rw [Kd.eq_ratPart_add_sqrtNegCoeff hd k, map_add, map_add, map_mul, map_mul,
    RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap,
    RingHom.map_rat_algebraMap, h1, h2]

theorem s24b_XiQ_PStd (v w : V ℚ n) :
    (PStd n d hd hn).XiQ (PStd_isCompl n d hd hn) v w = pairing ℚ n (fV n d v) w := by
  rw [KSecant.XiQ, LinearMap.BilinForm.compLeft_apply, fη_PStd]

theorem s24b_hClass_PStd : (PStd n d hd hn).hClass (PStd_isCompl n d hd hn) = hV n d := by
  rw [KSecant.hClass, s24b_formToExt2_eq]
  · have hF : ∀ i, ∑ j, (PStd n d hd hn).XiQ (PStd_isCompl n d hd hn) (vecF ℚ n i) (vecF ℚ n j) •
        vecE ℚ n j = ((0 : Module.Dual ℚ (H1 ℚ n)), d • thetaStd n (f ℚ n i)) := by
      intro i
      simp only [s24b_XiQ_PStd, s24b_pairing_apply, vecF, vecE, fV, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.comp_apply, LinearMap.fst_apply, map_zero, zero_add]
      exact s24b_sum_smul_inr n _
    have hE : ∀ i, ∑ j, (PStd n d hd hn).XiQ (PStd_isCompl n d hd hn) (vecE ℚ n i) (vecE ℚ n j) •
        vecF ℚ n j = (-(thetaStdInv n (e ℚ n i)), (0 : H1 ℚ n)) := by
      intro i
      simp only [s24b_XiQ_PStd, s24b_pairing_apply, vecF, vecE, fV, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        map_zero, add_zero]
      exact s24b_sum_smul_inl n _
    simp only [hF, hE]
    rw [s24b_sum_fin_two_mul n, s24b_sum_fin_two_mul n]
    simp only [vecE, vecF, s24b_thetaStd_f_even, s24b_thetaStd_f_odd, s24b_thetaStdInv_e_even,
      s24b_thetaStdInv_e_odd, neg_neg]
    have hA : ∀ a b : H1 ℚ n,
        ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), a) *
            ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), d • b) +
          ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), b) *
            ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), d • -a) =
        (2 * d) • (ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), a) *
          ExteriorAlgebra.ι ℚ ((0 : Module.Dual ℚ (H1 ℚ n)), b)) := by
      intro a b
      have h1 : (((0 : Module.Dual ℚ (H1 ℚ n)), d • b) : V ℚ n) = d • ((0, b) : V ℚ n) := by
        simp
      have h2 : (((0 : Module.Dual ℚ (H1 ℚ n)), d • -a) : V ℚ n) = (-d) • ((0, a) : V ℚ n) := by
        simp
      rw [h1, h2, map_smul, map_smul, mul_smul_comm, mul_smul_comm, s24b_ι_anticomm n (0, a) (0, b)]
      module
    have hB : ∀ a b : Module.Dual ℚ (H1 ℚ n),
        ExteriorAlgebra.ι ℚ ((a, (0 : H1 ℚ n)) : V ℚ n) * ExteriorAlgebra.ι ℚ ((b, (0 : H1 ℚ n)) : V ℚ n) +
          ExteriorAlgebra.ι ℚ ((b, (0 : H1 ℚ n)) : V ℚ n) *
            ExteriorAlgebra.ι ℚ ((-a, (0 : H1 ℚ n)) : V ℚ n) =
        (2 : ℚ) • (ExteriorAlgebra.ι ℚ ((a, (0 : H1 ℚ n)) : V ℚ n) *
          ExteriorAlgebra.ι ℚ ((b, (0 : H1 ℚ n)) : V ℚ n)) := by
      intro a b
      have h2 : ((-a, (0 : H1 ℚ n)) : V ℚ n) = -((a, 0) : V ℚ n) := by simp
      rw [h2, map_neg, mul_neg, s24b_ι_anticomm n (a, 0) (b, 0), neg_neg]
      module
    simp only [hA, hB, Finset.smul_sum, smul_smul]
    rw [hV, ThetaV, ThetaHatV, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      field_simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [inv_mul_cancel₀ two_ne_zero, one_smul]
  · intro i j
    simp [s24b_XiQ_PStd, vecF, vecE, fV]

/-- `h = d Θ + Θ̂` is the class of `Ξ_P` (2.4.2) of `P_Θ`: for `x, y ∈ V_ℚ`,
`⟪h, (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(x, y)`, where `⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` (degree-`0` part) as in
`WeilClasses.eval2`. -/
theorem hV_eq_XiQ (x y : V ℚ n) :
    ExteriorAlgebra.algebraMapInv
        (contractLeft (Q := 0) (pairing ℚ n y) (contractLeft (Q := 0) (pairing ℚ n x) (hV n d))) =
      (PStd n d hd hn).XiQ (PStd_isCompl n d hd hn) x y := by
  rw [← s24b_hClass_PStd n d hd hn]
  exact (PStd n d hd hn).hClass_spec (PStd_isCompl n d hd hn) x y

/-- `h = d Θ + Θ̂` is the class `Ξ_P^♯` of `WeilClasses.Secant.Defs` (`KSecant.hClass`). -/
theorem hClass_PStd : (PStd n d hd hn).hClass (PStd_isCompl n d hd hn) = hV n d :=
  s24b_hClass_PStd n d hd hn

/-- `P_Θ` of §8 (`PJac`, for an ample `Θ = ThetaStd` on a threefold) is `PStd`. -/
theorem PJac_eq_PStd {J : Module.End ℝ (H1 ℝ 3)} (hΘ : IsAmple 3 J (ThetaStd ℚ 3)) (hd : 0 < d) :
    PJac d hΘ hd = PStd 3 d hd (by norm_num) :=
  rfl

/-- The standard complex structure of `X × X̂` (`H^{1,0}` the `i`-eigenspace) is the negative of the
paper's `I_{V_ℝ}` (footnote in §2.4). -/
theorem stdStructure_eq_neg (J : Module.End ℝ (H1 ℝ n)) :
    stdStructure n J = -productStructure n J := by
  ext v <;> simp [stdStructure, productStructure]

/-! ## Transport of the Weil-type structure to the model -/

/-! ### Helpers for `weilDomain_eq_image_OmegaP` -/

theorem s24b_fR_PStd :
    (PStd n d hd hn).fR (PStd_isCompl n d hd hn) = bcEndV ℝ n (fV n d) := by
  rw [KSecant.fR, fη_PStd]

theorem s24b_fR_bcV (v : V ℚ n) :
    (PStd n d hd hn).fR (PStd_isCompl n d hd hn) (bcV ℚ ℝ n v) = bcV ℚ ℝ n (fV n d v) := by
  rw [s24b_fR_PStd, s24b_bcEndV_bcV]

theorem s24b_fR_fR (x : V ℝ n) :
    (PStd n d hd hn).fR (PStd_isCompl n d hd hn) ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) =
      -((d : ℝ) • x) := by
  have h : bcEndV ℝ n (fV n d ∘ₗ fV n d) = bcEndV ℝ n (-(d • LinearMap.id)) := by
    congr 1
    exact fV_mul_self n d
  rw [s24b_bcEndV_comp, s24b_bcEndV_neg, s24b_bcEndV_smul_one] at h
  have := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at this
  rw [s24b_fR_PStd, this]
  rfl

theorem s24b_pairing_fR_left (x y : V ℝ n) :
    pairing ℝ n ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) y =
      -pairing ℝ n x ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) y) := by
  set fR := (PStd n d hd hn).fR (PStd_isCompl n d hd hn)
  have h : (pairing ℝ n).compl₁₂ fR LinearMap.id = -((pairing ℝ n).compl₁₂ LinearMap.id fR) := by
    refine LinearMap.ext_basis (basisV ℝ n) (basisV ℝ n) fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.neg_apply]
    rw [← s24b_bcV_basisV ℚ ℝ n i, ← s24b_bcV_basisV ℚ ℝ n j, s24b_fR_bcV, s24b_fR_bcV,
      s24b_pairing_bcV, s24b_pairing_bcV, ← map_neg, ← fη_PStd n d hd hn,
      KSecant.pairing_fη_left]
  have := LinearMap.congr_fun₂ h x y
  simpa using this

theorem s24b_hV_mem : hV n d ∈ ⋀[ℚ]^2 (V ℚ n) := by
  have hι : ∀ a b : V ℚ n, ExteriorAlgebra.ι ℚ a * ExteriorAlgebra.ι ℚ b ∈ ⋀[ℚ]^2 (V ℚ n) := by
    intro a b
    show _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℚ : V ℚ n →ₗ[ℚ] ExtV ℚ n)) ^ 2
    rw [pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  exact add_mem (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hι _ _))
    (Submodule.sum_mem _ fun i _ => hι _ _)

theorem s24b_ev_hV_real (x y : V ℝ n) :
    s24b_ev (bcExt ℚ ℝ n (hV n d)) (pairing ℝ n x) (pairing ℝ n y) =
      (PStd n d hd hn).XiR (PStd_isCompl n d hd hn) x y := by
  have h : s24b_evForm ℝ n (bcExt ℚ ℝ n (hV n d)) = (PStd n d hd hn).XiR (PStd_isCompl n d hd hn) := by
    refine LinearMap.ext_basis (basisV ℝ n) (basisV ℝ n) fun i j => ?_
    rw [← s24b_bcV_basisV ℚ ℝ n i, ← s24b_bcV_basisV ℚ ℝ n j, s24b_evForm_apply,
      s24b_ev_bcExt ℚ ℝ n _ (pairing ℚ n (basisV ℚ n i)) (pairing ℚ n (basisV ℚ n j)) _ _
        (fun v => s24b_pairing_bcV ℚ ℝ n _ v) (fun v => s24b_pairing_bcV ℚ ℝ n _ v),
      KSecant.XiR_bcV]
    exact (congrArg (algebraMap ℚ ℝ) (hV_eq_XiQ n d hd hn _ _)).trans (eq_ratCast _ _)
  exact LinearMap.congr_fun₂ h x y

/-- Positivity: `⟪h, a ∧ a ∘ J'⟫ = g_I(x, x)` for `J' = -I` transported and `a = (x, ·)_V`. -/
theorem s24b_eval2_hX (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y) (x : V ℝ n) :
    eval2 ℝ (2 * n) (bcS ℚ ℝ (2 * n) (hX n d)) (pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap)
        ((pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap) ∘ₗ transportEnd n (-I)) =
      (PStd n d hd hn).gI (PStd_isCompl n d hd hn) I x x := by
  rw [hX, s24b_bcS_map_coordV, s24b_eval2_map]
  have h1 : (pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap) ∘ₗ (coordV ℝ n).toLinearMap =
      pairing ℝ n x := by
    refine LinearMap.ext fun v => ?_
    simp
  have h2 : ((pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap) ∘ₗ transportEnd n (-I)) ∘ₗ
      (coordV ℝ n).toLinearMap = pairing ℝ n (I x) := by
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun (s24b_pairing_comp_I n I hI hIso x) v
    simp only [LinearMap.comp_apply] at this
    simp [transportEnd, this]
  rw [h1, h2, s24b_ev_hV_real n d hd hn]
  rfl

/-- Transport of the Hodge type: if `Ξ_P` is of type `(1,1)` for `I`, `Ξ_P(I x, I y) = Ξ_P(x, y)`
(Corollary 3.2.3, `corollary3_2_3_type11`), then `h = d Θ + Θ̂`, the class of `Ξ_P`
(`hV_eq_XiQ`, `hClass_PStd`), is a Hodge class of degree `2` for `I`. -/
theorem s24b_hV_hodge (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y)
    (h11 : ∀ x y, (PStd n d hd hn).XiR (PStd_isCompl n d hd hn) (I x) (I y) =
      (PStd n d hd hn).XiR (PStd_isCompl n d hd hn) x y) :
    hV n d ∈ hodgeClassesV n I 1 := by
  apply s24b_hodgeV_of_inv n I hI _ (s24b_hV_mem n d)
  have hmem := s24b_bcExt_mem_exteriorPower (F := ℚ) (F' := ℝ) n (s24b_hV_mem n d)
  refine s24b_eq_of_ev ℝ n (s24b_map_mem_exteriorPower I hmem) hmem fun x y => ?_
  -- `⟪⋀² I (h), (x, ·)_V ∧ (y, ·)_V⟫ = Ξ_P(-I x, -I y) = Ξ_P(I x, I y)` (the adjoint of `I` is `-I`)
  rw [s24b_ev_map, s24b_pairing_comp_I n I hI hIso, s24b_pairing_comp_I n I hI hIso,
    s24b_ev_hV_real n d hd hn, s24b_ev_hV_real n d hd hn]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact h11 x y

theorem s24b_XiR_apply (x y : V ℝ n) :
    (PStd n d hd hn).XiR (PStd_isCompl n d hd hn) x y =
      pairing ℝ n ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) y := rfl

theorem s24b_isometry_of_ev (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hc : ∀ x, I ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) =
      (PStd n d hd hn).fR (PStd_isCompl n d hd hn) (I x))
    (hev : ∀ α β : Module.Dual ℝ (V ℝ n), s24b_ev (bcExt ℚ ℝ n (hV n d)) (α ∘ₗ I) (β ∘ₗ I) =
      s24b_ev (bcExt ℚ ℝ n (hV n d)) α β) :
    ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
  set fR := (PStd n d hd hn).fR (PStd_isCompl n d hd hn) with hfR
  choose adj hadj using fun x => s24b_pairing_surjective ℝ n (pairing ℝ n x ∘ₗ I)
  have ha : ∀ x y, pairing ℝ n (adj x) y = pairing ℝ n x (I y) := fun x y => by
    rw [hadj]; rfl
  have hb : ∀ x y, pairing ℝ n (fR (adj x)) (adj y) = pairing ℝ n (fR x) y := by
    intro x y
    rw [← s24b_XiR_apply n d hd hn, ← s24b_XiR_apply n d hd hn, ← s24b_ev_hV_real n d hd hn,
      ← s24b_ev_hV_real n d hd hn, hadj, hadj, hev]
  have hfadj : ∀ x, adj (fR x) = fR (adj x) := by
    intro x
    apply s24b_pairing_injective ℝ n
    refine LinearMap.ext fun w => ?_
    rw [ha, s24b_pairing_fR_left n d hd hn, ← hc, ← ha, ← s24b_pairing_fR_left n d hd hn]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h2 : ∀ z y, pairing ℝ n (adj z) (adj y) = pairing ℝ n z y := by
    intro z y
    have hx : fR ((-(d : ℝ)⁻¹) • fR z) = z := by
      rw [map_smul, s24b_fR_fR n d hd hn, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ hd', one_smul]
    have := hb ((-(d : ℝ)⁻¹) • fR z) y
    rwa [← hfadj, hx] at this
  have h3 : ∀ y, I (adj y) = y := by
    intro y
    have : I (adj y) - y = 0 := by
      apply s24b_pairing_nondeg ℝ n
      intro z
      rw [s24b_pairing_symm, map_sub, ← ha, h2, sub_self]
    exact sub_eq_zero.mp this
  have h4 : ∀ y, adj y = -(I y) := by
    intro y
    have := congrArg I (h3 y)
    rw [← Module.End.mul_apply, hI] at this
    simp only [LinearMap.neg_apply, Module.End.one_apply] at this
    rw [← this, neg_neg]
  intro x y
  rw [← ha, h4, ← Module.End.mul_apply, hI]
  simp

theorem s24b_ev_inv_of_hodgeX (I : Module.End ℝ (V ℝ n))
    (hcs' : IsComplexStructure (transportEnd n (-I)))
    (h11 : hX n d ∈ hodgeClassesX (2 * n) (transportEnd n (-I)) 1) :
    ∀ α β : Module.Dual ℝ (V ℝ n), s24b_ev (bcExt ℚ ℝ n (hV n d)) (α ∘ₗ I) (β ∘ₗ I) =
      s24b_ev (bcExt ℚ ℝ n (hV n d)) α β := by
  set J' := transportEnd n (-I) with hJ'
  set ξ := bcS ℚ ℝ (2 * n) (hX n d) with hξ
  have hξ2 : ξ ∈ ⋀[ℝ]^2 (H1 ℝ (2 * n)) :=
    s24b_bcS_mem_exteriorPower ℚ ℝ (2 * n) (Submodule.mem_inf.mp h11).1
  have hθ := thetaExt_comp_neg_dualMap (2 * n) J' hcs' (hX n d) h11
  have hJJ : ∀ w, J' (J' w) = -w := fun w => by
    have := congrArg (fun T => T w) hcs'; simpa using this
  have hinvX : ∀ a b, eval2 ℝ (2 * n) ξ (a ∘ₗ J') (b ∘ₗ J') = eval2 ℝ (2 * n) ξ a b := by
    intro a b
    rw [s24b_eval2_eq ℝ (2 * n) ξ hξ2, s24b_eval2_eq ℝ (2 * n) ξ hξ2]
    have h1 := LinearMap.congr_fun hθ a
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.dualMap_apply', map_neg,
      thetaExt] at h1
    rw [LinearMap.comp_apply, show contractOne ℝ (2 * n) ξ (a ∘ₗ J') =
      -(J' (contractOne ℝ (2 * n) ξ a)) by rw [← h1, neg_neg], map_neg, hJJ, neg_neg]
  intro α β
  have := hinvX (α ∘ₗ (coordV ℝ n).symm.toLinearMap) (β ∘ₗ (coordV ℝ n).symm.toLinearMap)
  rw [hξ, hX, s24b_bcS_map_coordV, s24b_eval2_map, s24b_eval2_map] at this
  have e1 : ∀ γ : Module.Dual ℝ (V ℝ n), ((γ ∘ₗ (coordV ℝ n).symm.toLinearMap) ∘ₗ J') ∘ₗ
      (coordV ℝ n).toLinearMap = -(γ ∘ₗ I) := by
    intro γ
    refine LinearMap.ext fun v => ?_
    simp [hJ', transportEnd]
  have e2 : ∀ γ : Module.Dual ℝ (V ℝ n),
      (γ ∘ₗ (coordV ℝ n).symm.toLinearMap) ∘ₗ (coordV ℝ n).toLinearMap = γ := by
    intro γ
    refine LinearMap.ext fun v => ?_
    simp
  rw [e1, e1, e2, e2, s24b_ev_neg_neg] at this
  exact this

theorem s24b_fC_W₁ (w : V (Kd d) n) (hw : w ∈ (PStd n d hd hn).W₁) :
    bcEndV ℂ n (fV n d) (bcV (Kd d) ℂ n w) = sqrtNeg d • bcV (Kd d) ℂ n w := by
  rw [s24b_bcEndV_tower, ← fη_PStd n d hd hn, KSecant.fη, s24b_bcEndV_η n d hd]
  have := s24b_ηK_add n d (PStd n d hd hn) (PStd_isCompl n d hd hn) (Kd.sqrtNeg d) hw
    (Submodule.zero_mem _)
  rw [add_zero, smul_zero, add_zero] at this
  rw [this, map_smul, ← algebraMap_smul ℂ (Kd.sqrtNeg d)]
  rfl

theorem s24b_fC_W₂ (w : V (Kd d) n) (hw : w ∈ (PStd n d hd hn).W₂) :
    bcEndV ℂ n (fV n d) (bcV (Kd d) ℂ n w) = (-sqrtNeg d) • bcV (Kd d) ℂ n w := by
  rw [s24b_bcEndV_tower, ← fη_PStd n d hd hn, KSecant.fη, s24b_bcEndV_η n d hd]
  have := s24b_ηK_add n d (PStd n d hd hn) (PStd_isCompl n d hd hn) (Kd.sqrtNeg d)
    (Submodule.zero_mem _) hw
  rw [zero_add, smul_zero, zero_add, s24b_σ_sqrtNeg] at this
  rw [this, map_smul, ← algebraMap_smul ℂ (-Kd.sqrtNeg d)]
  rfl

theorem s24b_W₁ℂ_le : (PStd n d hd hn).W₁ℂ ≤
    Module.End.eigenspace (bcEndV ℂ n (fV n d)) (sqrtNeg d) := by
  rw [KSecant.W₁ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (s24b_fC_W₁ n d hd hn w hw)

theorem s24b_W₂ℂ_le : (PStd n d hd hn).W₂ℂ ≤
    Module.End.eigenspace (bcEndV ℂ n (fV n d)) (-sqrtNeg d) := by
  rw [KSecant.W₂ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (s24b_fC_W₂ n d hd hn w hw)

theorem s24b_W₁ℂ_sup_W₂ℂ : (PStd n d hd hn).W₁ℂ ⊔ (PStd n d hd hn).W₂ℂ = ⊤ := by
  rw [eq_top_iff, ← (basisV ℂ n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [← s24b_bcV_basisV (Kd d) ℂ n k]
  obtain ⟨w₁, hw₁, w₂, hw₂, h⟩ := Submodule.mem_sup.mp
    ((PStd_isCompl n d hd hn).codisjoint.eq_top ▸ Submodule.mem_top :
      basisV (Kd d) n k ∈ (PStd n d hd hn).W₁ ⊔ (PStd n d hd hn).W₂)
  rw [← h, map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨w₁, hw₁, rfl⟩)
    (Submodule.subset_span ⟨w₂, hw₂, rfl⟩)

theorem s24b_eigenspace_fC :
    Module.End.eigenspace (bcEndV ℂ n (fV n d)) (sqrtNeg d) = (PStd n d hd hn).W₁ℂ ∧
      Module.End.eigenspace (bcEndV ℂ n (fV n d)) (-sqrtNeg d) = (PStd n d hd hn).W₂ℂ := by
  have hs : sqrtNeg d ≠ 0 := by
    have := s24b_sqrtNeg_ne_zero hd
    intro h; apply this; exact Subtype.ext h
  have h2s : (2 : ℂ) * sqrtNeg d ≠ 0 := mul_ne_zero two_ne_zero hs
  have hdec : ∀ v : V ℂ n, ∃ w₁ ∈ (PStd n d hd hn).W₁ℂ, ∃ w₂ ∈ (PStd n d hd hn).W₂ℂ,
      w₁ + w₂ = v := fun v => Submodule.mem_sup.mp
        ((s24b_W₁ℂ_sup_W₂ℂ n d hd hn) ▸ Submodule.mem_top)
  constructor
  · refine le_antisymm ?_ (s24b_W₁ℂ_le n d hd hn)
    intro v hv
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec v
    rw [Module.End.mem_eigenspace_iff, map_add,
      Module.End.mem_eigenspace_iff.mp (s24b_W₁ℂ_le n d hd hn hw₁),
      Module.End.mem_eigenspace_iff.mp (s24b_W₂ℂ_le n d hd hn hw₂)] at hv
    have h' : ((2 : ℂ) * sqrtNeg d) • w₂ = 0 := by
      have := congrArg (fun x => sqrtNeg d • (w₁ + w₂) - x) hv
      simp only [sub_self] at this
      rw [← this]
      module
    rw [(smul_eq_zero.mp h').resolve_left h2s, add_zero]
    exact hw₁
  · refine le_antisymm ?_ (s24b_W₂ℂ_le n d hd hn)
    intro v hv
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdec v
    rw [Module.End.mem_eigenspace_iff, map_add,
      Module.End.mem_eigenspace_iff.mp (s24b_W₁ℂ_le n d hd hn hw₁),
      Module.End.mem_eigenspace_iff.mp (s24b_W₂ℂ_le n d hd hn hw₂)] at hv
    have h' : ((2 : ℂ) * sqrtNeg d) • w₁ = 0 := by
      have := congrArg (fun x => x - (-sqrtNeg d) • (w₁ + w₂)) hv
      simp only [sub_self] at this
      rw [← this]
      module
    rw [(smul_eq_zero.mp h').resolve_left h2s, zero_add]
    exact hw₂

theorem s24b_W₂ℂ_le_graph : (PStd n d hd hn).W₂ℂ ≤ LinearMap.range (LinearMap.prod LinearMap.id
      (sqrtNeg d • contractOne ℂ n (bcS ℚ ℂ n (ThetaStd ℚ n)))) := by
  rw [KSecant.W₂ℂ, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, (equation2_4_6_W₂ n d hd _ (ThetaStd_mem n) (ThetaStd_ne_zero n hn)).2] at hw
  obtain ⟨y, rfl⟩ := hw
  refine ⟨bcDual (Kd d) ℂ n y, ?_⟩
  simp only [LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply, LinearMap.smul_apply,
    bcV, LinearMap.prodMap_apply]
  congr 1
  rw [map_smul, ← s24b_contractOne_bcS, s24b_bcS_bcS, ← algebraMap_smul ℂ (Kd.sqrtNeg d)]
  rfl

theorem s24b_finrank_Wℂ :
    Module.finrank ℂ (PStd n d hd hn).W₁ℂ = 2 * n ∧
      Module.finrank ℂ (PStd n d hd hn).W₂ℂ = 2 * n := by
  have h1 : Module.finrank ℂ (PStd n d hd hn).W₁ℂ ≤ 2 * n :=
    (Submodule.finrank_mono
      (s24b_PTheta_W₁ℂ n d hd _ (ThetaStd_mem n) (ThetaStd_ne_zero n hn))).trans
      (s24b_finrank_graph n _).le
  have h2 : Module.finrank ℂ (PStd n d hd hn).W₂ℂ ≤ 2 * n :=
    (Submodule.finrank_mono (s24b_W₂ℂ_le_graph n d hd hn)).trans (s24b_finrank_graph n _).le
  have hdisj : (PStd n d hd hn).W₁ℂ ⊓ (PStd n d hd hn).W₂ℂ = ⊥ := by
    rw [← (s24b_eigenspace_fC n d hd hn).1, ← (s24b_eigenspace_fC n d hd hn).2]
    have hs : sqrtNeg d ≠ -sqrtNeg d := by
      intro h
      have h2 : (2 : ℂ) * sqrtNeg d = 0 := by linear_combination h
      have hs0 : sqrtNeg d ≠ 0 := fun h0 => s24b_sqrtNeg_ne_zero hd (Subtype.ext h0)
      exact (mul_ne_zero two_ne_zero hs0) h2
    exact ((Module.End.eigenspaces_iSupIndep (bcEndV ℂ n (fV n d))).pairwiseDisjoint hs).eq_bot
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (PStd n d hd hn).W₁ℂ (PStd n d hd hn).W₂ℂ
  rw [s24b_W₁ℂ_sup_W₂ℂ n d hd hn, hdisj, finrank_top, finrank_bot, Module.finrank_prod,
    Subspace.dual_finrank_eq] at h3
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_zero] at h3
  omega

theorem s24b_eigenspace_fX :
    Module.End.eigenspace (bcMap ℚ ℂ (fX n d)) (sqrtNeg d) =
        (PStd n d hd hn).W₁ℂ.map (coordV ℂ n).toLinearMap ∧
      Module.End.eigenspace (bcMap ℚ ℂ (fX n d)) (-sqrtNeg d) =
        (PStd n d hd hn).W₂ℂ.map (coordV ℂ n).toLinearMap := by
  rw [fX, s24b_bcMap_transportEnd, transportEnd, s24b_eigenspace_conj, s24b_eigenspace_conj,
    (s24b_eigenspace_fC n d hd hn).1, (s24b_eigenspace_fC n d hd hn).2]
  exact ⟨rfl, rfl⟩

/-- `P_Θ` satisfies Assumption 2.4.1 for the complex structure `J₀` of `X` (`s8_J0`), for which
`Θ = ThetaStd` is ample: the setting in which §§3–4 are stated. -/
theorem s24b_assumption_J0 : Assumption2_4_1 (PStd n d hd hn) (s8_J0 n) :=
  PTheta_assumption2_4_1 n d hd hn (s8_J0 n) (s8_J0_isComplex n) (ThetaStd ℚ n) (s8_ample_J0 n)

theorem s24b_comm_of_mem_OmegaP (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ (PStd n d hd hn).OmegaP (PStd_isCompl n d hd hn)) :
    I * (PStd n d hd hn).fR (PStd_isCompl n d hd hn) =
      (PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I := by
  obtain ⟨⟨g, hg, hgI⟩, -⟩ := hI
  rw [← hgI]
  exact LinearMap.ext fun x => hg.2.1 x

/-- A point `I` of `Ω_P` satisfies the hypotheses of Lemma 3.2.1 and Corollary 3.2.3 (§3.2):
`I = ρ(Ĩ)` for some `Ĩ ∈ Spin(V_ℝ)_P` (Lemma 3.1.1 over `ℝ`), `I` is a complex structure,
`ν(I) = 2n` and `g_I` is positive definite. -/
theorem s24b_cor3_2_3_hyps (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ (PStd n d hd hn).OmegaP (PStd_isCompl n d hd hn)) :
    (∃ g ∈ (PStd n d hd hn).spinPR, (rho ℝ n g : V ℝ n →ₗ[ℝ] V ℝ n) = I) ∧
      IsComplexStructure I ∧ (PStd n d hd hn).nu (s24b_assumption_J0 n d hd hn).isCompl I = 2 * n ∧
      ∀ x : V ℝ n, x ≠ 0 → 0 < (PStd n d hd hn).gI (s24b_assumption_J0 n d hd hn).isCompl I x x := by
  have hP := s24b_assumption_J0 n d hd hn
  have hc := s24b_comm_of_mem_OmegaP n d hd hn I hI
  obtain ⟨⟨g, hg, hgI⟩, hcs, hEp, -, hpos⟩ := hI
  refine ⟨?_, hcs, ?_, hpos⟩
  · have h := (lemma3_1_1_real (PStd n d hd hn) (s8_J0 n) hP).2
    have hg' : g ∈ rho ℝ n '' ((PStd n d hd hn).spinPR : Set (Spin ℝ n)) := by
      rw [h]; exact hg
    obtain ⟨g', hg'1, hg'2⟩ := hg'
    exact ⟨g', hg'1, by rw [hg'2]; exact hgI⟩
  · rw [KSecant.nu]
    rw [show I * (PStd n d hd hn).fR hP.isCompl = (PStd n d hd hn).fR hP.isCompl * I from hc]
    exact hEp

/-- The Weil condition at a point `I` of `Ω_P`, for the standard complex structure `-I` (whose
`H^{1,0}` is `V^{0,1}` of `I`): Lemma 3.2.1. -/
theorem s24b_weil_of_mem_OmegaP (I : Module.End ℝ (V ℝ n))
    (hI : I ∈ (PStd n d hd hn).OmegaP (PStd_isCompl n d hd hn)) :
    Module.finrank ℂ ↥((PStd n d hd hn).W₁ℂ ⊓ V01 n I) = n ∧
      Module.finrank ℂ ↥((PStd n d hd hn).W₂ℂ ⊓ V01 n I) = n := by
  obtain ⟨hIP, hcs, hν, -⟩ := s24b_cor3_2_3_hyps n d hd hn I hI
  obtain ⟨-, -, h3, h4⟩ :=
    lemma3_2_1 (PStd n d hd hn) (s8_J0 n) (s24b_assumption_J0 n d hd hn) I hIP hcs hν
  rw [inf_comm] at h3 h4
  exact ⟨h3, h4⟩

theorem s24b_det_W (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I)
    (hc : I * (PStd n d hd hn).fR (PStd_isCompl n d hd hn) =
      (PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I)
    (W : Submodule ℂ (V ℂ n)) (μ : ℂ)
    (hW : W = Module.End.eigenspace (bcEndV ℂ n (fV n d)) μ) (m : ℕ)
    (hWdim : Module.finrank ℂ W = 2 * m) (h01 : Module.finrank ℂ ↥(W ⊓ V01 n I) = m) :
    ∃ h : ∀ x ∈ W, complexifyV n I x ∈ W, LinearMap.det ((complexifyV n I).restrict h) = 1 := by
  set Ic := complexifyV n I
  set Fc := bcEndV ℂ n (fV n d)
  have hFc : complexifyV n ((PStd n d hd hn).fR (PStd_isCompl n d hd hn)) = Fc := by
    rw [s24b_fR_PStd, s24b_complexifyV_bcEndV]
  have hcC : Ic * Fc = Fc * Ic := by
    rw [← hFc, ← s24b_complexifyV_mul, ← s24b_complexifyV_mul, hc]
  have hmaps : ∀ x ∈ W, Ic x ∈ W := by
    intro x hx
    rw [hW, Module.End.mem_eigenspace_iff] at hx ⊢
    have := congrArg (fun T => T x) hcC
    simp only [Module.End.mul_apply] at this
    rw [← this, hx, map_smul]
  have hsq := s24b_complexifyV_sq n I hI
  have hsq' : ∀ x, Ic (Ic x) = -x := fun x => by
    have := congrArg (fun T => T x) hsq
    simpa using this
  have hsplit : W ⊓ V10 n I ⊔ W ⊓ V01 n I = W := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    have hy : (2 : ℂ)⁻¹ • (x - Complex.I • Ic x) ∈ W ⊓ V10 n I := by
      refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.sub_mem hx (W.smul_mem _ (hmaps x hx))), ?_⟩
      rw [V10, Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hsq']
      linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • Ic x)
    have hz : (2 : ℂ)⁻¹ • (x + Complex.I • Ic x) ∈ W ⊓ V01 n I := by
      refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.add_mem hx (W.smul_mem _ (hmaps x hx))), ?_⟩
      rw [V01, Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hsq']
      linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • Ic x)
    have : x = (2 : ℂ)⁻¹ • (x - Complex.I • Ic x) + (2 : ℂ)⁻¹ • (x + Complex.I • Ic x) := by
      module
    rw [this]
    exact Submodule.add_mem_sup hy hz
  have hdisj : W ⊓ V10 n I ⊓ (W ⊓ V01 n I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← s24b_V10_inf_V01 n I]
    exact ⟨hx.1.2, hx.2.2⟩
  have hdim : Module.finrank ℂ ↥(W ⊓ V10 n I) = Module.finrank ℂ ↥(W ⊓ V01 n I) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ V10 n I) (W ⊓ V01 n I)
    rw [hsplit, hdisj, finrank_bot, add_zero, hWdim, h01] at this
    rw [h01]
    omega
  refine ⟨hmaps, ?_⟩
  rw [s24b_det_restrict Ic W _ _ hmaps inf_le_left inf_le_left hdisj hsplit Complex.I (-Complex.I)
    (fun x hx => Module.End.mem_eigenspace_iff.mp hx.2)
    (fun x hx => Module.End.mem_eigenspace_iff.mp hx.2), hdim, ← mul_pow]
  simp

theorem s24b_eig_dims (I : Module.End ℝ (V ℝ n))
    (hI : IsComplexStructure I)
    (hc : I * (PStd n d hd hn).fR (PStd_isCompl n d hd hn) =
      (PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I)
    (hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < (PStd n d hd hn).gI (PStd_isCompl n d hd hn) I x x) :
    Module.finrank ℝ (Module.End.eigenspace ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I)
        (Real.sqrt d)) = 2 * n ∧
      Module.finrank ℝ (Module.End.eigenspace ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I)
        (-Real.sqrt d)) = 2 * n := by
  have h1 : ∀ x, I ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) =
      (PStd n d hd hn).fR (PStd_isCompl n d hd hn) (I x) := by
    intro x; have := congrArg (fun T => T x) hc; simpa using this
  set fR := (PStd n d hd hn).fR (PStd_isCompl n d hd hn) with hfR
  have hsd : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (by exact_mod_cast hd.le)
  have hs0 : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hsd' : (Real.sqrt (d : ℝ))⁻¹ * d = Real.sqrt d := by
    rw [inv_mul_eq_iff_eq_mul₀ hs0]
    exact hsd.symm
  have hAA : ∀ x, (fR * I) ((fR * I) x) = (d : ℝ) • x := by
    intro x
    simp only [Module.End.mul_apply]
    rw [h1]
    have h2 := congrArg (fun T => T x) hI
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] at h2
    rw [s24b_fR_fR n d hd hn, h2]
    simp
  set L := LinearMap.range (LinearMap.inl ℝ (Module.Dual ℝ (H1 ℝ n)) (H1 ℝ n)) with hL
  have hLdim : Module.finrank ℝ L = 2 * n := by
    rw [hL, LinearMap.finrank_range_of_inj LinearMap.inl_injective, Subspace.dual_finrank_eq]
    simp
  have hLiso : ∀ x ∈ L, pairing ℝ n x x = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [s24b_pairing_apply]
    simp
  have hg : ∀ x, (PStd n d hd hn).gI (PStd_isCompl n d hd hn) I x x =
      -pairing ℝ n x ((fR * I) x) := by
    intro x
    rw [KSecant.gI, LinearMap.BilinForm.compRight_apply, s24b_XiR_apply n d hd hn,
      s24b_pairing_fR_left n d hd hn]
    rfl
  have hdisj : ∀ μ : ℝ, Module.End.eigenspace (fR * I) μ ⊓ L = ⊥ := by
    intro μ
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    by_contra hx
    have := hpos x hx
    rw [hg, Module.End.mem_eigenspace_iff.mp hx1, map_smul, hLiso x hx2, smul_zero,
      neg_zero] at this
    exact lt_irrefl 0 this
  have hVdim : Module.finrank ℝ (V ℝ n) = 2 * n + 2 * n := by
    rw [Module.finrank_prod, Subspace.dual_finrank_eq]
    simp
  have hle : ∀ μ : ℝ, Module.finrank ℝ (Module.End.eigenspace (fR * I) μ) ≤ 2 * n := by
    intro μ
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace (fR * I) μ) L
    rw [hdisj, finrank_bot, add_zero, hLdim] at h1
    have h2 := Submodule.finrank_le (Module.End.eigenspace (fR * I) μ ⊔ L)
    omega
  have hsup : Module.End.eigenspace (fR * I) (Real.sqrt d) ⊔
      Module.End.eigenspace (fR * I) (-Real.sqrt d) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hp : (2 : ℝ)⁻¹ • (x + (Real.sqrt d)⁻¹ • (fR * I) x) ∈
        Module.End.eigenspace (fR * I) (Real.sqrt d) := by
      rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hAA, smul_smul, hsd']
      linear_combination (norm := module) (mul_inv_cancel₀ hs0) • (-(2 : ℝ)⁻¹ • (fR * I) x)
    have hm : (2 : ℝ)⁻¹ • (x - (Real.sqrt d)⁻¹ • (fR * I) x) ∈
        Module.End.eigenspace (fR * I) (-Real.sqrt d) := by
      rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hAA, smul_smul, hsd']
      linear_combination (norm := module) (mul_inv_cancel₀ hs0) • (-(2 : ℝ)⁻¹ • (fR * I) x)
    have : x = (2 : ℝ)⁻¹ • (x + (Real.sqrt d)⁻¹ • (fR * I) x) +
        (2 : ℝ)⁻¹ • (x - (Real.sqrt d)⁻¹ • (fR * I) x) := by
      module
    rw [this]
    exact Submodule.add_mem_sup hp hm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace (fR * I) (Real.sqrt d))
    (Module.End.eigenspace (fR * I) (-Real.sqrt d))
  rw [hsup, finrank_top, hVdim] at hsum
  have h1 := hle (Real.sqrt d)
  have h2 := hle (-Real.sqrt d)
  omega

theorem s24b_etaV_apply (k : Kd d) (v : V ℚ n) :
    etaV n d hd k v = Kd.ratPart d k • v + Kd.sqrtNegCoeff d k • fV n d v := rfl

theorem s24b_bcEndV_etaV (k : Kd d) :
    bcEndV ℝ n (etaV n d hd k) =
      ((Kd.ratPart d k : ℚ) : ℝ) • 1 + ((Kd.sqrtNegCoeff d k : ℚ) : ℝ) • bcEndV ℝ n (fV n d) := by
  refine (basisV ℝ n).ext fun j => ?_
  rw [← s24b_bcV_basisV ℚ ℝ n j, s24b_bcEndV_bcV, s24b_etaV_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
    s24b_bcEndV_bcV]
  rw [← algebraMap_smul ℝ (Kd.ratPart d k), ← algebraMap_smul ℝ (Kd.sqrtNegCoeff d k)]
  rfl

theorem s24b_etaX_apply (k : Kd d) : etaX n d hd k = transportEnd n (etaV n d hd k) := rfl

theorem s24b_map_transportEnd_hX (A : Module.End ℚ (V ℚ n)) :
    ExteriorAlgebra.map (transportEnd n A) (hX n d) =
      ExteriorAlgebra.map (coordV ℚ n).toLinearMap (ExteriorAlgebra.map A (hV n d)) := by
  rw [hX, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp [transportEnd]

theorem s24b_hodgeMaps_iff (I : Module.End ℝ (V ℝ n)) :
    (∀ k, IsHodgeMap (transportEnd n (-I)) (transportEnd n (-I)) (etaX n d hd k)) ↔
      I * (PStd n d hd hn).fR (PStd_isCompl n d hd hn) =
        (PStd n d hd hn).fR (PStd_isCompl n d hd hn) * I := by
  have hT : ∀ X : Module.End ℝ (V ℝ n), (transportEnd n X ∘ₗ transportEnd n (-I) =
      transportEnd n (-I) ∘ₗ transportEnd n X ↔ X * I = I * X) := by
    intro X
    rw [show transportEnd n X ∘ₗ transportEnd n (-I) = transportEnd n X * transportEnd n (-I) from rfl,
      show transportEnd n (-I) ∘ₗ transportEnd n X = transportEnd n (-I) * transportEnd n X from rfl,
      ← s24b_transportEnd_mul, ← s24b_transportEnd_mul, (s24b_transportEnd_injective n).eq_iff,
      mul_neg, neg_mul, neg_inj]
  constructor
  · intro h
    have h1 := h (Kd.sqrtNeg d)
    rw [IsHodgeMap, etaX_sqrtNeg, fX, s24b_bcMap_transportEnd, hT, ← s24b_fR_PStd n d hd hn] at h1
    exact h1.symm
  · intro hc k
    rw [IsHodgeMap, s24b_etaX_apply, s24b_bcMap_transportEnd, hT, s24b_bcEndV_etaV,
      ← s24b_fR_PStd n d hd hn]
    rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul,
      mul_one, hc]

theorem s24b_map_mem_hodgeClassesX_iff (I : Module.End ℝ (V ℝ n)) (_hI : IsComplexStructure I)
    (p : ℕ) (α : ExtV ℚ n) :
    ExteriorAlgebra.map (coordV ℚ n).toLinearMap α ∈ hodgeClassesX (2 * n) (transportEnd n (-I)) p ↔
      α ∈ hodgeClassesV n I p := by
  have h10 : H10 (2 * n) (transportEnd n (-I)) = (V01 n I).map (coordV ℂ n).toLinearMap := by
    rw [H10, s24b_complexifyH1_transportEnd, transportEnd, s24b_eigenspace_conj,
      s24b_complexifyV_neg, s24b_eigenspace_neg]
    rfl
  have h01 : H01 (2 * n) (transportEnd n (-I)) = (V10 n I).map (coordV ℂ n).toLinearMap := by
    rw [H01, s24b_complexifyH1_transportEnd, transportEnd, s24b_eigenspace_conj,
      s24b_complexifyV_neg, s24b_eigenspace_neg, neg_neg]
    rfl
  rw [mem_hodgeClassesX_iff, mem_hodgeClassesV_iff, h10, h01, s24b_pqPiece_map, s24b_pqPiece_swap,
    s24b_bcS_map_coordV, s24b_mem_map_iff, s24b_map_mem_exteriorPower_iff]

/-- The Weil-type period domain of `(X × X̂, η, h)` in the model (`WeilDomain`) is the image of the
paper's period domain `Ω_P` of `P_Θ` (§4: "the period domain of deformations of `(X × X̂, Ξ_P, η)`
as a polarized abelian variety of Weil type"), under `I ↦ -I` (the paper's convention to the
standard one) and `coordV`.

`⊇` is Corollary 3.2.3 transported to the model: for `I ∈ Ω_P`, `η(K)` acts by Hodge
endomorphisms (`corollary3_2_3_comm`), `h = Ξ_P^♯` (`hClass_PStd`) is of type `(1,1)`
(`corollary3_2_3_type11`) and a Kähler class (`corollary3_2_3_kahler`), `η(k)^* h = Nm(k) h` (the
condition on the polarization, `corollary3_2_3_polarization`, with [van Geemen, Def. 4.9],
`s24b_map_η_hClass`), and the Weil condition is Lemma 3.2.1. `⊆` is the converse that the paper
leaves implicit (TeX line 443): a Weil-type complex structure of `(X × X̂, η, h)` lies in `Ω_P`. -/
theorem weilDomain_eq_image_OmegaP (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n)))
    (hη : η (Kd.sqrtNeg d) = fX n d) :
    WeilDomain η (hX n d) =
      (fun I => transportEnd n (-I)) '' (PStd n d hd hn).OmegaP (PStd_isCompl n d hd hn) := by
  obtain rfl : η = etaX n d hd := eq_etaX n d hd η hη
  have hWd := s24b_finrank_Wℂ n d hd hn
  have hEX := s24b_eigenspace_fX n d hd hn
  ext J'
  constructor
  · rintro ⟨hcs', hHod, hW1, hW2, hamp, -⟩
    set I := -s24b_untransport n J' with hIdef
    have hJ' : transportEnd n (-I) = J' := by
      rw [hIdef, neg_neg, s24b_transportEnd_untransport]
    refine ⟨I, ?_, hJ'⟩
    rw [← hJ'] at hcs' hHod hW1 hW2 hamp
    have hI : IsComplexStructure I := (s24b_isComplexStructure_transportEnd n I).mp hcs'
    have hc := (s24b_hodgeMaps_iff n d hd hn I).mp hHod
    have hc' : ∀ x, I ((PStd n d hd hn).fR (PStd_isCompl n d hd hn) x) =
        (PStd n d hd hn).fR (PStd_isCompl n d hd hn) (I x) := fun x => by
      have := congrArg (fun T => T x) hc; simpa using this
    have hIso := s24b_isometry_of_ev n d hd hn I hI hc' (s24b_ev_inv_of_hodgeX n d I hcs' hamp.1)
    have hpos : ∀ x : V ℝ n, x ≠ 0 → 0 < (PStd n d hd hn).gI (PStd_isCompl n d hd hn) I x x := by
      intro x hx
      have hne : pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap ≠ 0 := by
        intro h0
        apply hx
        apply s24b_pairing_injective ℝ n
        refine LinearMap.ext fun v => ?_
        have := LinearMap.congr_fun h0 (coordV ℝ n v)
        simpa using this
      have := hamp.2 _ hne
      rwa [s24b_eval2_hX n d hd hn I hI hIso x] at this
    obtain ⟨hE1, hE2⟩ := s24b_eig_dims n d hd hn I hI hc hpos
    obtain ⟨g, hg⟩ := remark2_4_3_exists_lift I hI hIso
    rw [etaX_sqrtNeg, hEX.1, s24b_H10_transport, s24b_finrank_map_inf] at hW1
    rw [etaX_sqrtNeg, hEX.2, s24b_H10_transport, s24b_finrank_map_inf] at hW2
    refine ⟨⟨rho ℝ n g, ⟨(mem_SOplus_iff ℝ n _).mpr ⟨g, rfl⟩, fun x => ?_, ?_, ?_⟩, hg⟩,
      hI, hE1, hE2, hpos⟩
    · have h1 : ∀ y, rho ℝ n g y = I y := fun y => by rw [← hg]; rfl
      rw [h1, h1, hc']
    · rw [hg]
      exact s24b_det_W n d hd hn I hI hc _ _ (s24b_eigenspace_fC n d hd hn).1.symm n hWd.1 hW1
    · rw [hg]
      exact s24b_det_W n d hd hn I hI hc _ _ (s24b_eigenspace_fC n d hd hn).2.symm n hWd.2 hW2
  · rintro ⟨I, hI, rfl⟩
    -- Corollary 3.2.3 for `I ∈ Ω_P`: `(V_ℝ/V_ℤ, I, Ξ_P)` is a polarized abelian variety of Weil
    -- type; the model's conditions are transported from its parts (`hClass_PStd`, `ηHom_PStd`)
    have hP := s24b_assumption_J0 n d hd hn
    have hweil := s24b_weil_of_mem_OmegaP n d hd hn I hI
    obtain ⟨hIP, hcs, hν, hpos⟩ := s24b_cor3_2_3_hyps n d hd hn I hI
    have hc := corollary3_2_3_comm (PStd n d hd hn) (s8_J0 n) hP I hIP hcs hν hpos
    have h11 := corollary3_2_3_type11 (PStd n d hd hn) (s8_J0 n) hP I hIP hcs hν hpos
    have hpol := corollary3_2_3_polarization (PStd n d hd hn) (s8_J0 n) hP I hIP hcs hν hpos
    have hIso : ∀ x y, pairing ℝ n (I x) (I y) = pairing ℝ n x y := by
      obtain ⟨g, -, hgI⟩ := hIP
      intro x y
      rw [← hgI]
      exact s24b_rho_isometry n g x y
    refine ⟨(s24b_isComplexStructure_transportEnd n I).mpr hcs,
      (s24b_hodgeMaps_iff n d hd hn I).mpr hc, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · rw [etaX_sqrtNeg, hEX.1, s24b_H10_transport, s24b_finrank_map_inf]
      exact hweil.1
    · rw [etaX_sqrtNeg, hEX.2, s24b_H10_transport, s24b_finrank_map_inf]
      exact hweil.2
    · -- `h` is of type `(1,1)`: `Ξ_P` is (Corollary 3.2.3)
      exact (s24b_map_mem_hodgeClassesX_iff n I hcs 1 (hV n d)).mpr
        (s24b_hV_hodge n d hd hn I hcs hIso h11)
    · -- positivity: `Ξ_P` is a Kähler class for `I` (Corollary 3.2.3)
      intro a ha
      obtain ⟨x, hx⟩ := s24b_pairing_surjective ℝ n (a ∘ₗ (coordV ℝ n).toLinearMap)
      have ha' : a = pairing ℝ n x ∘ₗ (coordV ℝ n).symm.toLinearMap := by
        rw [hx]
        refine LinearMap.ext fun w => ?_
        simp
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply ha
        rw [ha']
        simp
      rw [ha', s24b_eval2_hX n d hd hn I hcs hIso x]
      exact corollary3_2_3_kahler (PStd n d hd hn) (s8_J0 n) hP I hIP hcs hν hpos x hx0
    · -- `η(k)^* h = Nm(k) h`: the condition on the polarization (Corollary 3.2.3, `f^*Ξ_P = d Ξ_P`)
      -- with [van Geemen, Def. 4.9]
      intro k
      have h := s24b_map_η_hClass (PStd n d hd hn) hd (PStd_isCompl n d hd hn) hpol k
      have hηk : (PStd n d hd hn).η (PStd_isCompl n d hd hn) k = etaV n d hd k := by
        rw [← ηHom_PStd n d hd hn]; rfl
      rw [hClass_PStd n d hd hn, hηk] at h
      rw [s24b_etaX_apply, s24b_map_transportEnd_hX, h, map_smul]
      rfl

/-- Hodge classes for the standard complex structure `-I`, transported to the model, are the Hodge
classes of `I` (types `(p, q)` and `(q, p)` exchange, and `(p, p)` is symmetric). -/
theorem map_mem_hodgeClassesX_iff (I : Module.End ℝ (V ℝ n)) (hI : IsComplexStructure I) (p : ℕ)
    (α : ExtV ℚ n) :
    ExteriorAlgebra.map (coordV ℚ n).toLinearMap α ∈ hodgeClassesX (2 * n) (transportEnd n (-I)) p ↔
      α ∈ hodgeClassesV n I p :=
  s24b_map_mem_hodgeClassesX_iff n I hI p α

/-- The Hodge–Weil classes of `η` in the model (`HWof`) are the transported Hodge–Weil plane
`ĤW_P` of `P_Θ` (Corollary 3.2.2, `KSecant.hwPlane`). -/
theorem HWof_eq_map_hwPlane (η : Kd d →+* Module.End ℚ (H1 ℚ (2 * n)))
    (hη : η (Kd.sqrtNeg d) = fX n d) :
    HWof η =
      (PStd n d hd hn).hwPlane.map (ExteriorAlgebra.map (coordV ℚ n).toLinearMap).toLinearMap := by
  set P := PStd n d hd hn with hPdef
  have hW := PStd_isCompl n d hd hn
  have hf : bcMap ℚ (Kd d) (η (Kd.sqrtNeg d)) = transportEnd n (P.ηK hW (Kd.sqrtNeg d)) := by
    rw [hη, fX, s24b_bcMap_transportEnd, ← fη_PStd n d hd hn, KSecant.fη,
      s24b_bcEndV_η n d hd]
  have hE₁ : Module.End.eigenspace (bcMap ℚ (Kd d) (η (Kd.sqrtNeg d))) (Kd.sqrtNeg d) =
      P.W₁.map (coordV (Kd d) n).toLinearMap := by
    rw [hf, transportEnd, s24b_eigenspace_conj, (s24b_eigenspace_ηK n d hd P hW).1]
  have hE₂ : Module.End.eigenspace (bcMap ℚ (Kd d) (η (Kd.sqrtNeg d))) (-Kd.sqrtNeg d) =
      P.W₂.map (coordV (Kd d) n).toLinearMap := by
    rw [hf, transportEnd, s24b_eigenspace_conj, (s24b_eigenspace_ηK n d hd P hW).2]
  set T := topWedge P.W₁ (2 * n) ⊔ topWedge P.W₂ (2 * n) with hT
  have hT2 : T ≤ ⋀[Kd d]^(2 * n) (V (Kd d) n) :=
    sup_le (s24b_topWedge_le n _ _) (s24b_topWedge_le n _ _)
  ext x
  rw [HWof, KSecant.hwPlane, hE₁, hE₂, s24b_topWedge_map, s24b_topWedge_map, ← Submodule.map_sup,
    ← hT]
  simp only [Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem,
    AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨-, hx2⟩
    refine ⟨ExteriorAlgebra.map (coordV ℚ n).symm.toLinearMap x, ?_, ?_⟩
    · show bcExt ℚ (Kd d) n (ExteriorAlgebra.map (coordV ℚ n).symm.toLinearMap x) ∈ T
      rw [← s24b_mem_map_iff (coordV (Kd d) n), ← s24b_bcS_map_coordV]
      rwa [show ExteriorAlgebra.map (coordV ℚ n).toLinearMap
          (ExteriorAlgebra.map (coordV ℚ n).symm.toLinearMap x) = x from
        s24b_map_symm_map (coordV ℚ n).symm x]
    · exact s24b_map_symm_map (coordV ℚ n).symm x
  · rintro ⟨α, hα, rfl⟩
    have hα' : bcExt ℚ (Kd d) n α ∈ T := hα
    simp only [AlgHom.toLinearMap_apply]
    refine ⟨?_, ?_⟩
    · rw [s24b_map_mem_exteriorPower_iff]
      exact s24b_mem_exteriorPower_of_bcExt ℚ (Kd d) n (hT2 hα')
    · rw [s24b_bcS_map_coordV, s24b_mem_map_iff]
      exact hα'

end WeilClasses
