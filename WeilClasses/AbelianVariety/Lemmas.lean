module

public import WeilClasses.AbelianVariety.Defs
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import WeilClasses.WeilType.Theta

/-!
# Standard facts about abelian varieties used without citation (proof of Corollary 1.6.1)

The proof of Corollary 1.6.1 reduces the Hodge conjecture for an abelian fourfold to codimension
two and to the simple and non-simple cases. It uses, without citation:

* Poincaré's complete reducibility: a sub-Hodge structure of `H¹(A, ℚ)` has a complementary
  sub-Hodge structure (`AbVar.exists_isCompl_isHodgeSub`), so a non-simple abelian variety is
  isogenous to a product;
* sub-Hodge structures of `H¹(A, ℚ)` have even dimension (`AbVar.even_finrank_of_isHodgeSub`);
* the hard Lefschetz theorem for an ample class `h` on an abelian `g`-fold, in the case
  `h^{g-2} ∪ : H² → H^{2g-2}`, which maps Hodge classes onto Hodge classes
  (`AbVar.hodge_pred_le_map`), so that Hodge classes of degree `2g - 2` are algebraic once those of
  degree `2` are;
* the top degree: `H^{2g}(A, ℚ)` is spanned by `h^g` (`AbVar.top_eq_span_pow`).

The paper gives no proofs of these standard facts; ours are:

* hard Lefschetz: for `h ∈ ⋀² H¹` with `θ_h : y ↦ y ⌋ h` bijective, the operator
  `Λ = Σᵢ D_{θ_h⁻¹(eᵢ)} D_{fᵢ}` satisfies `Λ(h x) = h Λ(x) + 2(k - g) x` on `⋀^k`
  (`main_lef_Λ_mul`), and the usual `sl₂` induction shows that `h^r ∪ : ⋀^k → ⋀^{k+2r}` is
  injective for `k + r ≤ g` (`main_lef_injective`); an ample class is nondegenerate over `ℚ`
  (`IsAmple.bijective_thetaMap`) and over `ℝ` (by positivity, `main_lef_bijective_real`), and a
  dimension count gives bijectivity in degrees `2 → 2g - 2` and `0 → 2g`. Hodge types are detected
  by `⋀J`: it fixes the classes of type `(p, p)` (`main_lef_map_bcS_of_hodge`), and a `⋀J`-fixed
  rational class of degree `2` is of type `(1, 1)` (`main_lef_hodge_one_of_map`);
* Poincaré reducibility: the complement of `U` is `θ(U^⊥)` (`U^⊥ ⊆ H¹(A, ℚ)*` the annihilator,
  `θ = θ_Θ` for an ample `Θ`), the orthogonal of `U` for the polarization; it meets `U` trivially by
  positivity, and its real span `θ_ℝ(U_ℝ^⊥)` is `J`-stable since `θ_ℝ` intertwines `-J^*` and `J`
  (`thetaExt_comp_neg_dualMap`);
* even dimension: `J` restricts to the real span `U_ℝ`, of the same dimension as `U`
  (`main_lef_finrank_span_bcH1`), and `det(J|_{U_ℝ})² = (-1)^{dim U_ℝ}`.
-/

@[expose] public section

namespace WeilClasses

/-! ### Generic helpers (exterior algebras, base change, `eval2`) -/

section Helpers

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem main_algebraMapInv_ιMulti {M : Type*} [AddCommGroup M] [Module F M] (k : ℕ) (hk : k ≠ 0)
    (v : Fin k → M) : ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ιMulti F k v) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
  simp [ExteriorAlgebra.algebraMapInv]

omit [CharZero F] in
/-- The coefficient of `1 = e_∅` is the degree-`0` part. -/
theorem main_coord_empty :
    (basisS F n).coord ∅ = (ExteriorAlgebra.algebraMapInv : S F n →ₐ[F] F).toLinearMap := by
  refine (basisS F n).ext fun s => ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [basisS, AlgHom.toLinearMap_apply]
  rw [ExteriorAlgebra.basis_apply_ofCard (Pi.basisFun F (Fin (2 * n))) (s := s) rfl]
  by_cases hs : s = ∅
  · subst hs
    simp
  · simp only [hs, ↓reduceIte]
    exact (main_algebraMapInv_ιMulti F _ (by simpa [Finset.card_eq_zero] using hs) _).symm

theorem main_eval2_eq (ξ : S F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n ξ a b = ((basisS F n).coord ∅ ∘ₗ D F n b ∘ₗ D F n a) ξ := rfl

/-- `⟪x ∧ y, a ∧ b⟫ = a(x) b(y) - a(y) b(x)`. -/
theorem main_eval2_ι_mul_ι (x y : H1 F n) (a b : Module.Dual F (H1 F n)) :
    eval2 F n (ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F y) a b = a x * b y - a y * b x := by
  simp only [eval2, D, main_coord_empty]
  erw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
  simp only [map_sub, map_smul]
  rw [← Algebra.commutes, ← Algebra.smul_def, map_smul]
  erw [CliffordAlgebra.contractLeft_ι, CliffordAlgebra.contractLeft_ι]
  simp [ExteriorAlgebra.algebraMapInv]

theorem main_eval2_smul_right (ξ : S F n) (a b : Module.Dual F (H1 F n)) (c : F) :
    eval2 F n ξ a (c • b) = c * eval2 F n ξ a b := by
  simp only [eval2]
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]

omit [CharZero F] in
theorem main_bcH1_e (F' : Type*) [Field F'] [Algebra F F'] (i : Fin (2 * n)) :
    bcH1 F F' n (e F n i) = e F' n i := by
  funext k
  simp [bcH1, e, Pi.single_apply]

omit [CharZero F] in
theorem main_bcS_ι (F' : Type*) [Field F'] [CharZero F'] [Algebra F F'] (v : H1 F n) :
    bcS F F' n (ExteriorAlgebra.ι F v) = ExteriorAlgebra.ι F' (bcH1 F F' n v) := by
  unfold bcS
  erw [ExteriorAlgebra.lift_ι_apply]
  rfl

omit [CharZero F] in
theorem main_bcS_ThetaStd (F' : Type*) [Field F'] [CharZero F'] [Algebra F F'] :
    bcS F F' n (ThetaStd F n) = ThetaStd F' n := by
  simp only [ThetaStd, map_sum, map_mul, main_bcS_ι, main_bcH1_e]

end Helpers

section BcMap

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

theorem main_bcMap_smul {g g' : ℕ} (c : F) (φ : H1 F g →ₗ[F] H1 F g') :
    bcMap F F' (c • φ) = algebraMap F F' c • bcMap F F' φ := by
  simp only [bcMap]
  rw [map_smul LinearMap.toMatrix' c φ]
  rw [show (c • LinearMap.toMatrix' φ).map (algebraMap F F') =
      algebraMap F F' c • (LinearMap.toMatrix' φ).map (algebraMap F F') by ext; simp]
  rw [map_smul]

theorem main_bcMap_comp {g g' g'' : ℕ} (φ : H1 F g' →ₗ[F] H1 F g'') (ψ : H1 F g →ₗ[F] H1 F g') :
    bcMap F F' (φ ∘ₗ ψ) = bcMap F F' φ ∘ₗ bcMap F F' ψ := by
  simp only [bcMap, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]

theorem main_bcMap_id {g : ℕ} :
    bcMap F F' (LinearMap.id : H1 F g →ₗ[F] H1 F g) = LinearMap.id := by
  simp [bcMap, LinearMap.toMatrix'_id, Matrix.map_one]

theorem main_bcMap_bcH1 [CharZero F] [CharZero F'] {g g' : ℕ} (φ : H1 F g →ₗ[F] H1 F g')
    (v : H1 F g) : bcMap F F' φ (bcH1 F F' g v) = bcH1 F F' g' (φ v) := by
  funext i
  simp only [bcMap, Matrix.toLin'_apply, bcH1, LinearMap.compLeft_apply]
  rw [← LinearMap.toMatrix'_mulVec φ v]
  exact (RingHom.map_mulVec (algebraMap F F') (LinearMap.toMatrix' φ) v i).symm

/-- Base change commutes with the action of a linear map on cohomology. -/
theorem main_bcS_map [CharZero F] [CharZero F'] {g g' : ℕ} (φ : H1 F g →ₗ[F] H1 F g')
    (α : S F g) :
    bcS F F' g' (ExteriorAlgebra.map φ α) = ExteriorAlgebra.map (bcMap F F' φ) (bcS F F' g α) := by
  have : (bcS F F' g').comp (ExteriorAlgebra.map φ) =
      ((ExteriorAlgebra.map (bcMap F F' φ)).restrictScalars F).comp (bcS F F' g) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι, AlgHom.restrictScalars_apply]
    rw [main_bcS_ι, main_bcS_ι, ExteriorAlgebra.map_apply_ι, main_bcMap_bcH1]
  exact congrArg (fun f => f α) this

end BcMap

section Exterior

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem main_map_mem_topWedge (f : M →ₗ[R] N) (W : Submodule R M) (W' : Submodule R N)
    (hf : ∀ v ∈ W, f v ∈ W') (k : ℕ) {x : ExteriorAlgebra R M} (hx : x ∈ topWedge W k) :
    ExteriorAlgebra.map f x ∈ topWedge W' k := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [ExteriorAlgebra.map_apply_ιMulti]
    exact Submodule.subset_span ⟨f ∘ v, fun i => hf _ (hv i), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem main_map_mem_exteriorPower (f : M →ₗ[R] N) (k : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) : ExteriorAlgebra.map f x ∈ ⋀[R]^k N := by
  have := (exteriorPower.map k f ⟨x, hx⟩).2
  rwa [exteriorPower.coe_map] at this

theorem main_proj_of_mem {i j : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^j M) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) i x = if i = j then x else 0 := by
  rw [GradedAlgebra.proj_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx (Ne.symm h)

theorem main_contractLeft_map (φ : M →ₗ[R] N) (a : Module.Dual R N) (ξ : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R N)) a (ExteriorAlgebra.map φ ξ) =
      ExteriorAlgebra.map φ
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (a ∘ₗ φ) ξ) := by
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul m x hx =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    erw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
    rw [map_sub, map_smul, map_mul]
    erw [hx]
    simp [ExteriorAlgebra.map_apply_ι]

theorem main_algebraMapInv_map (φ : M →ₗ[R] N) (ξ : ExteriorAlgebra R M) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map φ ξ) = ExteriorAlgebra.algebraMapInv ξ := by
  rw [← AlgHom.comp_apply]
  congr 1
  exact ExteriorAlgebra.hom_ext (LinearMap.ext fun v => by simp [ExteriorAlgebra.algebraMapInv])

theorem main_algebraMapInv_reverse (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.reverse (Q := (0 : QuadraticForm R M)) x) =
      ExteriorAlgebra.algebraMapInv x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | mul a b ha hb => rw [CliffordAlgebra.reverse.map_mul, map_mul, map_mul, ha, hb, mul_comm]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Exterior

section Pairing

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- The pairing (1.2.2): `((θ₁,w₁),(θ₂,w₂))_V = θ₁(w₂) + θ₂(w₁)`. -/
theorem main_pairing_apply (v y : V F n) : pairing F n v y = v.1 y.2 + y.1 v.2 := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Q,
    QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

omit [CharZero F] in
theorem main_pairing_comm (v y : V F n) : pairing F n v y = pairing F n y v := by
  rw [main_pairing_apply, main_pairing_apply]; ring

omit [CharZero F] in
/-- The pairing (1.2.2) is nondegenerate. -/
theorem main_pairing_eq_zero (x : V F n) (h : ∀ y, pairing F n x y = 0) : x = 0 := by
  have h1 : x.1 = 0 := LinearMap.ext fun w => by
    simpa [main_pairing_apply] using h (0, w)
  have h2 : x.2 = 0 := (Module.forall_dual_apply_eq_zero_iff F x.2).mp fun θ => by
    simpa [main_pairing_apply] using h (θ, 0)
  exact Prod.ext h1 h2

end Pairing

/-! ### Graded-commutativity, reversal, nilpotency and grading projections -/

section Graded

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `y ∪ v = (-1)^k v ∪ y` for `y` of degree `k` and `v` of degree `1`. -/
theorem main_mul_ι_comm {k : ℕ} {y : ExteriorAlgebra R M} (hy : y ∈ ⋀[R]^k M) (a : M) :
    y * ExteriorAlgebra.ι R a = (-1 : R) ^ k • (ExteriorAlgebra.ι R a * y) := by
  induction k generalizing y with
  | zero =>
    rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one] at hy
    obtain ⟨c, rfl⟩ := hy
    simp [Algebra.commutes]
  | succ k ih =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc,
        ih (ExteriorAlgebra.ιMulti_range R k (Set.mem_range_self _)), mul_smul_comm,
        ← mul_assoc, ← mul_assoc,
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (w 0) a)]
      simp only [neg_mul, smul_neg, pow_succ, mul_neg, mul_one, neg_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, hx, hy, mul_add, smul_add]
    | smul c x _ hx => rw [smul_mul_assoc, hx, mul_smul_comm, smul_comm]

/-- The main anti-automorphism acts on `⋀^k` by `(-1)^{k(k-1)/2}`. -/
theorem main_reverse_of_mem {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    CliffordAlgebra.reverse (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ (k.choose 2) • x := by
  induction k generalizing x with
  | zero =>
    rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    simp
  | succ k ih =>
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      have hw := ExteriorAlgebra.ιMulti_range R k (Set.mem_range_self (Matrix.vecTail w))
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.reverse.map_mul,
        CliffordAlgebra.reverse_ι, ih hw]
      erw [smul_mul_assoc, main_mul_ι_comm hw]
      rw [smul_smul, ← pow_add, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
    | smul c y _ hy => rw [map_smul, hy, smul_comm]

/-- Classes of degree `2` are central. -/
theorem main_commute_of_mem_two {c : ExteriorAlgebra R M} (hc : c ∈ ⋀[R]^2 M)
    (x : ExteriorAlgebra R M) : Commute c x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r c |>.symm
  | ι v =>
    show c * _ = _ * c
    rw [main_mul_ι_comm hc]; simp
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

theorem main_mul_mem {i j : ℕ} {x y : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^i M)
    (hy : y ∈ ⋀[R]^j M) : x * y ∈ ⋀[R]^(i + j) M :=
  SetLike.mul_mem_graded hx hy

theorem main_pow_mem {i : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^i M) (k : ℕ) :
    x ^ k ∈ ⋀[R]^(i * k) M := by
  rw [mul_comm]; exact SetLike.pow_mem_graded k hx

/-- A homogeneous element of positive degree in the exterior algebra of a finite free module is
nilpotent. -/
theorem main_isNilpotent_of_mem [Module.Free R M] [Module.Finite R M] {k : ℕ} (hk : k ≠ 0)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) : IsNilpotent x := by
  refine ⟨Module.finrank R M + 1, ?_⟩
  have hmem := main_pow_mem hx (Module.finrank R M + 1)
  have := exteriorPower.eq_zero_of_finrank_lt (R := R) (M := M) _
    (show Module.finrank R M < k * (Module.finrank R M + 1) by
      calc Module.finrank R M < Module.finrank R M + 1 := Nat.lt_succ_self _
        _ ≤ k * (Module.finrank R M + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk))
    ⟨_, hmem⟩
  exact congrArg Subtype.val this

/-- The degree-`k` part of `c y` for `c` homogeneous of degree `j`. -/
theorem main_proj_mul_of_mem_left {j k : ℕ} {c : ExteriorAlgebra R M} (hc : c ∈ ⋀[R]^j M)
    (y : ExteriorAlgebra R M) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) k (c * y) =
      if j ≤ k then c * GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) (k - j) y else 0 := by
  simp only [GradedAlgebra.proj_apply]
  exact DirectSum.coe_decompose_mul_of_left_mem _ k hc

/-- The degree-`0` part is the `algebraMap` of the augmentation. -/
theorem main_proj_zero (y : ExteriorAlgebra R M) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) 0 y =
      algebraMap R _ (ExteriorAlgebra.algebraMapInv y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
  | zero => simp
  | @homogeneous j x =>
    obtain ⟨x, hx⟩ := x
    simp only
    rw [main_proj_of_mem hx]
    split_ifs with h
    · subst h
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp
        (show x ∈ (1 : Submodule R _) by simpa [ExteriorAlgebra.exteriorPower] using hx)
      rw [← hc]; simp
    · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
      have : ExteriorAlgebra.algebraMapInv x = 0 := by
        induction hx using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨w, rfl⟩ := hz
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Ne.symm h)
          rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
          simp [ExteriorAlgebra.algebraMapInv]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
        | smul c a _ ha => rw [map_smul, ha, smul_zero]
      rw [this, map_zero]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

/-- `ExteriorAlgebra.map` commutes with the grading projections. -/
theorem main_proj_map (f : M →ₗ[R] N) (k : ℕ) (y : ExteriorAlgebra R M) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i N) k (ExteriorAlgebra.map f y) =
      ExteriorAlgebra.map f (GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) k y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
  | zero => simp
  | @homogeneous j x =>
    rw [main_proj_of_mem x.2, main_proj_of_mem (main_map_mem_exteriorPower f j x.2)]
    split_ifs <;> simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end Graded

/-! ### Double contractions `⟪ξ, a ∧ b⟫ = b ⌋ (a ⌋ ξ)` determine classes of degree `2` -/

section DoubleContraction

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `⟪x ∧ y, a ∧ b⟫ = a(x) b(y) - a(y) b(x)`. -/
theorem main_dc_ι_mul_ι (a b : Module.Dual R M) (x y : M) :
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) b
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) a
        (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y))) = a x * b y - a y * b x := by
  erw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
  simp only [map_sub, map_smul]
  rw [← Algebra.commutes, ← Algebra.smul_def, map_smul]
  erw [CliffordAlgebra.contractLeft_ι, CliffordAlgebra.contractLeft_ι]
  simp [ExteriorAlgebra.algebraMapInv]

/-- Naturality of double contractions. -/
theorem main_dc_map {N : Type*} [AddCommGroup N] [Module R N] (T : M →ₗ[R] N)
    (a b : Module.Dual R N) (ξ : ExteriorAlgebra R M) :
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R N)) b
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R N)) a (ExteriorAlgebra.map T ξ))) =
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
      (b ∘ₗ T) (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (a ∘ₗ T) ξ)) := by
  rw [main_contractLeft_map, main_contractLeft_map, main_algebraMapInv_map]

/-- A class of degree `2` is determined by its double contractions:
`ξ = ½ Σ_{i,j} ⟪ξ, bᵢ* ∧ bⱼ*⟫ bᵢ ∧ bⱼ`. -/
theorem main_eq_sum_of_mem_two {F : Type*} [Field F] [CharZero F] {M : Type*} [AddCommGroup M]
    [Module F M] {ι : Type*} [Fintype ι] (bs : Module.Basis ι F M) {ξ : ExteriorAlgebra F M}
    (hξ : ξ ∈ ⋀[F]^2 M) :
    ξ = (2 : F)⁻¹ • ∑ i, ∑ j, ExteriorAlgebra.algebraMapInv
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) (bs.coord j)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) (bs.coord i) ξ)) •
        (ExteriorAlgebra.ι F (bs i) * ExteriorAlgebra.ι F (bs j)) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hξ
  induction hξ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, mul_one, main_dc_ι_mul_ι, sub_smul, Finset.sum_sub_distrib, mul_smul,
      Fin.succ_zero_eq_one]
    have hsum : ∀ w : M, ∑ i, bs.coord i w • ExteriorAlgebra.ι F (bs i) = ExteriorAlgebra.ι F w :=
      fun w => by
        have := congrArg (ExteriorAlgebra.ι F) (bs.sum_repr w)
        rw [map_sum] at this
        simpa [map_smul, Module.Basis.coord_apply] using this
    have h1 : ∑ i, ∑ j, bs.coord i (v 0) • bs.coord j (v 1) •
        (ExteriorAlgebra.ι F (bs i) * ExteriorAlgebra.ι F (bs j)) =
        ExteriorAlgebra.ι F (v 0) * ExteriorAlgebra.ι F (v 1) := by
      rw [← hsum (v 0), ← hsum (v 1), Finset.sum_mul_sum]
      simp only [smul_mul_smul_comm, smul_smul]
    have h2 : ∑ i, ∑ j, bs.coord i (v 1) • bs.coord j (v 0) •
        (ExteriorAlgebra.ι F (bs i) * ExteriorAlgebra.ι F (bs j)) =
        ExteriorAlgebra.ι F (v 1) * ExteriorAlgebra.ι F (v 0) := by
      rw [← hsum (v 0), ← hsum (v 1), Finset.sum_mul_sum]
      simp only [smul_mul_smul_comm, smul_smul]
    rw [h1, h2, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (v 1) (v 0)),
      sub_neg_eq_add, ← two_smul F (ExteriorAlgebra.ι F (v 0) * ExteriorAlgebra.ι F (v 1)),
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib, smul_add]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_comm (2 : F)⁻¹ c]
    rw [← hx]

/-- Two classes of degree `2` with the same double contractions are equal. -/
theorem main_eq_of_dc {F : Type*} [Field F] [CharZero F] {M : Type*} [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] {ξ η : ExteriorAlgebra F M} (hξ : ξ ∈ ⋀[F]^2 M)
    (hη : η ∈ ⋀[F]^2 M)
    (h : ∀ a b : Module.Dual F M,
      ExteriorAlgebra.algebraMapInv (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) b
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) a ξ)) =
      ExteriorAlgebra.algebraMapInv (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) b
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F M)) a η))) : ξ = η := by
  rw [main_eq_sum_of_mem_two (Module.finBasis F M) hξ,
    main_eq_sum_of_mem_two (Module.finBasis F M) hη]
  simp only [h]

end DoubleContraction

theorem main_eigenspace_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (c μ : K) (hc : c ≠ 0) :
    Module.End.eigenspace (c • f) (c * μ) = Module.End.eigenspace f μ := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, LinearMap.smul_apply, mul_smul]
  exact (smul_right_injective M hc).eq_iff

/-! ### Hard Lefschetz for a nondegenerate class of degree `2` -/

section Lefschetz

variable {F : Type*} [Field F] [CharZero F] {g : ℕ}

omit [CharZero F] in
theorem main_lef_ι_mem_one (v : H1 F g) : ExteriorAlgebra.ι F v ∈ ⋀[F]^1 (H1 F g) := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]; exact LinearMap.mem_range_self _ v

omit [CharZero F] in
theorem main_lef_D_ι (y : Module.Dual F (H1 F g)) (v : H1 F g) :
    D F g y (ExteriorAlgebra.ι F v) = algebraMap F (S F g) (y v) := by
  simp only [D]
  erw [CliffordAlgebra.contractLeft_ι]

omit [CharZero F] in
theorem main_lef_D_ι_mul (y : Module.Dual F (H1 F g)) (v : H1 F g) (x : S F g) :
    D F g y (ExteriorAlgebra.ι F v * x) = y v • x - ExteriorAlgebra.ι F v * D F g y x := by
  simp only [D]
  erw [CliffordAlgebra.contractLeft_ι_mul]

omit [CharZero F] in
theorem main_lef_D_algebraMap (y : Module.Dual F (H1 F g)) (c : F) :
    D F g y (algebraMap F (S F g) c) = 0 := by
  simp [D]

omit [CharZero F] in
/-- `D_y` lowers degrees by one. -/
theorem main_lef_D_mem (y : Module.Dual F (H1 F g)) :
    ∀ (k : ℕ) {x : S F g}, x ∈ ⋀[F]^(k + 1) (H1 F g) → D F g y x ∈ ⋀[F]^k (H1 F g) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [zero_add, ExteriorAlgebra.exteriorPower, pow_one] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [main_lef_D_ι, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  | succ k ih =>
    intro x hx
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [ExteriorAlgebra.ιMulti_succ_apply, main_lef_D_ι_mul]
      have hw := ExteriorAlgebra.ιMulti_range F (k + 1) (Set.mem_range_self (Matrix.vecTail w))
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hw) ?_
      have := main_mul_mem (main_lef_ι_mem_one (w 0)) (ih hw)
      rwa [add_comm 1 k] at this
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

omit [CharZero F] in
theorem main_lef_D_eq_zero_of_mem_zero (y : Module.Dual F (H1 F g)) {x : S F g}
    (hx : x ∈ ⋀[F]^0 (H1 F g)) : D F g y x = 0 := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one] at hx
  obtain ⟨c, rfl⟩ := hx
  exact main_lef_D_algebraMap y c

omit [CharZero F] in
theorem main_lef_ιMulti_two (w : Fin 2 → H1 F g) :
    ExteriorAlgebra.ιMulti F 2 w = ExteriorAlgebra.ι F (w 0) * ExteriorAlgebra.ι F (w 1) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

omit [CharZero F] in
/-- `D_y (c x) = D_y(c) x + c D_y(x)` for `c` of degree two. -/
theorem main_lef_D_mul_two (y : Module.Dual F (H1 F g)) {c : S F g} (hc : c ∈ ⋀[F]^2 (H1 F g))
    (x : S F g) : D F g y (c * x) = D F g y c * x + c * D F g y x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hc
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [main_lef_ιMulti_two, mul_assoc, main_lef_D_ι_mul, main_lef_D_ι_mul, main_lef_D_ι_mul,
      main_lef_D_ι,
      ← Algebra.commutes, ← Algebra.smul_def]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel
  | zero => simp
  | add a b _ _ ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | smul r a _ ha => rw [smul_mul_assoc, map_smul, map_smul, ha, smul_add, smul_mul_assoc,
      smul_mul_assoc]

omit [CharZero F] in
theorem main_lef_sum_e (a : H1 F g) : ∑ i, a i • e F g i = a := by
  ext j; simp [e, Pi.single_apply]

omit [CharZero F] in
theorem main_lef_f_apply (i : Fin (2 * g)) (a : H1 F g) : f F g i a = a i := rfl

/-- The Euler identity `Σᵢ eᵢ ∧ (fᵢ ⌋ x) = k x` on `⋀^k`. -/
theorem main_lef_euler : ∀ (k : ℕ) {x : S F g}, x ∈ ⋀[F]^k (H1 F g) →
    ∑ i, ExteriorAlgebra.ι F (e F g i) * D F g (f F g i) x = (k : F) • x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp [main_lef_D_eq_zero_of_mem_zero _ hx]
  | succ k ih =>
    intro x hx
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      have hw := ExteriorAlgebra.ιMulti_range F k (Set.mem_range_self (Matrix.vecTail w))
      have h1 : ∑ i, ExteriorAlgebra.ι F (e F g i) * D F g (f F g i)
          (ExteriorAlgebra.ι F (w 0) * ExteriorAlgebra.ιMulti F k (Matrix.vecTail w)) =
          ∑ i, (w 0 i • (ExteriorAlgebra.ι F (e F g i) *
              ExteriorAlgebra.ιMulti F k (Matrix.vecTail w)) +
            ExteriorAlgebra.ι F (w 0) * (ExteriorAlgebra.ι F (e F g i) *
              D F g (f F g i) (ExteriorAlgebra.ιMulti F k (Matrix.vecTail w)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [main_lef_D_ι_mul, main_lef_f_apply, mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc,
          eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e F g i) (w 0)),
          neg_mul, sub_neg_eq_add, mul_assoc]
      have h2 : ∑ i, w 0 i • (ExteriorAlgebra.ι F (e F g i) *
          ExteriorAlgebra.ιMulti F k (Matrix.vecTail w)) =
          ExteriorAlgebra.ι F (w 0) * ExteriorAlgebra.ιMulti F k (Matrix.vecTail w) := by
        simp only [← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum, main_lef_sum_e]
      rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ih hw, h2, mul_smul_comm, Nat.cast_succ,
        add_smul, one_smul, add_comm]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, mul_add, Finset.sum_add_distrib, ha, hb, smul_add]
    | smul c a _ ha =>
      simp only [map_smul, mul_smul_comm, ← Finset.smul_sum, ha]
      rw [smul_comm]

/-- `y'(θ_h y) = -y(θ_h y')` for `h` of degree `2` (`θ_h = contractOne h`). -/
theorem main_lef_theta_antisymm (h : S F g) (hh : h ∈ ⋀[F]^2 (H1 F g))
    (y y' : Module.Dual F (H1 F g)) :
    y' (contractOne F g h y) = -(y (contractOne F g h y')) := by
  have key : ∀ a b : Module.Dual F (H1 F g), b (contractOne F g h a) =
      ExteriorAlgebra.algebraMapInv (D F g b (D F g a h)) := by
    intro a b
    rw [← ι_contractOne F g h hh a, main_lef_D_ι]
    simp
  rw [key, key]
  simp only [D]
  rw [CliffordAlgebra.contractLeft_comm, map_neg]

variable (h : S F g) (hθ : Function.Bijective (contractOne F g h))

/-- The functionals `ψᵢ = θ⁻¹(eᵢ)`. -/
noncomputable def main_lefPsi (i : Fin (2 * g)) : Module.Dual F (H1 F g) :=
  (LinearEquiv.ofBijective (contractOne F g h) hθ).symm (e F g i)

omit [CharZero F] in
theorem main_lef_theta_psi (i : Fin (2 * g)) :
    contractOne F g h (main_lefPsi h hθ i) = e F g i := by
  have := (LinearEquiv.ofBijective (contractOne F g h) hθ).apply_symm_apply (e F g i)
  rwa [LinearEquiv.ofBijective_apply] at this

/-- The dual Lefschetz operator `Λ = Σᵢ D_{ψᵢ} D_{fᵢ}` (up to the factor `-1/2`). -/
noncomputable def main_lefΛ (x : S F g) : S F g :=
  ∑ i, D F g (main_lefPsi h hθ i) (D F g (f F g i) x)

omit [CharZero F] in
theorem main_lefΛ_zero : main_lefΛ h hθ 0 = 0 := by simp [main_lefΛ]

/-- `[Λ, L] = 2(k - g)` on `⋀^k`. -/
theorem main_lef_Λ_mul (hh : h ∈ ⋀[F]^2 (H1 F g)) {k : ℕ} {x : S F g} (hx : x ∈ ⋀[F]^k (H1 F g)) :
    main_lefΛ h hθ (h * x) = h * main_lefΛ h hθ x + (2 * (k : F) - 2 * g) • x := by
  have hθf : ∀ i, D F g (f F g i) h = ExteriorAlgebra.ι F (contractOne F g h (f F g i)) :=
    fun i => (ι_contractOne F g h hh _).symm
  have hθψ : ∀ i, D F g (main_lefPsi h hθ i) h = ExteriorAlgebra.ι F (e F g i) := fun i => by
    rw [← ι_contractOne F g h hh, main_lef_theta_psi]
  have step : ∀ i, D F g (main_lefPsi h hθ i) (D F g (f F g i) (h * x)) =
      (main_lefPsi h hθ i (contractOne F g h (f F g i))) • x
        - ExteriorAlgebra.ι F (contractOne F g h (f F g i)) * D F g (main_lefPsi h hθ i) x
        + ExteriorAlgebra.ι F (e F g i) * D F g (f F g i) x
        + h * D F g (main_lefPsi h hθ i) (D F g (f F g i) x) := by
    intro i
    rw [main_lef_D_mul_two _ hh, hθf, map_add, main_lef_D_ι_mul, main_lef_D_mul_two _ hh, hθψ]
    abel
  have hA : ∀ i, main_lefPsi h hθ i (contractOne F g h (f F g i)) = -1 := by
    intro i
    rw [main_lef_theta_antisymm h hh, main_lef_theta_psi, main_lef_f_apply]
    simp [e]
  have hcomb : ∀ j, ∑ i, (contractOne F g h (f F g i)) j • main_lefPsi h hθ i = -(f F g j) := by
    intro j
    apply hθ.1
    rw [map_sum, map_neg]
    simp only [map_smul, main_lef_theta_psi]
    have hsw : ∀ i, (contractOne F g h (f F g i)) j = -((contractOne F g h (f F g j)) i) :=
      fun i => main_lef_theta_antisymm h hh (f F g i) (f F g j)
    simp only [hsw, neg_smul, Finset.sum_neg_distrib, main_lef_sum_e]
  have hB : ∑ i, ExteriorAlgebra.ι F (contractOne F g h (f F g i)) * D F g (main_lefPsi h hθ i) x =
      -((k : F) • x) := by
    have hexp : ∀ i, ExteriorAlgebra.ι F (contractOne F g h (f F g i)) =
        ∑ j, (contractOne F g h (f F g i)) j • ExteriorAlgebra.ι F (e F g j) := fun i => by
      conv_lhs => rw [← main_lef_sum_e (contractOne F g h (f F g i))]
      rw [map_sum]
      simp only [map_smul]
    simp only [hexp, Finset.sum_mul, smul_mul_assoc]
    rw [Finset.sum_comm]
    simp only [← mul_smul_comm, ← Finset.mul_sum]
    have hj : ∀ j, ∑ i, (contractOne F g h (f F g i)) j • D F g (main_lefPsi h hθ i) x =
        -(D F g (f F g j) x) := fun j => by
      have := congrArg (fun φ => D F g φ x) (hcomb j)
      simpa [map_sum, map_smul, map_neg, LinearMap.sum_apply] using this
    simp only [hj, mul_neg, Finset.sum_neg_distrib, main_lef_euler k hx]
  simp only [main_lefΛ, step, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hA,
    hB,
    main_lef_euler k hx]
  rw [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  module

omit [CharZero F] in
theorem main_lef_Λ_mem {k : ℕ} {x : S F g}
    (hx : x ∈ ⋀[F]^(k + 2) (H1 F g)) : main_lefΛ h hθ x ∈ ⋀[F]^k (H1 F g) :=
  Submodule.sum_mem _ fun _ _ => main_lef_D_mem _ k (main_lef_D_mem _ (k + 1) hx)

omit [CharZero F] in
theorem main_lef_Λ_eq_zero {k : ℕ} (hk : k < 2) {x : S F g} (hx : x ∈ ⋀[F]^k (H1 F g)) :
    main_lefΛ h hθ x = 0 := by
  interval_cases k
  · simp [main_lefΛ, main_lef_D_eq_zero_of_mem_zero _ hx]
  · simp [main_lefΛ, main_lef_D_eq_zero_of_mem_zero _ (main_lef_D_mem _ 0 hx)]

/-- `Λ(h^{r+1} x) = h^{r+1} Λ(x) + 2(r+1)(k+r-g) h^r x` on `⋀^k`. -/
theorem main_lef_Λ_pow_mul (hh : h ∈ ⋀[F]^2 (H1 F g)) {k : ℕ} {x : S F g}
    (hx : x ∈ ⋀[F]^k (H1 F g)) (r : ℕ) :
    main_lefΛ h hθ (h ^ (r + 1) * x) = h ^ (r + 1) * main_lefΛ h hθ x +
      (2 * ((r : F) + 1) * ((k : F) + r - g)) • (h ^ r * x) := by
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one_mul, main_lef_Λ_mul h hθ hh hx]
    congr 2
    push_cast
    ring
  | succ r ih =>
    have hmem : h ^ (r + 1) * x ∈ ⋀[F]^(2 * (r + 1) + k) (H1 F g) :=
      main_mul_mem (main_pow_mem hh (r + 1)) hx
    rw [pow_succ' h (r + 1), mul_assoc, main_lef_Λ_mul h hθ hh hmem, ih, mul_add, ← mul_assoc,
      ← pow_succ', mul_smul_comm, ← mul_assoc h (h ^ r), ← pow_succ', add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

include hθ in
/-- **Hard Lefschetz** (injectivity): for a nondegenerate `h ∈ ⋀² H¹` and `k + r ≤ g`,
`h^r ∪ : ⋀^k → ⋀^{k + 2r}` is injective. -/
theorem main_lef_injective (hh : h ∈ ⋀[F]^2 (H1 F g)) :
    ∀ k r : ℕ, k + r ≤ g → ∀ x ∈ ⋀[F]^k (H1 F g), h ^ r * x = 0 → x = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro r
  induction r with
  | zero => intro _ x _ hx; simpa using hx
  | succ r ihr =>
    intro hkr x hx hzero
    have h1 := main_lef_Λ_pow_mul h hθ hh hx r
    rw [hzero, main_lefΛ_zero] at h1
    have h2 : h ^ (r + 2) * main_lefΛ h hθ x = 0 := by
      have := congrArg (h * ·) h1
      simp only [mul_zero, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ'] at this
      rw [hzero, smul_zero, add_zero] at this
      exact this.symm
    have hΛ : main_lefΛ h hθ x = 0 := by
      rcases lt_or_ge k 2 with hk | hk
      · exact main_lef_Λ_eq_zero h hθ hk hx
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        exact ihk k' (by omega) (r + 2) (by omega) _ (main_lef_Λ_mem h hθ hx) h2
    rw [hΛ, mul_zero, zero_add] at h1
    have hc : (2 * ((r : F) + 1) * ((k : F) + r - g)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
      · exact_mod_cast Nat.succ_ne_zero r
      · intro h0
        have : ((k + r : ℕ) : F) = ((g : ℕ) : F) := by push_cast; linear_combination h0
        have := Nat.cast_injective this
        omega
    have h3 : h ^ r * x = 0 := (smul_eq_zero.mp h1.symm).resolve_left hc
    exact ihr (by omega) x hx h3

end Lefschetz

/-! ### Base change of `H*(X)` and Hodge types via `⋀J` -/

section BaseChangeS

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

omit [CharZero F] in
theorem main_lef_bcS_ιMulti (k : ℕ) (v : Fin k → H1 F n) :
    bcS F F' n (ExteriorAlgebra.ιMulti F k v) =
      ExteriorAlgebra.ιMulti F' k (bcH1 F F' n ∘ v) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, main_bcS_ι]

omit [CharZero F] in
theorem main_lef_bcS_basisS (s : Finset (Fin (2 * n))) :
    bcS F F' n (basisS F n s) = basisS F' n s := by
  simp only [basisS]
  rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl,
    ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [main_lef_bcS_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.basisFun_apply]
  exact main_bcH1_e F n F' _

omit [CharZero F] in
/-- Base change `H*(X, F) → H*(X, F')` is injective. -/
theorem main_lef_bcS_injective : Function.Injective (bcS F F' n) := by
  refine (injective_iff_map_eq_zero (bcS F F' n)).mpr fun x hx => ?_
  have hli : LinearIndependent F (fun s => basisS F' n s) :=
    (basisS F' n).linearIndependent.restrict_scalars' F
  rw [← (basisS F n).sum_repr x, map_sum] at hx
  simp only [map_smul, main_lef_bcS_basisS] at hx
  have h0 := Fintype.linearIndependent_iff.mp hli _ hx
  rw [← (basisS F n).sum_repr x]
  simp [h0]

omit [CharZero F] in
/-- Base change preserves degrees. -/
theorem main_lef_bcS_mem {k : ℕ} {x : S F n} (hx : x ∈ ⋀[F]^k (H1 F n)) :
    bcS F F' n x ∈ ⋀[F']^k (H1 F' n) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [main_lef_bcS_ιMulti]
    exact ExteriorAlgebra.ιMulti_range F' k (Set.mem_range_self _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, ← algebraMap_smul F']; exact Submodule.smul_mem _ _ ha

end BaseChangeS

section Complex

variable (n : ℕ)

/-- `ℚ → ℝ → ℂ` base change is `ℚ → ℂ` base change. -/
theorem main_lef_bcS_bcS (x : S ℚ n) : bcS ℝ ℂ n (bcS ℚ ℝ n x) = bcS ℚ ℂ n x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    rw [main_bcS_ι, main_bcS_ι, main_bcS_ι]
    congr 1
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- `complexifyH1` is the base change `bcMap ℝ ℂ`. -/
theorem main_lef_complexifyH1_eq (A : Module.End ℝ (H1 ℝ n)) : complexifyH1 n A = bcMap ℝ ℂ A := by
  simp only [complexifyH1, bcMap, LinearMap.toMatrix_eq_toMatrix', Matrix.toLin_eq_toLin']

/-- `J_ℂ² = -1` for a complex structure `J`. -/
theorem main_lef_complexifyH1_sq {J : Module.End ℝ (H1 ℝ n)} (hJ : IsComplexStructure J)
    (v : H1 ℂ n) : complexifyH1 n J (complexifyH1 n J v) = -v := by
  rw [main_lef_complexifyH1_eq, ← LinearMap.comp_apply, ← main_bcMap_comp]
  have : J ∘ₗ J = (-1 : ℝ) • LinearMap.id := by
    rw [← Module.End.mul_eq_comp, hJ]
    ext
    simp
  rw [this, main_bcMap_smul, main_bcMap_id]
  simp

theorem main_lef_ιMulti_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (k : ℕ) (c : K)
    (v : Fin k → M) :
    ExteriorAlgebra.ιMulti K k (fun i => c • v i) = c ^ k • ExteriorAlgebra.ιMulti K k v := by
  have := (ExteriorAlgebra.ιMulti K k).toMultilinearMap.map_smul_univ (fun _ => c) v
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this

theorem main_lef_ιMulti_one {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (w : Fin 1 → M) :
    ExteriorAlgebra.ιMulti K 1 w = ExteriorAlgebra.ι K (w 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

/-- `⋀J` acts trivially on classes of type `(p, p)`. -/
theorem main_lef_map_pqPiece_pp (J : Module.End ℝ (H1 ℝ n)) (p : ℕ) {x : S ℂ n}
    (hx : x ∈ pqPiece (H10 n J) (H01 n J) p p) :
    ExteriorAlgebra.map (complexifyH1 n J) x = x := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    rw [map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
    have ha' : complexifyH1 n J ∘ a = fun i => Complex.I • a i :=
      funext fun i => Module.End.mem_eigenspace_iff.mp (ha i)
    have hb' : complexifyH1 n J ∘ b = fun i => (-Complex.I) • b i :=
      funext fun i => Module.End.mem_eigenspace_iff.mp (hb i)
    rw [ha', hb', main_lef_ιMulti_smul, main_lef_ιMulti_smul, smul_mul_smul_comm, ← mul_pow]
    simp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

theorem main_lef_gen_mem_pq11 (J : Module.End ℝ (H1 ℝ n)) {a b : H1 ℂ n} (ha : a ∈ H10 n J)
    (hb : b ∈ H01 n J) :
    ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b ∈ pqPiece (H10 n J) (H01 n J) 1 1 :=
  Submodule.subset_span ⟨fun _ => a, fun _ => b, fun _ => ha, fun _ => hb, by
    simp only [main_lef_ιMulti_one]⟩

/-- For `x ∈ ⋀² H¹(ℂ)`, `x + ⋀J x` is of type `(1,1)`. -/
theorem main_lef_add_map_mem_pq11 {J : Module.End ℝ (H1 ℝ n)} (hJ : IsComplexStructure J)
    {x : S ℂ n} (hx : x ∈ ⋀[ℂ]^2 (H1 ℂ n)) :
    x + ExteriorAlgebra.map (complexifyH1 n J) x ∈ pqPiece (H10 n J) (H01 n J) 1 1 := by
  set T := complexifyH1 n J with hTdef
  have hT := main_lef_complexifyH1_sq n hJ
  set P := pqPiece (H10 n J) (H01 n J) 1 1
  have hdec : ∀ u : H1 ℂ n, ∃ p ∈ H10 n J, ∃ q ∈ H01 n J, u = p + q := by
    intro u
    refine ⟨(2⁻¹ : ℂ) • (u - Complex.I • T u), ?_, (2⁻¹ : ℂ) • (u + Complex.I • T u), ?_, ?_⟩
    · rw [H10, Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hT]
      match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq]; ring1)
    · rw [H01, Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hT]
      match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq]; ring1)
    · module
  set Φ : H1 ℂ n → H1 ℂ n → S ℂ n := fun u v =>
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v +
      ExteriorAlgebra.ι ℂ (T u) * ExteriorAlgebra.ι ℂ (T v) with hΦ
  have hΦl : ∀ u₁ u₂ v, Φ (u₁ + u₂) v = Φ u₁ v + Φ u₂ v := fun u₁ u₂ v => by
    simp only [hΦ, map_add, add_mul]; abel
  have hΦr : ∀ u v₁ v₂, Φ u (v₁ + v₂) = Φ u v₁ + Φ u v₂ := fun u v₁ v₂ => by
    simp only [hΦ, map_add, mul_add]; abel
  have h10 : ∀ a ∈ H10 n J, T a = Complex.I • a := fun a ha => Module.End.mem_eigenspace_iff.mp ha
  have h01 : ∀ a ∈ H01 n J, T a = (-Complex.I) • a := fun a ha =>
    Module.End.mem_eigenspace_iff.mp ha
  have hpp : ∀ a ∈ H10 n J, ∀ b ∈ H10 n J, Φ a b ∈ P := fun a ha b hb => by
    have : Φ a b = 0 := by
      simp only [hΦ, h10 a ha, h10 b hb, map_smul, smul_mul_smul_comm, Complex.I_mul_I, neg_smul,
        one_smul, add_neg_cancel]
    rw [this]
    exact Submodule.zero_mem _
  have hqq : ∀ a ∈ H01 n J, ∀ b ∈ H01 n J, Φ a b ∈ P := fun a ha b hb => by
    have : Φ a b = 0 := by
      simp only [hΦ, h01 a ha, h01 b hb, neg_smul, map_neg, map_smul, neg_mul_neg,
        smul_mul_smul_comm, Complex.I_mul_I, one_smul, add_neg_cancel]
    rw [this]
    exact Submodule.zero_mem _
  have hpq : ∀ a ∈ H10 n J, ∀ b ∈ H01 n J, Φ a b ∈ P := fun a ha b hb => by
    simp only [hΦ, h10 a ha, h01 b hb, neg_smul, map_neg, map_smul, mul_neg, smul_mul_smul_comm,
      Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    exact Submodule.add_mem _ (main_lef_gen_mem_pq11 n J ha hb) (main_lef_gen_mem_pq11 n J ha hb)
  have hqp : ∀ a ∈ H01 n J, ∀ b ∈ H10 n J, Φ a b ∈ P := fun a ha b hb => by
    simp only [hΦ, h01 a ha, h10 b hb, neg_smul, map_neg, map_smul, neg_mul, smul_mul_smul_comm,
      Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (main_lef_gen_mem_pq11 n J hb ha))
      (Submodule.neg_mem _ (main_lef_gen_mem_pq11 n J hb ha))
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    have hz2 : ExteriorAlgebra.ιMulti ℂ 2 w =
        ExteriorAlgebra.ι ℂ (w 0) * ExteriorAlgebra.ι ℂ (w 1) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, main_lef_ιMulti_one]; rfl
    rw [hz2, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    show Φ (w 0) (w 1) ∈ P
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := hdec (w 0)
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := hdec (w 1)
    rw [h₁, h₂, hΦl, hΦr, hΦr]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hpp _ hp₁ _ hp₂) (hpq _ hp₁ _ hq₂))
      (Submodule.add_mem _ (hqp _ hq₁ _ hp₂) (hqq _ hq₁ _ hq₂))
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, add_add_add_comm]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, ← smul_add]; exact Submodule.smul_mem _ c ha

end Complex


/-! ### Ample classes, Hodge classes of degree `2`, and real spans -/

section MainProofs

variable {g : ℕ}

/-- `⟪ξ, a ∧ b⟫ = b(θ_ξ a)` for `ξ` of degree `2`. -/
theorem main_lef_eval2_eq {F : Type*} [Field F] [CharZero F] {ξ : S F g}
    (hξ : ξ ∈ ⋀[F]^2 (H1 F g)) (a b : Module.Dual F (H1 F g)) :
    eval2 F g ξ a b = b (contractOne F g ξ a) := by
  rw [eval2, main_coord_empty, ← ι_contractOne F g ξ hξ a, main_lef_D_ι]
  simp

/-- An ample class is nondegenerate over `ℝ`: `θ_ℝ` is bijective (positivity). -/
theorem main_lef_bijective_real {J : Module.End ℝ (H1 ℝ g)} {h : S ℚ g} (hh : IsAmple g J h) :
    Function.Bijective (contractOne ℝ g (bcS ℚ ℝ g h)) := by
  have h2 : bcS ℚ ℝ g h ∈ ⋀[ℝ]^2 (H1 ℝ g) := main_lef_bcS_mem ℚ ℝ g hh.mem_exteriorPower_two
  have hinj : Function.Injective (contractOne ℝ g (bcS ℚ ℝ g h)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra ha0
    have := hh.2 a ha0
    rw [main_lef_eval2_eq h2, ha, map_zero] at this
    exact lt_irrefl _ this
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mp hinj⟩

/-- `⋀J` fixes (the real image of) every Hodge class. -/
theorem main_lef_map_bcS_of_hodge {J : Module.End ℝ (H1 ℝ g)} {p : ℕ} {β : S ℚ g}
    (hβ : β ∈ hodgeClassesX g J p) :
    ExteriorAlgebra.map J (bcS ℚ ℝ g β) = bcS ℚ ℝ g β := by
  have hC := ((mem_hodgeClassesX_iff g J p β).mp hβ).2
  apply main_lef_bcS_injective ℝ ℂ g
  rw [main_bcS_map, main_lef_bcS_bcS, ← main_lef_complexifyH1_eq]
  exact main_lef_map_pqPiece_pp g J p hC

/-- A rational class of degree `2` whose real image is fixed by `⋀J` is a Hodge class. -/
theorem main_lef_hodge_one_of_map {J : Module.End ℝ (H1 ℝ g)} (hJ : IsComplexStructure J)
    {α : S ℚ g}
    (hα : α ∈ ⋀[ℚ]^2 (H1 ℚ g)) (hfix : ExteriorAlgebra.map J (bcS ℚ ℝ g α) = bcS ℚ ℝ g α) :
    α ∈ hodgeClassesX g J 1 := by
  rw [mem_hodgeClassesX_iff]
  refine ⟨by rw [mul_one]; exact hα, ?_⟩
  have hx2 : bcS ℚ ℂ g α ∈ ⋀[ℂ]^2 (H1 ℂ g) := main_lef_bcS_mem ℚ ℂ g hα
  have hfixC : ExteriorAlgebra.map (complexifyH1 g J) (bcS ℚ ℂ g α) = bcS ℚ ℂ g α := by
    rw [← main_lef_bcS_bcS, main_lef_complexifyH1_eq, ← main_bcS_map, hfix]
  have := main_lef_add_map_mem_pq11 g hJ hx2
  rw [hfixC, ← two_smul ℂ] at this
  have := Submodule.smul_mem _ (2⁻¹ : ℂ) this
  rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at this

/-- The real span of a rational subspace `U` has dimension `dim U`. -/
theorem main_lef_finrank_span_bcH1 (U : Submodule ℚ (H1 ℚ g)) :
    Module.finrank ℝ (Submodule.span ℝ (bcH1 ℚ ℝ g '' U)) = Module.finrank ℚ U := by
  set b := Module.finBasis ℚ U
  set v : Fin (Module.finrank ℚ U) → H1 ℝ g := fun i => bcH1 ℚ ℝ g (b i) with hv
  have hspan : Submodule.span ℝ (bcH1 ℚ ℝ g '' U) = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : H1 ℚ g) := by
        have h' := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
        exact h'.symm
      rw [hu', map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.span_mono (Set.range_subset_iff.mpr fun i => ⟨b i, (b i).2, rfl⟩)
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hli0 : LinearIndependent ℚ (fun j => (b j : H1 ℚ g)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    rw [← Module.forall_dual_apply_eq_zero_iff ℚ (c i)]
    intro φ
    have h1 : ∑ j, φ (c j) • (b j : H1 ℚ g) = 0 := by
      funext k
      have hk := congrFun hc k
      simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
      have := congrArg φ hk
      rw [map_sum, map_zero] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : c j * bcH1 ℚ ℝ g (b j) k = ((b j : H1 ℚ g) k) • c j := by
        simp [bcH1, Rat.smul_def, mul_comm]
      rw [this, map_smul, smul_eq_mul, mul_comm]
    exact Fintype.linearIndependent_iff.mp hli0 _ h1 i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end MainProofs

namespace AbVar

variable {g : ℕ} (A : AbVar g)

/-- Sub-Hodge structures of `H¹(A, ℚ)` have even dimension (their real span carries the complex
structure `J`). -/
theorem even_finrank_of_isHodgeSub (U : Submodule ℚ (H1 ℚ g)) (hU : A.IsHodgeSub U) :
    Even (Module.finrank ℚ U) := by
  rw [← main_lef_finrank_span_bcH1 U]
  set W := Submodule.span ℝ (bcH1 ℚ ℝ g '' U)
  let JW : Module.End ℝ W := A.J.restrict (fun x hx => hU x hx)
  have hJW : JW * JW = -1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := congrArg (fun φ : Module.End ℝ (H1 ℝ g) => φ (x : H1 ℝ g)) A.isComplex
    simpa [JW, LinearMap.restrict_apply] using this
  have hdet : LinearMap.det JW ^ 2 = (-1) ^ Module.finrank ℝ W := by
    rw [sq, ← map_mul, hJW, show (-1 : Module.End ℝ W) = (-1 : ℝ) • LinearMap.id by
      ext; simp, LinearMap.det_smul, LinearMap.det_id, mul_one]
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at hdet
  nlinarith [sq_nonneg (LinearMap.det JW)]

/-- **Poincaré's complete reducibility** (up to isogeny): every sub-Hodge structure of `H¹(A, ℚ)`
has a complement that is a sub-Hodge structure (the orthogonal complement for a polarization). -/
theorem exists_isCompl_isHodgeSub (U : Submodule ℚ (H1 ℚ g)) (hU : A.IsHodgeSub U) :
    ∃ U' : Submodule ℚ (H1 ℚ g), A.IsHodgeSub U' ∧ IsCompl U U' := by
  obtain ⟨Θ, hΘ⟩ := A.polarizable
  have hθ := hΘ.bijective_thetaMap
  have hΘR2 : bcS ℚ ℝ g Θ ∈ ⋀[ℝ]^2 (H1 ℝ g) := main_lef_bcS_mem ℚ ℝ g hΘ.mem_exteriorPower_two
  have hθR := main_lef_bijective_real hΘ
  set U' : Submodule ℚ (H1 ℚ g) := U.dualAnnihilator.map (contractOne ℚ g Θ) with hU'
  set UR := Submodule.span ℝ (bcH1 ℚ ℝ g '' U) with hUR
  have hbc : ∀ (f : Module.Dual ℚ (H1 ℚ g)) (v : H1 ℚ g),
      bcDual ℚ ℝ g f (bcH1 ℚ ℝ g v) = (f v : ℝ) := by
    intro f v
    conv_rhs => rw [← main_lef_sum_e v]
    simp [bcDual, bcH1, map_sum, WeilClasses.f, e, mul_comm]
  have hvan : ∀ f ∈ U.dualAnnihilator, ∀ x ∈ UR, bcDual ℚ ℝ g f x = 0 := by
    intro f hf x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hbc, (Submodule.mem_dualAnnihilator f).mp hf u hu, Rat.cast_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  have hdisj : Disjoint U U' := by
    rw [Submodule.disjoint_def]
    intro x hxU hxU'
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxU'
    have hxR : bcH1 ℚ ℝ g (contractOne ℚ g Θ f) ∈ UR := Submodule.subset_span ⟨_, hxU, rfl⟩
    have hJx := hU _ hxR
    have h0 : eval2 ℝ g (bcS ℚ ℝ g Θ) (bcDual ℚ ℝ g f) (bcDual ℚ ℝ g f ∘ₗ A.J) = 0 := by
      rw [main_lef_eval2_eq hΘR2, LinearMap.comp_apply]
      rw [show contractOne ℝ g (bcS ℚ ℝ g Θ) (bcDual ℚ ℝ g f) =
        bcH1 ℚ ℝ g (contractOne ℚ g Θ f) from thetaExt_bcDual g ℝ Θ f]
      exact hvan f hf _ hJx
    by_cases ha : bcDual ℚ ℝ g f = 0
    · have hf0 : f = 0 := by
        refine LinearMap.ext fun v => ?_
        have := congrArg (fun a => a (bcH1 ℚ ℝ g v)) ha
        simp only [hbc, LinearMap.zero_apply] at this
        exact_mod_cast this
      simp [hf0]
    · exact absurd h0 (ne_of_gt (hΘ.2 _ ha))
  have hfinU' : Module.finrank ℚ U' = Module.finrank ℚ U.dualAnnihilator :=
    (Submodule.equivMapOfInjective _ hθ.1 _).finrank_eq.symm
  have hsum : Module.finrank ℚ U + Module.finrank ℚ U' = 2 * g := by
    rw [hfinU', Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_fin_fun]
  have hcompl : IsCompl U U' :=
    (Submodule.isCompl_iff_disjoint U U' (by rw [hsum, Module.finrank_fin_fun])).mpr hdisj
  refine ⟨U', ?_, hcompl⟩
  set Y : Submodule ℝ (H1 ℝ g) := UR.dualAnnihilator.map (contractOne ℝ g (bcS ℚ ℝ g Θ))
  have hle : Submodule.span ℝ (bcH1 ℚ ℝ g '' U') ≤ Y := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨bcDual ℚ ℝ g f, (Submodule.mem_dualAnnihilator _).mpr (hvan f hf),
      thetaExt_bcDual g ℝ Θ f⟩
  have hfinY : Module.finrank ℝ Y = 2 * g - Module.finrank ℚ U := by
    have e1 : Module.finrank ℝ Y = Module.finrank ℝ UR.dualAnnihilator :=
      (Submodule.equivMapOfInjective _ hθR.1 _).finrank_eq.symm
    have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq UR
    have e3 : Module.finrank ℝ UR = Module.finrank ℚ U := main_lef_finrank_span_bcH1 U
    rw [Module.finrank_fin_fun] at e2
    omega
  have hfinU'R : Module.finrank ℝ (Submodule.span ℝ (bcH1 ℚ ℝ g '' U')) =
      2 * g - Module.finrank ℚ U := by
    rw [main_lef_finrank_span_bcH1]; omega
  have heq : Submodule.span ℝ (bcH1 ℚ ℝ g '' U') = Y :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinU'R, hfinY])
  intro x hx
  rw [heq] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  rw [Submodule.mem_dualAnnihilator] at ha
  refine ⟨-(A.J.dualMap a), (Submodule.mem_dualAnnihilator _).mpr fun w hw => ?_, ?_⟩
  · simp [LinearMap.dualMap_apply, ha _ (hU w hw)]
  · have := LinearMap.congr_fun (thetaExt_comp_neg_dualMap g A.J A.isComplex Θ hΘ.1) a
    simpa using this

/-- **Hard Lefschetz** for abelian varieties, degree `2` to degree `2g - 2`: for an ample class `h`,
every Hodge class of degree `2g - 2` is `h^{g-2} ∪ β` for a Hodge class `β` of degree `2`
(`2 ≤ g`). -/
theorem hodge_pred_le_map (hg : 2 ≤ g) (h : S ℚ g) (hh : IsAmple g A.J h) :
    A.hodge (g - 1) ≤ (A.hodge 1).map (LinearMap.mulLeft ℚ (h ^ (g - 2))) := by
  intro β hβ
  have hh2 := hh.mem_exteriorPower_two
  have hβ2 : β ∈ ⋀[ℚ]^(2 * (g - 1)) (H1 ℚ g) := (Submodule.mem_inf.mp hβ).1
  have hdeg : 2 * (g - 2) + 2 = 2 * (g - 1) := by omega
  have hmem : ∀ x ∈ ⋀[ℚ]^2 (H1 ℚ g), h ^ (g - 2) * x ∈ ⋀[ℚ]^(2 * (g - 1)) (H1 ℚ g) :=
    fun x hx => by rw [← hdeg]; exact main_mul_mem (main_pow_mem hh2 (g - 2)) hx
  let L : ⋀[ℚ]^2 (H1 ℚ g) →ₗ[ℚ] ⋀[ℚ]^(2 * (g - 1)) (H1 ℚ g) :=
    ((LinearMap.mulLeft ℚ (h ^ (g - 2))).domRestrict _).codRestrict _ (fun x => hmem x.1 x.2)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : h ^ (g - 2) * (x : S ℚ g) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (main_lef_injective h hh.bijective_thetaMap hh2 2 (g - 2) (by omega) x x.2 h0)
  have hfin : Module.finrank ℚ (⋀[ℚ]^2 (H1 ℚ g)) =
      Module.finrank ℚ (⋀[ℚ]^(2 * (g - 1)) (H1 ℚ g)) := by
    rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, Module.finrank_fin_fun,
      show 2 * (g - 1) = 2 * g - 2 by omega, Nat.choose_symm (by omega)]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  obtain ⟨⟨α, hα2⟩, hα⟩ := hsurj ⟨β, hβ2⟩
  have hαβ : h ^ (g - 2) * α = β := congrArg Subtype.val hα
  refine ⟨α, ?_, hαβ⟩
  apply main_lef_hodge_one_of_map A.isComplex hα2
  have hR2 : bcS ℚ ℝ g h ∈ ⋀[ℝ]^2 (H1 ℝ g) := main_lef_bcS_mem ℚ ℝ g hh2
  have hJh : ExteriorAlgebra.map A.J (bcS ℚ ℝ g h) = bcS ℚ ℝ g h := main_lef_map_bcS_of_hodge hh.1
  have hJβ : ExteriorAlgebra.map A.J (bcS ℚ ℝ g β) = bcS ℚ ℝ g β := main_lef_map_bcS_of_hodge hβ
  have hβR : bcS ℚ ℝ g β = bcS ℚ ℝ g h ^ (g - 2) * bcS ℚ ℝ g α := by
    rw [← hαβ, map_mul, map_pow]
  rw [hβR, map_mul, map_pow, hJh] at hJβ
  have hdiff : bcS ℚ ℝ g h ^ (g - 2) *
      (ExteriorAlgebra.map A.J (bcS ℚ ℝ g α) - bcS ℚ ℝ g α) = 0 := by
    rw [mul_sub, hJβ, sub_self]
  have hmemd : ExteriorAlgebra.map A.J (bcS ℚ ℝ g α) - bcS ℚ ℝ g α ∈ ⋀[ℝ]^2 (H1 ℝ g) :=
    Submodule.sub_mem _ (main_map_mem_exteriorPower _ 2 (main_lef_bcS_mem ℚ ℝ g hα2))
      (main_lef_bcS_mem ℚ ℝ g hα2)
  exact sub_eq_zero.mp
    (main_lef_injective _ (main_lef_bijective_real hh) hR2 2 (g - 2) (by omega) _ hmemd hdiff)

/-- The top degree `H^{2g}(A, ℚ)` is the line spanned by `h^g`, for an ample class `h`. -/
theorem top_eq_span_pow (h : S ℚ g) (hh : IsAmple g A.J h) :
    ⋀[ℚ]^(2 * g) (H1 ℚ g) = Submodule.span ℚ {h ^ g} := by
  have hh2 := hh.mem_exteriorPower_two
  have hpow : h ^ g ∈ ⋀[ℚ]^(2 * g) (H1 ℚ g) := main_pow_mem hh2 g
  have hne : h ^ g ≠ 0 := by
    intro h0
    have h1 : (1 : S ℚ g) ∈ ⋀[ℚ]^0 (H1 ℚ g) := by
      rw [ExteriorAlgebra.exteriorPower, pow_zero]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := main_lef_injective h hh.bijective_thetaMap hh2 0 g (by omega) 1 h1 (by rw [mul_one, h0])
    have h2 := congrArg ExteriorAlgebra.algebraMapInv this
    simp at h2
  symm
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hpow) ?_
  rw [finrank_span_singleton hne, exteriorPower.finrank_eq, Module.finrank_fin_fun, Nat.choose_self]

/-- Hodge classes live in degrees `0, …, 2g`: `H^{p,p}(A, ℚ) = 0` for `p > g`. -/
theorem hodge_eq_bot_of_lt (p : ℕ) (hp : g < p) : A.hodge p = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' : x ∈ ⋀[ℚ]^(2 * p) (H1 ℚ g) := (Submodule.mem_inf.mp hx).1
  have := exteriorPower.eq_zero_of_finrank_lt (R := ℚ) (M := H1 ℚ g) (2 * p)
    (by rw [Module.finrank_fin_fun]; omega) ⟨x, hx'⟩
  exact (Submodule.mem_bot ℚ).mpr (congrArg Subtype.val this)

end AbVar

end WeilClasses
