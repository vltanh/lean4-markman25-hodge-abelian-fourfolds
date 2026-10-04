module

public import WeilClasses.Spinor.Defs

/-!
# Change of coefficients for `V`, `S`, `C(V)` and `⋀• V`

The paper moves freely between coefficients `ℚ ⊆ K ⊆ ℂ` and `ℚ ⊆ ℝ ⊆ ℂ` (writing `V_K := V ⊗ K`
and so on), and uses the Galois involution `σ` of `K/ℚ` and complex conjugation. In the coordinates
of `WeilClasses.Spinor.Defs` these are coordinatewise maps:

* for an algebra `F → F'`: `bcH1`, `bcDual`, `bcV`, and the induced `F`-algebra homomorphisms
  `bcS : S_F → S_{F'}`, `bcC : C(V_F) → C(V_{F'})`, `bcExt : ⋀•V_F → ⋀•V_{F'}`;
* for a ring automorphism `c` of `F` (such as `σ` or complex conjugation), the `c`-semilinear
  automorphisms `conjH1`, `conjV`, `conjS`, `conjExt`, defined coordinatewise in the standard bases.

A vector or subspace "defined over `F`" is one in the image of these maps.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section BaseChange

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

/-- Change of coefficients on `H¹(X̂, ·) = H¹(X, ·)*`: the functional with the same coordinates. -/
noncomputable def bcDual : Module.Dual F (H1 F n) →ₗ[F] Module.Dual F' (H1 F' n) where
  toFun θ := ∑ i, algebraMap F F' (θ (e F n i)) • f F' n i
  map_add' θ θ' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c θ := by
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, algebraMap_smul]

/-- Change of coefficients on `V = H¹(X̂) ⊕ H¹(X)`. -/
noncomputable def bcV : V F n →ₗ[F] V F' n := (bcDual F F' n).prodMap (bcH1 F F' n)

theorem Q_bcV (v : V F n) : Q F' n (bcV F F' n v) = algebraMap F F' (Q F n v) := by
  obtain ⟨θ, w⟩ := v
  have hw : w = ∑ i, w i • e F n i := by
    ext j
    simp [e, Pi.single_apply]
  simp only [Q, QuadraticForm.dualProd_apply, bcV, LinearMap.prodMap_apply, bcDual,
    LinearMap.coe_mk, AddHom.coe_mk]
  conv_rhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, f, bcH1, e]
  simp [Algebra.smul_def, mul_comm]

/-- Change of coefficients on the Clifford algebra, an `F`-algebra homomorphism. -/
noncomputable def bcC : C F n →ₐ[F] C F' n :=
  CliffordAlgebra.lift (Q F n)
    ⟨((CliffordAlgebra.ι (Q F' n)).restrictScalars F) ∘ₗ bcV F F' n, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        CliffordAlgebra.ι_sq_scalar, Q_bcV]
      rw [← IsScalarTower.algebraMap_apply]⟩

/-- Change of coefficients on `⋀• V = H*(X × X̂)`, an `F`-algebra homomorphism. -/
noncomputable def bcExt : ExteriorAlgebra F (V F n) →ₐ[F] ExteriorAlgebra F' (V F' n) :=
  ExteriorAlgebra.lift F
    ⟨((ExteriorAlgebra.ι F' : V F' n →ₗ[F'] ExteriorAlgebra F' (V F' n)).restrictScalars F) ∘ₗ
        bcV F F' n,
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

/-- `bcC` sends `ι v` to `ι (bcV v)`. -/
theorem fnd_bcC_ι (v : V F n) : bcC F F' n (ι (Q F n) v) = ι (Q F' n) (bcV F F' n v) := by
  simp [bcC]

/-- `bcC` commutes with the conjugation `x ↦ x*` of `C(V)`. -/
theorem fnd_bcC_star (x : C F n) : bcC F F' n (star x) = star (bcC F F' n x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [star_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n),
        star_algebraMap]
  | ι m => simp [fnd_bcC_ι, star_ι]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

/-- `bcC` sends `C(V_F)^even` into `C(V_{F'})^even`. -/
private theorem fnd_bcC_mem_even {x : C F n} (hx : x ∈ even (Q F n)) :
    bcC F F' n x ∈ even (Q F' n) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (C F' n)]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
      simpa only [map_mul, fnd_bcC_ι, zero_add] using
        SetLike.mul_mem_graded
          (ι_mul_ι_mem_evenOdd_zero (Q F' n) (bcV F F' n m₁) (bcV F F' n m₂)) hx

/-- `bcC` maps the Lipschitz group of `V_F` into that of `V_{F'}` (it sends vectors to vectors). -/
private theorem fnd_bcC_mem_lipschitzGroup {x : (C F n)ˣ} (hx : x ∈ lipschitzGroup (Q F n)) :
    Units.map (bcC F F' n).toRingHom.toMonoidHom x ∈ lipschitzGroup (Q F' n) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hx
      change ↑(Units.map (bcC F F' n).toRingHom.toMonoidHom x) ∈ Set.range (ι (Q F' n))
      refine ⟨bcV F F' n m, ?_⟩
      rw [Units.coe_map, ← fnd_bcC_ι, hm]
      rfl
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

theorem bcC_mem_spinGroup (g : Spin F n) : bcC F F' n g ∈ spinGroup (Q F' n) := by
  rw [spinGroup.mem_iff, pinGroup.mem_iff]
  refine ⟨⟨?_, ?_⟩, fnd_bcC_mem_even F F' n (spinGroup.mem_even g.2)⟩
  · have hx := spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits g) g.2
    exact ⟨_, fnd_bcC_mem_lipschitzGroup F F' n hx, rfl⟩
  · rw [Unitary.mem_iff]
    constructor
    · rw [← fnd_bcC_star, ← map_mul, spinGroup.star_mul_self_of_mem g.2, map_one]
    · rw [← fnd_bcC_star, ← map_mul, spinGroup.mul_star_self_of_mem g.2, map_one]

/-- Change of coefficients on the spin group, `Spin(V_F) → Spin(V_{F'})`. -/
noncomputable def bcSpin : Spin F n →* Spin F' n where
  toFun g := ⟨bcC F F' n g, bcC_mem_spinGroup F F' n g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

end BaseChange

/-- The `c`-semilinear additive map `s ↦ Σ_K c(s_K) b_K` of `⋀• M`, acting on the coefficients in
the basis `b_K` of `⋀• M` induced by a basis `b` of `M`. -/
private noncomputable def fnd_conjAux {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*}
    [LinearOrder I] [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) :
    ExteriorAlgebra F M →+ ExteriorAlgebra F M where
  toFun s := ∑ K, c (b.ExteriorAlgebra.repr s K) • b.ExteriorAlgebra K
  map_zero' := by simp
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]

private theorem fnd_conjAux_apply {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) (s : ExteriorAlgebra F M) :
    fnd_conjAux c b s = ∑ K, c (b.ExteriorAlgebra.repr s K) • b.ExteriorAlgebra K := rfl

private theorem fnd_conjAux_smul {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) (a : F)
    (s : ExteriorAlgebra F M) : fnd_conjAux c b (a • s) = c a • fnd_conjAux c b s := by
  simp [fnd_conjAux_apply, Finset.smul_sum, smul_smul]

private theorem fnd_conjAux_basis {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) (K : Finset I) :
    fnd_conjAux c b (b.ExteriorAlgebra K) = b.ExteriorAlgebra K := by
  rw [fnd_conjAux_apply, Module.Basis.repr_self, Finset.sum_eq_single K]
  · simp
  · intro L _ hL
    simp [Ne.symm hL]
  · simp

/-- The products of two basis vectors `b_K b_L` (`0` or `±b_{K ∪ L}`) have integral coefficients,
so the coefficientwise map fixes them. -/
private theorem fnd_conjAux_basis_mul_basis {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*}
    [LinearOrder I] [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M)
    (K L : Finset I) :
    fnd_conjAux c b (b.ExteriorAlgebra K * b.ExteriorAlgebra L) =
      b.ExteriorAlgebra K * b.ExteriorAlgebra L := by
  by_cases h : Disjoint K L
  · have hKL := ExteriorAlgebra.basis_mul_of_disjoint b
      (Set.powersetCard.ofCard (rfl : K.card = K.card))
      (Set.powersetCard.ofCard (rfl : L.card = L.card)) h
    simp only [Set.powersetCard.val_ofCard] at hKL
    rw [hKL, Units.smul_def, map_zsmul, fnd_conjAux_basis]
  · have hKL := ExteriorAlgebra.basis_mul_of_not_disjoint b
      (Set.powersetCard.ofCard (rfl : K.card = K.card))
      (Set.powersetCard.ofCard (rfl : L.card = L.card)) h
    simp only [Set.powersetCard.val_ofCard] at hKL
    rw [hKL, map_zero]

private theorem fnd_sum_smul_mul_sum_smul {F : Type*} [Field F] {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) (α β : Finset I → F) :
    (∑ K, α K • b.ExteriorAlgebra K) * (∑ L, β L • b.ExteriorAlgebra L) =
      ∑ K, ∑ L, (α K * β L) • (b.ExteriorAlgebra K * b.ExteriorAlgebra L) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
  rw [smul_mul_smul_comm]

private theorem fnd_conjAux_mul {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) (s t : ExteriorAlgebra F M) :
    fnd_conjAux c b (s * t) = fnd_conjAux c b s * fnd_conjAux c b t := by
  conv_lhs => rw [← b.ExteriorAlgebra.sum_repr s, ← b.ExteriorAlgebra.sum_repr t]
  rw [fnd_sum_smul_mul_sum_smul, fnd_conjAux_apply c b s, fnd_conjAux_apply c b t,
    fnd_sum_smul_mul_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [fnd_conjAux_smul, fnd_conjAux_basis_mul_basis, map_mul]

private theorem fnd_conjAux_one {F : Type*} [Field F] (c : F ≃+* F) {I M : Type*} [LinearOrder I]
    [Fintype I] [AddCommGroup M] [Module F M] (b : Module.Basis I F M) :
    fnd_conjAux c b 1 = 1 := by
  have h1 : b.ExteriorAlgebra ∅ = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  rw [← h1, fnd_conjAux_basis]

section Conj

variable {F : Type*} [Field F] [CharZero F] (c : F ≃+* F) (n : ℕ)

/-- The `c`-semilinear automorphism of `H¹(X, F)` acting on coordinates. -/
noncomputable def conjH1 : H1 F n →+ H1 F n where
  toFun w := c ∘ w
  map_zero' := by ext; simp
  map_add' w w' := by ext; simp

/-- The `c`-semilinear automorphism of `V_F` acting on coordinates. -/
noncomputable def conjV : V F n →+ V F n where
  toFun v := (∑ i, c (v.1 (e F n i)) • f F n i, c ∘ v.2)
  map_zero' := by ext <;> simp
  map_add' v v' := by ext <;> simp [Finset.sum_add_distrib, add_smul]

theorem conjS_map_one :
    ∑ K, c ((basisS F n).repr 1 K) • basisS F n K = 1 := by
  exact fnd_conjAux_one c (Pi.basisFun F (Fin (2 * n)))

theorem conjS_map_mul (s t : S F n) :
    ∑ K, c ((basisS F n).repr (s * t) K) • basisS F n K =
      (∑ K, c ((basisS F n).repr s K) • basisS F n K) *
        ∑ K, c ((basisS F n).repr t K) • basisS F n K := by
  exact fnd_conjAux_mul c (Pi.basisFun F (Fin (2 * n))) s t

/-- The `c`-semilinear ring automorphism of `S_F` acting on the coefficients of the basis `e_K`
(for `c = σ`, the conjugation `S_K → S_K` of §2.2; for complex conjugation, `s ↦ s̄`). -/
noncomputable def conjS : S F n →+* S F n where
  toFun s := ∑ K, c ((basisS F n).repr s K) • basisS F n K
  map_one' := conjS_map_one c n
  map_mul' := conjS_map_mul c n
  map_zero' := by simp
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]

theorem conjExt_map_one :
    ∑ K, c ((basisExt F n).repr 1 K) • basisExt F n K = 1 := by
  exact fnd_conjAux_one c (basisV F n)

theorem conjExt_map_mul (s t : ExteriorAlgebra F (V F n)) :
    ∑ K, c ((basisExt F n).repr (s * t) K) • basisExt F n K =
      (∑ K, c ((basisExt F n).repr s K) • basisExt F n K) *
        ∑ K, c ((basisExt F n).repr t K) • basisExt F n K := by
  exact fnd_conjAux_mul c (basisV F n) s t

/-- The `c`-semilinear ring automorphism of `⋀• V_F` acting on coefficients in `basisExt`. -/
noncomputable def conjExt : ExteriorAlgebra F (V F n) →+* ExteriorAlgebra F (V F n) where
  toFun s := ∑ K, c ((basisExt F n).repr s K) • basisExt F n K
  map_one' := conjExt_map_one c n
  map_mul' := conjExt_map_mul c n
  map_zero' := by simp
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]

end Conj

end WeilClasses
