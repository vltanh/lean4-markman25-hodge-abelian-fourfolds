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

/-- Change of coefficients on `H¹(X, ·)`. -/
noncomputable def bcH1 : H1 F n →ₗ[F] H1 F' n := (Algebra.linearMap F F').compLeft _

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
  sorry

/-- Change of coefficients on `S = ⋀• H¹(X)`, an `F`-algebra homomorphism. -/
noncomputable def bcS : S F n →ₐ[F] S F' n :=
  ExteriorAlgebra.lift F
    ⟨((ExteriorAlgebra.ι F' : H1 F' n →ₗ[F'] S F' n).restrictScalars F) ∘ₗ bcH1 F F' n,
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

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

theorem bcC_mem_spinGroup (g : Spin F n) : bcC F F' n g ∈ spinGroup (Q F' n) := by
  sorry

/-- Change of coefficients on the spin group, `Spin(V_F) → Spin(V_{F'})`. -/
noncomputable def bcSpin : Spin F n →* Spin F' n where
  toFun g := ⟨bcC F F' n g, bcC_mem_spinGroup F F' n g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

end BaseChange

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
  sorry

theorem conjS_map_mul (s t : S F n) :
    ∑ K, c ((basisS F n).repr (s * t) K) • basisS F n K =
      (∑ K, c ((basisS F n).repr s K) • basisS F n K) *
        ∑ K, c ((basisS F n).repr t K) • basisS F n K := by
  sorry

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
  sorry

theorem conjExt_map_mul (s t : ExteriorAlgebra F (V F n)) :
    ∑ K, c ((basisExt F n).repr (s * t) K) • basisExt F n K =
      (∑ K, c ((basisExt F n).repr s K) • basisExt F n K) *
        ∑ K, c ((basisExt F n).repr t K) • basisExt F n K := by
  sorry

/-- The `c`-semilinear ring automorphism of `⋀• V_F` acting on coefficients in `basisExt`. -/
noncomputable def conjExt : ExteriorAlgebra F (V F n) →+* ExteriorAlgebra F (V F n) where
  toFun s := ∑ K, c ((basisExt F n).repr s K) • basisExt F n K
  map_one' := conjExt_map_one c n
  map_mul' := conjExt_map_mul c n
  map_zero' := by simp
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]

end Conj

end WeilClasses
