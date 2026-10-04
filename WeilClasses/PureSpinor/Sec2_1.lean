module

public import WeilClasses.Spinor.Integral
public import WeilClasses.External.GolyshevLuntsOrlov.Sec2_1

/-!
# The Clifford algebra and the spin group (paper §2.1)

The paper's §2.1 recalls the Clifford algebra `C(V)` (relation (2.1.1)), the spin representation
`m : C(V) → End(S)` ((2.1.2)–(2.1.3)), the main anti-automorphism `τ`, the main involution `α`, the
conjugation `x* = τ(α(x))`, the integral Clifford group `G(V)`, the integral spin group
`Spin(V)`, the standard representation `ρ(x)(v) = x v x⁻¹`, the norm character `N(g) = g τ(g)`, and
a list of facts. Everything is then repeated over a field `K` ("the same definitions above
yield ...").

The objects `C(V_F)`, `m`, `τ`, `S^±`, the Mukai pairing, `Spin(V_F)` (Mathlib's `spinGroup`),
`ρ` on `Spin(V_F)`, and the integral `C(V)` (`CZ`) and `Spin(V)` (`SpinZ`) are in
`WeilClasses.Spinor.Defs` and `WeilClasses.Spinor.Integral`. In Mathlib's language `τ` is
`CliffordAlgebra.reverse`, `α` is `CliffordAlgebra.involute`, and `x* = τ(α(x))` is `star x`.

## Main definitions

* `WeilClasses.mEquiv`: the isomorphism (2.1.3) `m : C(V_F) ≅ End(S_F)` over a field
  ([GLO, Prop. 3.2.1(e)], `WeilClasses.glo_prop3_2_1_e_field`).
* `WeilClasses.cliffordGroup F n`: the Clifford group `G(V_F) = {x ∈ C(V_F)ˣ : x V x⁻¹ ⊆ V}`
  (untwisted, as in the paper).
* `WeilClasses.cliffordGroupZ n`: the integral Clifford group `G(V) = {x ∈ C(V)ˣ : x V x⁻¹ ⊆ V}`,
  inside `C(V_ℚ)ˣ`.

## Statements (claims of §2.1)

* `m_ι_injective`, `m_ι_mul_add_mul_swap`: `m : V → End(S)` is an embedding (2.1.2) satisfying the
  analogue of the Clifford relation (2.1.1); `pairing_eq_of_conj_ι`: `ρ : G(V) → O(V)`.
* `mem_spin_iff`, `mem_SpinZ_iff`: the paper's definitions of `Spin(V_F)` and of the integral
  `Spin(V)` agree with the model (`spinGroup`, `SpinZ`).
* `exists_mul_reverse_eq_algebraMap`, `mul_reverse_eq_one_or_neg_one_of_mem_cliffordGroupZ`: the
  norm `N(g) = g τ(g)` is a scalar on `G(V_F)`, and is `±1` on the integral `G(V)`.
* `spinZ_relIndex_cliffordGroupZ`: `Spin(V)` has index four in `G(V)`.
* `exists_unit_ι_mem_cliffordGroup`, `neg_conj_ι_eq_reflection`: for `(v,v)_V = ±2`, `v ∈ G(V)`
  and `-ρ(v)` is the reflection in `v^⊥`.
* `exists_spinZ_eq_ι_mul_ι`, `spinZ_eq_closure`: `v₁ v₂ ∈ Spin(V)` when
  `(v₁,v₁)_V = (v₂,v₂)_V = ±2`, and these elements generate `Spin(V)`.
* `m_mem_Sminus_of_odd`, `m_mem_Splus_of_odd`: odd elements of `C(V)` swap `S⁺` and `S⁻`;
  `m_ι_rho_m`: the maps `V ⊗ S^± → S^∓` are `Spin(V)`-equivariant.
* `ι_mul_reverse_ι_of_pairing_eq_two`, `mukai_m_ι_m_ι_of_pairing_eq_two`,
  `m_ι_mul_m_ι_of_pairing_eq_two`, `m_ι_mem_Sminus_of_pairing_eq_two`,
  `m_ι_mem_Splus_of_pairing_eq_two`, `exists_mem_cliffordGroupZ_of_pairing_eq_two`: for
  `(v,v)_V = 2`: `v ∈ G(V)`, `N(v) = 1`, `m_v` is an isometry of `(·,·)_S` interchanging `S⁺` and
  `S⁻`, and `m_v² = 1`.

The cited facts `(m_v s, t)_S = (s, m_v t)_S` [Chevalley, III.2.2] and
`(g s, g t)_S = N(g)(s,t)_S` [Chevalley, III.2.1] are in `WeilClasses.External.Chevalley.Sec2_1`;
the isomorphism `m` over `ℤ` and over a field [GLO, Prop. 3.2.1(e)] is in
`WeilClasses.External.GolyshevLuntsOrlov.Sec2_1`.

Facts stated over a field `F` of characteristic zero imply the paper's integral statements, since
`C(V) ⊆ C(V_ℚ)`; the paper itself repeats them over fields at the end of §2.1.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section Field

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The isomorphism (2.1.3) `m : C(V_F) ≅ End(S_F)` over a field, extending
`m_{(θ, w)} = L_w + D_θ` ([GLO, Prop. 3.2.1(e)]; end of §2.1 for `V_K`). -/
noncomputable def mEquiv : C F n ≃ₐ[F] Module.End F (S F n) :=
  AlgEquiv.ofBijective (m F n) (glo_prop3_2_1_e_field F n)

theorem mEquiv_apply (x : C F n) : mEquiv F n x = m F n x :=
  congrFun (AlgEquiv.coe_ofBijective _ _) x

/-- "**We get the embedding `m : V → End(S)`**" (2.1.2): `v ↦ m_v` is injective. -/
theorem m_ι_injective : Function.Injective fun v : V F n => m F n (ι (Q F n) v) := by
  sorry

/-- The analogue `m_{v₁} ∘ m_{v₂} + m_{v₂} ∘ m_{v₁} = (v₁, v₂)_V · id_S` of the Clifford relation
(2.1.1) (§2.1). -/
theorem m_ι_mul_add_mul_swap (v₁ v₂ : V F n) :
    m F n (ι (Q F n) v₁) * m F n (ι (Q F n) v₂) + m F n (ι (Q F n) v₂) * m F n (ι (Q F n) v₁) =
      algebraMap F (Module.End F (S F n)) (pairing F n v₁ v₂) := by
  sorry

/-- **The spin group over a field** (§2.1, end): the paper's
`Spin(V_F) = {x ∈ C(V_F)^even : x x* = 1, x V_F x* ⊆ V_F}` is Mathlib's `spinGroup (Q F n)`
(Tau Ceti: `CliffordAlgebra.mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι`). Here
`x* = τ(α(x))` is `star x`. For `n = 0` the two differ (`spinGroup` of the zero form is `{1}`),
hence `0 < n`. This is the bridge referred to as `WeilClasses.mem_spin_iff` in
`WeilClasses.Spinor.Defs`. -/
theorem mem_spin_iff (hn : 0 < n) (x : C F n) :
    x ∈ spinGroup (Q F n) ↔
      x ∈ evenOdd (Q F n) 0 ∧ x * star x = 1 ∧
        ∀ v : V F n, ∃ u : V F n, x * ι (Q F n) v * star x = ι (Q F n) u := by
  sorry

/-- The Clifford group `G(V_F) = {x ∈ C(V_F)ˣ : x V_F x⁻¹ ⊆ V_F}` of §2.1 (the untwisted Clifford
group, the paper's convention), as a subgroup of the units of `C(V_F)`. -/
def cliffordGroup : Subgroup (C F n)ˣ where
  carrier := {x | ∀ v : V F n, ∃ u : V F n,
    (x : C F n) * ι (Q F n) v * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u}
  one_mem' := fun v => ⟨v, by simp⟩
  mul_mem' := by
    intro x y hx hy v
    obtain ⟨u, hu⟩ := hy v
    obtain ⟨u', hu'⟩ := hx u
    refine ⟨u', ?_⟩
    rw [← hu', ← hu]
    simp only [mul_inv_rev, Units.val_mul, mul_assoc]
  inv_mem' := by sorry

/-- **The standard representation `ρ : G(V_F) → O(V_F)`**, `ρ(x)(v) = x v x⁻¹` (§2.1), takes values
in the orthogonal group: if `x v₁ x⁻¹ = u₁` and `x v₂ x⁻¹ = u₂` in `C(V_F)`, then
`(u₁, u₂)_V = (v₁, v₂)_V`. -/
theorem pairing_eq_of_conj_ι (x : (C F n)ˣ) (v₁ v₂ u₁ u₂ : V F n)
    (h₁ : (x : C F n) * ι (Q F n) v₁ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₁)
    (h₂ : (x : C F n) * ι (Q F n) v₂ * ((x⁻¹ : (C F n)ˣ) : C F n) = ι (Q F n) u₂) :
    pairing F n u₁ u₂ = pairing F n v₁ v₂ := by
  sorry

/-- The norm character `N(g) = g τ(g)` (§2.1) takes scalar values on the Clifford group: for
`g ∈ G(V_F)`, `g τ(g)` is a scalar. -/
theorem exists_mul_reverse_eq_algebraMap (x : (C F n)ˣ) (hx : x ∈ cliffordGroup F n) :
    ∃ c : F, (x : C F n) * reverse (x : C F n) = algebraMap F (C F n) c := by
  sorry

/-- If `(v, v)_V = ±2`, then `v` is invertible in `C(V_F)` and belongs to the Clifford group
`G(V_F)` (§2.1; implicit in "`-ρ(v)` is the reflection"). -/
theorem exists_unit_ι_mem_cliffordGroup (v : V F n)
    (hv : pairing F n v v = 2 ∨ pairing F n v v = -2) :
    ∃ x : (C F n)ˣ, (x : C F n) = ι (Q F n) v ∧ x ∈ cliffordGroup F n := by
  sorry

/-- **`-ρ(v)` is a reflection** (§2.1): if `(v, v)_V = ±2`, then
`-ρ(v)(λ) = λ - 2 (λ, v)_V / (v, v)_V · v` for all `λ ∈ V`, where `ρ(v)(λ) = v λ v⁻¹` is the
standard (untwisted) representation of the Clifford group. Here `x` is `v` as a unit of `C(V_F)`. -/
theorem neg_conj_ι_eq_reflection (v : V F n)
    (hv : pairing F n v v = 2 ∨ pairing F n v v = -2)
    (x : (C F n)ˣ) (hx : (x : C F n) = ι (Q F n) v) (l : V F n) :
    -((x : C F n) * ι (Q F n) l * ((x⁻¹ : (C F n)ˣ) : C F n)) =
      ι (Q F n) (l - (2 * pairing F n l v / pairing F n v v) • v) := by
  sorry

/-- **Odd elements swap the half-spin representations** (§2.1): an element `x ∈ C(V)^odd` maps `S⁺`
to `S⁻` under `m`. -/
theorem m_mem_Sminus_of_odd (x : C F n) (hx : x ∈ evenOdd (Q F n) 1) (s : S F n)
    (hs : s ∈ Splus F n) : m F n x s ∈ Sminus F n := by
  sorry

/-- **Odd elements swap the half-spin representations** (§2.1): an element `x ∈ C(V)^odd` maps `S⁻`
to `S⁺` under `m`. -/
theorem m_mem_Splus_of_odd (x : C F n) (hx : x ∈ evenOdd (Q F n) 1) (s : S F n)
    (hs : s ∈ Sminus F n) : m F n x s ∈ Splus F n := by
  sorry

/-- The homomorphisms `V ⊗ S⁺ → S⁻` and `V ⊗ S⁻ → S⁺`, `v ⊗ s ↦ m_v(s)`, are
`Spin(V)`-equivariant (§2.1): `m_{ρ(g)v}(g s) = g (m_v s)`. -/
theorem m_ι_rho_m (g : Spin F n) (v : V F n) (s : S F n) :
    m F n (ι (Q F n) (rho F n g v)) (m F n (g : C F n) s) =
      m F n (g : C F n) (m F n (ι (Q F n) v) s) := by
  sorry

/-- If `(v, v)_V = 2` then `N(v) = v τ(v) = 1` (§2.1). -/
theorem ι_mul_reverse_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) :
    ι (Q F n) v * reverse (ι (Q F n) v) = 1 := by
  sorry

/-- If `(v, v)_V = 2` then `m_v : S → S` is an isometry of the Mukai pairing (§2.1). -/
theorem mukai_m_ι_m_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s t : S F n) :
    mukai F n (m F n (ι (Q F n) v) s) (m F n (ι (Q F n) v) t) = mukai F n s t := by
  sorry

/-- If `(v, v)_V = 2` then `m_v² = 1_S` (§2.1). -/
theorem m_ι_mul_m_ι_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) :
    m F n (ι (Q F n) v) * m F n (ι (Q F n) v) = 1 := by
  sorry

/-- If `(v, v)_V = 2` then `m_v` maps `S⁺` to `S⁻` (§2.1). -/
theorem m_ι_mem_Sminus_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s : S F n)
    (hs : s ∈ Splus F n) : m F n (ι (Q F n) v) s ∈ Sminus F n := by
  sorry

/-- If `(v, v)_V = 2` then `m_v` maps `S⁻` to `S⁺` (§2.1). -/
theorem m_ι_mem_Splus_of_pairing_eq_two (v : V F n) (hv : pairing F n v v = 2) (s : S F n)
    (hs : s ∈ Sminus F n) : m F n (ι (Q F n) v) s ∈ Splus F n := by
  sorry

end Field

section Integral

variable (n : ℕ)

/-- **The integral spin group** (§2.1): the paper's
`Spin(V) = {x ∈ C(V)^even : x x* = 1, x V x* ⊆ V}` is the model's `SpinZ n` (elements of
`Spin(V_ℚ)` lying in `CZ n` and preserving the lattice `VZ n`). For `n = 0` the model's `Spin(V_ℚ)`
is `{1}`, hence `0 < n`. -/
theorem mem_SpinZ_iff (hn : 0 < n) (x : C ℚ n) :
    (∃ g ∈ SpinZ n, (g : C ℚ n) = x) ↔
      x ∈ CZ n ∧ x ∈ evenOdd (Q ℚ n) 0 ∧ x * star x = 1 ∧
        ∀ v ∈ VZ n, ∃ u ∈ VZ n, x * ι (Q ℚ n) v * star x = ι (Q ℚ n) u := by
  sorry

/-- The integral Clifford group `G(V) = {x ∈ C(V)ˣ : x V x⁻¹ ⊆ V}` of §2.1, inside `C(V_ℚ)ˣ`: the
units `x` of `C(V_ℚ)` with `x, x⁻¹ ∈ C(V)` (`CZ n`) and `x V x⁻¹ ⊆ V` (`VZ n`). -/
noncomputable def cliffordGroupZ : Subgroup (C ℚ n)ˣ where
  carrier := {x | (x : C ℚ n) ∈ CZ n ∧ ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) ∈ CZ n ∧
    ∀ v ∈ VZ n, ∃ u ∈ VZ n, (x : C ℚ n) * ι (Q ℚ n) v * ((x⁻¹ : (C ℚ n)ˣ) : C ℚ n) = ι (Q ℚ n) u}
  one_mem' := ⟨Subring.one_mem _, by simp, fun v hv => ⟨v, hv, by simp⟩⟩
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- **The norm character `N : G(V) → {±1}`** (§2.1): for `g` in the integral Clifford group,
`N(g) = g τ(g) = ±1`. -/
theorem mul_reverse_eq_one_or_neg_one_of_mem_cliffordGroupZ (x : (C ℚ n)ˣ)
    (hx : x ∈ cliffordGroupZ n) :
    (x : C ℚ n) * reverse (x : C ℚ n) = 1 ∨ (x : C ℚ n) * reverse (x : C ℚ n) = -1 := by
  sorry

/-- "**The integral spin group is its index four subgroup**" (§2.1): `Spin(V)` (embedded in
`C(V_ℚ)ˣ`) has index `4` in `G(V)`. For `n = 0` there are no vectors with `(v, v)_V = ±2` and the
index is `1`, hence `0 < n`. -/
theorem spinZ_relIndex_cliffordGroupZ (hn : 0 < n) :
    ((SpinZ n).map (spinGroup.toUnits (Q := Q ℚ n))).relIndex (cliffordGroupZ n) = 4 := by
  sorry

/-- If `v ∈ V` (integral) and `(v, v)_V = ±2`, then `v` belongs to the integral Clifford group
`G(V)` (§2.1; stated in the paper for `(v, v)_V = 2`, and implicit for `-2` in "`-ρ(v)` is the
reflection with respect to `v^⊥`"). -/
theorem exists_mem_cliffordGroupZ_of_pairing_eq_two (v : V ℚ n) (hvZ : v ∈ VZ n)
    (hv : pairing ℚ n v v = 2 ∨ pairing ℚ n v v = -2) :
    ∃ x ∈ cliffordGroupZ n, (x : C ℚ n) = ι (Q ℚ n) v := by
  sorry

/-- If `(v₁, v₁)_V = (v₂, v₂)_V = 2`, or `(v₁, v₁)_V = (v₂, v₂)_V = -2` (with `v₁, v₂` integral),
then `v₁ · v₂` belongs to the integral `Spin(V)` (§2.1). -/
theorem exists_spinZ_eq_ι_mul_ι (v₁ v₂ : V ℚ n) (h₁ : v₁ ∈ VZ n) (h₂ : v₂ ∈ VZ n)
    (h : (pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
      (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2)) :
    ∃ g ∈ SpinZ n, (g : C ℚ n) = ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂ := by
  sorry

/-- **`Spin(V)` is generated by the products `v₁ v₂` with `(v₁,v₁)_V = (v₂,v₂)_V = ±2`** (§2.1,
stated without reference in the paper; it follows from the generation of `O(V)`, for the even
unimodular lattice `V = U^{⊕ 2n}`, by reflections in vectors of square `±2` (Wall)). We assume the
paper's standing hypothesis `n ≥ 2`: for `n = 0` the paper's `Spin(V) = {±1}` has no such
generators, and the case `n = 1` was not checked. -/
theorem spinZ_eq_closure (hn : 2 ≤ n) :
    SpinZ n = Subgroup.closure {g : Spin ℚ n | ∃ v₁ ∈ VZ n, ∃ v₂ ∈ VZ n,
      ((pairing ℚ n v₁ v₁ = 2 ∧ pairing ℚ n v₂ v₂ = 2) ∨
        (pairing ℚ n v₁ v₁ = -2 ∧ pairing ℚ n v₂ v₂ = -2)) ∧
      (g : C ℚ n) = ι (Q ℚ n) v₁ * ι (Q ℚ n) v₂} := by
  sorry

end Integral

end WeilClasses
