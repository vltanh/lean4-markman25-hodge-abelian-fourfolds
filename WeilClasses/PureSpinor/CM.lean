module

public import WeilClasses.PureSpinor.Defs

/-!
# The action of `K` on `V_ℚ` attached to a `K`-secant (paper (2.2.3)–(2.2.4))

When `W₁ ∩ W₂ = 0`, `V_K = W₁ ⊕ W₂`, and `η_λ` acts on `W₁` by `λ` and on `W₂` by `σ(λ)`. It commutes
with `σ`, so it preserves `V_ℚ`; this gives `η : K → End(V_ℚ)` (2.2.4), whose restriction to `K^×`
is the paper's homomorphism `K^× → GL(V_ℚ)`. The rational similarity group `Õ(V_ℚ)` is (2.2.3).

To descend a `σ`-equivariant endomorphism of `V_K` to `V_ℚ` we take rational parts of coordinates
(`WeilClasses.Kd.ratPart`, the coefficient `a` of `a + b√-d`).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable (n : ℕ) (d : ℚ)

namespace Kd

theorem exists_ratPart (z : Kd d) : ∃ a : ℚ, (a : ℝ) = (z : ℂ).re := by
  obtain ⟨a, b, hz⟩ := (mem_iff d).mp z.2
  refine ⟨a, ?_⟩
  rw [hz]
  simp [fnd_re_sqrtNeg]

/-- The rational part `a` of `z = a + b√-d ∈ K` (the real part of `z`). -/
noncomputable def ratPartFun (z : Kd d) : ℚ := Classical.choose (exists_ratPart d z)

theorem fnd_ratPartFun_spec (z : Kd d) : ((ratPartFun d z : ℚ) : ℝ) = (z : ℂ).re :=
  Classical.choose_spec (exists_ratPart d z)

/-- The rational part `a` of `z = a + b√-d ∈ K`, as a `ℚ`-linear map. -/
noncomputable def ratPart : Kd d →ₗ[ℚ] ℚ where
  toFun := ratPartFun d
  map_add' := by
    intro x y
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, fnd_ratPartFun_spec, fnd_ratPartFun_spec, fnd_ratPartFun_spec,
      Subfield.coe_add, Complex.add_re]
  map_smul' := by
    intro c x
    apply Rat.cast_injective (α := ℝ)
    rw [RingHom.id_apply, smul_eq_mul, Rat.cast_mul, fnd_ratPartFun_spec, fnd_ratPartFun_spec,
      fnd_coe_smul]
    simp

/-- The rational part of `a + b√-d` is `a`. -/
theorem fnd_ratPart_eq {z : Kd d} {a b : ℚ} (hz : (z : ℂ) = a + b * WeilClasses.sqrtNeg d) :
    ratPart d z = a := by
  apply Rat.cast_injective (α := ℝ)
  show ((ratPartFun d z : ℚ) : ℝ) = a
  rw [fnd_ratPartFun_spec, hz]
  simp [fnd_re_sqrtNeg]

/-- The coefficient `b` of `z = a + b √-d ∈ K = ℚ(√-d)` (for `d > 0`):
`b = -(1/d) · Re(z √-d)`. Together with `Kd.ratPart` it gives the coordinates of `K = ℚ ⊕ ℚ √-d`. -/
noncomputable def sqrtNegCoeff : Kd d →ₗ[ℚ] ℚ :=
  (-(d⁻¹)) • (Kd.ratPart d ∘ₗ LinearMap.mulRight ℚ (Kd.sqrtNeg d))

/-- `z = a + b √-d` with `a = Kd.ratPart d z` and `b = Kd.sqrtNegCoeff d z` (for `d > 0`). -/
theorem eq_ratPart_add_sqrtNegCoeff {d : ℚ} (hd : 0 < d) (z : Kd d) :
    z = algebraMap ℚ (Kd d) (Kd.ratPart d z) +
      algebraMap ℚ (Kd d) (Kd.sqrtNegCoeff d z) * Kd.sqrtNeg d := by
  obtain ⟨a, b, hz⟩ := (mem_iff d).mp z.2
  have hs : WeilClasses.sqrtNeg d * WeilClasses.sqrtNeg d = -(d : ℂ) := by
    rw [← sq, sqrtNeg_sq hd.le]
  have h1 : ratPart d z = a := fnd_ratPart_eq d hz
  -- `z √-d = -d b + a √-d`
  have h2 : ratPart d (z * Kd.sqrtNeg d) = -d * b := by
    apply fnd_ratPart_eq d (b := a)
    rw [Subfield.coe_mul, hz]
    show ((a : ℂ) + b * WeilClasses.sqrtNeg d) * WeilClasses.sqrtNeg d = _
    push_cast
    linear_combination (b : ℂ) * hs
  have h3 : sqrtNegCoeff d z = b := by
    simp only [sqrtNegCoeff, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, h2, smul_eq_mul]
    field_simp
  rw [h1, h3]
  apply Subtype.ext
  rw [hz]
  simp only [Subfield.coe_add, Subfield.coe_mul]
  rfl

/-- An element of `K` fixed by `σ` is rational: `ratPart` recovers it. -/
theorem fnd_algebraMap_ratPart_of_σ {z : Kd d} (hz : σ d z = z) :
    algebraMap ℚ (Kd d) (ratPart d z) = z := by
  obtain ⟨a, b, hab⟩ := (mem_iff d).mp z.2
  have hc := congrArg (fun x : Kd d => (x : ℂ)) hz
  simp only [coe_σ, hab, map_add, map_mul, map_ratCast, fnd_conj_sqrtNeg] at hc
  have hb : (b : ℂ) * WeilClasses.sqrtNeg d = 0 := by linear_combination -hc / 2
  have hz' : (z : ℂ) = a + (0 : ℚ) * WeilClasses.sqrtNeg d := by
    rw [hab, hb]; simp
  rw [fnd_ratPart_eq d hz']
  apply Subtype.ext
  rw [hab, hb, add_zero]
  rfl

/-- `σ` fixes the rational numbers. -/
theorem fnd_σ_algebraMap (q : ℚ) : σ d (algebraMap ℚ (Kd d) q) = algebraMap ℚ (Kd d) q := by
  apply Subtype.ext
  rw [coe_σ]
  show (starRingEnd ℂ) (q : ℂ) = (q : ℂ)
  simp

end Kd

/-- A functional on `F^{2n}` is `θ = Σᵢ θ(eᵢ) fᵢ`. -/
theorem fnd_dual_eq_sum (F : Type*) [Field F] [CharZero F] (θ : Module.Dual F (H1 F n)) :
    θ = ∑ i, θ (e F n i) • f F n i := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [show w = ∑ i, w i • e F n i by ext j; simp [e, Pi.single_apply]]
  simp [map_sum, f, mul_comm]

/-- `(Σᵢ cᵢ fᵢ)(eⱼ) = cⱼ`. -/
theorem fnd_sum_smul_f_apply (F : Type*) [Field F] [CharZero F] (c : Fin (2 * n) → F)
    (j : Fin (2 * n)) : (∑ i, c i • f F n i) (e F n j) = c j := by
  simp [f, e, Pi.single_apply]

/-- Rational parts of the coordinates of a vector of `V_K`. -/
noncomputable def ratPartV : V (Kd d) n →ₗ[ℚ] V ℚ n where
  toFun v := (∑ i, Kd.ratPart d (v.1 (e (Kd d) n i)) • f ℚ n i, fun i => Kd.ratPart d (v.2 i))
  map_add' v w := by
    ext <;> simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext <;> simp [Finset.smul_sum, smul_smul]

/-- The rational endomorphism of `V_ℚ` induced by an endomorphism of `V_K` (meaningful when the
endomorphism commutes with `σ`, `WeilClasses.bcV_descend`). -/
noncomputable def descend (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n) : V ℚ n →ₗ[ℚ] V ℚ n :=
  ratPartV n d ∘ₗ (A.restrictScalars ℚ) ∘ₗ bcV ℚ (Kd d) n

/-- `σ` fixes the vectors of `V_K` defined over `ℚ`. -/
theorem fnd_σV_bcV (v : V ℚ n) : σV n d (bcV ℚ (Kd d) n v) = bcV ℚ (Kd d) n v := by
  have he : ∀ i, (bcV ℚ (Kd d) n v).1 (e (Kd d) n i) = algebraMap ℚ (Kd d) (v.1 (e ℚ n i)) := by
    intro i
    simp only [bcV, LinearMap.prodMap_apply, bcDual, LinearMap.coe_mk, AddHom.coe_mk]
    exact fnd_sum_smul_f_apply n (Kd d) _ i
  refine Prod.ext ?_ ?_
  · show ∑ i, Kd.σ d ((bcV ℚ (Kd d) n v).1 (e (Kd d) n i)) • f (Kd d) n i =
      (bcV ℚ (Kd d) n v).1
    simp only [he, Kd.fnd_σ_algebraMap]
    rfl
  · funext i
    show Kd.σ d ((bcV ℚ (Kd d) n v).2 i) = (bcV ℚ (Kd d) n v).2 i
    exact Kd.fnd_σ_algebraMap d _

/-- A vector of `V_K` fixed by `σ` is defined over `ℚ`: it is the base change of its rational
parts. -/
theorem fnd_bcV_ratPartV (w : V (Kd d) n) (hw : σV n d w = w) :
    bcV ℚ (Kd d) n (ratPartV n d w) = w := by
  have h1 : ∀ j, Kd.σ d (w.1 (e (Kd d) n j)) = w.1 (e (Kd d) n j) := by
    intro j
    have := congrArg (fun u : V (Kd d) n => u.1 (e (Kd d) n j)) hw
    simpa [σV, conjV, fnd_sum_smul_f_apply] using this
  have h2 : ∀ j, Kd.σ d (w.2 j) = w.2 j := by
    intro j
    have := congrArg (fun u : V (Kd d) n => u.2 j) hw
    simpa [σV, conjV] using this
  refine Prod.ext ?_ ?_
  · show ∑ i, algebraMap ℚ (Kd d)
        ((∑ j, Kd.ratPart d (w.1 (e (Kd d) n j)) • f ℚ n j) (e ℚ n i)) • f (Kd d) n i = w.1
    simp only [fnd_sum_smul_f_apply, Kd.fnd_algebraMap_ratPart_of_σ d (h1 _)]
    exact (fnd_dual_eq_sum n (Kd d) w.1).symm
  · funext i
    show algebraMap ℚ (Kd d) (Kd.ratPart d (w.2 i)) = w.2 i
    exact Kd.fnd_algebraMap_ratPart_of_σ d (h2 i)

theorem bcV_descend (A : V (Kd d) n →ₗ[Kd d] V (Kd d) n)
    (hA : ∀ v, σV n d (A v) = A (σV n d v)) (v : V ℚ n) :
    bcV ℚ (Kd d) n (descend n d A v) = A (bcV ℚ (Kd d) n v) := by
  -- `A(v)` is `σ`-invariant, hence defined over `ℚ`.
  have hfix : σV n d (A (bcV ℚ (Kd d) n v)) = A (bcV ℚ (Kd d) n v) := by
    rw [hA, fnd_σV_bcV]
  exact fnd_bcV_ratPartV n d _ hfix

/-- `Nm(k) ≠ 0` for `k ≠ 0` (the norm of a unit is a unit). -/
theorem Kd.fnd_Nm_ne_zero {z : Kd d} (hz : z ≠ 0) : Kd.Nm d z ≠ 0 :=
  ((isUnit_iff_ne_zero.mpr hz).map (Algebra.norm ℚ)).ne_zero

/-- `Nm(k⁻¹) = Nm(k)⁻¹` for `k ≠ 0`. -/
theorem Kd.fnd_Nm_inv {z : Kd d} (hz : z ≠ 0) : Kd.Nm d z⁻¹ = (Kd.Nm d z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [Kd.Nm, Kd.Nm, ← map_mul, inv_mul_cancel₀ hz, map_one]

/-- The group `Õ(V_ℚ)` of rational similarities of `V_ℚ` with multiplier in `Nm(K^×)` (2.2.3). -/
def Otilde : Subgroup (V ℚ n ≃ₗ[ℚ] V ℚ n) where
  carrier := {g | ∃ c ∈ Kd.normGroup d, ∀ x y, pairing ℚ n (g x) (g y) = c * pairing ℚ n x y}
  one_mem' := ⟨1, ⟨1, one_ne_zero, map_one _⟩, fun x y => by simp⟩
  mul_mem' := by
    rintro g h ⟨a, ⟨za, hza0, hza⟩, hga⟩ ⟨b, ⟨zb, hzb0, hzb⟩, hhb⟩
    refine ⟨a * b, ⟨za * zb, mul_ne_zero hza0 hzb0, ?_⟩, fun x y => ?_⟩
    · rw [← hza, ← hzb, Kd.Nm, Kd.Nm, Kd.Nm, map_mul]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hga, hhb, mul_assoc]
  inv_mem' := by
    rintro g ⟨a, ⟨za, hza0, hza⟩, hga⟩
    have ha0 : a ≠ 0 := hza ▸ Kd.fnd_Nm_ne_zero d hza0
    refine ⟨a⁻¹, ⟨za⁻¹, inv_ne_zero hza0, by rw [Kd.fnd_Nm_inv d hza0, hza]⟩, fun x y => ?_⟩
    have h := hga (g⁻¹ x) (g⁻¹ y)
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
    simp only [LinearEquiv.coe_inv]
    rw [h, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]

namespace KSecant

variable {n d} (P : KSecant n d)

/-- The `K`-linear endomorphism `η_λ` of `V_K = W₁ ⊕ W₂`: multiplication by `λ` on `W₁` and by
`σ(λ)` on `W₂` (2.2.4); here `hW : V_K = W₁ ⊕ W₂`. -/
noncomputable def ηK (hW : IsCompl P.W₁ P.W₂) (l : Kd d) : V (Kd d) n →ₗ[Kd d] V (Kd d) n :=
  l • (P.W₁.subtype ∘ₗ Submodule.projectionOnto P.W₁ P.W₂ hW) +
    Kd.σ d l • (P.W₂.subtype ∘ₗ Submodule.projectionOnto P.W₂ P.W₁ hW.symm)

/-- The rational endomorphism `η_λ` of `V_ℚ` (2.2.4): the descent of `ηK`. -/
noncomputable def η (hW : IsCompl P.W₁ P.W₂) (l : Kd d) : V ℚ n →ₗ[ℚ] V ℚ n :=
  descend n d (P.ηK hW l)

/-- `f = η_{√-d}` (2.4.1). -/
noncomputable def fη (hW : IsCompl P.W₁ P.W₂) : V ℚ n →ₗ[ℚ] V ℚ n := P.η hW (Kd.sqrtNeg d)

end KSecant

end WeilClasses
