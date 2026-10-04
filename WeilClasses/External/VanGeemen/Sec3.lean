module

public import WeilClasses.WeilType.Basic

/-!
# van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, Def. 4.9

B. van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, in: Algebraic
cycles and Hodge theory (Torino 1993), Lecture Notes in Math. 1594, Springer (1994), Def. 4.9: a
polarized abelian variety of Weil type is an abelian variety of Weil type `(A, K)` with a
polarization `E` such that `E(η(k) x, η(k) y) = Nm(k) E(x, y)` for all `k ∈ K`. (In the paper's §1.1:
"`η(k)` maps `h` to `Nm(k) h`".)

The paper uses the definition in the proof of Corollary 3.2.3 (TeX lines 1698–1705), where it checks
only `f^*Ξ_P = d Ξ_P` for `f = η(√-d)`, "verifying the condition on the polarization in
[van Geemen, Def. 4.9]". The statement below is the (elementary) fact that this suffices: for
`η(a + b√-d) = a + b f` with `f² = -d`, `f^*E = d E` implies `η(k)^*E = Nm(k) E` for every `k ∈ K`.
The model of polarized abelian varieties of Weil type is `WeilClasses.PolarizedWeilType`
(`WeilClasses.Defs`).
-/

@[expose] public section

namespace WeilClasses

variable {n : ℕ} {d : ℚ}

/-! ## Helpers (prover SC, prefix `sc_`) -/

/-- `Nm(a + b√-d) = a² + d b²`, with `a = Kd.ratPart d k` and `b = Kd.sqrtNegCoeff d k`. -/
theorem sc_Nm_eq_ratPart_sq_add (hd : 0 < d) (k : Kd d) :
    Kd.Nm d k = Kd.ratPart d k ^ 2 + d * Kd.sqrtNegCoeff d k ^ 2 := by
  have hk := congrArg (fun z : Kd d => (z : ℂ)) (Kd.eq_ratPart_add_sqrtNegCoeff hd k)
  simp only [Subfield.coe_add, Subfield.coe_mul] at hk
  have hq : ∀ q : ℚ, ((algebraMap ℚ (Kd d) q : Kd d) : ℂ) = (q : ℂ) := fun q => by
    rw [eq_ratCast (algebraMap ℚ (Kd d)) q, SubfieldClass.coe_ratCast]
  rw [hq, hq] at hk
  have hs : (WeilClasses.sqrtNeg d) ^ 2 = -(d : ℂ) := sqrtNeg_sq hd.le
  have hsK : ((Kd.sqrtNeg d : Kd d) : ℂ) = WeilClasses.sqrtNeg d := rfl
  rw [hsK] at hk
  apply Rat.cast_injective (α := ℂ)
  rw [Kd.coe_Nm hd, hk]
  simp only [map_add, map_mul, map_ratCast, fnd_conj_sqrtNeg]
  push_cast
  linear_combination (-(Kd.sqrtNegCoeff d k : ℂ) ^ 2) * hs

/-- **[van Geemen, Def. 4.9]**, the condition on the polarization, in the form used in the proof of
Corollary 3.2.3: if `f² = -d` and `E(f x, f y) = d E(x, y)` for a bilinear form `E` on `V_ℚ`, then
`E(η(k) x, η(k) y) = Nm(k) E(x, y)` for every `k = a + b√-d ∈ K`, where `η(k) = a + b f`. -/
theorem vanGeemen_def4_9 (hd : 0 < d) (E : LinearMap.BilinForm ℚ (V ℚ n))
    (f : V ℚ n →ₗ[ℚ] V ℚ n) (hf : f ∘ₗ f = -(d • LinearMap.id))
    (hE : ∀ x y, E (f x) (f y) = d * E x y) (k : Kd d) (x y : V ℚ n) :
    E (Kd.ratPart d k • x + Kd.sqrtNegCoeff d k • f x) (Kd.ratPart d k • y + Kd.sqrtNegCoeff d k • f y) =
      Kd.Nm d k * E x y := by
  -- `f² = -d` gives `E(x, f y) = -E(f x, y)`: apply `hE` to `f x` and `y`.
  have hff : ∀ v, f (f v) = -(d • v) := fun v => by
    have := LinearMap.congr_fun hf v
    simpa using this
  have hskew : E x (f y) = -E (f x) y := by
    have h := hE (f x) y
    rw [hff x, map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at h
    have hd0 : d ≠ 0 := hd.ne'
    have h' : d * (E x (f y) + E (f x) y) = 0 := by linear_combination -h
    have := (mul_eq_zero.mp h').resolve_left hd0
    linear_combination this
  rw [sc_Nm_eq_ratPart_sq_add hd k]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hE, hskew]
  ring

end WeilClasses
