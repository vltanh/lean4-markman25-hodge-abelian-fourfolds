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
(`WeilClasses.AbelianVariety.Defs`).
-/

@[expose] public section

namespace WeilClasses

variable {n : ℕ} {d : ℚ}

/-- **[van Geemen, Def. 4.9]**, the condition on the polarization, in the form used in the proof of
Corollary 3.2.3: if `f² = -d` and `E(f x, f y) = d E(x, y)` for a bilinear form `E` on `V_ℚ`, then
`E(η(k) x, η(k) y) = Nm(k) E(x, y)` for every `k = a + b√-d ∈ K`, where `η(k) = a + b f`. -/
theorem vanGeemen_def4_9 (hd : 0 < d) (E : LinearMap.BilinForm ℚ (V ℚ n))
    (f : V ℚ n →ₗ[ℚ] V ℚ n) (hf : f ∘ₗ f = -(d • LinearMap.id))
    (hE : ∀ x y, E (f x) (f y) = d * E x y) (k : Kd d) (x y : V ℚ n) :
    E (Kd.ratPart d k • x + Kd.sqrtNegCoeff d k • f x) (Kd.ratPart d k • y + Kd.sqrtNegCoeff d k • f y) =
      Kd.Nm d k * E x y := by
  sorry

end WeilClasses
