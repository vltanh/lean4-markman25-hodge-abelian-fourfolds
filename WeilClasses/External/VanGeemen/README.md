# van Geemen, *An introduction to the Hodge conjecture for abelian varieties* (1994)

B. van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, in: Algebraic
cycles and Hodge theory (Torino 1993), Lecture Notes in Math. 1594, Springer (1994).

## `Sec3.lean`: [Def. 4.9] (prover SC)

The paper (proof of Corollary 3.2.3, TeX lines 1698–1705) checks only `f^*Ξ_P = d Ξ_P` for
`f = η(√-d)`, "verifying the condition on the polarization in [van Geemen, Def. 4.9]", which asks
`E(η(k) x, η(k) y) = Nm(k) E(x, y)` for every `k ∈ K = ℚ(√-d)`.

* `vanGeemen_def4_9`: for a bilinear form `E` on `V_ℚ` and `f` with `f² = -d`, `E(f x, f y) = d E(x, y)`
  implies `E(η(k) x, η(k) y) = Nm(k) E(x, y)` for `η(k) = a + b f`, `k = a + b√-d`
  (`a = Kd.ratPart d k`, `b = Kd.sqrtNegCoeff d k`, `d > 0`).

Proved (no hypothesis). Proof: applying the hypothesis to `f x, y` and `f² = -d` gives
`E(x, f y) = -E(f x, y)`, so the cross terms cancel and
`E(a x + b f x, a y + b f y) = (a² + d b²) E(x, y)`; `Nm(a + b√-d) = a² + d b²` is
`sc_Nm_eq_ratPart_sq_add` (from `Kd.coe_Nm` and `Kd.eq_ratPart_add_sqrtNegCoeff`).
Public helper: `sc_Nm_eq_ratPart_sq_add`.

## [Th. 5.2(3)], in the case used in Theorem 1.5.1 (prover L1a, helper prefix `vg_`)

Theorem 1.5.1 uses [Th. 5.2(3)] (polarized abelian `2n`-folds of Weil type with the same `K` and
discriminant form one connected family up to isogeny) once, at the end of its proof (TeX line 6847,
E3): for a sixfold `A` of discriminant `-1` against the sixfold `X × X̂` of discriminant `-1`.

* `vanGeemen_moduli_XXhat` (`WeilClasses/External/VanGeemen/Moduli.lean`): for every `n > 0` and every polarized
  abelian `2n`-fold of Weil type `A` of discriminant `(-1)ⁿ`, a `K`-linear isomorphism `ψ` of `H¹`
  maps the polarization of `A` to that of `X × X̂` and carries the complex structure of `A` into the
  connected component of `X × X̂` in its Weil-type period domain. **Proved.**
* `weilDomainMat_isPreconnected`: the Weil-type period domain of `X × X̂` is connected (it is the image of
  `Ω_P` under `I ↦ -I`, `weilDomain_eq_image_OmegaP`, and `Ω_P` is path-connected, Lemma 4.0.2).
* `vg_HermSpace.landherr_split` (`Landherr.lean`): Landherr's theorem in the split case: a Hermitian
  form over `K = ℚ(√-d)` of `K`-rank `2n`, signature `(n, n)` and discriminant `(-1)ⁿ` is hyperbolic.
  The isotropic vectors come from Meyer's theorem (`HasseMinkowski.meyer`, vendored in
  `WeilClasses/External/HasseMinkowski/`) while the complement has `K`-rank at least `4`, and from the
  discriminant for the last plane.

Proof (van Geemen's: Landherr's theorem and the connectedness of the period domain). Van Geemen's
Hermitian form `H(x, y) = E(x, f y) + √-d E(x, y)` on `H₁(A, ℚ)` has signature `(n, n)`: on the two
eigenspaces of `f Jᵀ`, `H(a, a) = ±√d E(a, a ∘ J)`, of sign `±` by ampleness, and the Weil condition
gives both dimension at least `2n` (`vg_posBound`, `vg_negBound`). Landherr's theorem makes the forms
of `A` and of `X × X̂` hyperbolic, hence isometric (`exists_isometry`); `ψ` is the inverse transpose of
the isometry, and the complex structure of `A` is transported into the period domain of `X × X̂`
(`vg_transport_mem`), which is connected. Only this case is proved; the general statement (every
discriminant) is not needed.
