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
