# Voisin, Séminaire Bourbaki, exposé 1248 (January 2026), Lemme 2.9 and Corollaire 2.10

C. Voisin, *La conjecture de Hodge pour les variétés abéliennes de dimension au plus 5 [d'après
Markman]*, Séminaire Bourbaki, exposé 1248, 31 January 2026
(<https://www.bourbaki.fr/TEXTES/Exp1248-Voisin.pdf>).

## `Lemma2_9.lean`: [Schoen, Prop. 10] from push-forward (prover L1c, helper prefix `vo_`)

Corollary 1.6.1 uses [Schoen, Prop. 10] (TeX line 600), in the form of the class `SchoenDegeneration`
(`Lemma2_9.lean`): if the Hodge–Weil classes of all polarized abelian sixfolds
of Weil type for `K = ℚ(√-d)` with discriminant `-1` are algebraic, so are those of all abelian
fourfolds of Weil type for `K`. Voisin's Lemme 2.9 (if the Hodge conjecture holds for the Weil
classes of `A₁` and of `A₁ × A₂`, it holds for those of `A₂`) and Corollaire 2.10 (with `A₁` a Weil
surface of a suitable discriminant) give the same conclusion by a different argument, a
correspondence instead of Schoen's degeneration.

* `schoenDegeneration_of_pushforward`: for every system of algebraic classes `Z` with
  `PullbackClosed`, `SubalgebraClosed`, `LefschetzOneOne` and `PushforwardClosed`,
  `SchoenDegeneration Z`. **Proved.** It is exactly the statement of [Schoen, Prop. 10] used in
  Corollary 1.6.1, which therefore takes `PushforwardClosed` as a hypothesis instead.
* `PushforwardClosed` (in `WeilClasses/Defs.lean`, since Corollary 1.6.1 states it): push-forward along the
  projection `A₁ × A₂ → A₂` maps algebraic classes to algebraic classes. In the model, `A₁ × A₂` has
  `H¹ = H¹(A₁) ⊕ H¹(A₂)` (`prodEquiv`), the complex structure `prodJ`, and the push-forward is
  integration over the fibre (`pushSnd`: contraction with the dual basis of `H¹(A₁)`, then restriction
  to `A₂`), characterized by the projection formula `pr₂,*(pr₁^*a ∪ pr₂^*b) = (∫_{A₁} a) b`
  (`pushSnd_prodInl_mul_prodInr`). This is a new hypothesis, standard for actual cycles (proper
  push-forward of cycles is compatible with the cycle class map).

How the proof relates to Voisin's argument (`w₂ = pr₂,*(pr₁^*w₁' ∪ w)`, `w` a Weil class of
`A₁ × A₂`): for an abelian fourfold `A₂` of Weil type and `w₂ ∈ ĤW(A₂)`,

1. `A₂` gets the compatible polarization `h = Θ + η(√-d)^*Θ/d` (`vo_polarize`), and a `K`-basis in
   which the Gram determinant `δ` of van Geemen's form is a positive rational number (`vo_disc_pos`;
   `δ > 0` because the form has signature `(2, 2)`, `vo_herm_det_sign`, for every `m`:
   `(-1)^m det > 0` on a `2m`-fold);
2. `A₁ = E₊ × E₋` (`vo_XS`) is the Weil surface made of the elliptic curves `ℚ²` with complex
   multiplication by `K` of the two CM types, polarized so that its Hermitian form is
   `diag(d, -dδ)` (discriminant `-δ ≡ -δ⁻¹` modulo norms);
3. `A₁ × A₂` (`vo_X6`) is a polarized abelian sixfold of Weil type with discriminant `-1`
   (`vo_X6_discIs`);
4. the class `w = pr₁^*A ∪ pr₂^*w₂ + pr₁^*B ∪ pr₂^*v₂` (`vo_w`), built from rational classes `A`,
   `B` of the surface with `2A = ω₁ + ω̄₁`, `2√-d B = ω₁ - ω̄₁` (`ω₁` spanning `⋀²W₁`) and
   `v₂ = √-d(ω - ω̄)` when `w₂ = ω + ω̄` over `K`, is a Hodge–Weil class of `A₁ × A₂`
   (`vo_w_mem_HW`); it is `pr₁^*ω₁ ∪ pr₂^*ω + pr₁^*ω̄₁ ∪ pr₂^*ω̄` over `K`;
5. `w` is algebraic by the sixfold statement, `A` (a class of type `(1,1)`, `vo_AS_hodge`) by
   Lefschetz `(1,1)`, so `pr₁^*A ∪ w` is algebraic (`PullbackClosed`, `SubalgebraClosed`);
6. `pr₂,*(pr₁^*A ∪ w) = (∫A²) w₂ = 2d w₂` (`vo_pushSnd_w`) is algebraic (`PushforwardClosed`).

Here `w₁' = A` and `w` is a Weil class of `A₁ × A₂`; the product `pr₁^*w₁ ∪ pr₂^*w₂` of a Weil class
of `A₁` and one of `A₂` is not a Weil class of `A₁ × A₂` (its parts `ω₁ ∧ ω̄` and `ω̄₁ ∧ ω` have
mixed type), which is why step 4 uses `w`. The surfaces of step 2 exist only for `δ > 0` (a Weil
surface has signature `(1,1)`), which is why step 1 proves the sign of `δ`.

The proof is in the model: no result of Voisin's text is assumed, and nothing beyond the four
hypotheses on `Z`. Public helpers (all prefixed `vo_`) include `vo_det_sign` (sign of the determinant
of a Hermitian matrix that is positive on one subspace and negative on a complementary orthogonal
one), `vo_herm_det_sign`, `vo_norm_of_sqrtNeg` (`η(√-d)^*h = d h` implies `η(k)^*h = Nm(k) h`) and the
product lemmas of `Product.lean`.
