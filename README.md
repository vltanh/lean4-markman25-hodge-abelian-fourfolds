# Weil classes on abelian sixfolds and the Hodge conjecture for abelian fourfolds, in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-markman25-hodge-abelian-fourfolds/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-markman25-hodge-abelian-fourfolds/actions/workflows/lean_action_ci.yml)

A conditional Lean 4 formalization, on Mathlib, of

> Eyal Markman, *Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds*,
> [arXiv:2502.03415v2](https://arxiv.org/abs/2502.03415v2) (8 June 2025).

The paper proves that the Hodge–Weil classes of polarized abelian sixfolds of Weil type with discriminant `-1` are
algebraic (Theorem 1.5.1), and deduces the Hodge conjecture for abelian fourfolds (Corollary 1.6.1). The proof
constructs, on `X × X̂` for the Jacobian `X` of a genus-`3` curve, a sheaf whose characteristic class `κ(E)` stays of
Hodge type on every deformation of `X × X̂` as an abelian variety of Weil type (Theorem 1.4.1), and deforms it with the
semiregularity theorem. The algebra behind this, a rational secant line to the spinor variety of `H*(X)` and the
`Spin(V)`-equivariance of Orlov's derived equivalence, fills §§2–6 of the paper.

**It is conditional.** Every result of the paper about cohomology classes, Clifford algebras, spin representations,
Hodge structures and period domains is proved in a linear-algebra model of the cohomology of abelian varieties, by the
paper's arguments except the departures listed in [REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs) (notably Proposition 6.1.2 and Lemma 4.0.2,
proved by other arguments with the owner's approval). Theorem 1.5.1 and Corollary 1.6.1 are proved from named
hypotheses, each a class in their statements ([REPORT.md, Section 2](REPORT.md#assumed)):

- the paper's own sheaf-theoretic Sections 7–9, in the form "the class `κ₃(E)` is algebraic near `X × X̂` wherever
  `κ(E)` is of Hodge type" ([`SecantSheafDeformation`](Challenge.lean#L660)); that `κ(E)` is of Hodge type there is the paper's
  Corollary 1.3.2, which is proved;
- results from algebraic geometry not yet available in Lean. About algebraic cycles: pullbacks and products of
  algebraic classes, the Lefschetz (1,1) theorem, Voisin's algebraicity loci, Schoen's degeneration, and Ramón-Marí's
  theorem on products of surfaces. About Hodge structures: van Geemen's moduli of Weil-type abelian varieties and two
  theorems of Moonen–Zarhin on Hodge rings of fourfolds.

Three results of the paper's §10 (not used for the main theorems) assume two parts of Igusa's Proposition 3.

## What is proved

- **The paper's own results about cohomology classes, Clifford algebras, spin representations, Hodge structures and
  period domains**, in §§1–6, §8 and §10 (three of §10 under two parts of Igusa's Proposition 3), by the paper's
  arguments, except where the paper's argument is wrong or has a gap, needs mathematics Lean lacks, or has no meaning
  in the model, each case documented ([REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs)). Highlights: Theorem 1.4.1(3) and (4) (the classes
  `κ_k(E)` stay of Hodge type on the Weil-type deformations, and the `η(K)`-translates of `κ₃(E)` with `h³` span
  `ℚh³ ⊕ ĤW`), Corollary 1.3.2, Proposition 6.1.2 (Orlov's equivalence is `Spin(V)`-equivariant up to a class
  `exp(½[c₁(𝒫) - ρ_g c₁(𝒫)])`), Lemma 6.2.3, and the structure of the period domain `Ω_P` (§4).
- **The results the paper cites**, in [`WeilClasses/External/`](WeilClasses/External): Chevalley's theory of pure spinors, Igusa's Lemmas 1
  and 2, §2 and the invariance of the quartic in Proposition 3, results of Golyshev–Lunts–Orlov, Orlov, Huybrechts,
  Trautman, van Geemen (Def. 4.9) and Markman (2023), each in the case the paper uses ([REPORT.md, Section 2](REPORT.md#proved-in-external)).
- **No `sorry` outside [`Challenge.lean`](Challenge.lean), no `axiom`.** [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration depends only
  on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists the results from prior work each paper result uses.
- **The seven hypotheses on algebraic classes can be met**: they hold for the system in which every class is
  algebraic, and `X × X̂` is a polarized abelian `2n`-fold of Weil type with discriminant `(-1)ⁿ`
  ([`WeilClasses/Main/Instances.lean`](WeilClasses/Main/Instances.lean)). The hypotheses about Hodge structures and the two parts of Igusa's
  Proposition 3 are published results with no instance in Lean.

## The main results

[`Challenge.lean`](Challenge.lean) states, using only Mathlib, with the definitions written out between two marker
comments (a copy of [`WeilClasses/Defs.lean`](WeilClasses/Defs.lean)):

- [`Challenge.theorem1_4_1_3`](Challenge.lean#L711): for a principally polarized abelian threefold `X` and `d ≥ 3`, every graded summand of
  `κ(E)`, the characteristic class of the sheaf of Theorem 1.4.1, is a Hodge class on every polarized abelian sixfold
  of Weil type in the connected component of `X × X̂` in its period domain.
- [`Challenge.theorem1_4_1_4`](Challenge.lean#L721): the `η(K)`-translates of `κ₃(E)`, together with `h³`, span the `3`-dimensional space
  `ℚh³ ⊕ ĤW` of `H⁶(X × X̂, ℚ)`.
- [`Challenge.theorem1_5_1`](Challenge.lean#L734): under the hypotheses above, the Hodge–Weil classes of every polarized abelian sixfold of
  Weil type for `ℚ(√-d)` with discriminant `-1` are algebraic.
- [`Challenge.corollary1_6_1`](Challenge.lean#L742): under the hypotheses above, every Hodge class on an abelian fourfold is algebraic.
- Five compared theorems check the definitions against the paper: `Nm(a + b√-d) = a² + db²`, `f² = -d`, `X × X̂` lies
  in its own period domain, its discriminant is `(-1)ⁿ`, and the sheaf `E` has rank `8d`.

Abelian varieties are polarizable rational Hodge structures of weight one; "algebraic" refers to an abstract system
of subspaces [`CycleClasses`](Challenge.lean#L347) with the hypotheses as classes ([REPORT.md, Section 6](REPORT.md#6-how-the-formalization-reads-the-paper)).

## Palomar

[`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) (the same statements, proved from the library) and [`comparator.json`](comparator.json) form the
Palomar package. Run Comparator (it needs bubblewrap) with

```sh
lake env lake comparator --config=comparator.json    # "Your solution is okay!"
```

[`formalization.yaml`](formalization.yaml) describes the project for Palomar. The workflow `.github/workflows/palomar_preflight.yml` runs
Palomar's preflight on demand.

## Audit summary

[`REPORT.md`](REPORT.md) audits the paper against the formalization. In short:

- **Statements false or misprinted as printed (corrected here):** the equivariance in Proposition 1.3.1 (E2);
  Lemma 2.2.1 for odd `n` (E5); `Spin(V_K)_{ℓ₁,ℓ₂}/±1 ≅ GL(W₁)` on `K`-points (E6); Remark 2.2.5 (E9); the signs in
  Remark 2.3.1 (E10) and Lemma 6.3.2 (E21); (8.1.2), which needs `End_ℚ(X) = ℚ` (E23); the involution of §8.1 (E24);
  Remark 10.1.2(1) for `d = 0` (E26); misprints in Lemma 2.2.2 and in §8.1 (E28). The basis of Example 10.2.2 is
  also misprinted; the value computed there is unaffected (E28). The author has since corrected the integral Clifford
  algebra of §2.1, which has `2`-torsion as printed (E4).
- **Errors in proofs:** steps of the proofs of Lemma 2.2.1 (E5), Lemma 2.3.2(1) (E11), Lemma 3.1.2 (E16) and
  Lemma 6.3.2 (E21) are wrong; the statements hold, with the corrections above. §6.4 claims a transitivity that holds
  only within each family of maximal isotropic subspaces, and uses it only where it holds (E22). The paper states the
  orientation of the complex structure of `X × X̂` in two incompatible ways (E12).
- **Gaps, all filled:** the cases `d = 1, 2` and the passage to all of moduli in the proof of Theorem 1.5.1 (E3);
  irreducibility, density and complete reducibility for the arithmetic group `Spin(V)_P` and the rational groups
  `Spin(V_ℚ)_P`, `Spin(V_ℚ)_w` (E8, E19, E20, E27); and steps in Remark 2.2.3, Remark 2.4.3, Proposition 2.4.4,
  Lemma 3.1.1, Lemma 4.0.1, §4 and §10 (E7, E13–E15, E17, E18, E25).
- **None of this affects Theorem 1.4.1, Theorem 1.5.1 or Corollary 1.6.1.**
- **Proofs.** Every proof follows the paper's argument, except: Proposition 6.1.2 (and Lemma 6.2.5) is proved
  algebraically instead of by the paper's reduction to abelian surfaces, and Lemma 4.0.2 by transitivity instead of a
  dimension count, both authorized by the project owner; and single steps where the paper's step is wrong or has a
  gap, needs mathematics Lean lacks (Zariski density and closures, identity components, Hodge theory), or has no
  meaning in the model (line bundles, isogenies, sheaves, the Hodge structure of `C(V)`, fields of definition of
  algebraic groups). A route check ([`docs/route_differences.tsv`](docs/route_differences.tsv)) records every difference between the results a
  formal proof uses and those the paper's proof cites.

## Credits

- Author and maintainer: The-Anh Vu-Le, who chose the scope and decided every change of a statement.
- Tool: the Lean code and these documents were produced with Claude Opus 5.5 (Anthropic), run as an agent with
  sub-agents in Claude Code, following the [`formalize-math-paper`](https://github.com/vltanh/formalize-math-paper) skill, version 2.1.0.
- The statements, the proofs and the audit were each reviewed by independent agents against the TeX source. No person
  has reviewed the proofs yet.
- Made on 4 October 2026. [`CREDITS.md`](CREDITS.md) gives the procedure, the agents and the figures.

## Related work

- The Hodge conjecture for abelian fourfolds reduces, by Moonen–Zarhin and Schoen, to the algebraicity of Weil
  classes on fourfolds of Weil type; Markman's earlier work (JEMS 2023) settled discriminant `1`, and this paper all of
  them. The author's ICM 2026 survey (arXiv:2509.23403) extends the result to dimension at most `5`; Voisin's
  Bourbaki exposé 1248 presents the proof.
- **Earlier formalizations:** none of this paper or of its results was found. Formal statements of the Hodge
  conjecture exist in Lean (Paul-Lez/HodgeConjecture, work in progress, whose variant
  `HodgeConjectureForAbelianVarietiesInDimensionLE` cites this paper; the statement in LeanMillenniumPrizeProblems is
  marked incomplete); they were not used here. Repositories claiming machine-checked proofs of the Hodge conjecture
  rest on added axioms, `sorry` or unproved assumptions.
- The project reuses no code from these; it builds on Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Clifford algebras, spin groups).

## What's next

Nothing published since the paper casts doubt on its results; the author has corrected the integral Clifford algebra
of §2.1 (E4) and a misprint in Lemma 2.2.2 (E28). Perry claims the paper's Conjecture 7.3.9 (preprint), which would
simplify §9. See [REPORT.md, Section 10](REPORT.md#10-whats-next). [`ROADMAP.md`](ROADMAP.md) plans how to remove the
hypotheses, in layers: first those about Hodge structures, then actual abelian varieties and their algebraic cycles,
and finally the paper's sheaf theory.

## Building

```sh
lake exe cache get        # Mathlib's compiled files
lake build                # the library, Challenge and Solution
lake env lean scripts/Audit.lean    # axioms and dependencies of every result
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
```

Lean `v4.35.0-rc3`, Mathlib `ec6a61c`, Tau Ceti `fd2b86b` (in proofs only; the Challenge imports nothing but
Mathlib). Generated files: [`scripts/Audit.lean`](scripts/Audit.lean) (`python3 scripts/gen_audit.py`), the definitions block of
[`Challenge.lean`](Challenge.lean) (`python3 scripts/sync_challenge_defs.py`), [`docs/paper_routes.tsv`](docs/paper_routes.tsv) (extracted from the TeX source by
`route_check.py extract`). `python3 scripts/linkify_docs.py` updates the links to the code in the Markdown files.

## Layout

| Path | Contents |
|---|---|
| [`WeilClasses/Defs.lean`](WeilClasses/Defs.lean) | The definitions of the statements of record (shared with [`Challenge.lean`](Challenge.lean)): `K = ℚ(√-d)`, the model of cohomology, abelian varieties of Weil type, the hypothesis classes, `X × X̂`, the classes `κ(E)` |
| [`WeilClasses/Basic`](WeilClasses/Basic), `Spinor`, `Hodge` | `K`, the spin representation, base change, integral structures, Hodge classes (§§1.2, 2.1) |
| [`WeilClasses/PureSpinor`](WeilClasses/PureSpinor) | §2.1–2.2: pure spinors, `K`-secants, Lemmas 2.2.1–2.2.7 |
| [`WeilClasses/Chevalley`](WeilClasses/Chevalley) | §2.3: Chevalley's isomorphism `φ̃` |
| [`WeilClasses/WeilType`](WeilClasses/WeilType) | §2.4: polarized abelian varieties of Weil type from oriented `K`-secants, Proposition 2.4.4 |
| [`WeilClasses/Hermitian`](WeilClasses/Hermitian) | §3: the Hermitian form, Lemmas 3.1.1–3.2.1, Corollaries 3.2.2–3.2.3 |
| [`WeilClasses/PeriodDomain`](WeilClasses/PeriodDomain) | §4: the period domain `Ω_P`, Lemmas 4.0.1–4.0.3, Corollary 4.0.4 |
| [`WeilClasses/Correspondence`](WeilClasses/Correspondence) | §5.2: correspondences, the Poincaré bundle, Fourier–Mukai transforms |
| [`WeilClasses/Orlov`](WeilClasses/Orlov) | §1.3, §6: Orlov's equivalence, Proposition 6.1.2, Lemma 6.2.3, Lemma 6.3.2, Proposition 6.4.1, Corollary 1.3.2 |
| [`WeilClasses/Secant`](WeilClasses/Secant) | §8: `K`-secants on a generic ppav, Lemma 8.2.1, Lemma 8.3.1 |
| [`WeilClasses/Igusa`](WeilClasses/Igusa) | §10: the Igusa quartic, Lemmas 10.1.1 and 10.2.1 |
| [`WeilClasses/AbelianVariety`](WeilClasses/AbelianVariety) | Abelian varieties up to isogeny; hard Lefschetz and Poincaré reducibility (for Corollary 1.6.1) |
| [`WeilClasses/Main`](WeilClasses/Main) | Theorems 1.4.1, 1.5.1, Corollary 1.6.1; `X × X̂` explicitly; the instances |
| `WeilClasses/External/<Source>` | The cited results, one directory per source, each with a README |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | The statements of record, and their proofs from the library |
| [`scripts/`](scripts) | The audit, the route check, the synchronization of the Challenge |
| [`docs/`](docs) | The routes of the paper's proofs and the recorded differences |

## GitHub configuration

- `.github/workflows/lean_action_ci.yml` builds the project, runs the audit, and checks the Challenge's definitions,
  the documentation's links and the Markdown tables, on every push.
- `.github/workflows/palomar_preflight.yml` runs Palomar's preflight on demand (the repository must be public).

## License

Apache-2.0 ([`LICENSE`](LICENSE)).
