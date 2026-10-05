# Audit of the paper and the formalization

Paper: Eyal Markman, *Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds*,
[arXiv:2502.03415v2](https://arxiv.org/abs/2502.03415v2) (8 June 2025). The audit was made against the arXiv LaTeX source of that version (`250531.tex`);
"TeX l." numbers refer to its lines. Section, result and equation numbers are the paper's.

Status of the formalization:

- **Proved, by the paper's arguments.** Every result of §§1–6, §8 and §10 that the paper proves about cohomology
  classes, Clifford algebras, spin representations, Hodge structures and period domains is proved, in a linear-algebra
  model of the cohomology of abelian varieties (Section 6). This includes Proposition 1.2.1, Proposition 1.3.1,
  Corollary 1.3.2, Theorem 1.4.1(1), (3), (4) and the rank in (2), all numbered results of §§2–6 except the
  derived-category Lemma 6.2.1 (and Definition 6.2.2), the cohomological results of §8, and §10 (Lemma 10.1.1,
  Remark 10.1.2 and Lemma 10.2.1 under two parts of [Igusa, Prop. 3]). Every proof follows the paper's argument,
  except the departures listed in Section 7, each forced by one of three reasons (the paper's step is wrong or has a
  gap; the step needs mathematics that Lean lacks; the step has no meaning in the model).
- **Cited results, proved.** The results of Chevalley, Igusa (except two parts of Prop. 3), Golyshev–Lunts–Orlov,
  Huybrechts, Orlov, Trautman, van Geemen (Def. 4.9) and Markman's [JEMS 2023, Prop. 1.7] that the proofs use are
  proved in [`WeilClasses/External/`](WeilClasses/External) (Section 2).
- **Conditional results.** Theorem 1.5.1 and Corollary 1.6.1 are proved from named hypotheses, each a class in their
  statements (Section 2): the paper's own sheaf-theoretic §§7–9, in the cohomological form "κ₃(E) is algebraic near
  X × X̂ wherever κ(E) is of Hodge type" ([`SecantSheafDeformation`](Challenge.lean#L660)); and results from algebraic geometry that Lean
  does not have: pullbacks and products of algebraic cycles, the Lefschetz (1,1) theorem, [Voisin, §4.2],
  [van Geemen, Th. 5.2(3)], [Schoen, Prop. 10], [Moonen–Zarhin 1995, Th. 2.11], [Ramón-Marí, Th. 4.11] and
  [Moonen–Zarhin 1999]. Three results of §10 assume two parts of [Igusa, Prop. 3]. For the system in which every class
  is algebraic, the seven hypotheses on algebraic classes hold, and `X × X̂` is a polarized abelian sixfold of Weil
  type with discriminant `-1` ([`WeilClasses/Main/Instances.lean`](WeilClasses/Main/Instances.lean)). The hypotheses about Hodge structures
  ([van Geemen, Th. 5.2(3)] and the two Moonen–Zarhin theorems) and the two parts of [Igusa, Prop. 3] are published
  results with no instance in Lean.
- **Build and axioms.** `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean) and no `axiom`.
  [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library, every paper result and every Challenge theorem
  depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- **Challenge and Comparator.** [`Challenge.lean`](Challenge.lean) states, in Mathlib's vocabulary, Theorem 1.4.1(3) and (4),
  Theorem 1.5.1, Corollary 1.6.1, and five theorems that compare its definitions with the paper (the norm of `K`,
  `f² = -d`, `X × X̂` in its period domain, its discriminant `(-1)ⁿ`, the rank `8d` of `E`). Palomar's Comparator
  accepts [`Solution.lean`](Solution.lean) (Lean kernel and NanoDa).
- **Statements changed.** Eleven statements of the paper are false or misprinted as printed; the formalization
  states the closest correct version, each correction agreed with the project owner or an obvious misprint (E2, E5,
  E6, E9, E10, E21, E23, E24, E26 and two misprints in E28; Section 6 lists them). The basis given in Example 10.2.2
  is also false as printed (E28); it needs no corrected statement, because the value computed there is the same for
  the corrected basis.
- **Routes.** The route check ([`scripts/route_check.py`](scripts/route_check.py)) compares, for each result, the results its formal proof uses
  with those the paper's proof cites. Every difference is recorded with its reason in [`docs/route_differences.tsv`](docs/route_differences.tsv),
  and the check passes.
- **Review.** The statements were reviewed against the TeX source by five independent agents before any proof was
  written, the proofs by five other agents after they were written, and the findings below by a separate verifier.
  No person has reviewed the proofs.

## 1. Summary

- **Errors.** Eleven statements are false or misprinted as printed, each with a correct version that the paper's
  argument proves: the equivariance in Proposition 1.3.1 (`m ⊗ m†` must be `m ⊗ m`, E2); the second sentence of
  Lemma 2.2.1 for odd `n` (E5); `Spin(V_K)_{ℓ₁,ℓ₂}/±1 ≅ GL(W₁)` on `K`-points (E6); Remark 2.2.5 (E9); the sign in
  Remark 2.3.1 (E10); the sign in Lemma 6.3.2 (E21); (8.1.2), which needs `End_ℚ(X) = ℚ` (E23); the involution in §8.1
  (E24); Remark 10.1.2(1) for `d = 0` (E26); and misprints in Lemma 2.2.2 and in the expansion of `β` in §8.1 (E28).
  The basis claimed in Example 10.2.2 is also false as printed (E28); it needs no corrected statement, because
  `J(2 - dΘ²)` is the same for both orientations. §6.4 claims transitivity on all complementary pairs, but uses it
  only for even pairs (E22). The author has since corrected the definition of the integral Clifford algebra in §2.1,
  which has `2`-torsion as printed (E4). Steps of proofs are wrong in Lemma 2.2.1 (E5), Lemma 2.3.2(1) (E11),
  Lemma 3.1.2 (E16) and Lemma 6.3.2 (E21), and the paper states the orientation of the complex structure of `X × X̂`
  in two incompatible ways (E12). None of this affects Theorem 1.4.1, Theorem 1.5.1 or Corollary 1.6.1.
- **Gaps.** Claims used without proof, all true: the passage to all of moduli and the cases `d = 1, 2` in the proof of
  Theorem 1.5.1 (E3); irreducibility, density and complete reducibility for the arithmetic group `Spin(V)_P` and the
  rational groups `Spin(V_ℚ)_P`, `Spin(V_ℚ)_w` (E8, E19, E20, E27); the existence of a real lift in Remark 2.4.3
  (E13); the computation of Proposition 2.4.4 for real classes (E14); the non-emptiness of `Ω_P` for a general `P`
  (E17); the uniqueness of the secant through `w` (E7, E25); and smaller steps (E15, E18). One claim is unproved and
  unused (E1).
- **Missing hypotheses.** One: (8.1.2) needs `End_ℚ(X) = ℚ` (E23, Section 4).
- **Redundant hypotheses.** Several statements hold without some of their hypotheses; the most notable is that
  Lemma 6.2.3 needs `Ξ_P` only nondegenerate, not ample (Section 5).
- **Use of cited results.** Every cited result is applied correctly, except [Igusa, Lemma 1], which is applied on
  `K`-points where its conclusion holds only over an algebraically closed field (E6);
  [Golyshev–Lunts–Orlov, Prop. 3.2.1(e)], which needs the corrected integral Clifford algebra (E4); and
  [Chevalley, §3.3, Lemma 1], quoted for all complementary pairs, where it gives transitivity within each family (E22)
  (Section 2).
- **Proofs.** Every proof follows the paper's argument, with the departures of Section 7: the proof of
  Proposition 6.1.2 (and with it Lemma 6.2.5) is algebraic instead of the paper's reduction to abelian surfaces, and
  Lemma 4.0.2 is proved by transitivity instead of a dimension count (both authorized by the project owner); the
  other departures are single steps, where the paper's step is wrong or has a gap, needs mathematics Lean lacks
  (Zariski density and closures, identity components, Hodge theory), or has no meaning in the model (line bundles,
  isogenies, sheaves, the Hodge structure of `C(V)`, fields of definition of algebraic groups).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

Each statement is the case the paper uses; the README of each directory of [`WeilClasses/External/`](WeilClasses/External) says how the Lean
form relates to the source.

| Result | Where the paper uses it | Source | Theorem in `External/` |
|---|---|---|---|
| Spin-invariance of the Mukai pairing; `m_v` self-adjoint | §2.1 (TeX l. 728–741) | [Chevalley, III.2.1, III.2.2] | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159) |
| Pure spinors: existence and uniqueness, the two families, secants, pairings | §2.2, Lemma 2.2.1, Remark 2.2.3 | [Chevalley, III.1.4, III.1.5, III.1.12, III.2.4] | [`chevalley_III_1_4_exists`](WeilClasses/External/Chevalley/Sec2_2.lean#L252), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_5_families`](WeilClasses/External/Chevalley/Sec2_2.lean#L271), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Chevalley's isomorphism `S ⊗ S ≅ C(V)`, its equivariance, `φ(u ⊗ u)` spans `⋀^{2n}W` | Lemma 2.2.6, §6.3, §6.4 | [Chevalley, III.3.1, III.3.2] | [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414) |
| Transitivity on pairs of complementary maximal isotropic subspaces (even family) | §6.4 (TeX l. 2964) | [Chevalley, §3.3, Lemma 1] | [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465) |
| `exp(u) ∈ Spin(V)` for `u ∈ ⋀²H¹` and its action | (2.4.4) | [Chevalley, III.1.7] | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| `g u = c u` with `c² = det(ρ(g)\|_W)` | Lemma 3.1.1 | [Chevalley, III.3.2, III.4.5] | [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| The filtration of `C(V)`, its graded pieces, equivariance | §2.3 (TeX l. 1064–1077), Lemma 6.1.1 | [Chevalley, II.1.6, §3.3, p. 85] | [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_surjective`](WeilClasses/External/Chevalley/Sec2_3.lean#L270), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_sec3_3_conj_mem`](WeilClasses/External/Chevalley/Sec2_3.lean#L336), [`chevalley_sec3_3_equivariant`](WeilClasses/External/Chevalley/Sec2_3.lean#L345), [`chevalley_p85_transport_graded`](WeilClasses/External/Chevalley/Sec2_3.lean#L392) |
| `Spin(V)` stabilizer of a pair of pure spinors; its image in `GL(W₁)`; `ℓ̃ᵢ⊗ℓ̃ᵢ ≅ detᵢ` | §2.2 (TeX l. 798–808), Lemma 2.2.2 | [Igusa, Lemma 1] | [`igusa_lemma1_ker`](WeilClasses/External/Igusa/Sec2_2.lean#L1259), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Stabilizer of `a u₁ + b u₂` | Remark 2.2.3 (TeX l. 831) | [Igusa, Lemma 2 and the remark after it] | [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354), [`igusa_lemma2_stab_even`](WeilClasses/External/Igusa/Sec2_2.lean#L1374) |
| The elements `s(λ)` | Remark 2.4.3 | [Igusa, §2] | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Invariance of the quartic `J`; the stabilizer of `1 + c[pt_X]` | §10 | [Igusa, Prop. 3, Lemma 2] | [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119) |
| `m : C(V) → End(S)` is an isomorphism (over a field, and integrally for the corrected `C(V)`, E4) | §2.1 (TeX l. 698), Lemma 2.2.6 | [Golyshev–Lunts–Orlov, Prop. 3.2.1(e)] | [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`glo_prop3_2_1_e_integral`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L460) |
| `ρ'_g` preserves the filtration (6.1.5), graded action `ρ_g` | §6.1 (TeX l. 2228) | [Golyshev–Lunts–Orlov, Prop. 4.3.7, Cor. 4.3.8] | [`glo_prop4_3_7`](WeilClasses/External/GolyshevLuntsOrlov/Sec6_1.lean#L36) |
| `ρ'_g = ch(N_g) ∪ ρ_g`, `c₁(N_g)` integral for integral `g` | (6.1.8) | [Orlov, Th. 2.10] | [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49) |
| The cocycle identity | (6.1.9) | [Huybrechts, Ex. 9.41] | [`huybrechts_ex9_41`](WeilClasses/External/Huybrechts/Sec6_1.lean#L35) |
| `φ_𝒫` is Poincaré duality up to sign; its square | §6.3, footnote; Lemma 6.3.2 | [Huybrechts, Lemma 9.23, Cor. 9.24] | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| A symmetric form `B` gives an equivariant isomorphism `C(V) ≅ ⋀V` | Remark 2.3.1 | [Trautman, Th. 1(i)] | [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| The condition on the polarization of an abelian variety of Weil type | Corollary 3.2.3 | [van Geemen, Def. 4.9] | [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| `span{w, h}` is a `ℚ(√-d)`-secant | Example 8.2.2 | [Markman, JEMS 25 (2023), Prop. 1.7] | [`markmanM2_prop1_7`](WeilClasses/External/Markman/Sec8_2.lean#L472) |

The proofs follow the sources where the model allows, and otherwise argue in the model (the READMEs say which).
[Orlov, Th. 2.10] is proved from the computation behind Proposition 6.1.2, whose proof here does not use it.

### Assumed

Each assumption is a `Prop`-valued class or definition, named after its source, and appears in the signature of every
statement whose proof uses it. None is an axiom.

| Result | Where the paper uses it | Source | Hypothesis | What Lean lacks |
|---|---|---|---|---|
| The paper's own §§7–9: the semiregular twisted sheaf `B` on `Y = (X × X̂)/Ḡ` (Lemma 9.3.11), Conjecture 7.3.9 for families of abelian varieties (§7.4, from [Buchweitz–Flenner, Th. 5.1]), `q^*κ(B) = κ(E)` | Proof of Theorem 1.5.1 (TeX l. 555–570, 6843) | the paper, §§7–9 | [`SecantSheafDeformation`](Challenge.lean#L660) | coherent and twisted sheaves, Atiyah classes, the semiregularity map, deformation theory |
| Pullbacks of algebraic cycles along homomorphisms | Theorem 1.5.1 (`η(K)` acts by correspondences, TeX l. 6845); isogeny invariance | standard | [`PullbackClosed`](Challenge.lean#L353) | algebraic cycles, Chow groups, the cycle class map |
| `[A]` and products of algebraic classes are algebraic | Theorem 1.5.1 (`h³`), Corollary 1.6.1 | standard | [`SubalgebraClosed`](Challenge.lean#L359) | the same |
| The Lefschetz (1,1) theorem | Theorem 1.5.1, Corollary 1.6.1 | standard | [`LefschetzOneOne`](Challenge.lean#L365) | the same, line bundles |
| The locus where a class stays algebraic is a countable union of closed algebraic subsets (TeX l. 6847); assumed in the form needed in the model: closed analytic subsets of a component of the period domain | Theorem 1.5.1 (TeX l. 6847) | [Voisin, *The Hodge conjecture*, §4.2] | [`VoisinLocus`](Challenge.lean#L390) | relative Hilbert schemes, analytic geometry |
| Weil-type abelian varieties with given `K` and discriminant form one family | Theorem 1.5.1 (TeX l. 283; E3) | [van Geemen, Th. 5.2(3)] | [`VanGeemenModuli`](Challenge.lean#L405) | the classification of Hermitian forms over number fields (Landherr), Hermitian symmetric domains |
| HW classes of sixfolds of discriminant `-1` give those of fourfolds | Corollary 1.6.1 (TeX l. 600) | [Schoen, Prop. 10] | [`SchoenDegeneration`](Challenge.lean#L425) | degenerations of abelian varieties, algebraic cycles |
| Hodge ring of a simple abelian fourfold | Corollary 1.6.1 (TeX l. 603) | [Moonen–Zarhin 1995, Th. 2.11] | [`MoonenZarhinSimple`](Challenge.lean#L432) | Mumford–Tate groups, their classification |
| Hodge conjecture for products of two abelian surfaces | Corollary 1.6.1 (TeX l. 604) | [Ramón-Marí, Th. 4.11] | [`RamonMariProducts`](Challenge.lean#L447) | the same, algebraic cycles |
| Hodge ring of `B × E`, `B` a simple threefold | Corollary 1.6.1 (TeX l. 604) | [Moonen–Zarhin 1999, Prop. 3.8, Th. 0.1(i)] | [`MoonenZarhinLowDim`](Challenge.lean#L454) | the same |
| The normal form `1 + 2s[pt_X]` over fields contained in `ℂ` | Lemma 10.1.1, Remark 10.1.2(2), Lemma 10.2.1 | [Igusa, Prop. 3, last paragraph of the proof] | [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034) | the classification of the generic `Spin(12)`-orbit on the half-spin representation |
| Level sets of `J` over subfields of `ℂ` are single orbits | Remark 10.1.2(1) | [Igusa, Prop. 3] | [`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2072) | the same, and Galois cohomology of special unitary groups |

Each hypothesis was checked against its source as carefully as a statement, except the two parts of [Igusa, Prop. 3],
whose attribution is unchecked (Igusa's paper was not available). [`SecantSheafDeformation`](Challenge.lean#L660) assumes only the
deformation along the Hodge locus of `κ(E)`: that `κ(E)` stays of Hodge type on the Weil-type deformations is the
paper's Corollary 1.3.2, which is proved. [`VanGeemenModuli`](Challenge.lean#L405) holds trivially for `m = 0` (the polarization is then `0`)
and for `m ≥ 1` by Landherr's theorem and the connectedness of the type `I_{m,m}` domain. [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034) is
implied by [`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2072) on subfields of `ℂ` (checked in Lean). The project owner chose to keep these
results as hypotheses and to formalize them in layers later.

### Standard facts used without citation

| Fact | Where | In the formalization |
|---|---|---|
| `Spin(V)` has index `4` in `G(V)`, is generated by products `v₁v₂` with `(vᵢ, vᵢ) = ±2`; `N(g) = g·τ(g) = ±1` | §2.1 (TeX l. 709, 720, 736) | proved (`PureSpinor/Sec2_1.lean`) |
| `ker(ρ : Spin → SO) = {±1}` | throughout | Tau Ceti (`mem_ker_spinToOrthogonal_iff`) |
| Zariski density of rational points; Borel density of arithmetic subgroups | Lemmas 2.2.4, 2.2.7, Cor. 4.0.4, Lemmas 6.2.3, 10.2.1 | replaced by transvections, weights and invariant pairings (E8, E19, E20, E27) |
| Hard Lefschetz | Lemma 6.2.3; Corollary 1.6.1 (`h² ∪ : H^{1,1} → H^{3,3}`) | algebraic `sl₂` arguments ([`lemma6_2_3_injective`](WeilClasses/Orlov/Sec6_2.lean#L2104); `AbelianVariety/Lemmas.lean`) |
| Poincaré reducibility; sub-Hodge structures of an abelian fourfold | Corollary 1.6.1 (TeX l. 603–604) | proved in the model (`AbelianVariety/Lemmas.lean`) |
| Gram–Schmidt for Hermitian forms; Sylvester's law of inertia | Lemma 3.1.2 | proved; Mathlib |
| Witt's theorem on the transitivity of isometries | §6.4 | through [Chevalley, §3.3, Lemma 1] |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
|---|---|---|
| [Chevalley] (all items above) | §§2.1–2.4, 3.1, 6.3, 6.4 | Correct, except at §6.4, which quotes transitivity for all complementary pairs, where it holds only within each family; only even pairs are needed (E22). |
| [Igusa, Lemma 1] | §2.2 (TeX l. 798–808) | Applied loosely: it describes the algebraic groups, and the paper states its conclusion `Spin(V_K)_{ℓ₁,ℓ₂}/±1 ≅ GL(W₁)` on `K`-points, where the image is the square-determinant subgroup (E6). Nothing downstream depends on the difference. |
| [Igusa, Lemma 2 and remark], [Igusa, §2] | Remark 2.2.3, Remark 2.4.3, Lemma 10.1.1 | Correct. |
| [Igusa, Prop. 3] | §10 | Not checked against Igusa's paper (not available). As quoted it fails for `d = 0` (E26); for `d ≠ 0` over a field that is not algebraically closed it also needs a Galois-cohomology step. Assumed (Section 2). |
| [Golyshev–Lunts–Orlov, Prop. 3.2.1(e)] | §2.1 | Correct for the Clifford algebra of the quadratic form; the paper's integral `C(V)` (E4) is not that algebra. |
| [Golyshev–Lunts–Orlov, Prop. 4.3.7, Cor. 4.3.8], [Orlov, Th. 2.10], [Huybrechts, Ex. 9.41, Cor. 9.24], [Trautman, Th. 1(i)], [van Geemen, Def. 4.9], [Markman 2023, Prop. 1.7] | §§2.3, 3.2, 6.1, 6.3, 8.2 | Correct. |
| [Huybrechts, Lemma 9.23] | §6.3, footnote | Correct with `PD_k` read as the inverse of `PD_X` for `X̂ → X` (E21). |
| [van Geemen, Th. 5.2(3)] | §1.1; implicitly at the end of the proof of Theorem 1.5.1 | Correct, but not invoked where it is needed (E3). |
| [Voisin, §4.2], [Schoen, Prop. 10], [Moonen–Zarhin 1995, 1999], [Ramón-Marí] | Theorem 1.5.1, Corollary 1.6.1 | Assumed; applied in the form stated. |
| [Buchweitz–Flenner, Th. 5.1], Conjecture 7.3.9 | §§7–9 | Part of the assumed [`SecantSheafDeformation`](Challenge.lean#L660); not audited (sheaf theory). |

Citations that give context only and are not used in proofs include [Abuaf, Rem. 2.1.1] (the tangent variety of
`V(J)`, §10), the invariant ring of `Spin(12)` on `S⁺` (§10.1), and the motivating references of §1.

## 3. Errors and gaps in the paper

Every item was checked against the TeX source by someone other than its recorder. Computations and counterexamples
were redone in an exact model of the paper's conventions (its Clifford algebra, Mukai pairing, orientation, and the
maps of Orlov and Chevalley), and the statements that the formalization corrects are proved in their corrected form.
Unless an item says otherwise, the paper's results that depend on it still hold.

**E1. §1.3 (TeX l. 411), an unproved claim.** "The two integral `Spin(V)`-representation `ρ` and `ρ'` are
non-isomorphic, but they are isomorphic once tensored with `ℚ`." The first half is not proved and is not used. It is
not formalized.

**E2. Proposition 1.3.1, diagram (1.3.1), the sentence after (1.3.2) (TeX l. 412–438), an error.** The intro states
that `φ ∘ (id ⊗ τ)` and `φ̃` are `Spin(V)`-equivariant "where the domain is the representation `m ⊗ m†`". Since
`(id ⊗ τ)(m_g ⊗ m_g†)(id ⊗ τ) = m_g ⊗ τ m_g† τ = m_g ⊗ m_g`, equivariance for `m ⊗ m†` would need `τ m_g τ = m_g`,
which fails. Counterexample: `n = 1`, `g = 1 + e₁e₂`, `y = 1 ⊗ 1`; the degree-`0` part of `φ(id ⊗ τ)((m_g ⊗ m_g†) y)`
is `-2`, and that of `ρ'_g(φ(id ⊗ τ) y)` is `0`. The correct statement, which the body uses ((6.1.4) and TeX
l. 2903–2904), is equivariance for `m ⊗ m` (equivalently, `φ` is equivariant for `m ⊗ m†`). The proof of
Corollary 1.3.2 uses the correct version. Lean: [`proposition1_3_1_equivariant`](WeilClasses/Orlov/Intro.lean#L56), [`equation1_3_2_equivariant`](WeilClasses/Orlov/Intro.lean#L88) with
`m ⊗ m`.

**E3. Theorem 1.5.1 and its proof (TeX l. 563, 572–578, 6841–6849), two gaps.**

- The proof uses Theorem 1.4.1, which assumes `d ≥ 3` (TeX l. 497, 500), while the theorem claims every positive `d`.
  The footnote at TeX l. 563 ("If `d` is odd replace it with `4d` and note that `ℚ(√-4d) = ℚ(√-d)`") turns `d = 1`
  into `4`; `d = 2` needs the same device (`d ↦ 8`), which the paper does not state. Lean: [`theorem1_5_1`](WeilClasses/Main/Theorems.lean#L518) reduces
  `d ∈ {1, 2}` to `4d` ([`main_exists_four_mul`](WeilClasses/Main/Theorems.lean#L118)).
- The proof ends with "the locus contains the whole irreducible component of moduli of deformations of
  `(X × X̂, η, h)`" (TeX l. 6847). That every polarized abelian sixfold of Weil type for `K` with discriminant `-1`
  lies, up to isogeny, in this component is [van Geemen, Th. 5.2(3)], stated in §1.1 (TeX l. 283) but not invoked in
  the proof. The author's ICM survey (arXiv:2509.23403, §11.5) supplies this step. Lean: the step uses the hypothesis
  [`VanGeemenModuli`](Challenge.lean#L405) explicitly ([`main_theorem1_5_1_of_three_le`](WeilClasses/Main/Theorems.lean#L418)).

**E4. §2.1 (TeX l. 673–677, 697–698), an error corrected by the author.** `C(V)` is defined over `ℤ` as the quotient
of the tensor algebra by `v₁ · v₂ + v₂ · v₁ = (v₁, v₂)_V` (2.1.1), and `m : C(V) → End(S)` is said to be "in fact an
isomorphism, by [GLO, Prop. 3.2.1(e)]". The relation gives only `2v² = (v, v)_V`, so `v² - ½(v, v)_V` is a nonzero
`2`-torsion element, and `m`, whose target is torsion-free, is not injective. The author's correction (E. Markman,
*Suggested program for JAVA 2026*, 14 February 2026, footnote 3): "One needs to use the quadratic form
`Q(•) = ½(•,•)_V` and not the bilinear pairing, as was unfortunately done in early versions of [M2, Sec. 2.1], in
order to avoid two-torsion in `C(V)`", where [M2] is arXiv:2502.03415v2. Only integral statements are affected (those
of §2.1, and the integral isomorphism `φ : S ⊗ S → C(V)` in the proof of Lemma 2.2.6, TeX l. 938–959); the rational
statements and the main theorems are not. Lean: `C(V)` is the Clifford algebra of `Q(θ, w) = θ(w)` ([`WeilClasses.Q`](WeilClasses/Spinor/Defs.lean#L58)),
and the integral `C(V)` is the subring `CZ` of `C(V_ℚ)` generated by the lattice: the corrected definition
([`glo_prop3_2_1_e_integral`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L460)).

**E5. Lemma 2.2.1 (TeX l. 773–790), an error in the statement and in the proof (odd `n`).**

- The second sentence, "The restriction of the pairing `(•,•)_S` to `P` is definite, if and only if `W₁ ∩ W₂ = (0)`",
  is false for odd `n`: the Mukai pairing is then alternating on `S⁺` ("anti-symmetric", TeX l. 327), so its
  restriction to a plane is never definite. Example: `n = 3`, `P = P_Θ` of (2.4.5), `d = 3`; the Gram matrix of
  `(•,•)_S` on `{Re exp(u), Im exp(u)/√d}` is `[[0, -12], [12, 0]]`. For even `n` the sentence is right. Correct
  version for odd `n`: the restriction is nondegenerate if and only if `W₁ ∩ W₂ = 0`. Only "non-isotropic" is used
  later (TeX l. 846, Assumption 2.4.1). Lean: [`lemma2_2_1_even`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1569) (as printed), [`lemma2_2_1_odd`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1645) (corrected).
- The proof of the first sentence computes `(λ₁, λ₁) = (a, a)_S - (b, b)_S + 2i(a, b)_S` and concludes "`(a, a) = 0`,
  if and only if `W₁ ∩ W₂ ≠ 0`" (TeX l. 783–789). Both steps assume a symmetric pairing; for odd `n`, `(a, a) = 0`
  always. The first sentence still holds for every `n` (for odd `n`, the Gram matrix is `(a, b)_S [[0, 1], [-1, 0]]`).
  Also "`λ₁ = a + ib`, with `a, b ∈ S⁺_ℚ`" is possible only for `K = ℚ(i)`; read `λ₁ = a + √-d b`. Lean: [`lemma2_2_1`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1529)
  keeps `(λ₂, λ₁) = (-1)ⁿ(λ₁, λ₂)` ([`mukai_swap_of_mem_Splus`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L354)), a departure at one step (Section 7).

**E6. §2.2, after Lemma 2.2.1 (TeX l. 798–799), an error.** "The quotient `Spin(V_K)_{ℓ₁,ℓ₂}/{±1}` is isomorphic to
`GL(W₁)`, and so to `GL_{2n}(K)`." On `K`-points the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)` is the subgroup of
elements whose determinant is a square: by TeX l. 806, `det₁ = χ₁²`; for `t ∉ K^{×2}` the element `diag(t, 1, …, 1)`
of `GL(W₁)` (acting dually on `W₂`) has no lift in `Spin(V_K)`. The statement holds for the algebraic groups (over an
algebraically closed field), which is the setting of [Igusa, Lemma 1]. The argument only uses the characters `detᵢ`
and `Spin(V_K)_P ≅ SL(W₁)`, which are unaffected. Lean: [`range_restrictW₁`](WeilClasses/PureSpinor/Stabilizer.lean#L524) (the square-determinant image), from
[`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299).

**E7. Remark 2.2.3 (TeX l. 831–836), a gap.** "In particular, `w` determines `P` and `ℙ(P)` is the unique secant to the
spinor variety through `w`." The remark speaks of connected components of the stabilizer, so it concerns the
algebraic group; read that way, `P` is the plane fixed by the identity component. That an arbitrary secant through
`w` has transversal pure spinors (so that it is the fixed plane of its own stabilizer) is not argued for odd
`n ≥ 5`. It holds for every `n ≥ 3`: `ker m_w = 0` forces transversality. Lean: [`remark2_2_3_unique_secant`](WeilClasses/PureSpinor/Stabilizer.lean#L951), via the
joint kernel of the infinitesimal stabilizer (a departure, Section 7).

**E8. Lemmas 2.2.4 and 2.2.7 (TeX l. 856–1036), a gap.** Lemma 2.2.4 (about the rational group `Spin(V_ℚ)_P`) uses
that `W₁` and `W₂` are absolutely irreducible and non-isomorphic under it, which needs the density of rational points
and `n ≥ 2` (for `n = 1`, `W₂ ≅ W₁* ≅ W₁` under `SL₂`). Lemma 2.2.7 (about the integral group `Spin(V)_P`) uses
"`⋀ᵏWᵢ`, `i = 1, 2`, are dual irreducible `Spin(V)_P` representation[s]" (TeX l. 1014), Schur's lemma and
`⋀ᵃW₁ ≇ ⋀ᵇW₁` for `a ≠ b`, `{a, b} ≠ {0, 2n}`, which need Borel density in `SU(n, n)`. All are true. Lean: Lemma 2.2.4
via unitary transvections in `Spin(V_ℚ)_P` and a Schur step ([`s22b_E_mem_spinPℚ`](WeilClasses/PureSpinor/Lemma2_2_4.lean#L866), [`s22b_Dop_mem_nK`](WeilClasses/PureSpinor/Lemma2_2_4.lean#L1094),
[`s22b_eigen_of_commute`](WeilClasses/PureSpinor/Lemma2_2_4.lean#L421)); Lemma 2.2.7 by computing the invariants with the weights and root operators of `sl(W₁)`,
without irreducibility.

**E9. Remark 2.2.5 (TeX l. 887–891), an error.** "`P` is contained in the Hodge ring of `X` for every complex structure
`I` … which belongs to `ρ(Spin(V_ℝ)_P)`." Counterexample: `n = 2`, `X = E × E` with `E = ℂ/ℤ[i]`, `K = ℚ(i)`, `P`
spanned by the real and imaginary parts of `dz₁ ∧ dz₂` (so `P ⊆ H^{2,0} ⊕ H^{0,2}`, non-isotropic, with `W₁ = V^{1,0}`,
`W₂ = V^{0,1}` transversal). The lift `g₀ = ϖ̃(e^{iπ/4})` of Remark 2.4.3 acts by `-1` on `H^{2,0} ⊕ H^{0,2}` and by
`+1` on `H^{1,1}`, `H⁰`, `H⁴`; so `-g₀ ∈ Spin(V_ℝ)_P` and `ρ(-g₀) = I`, while `P` is not of Hodge type. Correct
version: if the whole circle `{cos θ + sin θ I}` lies in `ρ(Spin(V_ℝ)_P)`, then `P` lies in the Hodge ring. The remark
is an aside; Lemma 4.0.3(2) uses the circle argument. Lean: [`remark2_2_5`](WeilClasses/PureSpinor/Lemma2_2_6.lean#L2461) (circle form).

**E10. Remark 2.3.1 (TeX l. 1079–1088), an error (sign).** "The right hand side is `-1/2` times the alternating form
of the Poincaré line bundle … and so equal to `½c₁(𝒫)`." The sign of `c₁(𝒫)` is forced by the formula for
`Ψ_{𝒫⁻¹[n]}` in the footnote of §6.3 (TeX l. 2700), Lemma 6.3.1, Lemma 6.1.1 and Proposition 6.1.2: all four hold for
`c₁(𝒫) = +Σ eᵢ ∪ fᵢ` and fail for the opposite sign. With that sign, identifying alternating forms on `V` with classes
through `(•,•)_V`, `B̄₀ = -½c₁(𝒫)` (checked for `n = 1, 2, 3`). The remark motivates; no proof uses it. Lean:
[`remark2_3_1_B0bar_eq_neg_half_c1P`](WeilClasses/Chevalley/Sec2_3.lean#L473).

**E11. Lemma 2.3.2(1), proof (TeX l. 1139–1147), an error in the proof.** The image of the commutator
`[pt_X][pt_X̂] - [pt_X̂][pt_X]` in `⋀^{4n-2}V` is printed as "`2 Σ_{k=1}^n …`"; it is `(-1)ⁿ Σ_{k=1}^n …` (`n = 1`:
the commutator is `1 - e₁f₁ - e₂f₂`, and its image in `⋀²V` is `-(e₁ ∧ f₁ + e₂ ∧ f₂)`). The lemma holds: the degrees are
`4n - 2` and `4n`. Lean: [`lemma2_3_2_1`](WeilClasses/Chevalley/Sec2_3.lean#L1348) (corrected step).

**E12. §2.4, the orientation of the complex structure of `X × X̂` (TeX l. 885, 918, 1265–1275, 1370), an
inconsistency.** Two sets of passages fix `I` in opposite ways. TeX l. 885 ("the Hodge decomposition with respect to
the complex structure of `X × X̂`"), the footnote at l. 918 and Lemma 3.2.1 take `I` to act by `+i` on
`H^{1,0}(X × X̂)`; the footnote at l. 1265–1275, with its rule that the complex structure of the dual is composition
with `-I_X`, gives the opposite orientation. With the first convention, `g_P` is positive definite, not negative (TeX
l. 1370): for `n = 1`, `d = 1` and `x = (-2e₁, 2f₁)`, `g_P(x, x) = 8`, and the step "the two summands are
non-negative" (TeX l. 1431) fails. With the footnote's convention, Lemma 2.4.2, Proposition 2.4.4 and Lemma 4.0.1 hold
as printed, and the passages at l. 885 and 918 are off by complex conjugation, which does not affect statements about
Hodge types. Lean: the library's [`productStructure`](WeilClasses/Hodge/Defs.lean#L62) follows the footnote's convention; the statements of record use
the standard structure `JX`, its negative (Section 6).

**E13. Remark 2.4.3 (TeX l. 1302–1307), a gap.** "`ϖ̃(e^{iπ/4})` of `Spin(V_ℂ)` which must be already in `Spin(V_ℝ)` as
it maps to `I`." An element of `Spin(V_ℂ)` mapping to a real element `γ` is real up to sign only if `γ ∈ ρ(Spin(V_ℝ))`;
`-id` on a real hyperbolic plane has no real lift. Here it holds: `I = G²` with `G = (1 + I)/√2 ∈ SO(V_ℝ)`, so the
spinor norm of `I` is a square. The subspaces are also named inconsistently (`M`, `N`, then `L`, `M` at l. 1302;
`L = V^{1,0}`, `N = V^{0,1}` at l. 1306). Lean: [`remark2_4_3_complexStructure`](WeilClasses/WeilType/Basic.lean#L1382) (`s24a_exists_spin_lift`).

**E14. Proposition 2.4.4, proof (TeX l. 1374), a gap.** "Let `x` be a class in `V_ℚ` …": `g_P` is a real form, and
negativity on `V_ℚ ∖ 0` gives only semi-definiteness on `V_ℝ`. The same computation works for `x ∈ V_ℝ`. Lean:
[`proposition2_4_4`](WeilClasses/WeilType/Theta.lean#L1690), for real `x`.

**E15. Lemma 3.1.1 (TeX l. 1475), a gap (minor).** "The homomorphism `ρ` restricts to an injective homomorphism from the
stabilizer `Spin(V_ℚ)_P` into `SO₊(V_ℚ)_f`, since the kernel of `ρ` has order two." The "since" justifies only
injectivity; that the image commutes with `f` and has determinant `1` on `Wᵢ` follows from TeX l. 806
(`det_i = χ_i² = 1`). §4 uses the real version (TeX l. 1713, 1832), which is not stated; the proof transfers. Lean:
[`lemma3_1_1`](WeilClasses/Hermitian/Defs.lean#L1580), [`lemma3_1_1_real`](WeilClasses/Hermitian/Defs.lean#L1720).

**E16. Lemma 3.1.2 (TeX l. 1496–1538), a reading and errors in the proof.**

- "`SO₊(V_ℚ)_f` is a finite index subgroup of the subgroup `SU(V_ℚ, H)` of `SL(V_ℚ)` leaving `H` invariant": the
  literal subgroup is the unitary group `U(H)` (its elements have `ℚ`-determinant `Nm(det_K) = 1` automatically), and
  `[U(H) : SU(H)] = |K¹| = ∞`. The statement is read with `SU(V_ℚ, H)` the special unitary group, as its name and the
  dimension `(2n)² - 1` in Lemma 4.0.2 indicate.
- "The norm character has finitely many values on `SO(V_ℚ)`" (TeX l. 1529) is false: the spinor norm maps `SO(V_ℚ)`
  onto `ℚ^×/ℚ^{×2}` (the product of the reflections in `v`, `w` with `Q(v) = q`, `Q(w) = 1` has spinor norm `q`).
  "Since the number of units is finite" (TeX l. 1537) needs integrality: `det M` lies in `K¹`, which is infinite and
  contains non-integral elements such as `(3 + 4i)/5`.
- The statement holds with index `1`: the spinor norm is trivial on `SU(V_ℚ, H)`, so `SO₊(V_ℚ)_f = SU(V_ℚ, H)`.
- "Multiplying by `√d`" (TeX l. 1508) should be "by `d`".
- Lean: [`lemma3_1_2_finiteIndex`](WeilClasses/Hermitian/Defs.lean#L3078), [`lemma3_1_2_eq_SUH`](WeilClasses/Hermitian/Defs.lean#L3094) (a departure at one step, Section 7).

**E17. Lemma 4.0.1 (TeX l. 1729–1753), a gap.** The non-emptiness of `Ω_P` is proved through Proposition 2.4.4
("the negative definite bilinear form `g_P` of Proposition 2.4.4 is `-g_I`", TeX l. 1743), which is about the plane
`P_Θ` of (2.4.5) only, while `Ω_P` is defined for every `P` satisfying Assumption 2.4.1. It holds for every such `P`:
the Hermitian form `H` has signature `(n, n)` (Lemma 3.1.2); take `I = J` on a positive and `I = -J` on a negative
`J`-invariant half (`J = f/√d`). Lean: [`lemma4_0_1_nonempty`](WeilClasses/PeriodDomain/Defs.lean#L3320) (and [`productStructure_mem_OmegaP`](WeilClasses/PeriodDomain/Defs.lean#L3437) for `P_Θ`, as in the
paper).

**E18. §4 (TeX l. 1808–1811), an unproved claim.** "The identity component of its inverse image in `Spin(V_ℝ)` defines a
real Hodge structure of weight `0` on `S⁺_ℝ`." No argument is given that the weights are integers. It is true. Lean:
[`Spq_iSupIndep`](WeilClasses/PeriodDomain/SemiHodge.lean#L1669), [`conj_Spq`](WeilClasses/PeriodDomain/SemiHodge.lean#L1675).

**E19. Corollary 4.0.4 (TeX l. 1846–1847), a gap.** "A class `α` in `⋀²(V_ℚ)` is of type `(1,1)` … if and only if
`I(α) = α`. Hence the statement holds for classes in `⋀²(V_ℚ)^{Spin(V)_P}`." Here `Ĩ` lies in the real group
`Spin(V_ℝ)_P`, while `α` is only known to be invariant under the integral group; this needs Borel density. Filled: the
invariants are `ℚ Ξ_P` (Lemma 2.2.7), and `Ξ_P` is of type `(1,1)` for every `I ∈ Ω_P`. Lean: [`corollary4_0_4`](WeilClasses/PeriodDomain/SemiHodge.lean#L2562).

**E20. §6.2 and the proof of Lemma 6.2.3 (TeX l. 2414–2417, 2427, 2462–2464), three gaps.** "The coset
`β_{k+1} + β_k ∪ H²` is `Spin(V)_P`-invariant. Hence, `β_{k+1}` belongs to the sum of `β_k ∪ H²` and …
`H^{2k+2}(X × X̂, ℚ)^{Spin(V)_P}`" needs a `Spin(V)_P`-stable complement of `β_k ∪ H²` (complete reducibility, via
density). Filled: the invariant pairing `(x, y) ↦ ∫ x ∧ y ∧ h^{2n-2k-2}` is nondegenerate on `β_k ∪ H²` (Lefschetz
property of `Ξ_P` and Poincaré duality), and its orthogonal complement is invariant. The statement asserts that `ℓ` is
"of type `(1,1)`", which the proof never addresses; it follows from Proposition 6.1.2: `ℓ + ½c₁(𝒫)` is invariant,
hence a multiple of `Ξ_P` by Lemma 2.2.7. Lean: [`lemma6_2_3`](WeilClasses/Orlov/Sec6_2.lean#L2402) ([`s62_coset_inv`](WeilClasses/Orlov/Sec6_2.lean#L2210), [`s62_pairing_nondeg`](WeilClasses/Orlov/Sec6_2.lean#L2150)). The
decomposition `H² = H²_P + ℚΞ_P` before the lemma (TeX l. 2414–2417), with `H²_P` the sum of the non-trivial
irreducible subrepresentations, presupposes complete reducibility in the same way; Lean takes `H²_P` to be the span of
the `ρ_g x - x` and bounds its codimension with the invariant pairing of `⋀²V` ([`exteriorPower_two_eq`](WeilClasses/Orlov/Sec6_2.lean#L1964)).

**E21. Lemma 6.3.2 and the footnote of §6.3 (TeX l. 2703, 2816–2846), an error (sign).** The lemma states that
`φ_𝒫 ⊗ ψ_{𝒫⁻¹} : H^d(X̂ × X) → H^{4n-d}(X × X̂)` is `(-1)^{d(d+1)/2} PD`. For this map (no shift) the sign is
`(-1)^{d(d-1)/2}`; counterexample `n = 1`, `α = f₁`, `β = f₂ ∧ e₁ ∧ e₂`: the pairing of the image of `α` with `β` is
`1 = ∫ f₁ ∧ β`, where the lemma predicts `-1`. For the shifted map `φ_𝒫 ⊗ ψ_{𝒫⁻¹[n]} = φ_𝒫 ⊗ φ_𝒫⁻¹`, which §6.4 uses,
the sign is `(-1)^{n + d(d-1)/2}`. The proof has three slips: it drops a factor `(-1)ⁿ` between its first two
displays, it identifies `φ_𝒫⁻¹` with the unshifted `ψ_{𝒫⁻¹}` (they differ by `(-1)ⁿ`), and it evaluates `PD` with
signs that match the footnote's formula only when `PD_k` is read as the inverse of `PD_X` (the footnote's
[Huybrechts, Lemma 9.23] for `X̂ → X` holds only with that reading). Only the reversal of degrees is used later
(Proposition 6.4.1). Lean: [`lemma6_3_2`](WeilClasses/Orlov/Sec6_3.lean#L1119) for the unshifted map, with `(-1)^{d(d-1)/2}`; [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97)
with `PD_k = PD_X⁻¹`.

**E22. §6.4 (TeX l. 2964–2965), an overstatement (minor, harmless).** "The group `Spin(V_K)` acts transitively on the
set of ordered pairs of complementary maximally isotropic subspaces of `V_K`." `Spin(V_K)` preserves each of the two
families of maximal isotropic subspaces, so there are two orbits; the proof needs only pairs from the even family, on
which the action is transitive. Lean: [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), for even pairs.

**E23. (8.1.2) (TeX l. 3636–3653), a missing hypothesis.** See Section 4.

**E24. §8.1, after Lemma 8.1.1 (TeX l. 3679–3681), an error.** "The action of the element `[[0, -f⁻¹], [f, 0]]` on
`ℙ(S_K)` extends the action of `ι`", where `ι(exp(kΘ)) = kⁿ exp(k⁻¹Θ)`. A matrix `[[a₁₁, a₁₂f⁻¹], [a₂₁f, a₂₂]]` maps
the maximal isotropic subspace of `exp(kΘ)` to that of `exp(k'Θ)` with `k' = (a₁₁k + a₁₂)/(a₂₁k + a₂₂)`; so
`[[0, -f⁻¹], [f, 0]]` acts by `k ↦ -1/k`, which is `ι ∘ τ` (`τ exp(kΘ) = exp(-kΘ)`). For `K ≠ ℚ(i)` no element of
`SO⁺_Hdg(V_K)` acts by `k ↦ 1/k`; for `K = ℚ(i)`, `[[0, i f⁻¹], [i f, 0]]` does. Lean: [`iota_tau_extends`](WeilClasses/Secant/Sec8_1.lean#L1272).

**E25. Lemma 10.1.1 (TeX l. 9709–9711), a gap.** The proof shows that `ℙ(span{1, [pt_X]})` is "the unique line secant
to the spinor variety and passing through `w`, every point of which is `Spin(V_ℂ)_w`-invariant". That every
transversal secant through `w` has this property is [Igusa, Lemma 2] applied to its own pair, which the proof does not
say. Lean: [`lemma10_1_1`](WeilClasses/Igusa/Secant.lean#L2279) ([`s10_secant_lines`](WeilClasses/Igusa/Secant.lean#L785)).

**E26. Remark 10.1.2(1) (TeX l. 9751–9752), an error (slip).** "the level set `J⁻¹(d) ⊂ S⁺_F`, `d ∈ F`, consists of a
single `Spin(V_F)`-orbit" fails for `d = 0`: `J(0) = J(1) = 0`, and `0` is a fixed point. Correct for `d ≠ 0`. §10 is
not used for the main theorems (TeX l. 9633). Lean: [`remark10_1_2_orbit`](WeilClasses/Igusa/Secant.lean#L2447) with `d ≠ 0`.

**E27. Lemma 10.2.1, proof (TeX l. 9793–9796), a gap and an ordering slip.** "`W₁ := g⁻¹(H¹(X, ℚ))` and
`W₂ := g⁻¹(H¹(X̂, ℚ))` are defined over `K` and are the two maximal isotropic subspaces of `V_K` invariant under
`Spin(V_ℚ)_w`": that there are no others needs the Zariski density of `Spin(V_ℚ)_w` in `Spin(V_ℂ)_w ≅ SL(W₁)`. (Since
`g ∈ Spin(V_K)`, the `K`-spans `H¹(X, K)`, `H¹(X̂, K)` are meant.) The next sentence, "`W₁` and `W₂` are not defined
over `ℚ`, since otherwise …" (TeX l. 9795), shows only that they are not both rational; that neither is uses the
`σ`-invariance of the pair, stated one sentence later (TeX l. 9796). Lean: [`lemma10_2_1`](WeilClasses/Igusa/CM.lean#L1608) (density by unitary
transvections, [`s10_D_mem`](WeilClasses/Igusa/CM.lean#L1480); the two sentences in the corrected order).

**E28. Typos and misprints.**

- Lemma 2.2.2 (TeX l. 821): `SL_n(K)` should be `SL_{2n}(K)`; in the proof (TeX l. 825), `ker det₁` should be `ker χ₁`
  (`-1` lies in `ker det₁` but not in `Spin(V_K)_P`). The author confirms the first (*Suggested program for JAVA
  2026*, footnote 8). Lean: [`lemma2_2_2`](WeilClasses/PureSpinor/Stabilizer.lean#L815).
- §8.1, the expansion of `β` (TeX l. 3693): the coefficient of `Θ⁴/4!` is `4q^{n-4}ρ(ρ² - τ²d)`; the factor `4` is
  missing. Lean: [`betaPP_expansion`](WeilClasses/Secant/Sec8_1.lean#L1573).
- Example 10.2.2 (TeX l. 9854): with the orientation `∫_X e₁ ∧ ⋯ ∧ e₆ = 1` of TeX l. 9647,
  `Θ = e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` has `∫ Θ³ = -6`; `-e₁ ∧ e₄ + e₂ ∧ e₅ + e₃ ∧ e₆` is principal. The value
  `J(2 - dΘ²) = 16d³` is the same for both. Lean: [`example10_2_2`](WeilClasses/Igusa/CM.lean#L2023), [`example10_2_2_principal`](WeilClasses/Igusa/CM.lean#L2030).
- Pridham's remark is cited as "Remark 2.6" at TeX l. 547 and 2994; it is Remark 2.26 (as at TeX l. 627, 3252).
- TeX l. 443 and 1827 cite Proposition 2.4.4 and Corollary 3.2.2 as "Lemma".
- TeX l. 1615: "`I∘f)² = d`" lacks a parenthesis. TeX l. 1660–1661: the inclusion proved by isotropy is
  "right ⊆ left", not "left ⊆ right". TeX l. 1678: `Spin(V_ℝ)_w` should be `Spin(V_ℝ)_P`. TeX l. 1778: "`∩ ℝ`" should
  be "`∩ V_ℝ`". TeX l. 2179: "`(x₁, x₂) = (x₁ + x₂, x₂)`" lacks `μ`.
- Proposition 6.4.1, proof (TeX l. 2933, 2940): the second summand `φ'(ℓ̃₁²)` should be `φ'(ℓ̃₂²)`.
- TeX l. 3636: "polazixed". TeX l. 6323–6324 swap the roles of `G₁` and `G₂` relative to §1.5 and Lemma 9.3.1
  (harmless, by symmetry).

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
|---|---|---|---|
| (8.1.2) (TeX l. 3636–3653) | `End_ℚ(X) = ℚ` | (8.1.2) asserts that for a principally polarized `X` with `NS(X) = ℤΘ`, `End_ℚ(X × X̂)` is the algebra of matrices `[[a₁₁, a₁₂f⁻¹], [a₂₁f, a₂₂]]`, `aᵢⱼ ∈ ℚ`. The Picard number is the dimension of the Rosati-symmetric part of `End_ℚ(X)`, so a CM field of endomorphisms is compatible with `NS(X) = ℤΘ`: the Jacobian of a very general Picard curve `y³ = (x - a₁)⋯(x - a₄)` (`n = 3`) has `End_ℚ(X) = ℚ(ζ₃)`, and `End_ℚ(X × X̂) ≅ M₂(ℚ(ζ₃))` is larger than the printed algebra; for `n = 1`, a CM elliptic curve. For `n = 2` the hypothesis is automatic. | [`equation8_1_2`](WeilClasses/Secant/Sec8_1.lean#L484) assumes `End_ℚ(X) = ℚ` (agreed with the project owner); §8.1 is the generic case ("a generic principally polarized abelian variety"), and nothing outside §8.1 uses (8.1.2). |

## 5. Redundant hypotheses

The proofs of these statements do not use some of their hypotheses; the Lean statements leave them out, so they are
more general than the paper's. The Challenge states Theorem 1.4.1(3) and (4) with `d ≥ 3` (for every principally
polarized threefold `X`, by design, see below), Theorem 1.5.1 with `d > 0`, and Corollary 1.6.1; its compared theorems
[`Challenge.rank_chE`](Challenge.lean#L702) and [`Challenge.discIs_XXhat`](Challenge.lean#L697) have the generality of the library (every `d`; no complex structure
on `X`).

| Result | Hypothesis that is not needed | Lean |
|---|---|---|
| Lemma 2.2.2 | `d > 0` | [`lemma2_2_2`](WeilClasses/PureSpinor/Stabilizer.lean#L815), [`lemma2_2_2_restrict`](WeilClasses/PureSpinor/Stabilizer.lean#L834) |
| Remark 2.2.3 | `d > 0`; for the unique secant, that the two pure spinors are linearly independent | [`remark2_2_3_not_pure`](WeilClasses/PureSpinor/Stabilizer.lean#L863), [`remark2_2_3_odd`](WeilClasses/PureSpinor/Stabilizer.lean#L883), [`remark2_2_3_even`](WeilClasses/PureSpinor/Stabilizer.lean#L898), [`remark2_2_3_determines`](WeilClasses/PureSpinor/Stabilizer.lean#L916), [`remark2_2_3_unique_secant`](WeilClasses/PureSpinor/Stabilizer.lean#L951) |
| Lemma 3.1.3 | `J` a complex structure (only the class `Θ` matters) | [`lemma3_1_3`](WeilClasses/Hermitian/Defs.lean#L3120) |
| Corollary 3.2.3 | Part by part: `Ξ_P` is of type `(1,1)` for every `I ∈ ρ(Spin(V_ℝ)_P)` (no positivity, no `ν(I) = 2n`); `Ξ_P(x, I x) > 0` needs only `g_I > 0`; the Weil condition needs no positivity; the condition on the polarization is an algebraic identity in `f` | [`corollary3_2_3_type11`](WeilClasses/Hermitian/ComplexStructures.lean#L1353), [`corollary3_2_3_kahler`](WeilClasses/Hermitian/ComplexStructures.lean#L1368), [`corollary3_2_3_weil`](WeilClasses/Hermitian/ComplexStructures.lean#L1387), [`corollary3_2_3_polarization`](WeilClasses/Hermitian/ComplexStructures.lean#L1399) |
| Theorem 1.4.1(1) | `J` a complex structure | [`theorem1_4_1_1`](WeilClasses/Main/Intro.lean#L760) |
| Theorem 1.4.1(2), the rank `8d` | `d ≥ 3` | [`theorem1_4_1_2_rank`](WeilClasses/Main/Intro.lean#L919) |
| Lemma 6.2.3, Remark 6.2.4 | `Ξ_P` ample (the setting of §6.2): the Lefschetz property that the proof uses holds for the nondegenerate form `Ξ_P`; for the class `ℓ` in Remark 6.2.4, also `w₁, w₂ ∈ P` | [`lemma6_2_3`](WeilClasses/Orlov/Sec6_2.lean#L2402), [`lemma6_2_3_unique`](WeilClasses/Orlov/Sec6_2.lean#L2490), [`lemma6_2_3_c1N`](WeilClasses/Orlov/Sec6_2.lean#L2504), [`lemma6_2_3_injective`](WeilClasses/Orlov/Sec6_2.lean#L2104), [`remark6_2_4`](WeilClasses/Orlov/Sec6_2.lean#L2526), [`remark6_2_4_ell`](WeilClasses/Orlov/Sec6_2.lean#L2596) |
| Lemma 8.1.1 | `d > 0` | [`lemma8_1_1`](WeilClasses/Secant/Sec8_1.lean#L1155) |
| [Igusa, Prop. 3], invariance of `J` | `x ∈ S⁺` | [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980) |
| [Igusa, Lemma 1], the action on `W₂` | `x ∈ W₁`, `y ∈ W₂` (the statement is that `ρ(g)` is an isometry) | [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332) |

Statements the formalization proves more generally by design: Theorem 1.4.1 for every principally polarized abelian
threefold (the paper: the Jacobian of a non-hyperelliptic curve of genus `3`; the classes do not depend on the
curve); Lemma 5.2.1 for abelian varieties of different dimensions; and most results of §§2–6 over every field of
characteristic `0`.

## 6. How the formalization reads the paper

**The model.**

- An abelian `g`-fold up to isogeny is a polarizable rational Hodge structure of weight one: `H¹(A, ℚ) = ℚ^{2g}` with
  a complex structure `J` on `H¹(A, ℝ)` that admits an ample class ([`AbVar`](Challenge.lean#L257)). Its cohomology is `⋀• H¹(A, ℚ)`.
  Morphisms are rational maps commuting with the complex structures; Hodge classes are rational classes of type
  `(p, p)`; a class is ample if it is of type `(1,1)` and `⟪Θ, a ∧ (a ∘ J)⟫ > 0` for `a ≠ 0` (Kähler positivity).
- Abelian varieties of Weil type, their polarizations, Hodge–Weil classes and discriminant are defined as in [van
  Geemen] and the paper ([`WeilType`](Challenge.lean#L295), [`PolarizedWeilType`](Challenge.lean#L311), [`HWof`](Challenge.lean#L285), [`PolarizedWeilType.DiscIs`](Challenge.lean#L335)). The Weil-type period
  domain of `(η, h)` is the set of complex structures for which `(J, η, h)` is polarized of Weil type ([`WeilDomain`](Challenge.lean#L370)).
- Algebraic classes are an abstract system [`CycleClasses`](Challenge.lean#L347): a subspace of `H*(A, ℚ)` for every complex structure, with
  the properties of Section 2 as hypotheses. Nothing constructs it from cycles. For the system in which every class is
  algebraic, the seven hypotheses on algebraic classes hold ([`WeilClasses/Main/Instances.lean`](WeilClasses/Main/Instances.lean)); the hypotheses about
  Hodge structures and the two parts of [Igusa, Prop. 3] are published results with no instance in Lean.
- `X × X̂` is explicit: `V = H¹(X̂) ⊕ H¹(X)` with the Mathlib order `(θ, w)`, `f`, `η(a + b√-d) = a + b f`,
  `h = dΘ + Θ̂`, and the complex structure of `X × X̂` (`fX`, `hX`, `JX`; `Main/Jacobian.lean`, `Main/Compare.lean`
  compare it with the paper's `P_Θ`).
- The sheaves of §§7–9 enter only through their Chern characters: `ch(F₁)` is the class of Lemma 8.2.1, and
  `ch(E) = τ φ(ch F₁ ⊗ ch F₁)` ([`chF1`](Challenge.lean#L632), `chE`, [`kappaX`](Challenge.lean#L640)).

**Conventions.**

- `c₁(𝒫) = +Σ eᵢ ∪ fᵢ`: the sign is forced by Lemmas 6.1.1, 6.3.1 and Proposition 6.1.2 (E10).
- The library's complex structure `I_{V_ℝ}` of `X × X̂` ([`productStructure`](WeilClasses/Hodge/Defs.lean#L62)) is the paper's footnote convention
  (TeX l. 1265–1275), the negative of the standard one (E12). The statements of record use the standard structure
  `JX = -I_{V_ℝ}` (`H^{1,0}` the `i`-eigenspace, as for every [`AbVar`](Challenge.lean#L257)); [`weilDomain_eq_image_OmegaP`](WeilClasses/Main/Compare.lean#L1945) identifies the
  Weil-type period domain with the image of `Ω_P` under `I ↦ -I`.
- Bases are indexed from `0`; `e_{14}^*` of §10 is `eStar F 0 3`.
- The integral Clifford algebra is that of the quadratic form `Q(θ, w) = θ(w)` (E4).

**Readings.**

- `Spin(V)_P` is the stabilizer in the integral spin group (2.2.2). Where the paper reasons about algebraic groups
  (the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)`, the two components in Remark 2.2.3), the statements are for
  `K`-points (E6, E7).
- Lemma 3.1.2: `SU(V_ℚ, H)` is the special unitary group (E16).
- `H²_P` is the span of the `ρ_g x - x` (a departure, Section 7); the Hodge–Weil plane of `P` is the rational form of
  `⋀^{2n}W₁ ⊕ ⋀^{2n}W₂`; `h = Ξ_P^♯`.
- Theorem 1.4.1(3) and Corollary 1.3.2: "every deformation of `(X × X̂, η, h)` as a polarized abelian variety of Weil
  type" is a point of the period domain `Ω_P` (equivalently, up to `I ↦ -I`, the connected component of the Weil-type
  period domain).
- Lemma 6.2.3: "unique class `ℓ` of type `(1,1)` in `H²_P`" is read literally; the proof gives uniqueness in all of
  `H²_P`.
- (6.1.8), (6.1.9) are stated over every field; the paper uses them for integral `g`.
- [Huybrechts, Lemma 9.23] for `X̂ → X`: `PD_k` is the inverse of `PD_X` (E21).
- §10: "the two maximal isotropic subspaces invariant under `Spin(V_ℚ)_w`" (Lemma 10.2.1) is stated as an equivalence
  (exactly these two).

**Corrections of statements** (each agreed with the project owner, or an obvious misprint):

1. Proposition 1.3.1, (1.3.1), (1.3.2): equivariance for `m ⊗ m` (E2).
2. Lemma 2.2.1, second sentence, odd `n`: nondegenerate instead of definite (E5).
3. §2.2: the image of `Spin(V_K)_{ℓ₁,ℓ₂}` in `GL(W₁)` is the square-determinant subgroup (E6).
4. Lemma 2.2.2: `SL_{2n}(K)` (misprint; E28).
5. Remark 2.2.5: the whole circle in `ρ(Spin(V_ℝ)_P)` (E9).
6. Remark 2.3.1: `B̄₀ = -½c₁(𝒫)` (E10).
7. Lemma 6.3.2: the sign `(-1)^{d(d-1)/2}` (E21).
8. (8.1.2): with `End_ℚ(X) = ℚ` (E23).
9. §8.1: the element extends `ι ∘ τ` (E24).
10. §8.1: the coefficient `4` in the expansion of `β` (misprint; E28).
11. Remark 10.1.2(1): `d ≠ 0` (slip; E26).

## 7. Departures from the paper's proofs

Each departure is documented in the docstring of the declaration, as "Departure from the paper (reason k)" or, for a
gap of the paper that the formalization fills, "Gap in the paper (filled)"; in [`formalization.yaml`](formalization.yaml)
(`fidelity.divergences`); and, where the results used change, in [`docs/route_differences.tsv`](docs/route_differences.tsv). Gaps that are filled
along the paper's own lines are not departures; Section 3 lists them. Reasons: (1) the paper's step is wrong or has a
gap that cannot be repaired along its lines; (2) the step needs mathematics that Lean lacks and that the project
cannot reasonably build; (3) the step has no meaning in the model.

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
|---|---|---|---|---|
| Proposition 6.1.2 | Reduction to abelian surfaces: Obata's Th. B, Lemma 6.2.5 (ideal sheaves, [Markman, JEMS 2023, Prop. 11.2], Verbitsky's Zariski density) (TeX l. 2269–2575) | Algebraic: Lemma 6.1.1, Remark 2.3.1 with [Trautman], Lemma 6.3.2 | Reason 2 (sheaves, Zariski density of monodromy); authorized by the project owner | — |
| Lemma 6.2.5, (6.2.5) | Ideal sheaves of points, [Markman, JEMS 2023, Prop. 11.2], Lemma 6.2.3, (6.1.9), [Verbitsky, Th. 2.1] | The case `n = 2` of Proposition 6.1.2 | Reason 2; part of the authorized departure | — |
| Lemma 4.0.2 | The dimension of an adjoint orbit equals that of `Ω_P` (TeX l. 1772–1803) | `SO₊(V_ℝ)_f ≅ SU(n, n)` acts transitively on `Ω_P`, via Cartan involutions | Reason 2 (dimensions of orbits of real Lie groups); authorized by the project owner | — |
| §2.4, `θ` is an isomorphism of Hodge structures | `-θ` is the differential of the isogeny `φ_L` [Birkenhake–Lange, 2.4.5] | Ampleness and type `(1,1)` | Reason 3 (no line bundles or isogenies in the model) | — |
| Lemma 2.2.6 | The Hodge structure on `C(V)` transported by `m`; `φ` a morphism of Hodge structures (TeX l. 908–936) | One element of `Spin(V_ℂ)` of the complexified circle and the equivariance of `φ` ([Chevalley, III.3.1]) | Reason 3 (Hodge structures in the model are circle actions on `⋀•V`; the transported structure on `C(V)` is not modeled) | — |
| Lemma 2.2.7, type of the lines `ω^j` | "a one-dimensional `U(1)`-invariant subspace … defined over `ℚ`" (TeX l. 1032–1033) | Fixed by one non-real element of the complexified circle; the type of `⋀^{2n}Wᵢ` from Lemma 2.2.6 as in the paper | Reasons 3 and 1 ("`U(1)`-invariant" is not justified) | E8 |
| Lemmas 2.2.4, 2.2.7, invariants | Irreducibility of `⋀ᵏWᵢ` under the arithmetic group (density) | Unitary transvections and a Schur step; weights and root operators | Reasons 1 and 2 (the paper's step is a gap; density is not in Lean) | E8 |
| Lemma 2.2.1, first sentence, one step | The pairing on `P` computed as if it were symmetric: `(λ₁, λ₁) = (a, a)_S - (b, b)_S + 2i(a, b)_S` and "`(a, a) = 0` iff `W₁ ∩ W₂ ≠ 0`" (TeX l. 783–789) | The Gram matrix of `P` keeps `(λ₁, λ₂)_S` and `(λ₂, λ₁)_S = (-1)ⁿ(λ₁, λ₂)_S` apart | Reason 1 (the step is wrong for odd `n`) | E5 |
| Remark 2.2.3, "`w` determines `P`", the unique secant | The identity component of `Stab(w)` (TeX l. 835) | The joint kernel of the infinitesimal stabilizer of `w` | Reason 2 (identity components of algebraic groups); see E7 | E7 |
| Lemma 2.3.2(1), one step | The commutator maps to `2Σ_k …` | `(-1)ⁿ Σ_k …` | Reason 1 (the step is wrong) | E11 |
| Remark 2.4.3, one step | "must be already in `Spin(V_ℝ)` as it maps to `I`" | The spinor norm of `I = G²` is a square, so `I` lifts to `Spin(V_ℝ)` | Reason 1 (gap) | E13 |
| Lemma 3.1.2, one step | "The norm character has finitely many values on `SO(V_ℚ)`"; finitely many units | The spinor norm is trivial on `SU(V_ℚ, H)` ([Chevalley, III.3.2/III.4.5], the Mukai pairing): index `1` | Reason 1 (the step is wrong) | E16 |
| Lemma 4.0.1, non-emptiness | Proposition 2.4.4 for the complex structure of `X × X̂` (only for `P_Θ`) | The signature `(n, n)` of `H` for a general `P` (`P_Θ`: the paper's argument) | Reason 1 (gap) | E17 |
| Corollary 4.0.4, one step | `I(α) = α` for invariants of the integral group (density) | `⋀²`-invariants are `ℚ Ξ_P^♯` (Lemma 2.2.7), of type `(1,1)` on `Ω_P` | Reason 2 (density) | E19 |
| §6.2, `H² = H²_P + ℚΞ_P` (TeX l. 2414–2417) | `H²_P` the sum of the non-trivial irreducible subrepresentations, which presupposes complete reducibility of the `Spin(V)_P`-representation | `H²_P` := the span of the `ρ_g x - x`; its codimension bounded with the invariant pairing of `⋀²V` | Reason 2 (density) | E20 |
| Lemma 6.2.3 | Complete reducibility of `Spin(V)_P`-representations (TeX l. 2462–2464); hard Lefschetz for the ample `Ξ_P`; the `(1,1)` type of `ℓ` not proved | A `Spin(V)_P`-invariant complement for the pairing `∫ x ∧ y ∧ h^{2n-2k-2}`; the algebraic `sl₂` Lefschetz property; the `(1,1)` type from Proposition 6.1.2 and Lemma 2.2.7 | Reason 2 (density, Hodge theory); reason 1 for the `(1,1)` type | E20 |
| Lemma 8.1.1 | The stabilizer of `H¹(X̂, K)`, the rational normal curve and its Zariski closure (TeX l. 3672–3676) | The stabilizer step as printed, and the orbit `ℙ¹_K` by the coset decomposition `a = [[1, k], [0, 1]] b` | Reason 2 (Zariski closures) | — |
| Theorem 1.4.1(2), the rank | Read off the reflexive sheaf (Proposition 9.2.2, TeX l. 5455) | The degree-`0` part of `ch(E)` | Reason 3 (sheaves are not modeled) | — |
| Theorem 1.5.1, `d ∈ {1, 2}`, and the passage to all of moduli | Not treated (E3) | `d ↦ 4d`, `ℚ(√-4d) = ℚ(√-d)`; [van Geemen, Th. 5.2(3)] at the last step | Reason 1 (gap) | E3 |
| Lemma 10.1.1, last sentence | "`Spin(V_ℂ)_w` is defined over `ℚ`; the latter determines `P_w`" (TeX l. 9716–9717) | Galois descent through `w`: `P_w` is determined by `w` | Reason 3 (stabilizers as algebraic groups over `ℚ` are not modeled) | — |
| Lemma 10.1.1, uniqueness | Uniqueness among secants whose points are `Spin(V_ℂ)_w`-invariant (TeX l. 9709–9711) | [Igusa, Lemma 2] for every transversal pair | Reason 1 (gap) | E25 |
| Lemma 10.2.1 | "not defined over `ℚ`" (TeX l. 9795) before the `σ`-invariance of the pair (l. 9796); Zariski density (l. 9793) | The `σ`-invariance first, then the paper's two steps; unitary transvections for density | Reason 1 (order); reason 2 (density) | E27 |

Every other proof follows the paper's argument step by step, with the same citations; an independent review against
the TeX compared every formal proof with the paper's.

## 8. What each result depends on

Generated from [`scripts/Audit.lean`](scripts/Audit.lean) (`python3 scripts/gen_dependency_table.py`): for each paper result, the results
from prior work its proof uses, proved in `External/` or assumed. Every result depends only on the standard axioms.

| Result | Lean | Results from prior work used |
|---|---|---|
| Proposition 1.2.1 | [`proposition1_2_1`](WeilClasses/Main/Intro.lean#L596) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Proposition 1.3.1 | [`proposition1_3_1_eq`](WeilClasses/Orlov/Intro.lean#L45) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Proposition 1.3.1 | [`proposition1_3_1_equivariant`](WeilClasses/Orlov/Intro.lean#L56) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Corollary 1.3.2 | [`corollary1_3_2`](WeilClasses/Orlov/Cor1_3_2.lean#L349) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Corollary 1.3.2 | [`corollary1_3_2_hodge`](WeilClasses/Orlov/Cor1_3_2.lean#L362) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| (1.3.2) | [`equation1_3_2_equivariant`](WeilClasses/Orlov/Intro.lean#L88) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Theorem 1.4.1(1) | [`theorem1_4_1_1`](WeilClasses/Main/Intro.lean#L760) | [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| Theorem 1.4.1(2) | [`theorem1_4_1_2_rank`](WeilClasses/Main/Intro.lean#L919) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Theorem 1.4.1(3) | [`theorem1_4_1_3`](WeilClasses/Main/Intro.lean#L927) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Theorem 1.4.1(4) | [`theorem1_4_1_4`](WeilClasses/Main/Intro.lean#L1109) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Theorem 1.4.1(4) | [`theorem1_4_1_4_finrank`](WeilClasses/Main/Intro.lean#L1246) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Theorem 1.4.1(3) | [`theorem1_4_1_3_model`](WeilClasses/Main/Theorems.lean#L324) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157), [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Theorem 1.4.1(4) | [`theorem1_4_1_4_model`](WeilClasses/Main/Theorems.lean#L366) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Theorem 1.5.1 | [`theorem1_5_1`](WeilClasses/Main/Theorems.lean#L518) | [`PullbackClosed`](Challenge.lean#L353), [`SubalgebraClosed`](Challenge.lean#L359), [`LefschetzOneOne`](Challenge.lean#L365), [`VoisinLocus`](Challenge.lean#L390), [`VanGeemenModuli`](Challenge.lean#L405), [`SecantSheafDeformation`](Challenge.lean#L660), [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Corollary 1.6.1 | [`corollary1_6_1`](WeilClasses/Main/Theorems.lean#L552) | [`PullbackClosed`](Challenge.lean#L353), [`SubalgebraClosed`](Challenge.lean#L359), [`LefschetzOneOne`](Challenge.lean#L365), [`VoisinLocus`](Challenge.lean#L390), [`VanGeemenModuli`](Challenge.lean#L405), [`SchoenDegeneration`](Challenge.lean#L425), [`MoonenZarhinSimple`](Challenge.lean#L432), [`RamonMariProducts`](Challenge.lean#L447), [`MoonenZarhinLowDim`](Challenge.lean#L454), [`SecantSheafDeformation`](Challenge.lean#L660), [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84), [`vanGeemen_def4_9`](WeilClasses/External/VanGeemen/Sec3.lean#L50) |
| Lemma 2.2.1 | [`lemma2_2_1`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1529) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.1 | [`lemma2_2_1_even`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1569) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.1 | [`lemma2_2_1_odd`](WeilClasses/PureSpinor/Lemma2_2_1.lean#L1645) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.2 | [`lemma2_2_2`](WeilClasses/PureSpinor/Stabilizer.lean#L815) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`igusa_lemma1_ker`](WeilClasses/External/Igusa/Sec2_2.lean#L1259), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Lemma 2.2.2 | [`lemma2_2_2_restrict`](WeilClasses/PureSpinor/Stabilizer.lean#L834) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`igusa_lemma1_ker`](WeilClasses/External/Igusa/Sec2_2.lean#L1259), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Remark 2.2.3 | [`remark2_2_3_not_pure`](WeilClasses/PureSpinor/Stabilizer.lean#L863) | [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283) |
| Remark 2.2.3 | [`remark2_2_3_odd`](WeilClasses/PureSpinor/Stabilizer.lean#L883) | [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Remark 2.2.3 | [`remark2_2_3_even`](WeilClasses/PureSpinor/Stabilizer.lean#L898) | [`igusa_lemma2_stab_even`](WeilClasses/External/Igusa/Sec2_2.lean#L1374) |
| Remark 2.2.3 | [`remark2_2_3_determines`](WeilClasses/PureSpinor/Stabilizer.lean#L916) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283) |
| Remark 2.2.3 | [`remark2_2_3_unique_secant`](WeilClasses/PureSpinor/Stabilizer.lean#L951) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263) |
| Lemma 2.2.4 | [`lemma2_2_4`](WeilClasses/PureSpinor/Lemma2_2_4.lean#L1335) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Remark 2.2.5 | [`remark2_2_5`](WeilClasses/PureSpinor/Lemma2_2_6.lean#L2461) | [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101) |
| Lemma 2.2.6 | [`lemma2_2_6`](WeilClasses/PureSpinor/Lemma2_2_6.lean#L2634) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101) |
| Lemma 2.2.6 | [`lemma2_2_6_V01`](WeilClasses/PureSpinor/Lemma2_2_6.lean#L2655) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101) |
| Lemma 2.2.7 | [`lemma2_2_7_hodge`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3506) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Lemma 2.2.7 | [`lemma2_2_7_odd`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3535) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_even`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3546) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_middle`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3561) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Lemma 2.2.7 | [`lemma2_2_7_K_eq`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3572) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Lemma 2.2.7 | [`lemma2_2_7_K_indep`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3585) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_K_finrank`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3607) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_K_det₁`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3624) | – |
| Lemma 2.2.7 | [`lemma2_2_7_K_det₂`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3635) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_K_trivial`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3647) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 2.2.7 | [`lemma2_2_7_trivial`](WeilClasses/PureSpinor/Lemma2_2_7.lean#L3659) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Remark 2.3.1 | [`remark2_3_1_B0bar_apply`](WeilClasses/Chevalley/Sec2_3.lean#L428) | – |
| Remark 2.3.1 | [`remark2_3_1_altPart_add_pairing`](WeilClasses/Chevalley/Sec2_3.lean#L434) | – |
| Remark 2.3.1 | [`remark2_3_1_B0bar_eq_neg_half_c1P`](WeilClasses/Chevalley/Sec2_3.lean#L473) | – |
| Remark 2.3.1 | [`remark2_3_1_sym_equivariant`](WeilClasses/Chevalley/Sec2_3.lean#L535) | [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Remark 2.3.1 | [`remark2_3_1_sym_bijective`](WeilClasses/Chevalley/Sec2_3.lean#L542) | [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351) |
| Lemma 2.3.2(1) | [`lemma2_3_2_1`](WeilClasses/Chevalley/Sec2_3.lean#L1348) | [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301) |
| Lemma 2.3.2(2) | [`lemma2_3_2_2`](WeilClasses/Chevalley/Sec2_3.lean#L1388) | [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261) |
| Lemma 2.4.2 | [`lemma2_4_2`](WeilClasses/WeilType/Basic.lean#L1060) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Remark 2.4.3 | [`remark2_4_3_mem`](WeilClasses/WeilType/Basic.lean#L1124) | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97) |
| Remark 2.4.3 | [`remark2_4_3_rho`](WeilClasses/WeilType/Basic.lean#L1157) | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Remark 2.4.3 | [`remark2_4_3_complexStructure`](WeilClasses/WeilType/Basic.lean#L1382) | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Remark 2.4.3 | [`remark2_4_3_exists_lift`](WeilClasses/WeilType/Basic.lean#L1527) | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Remark 2.4.3 | [`remark2_4_3`](WeilClasses/WeilType/Basic.lean#L1563) | [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| (2.4.4) | [`equation2_4_4`](WeilClasses/WeilType/Theta.lean#L1380) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| Proposition 2.4.4 | [`proposition2_4_4`](WeilClasses/WeilType/Theta.lean#L1690) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101) |
| (2.4.5) | [`equation2_4_5`](WeilClasses/WeilType/Theta.lean#L1497) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| (2.4.6) | [`equation2_4_6_W₁`](WeilClasses/WeilType/Theta.lean#L1532) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| (2.4.6) | [`equation2_4_6_W₂`](WeilClasses/WeilType/Theta.lean#L1545) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| Lemma 3.1.1 | [`lemma3_1_1`](WeilClasses/Hermitian/Defs.lean#L1580) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Lemma 3.1.2 | [`KSecant.s3_hasSignature`](WeilClasses/Hermitian/Defs.lean#L2185) | – |
| Lemma 3.1.2 | [`lemma3_1_2_hermitian`](WeilClasses/Hermitian/Defs.lean#L3029) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 3.1.2 | [`lemma3_1_2_linear`](WeilClasses/Hermitian/Defs.lean#L3036) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 3.1.2 | [`lemma3_1_2_invariant`](WeilClasses/Hermitian/Defs.lean#L3042) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 3.1.2 | [`lemma3_1_2_signature`](WeilClasses/Hermitian/Defs.lean#L3049) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 3.1.2 | [`lemma3_1_2_finiteIndex`](WeilClasses/Hermitian/Defs.lean#L3078) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Lemma 3.1.3 | [`lemma3_1_3`](WeilClasses/Hermitian/Defs.lean#L3120) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| Lemma 3.2.1 | [`lemma3_2_1`](WeilClasses/Hermitian/ComplexStructures.lean#L625) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| (3.2.1) | [`equation3_2_1`](WeilClasses/Hermitian/ComplexStructures.lean#L636) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 3.2.2 | [`corollary3_2_2_rational`](WeilClasses/Hermitian/ComplexStructures.lean#L1233) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Corollary 3.2.2 | [`corollary3_2_2_hodge`](WeilClasses/Hermitian/ComplexStructures.lean#L1274) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 3.2.3 | [`corollary3_2_3_type11`](WeilClasses/Hermitian/ComplexStructures.lean#L1353) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 3.2.3 | [`corollary3_2_3_kahler`](WeilClasses/Hermitian/ComplexStructures.lean#L1368) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Corollary 3.2.3 | [`corollary3_2_3_comm`](WeilClasses/Hermitian/ComplexStructures.lean#L1377) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 3.2.3 | [`corollary3_2_3_weil`](WeilClasses/Hermitian/ComplexStructures.lean#L1387) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 3.2.3 | [`corollary3_2_3_polarization`](WeilClasses/Hermitian/ComplexStructures.lean#L1399) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 4.0.1 | [`lemma4_0_1_injective`](WeilClasses/PeriodDomain/Defs.lean#L3288) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Lemma 4.0.1 | [`lemma4_0_1_nonempty`](WeilClasses/PeriodDomain/Defs.lean#L3320) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Lemma 4.0.1 | [`lemma4_0_1_isOpen`](WeilClasses/PeriodDomain/Defs.lean#L3344) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340) |
| Lemma 4.0.1 | [`lemma4_0_1_isEmbedding`](WeilClasses/PeriodDomain/Defs.lean#L3403) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Lemma 4.0.2 | [`lemma4_0_2`](WeilClasses/PeriodDomain/Defs.lean#L3489) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_sec2_mem`](WeilClasses/External/Igusa/Sec2_4.lean#L97), [`igusa_sec2_rho`](WeilClasses/External/Igusa/Sec2_4.lean#L157) |
| Lemma 4.0.3 | [`lemma4_0_3_hodgeWeil`](WeilClasses/PeriodDomain/SemiHodge.lean#L1710) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Lemma 4.0.3 | [`lemma4_0_3_semiHodge`](WeilClasses/PeriodDomain/SemiHodge.lean#L1722) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254) |
| Corollary 4.0.4 | [`corollary4_0_4`](WeilClasses/PeriodDomain/SemiHodge.lean#L2562) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_2_III_4_5`](WeilClasses/External/Chevalley/Sec3.lean#L1254), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| (5.2.1) | [`equation5_2_1`](WeilClasses/Correspondence/Sec5_2.lean#L39) | – |
| Lemma 5.2.1 | [`lemma5_2_1_1`](WeilClasses/Correspondence/Sec5_2.lean#L286) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| Lemma 5.2.1 | [`lemma5_2_1_2`](WeilClasses/Correspondence/Sec5_2.lean#L302) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| (5.2.2) | [`equation5_2_2`](WeilClasses/Correspondence/Sec5_2.lean#L73) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| Corollary 5.2.2 | [`corollary5_2_2_1`](WeilClasses/Correspondence/Sec5_2.lean#L315) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| Corollary 5.2.2 | [`corollary5_2_2_2`](WeilClasses/Correspondence/Sec5_2.lean#L331) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| (5.2.3) | [`equation5_2_3`](WeilClasses/Correspondence/Sec5_2.lean#L172) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166) |
| Remark 5.2.3 | [`remark5_2_3`](WeilClasses/Correspondence/Sec5_2.lean#L244) | – |
| Lemma 6.1.1 | [`lemma6_1_1`](WeilClasses/Orlov/Sec6_3.lean#L1040) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Proposition 6.1.2 | [`proposition6_1_2`](WeilClasses/Orlov/Sec6_1.lean#L303) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| (6.1.4) | [`rhoPrime_eq_phiOrlov_conj`](WeilClasses/Orlov/Sec6_1.lean#L201) | – |
| (6.1.8) | [`equation6_1_8`](WeilClasses/Orlov/Sec6_1.lean#L260) | [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49) |
| (6.1.8) | [`equation6_1_8_integral`](WeilClasses/Orlov/Sec6_1.lean#L319) | [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49) |
| (6.1.9) | [`equation6_1_9`](WeilClasses/Orlov/Sec6_1.lean#L273) | [`huybrechts_ex9_41`](WeilClasses/External/Huybrechts/Sec6_1.lean#L35) |
| Lemma 6.2.3 | [`lemma6_2_3`](WeilClasses/Orlov/Sec6_2.lean#L2402) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Lemma 6.2.3 | [`lemma6_2_3_unique`](WeilClasses/Orlov/Sec6_2.lean#L2490) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49) |
| (6.2.4) | [`equation6_2_4`](WeilClasses/Orlov/Sec6_2.lean#L2037) | – |
| (6.2.4) | [`equation6_2_4_exists`](WeilClasses/Orlov/Sec6_2.lean#L2048) | [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49) |
| Remark 6.2.4 | [`remark6_2_4`](WeilClasses/Orlov/Sec6_2.lean#L2526) | [`chevalley_III_2_2`](WeilClasses/External/Chevalley/Sec2_1.lean#L159), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_III_3_1_bijective`](WeilClasses/External/Chevalley/Sec2_2.lean#L351), [`chevalley_III_3_1_equivariant`](WeilClasses/External/Chevalley/Sec2_2.lean#L406), [`chevalley_III_3_2`](WeilClasses/External/Chevalley/Sec2_2.lean#L414), [`glo_prop3_2_1_e_field`](WeilClasses/External/GolyshevLuntsOrlov/Sec2_1.lean#L101), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`orlov_theorem2_10`](WeilClasses/External/Orlov/Sec6_1.lean#L49), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Remark 6.2.4 | [`remark6_2_4_ell`](WeilClasses/Orlov/Sec6_2.lean#L2596) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342) |
| Lemma 6.2.5 | [`lemma6_2_5`](WeilClasses/Orlov/Sec6_2.lean#L2656) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| (6.2.5) | [`equation6_2_5`](WeilClasses/Orlov/Sec6_2.lean#L2670) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Lemma 6.2.6(1) | [`lemma6_2_6_1`](WeilClasses/Orlov/Sec6_2.lean#L2726) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Lemma 6.2.6(2) | [`lemma6_2_6_2`](WeilClasses/Orlov/Sec6_2.lean#L2783) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| (6.3.1) | [`equation6_3_1`](WeilClasses/Orlov/Sec6_3.lean#L860) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Lemma 6.3.1 | [`lemma6_3_1`](WeilClasses/Orlov/Sec6_3.lean#L1015) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| (6.3.2) | [`equation6_3_2`](WeilClasses/Orlov/Sec6_3.lean#L1002) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Lemma 6.3.2 | [`lemma6_3_2`](WeilClasses/Orlov/Sec6_3.lean#L1119) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Remark 6.3.3 | [`remark6_3_3`](WeilClasses/Orlov/Sec6_3.lean#L1151) | [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127) |
| Proposition 6.4.1(1) | [`proposition6_4_1_1_line₁`](WeilClasses/Orlov/Sec6_4.lean#L1215) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Proposition 6.4.1(1) | [`proposition6_4_1_1_line₂`](WeilClasses/Orlov/Sec6_4.lean#L1263) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Proposition 6.4.1(1) | [`proposition6_4_1_1`](WeilClasses/Orlov/Sec6_4.lean#L1459) | [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Proposition 6.4.1(2) | [`proposition6_4_1_2_even`](WeilClasses/Orlov/Sec6_4.lean#L1502) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Proposition 6.4.1(2) | [`proposition6_4_1_2_odd`](WeilClasses/Orlov/Sec6_4.lean#L1519) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| (8.1.1) | [`equation8_1_1`](WeilClasses/Secant/Sec8_1.lean#L182) | – |
| Lemma 8.1.1 | [`lemma8_1_1`](WeilClasses/Secant/Sec8_1.lean#L1155) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| (8.1.2) | [`equation8_1_2`](WeilClasses/Secant/Sec8_1.lean#L484) | – |
| Lemma 8.2.1 | [`lemma8_2_1`](WeilClasses/Secant/Sec8_2.lean#L142) | [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363) |
| Example 8.2.2 | [`example8_2_2`](WeilClasses/Secant/Sec8_2.lean#L167) | [`markmanM2_prop1_7`](WeilClasses/External/Markman/Sec8_2.lean#L472) |
| Lemma 8.3.1 | [`lemma8_3_1_rank`](WeilClasses/Secant/Sec8_3.lean#L542) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Lemma 8.3.1 | [`lemma8_3_1`](WeilClasses/Secant/Sec8_3.lean#L755) | [`chevalley_III_2_1`](WeilClasses/External/Chevalley/Sec2_1.lean#L166), [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`chevalley_II_1_6_filtration`](WeilClasses/External/Chevalley/Sec2_3.lean#L261), [`chevalley_II_1_6_injective`](WeilClasses/External/Chevalley/Sec2_3.lean#L301), [`chevalley_III_1_7_mem`](WeilClasses/External/Chevalley/Sec2_4.lean#L355), [`chevalley_III_1_7_rho`](WeilClasses/External/Chevalley/Sec2_4.lean#L363), [`huybrechts_lemma9_23_X`](WeilClasses/External/Huybrechts/Sec6_3.lean#L72), [`huybrechts_lemma9_23_Xhat`](WeilClasses/External/Huybrechts/Sec6_3.lean#L97), [`huybrechts_cor9_24`](WeilClasses/External/Huybrechts/Sec6_3.lean#L127), [`igusa_lemma1_range`](WeilClasses/External/Igusa/Sec2_2.lean#L1299), [`igusa_lemma1_dual`](WeilClasses/External/Igusa/Sec2_2.lean#L1332), [`igusa_lemma1_sq`](WeilClasses/External/Igusa/Sec2_2.lean#L1342), [`trautman_theorem1_i`](WeilClasses/External/Trautman/Sec2_3.lean#L84) |
| Lemma 10.1.1 | [`lemma10_1_1`](WeilClasses/Igusa/Secant.lean#L2279) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Lemma 10.1.1 | [`lemma10_1_1_stabilizer`](WeilClasses/Igusa/Secant.lean#L2299) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Lemma 10.1.1 | [`lemma10_1_1_rational`](WeilClasses/Igusa/Secant.lean#L2382) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_normalForm_of_sq`](WeilClasses/External/Igusa/Sec10.lean#L2041), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Remark 10.1.2(1) | [`remark10_1_2_orbit`](WeilClasses/Igusa/Secant.lean#L2447) | [`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2072), [`igusa_prop3_orbit_subfield`](WeilClasses/External/Igusa/Sec10.lean#L2084) |
| Remark 10.1.2(1) | [`remark10_1_2_value`](WeilClasses/Igusa/Secant.lean#L2455) | – |
| Remark 10.1.2(2) | [`remark10_1_2_secant`](WeilClasses/Igusa/Secant.lean#L2465) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980) |
| Remark 10.1.2(2) | [`remark10_1_2_singular`](WeilClasses/Igusa/Secant.lean#L2543) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980) |
| Remark 10.1.2(2) | [`remark10_1_2_rational`](WeilClasses/Igusa/Secant.lean#L2556) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_normalForm_of_sq`](WeilClasses/External/Igusa/Sec10.lean#L2041), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Lemma 10.2.1 | [`lemma10_2_1`](WeilClasses/Igusa/CM.lean#L1608) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_normalForm_of_sq`](WeilClasses/External/Igusa/Sec10.lean#L2041), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_prop3_normalForm`](WeilClasses/External/Igusa/Sec10.lean#L2093), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Lemma 10.2.1 | [`lemma10_2_1_centralizer`](WeilClasses/Igusa/CM.lean#L1743) | [`chevalley_III_1_4_unique`](WeilClasses/External/Chevalley/Sec2_2.lean#L263), [`chevalley_III_1_12`](WeilClasses/External/Chevalley/Sec2_2.lean#L283), [`chevalley_III_2_4`](WeilClasses/External/Chevalley/Sec2_2.lean#L314), [`chevalley_III_2_4_self`](WeilClasses/External/Chevalley/Sec2_2.lean#L340), [`chevalley_sec3_3_lemma1`](WeilClasses/External/Chevalley/Sec2_2.lean#L465), [`igusa_prop3_invariant`](WeilClasses/External/Igusa/Sec10.lean#L1980), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034), [`igusa_prop3_normalForm_of_sq`](WeilClasses/External/Igusa/Sec10.lean#L2041), [`igusa_prop3_orbit_complex`](WeilClasses/External/Igusa/Sec10.lean#L2050), [`igusa_prop3_normalForm`](WeilClasses/External/Igusa/Sec10.lean#L2093), [`igusa_lemma2`](WeilClasses/External/Igusa/Sec10.lean#L2119), [`igusa_lemma2_stab_odd`](WeilClasses/External/Igusa/Sec2_2.lean#L1354) |
| Example 10.2.2 | [`example10_2_2_theta_sq`](WeilClasses/Igusa/CM.lean#L1970) | – |
| Example 10.2.2 | [`example10_2_2_w`](WeilClasses/Igusa/CM.lean#L1984) | – |
| Example 10.2.2 | [`example10_2_2_steps`](WeilClasses/Igusa/CM.lean#L1993) | – |
| Example 10.2.2 | [`example10_2_2`](WeilClasses/Igusa/CM.lean#L2023) | – |
| Example 10.2.2 | [`example10_2_2_principal`](WeilClasses/Igusa/CM.lean#L2030) | – |
| Example 10.2.2 | [`example10_2_2_alpha`](WeilClasses/Igusa/CM.lean#L2041) | – |
| Example 10.2.2 | [`example10_2_2_field`](WeilClasses/Igusa/CM.lean#L2057) | – |
| Example 10.2.3 | [`example10_2_3`](WeilClasses/Igusa/CM.lean#L2095) | – |
| Example 10.2.3 | [`example10_2_3_field`](WeilClasses/Igusa/CM.lean#L2104) | – |

The route check compares, for each result that the paper proves, the numbered results its formal proof uses with those
that the paper's proof cites ([`docs/paper_routes.tsv`](docs/paper_routes.tsv), extracted from the TeX source). Every proof uses the results
that the paper's proof cites, except the differences recorded, each with its reason, in [`docs/route_differences.tsv`](docs/route_differences.tsv):
uses that the paper leaves implicit (for example its standing step "`W₁ ∩ W₂ = 0` by Lemma 2.2.1"), the departures of
Section 7, and the paper's §§7–9 taken as the hypothesis [`SecantSheafDeformation`](Challenge.lean#L660).

## 9. Not formalized

- **Sheaf theory and derived categories.** §7 (semiregular coherent sheaves, projective bundles and `μ_r`-twisted
  sheaves, Conjecture 7.3.9 and its proof for families of abelian varieties in §7.4); the constructions of sheaves in
  §8 (the ideal sheaves of Lemma 8.2.1 and Examples 8.2.2–8.2.4, the obstruction maps of §8.3 beyond Lemma 8.3.1,
  §8.4 and §8.5); all of §9 (general position, the reflexive sheaf `E` and its semiregularity, the descent to `Y`); the
  Appendix (§11, Tor sheaves); §5.1 (the factorization through `Spin(V)` of the action of autoequivalences, and
  (5.1.3)); Lemma 6.2.1 and the objects of §6.2 before Lemma 6.2.3 (the sheaves (6.2.1), `ι_F`, Definition 6.2.2);
  and the statements of Theorem 1.4.1(2) and (5) about sheaves, except the rank of `E`. These enter
  Theorem 1.5.1 through the hypothesis [`SecantSheafDeformation`](Challenge.lean#L660) (Section 2), and the cohomological classes they produce
  enter as `ch(F₁)` (Lemma 8.2.1) and `ch(E)`.
- **Algebraic cycles and moduli.** Algebraic classes are an abstract system with hypotheses (Section 6); the results
  of Section 2 that are assumed are not formalized.
- **Claims not used in proofs.** E1 (`ρ` and `ρ'` over `ℤ`); the invariant ring of `Spin(12)` on `S⁺` and the tangent
  variety of `V(J)` (§10.1, context); the moduli spaces of Gulbrandsen in Example 10.2.2 and the
  ideal sheaves of Example 10.2.3 (only the cohomological identities are formalized).
- **The parts of Igusa's Proposition 3 that are assumed** (Section 2).

## 10. What's next

The search was made on 4 October 2026 (arXiv listings and API, Semantic Scholar, OpenAlex, Crossref, zbMATH,
Google Scholar, MathOverflow, blogs, GitHub and Zenodo) and checked by a second reader against each source.

### Since the paper

- **No later version, erratum or counterexample.** arXiv shows v1 (5 February 2025) and v2 (8 June 2025), with no
  journal reference. The author has corrected §2.1 and Lemma 2.2.2 in the program for the JAVA 2026 school (E4, E28).
- **E. Markman, *Secant sheaves and Weil classes on abelian varieties*** (arXiv:2509.23403, Proceedings of the ICM
  2026, published). A survey of the proof and its generalization to CM fields `K ⊃ F`; Corollary 1.3: the Hodge
  conjecture for abelian varieties of dimension at most `5` (with Tankeev's theorem and [Moonen–Zarhin 1999,
  Th. 0.2]); §11.5 supplies the passage to all of moduli (E3). The candidate object of its §12 for eightfolds needs
  the twist `𝒪_X(3Θ)`, not `𝒪_X(Θ)`. This correction to the survey is due to B. L. Ross (GitHub
  `brianross93/thetatwist`, July 2026), was found independently in the H8 archive of Bhattacharjee, Mandal and
  Bhattacharya (Zenodo, unrefereed), and was recomputed here.
- **E. Markman, *Secant sheaves on abelian n-folds with real multiplication …*** (arXiv:2509.23079, preprint). For
  CM fields with real quadratic `F`, reduces the algebraicity of Weil classes to the semiregularity of a sheaf
  `Φ(F₁ ⊠ F₂^∨)`; "the semiregularity of E has not been addressed yet" (abstract).
- **C. Voisin, Séminaire Bourbaki, exposé 1248** (January 2026), and Voisin's survey in *J. Open Math. Problems* 1
  (2025): expositions of the proof. Bourbaki Lemma 2.9 replaces Schoen's degeneration by a product with a Weil
  surface.
- **A. Perry, *The semiregularity theorem for equivariant noncommutative varieties*** (arXiv:2604.00511, preprint)
  claims Conjecture 7.3.9 for smooth proper algebraic families, étale-locally on the base ("This answers a question
  of Markman"), and an equivariant version that would replace the reflexivity and descent of §9.
- **New proofs and related results for fourfolds.** S. Floccari and L. Fu (*J. Math. Pures Appl.* 2026) give a proof
  for Weil fourfolds of discriminant `1` through singular OG6 varieties, independent of the paper; B. van Geemen and
  A. Rapagnetta (arXiv:2607.18341, preprint) claim another for very general such fourfolds. The Hodge conjecture for
  all powers of these fourfolds is due to Floccari (*Geom. Topol.* 30 (2026)), independently of the paper.
- **Applications.** M. Broe (arXiv:2608.28651, preprint) claims the Tate conjecture for abelian fourfolds over finite
  fields, applying Theorem 1.5.1 to CM sixfolds; N. Li (arXiv:2609.27916, 2609.06265, preprints) claims the Hodge
  conjecture for powers of CM fourfolds and the Tate conjecture for abelian fivefolds over finite fields.
- **Limits.** P. Brosnan (arXiv:2609.14169, preprint): maximal degenerations of Weil-type families exist only in the
  split case (Prop. 4 there). So Kontsevich's tropical approach, which needs one, can test only split families, where
  Theorem 1.5.1 holds; Brosnan concludes that it "cannot disprove the Hodge conjecture for Weil type abelian 6-folds".
  Non-maximal degenerations are not excluded. Engel, de Gaay Fortman and Schreieder (arXiv:2507.15704, preprint): the
  integral Hodge conjecture fails for very general principally polarized abelian varieties of dimension at least `4`.

### Open directions

1. **Formal foundations for §§7–9.** Replacing [`SecantSheafDeformation`](Challenge.lean#L660) needs coherent and twisted sheaves, Atiyah
   classes, the semiregularity map and their deformation theory, none of which is in Mathlib. Perry's equivariant
   theorem, if confirmed, would shrink what is needed: the `G`-semiregularity of `I_{∪Cᵢ} ⊠ I_{∪Σᵢ}` (the paper's
   Lemmas 8.3.7, 8.4.1, 9.3.2) and Corollary 1.3.2 (proved here), without the reflexivity, the general-position
   assumptions and the descent of §9.
2. **Higher dimensions.** Split Weil `2n`-folds with `n ≥ 4`: the paper constructs secant sheaves for every `n`
   (Examples 8.2.3–8.2.4), but their semiregularity can hold for at most finitely many `d` (TeX l. 3840–3847, 3911).
   Split eightfolds would give, by a product with a Weil surface, the Weil classes of sixfolds of every discriminant.
3. **Other discriminants and other fields.** Every construction so far reaches only the split component
   (Lemma 3.1.3; van Geemen–Rapagnetta, Lemma 1.5). For CM fields `K ⊃ F` with `F ≠ ℚ`, together with item 2, André's
   reduction would give the Hodge conjecture for CM abelian varieties.
4. **Other secant sheaves on threefolds (§10).** Gulbrandsen's bundles of Example 10.2.2 have `ch = 2α`; their
   obstruction maps are not computed.
5. **For the formalization: the assumed results.** [`VanGeemenModuli`](Challenge.lean#L405) (Landherr's classification and the symmetric
   domain of `SU(n, n)`), [`VoisinLocus`](Challenge.lean#L390), and the Moonen–Zarhin and Schoen results each need substantial Hodge theory;
   Voisin's Lemma 2.9 would replace [`SchoenDegeneration`](Challenge.lean#L425) by an argument in the cohomological model. It needs Künneth,
   push-forward of algebraic classes along projections (not among the present hypotheses), Weil surfaces of every
   discriminant ([van Geemen, Th. 5.2]) and Lefschetz (1,1). Connecting [`CycleClasses`](Challenge.lean#L347) to actual cycles would use a
   formal statement of the Hodge conjecture such as Paul-Lez/HodgeConjecture (work in progress).

### Simpler proofs

- **Proposition 6.1.2 without sheaves** (checked in Lean, [`proposition6_1_2`](WeilClasses/Orlov/Sec6_1.lean#L303)). Instead of the reduction to abelian
  surfaces (Obata, Verbitsky, ideal sheaves), write `B₀ = S + A` with `S = ½(•,•)_V` symmetric and `A` alternating:
  `ψ_{B₀} = exp(ι_A) ∘ ψ_S`, `ψ_S ∘ φ` is equivariant ([Trautman, Th. 1(i)], cited in Remark 2.3.1), and Lemmas 6.1.1
  and 6.3.2 turn the correction into cup product with `exp(½[c₁(𝒫) - ρ_g c₁(𝒫)])`. This proves (6.1.10) over every
  field of characteristic `0`, and it is what Remark 2.3.1 motivates (TeX l. 2280). Given it, Lemma 6.2.5 is the case
  `n = 2`, and `ℓ` in Lemma 6.2.3 is the `H²_P`-component of `-½c₁(𝒫)`, which also proves that `ℓ` has type `(1,1)`
  (E20).
- **Proposition 2.4.4 on `V_ℝ`**. For real `x = (w, y)` and `z = θ⁻¹(w)`, `g_P(x, x) = -Θ(z ∧ Iz) - dΘ(y ∧ Iy) < 0` by
  ampleness, without Lemma 2.4.2's four summands (closes E14).
- **Remark 2.4.3.** `I_θ = (I_{θ/2})²`, so every `I_θ` has trivial spinor norm and lifts to `Spin(V_ℝ)` (closes E13).
- **Lemma 2.3.2.** `ψ([pt_X][pt_X̂]) = (-1)ⁿ exp(c₁(𝒫))` gives both parts at once, with the factor `(-1)ⁿ` of E11.
- **That `ρ'` factors through `SO⁺(V)`** (used in the proof of Proposition 6.1.2, TeX l. 2298): `ρ(g) = ρ(g')` implies
  `g' = ±g`, hence `m_{g'} ⊗ m_{g'} = m_g ⊗ m_g`; the paper gives no proof, and this one does not use Proposition 6.1.2
  (checked in Lean, [`rhoPrime_factors`](WeilClasses/Orlov/Sec6_4.lean#L232)).
- **Lemma 8.1.1** by the Bruhat decomposition `SL₂(K) = U B ⊔ w B`: the orbit of `[1]` is `{[exp(kΘ)] : k ∈ K} ∪
  {[Θⁿ]}` on `K`-points, without the rational normal curve (checked in Lean, `lemma8_1_1`).
- **Lemma 4.0.2.** `Ω_P` is the classical symmetric domain of `SU(H)` (positive `n`-planes in `W_{1,ℂ}`), on which
  `SU(n, n)` acts transitively; this gives one orbit and the connectedness of `Ω_P` directly (the formalization
  proves transitivity with Cartan involutions).
- **Density statements.** Borel's density theorem (`SU(n, n)` has no compact factor) gives the irreducibility used in
  Lemmas 2.2.4, 2.2.7, Corollary 4.0.4, Lemma 6.2.3 and Lemma 10.2.1 in one stroke (E8, E19, E20, E27); the
  formalization, which has no algebraic groups, replaces it by explicit transvections and weights.

### The formalization

- Replace the hypotheses of Section 2 layer by layer, as the project owner intends. A possible order: first the
  results that are linear algebra or Hodge theory of tori ([`VanGeemenModuli`](Challenge.lean#L405), the Moonen–Zarhin computations of Hodge
  rings, [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034)), then the geometric ones ([`VoisinLocus`](Challenge.lean#L390), [`SchoenDegeneration`](Challenge.lean#L425)), and finally the sheaf
  theory of §§7–9.
- Contributions to Mathlib that would help: Hodge structures and Mumford–Tate groups, algebraic groups with density
  theorems, Clifford algebras over `ℤ` (the integral `C(V)` of E4, here [`WeilClasses.CZ`](WeilClasses/Spinor/Integral.lean#L99) and [`WeilClasses.SpinZ`](WeilClasses/Spinor/Integral.lean#L183)), and
  the classification of Hermitian forms over number fields.
