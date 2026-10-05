# Roadmap: from a conditional to a complete formalization

Theorem 1.5.1 and Corollary 1.6.1 are proved here from named hypotheses ([REPORT.md, Section 2](REPORT.md#assumed)), and three results of
§10 from two parts of Igusa's Proposition 3. This roadmap says how to remove those hypotheses and formalize what is
still missing ([REPORT.md, Section 9](REPORT.md#9-not-formalized)). The work is planned in layers. Each layer replaces some hypotheses by
constructions and proofs from more basic ones, and ends in a state that can be released.

Sizes are rough, in lines of Lean, calibrated on this project (about 63,500 lines): **S** under 1,000; **M**
1,000–5,000; **L** 5,000–20,000; **XL** more, or foundations that Lean does not have yet. "Pinned Mathlib" is the
Mathlib commit of this project (`ec6a61c`); "elsewhere" is the wider Lean ecosystem as surveyed on 4 October 2026.

## What is missing

| Missing piece | Source | Used by | What it needs | Available now | Size | Layer |
|---|---|---|---|---|---|---|
| [`VanGeemenModuli`](Challenge.lean#L405) | [van Geemen, Th. 5.2(3)] | Theorem 1.5.1 | Landherr's classification of Hermitian forms over `K = ℚ(√-d)` by rank, discriminant and signature, through Jacobson's trace-form theorem and Hasse–Minkowski over `ℚ`; connectedness of the Weil-type period domain of every form of signature `(m, m)` (proved here for the domains `Ω_P` of §4, Lemma 4.0.2, which include that of `X × X̂`, [`weilDomain_eq_image_OmegaP`](WeilClasses/Main/Compare.lean#L1945)) | Pinned Mathlib: quadratic forms and their isometries; no Hasse–Minkowski, no Hilbert symbols. Elsewhere: Hasse–Minkowski over `ℚ` in the isotropy form ([jayyswan/hasse-minkowski](https://github.com/jayyswan/hasse-minkowski), also in [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) on this project's toolchain); the classification of quadratic forms over `ℚ_p` and Witt cancellation in Tau Ceti. Nowhere: Hermitian forms over quadratic extensions, Jacobson's or Landherr's theorem. | M–L | 1 |
| [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034) | [Igusa, Prop. 3] | Lemma 10.1.1, Remark 10.1.2(2), Lemma 10.2.1 | The generic `Spin(12)`-orbit on `S⁺`: every `w` with `J(w) ≠ 0` lies on a secant through two pure spinors with transversal maximal isotropic subspaces, defined over `F` when `-J(w)` is a square | This project: generators of `Spin(V_F)` and the invariance of `J` ([`WeilClasses/External/Igusa/README.md`](WeilClasses/External/Igusa/README.md)); Clifford algebras in Mathlib, spin groups in Tau Ceti. Elsewhere: nothing on Igusa's classification or on pure spinors. | M | 1 |
| [`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2072) | [Igusa, Prop. 3] | Remark 10.1.2(1) | When `-d` is not a square in `F`: the stabilizer is `SU(h)` for a Hermitian form `h` over `F(√-d)`, and `H¹(F, SU(h)) → H¹(F, Spin(V))` is injective (Jacobson) | Pinned Mathlib: group cohomology and Hilbert 90; no Galois cohomology of algebraic groups. Tau Ceti: Galois cohomology, Hilbert 90 for infinite Galois extensions, Galois descent (the input to `H¹(G, GLₙ) = 1`). Nowhere: `H¹(k, SU(h))`. | M–L | 1 |
| [`SchoenDegeneration`](Challenge.lean#L425) | [Schoen, Prop. 10] | Corollary 1.6.1 | Schoen's degeneration argument; or, replacing it, Voisin's Lemma 2.9 (Bourbaki exposé 1248): Künneth and Weil surfaces of every discriminant in the model, Lefschetz (1,1), and push-forward of algebraic classes along projections, a new but standard hypothesis | Voisin's route needs nothing beyond the model except push-forward | M (Voisin's route) | 1 |
| [`MoonenZarhinSimple`](Challenge.lean#L432) | [Moonen–Zarhin 1995, Th. 2.11] | Corollary 1.6.1 | Albert's classification of the endomorphism algebras of simple abelian fourfolds; their Hodge (Mumford–Tate) groups and the invariants of these groups, case by case | Pinned Mathlib: central simple algebras, the start of Brauer groups; no algebraic groups, Mumford–Tate groups or Albert classification. Tau Ceti: Hodge structures, polarizations, semisimplicity of polarizable rational Hodge structures; reductive classical groups over fields. Nowhere: Mumford–Tate groups. | XL | 1 |
| [`MoonenZarhinLowDim`](Challenge.lean#L454) | [Moonen–Zarhin 1999, Prop. 3.8, Th. 0.1(i)] | Corollary 1.6.1 | The same for `A` isogenous to `B × E`, `B` a simple threefold | As above | L–XL | 1 |
| Abelian varieties and their algebraic classes | — | Every statement about [`CycleClasses`](Challenge.lean#L347) | Complex abelian varieties (complex tori with a Riemann form, projective by the Lefschetz embedding theorem); Riemann's theorem identifying them up to isogeny with polarizable rational Hodge structures of weight one ([`AbVar`](Challenge.lean#L257)); `H*(A, ℚ) = ⋀•H¹(A, ℚ)` with its Hodge decomposition; algebraic classes and the instance of [`CycleClasses`](Challenge.lean#L347) they form | Pinned Mathlib: algebraic cycles on schemes (the definition), commutativity of proper group schemes over a field, singular homology (basics), sheaf cohomology on sites, smooth vector bundles; no complex tori, cycle class map, Chern classes or Hodge decomposition. Elsewhere: [Paul-Lez/HodgeConjecture](https://github.com/Paul-Lez/HodgeConjecture) defines smooth projective complex varieties, the rational cohomology of `X(ℂ)`, cycle classes and Hodge classes, and states the Hodge conjecture for abelian varieties (draft PR #231: Chow groups). Tau Ceti: abelian varieties as group schemes, weight-one Hodge structures as complex structures, Riemann forms as polarizations, singular cohomology with cup product. lean-pool: complex tori as compact complex Lie groups. Nowhere: `H*(A, ℚ) = ⋀•H¹(A, ℚ)` as rings, Appell–Humbert, the Lefschetz embedding theorem. | XL | 2 |
| [`PullbackClosed`](Challenge.lean#L353) | standard | Theorem 1.5.1, Corollary 1.6.1 | Pullback of cycles along homomorphisms, compatible with cycle classes; every rational Hodge map between the `H¹` comes from a homomorphism up to isogeny (Riemann) | — | L | 3 |
| [`SubalgebraClosed`](Challenge.lean#L359) | standard | Theorem 1.5.1, Corollary 1.6.1 | Intersection products compatible with the cup product; formal if algebraic classes are defined by Chern characters (Layer 2) | — | L–XL | 3 |
| [`LefschetzOneOne`](Challenge.lean#L365) | the Lefschetz (1,1) theorem | Theorem 1.5.1, Corollary 1.6.1 | For abelian varieties: the Appell–Humbert theorem (line bundles on complex tori), algebraicity of line bundles (theta functions, the Lefschetz embedding theorem, GAGA for line bundles), `c₁` as the class of a divisor | Pinned Mathlib: Jacobi's theta function in one variable. Elsewhere: Paul-Lez/HodgeConjecture PR #228 (open) proves rational Lefschetz (1,1) for smooth projective complex varieties, through GAGA from [chrisflav/oka](https://github.com/chrisflav/oka); here it still needs Layer 2. | L | 3 |
| [`VoisinLocus`](Challenge.lean#L390) | [Voisin, §4.2] | Theorem 1.5.1 | Relative Hilbert schemes (or Chow varieties) of the universal family over the period domain: countably many components, each proper over the base; Baire's theorem and the identity theorem then give the form assumed | Pinned Mathlib: Baire spaces, the identity theorem for analytic functions; no Hilbert schemes. Nowhere: Hilbert or Quot schemes. | XL | 3 |
| [`RamonMariProducts`](Challenge.lean#L447) | [Ramón-Marí, Th. 4.11] | Corollary 1.6.1 | The Hodge conjecture for products of two abelian surfaces: their Hodge classes, and cycles representing them | — | XL | 3 |
| [`SecantSheafDeformation`](Challenge.lean#L660) | the paper, §§7–9; [Buchweitz–Flenner, Th. 5.1] | Theorem 1.5.1 | Coherent sheaves on abelian varieties; Orlov's equivalence and Fourier–Mukai transforms; the secant sheaves of §8 (ideal sheaves of Abel–Jacobi curves); the reflexive sheaf `E` and its semiregularity (§9); twisted sheaves and the descent to `Y`; the semiregularity theorem for families of abelian varieties (§7.4) | Pinned Mathlib: abstract derived categories, sheaves of modules and ideal sheaves on schemes; no coherent cohomology of projective schemes, Fourier–Mukai transforms or deformation theory. Elsewhere: [chris-dare-dev/derived-alg-geo-lean](https://github.com/chris-dare-dev/derived-alg-geo-lean) has `Dᵇ(Coh X)` and Fourier–Mukai kernels, with base change and the projection formula as hypotheses; chrisflav/oka has coherent analytic sheaves and GAGA. Nowhere: Atiyah classes, the semiregularity map, twisted sheaves. | XL | 4 |
| The rest of the paper | the paper, §§5.1, 6.2, 7–9, 11 | (through [`SecantSheafDeformation`](Challenge.lean#L660)) | Lemma 6.2.1 and Definition 6.2.2, §5.1, the constructions of §8 beyond Lemma 8.3.1, §9, the Appendix; the integral claim E1 | As above | XL | 4 |

## The layers

### Layer 0: the present state

Theorem 1.5.1 and Corollary 1.6.1 are proved for every system of algebraic classes `Z` that satisfies the hypotheses
about cycles, assuming also the hypotheses about Hodge structures; §10 is proved under two parts of [Igusa, Prop. 3].
Everything else that the paper proves about cohomology classes, Clifford algebras, spin representations, Hodge
structures and period domains is proved.

### Layer 1: the hypotheses about Hodge structures

These are statements about rational Hodge structures and spin representations, with no algebraic cycles. They can
be proved in the present model, with number theory, linear algebra and some Lie theory, and each can be done on its
own.

- **1a. [`VanGeemenModuli`](Challenge.lean#L405).** The Hermitian form of a polarized abelian `2m`-fold of Weil type has signature
  `(m, m)` (Lemma 3.1.2 proves it for the secants of §3); Landherr's theorem makes two such forms with the same
  discriminant isometric; the isometry carries one Weil-type period domain onto the other, and the domain is
  connected (generalize the Cartan-involution argument of Lemma 4.0.2 from `Ω_P` to every form of signature
  `(m, m)`). Hasse–Minkowski over `ℚ` exists outside Mathlib (in the isotropy form; the isometry form follows with
  Witt cancellation, which Tau Ceti has); what is missing is the theory of Hermitian forms over `K` and Jacobson's
  reduction to their trace forms.
- **1b. Igusa's Proposition 3.** The normal form ([`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034)) completes Igusa's classification of the
  generic orbit, on top of the generation of `Spin(V_F)` and the invariance of `J` proved in
  [`WeilClasses/External/Igusa/`](WeilClasses/External/Igusa) (estimated there at 1,500–3,000 lines). The orbits over subfields of `ℂ`
  ([`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2072)) add a Galois-cohomology argument for `SU(h)`. With both, §10 is unconditional.
- **1c. [`SchoenDegeneration`](Challenge.lean#L425) traded for push-forward.** Voisin's Lemma 2.9 (Séminaire Bourbaki, exposé 1248)
  proves the Hodge conjecture for the Weil classes of `A₂` from that of `A₁` and `A₁ × A₂`, through
  `w₂ = pr₂,*(pr₁^* w₁ ∪ w)`; with `A₁` a Weil surface (whose Weil classes are algebraic by Lefschetz (1,1)) of a
  suitable discriminant, it gives the fourfolds from the sixfolds of discriminant `-1`. In the model this needs
  products of abelian varieties (Künneth), Weil surfaces of every discriminant, and a new hypothesis that push-forward
  along projections preserves algebraic classes, which is standard and is proved in Layer 3 with the others. It
  replaces the paper's use of [Schoen, Prop. 10] in Corollary 1.6.1, a departure from the paper's proof (reason 2),
  to be agreed with the owner.
- **1d. Moonen–Zarhin.** [`MoonenZarhinSimple`](Challenge.lean#L432) and [`MoonenZarhinLowDim`](Challenge.lean#L454) need Albert's classification of endomorphism
  algebras and the Hodge (Mumford–Tate) groups of abelian fourfolds. This is the largest part of Layer 1, and it only
  serves Corollary 1.6.1.

**Release after 1a–1c:** Theorem 1.5.1 under [`PullbackClosed`](Challenge.lean#L353), [`SubalgebraClosed`](Challenge.lean#L359), [`LefschetzOneOne`](Challenge.lean#L365), [`VoisinLocus`](Challenge.lean#L390)
and [`SecantSheafDeformation`](Challenge.lean#L660), all about algebraic cycles or the paper's own §§7–9; §10 unconditional; Corollary 1.6.1
under these, push-forward, [`RamonMariProducts`](Challenge.lean#L447) and the two Moonen–Zarhin results until 1d is done.

### Layer 2: actual abelian varieties and their algebraic classes

In the model, [`AbVar`](Challenge.lean#L257) stands for a complex abelian variety up to isogeny and [`CycleClasses`](Challenge.lean#L347) for its algebraic
classes, but nothing ties them to geometry. Layer 2 builds that tie:

- complex abelian varieties: complex tori with a Riemann form, projective by the Lefschetz embedding theorem; and
  Riemann's theorem that, up to isogeny, they are the polarizable rational Hodge structures of weight one, which is
  what [`AbVar`](Challenge.lean#L257) encodes;
- `H*(A, ℚ) = ⋀•H¹(A, ℚ)`, with the Hodge decomposition (for a torus, by translation-invariant forms);
- algebraic classes, by one of two equivalent definitions on smooth projective varieties: the classes of algebraic
  cycles (the standard one, through a cycle class map), or the `ℚ`-span of the homogeneous components of Chern
  characters of algebraic vector bundles (equivalent by Grothendieck–Riemann–Roch). The second is closer to the
  paper, whose classes are Chern characters of sheaves, and makes [`SubalgebraClosed`](Challenge.lean#L359) and [`PullbackClosed`](Challenge.lean#L353)
  consequences of the multiplicativity and naturality of the Chern character. The choice decides much of the cost of
  Layer 3;
- the instance of [`CycleClasses`](Challenge.lean#L347) given by algebraic classes, and the main theorems restated for it.

Two existing projects shape the choices. [Paul-Lez/HodgeConjecture](https://github.com/Paul-Lez/HodgeConjecture) states the Hodge conjecture for smooth projective
complex varieties, with cycle classes in the rational cohomology of `X(ℂ)`, and a variant for abelian varieties; using
its definitions would let Corollary 1.6.1 be stated in its terms. Tau Ceti's weight-one Hodge structures and Riemann
forms (`isRiemannForm_iff_isPolarization`) could replace the part of the model in [`WeilClasses/Defs.lean`](WeilClasses/Defs.lean) that encodes
abelian varieties up to isogeny.

The statements of record may import only Lean, Mathlib and Tau Ceti, and the Challenge is limited to 1,000 lines. So
the definitions of this layer must reach Mathlib or Tau Ceti before the restated theorems can replace the present
statements of record.

**Release:** the main theorems about actual algebraic cycles, still under the hypotheses of Layer 3 and Layer 4.

### Layer 3: the hypotheses about algebraic cycles

With Layer 2: [`PullbackClosed`](Challenge.lean#L353) and [`SubalgebraClosed`](Challenge.lean#L359) (functoriality of cycle classes, or of the Chern character);
[`LefschetzOneOne`](Challenge.lean#L365) (from Paul-Lez/HodgeConjecture's PR #228 for all smooth projective varieties, or for abelian
varieties from Appell–Humbert and the algebraicity of line bundles); push-forward along projections, if 1c replaced
Schoen's degeneration; then [`VoisinLocus`](Challenge.lean#L390), which needs relative Hilbert schemes, and [`RamonMariProducts`](Challenge.lean#L447).

**Release:** Theorem 1.5.1 under [`SecantSheafDeformation`](Challenge.lean#L660) alone (and [`VoisinLocus`](Challenge.lean#L390) until it is done).

### Layer 4: the paper's sheaf theory

[`SecantSheafDeformation`](Challenge.lean#L660) is the paper's own §§7–9: Orlov's equivalence on `X × X̂`, the secant sheaves of §8, the
reflexive sheaf `E` and its semiregularity, twisted sheaves and the descent to `Y`, and the semiregularity theorem for
families of abelian varieties (§7.4, after [Buchweitz–Flenner]). With them come the parts of §§5.1, 6.2, 8 and 11 that
are not formalized ([REPORT.md, Section 9](REPORT.md#9-not-formalized)). A. Perry's equivariant semiregularity theorem (arXiv:2604.00511,
preprint), if confirmed, would remove the reflexive sheaf and the descent of §9: what would remain is the
`G`-semiregularity of `I_{∪Cᵢ} ⊠ I_{∪Σᵢ}` (Lemmas 8.3.7, 8.4.1, 9.3.2) and Corollary 1.3.2, which is proved here.

**Release:** Theorem 1.5.1 and Corollary 1.6.1 unconditional.

### Order

```text
Layer 1   1a van Geemen   1b Igusa   1c Voisin's Lemma 2.9   (independent; release after the three)
          1d Moonen–Zarhin                                     (long; any time)
Layer 2   abelian varieties, H*(A, Q), algebraic classes       (in Mathlib)
Layer 3   the hypotheses about cycles                          (needs Layer 2)
Layer 4   §§7–9: sheaves, Fourier–Mukai, semiregularity        (needs Layer 2)
```

Layer 1 can start now and in parallel. Layers 2–4 are mostly foundational work in Mathlib, where Layer 4's sheaf
theory can start independently of Layer 2.

## How to remove a hypothesis

1. **Narrow it first.** Several hypotheses are stated more generally than the proofs use them: [`VanGeemenModuli`](Challenge.lean#L405)
   for every `m` (only `m = 3` is used), [`IgusaProp3NormalForm`](WeilClasses/External/Igusa/Sec10.lean#L2034) for every field embedded in `ℂ` (only `ℂ`, `K` and
   the algebraic closure of `ℚ` in `ℂ` are used). Restricting a hypothesis to what is used makes the theorems
   stronger and the later proof shorter.
2. **State the source's result precisely**, in `WeilClasses/External/<Source>/` with a README entry, as close to
   the source as the model allows, and have it reviewed against the source before proving it, as the paper's
   statements were. The hypothesis classes are this project's formulations; the theorem that replaces one must
   imply it.
3. **Prove it**, then replace the class: for a hypothesis without parameters, an `instance`; for one about a system
   of algebraic classes `Z`, an instance for the actual system (Layer 2). Then drop the argument from the theorems.
4. **Release.** Dropping a hypothesis changes the statements of record: update [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean),
   [`REPORT.md`](REPORT.md) (Sections 2 and 8), [`README.md`](README.md) and [`formalization.yaml`](formalization.yaml); rerun the audit, the route check, Comparator
   and Palomar's preflight; submit the new version.
5. **Upstream** what is general (Hasse–Minkowski, Hermitian forms, Galois cohomology, pure spinors) to Mathlib or
   Tau Ceti, where it is maintained with the libraries it builds on.

## Existing Lean work to build on

Surveyed on 4 October 2026; check again before starting a layer, since these projects move quickly.

| Project | Status | Provides | Layer |
|---|---|---|---|
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (pinned here) | active; this project's toolchain | Hodge structures (weight one as complex structures, Riemann forms as polarizations, semisimplicity, mixed Hodge structures); spin groups, spinor norms, half-spin representations; quadratic forms over `ℚ_p`, Hilbert symbols, Witt cancellation; classical algebraic groups over fields; Galois cohomology and descent; singular cohomology with cup product; abelian varieties as group schemes | 1, 2 |
| [jayyswan/hasse-minkowski](https://github.com/jayyswan/hasse-minkowski), also in [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) | complete, no `sorry`; lean-pool's copy builds on this project's toolchain | Hasse–Minkowski over `ℚ` (isotropy form), Meyer's theorem, Hilbert symbols and reciprocity | 1a |
| [Paul-Lez/HodgeConjecture](https://github.com/Paul-Lez/HodgeConjecture) | active, work in progress; Lean `v4.33.1` | Smooth projective complex varieties, rational cohomology of `X(ℂ)`, cycle classes, Hodge classes, the statement of the Hodge conjecture and of its variant for abelian varieties; PR #228 (open): rational Lefschetz (1,1); PR #231 (draft): Chow groups | 2, 3 |
| [chrisflav/oka](https://github.com/chrisflav/oka) | active; Lean `v4.32.0` | Complex analytic spaces, coherent analytic sheaves, analytification, GAGA for proper schemes | 2, 3, 4 |
| lean-pool `JacobianDiffgeo` (in [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool)) | builds on this project's toolchain | Complex tori `V/L` as compact complex Lie groups; Jacobians of compact Riemann surfaces | 2 |
| [chris-dare-dev/derived-alg-geo-lean](https://github.com/chris-dare-dev/derived-alg-geo-lean) | very active; Lean `v4.32.1` | `Dᵇ(Coh X)`, perfect complexes, Fourier–Mukai kernels (base change and the projection formula as hypotheses) | 4 |

Nothing was found, in Mathlib, Tau Ceti or elsewhere, for Hermitian forms over quadratic or CM extensions (Jacobson,
Landherr), nonabelian Galois cohomology such as `H¹(k, SU(h))`, Borel density, Mumford–Tate groups, Igusa's
classification of half-spinors, Appell–Humbert and theta functions on `ℂ^g`, the Lefschetz embedding theorem, the
cohomology ring of a torus, pull-backs and intersection products of cycles, Hilbert schemes, Atiyah classes, the
semiregularity map, or twisted sheaves. Each layer therefore contains foundational work that belongs upstream.
