# The Hasse–Minkowski theorem over ℚ (vendored)

This directory is a copy of the Hasse–Minkowski development of
[jayyswan/hasse-minkowski](https://github.com/jayyswan/hasse-minkowski) (authors: jayyswan, Nirvana Coppola,
María Inés de Frutos-Fernández; parts derive from
[mariainesdff/HassePrinciple](https://github.com/mariainesdff/HassePrinciple)), as packaged in
[Vilin97/lean-pool](https://github.com/Vilin97/lean-pool) at commit `98ae4aac92035e84f5369b6f5e2eb8fc21b9ef86`
(directory `LeanPool/HasseMinkowski`), which builds on this project's Lean toolchain. It is released under the
Apache License 2.0, the license of this repository; the copyright notices at the top of the files are kept.

The module path changed from `LeanPool.HasseMinkowski` to `WeilClasses.External.HasseMinkowski`; the two other
edits are listed at the end. This project's documents do not describe these files as its own work.

## What this project uses

* `HasseMinkowski.meyer` (`Main.lean`): an indefinite quadratic form over `ℚ` in at least five variables is
  isotropic (Meyer's theorem). It is the arithmetic input of Landherr's classification of Hermitian forms over
  `K = ℚ(√-d)`, through which [van Geemen, Th. 5.2(3)] is proved in the case that Theorem 1.5.1 uses
  (`WeilClasses/External/VanGeemen/`).

The development also proves the isotropy form of the Hasse–Minkowski theorem (`HasseMinkowski.hasseMinkowski`),
Hilbert symbols at every place with Hilbert reciprocity, and the Hasse invariant.

Two edits were needed to compile against this project's Mathlib commit (`ec6a61c`, four days after lean-pool's):
`RankTwo.lean` imports `Mathlib.Tactic.LinearCombination`, which lean-pool's Mathlib reached transitively; and in
`Padics/Squares.lean` two norm identities `‖x - 1‖ = ‖z‖` for `z = ⟨x - 1, _⟩ : ℤ_[p]` are closed by `rfl`
instead of `simp`.
