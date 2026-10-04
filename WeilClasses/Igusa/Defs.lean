module

public import WeilClasses.PureSpinor.CM
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# The Igusa quartic on the half-spin representation `S⁺` of an abelian threefold (paper §10.1)

Let `X` be an abelian threefold (`n = 3`), so that `V` has rank `12` and `S⁺ = H^ev(X)` has
dimension `32`. We fix the basis `e₁, …, e₆` of `H¹(X, ℤ)` of `WeilClasses.Spinor.Defs`, with
`∫_X e₁ ∧ ⋯ ∧ e₆ = 1` and `[pt_X] = e₁ ∧ ⋯ ∧ e₆`. **Indices are 0-based in Lean**: `i : Fin 6`
stands for the paper's `i + 1`; e.g. `eStar F 0 3` is the paper's `e₁₄^*`.

## Main definitions

* `WeilClasses.pf4`, `WeilClasses.pf6`: Pfaffians of `4 × 4` and `6 × 6` alternating matrices,
  normalized as in §10.1 by `Pf [[0, I_r], [-I_r, 0]] = 1` (`pf4_stdAlt`, `pf6_stdAlt`). This is
  `(-1)^{r(r-1)/2}` times the usual Pfaffian, i.e. its negative for `r = 2, 3`.
* `WeilClasses.crossOut`: the matrix `X_ij` obtained from a `6 × 6` matrix by crossing out the
  `i`-th and `j`-th rows and columns.
* The coordinates (10.1.1) of `x ∈ S⁺_F`: `x0` (degree `0`), `xCoord x i j` (coefficient of
  `e_i ∧ e_j`, `i < j`), `yCoord x i j` (coefficient of `e_ij^*`), `y0` (coefficient of
  `[pt_X]`), where `e_ij^* = (-1)^{i+j-1} e₁ ∧ ⋯ ê_i ⋯ ê_j ⋯ ∧ e₆` (`WeilClasses.eStar`), so that
  `e_i ∧ e_j ∧ e_ij^* = [pt_X]`; the alternating matrices `xMat x = (x_ij)`, `yMat x = (y_ij)`.
* `WeilClasses.J`: the Igusa quartic (10.1.1), as a function `S_F → F` (it only reads the even
  coordinates; the paper's `J` is its restriction to `S⁺_F`).
* `WeilClasses.Jcone`: the cone `Ṽ(J) ⊆ S⁺_F`; `WeilClasses.VJ`: the quartic `V(J) ⊆ ℙ(S⁺_F)`.
* `WeilClasses.evenCoords`: the `32` coordinates of `S⁺_F`, so that `MvPolynomial EvenIdx F` is the
  coordinate ring `Sym((S⁺_F)*)`.

Reading: the paper's "alternating matrix `A` of rank `2r`" in the normalization of `Pf` means a
`2r × 2r` alternating matrix (the normalization is stated on `[[0, I_r], [-I_r, 0]]`); only
`r = 2` (the `X_ij`, `Y_ij`) and `r = 3` (`(x_ij)`, `(y_ij)`) occur.

Auxiliary notions used in the statements of §10 (for any `n`):

* `WeilClasses.spinStab F n w`: the stabilizer `Spin(V_F)_w` of a spinor `w`;
* `WeilClasses.IsTransversalSecant`: a plane `P ⊆ S_F` whose line `ℙ(P)` meets the even spinor
  variety exactly in two points `[u₁], [u₂]` with transversal `W_i = ker m_{u_i}`;
* `WeilClasses.slImage F n W₁ W₂`: the image of the embedding `e : SL(W₁) → SO(V_F)` of (10.1.2);
* base change of subspaces (`bcSubV`, `bcSubS`), subspaces defined over a subfield
  (`IsDefinedOverV`, `IsDefinedOverS`), and invariance of a subspace of `V_{F'}` under a subgroup of
  `Spin(V_F)` (`IsInvariantUnder`).

The formula for `J` and every explicit value in §10 were checked with exact rational arithmetic
(Phase-3 report for §10), including the invariance of `J` under the unipotent generators
`exp(t e_i e_j)`, `exp(t f_i f_j)`, `exp(t e_i f_j)` of `Spin(V)` and under
`(e₁ + f₁) ⋯ (e₆ + f₆)`; with any other choice of the signs of the two Pfaffian terms, or
without the sign `(-1)^{i+j-1}` in `e_ij^*`, the invariance fails.
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

/-! ## Pfaffians -/

section Pfaffian

variable {R : Type*} [CommRing R]

/-- **The Pfaffian of a `4 × 4` alternating matrix**, normalized as in §10.1:
`Pf [[0, I₂], [-I₂, 0]] = 1` (`pf4_stdAlt`). Explicitly
`Pf(A) = a₁₃ a₂₄ - a₁₂ a₃₄ - a₁₄ a₂₃` (paper's 1-based indices): the sum over the three perfect
matchings of `{1, 2, 3, 4}`, with the sign of the matching relative to `{13, 24}`. It is the
negative of the usual Pfaffian `a₁₂ a₃₄ - a₁₃ a₂₄ + a₁₄ a₂₃`. -/
def pf4 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  A 0 2 * A 1 3 - A 0 1 * A 2 3 - A 0 3 * A 1 2

/-- Pairs `(i, j)` of indices `i < j` in `Fin 6` (the paper's `1 ≤ i < j ≤ 6`, shifted by one). -/
abbrev Pair6 : Type := {p : Fin 6 × Fin 6 // p.1 < p.2}

/-- The increasing enumeration `Fin 4 → Fin 6` of `{0, …, 5} ∖ {i, j}`, for a pair `i < j`. -/
def skipTwo (p : Pair6) : Fin 4 → Fin 6 := fun k =>
  p.1.2.succAbove ((p.1.1.castLT (by have h := p.2; have h' := p.1.2.isLt; omega)).succAbove k)

/-- The `4 × 4` matrix obtained from a `6 × 6` matrix `A` by crossing out the `i`-th and `j`-th
rows and columns (the paper's `X_ij`, `Y_ij` in (10.1.1)), for a pair `p = (i, j)`, `i < j`. -/
def crossOut (A : Matrix (Fin 6) (Fin 6) R) (p : Pair6) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix (skipTwo p) (skipTwo p)

/-- **The Pfaffian of a `6 × 6` alternating matrix**, normalized as in §10.1:
`Pf [[0, I₃], [-I₃, 0]] = 1` (`pf6_stdAlt`). Defined by expansion along the first row:
`Pf(A) = Σ_{j=2}^{6} (-1)^j a_{1j} Pf(A_{1j})` (paper's 1-based indices), where `A_{1j}` is `A`
with the rows and columns `1, j` crossed out and `Pf = pf4`; equivalently, the sum over the `15`
perfect matchings of `{1, …, 6}` with the sign of the matching relative to `{14, 25, 36}`. It is the
negative of the usual Pfaffian. -/
def pf6 (A : Matrix (Fin 6) (Fin 6) R) : R :=
  ∑ j : Fin 5, (-1) ^ (j : ℕ) * A 0 j.succ * pf4 (crossOut A ⟨(0, j.succ), Fin.succ_pos j⟩)

/-- The `2r × 2r` matrix `[[0, I_r], [-I_r, 0]]` (§10.1), indexed by `Fin (r + r)`. -/
def stdAlt (r : ℕ) : Matrix (Fin (r + r)) (Fin (r + r)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 1 (-1) 0)

/-- The normalization of §10.1 for `r = 2`: `Pf [[0, I₂], [-I₂, 0]] = 1`. -/
theorem pf4_stdAlt : pf4 (stdAlt (R := R) 2) = 1 := by
  sorry

/-- The normalization of §10.1 for `r = 3`: `Pf [[0, I₃], [-I₃, 0]] = 1`. -/
theorem pf6_stdAlt : pf6 (stdAlt (R := R) 3) = 1 := by
  sorry

end Pfaffian

/-! ## Coordinates on `S_F = H*(X, F)` for an abelian threefold -/

section Coordinates

variable (F : Type*) [Field F] [CharZero F]

/-- `x₀`: the coefficient of `1 ∈ H⁰(X)` in `x ∈ S_F` ((10.1.1)). -/
noncomputable def x0 (x : S F 3) : F := (basisS F 3).repr x ∅

/-- `y₀`: the coefficient of `[pt_X] = e₁ ∧ ⋯ ∧ e₆` in `x ∈ S_F` ((10.1.1)). -/
noncomputable def y0 (x : S F 3) : F := (basisS F 3).repr x Finset.univ

/-- `x_ij`: the coefficient of `e_i ∧ e_j` in `x ∈ S_F` (meaningful for `i < j`; (10.1.1)). -/
noncomputable def xCoord (x : S F 3) (i j : Fin 6) : F := (basisS F 3).repr x {i, j}

/-- The class `e_ij^* := (-1)^{i+j-1} e₁ ∧ ⋯ ∧ ê_i ∧ ⋯ ∧ ê_j ∧ ⋯ ∧ e₆ ∈ H⁴(X, F)` of §10.1 (for
`i < j`), so that `e_i ∧ e_j ∧ e_ij^* = [pt_X]`. With the 0-based indices `i j : Fin 6` the sign
is `(-1)^{i+j+1}`. -/
noncomputable def eStar (i j : Fin 6) : S F 3 :=
  ((-1 : F) ^ ((i : ℕ) + j + 1)) • basisS F 3 ({i, j}ᶜ)

/-- `y_ij`: the coefficient of `e_ij^*` in `x ∈ S_F` (meaningful for `i < j`; (10.1.1)). -/
noncomputable def yCoord (x : S F 3) (i j : Fin 6) : F :=
  (-1 : F) ^ ((i : ℕ) + j + 1) * (basisS F 3).repr x ({i, j}ᶜ)

/-- The alternating matrix `(x_ij)` of §10.1 (`x_ji = -x_ij`, zero diagonal). -/
noncomputable def xMat (x : S F 3) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if i < j then xCoord F x i j else if j < i then -xCoord F x j i else 0

/-- The alternating matrix `(y_ij)` of §10.1 (`y_ji = -y_ij`, zero diagonal). -/
noncomputable def yMat (x : S F 3) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if i < j then yCoord F x i j else if j < i then -yCoord F x j i else 0

/-- **The Igusa quartic** (10.1.1), [Igusa, Prop. 3]:
`J(x) = x₀ Pf((y_ij)) + y₀ Pf((x_ij)) + Σ_{i<j} Pf(X_ij) Pf(Y_ij) - ¼ (x₀ y₀ - Σ_{i<j} x_ij y_ij)²`,
with the Pfaffians normalized by `Pf [[0, I_r], [-I_r, 0]] = 1` (`pf4`, `pf6`). It is defined on
all of `S_F` and only reads the coordinates of the even part; the paper's `J` is its restriction to
`S⁺_F`. -/
noncomputable def J (x : S F 3) : F :=
  x0 F x * pf6 (yMat F x) + y0 F x * pf6 (xMat F x) +
      ∑ p : Pair6, pf4 (crossOut (xMat F x) p) * pf4 (crossOut (yMat F x) p) -
    (1 / 4 : F) *
      (x0 F x * y0 F x - ∑ p : Pair6, xCoord F x p.1.1 p.1.2 * yCoord F x p.1.1 p.1.2) ^ 2

/-- The index set `{K ⊆ {1, …, 6} : |K| even}` of the `32` coordinates of `S⁺`. -/
abbrev EvenIdx : Type := {K : Finset (Fin 6) // Even K.card}

/-- The coordinates of `x ∈ S_F` along `S⁺_F`: its coefficients on the `e_K` with `|K|` even. A
polynomial in these coordinates, `p : MvPolynomial EvenIdx F`, is an element of `Sym((S⁺_F)*)`
(§10.1), with value `MvPolynomial.eval (evenCoords F x) p` at `x`. -/
noncomputable def evenCoords (x : S F 3) : EvenIdx → F := fun K => (basisS F 3).repr x K.1

/-- The cone `Ṽ(J) = {x ∈ S⁺_F : J(x) = 0}` over the quartic `V(J)` (§10.1). -/
def Jcone : Set (S F 3) := {x | x ∈ Splus F 3 ∧ J F x = 0}

/-- The quartic hypersurface `V(J) ⊆ ℙ(S⁺_F)` (§10.1; the paper calls it a hyperplane). -/
def VJ : Set (Projectivization F (Splus F 3)) := {p | J F (p.rep : S F 3) = 0}

/-- `J` is a homogeneous quartic: `J(c x) = c⁴ J(x)`. -/
theorem J_smul (c : F) (x : S F 3) : J F (c • x) = c ^ 4 * J F x := by
  sorry

/-- `[w] ∈ V(J)` if and only if `J(w) = 0`. -/
theorem mk_mem_VJ_iff (w : Splus F 3) (hw : w ≠ 0) :
    Projectivization.mk F w hw ∈ VJ F ↔ J F (w : S F 3) = 0 := by
  sorry

/-- `J` is defined over `ℚ`: it commutes with every change of coefficients `F → F'`. -/
theorem J_bcS (F' : Type*) [Field F'] [CharZero F'] [Algebra F F'] (x : S F 3) :
    J F' (bcS F F' 3 x) = algebraMap F F' (J F x) := by
  sorry

end Coordinates

/-! ## Stabilizers, secant planes, the embedding `e` (10.1.2), and fields of definition -/

section Secants

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The stabilizer `Spin(V_F)_w = {g ∈ Spin(V_F) : m_g(w) = w}` of a spinor `w ∈ S_F` (§10). -/
def spinStab (w : S F n) : Subgroup (Spin F n) where
  carrier := {g | m F n (g : C F n) w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel,
      OneMemClass.coe_one, map_one, Module.End.one_apply]

theorem mem_spinStab_iff (w : S F n) (g : Spin F n) :
    g ∈ spinStab F n w ↔ m F n (g : C F n) w = w :=
  Iff.rfl

/-- `P ⊆ S_F` is a plane whose line `ℙ(P)` is secant to the even spinor variety, meeting it exactly
in the two points `[u₁] ≠ [u₂]`, which correspond to transversal maximal isotropic subspaces
`W_i = ker m_{u_i}` (`W₁ ∩ W₂ = 0`) (Lemma 10.1.1). -/
def IsTransversalSecant (P : Submodule F (S F n)) (u₁ u₂ : S F n) : Prop :=
  P = Submodule.span F {u₁, u₂} ∧ LinearIndependent F ![u₁, u₂] ∧
    IsEvenPureSpinor F n u₁ ∧ IsEvenPureSpinor F n u₂ ∧ ann F n u₁ ⊓ ann F n u₂ = ⊥ ∧
    ∀ u ∈ P, IsEvenPureSpinor F n u →
      u ∈ Submodule.span F {u₁} ∨ u ∈ Submodule.span F {u₂}

/-- The image of the embedding (10.1.2) `e : SL(W₁) → SO(V_F)`, acting on `W₂` through the
isomorphism `W₁* ≅ W₂` induced by the pairing (1.2.2) (for transversal maximal isotropic `W₁, W₂`):
the isometries `g` of `V_F` with `g(W₁) ⊆ W₁`, `g(W₂) ⊆ W₂` and `det(g|_{W₁}) = 1`. Indeed an
isometry preserving `W₁` and `W₂` acts on `W₂ ≅ W₁*` by the inverse transpose of its action on
`W₁`. -/
def slImage (W₁ W₂ : Submodule F (V F n)) : Set (V F n ≃ₗ[F] V F n) :=
  {g | (∀ x y, pairing F n (g x) (g y) = pairing F n x y) ∧
    ∃ h₁ : ∀ v ∈ W₁, g v ∈ W₁, (∀ v ∈ W₂, g v ∈ W₂) ∧
      LinearMap.det ((g : V F n →ₗ[F] V F n).restrict h₁) = 1}

end Secants

section BaseChange

variable (F F' : Type*) [Field F] [CharZero F] [Field F'] [CharZero F'] [Algebra F F'] (n : ℕ)

/-- The base change `W_{F'} = W ⊗_F F' ⊆ V_{F'}` of a subspace `W ⊆ V_F`: the `F'`-span of its
image. -/
noncomputable def bcSubV (W : Submodule F (V F n)) : Submodule F' (V F' n) :=
  Submodule.span F' (bcV F F' n '' W)

/-- The base change `P_{F'} = P ⊗_F F' ⊆ S_{F'}` of a subspace `P ⊆ S_F`. -/
noncomputable def bcSubS (P : Submodule F (S F n)) : Submodule F' (S F' n) :=
  Submodule.span F' (bcS F F' n '' P)

/-- A subspace of `V_{F'}` is *defined over `F`* if it is the base change of a subspace of `V_F`. -/
def IsDefinedOverV (W : Submodule F' (V F' n)) : Prop :=
  ∃ W₀ : Submodule F (V F n), W = bcSubV F F' n W₀

/-- A subspace of `S_{F'}` is *defined over `F`* if it is the base change of a subspace of `S_F`. -/
def IsDefinedOverS (P : Submodule F' (S F' n)) : Prop :=
  ∃ P₀ : Submodule F (S F n), P = bcSubS F F' n P₀

/-- A subspace `W ⊆ V_{F'}` is invariant under a subgroup `G ⊆ Spin(V_F)`, acting on `V_{F'}`
through `Spin(V_F) → Spin(V_{F'})` and `ρ`. -/
def IsInvariantUnder (G : Subgroup (Spin F n)) (W : Submodule F' (V F' n)) : Prop :=
  ∀ g ∈ G, ∀ v ∈ W, rho F' n (bcSpin F F' n g) v ∈ W

end BaseChange

end WeilClasses
