module

public import WeilClasses.Spinor.Defs
public import Mathlib.Algebra.Algebra.Rat

/-!
# Igusa, *A classification of spinors up to dimension twelve*, §2 (as used in §2.4 of the paper)

J.-I. Igusa, *A classification of spinors up to dimension twelve*, Amer. J. Math. 92 (1970),
997–1028, §2: for a hyperbolic pair `e_k, e_{k+2n}` (isotropic, `(e_k, e_{k+2n}) = 1`), the
element `s_k(λ) = λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n}` of the even Clifford algebra lies in the spin group,
and its vector action multiplies `e_k` by `λ²`, `e_{k+2n}` by `λ⁻²` and fixes the orthogonal
complement of the pair (the second displayed formula of §2).

The paper uses this in Remark 2.4.3 (TeX lines 1300–1308): the product
`ϖ̃(λ) = ∏_k (λ⁻¹ + (λ - λ⁻¹) e_k e_{k+2n})` over a basis of two complementary maximal isotropic
subspaces is an element of `Spin(V_F)` mapping to `ϖ(λ)` ("apply the second displayed formula in
[Igusa, Sec. 2]"); and in §2.2 for `ℓ̃ᵢ ⊗ ℓ̃ᵢ ≅ detᵢ`. We state the one-factor case over a field `F`
of characteristic `0` (the relation of `C(V_F)` is `v² = Q(v) = ½ (v, v)_V`, i.e. the paper's
(2.1.1)).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- Igusa's element `s(λ) = λ⁻¹ + (λ - λ⁻¹) a b ∈ C(V_F)` for vectors `a, b ∈ V_F` and `λ ∈ F^×`. -/
noncomputable def igusaFactor (a b : V F n) (l : Fˣ) : C F n :=
  algebraMap F (C F n) ((l⁻¹ : Fˣ) : F) +
    ((l : F) - ((l⁻¹ : Fˣ) : F)) • (CliffordAlgebra.ι (Q F n) a * CliffordAlgebra.ι (Q F n) b)

/-- **[Igusa 1970, §2]** (special case used in Remark 2.4.3): for a hyperbolic pair `a, b`
(`(a, a)_V = (b, b)_V = 0`, `(a, b)_V = 1`) and `λ ∈ F^×`, `s(λ) = λ⁻¹ + (λ - λ⁻¹) a b` lies in
`Spin(V_F)`. -/
theorem igusa_sec2_mem (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) : igusaFactor a b l ∈ spinGroup (Q F n) := by
  sorry

/-- **[Igusa 1970, §2, second displayed formula]** (special case used in Remark 2.4.3): the vector
action of `s(λ)` multiplies `a` by `λ²`, `b` by `λ⁻²`, and fixes every vector orthogonal to `a`
and `b`. -/
theorem igusa_sec2_rho (a b : V F n) (ha : pairing F n a a = 0) (hb : pairing F n b b = 0)
    (hab : pairing F n a b = 1) (l : Fˣ) :
    rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ a = ((l : F) ^ 2) • a ∧
      rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ b =
        (((l⁻¹ : Fˣ) : F) ^ 2) • b ∧
      ∀ v : V F n, pairing F n a v = 0 → pairing F n b v = 0 →
        rho F n ⟨igusaFactor a b l, igusa_sec2_mem a b ha hb hab l⟩ v = v := by
  sorry

end WeilClasses
