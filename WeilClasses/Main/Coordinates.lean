module

public import WeilClasses.AbelianVariety.Defs

/-!
# `X × X̂` as an abelian `2n`-fold of the model

`V_F = H¹(X̂, F) ⊕ H¹(X, F) = H¹(X × X̂, F)` has dimension `4n`, so `X × X̂` and its deformations as
abelian varieties of Weil type are abelian `2n`-folds whose `H¹` is `V_ℚ`. The coordinate isomorphism
`coordV : V_F ≃ F^{4n} = H1 F (2n)` sends the basis `basisV` (`f₁, …, f_{2n}, e₁, …, e_{2n}`) to the
standard basis, so that complex structures, classes and endomorphisms of `V` become those of the
model (`WeilClasses.AbVar (2 * n)`).

Also: the class `Θ = e₁ ∧ e₂ + e₃ ∧ e₄ + ⋯ + e_{2n-1} ∧ e_{2n}` of a principal polarization in
symplectic coordinates (`WeilClasses.ThetaStd`), with `Θⁿ/n! = [pt]` for the orientation
`∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1`.
-/

@[expose] public section

namespace WeilClasses

open ExteriorAlgebra in
/-- `a ∧ b ∧ c = c ∧ a ∧ b` in `⋀• M`. -/
private theorem fnd_ι_mul_ι_mul_ι {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b c : M) : ι R a * ι R b * ι R c = ι R c * ι R a * ι R b := by
  have h : ∀ x y : M, ι R x * ι R y = -(ι R y * ι R x) := fun x y =>
    eq_neg_of_add_eq_zero_left (ι_add_mul_swap x y)
  rw [mul_assoc, h b c, mul_neg, ← mul_assoc, h a c, neg_mul, neg_neg]

open ExteriorAlgebra in
/-- Products of two vectors commute in `⋀• M`. -/
private theorem fnd_commute_ι_mul_ι {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b c d : M) : Commute (ι R a * ι R b) (ι R c * ι R d) := by
  show ι R a * ι R b * (ι R c * ι R d) = ι R c * ι R d * (ι R a * ι R b)
  rw [← mul_assoc, fnd_ι_mul_ι_mul_ι, mul_assoc, mul_assoc, ← mul_assoc (ι R a),
    fnd_ι_mul_ι_mul_ι, ← mul_assoc, ← mul_assoc, ← mul_assoc]

open ExteriorAlgebra in
/-- `(a ∧ b)² = 0` in `⋀• M`. -/
private theorem fnd_ι_mul_ι_sq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b : M) : ι R a * ι R b * (ι R a * ι R b) = 0 := by
  rw [← mul_assoc, fnd_ι_mul_ι_mul_ι, ι_sq_zero, zero_mul, zero_mul]

/-- `(x + y)^{m+1} = x^{m+1} + (m+1) x^m y` for commuting `x, y` with `y² = 0`. -/
private theorem fnd_add_pow_of_sq_eq_zero {R : Type*} [Semiring R] {x y : R} (hc : Commute x y)
    (hy : y * y = 0) (m : ℕ) : (x + y) ^ (m + 1) = x ^ (m + 1) + (m + 1) • (x ^ m * y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc,
      mul_assoc (x ^ m) y x, ← hc.eq, mul_assoc (x ^ m) y y, hy, mul_zero, smul_zero, add_zero,
      ← mul_assoc, ← pow_succ, add_assoc, ← pow_succ, ← succ_nsmul']

private theorem fnd_ofFn_eq_map_range {α : Type*} (G : ℕ → α) (m : ℕ) :
    List.ofFn (fun i : Fin m => G i) = (List.range m).map G := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.range_succ, List.map_append, ← ih]
    simp

/-- `e_j` for `j < 2n`, and `0` for `j ≥ 2n`. -/
private noncomputable def fnd_vec (F : Type*) [Field F] (n : ℕ) (j : ℕ) : H1 F n :=
  if h : j < 2 * n then e F n ⟨j, h⟩ else 0

/-- `ωᵢ = e_{2i} ∧ e_{2i+1}` (`0` for `i ≥ n`), so that `Θ = Σ_{i<n} ωᵢ`. -/
private noncomputable def fnd_ω (F : Type*) [Field F] (n : ℕ) (i : ℕ) : S F n :=
  ExteriorAlgebra.ι F (fnd_vec F n (2 * i)) * ExteriorAlgebra.ι F (fnd_vec F n (2 * i + 1))

/-- `e₀ ∧ e₁ ∧ ⋯ ∧ e_{2k-1} = ω₀ ω₁ ⋯ ω_{k-1}`. -/
private noncomputable def fnd_P (F : Type*) [Field F] (n : ℕ) (k : ℕ) : S F n :=
  ((List.range (2 * k)).map fun j => ExteriorAlgebra.ι F (fnd_vec F n j)).prod

private theorem fnd_P_succ (F : Type*) [Field F] (n : ℕ) (k : ℕ) :
    fnd_P F n (k + 1) = fnd_P F n k * fnd_ω F n k := by
  simp only [fnd_P, fnd_ω]
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.range_succ, List.range_succ]
  simp [List.map_append, List.prod_append]

private theorem fnd_Theta_eq (F : Type*) [Field F] (n : ℕ) :
    ThetaStd F n = ∑ i ∈ Finset.range n, fnd_ω F n i := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 2 * (i : ℕ) < 2 * n := by omega
  have h2 : 2 * (i : ℕ) + 1 < 2 * n := by omega
  simp [fnd_ω, fnd_vec, h1, h2]

/-- `[pt] = e₀ ∧ ⋯ ∧ e_{2n-1}` is the product of the basis vectors in order. -/
private theorem fnd_pt_eq (F : Type*) [Field F] (n : ℕ) : pt F n = fnd_P F n n := by
  have hcard : (Finset.univ : Finset (Fin (2 * n))).card = 2 * n := by simp
  have hemb : ⇑((Finset.univ : Finset (Fin (2 * n))).orderEmbOfFin hcard) = id :=
    (Finset.orderEmbOfFin_unique hcard (f := id) (fun x => Finset.mem_univ x) strictMono_id).symm
  rw [pt, basisS, ExteriorAlgebra.basis_apply_ofCard _ hcard]
  simp only [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.val_ofCard]
  rw [hemb, ExteriorAlgebra.ιMulti_apply, fnd_P, ← fnd_ofFn_eq_map_range]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp [fnd_vec, e, i.isLt]

/-- With `Θ_k = ω₀ + ⋯ + ω_{k-1}` (commuting, square-zero): `Θ_k^{k+1} = 0` and
`Θ_k^k = k! ω₀ ⋯ ω_{k-1}`. -/
private theorem fnd_pow (F : Type*) [Field F] (n : ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, fnd_ω F n i) ^ (k + 1) = 0 ∧
      (∑ i ∈ Finset.range k, fnd_ω F n i) ^ k = k.factorial • fnd_P F n k := by
  induction k with
  | zero => simp [fnd_P]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hc : Commute (∑ i ∈ Finset.range k, fnd_ω F n i) (fnd_ω F n k) :=
      Commute.sum_left _ _ _ fun i _ => fnd_commute_ι_mul_ι _ _ _ _
    have hsq : fnd_ω F n k * fnd_ω F n k = 0 := fnd_ι_mul_ι_sq _ _
    rw [Finset.sum_range_succ]
    constructor
    · rw [fnd_add_pow_of_sq_eq_zero hc hsq, pow_succ, h1, zero_mul, zero_mul, smul_zero, add_zero]
    · rw [fnd_add_pow_of_sq_eq_zero hc hsq, h1, h2, zero_add, smul_mul_assoc, smul_smul,
        ← fnd_P_succ, Nat.factorial_succ]

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
/-- `Θⁿ = n! [pt]` for `ThetaStd`: the orientation `∫_X e₁ ∧ ⋯ ∧ e_{2n} = 1` is the one for which `Θ`
has degree `Θⁿ/n! = 1`. -/
theorem ThetaStd_pow : ThetaStd F n ^ n = (n.factorial : F) • pt F n := by
  rw [fnd_Theta_eq, (fnd_pow F n n).2, fnd_pt_eq, Nat.cast_smul_eq_nsmul]

end WeilClasses
