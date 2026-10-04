module

public import WeilClasses.Correspondence.FourierMukai
public import Mathlib.RepresentationTheory.Basic

/-!
# The cohomological action of Orlov's equivalence (paper §1.3, §6.1, §6.3)

Orlov's equivalence `Φ = (id × Ψ_{𝒫⁻¹[n]}) ∘ μ^* : Dᵇ(X × X) → Dᵇ(X × X̂)` (6.1.2) induces the
correspondence isomorphism `φ : S ⊗ S → ⋀•V` (6.1.3) on cohomology. **In the model, `φ` is defined
as the composite of the cohomological transforms**, `φ := (id ⊗ ψ_{𝒫⁻¹[n]}) ∘ μ^*` (`phiOrlov`);
that this is the Chern character of Orlov's kernel acting by correspondence is geometric
(Grothendieck–Riemann–Roch with trivial Todd classes) and is not stated.

* `phiOrlov = φ` (6.1.3): `H*(X × X) = S ⊗ S → H*(X × X̂) = ⋀•V`;
* `nuOrlov = ν = (ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^* : H*(X × X) → H*(X̂ × X)` (§6.3);
* `phiPrime = φ ∘ (id ⊗ τ)` (Prop. 1.3.1, (1.3.1)), with explicit inverses `phiOrlovInv`,
  `phiPrimeInv` (`φ⁻¹ = (μ^*)⁻¹ ∘ (id ⊗ φ_𝒫)`, since `φ_𝒫 = ψ_{𝒫⁻¹[n]}⁻¹`);
* `rhoPrime g = ρ'_g = φ' (m_g ⊗ m_g) φ'⁻¹ = φ (m_g ⊗ m†_g) φ⁻¹` (6.1.4) and the explicit
  `rhoPrimeFormula g = exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g` (the right side of (6.1.10), and the
  intro's definition of `ρ'`);
* the representations `ρ` (6.1.6, `rhoRep`) and `ρ'` (6.1.7, `rhoPrimeRep`) of `Spin(V)` on `⋀•V`;
* `phiTildeIntro = exp(-c₁(𝒫)/2) ∪ φ ∘ (id ⊗ τ)` (1.3.2) (`φ̃` of the introduction, not to be
  confused with Chevalley's `φ̃` (2.3.2), `varphiTilde`).

Helpers (prefix `s61_`, used here and in `WeilClasses.Orlov.Sec6_3`, `Sec6_1`): exterior bases as
ordered products (`s61_basis_eq_prod`), the product of basis vectors `e_K ∧ e_L = ε_{K,L} e_{K ∪ L}`
with `ε_{K,L} = (-1)^{#inversions}` (`s61_basis_mul_basis`, `s61_epsSign_eq`), the expansion
`exp(t c₁(𝒫)) = Σ_K t^{|K|} (-1)^{|K|(|K|-1)/2} π_X^*e_K ∪ π_X̂^*f_K` (`s61_exp_smul_c1P`), and the
transforms `ψ_{𝒫⁻¹[n]}`, `ψ_{𝒫⁻¹}`, `φ_𝒫` on basis vectors (`s61_psiPinvShift_basisS`, ...).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra TensorProduct

/-! ## Helpers (prover P10): exterior bases, the expansion of `exp(t c₁(𝒫))`, and the transforms
`φ_𝒫`, `ψ_{𝒫⁻¹[n]}` on basis vectors -/

section S61Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]
  (b : Module.Basis ι R M)

theorem s61_basis_eq_prod (s : Finset ι) :
    b.ExteriorAlgebra s = ((s.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (b i)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Finset.orderEmbOfFin_apply, Set.powersetCard.ofCard]

theorem s61_basis_insert_min (a : ι) (s : Finset ι) (h : ∀ x ∈ s, a < x) :
    b.ExteriorAlgebra (insert a s) = ExteriorAlgebra.ι R (b a) * b.ExteriorAlgebra s := by
  have ha : a ∉ s := fun ha => lt_irrefl a (h a ha)
  rw [s61_basis_eq_prod, s61_basis_eq_prod, Finset.sort_insert _ (fun x hx => (h x hx).le) ha]
  simp

theorem s61_basis_empty : b.ExteriorAlgebra ∅ = 1 := by
  rw [s61_basis_eq_prod]; simp

/-- Inserting a basis vector: `ι(b i) ∧ b_s = ± b_{s ∪ {i}}`, the sign counting the elements of `s`
below `i`. -/
theorem s61_ι_mul_basis (i : ι) (s : Finset ι) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0 else (-1 : R) ^ (s.filter (· < i)).card • b.ExteriorAlgebra (insert i s) := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    simp only [Finset.notMem_empty, ite_false, Finset.filter_empty, Finset.card_empty, pow_zero,
      one_smul]
    rw [s61_basis_insert_min b i ∅ (by simp), s61_basis_empty]
  | insert a s ha ih =>
    rw [s61_basis_insert_min b a s ha]
    rcases lt_trichotomy i a with hia | rfl | hai
    · have hi : i ∉ insert a s := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hia.ne, fun hs => lt_asymm hia (ha i hs)⟩
      have hf : (insert a s).filter (· < i) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hx) hxi
        · exact lt_asymm hxi hia
        · exact lt_asymm hxi (hia.trans (ha x hx))
      rw [ite_eq_right hi, hf, Finset.card_empty, pow_zero, one_smul,
        s61_basis_insert_min b i (insert a s), s61_basis_insert_min b a s ha]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hia
      · exact hia.trans (ha x hx)
    · rw [ite_eq_left (Finset.mem_insert_self _ _), ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    · have hswap : ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b a) =
          -(ExteriorAlgebra.ι R (b a) * ExteriorAlgebra.ι R (b i)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      rw [← mul_assoc, hswap, neg_mul, mul_assoc, ih]
      by_cases his : i ∈ s
      · rw [ite_eq_left his, ite_eq_left (Finset.mem_insert_of_mem his), mul_zero, neg_zero]
      · have hi : i ∉ insert a s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hai.ne', his⟩
        rw [ite_eq_right his, ite_eq_right hi, mul_smul_comm,
          ← s61_basis_insert_min b a (insert i s)]
        · have hf : (insert a s).filter (· < i) = insert a (s.filter (· < i)) := by
            rw [Finset.filter_insert, ite_eq_left hai]
          have ha' : a ∉ s.filter (· < i) := fun h => lt_irrefl a (ha a (Finset.mem_filter.mp h).1)
          rw [hf, Finset.card_insert_of_notMem ha', Finset.insert_comm, pow_succ, mul_neg_one,
            neg_smul]
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hai
          · exact ha x hx

/-- The number of inversions `#{(x, y) ∈ s × t : y < x}` of the concatenation of `s` and `t`
(both increasing). -/
def s61_inv (s t : Finset ι) : ℕ := ∑ x ∈ s, (t.filter (· < x)).card

theorem s61_inv_empty_left (t : Finset ι) : s61_inv (∅ : Finset ι) t = 0 := by
  simp [s61_inv]

theorem s61_inv_insert_left {a : ι} {s : Finset ι} (ha : a ∉ s) (t : Finset ι) :
    s61_inv (insert a s) t = (t.filter (· < a)).card + s61_inv s t := by
  classical
  rw [s61_inv, Finset.sum_insert ha, s61_inv]

/-- The product of two exterior basis vectors: `b_s ∧ b_t = ε_{s,t} b_{s ∪ t}` with
`ε_{s,t} = (-1)^{inv(s,t)}` if `s, t` are disjoint, `0` otherwise. -/
theorem s61_basis_mul_basis (s t : Finset ι) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      if Disjoint s t then (-1 : R) ^ s61_inv s t • b.ExteriorAlgebra (s ∪ t) else 0 := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    simp [s61_basis_empty, s61_inv_empty_left]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [s61_basis_insert_min b a s ha, mul_assoc, ih]
    by_cases hst : Disjoint s t
    · rw [ite_eq_left hst, mul_smul_comm, s61_ι_mul_basis]
      by_cases hat : a ∈ t
      · have : ¬Disjoint (insert a s) t := by
          rw [Finset.disjoint_left]; push Not; exact ⟨a, Finset.mem_insert_self _ _, hat⟩
        rw [ite_eq_left (Finset.mem_union_right _ hat), ite_eq_right this, smul_zero]
      · have hd : Disjoint (insert a s) t := by
          rw [Finset.disjoint_insert_left]; exact ⟨hat, hst⟩
        have hnot : a ∉ s ∪ t := by simp [has, hat]
        have hf : (s ∪ t).filter (· < a) = t.filter (· < a) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hx | hx, hxa⟩
            · exact absurd hxa (lt_asymm (ha x hx))
            · exact ⟨hx, hxa⟩
          · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
        rw [ite_eq_right hnot, ite_eq_left hd, hf, smul_smul, ← pow_add,
          s61_inv_insert_left has, Finset.insert_union, add_comm]
    · have : ¬Disjoint (insert a s) t := by
        rw [Finset.disjoint_insert_left]; exact fun h => hst h.2
      rw [ite_eq_right hst, ite_eq_right this, mul_zero]

theorem s61_basis_singleton (a : ι) : b.ExteriorAlgebra {a} = ExteriorAlgebra.ι R (b a) := by
  rw [show ({a} : Finset ι) = insert a ∅ from rfl, s61_basis_insert_min b a ∅ (by simp),
    s61_basis_empty, mul_one]

theorem s61_inv_singleton_right_of_lt {a : ι} {s : Finset ι} (h : ∀ x ∈ s, x < a) :
    s61_inv s {a} = 0 := by
  classical
  refine Finset.sum_eq_zero fun x hx => ?_
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_singleton]
  rintro y rfl
  exact lt_asymm (h x hx)

theorem s61_basis_insert_max (a : ι) (s : Finset ι) (h : ∀ x ∈ s, x < a) :
    b.ExteriorAlgebra (insert a s) = b.ExteriorAlgebra s * ExteriorAlgebra.ι R (b a) := by
  classical
  have ha : a ∉ s := fun ha => lt_irrefl a (h a ha)
  rw [← s61_basis_singleton, s61_basis_mul_basis, ite_eq_left (Finset.disjoint_singleton_right.mpr ha),
    s61_inv_singleton_right_of_lt h, pow_zero, one_smul, Finset.union_comm]
  rfl

theorem s61_inv_insert_right {a : ι} {t : Finset ι} (ha : a ∉ t) (s : Finset ι) :
    s61_inv s (insert a t) = s61_inv s t + (s.filter (a < ·)).card := by
  classical
  rw [s61_inv, s61_inv, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.mp h').1)]
  · rw [add_zero]

theorem s61_card_filter_lt_add_gt {a : ι} {t : Finset ι} (ha : a ∉ t) :
    (t.filter (· < a)).card + (t.filter (a < ·)).card = t.card := by
  classical
  have h : t.filter (a < ·) = t.filter (fun y => ¬ y < a) := by
    ext y
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hy, h⟩; exact ⟨hy, h.le⟩
    · rintro ⟨hy, h⟩; exact ⟨hy, lt_of_le_of_ne h (fun h' => ha (h' ▸ hy))⟩
  rw [h]
  exact Finset.card_filter_add_card_filter_not _

theorem s61_inv_add_inv {s t : Finset ι} (h : Disjoint s t) :
    s61_inv s t + s61_inv t s = s.card * t.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s61_inv]
  | @insert a s has ih =>
    rw [Finset.disjoint_insert_left] at h
    rw [s61_inv_insert_left has, Finset.card_insert_of_notMem has,
      s61_inv_insert_right has, add_mul, one_mul, ← ih h.2, ← s61_card_filter_lt_add_gt h.1]
    ring

/-- Graded commutativity for exterior basis vectors. -/
theorem s61_basis_mul_comm (s t : Finset ι) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (-1 : R) ^ (s.card * t.card) • (b.ExteriorAlgebra t * b.ExteriorAlgebra s) := by
  rw [s61_basis_mul_basis, s61_basis_mul_basis]
  by_cases h : Disjoint s t
  · rw [ite_eq_left h, ite_eq_left h.symm, smul_smul, ← pow_add, Finset.union_comm,
      ← s61_inv_add_inv h]
    congr 1
    rw [pow_add, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm), smul_zero]

theorem s61_basis_mem (s : Finset ι) : b.ExteriorAlgebra s ∈ ⋀[R]^s.card M := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl]
  exact ExteriorAlgebra.ιMulti_range R s.card ⟨_, rfl⟩

theorem s61_map_basis {N κ : Type*} [AddCommGroup N] [Module R N] [LinearOrder κ]
    (b' : Module.Basis κ R N) (g : M →ₗ[R] N) (φ : ι ↪o κ) (h : ∀ i, g (b i) = b' (φ i))
    (s : Finset ι) :
    ExteriorAlgebra.map g (b.ExteriorAlgebra s) = b'.ExteriorAlgebra (s.map φ.toEmbedding) := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp [s61_basis_empty]
  | insert a s ha ih =>
    rw [s61_basis_insert_min b a s ha, map_mul, ExteriorAlgebra.map_apply_ι, ih, h,
      Finset.map_insert, s61_basis_insert_min b' (φ.toEmbedding a)]
    · rfl
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact φ.strictMono (ha x hx)

end S61Basis

section S61Model

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

omit [CharZero F] in
theorem s61_basisFun_apply (i : Fin (2 * n)) : Pi.basisFun F (Fin (2 * n)) i = e F n i := by
  rw [Pi.basisFun_apply]; rfl

omit [CharZero F] in
theorem s61_dualBasis_apply (i : Fin (2 * n)) :
    (Pi.basisFun F (Fin (2 * n))).dualBasis i = f F n i := by
  ext x
  simp [f]

omit [CharZero F] in
theorem s61_basisV_castAdd (i : Fin (2 * n)) :
    basisV F n (Fin.castAdd (2 * n) i) = ((f F n i, 0) : V F n) := by
  rw [basisV, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, s61_dualBasis_apply]
  rfl

omit [CharZero F] in
theorem s61_basisV_natAdd (i : Fin (2 * n)) :
    basisV F n (Fin.natAdd (2 * n) i) = ((0, e F n i) : V F n) := by
  rw [basisV, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, s61_basisFun_apply]
  rfl

omit [CharZero F] in
/-- `π_X^* e_K` is the exterior basis vector of `⋀•V` indexed by `K` shifted into the `H¹(X)` block. -/
theorem s61_pullX_basisS (K : Finset (Fin (2 * n))) :
    pullX F n (basisS F n K) =
      basisExt F n (K.map (Fin.natAddOrderEmb (2 * n)).toEmbedding) := by
  refine s61_map_basis _ (basisV F n) _ _ (fun i => ?_) K
  rw [s61_basisFun_apply]
  exact (s61_basisV_natAdd F n i).symm

omit [CharZero F] in
/-- `π_X̂^* f_L` is the exterior basis vector of `⋀•V` indexed by `L` (the `H¹(X̂)` block). -/
theorem s61_pullXHat_basisSHat (L : Finset (Fin (2 * n))) :
    pullXHat F n (basisSHat F n L) =
      basisExt F n (L.map (Fin.castAddOrderEmb (2 * n)).toEmbedding) := by
  refine s61_map_basis _ (basisV F n) _ _ (fun i => ?_) L
  rw [s61_dualBasis_apply]
  exact (s61_basisV_castAdd F n i).symm

omit [CharZero F] in
/-- `e_K ∧ e_L = ε_{K,L} e_{K ∪ L}`. -/
theorem s61_epsSign_eq (K L : Finset (Fin (2 * n))) :
    epsSign F n K L = if Disjoint K L then (-1 : F) ^ s61_inv K L else 0 := by
  rw [epsSign, basisS, s61_basis_mul_basis]
  split_ifs <;> simp

omit [CharZero F] in
theorem s61_basisS_mul (K L : Finset (Fin (2 * n))) :
    basisS F n K * basisS F n L = epsSign F n K L • basisS F n (K ∪ L) := by
  rw [s61_epsSign_eq, basisS, s61_basis_mul_basis]
  split_ifs <;> simp

end S61Model

section S61Central

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Products of two vectors are central in the exterior algebra. -/
theorem s61_commute_ι_mul_ι (u v : M) (x : ExteriorAlgebra R M) :
    Commute (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commute_algebraMap_right r _
  | ι w =>
    have h1 : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
        -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h2 : ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w =
        -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    show _ * _ = _ * _
    rw [mul_assoc, h1, mul_neg, ← mul_assoc, h2, neg_mul, neg_neg, mul_assoc]
  | mul x y hx hy => exact hx.mul_right hy
  | add x y hx hy => exact hx.add_right hy

theorem s61_ι_mul_ι_mul_self (u v : M) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  have h1 : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u =
      -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R v), h1, neg_mul, mul_neg, ← mul_assoc,
    ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul, neg_zero]

end S61Central

section S61Exp

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_tri_succ (k : ℕ) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  have h1 := Finset.sum_range_id (k + 1)
  have h2 := Finset.sum_range_id k
  rw [Finset.sum_range_succ, h2, Nat.add_sub_cancel] at h1
  exact h1.symm

/-- The summand `π_X^*eᵢ ∪ π_X̂^*fᵢ` of `c₁(𝒫)`. -/
noncomputable def s61_a (i : Fin (2 * n)) : ExtV F n :=
  pullX F n (ExteriorAlgebra.ι F (e F n i)) * pullXHat F n (ExteriorAlgebra.ι F (f F n i))

omit [CharZero F] in
theorem s61_a_eq (i : Fin (2 * n)) :
    s61_a F n i = ExteriorAlgebra.ι F ((0, e F n i) : V F n) *
      ExteriorAlgebra.ι F ((f F n i, 0) : V F n) := by
  simp [s61_a, pullX, pullXHat]

omit [CharZero F] in
theorem s61_c1P_eq : c1P F n = ∑ i, s61_a F n i := rfl

omit [CharZero F] in
theorem s61_commute_a (i : Fin (2 * n)) (x : ExtV F n) : Commute (s61_a F n i) x := by
  rw [s61_a_eq]; exact s61_commute_ι_mul_ι _ _ x

omit [CharZero F] in
theorem s61_a_mul_self (i : Fin (2 * n)) : s61_a F n i * s61_a F n i = 0 := by
  rw [s61_a_eq]; exact s61_ι_mul_ι_mul_self _ _

/-- `X_K = π_X^*e_K ∪ π_X̂^*f_K`. -/
noncomputable def s61_X (K : Finset (Fin (2 * n))) : ExtV F n :=
  pullX F n (basisS F n K) * pullXHat F n (basisSHat F n K)

omit [CharZero F] in
theorem s61_X_insert_max (m : Fin (2 * n)) (K : Finset (Fin (2 * n))) (h : ∀ x ∈ K, x < m) :
    s61_X F n (insert m K) = (-1 : F) ^ K.card • (s61_X F n K * s61_a F n m) := by
  have hS : basisS F n (insert m K) = basisS F n K * ExteriorAlgebra.ι F (e F n m) := by
    rw [basisS, s61_basis_insert_max _ m K h, s61_basisFun_apply]
  have hSH : basisSHat F n (insert m K) = basisSHat F n K * ExteriorAlgebra.ι F (f F n m) := by
    rw [basisSHat, s61_basis_insert_max _ m K h, s61_dualBasis_apply]
  have hc : pullX F n (ExteriorAlgebra.ι F (e F n m)) * pullXHat F n (basisSHat F n K) =
      (-1 : F) ^ K.card • (pullXHat F n (basisSHat F n K) * pullX F n (ExteriorAlgebra.ι F (e F n m))) := by
    rw [← s61_basisFun_apply, ← s61_basis_singleton, ← basisS, s61_pullX_basisS,
      s61_pullXHat_basisSHat, basisExt, s61_basis_mul_comm]
    simp
  rw [s61_X, hS, hSH, map_mul, map_mul, s61_X, s61_a]
  rw [mul_assoc, ← mul_assoc (pullX F n _) (pullXHat F n _), hc]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

omit [CharZero F] in
theorem s61_isNilpotent_smul_sum (t : F) (T : Finset (Fin (2 * n))) :
    IsNilpotent (t • ∑ i ∈ T, s61_a F n i) := by
  refine IsNilpotent.smul (Commute.isNilpotent_sum (fun i _ => ⟨2, ?_⟩)
    (fun i j _ _ => s61_commute_a F n i _)) t
  rw [pow_two, s61_a_mul_self]

/-- **The expansion of `exp(t c₁(𝒫))`**: `exp(t Σ_{i ∈ T} π_X^*eᵢ ∪ π_X̂^*fᵢ) =
Σ_{K ⊆ T} t^{|K|} (-1)^{|K|(|K|-1)/2} π_X^*e_K ∪ π_X̂^*f_K`. -/
theorem s61_exp_smul_sum (t : F) (T : Finset (Fin (2 * n))) :
    IsNilpotent.exp (t • ∑ i ∈ T, s61_a F n i) =
      ∑ K ∈ T.powerset, (t ^ K.card * (-1 : F) ^ (K.card * (K.card - 1) / 2)) • s61_X F n K := by
  classical
  induction T using Finset.induction_on_max with
  | empty =>
    simp [s61_X, basisS, basisSHat, s61_basis_empty, IsNilpotent.exp_zero]
  | insert m T hm ih =>
    have hmT : m ∉ T := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmT, smul_add, add_comm,
      IsNilpotent.exp_add_of_commute ((s61_commute_a F n m _).symm.smul_left t |>.smul_right t)
        (s61_isNilpotent_smul_sum F n t T) (IsNilpotent.smul ⟨2, by rw [pow_two, s61_a_mul_self]⟩ t),
      ih, IsNilpotent.exp_eq_sum (k := 2) (by rw [pow_two, smul_mul_smul_comm, s61_a_mul_self,
        smul_zero]), Finset.sum_powerset_insert hmT]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.cast_one,
      inv_one, pow_zero, one_smul, zero_add, Nat.factorial_one, pow_one, mul_add, mul_one,
      Finset.sum_mul, add_right_inj]
    refine Finset.sum_congr rfl fun K hK => ?_
    have hKm : ∀ x ∈ K, x < m := fun x hx => hm x (Finset.mem_powerset.mp hK hx)
    have hmK : m ∉ K := fun h => lt_irrefl m (hKm m h)
    rw [s61_X_insert_max F n m K hKm, Finset.card_insert_of_notMem hmK, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, Nat.add_sub_cancel, s61_tri_succ, pow_add,
      pow_succ]
    congr 1
    have h2 : ((-1 : F) ^ K.card) * (-1) ^ K.card = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (-(t ^ K.card * t * (-1) ^ (K.card * (K.card - 1) / 2))) * h2

theorem s61_tri_add (a b : ℕ) :
    (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 := s61_tri_succ (a + b)
    have h2 := s61_tri_succ b
    rw [show a + (b + 1) = a + b + 1 by ring, Nat.add_sub_cancel, h1, ih,
      Nat.add_sub_cancel, h2, Nat.mul_succ]
    ring

theorem s61_tri_two_mul (n : ℕ) : 2 * n * (2 * n - 1) / 2 + n = 2 * (n * n) := by
  rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  cases n with
  | zero => simp
  | succ k =>
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring

theorem s61_neg_one_pow_congr {R : Type*} [Ring R] {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : R) ^ a = (-1 : R) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

end S61Exp

section S61Corr

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {N : ℕ}
  (b : Module.Basis (Fin N) F M)

theorem s61_coord_univ_basis_mul (L K : Finset (Fin N)) :
    (b.ExteriorAlgebra).coord Finset.univ (b.ExteriorAlgebra L * b.ExteriorAlgebra K) =
      if K = Lᶜ then (-1 : F) ^ s61_inv L Lᶜ else 0 := by
  classical
  rw [s61_basis_mul_basis]
  by_cases hK : K = Lᶜ
  · subst hK
    rw [ite_eq_left disjoint_compl_right, ite_eq_left rfl, map_smul, Finset.union_compl]
    simp
  · rw [ite_eq_right hK]
    split_ifs with hd
    · have hne : L ∪ K ≠ Finset.univ := by
        intro hu
        apply hK
        ext x
        simp only [Finset.mem_compl]
        constructor
        · exact fun hx hL => Finset.disjoint_left.mp hd hL hx
        · intro hx
          have : x ∈ L ∪ K := hu ▸ Finset.mem_univ x
          exact (Finset.mem_union.mp this).resolve_left hx
      rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right hne, smul_zero]
    · simp

theorem s61_corr_basis {B : Type*} [AddCommGroup B] [Module F B]
    (c : Finset (Fin N) → F) (v : Finset (Fin N) → B) (L : Finset (Fin N)) :
    corr ((b.ExteriorAlgebra).coord Finset.univ)
        (∑ K, c K • (b.ExteriorAlgebra K ⊗ₜ[F] v K)) (b.ExteriorAlgebra L) =
      (c Lᶜ * (-1 : F) ^ s61_inv L Lᶜ) • v Lᶜ := by
  classical
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    corr_tmul, s61_coord_univ_basis_mul, smul_smul]
  rw [Finset.sum_eq_single Lᶜ]
  · rw [ite_eq_left rfl]
  · intro K _ hK
    rw [ite_eq_right hK, mul_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end S61Corr

section S61Transforms

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

theorem s61_exp_smul_c1P (t : F) :
    IsNilpotent.exp (t • c1P F n) =
      ∑ K, (t ^ K.card * (-1 : F) ^ (K.card * (K.card - 1) / 2)) • s61_X F n K := by
  rw [s61_c1P_eq, s61_exp_smul_sum, Finset.powerset_univ]

theorem s61_kunnethXHat_symm_X_sum (c : Finset (Fin (2 * n)) → F) :
    (kunnethXHat F n).symm (∑ K, c K • s61_X F n K) =
      ∑ K, c K • (basisS F n K ⊗ₜ[F] basisSHat F n K) := by
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_sum, map_smul, kunnethXHat_tmul, s61_X]

omit [CharZero F] in
/-- `π_X^*e_K ∪ π_X̂^*f_K = (-1)^{|K|} π_X̂^*f_K ∪ π_X^*e_K`. -/
theorem s61_X_eq_swap (K : Finset (Fin (2 * n))) :
    s61_X F n K = (-1 : F) ^ (K.card * K.card) •
      (pullXHat F n (basisSHat F n K) * pullX F n (basisS F n K)) := by
  rw [s61_X, s61_pullX_basisS, s61_pullXHat_basisSHat, basisExt, s61_basis_mul_comm]
  simp

omit [CharZero F] in
theorem s61_kunnethHatX_symm_X_sum (c : Finset (Fin (2 * n)) → F) :
    (kunnethHatX F n).symm (∑ K, c K • s61_X F n K) =
      ∑ K, (c K * (-1 : F) ^ (K.card * K.card)) • (basisSHat F n K ⊗ₜ[F] basisS F n K) := by
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_sum, map_smul, kunnethHatX_tmul, s61_X_eq_swap, smul_smul]

/-- `ψ_{𝒫⁻¹[n]}(e_L) = (-1)ⁿ (-1)^{m} (-1)^{m(m-1)/2} ε_{L,L^c} f_{L^c}`, `m = |L^c|`. -/
theorem s61_psiPinvShift_basisS (L : Finset (Fin (2 * n))) :
    psiPinvShift F n (basisS F n L) =
      ((-1 : F) ^ n * ((-1 : F) ^ Lᶜ.card * (-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2)) *
        (-1 : F) ^ s61_inv L Lᶜ) • basisSHat F n Lᶜ := by
  rw [psiPinvShift, chPinvShift, ← neg_one_smul F (c1P F n), s61_exp_smul_c1P, Finset.smul_sum]
  simp only [smul_smul]
  rw [s61_kunnethXHat_symm_X_sum, integral, basisS]
  rw [s61_corr_basis]

/-- `ψ_{𝒫⁻¹}(e_L) = (-1)^{m} (-1)^{m(m-1)/2} ε_{L,L^c} f_{L^c}`, `m = |L^c|`. -/
theorem s61_psiPinv_basisS (L : Finset (Fin (2 * n))) :
    psiPinv F n (basisS F n L) =
      (((-1 : F) ^ Lᶜ.card * (-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2)) *
        (-1 : F) ^ s61_inv L Lᶜ) • basisSHat F n Lᶜ := by
  rw [psiPinv, ← neg_one_smul F (c1P F n), s61_exp_smul_c1P, s61_kunnethXHat_symm_X_sum,
    integral, basisS, s61_corr_basis]

/-- `φ_𝒫(e_L) = (-1)^{m(m-1)/2} ε_{L,L^c} f_{L^c}` (`φ_𝒫 : H*(X) → H*(X̂)`), `m = |L^c|`. -/
theorem s61_phiPX_basisS (L : Finset (Fin (2 * n))) :
    phiPX F n (basisS F n L) =
      ((-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2) * (-1 : F) ^ s61_inv L Lᶜ) •
        basisSHat F n Lᶜ := by
  rw [phiPX, chP, ← one_smul F (c1P F n), s61_exp_smul_c1P, s61_kunnethXHat_symm_X_sum,
    integral, basisS, s61_corr_basis]
  simp

/-- `φ_𝒫(f_L) = (-1)^{m(m-1)/2} (-1)^{m·m} ε_{L,L^c} e_{L^c}` (`φ_𝒫 : H*(X̂) → H*(X)`). -/
theorem s61_phiP_basisSHat (L : Finset (Fin (2 * n))) :
    phiP F n (basisSHat F n L) =
      (((-1 : F) ^ (Lᶜ.card * (Lᶜ.card - 1) / 2) * (-1 : F) ^ (Lᶜ.card * Lᶜ.card)) *
        (-1 : F) ^ s61_inv L Lᶜ) • basisS F n Lᶜ := by
  rw [phiP, chP, ← one_smul F (c1P F n), s61_exp_smul_c1P, s61_kunnethHatX_symm_X_sum,
    integralHat, basisSHat, s61_corr_basis]
  simp

theorem s61_mul_self_mod_two (k : ℕ) : k * k % 2 = k % 2 := by
  rw [Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h]

theorem s61_card_add_card_compl (L : Finset (Fin (2 * n))) : L.card + Lᶜ.card = 2 * n := by
  rw [Finset.card_compl, Fintype.card_fin]
  have := L.card_le_univ
  rw [Fintype.card_fin] at this
  omega

theorem s61_phiP_comp_psiPinvShift : phiP F n ∘ₗ psiPinvShift F n = LinearMap.id := by
  refine (basisS F n).ext fun L => ?_
  rw [LinearMap.comp_apply, s61_psiPinvShift_basisS, map_smul, s61_phiP_basisSHat, compl_compl,
    smul_smul, LinearMap.id_apply]
  convert one_smul F (basisS F n L) using 2
  have h1 := s61_inv_add_inv (disjoint_compl_right : Disjoint L Lᶜ)
  have h2 := s61_card_add_card_compl n L
  have h3 := s61_tri_add L.card Lᶜ.card
  have h4 := s61_tri_two_mul n
  have h5 := s61_mul_self_mod_two L.card
  rw [h2] at h3
  simp only [← pow_add]
  rw [s61_neg_one_pow_congr (b := 0) (by omega), pow_zero]

theorem s61_psiPinvShift_comp_phiP : psiPinvShift F n ∘ₗ phiP F n = LinearMap.id := by
  refine (basisSHat F n).ext fun L => ?_
  rw [LinearMap.comp_apply, s61_phiP_basisSHat, map_smul, s61_psiPinvShift_basisS, compl_compl,
    smul_smul, LinearMap.id_apply]
  convert one_smul F (basisSHat F n L) using 2
  have h1 := s61_inv_add_inv (disjoint_compl_right : Disjoint L Lᶜ)
  have h2 := s61_card_add_card_compl n L
  have h3 := s61_tri_add L.card Lᶜ.card
  have h4 := s61_tri_two_mul n
  have h5 := s61_mul_self_mod_two Lᶜ.card
  rw [h2] at h3
  simp only [← pow_add]
  rw [s61_neg_one_pow_congr (b := 0) (by omega), pow_zero]

end S61Transforms

section Defs

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `ν = (ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^* : H*(X × X) → H*(X̂ × X)` (§6.3), the cohomological action of
`(Ψ_{𝒫⁻¹[n]} ⊗ 1) ∘ μ^*`; `H*(X̂ × X) = ⋀•V` by `a ⊗ b ↦ π_X̂^*a ∪ π_X^*b`. -/
noncomputable def nuOrlov : S F n ⊗[F] S F n →ₗ[F] ExtV F n :=
  (kunnethHatX F n).toLinearMap ∘ₗ TensorProduct.map (psiPinvShift F n) LinearMap.id ∘ₗ
    muStar F n

/-- `φ' = φ ∘ (id ⊗ τ)`. -/
noncomputable def phiPrime : S F n ⊗[F] S F n →ₗ[F] ExtV F n := phiOrlov F n ∘ₗ tauTensor F n

/-- The inverse `φ⁻¹ = (μ^*)⁻¹ ∘ (id ⊗ φ_𝒫)` of `φ` (`φ_𝒫 = ψ_{𝒫⁻¹[n]}⁻¹`, footnote in §6.3);
see `phiOrlov_comp_phiOrlovInv`. -/
noncomputable def phiOrlovInv : ExtV F n →ₗ[F] S F n ⊗[F] S F n :=
  muStarInv F n ∘ₗ TensorProduct.map LinearMap.id (phiP F n) ∘ₗ (kunnethXHat F n).symm.toLinearMap

/-- The inverse `φ'⁻¹ = (id ⊗ τ) ∘ φ⁻¹` of `φ'`. -/
noncomputable def phiPrimeInv : ExtV F n →ₗ[F] S F n ⊗[F] S F n :=
  tauTensor F n ∘ₗ phiOrlovInv F n

/-! ## Invertibility -/

/-- `Ψ_{𝒫⁻¹[n]}` is the inverse of `Φ_𝒫` (footnote in §6.3): `φ_𝒫 ∘ ψ_{𝒫⁻¹[n]} = id`. -/
theorem phiP_comp_psiPinvShift : phiP F n ∘ₗ psiPinvShift F n = LinearMap.id :=
  s61_phiP_comp_psiPinvShift F n

/-- `ψ_{𝒫⁻¹[n]} ∘ φ_𝒫 = id`. -/
theorem psiPinvShift_comp_phiP : psiPinvShift F n ∘ₗ phiP F n = LinearMap.id :=
  s61_psiPinvShift_comp_phiP F n

theorem phiOrlov_comp_phiOrlovInv : phiOrlov F n ∘ₗ phiOrlovInv F n = LinearMap.id := by
  have h1 : muStar F n ∘ₗ muStarInv F n = LinearMap.id := muStar_comp_muStarInv F n
  have h2 : TensorProduct.map (LinearMap.id : S F n →ₗ[F] S F n) (psiPinvShift F n) ∘ₗ
      TensorProduct.map LinearMap.id (phiP F n) = LinearMap.id := by
    rw [← TensorProduct.map_comp, LinearMap.id_comp, psiPinvShift_comp_phiP, TensorProduct.map_id]
  refine LinearMap.ext fun x => ?_
  simp only [phiOrlov, phiOrlovInv, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← LinearMap.comp_apply (muStar F n) (muStarInv F n), h1, LinearMap.id_apply,
    ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _), h2, LinearMap.id_apply,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]

theorem phiOrlovInv_comp_phiOrlov : phiOrlovInv F n ∘ₗ phiOrlov F n = LinearMap.id := by
  have h1 : muStarInv F n ∘ₗ muStar F n = LinearMap.id := muStarInv_comp_muStar F n
  have h2 : TensorProduct.map (LinearMap.id : S F n →ₗ[F] S F n) (phiP F n) ∘ₗ
      TensorProduct.map LinearMap.id (psiPinvShift F n) = LinearMap.id := by
    rw [← TensorProduct.map_comp, LinearMap.id_comp, phiP_comp_psiPinvShift, TensorProduct.map_id]
  refine LinearMap.ext fun x => ?_
  simp only [phiOrlov, phiOrlovInv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _), h2,
    LinearMap.id_apply, ← LinearMap.comp_apply (muStarInv F n) (muStar F n), h1, LinearMap.id_apply]

/-- `φ'` is invertible, with inverse `phiPrimeInv` (needed for (6.1.4)). -/
theorem phiPrime_comp_phiPrimeInv : phiPrime F n ∘ₗ phiPrimeInv F n = LinearMap.id := by
  rw [phiPrime, phiPrimeInv, LinearMap.comp_assoc, ← LinearMap.comp_assoc (phiOrlovInv F n),
    tauTensor_comp_tauTensor, LinearMap.id_comp, phiOrlov_comp_phiOrlovInv]

theorem phiPrimeInv_comp_phiPrime : phiPrimeInv F n ∘ₗ phiPrime F n = LinearMap.id := by
  rw [phiPrime, phiPrimeInv, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (tauTensor F n) (phiOrlov F n), phiOrlovInv_comp_phiOrlov,
    LinearMap.id_comp, tauTensor_comp_tauTensor]

/-! ## The representations `ρ` and `ρ'` -/

/-- **(6.1.4)** (`rho-prime-g`) `ρ'_g = φ' (m_g ⊗ m_g) φ'⁻¹ : ⋀•V → ⋀•V`, `φ' = φ ∘ (id ⊗ τ)`;
equivalently `ρ'_g = φ (m_g ⊗ m†_g) φ⁻¹` as printed (`rhoPrime_eq_phiOrlov_conj`). -/
noncomputable def rhoPrime (g : Spin F n) : Module.End F (ExtV F n) :=
  phiPrime F n ∘ₗ TensorProduct.map (m F n (g : C F n)) (m F n (g : C F n)) ∘ₗ phiPrimeInv F n

/-- The right side of (6.1.10) (and the introduction's definition of `ρ'_g`):
`x ↦ exp(½[c₁(𝒫) - ρ_g(c₁(𝒫))]) ∪ ρ_g(x)`. -/
noncomputable def rhoPrimeFormula (g : Spin F n) : Module.End F (ExtV F n) :=
  LinearMap.mulLeft F (IsNilpotent.exp ((2 : F)⁻¹ • (c1P F n - rhoExt F n g (c1P F n)))) ∘ₗ
    (rhoExt F n g).toLinearMap

/-- **(6.1.6)** (`eq-rho-extended-to-exterior-algebra`) `ρ : Spin(V) → GL(⋀•V)`, acting on `⋀^k V`
by `⋀^k ρ_g`. -/
noncomputable def rhoRep : Representation F (Spin F n) (ExtV F n) where
  toFun g := (rhoExt F n g).toLinearMap
  map_one' := by
    have h : (rho F n 1 : V F n →ₗ[F] V F n) = LinearMap.id := by
      simp [rho]
    simp only [rhoExt, h, ExteriorAlgebra.map_id]
    rfl
  map_mul' g h := by
    have hh : (rho F n (g * h) : V F n →ₗ[F] V F n) =
        (rho F n g : V F n →ₗ[F] V F n) ∘ₗ (rho F n h : V F n →ₗ[F] V F n) := by
      simp [rho]; rfl
    simp only [rhoExt, hh, ← ExteriorAlgebra.map_comp_map]
    rfl

/-- **(6.1.7)** (`eq-rho-prime`) `ρ' : Spin(V) → GL(⋀•V)`, `g ↦ ρ'_g` (6.1.4). -/
noncomputable def rhoPrimeRep : Representation F (Spin F n) (ExtV F n) where
  toFun g := rhoPrime F n g
  map_one' := by
    have h1 : m F n ((1 : Spin F n) : C F n) = LinearMap.id := by
      rw [OneMemClass.coe_one, map_one]; rfl
    show rhoPrime F n 1 = 1
    simp only [rhoPrime, h1, TensorProduct.map_id, LinearMap.id_comp]
    exact phiPrime_comp_phiPrimeInv F n
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    have hinv : ∀ y, phiPrimeInv F n (phiPrime F n y) = y := fun y => by
      rw [← LinearMap.comp_apply (phiPrimeInv F n) (phiPrime F n) y, phiPrimeInv_comp_phiPrime,
        LinearMap.id_apply]
    have hm : m F n ((g * h : Spin F n) : C F n) = m F n (g : C F n) * m F n (h : C F n) := by
      rw [Submonoid.coe_mul, map_mul]
    rw [Module.End.mul_apply]
    simp only [rhoPrime, LinearMap.comp_apply]
    rw [hinv, hm, TensorProduct.map_mul, Module.End.mul_apply]

/-! ## The introduction's `φ̃` (1.3.2) -/

/-- **(1.3.2)** (`eq-tilde-phi`) `φ̃ = exp(-c₁(𝒫)/2) ∪ φ ∘ (id ⊗ τ) : H*(X × X, ℚ) → H*(X × X̂, ℚ)`
(the
introduction's `\tilde{\phi}`; Chevalley's `\tilde{\varphi}` (2.3.2) is `varphiTilde`). -/
noncomputable def phiTildeIntro : S F n ⊗[F] S F n →ₗ[F] ExtV F n :=
  LinearMap.mulLeft F (IsNilpotent.exp (-((2 : F)⁻¹ • c1P F n))) ∘ₗ phiPrime F n

end Defs

end WeilClasses
