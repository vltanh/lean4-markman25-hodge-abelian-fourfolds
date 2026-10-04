module

public import WeilClasses.AbelianVariety.Defs

/-!
# Standard facts about abelian varieties used without citation (proof of Corollary 1.6.1)

The proof of Corollary 1.6.1 reduces the Hodge conjecture for an abelian fourfold to codimension
two and to the simple and non-simple cases. It uses, without citation:

* Poincaré's complete reducibility: a sub-Hodge structure of `H¹(A, ℚ)` has a complementary
  sub-Hodge structure (`AbVar.exists_isCompl_isHodgeSub`), so a non-simple abelian variety is
  isogenous to a product;
* sub-Hodge structures of `H¹(A, ℚ)` have even dimension (`AbVar.even_finrank_of_isHodgeSub`);
* the hard Lefschetz theorem for an ample class `h` on an abelian `g`-fold, in the case
  `h^{g-2} ∪ : H² → H^{2g-2}`, which maps Hodge classes onto Hodge classes
  (`AbVar.hodge_pred_le_map`), so that Hodge classes of degree `2g - 2` are algebraic once those of
  degree `2` are;
* the top degree: `H^{2g}(A, ℚ)` is spanned by `h^g` (`AbVar.top_eq_span_pow`).
-/

@[expose] public section

namespace WeilClasses

namespace AbVar

variable {g : ℕ} (A : AbVar g)

/-- Sub-Hodge structures of `H¹(A, ℚ)` have even dimension (their real span carries the complex
structure `J`). -/
theorem even_finrank_of_isHodgeSub (U : Submodule ℚ (H1 ℚ g)) (hU : A.IsHodgeSub U) :
    Even (Module.finrank ℚ U) := by
  sorry

/-- **Poincaré's complete reducibility** (up to isogeny): every sub-Hodge structure of `H¹(A, ℚ)`
has a complement that is a sub-Hodge structure (the orthogonal complement for a polarization). -/
theorem exists_isCompl_isHodgeSub (U : Submodule ℚ (H1 ℚ g)) (hU : A.IsHodgeSub U) :
    ∃ U' : Submodule ℚ (H1 ℚ g), A.IsHodgeSub U' ∧ IsCompl U U' := by
  sorry

/-- **Hard Lefschetz** for abelian varieties, degree `2` to degree `2g - 2`: for an ample class `h`,
every Hodge class of degree `2g - 2` is `h^{g-2} ∪ β` for a Hodge class `β` of degree `2`
(`2 ≤ g`). -/
theorem hodge_pred_le_map (hg : 2 ≤ g) (h : S ℚ g) (hh : IsAmple g A.J h) :
    A.hodge (g - 1) ≤ (A.hodge 1).map (LinearMap.mulLeft ℚ (h ^ (g - 2))) := by
  sorry

/-- The top degree `H^{2g}(A, ℚ)` is the line spanned by `h^g`, for an ample class `h`. -/
theorem top_eq_span_pow (h : S ℚ g) (hh : IsAmple g A.J h) :
    ⋀[ℚ]^(2 * g) (H1 ℚ g) = Submodule.span ℚ {h ^ g} := by
  sorry

/-- Hodge classes live in degrees `0, …, 2g`: `H^{p,p}(A, ℚ) = 0` for `p > g`. -/
theorem hodge_eq_bot_of_lt (p : ℕ) (hp : g < p) : A.hodge p = ⊥ := by
  sorry

end AbVar

end WeilClasses
