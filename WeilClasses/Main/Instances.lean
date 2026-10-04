module

public import WeilClasses.Main.Theorems

/-!
# The hypotheses of the main theorems can be met

A check that the conditional statements of Theorem 1.5.1 and Corollary 1.6.1 are not vacuous:
their hypotheses are consistent, and the objects they quantify over exist.

* **The hypothesis classes on a system of algebraic classes.** For the system
  `CycleClasses.all`, in which every rational class is algebraic, each of `PullbackClosed`,
  `SubalgebraClosed`, `LefschetzOneOne`, `VoisinLocus`, `SecantSheafDeformation`,
  `SchoenDegeneration` and `RamonMariProducts` holds. For `SecantSheafDeformation` this needs a
  complex structure on `ℝ⁶` for which `ThetaStd` is ample: the standard `J₀`
  (`main_J0`, `main_ample_J0`).
* **The objects.** For every `n` and every `d > 0`, `X × X̂` (with `X = (ℝ^{2n}, J₀)`) is a
  polarized abelian `2n`-fold of Weil type for `ℚ(√-d)` with discriminant `(-1)ⁿ`
  (`XXhatWeil`, `XXhatWeil_discIs`); for `n = 3` this is a sixfold with discriminant `-1`, as in
  Theorem 1.5.1. `(ℝ⁸, J₀)` is an abelian fourfold, as in Corollary 1.6.1.

The three hypotheses that do not involve the system of algebraic classes, `VanGeemenModuli`,
`MoonenZarhinSimple` and `MoonenZarhinLowDim`, are published theorems ([van Geemen, Th. 5.2(3)],
[Moonen–Zarhin 1995, Th. 2.11], [Moonen–Zarhin 1999, Prop. 3.8, Th. 0.1(i)]) about Hodge
structures of abelian varieties. No instance of them is constructed here: that would be a proof
of those theorems (see `REPORT.md`).
-/

@[expose] public section

namespace WeilClasses

/-! ### The system in which every class is algebraic -/

/-- The system of algebraic classes in which every rational class is algebraic. -/
def CycleClasses.all : CycleClasses := ⟨fun _ _ => ⊤⟩

instance CycleClasses.all_pullbackClosed : PullbackClosed CycleClasses.all :=
  ⟨fun _ _ _ _ _ _ => Submodule.mem_top⟩

instance CycleClasses.all_subalgebraClosed : SubalgebraClosed CycleClasses.all :=
  ⟨fun _ => Submodule.mem_top, fun _ _ _ _ _ => Submodule.mem_top⟩

instance CycleClasses.all_lefschetzOneOne : LefschetzOneOne CycleClasses.all :=
  ⟨fun _ => le_top⟩

instance CycleClasses.all_voisinLocus : VoisinLocus CycleClasses.all :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ => Submodule.mem_top⟩

instance CycleClasses.all_secantSheafDeformation : SecantSheafDeformation CycleClasses.all :=
  ⟨fun _ _ => ⟨main_J0 3, main_J0_isComplex 3, main_ample_J0 3, fun _ _ =>
    Filter.Eventually.of_forall fun _ _ => Submodule.mem_top⟩⟩

instance CycleClasses.all_schoenDegeneration : SchoenDegeneration CycleClasses.all :=
  ⟨fun _ _ _ _ _ => le_top⟩

instance CycleClasses.all_ramonMariProducts : RamonMariProducts CycleClasses.all :=
  ⟨fun _ _ _ _ _ => le_top⟩

/-! ### `X × X̂` as a polarized abelian variety of Weil type -/

variable (n : ℕ) (d : ℚ) (hd : 0 < d)

/-- The standard principally polarized abelian `n`-fold `X = (ℝ^{2n}, J₀)`. -/
noncomputable def stdAbVar : AbVar n := ⟨main_J0 n, main_J0_isComplex n, ⟨_, main_ample_J0 n⟩⟩

/-- `X × X̂` for `X = (ℝ^{2n}, J₀)`, as an abelian `2n`-fold. -/
noncomputable def XXhatAbVar : AbVar (2 * n) :=
  have h := JX_mem_weilDomain n d hd (main_J0 n) (main_J0_isComplex n) (main_ample_J0 n)
    (etaX n d hd) (etaX_sqrtNeg n d hd)
  ⟨JX n (main_J0 n), h.1, ⟨hX n d, h.2.2.2.2.1⟩⟩

/-- `X × X̂` with the action `η` of `ℚ(√-d)` (`η(√-d) = f`) and the polarization `h = dΘ + Θ̂`:
a polarized abelian `2n`-fold of Weil type. -/
noncomputable def XXhatWeil : PolarizedWeilType (XXhatAbVar n d hd) d :=
  have h := JX_mem_weilDomain n d hd (main_J0 n) (main_J0_isComplex n) (main_ample_J0 n)
    (etaX n d hd) (etaX_sqrtNeg n d hd)
  { η := etaX n d hd
    isHodge := h.2.1
    weil₁ := h.2.2.1
    weil₂ := h.2.2.2.1
    h := hX n d
    ample := h.2.2.2.2.1
    norm := h.2.2.2.2.2 }

/-- The discriminant of `X × X̂` is `(-1)ⁿ`. -/
theorem XXhatWeil_discIs : (XXhatWeil n d hd).DiscIs ((-1) ^ n) :=
  discIs_XXhat n d hd _ _ (etaX_sqrtNeg n d hd) rfl

/-- The objects of Theorem 1.5.1 exist: for every `d > 0` there is a polarized abelian sixfold of
Weil type for `ℚ(√-d)` with discriminant `-1`. -/
theorem exists_sixfold_discIs_neg_one (d : ℚ) (hd : 0 < d) :
    ∃ (A : AbVar (2 * 3)) (X : PolarizedWeilType A d), X.DiscIs (-1) :=
  ⟨_, XXhatWeil 3 d hd, by
    have h := XXhatWeil_discIs 3 d hd
    rwa [show ((-1 : ℚ) ^ 3) = -1 by norm_num] at h⟩

end WeilClasses
