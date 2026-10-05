module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the library, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find PaperName -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all WeilClasses.AbelianVariety.Defs
import all WeilClasses.AbelianVariety.Lemmas
import all WeilClasses.Basic.Field
import all WeilClasses.Chevalley.Defs
import all WeilClasses.Chevalley.Sec2_3
import all WeilClasses.Correspondence.Defs
import all WeilClasses.Correspondence.FourierMukai
import all WeilClasses.Correspondence.Sec5_2
import all WeilClasses.Defs
import all WeilClasses.External.Chevalley.Sec2_1
import all WeilClasses.External.Chevalley.Sec2_2
import all WeilClasses.External.Chevalley.Sec2_3
import all WeilClasses.External.Chevalley.Sec2_4
import all WeilClasses.External.Chevalley.Sec3
import all WeilClasses.External.GolyshevLuntsOrlov.Sec2_1
import all WeilClasses.External.GolyshevLuntsOrlov.Sec6_1
import all WeilClasses.External.Huybrechts.Sec6_1
import all WeilClasses.External.Huybrechts.Sec6_3
import all WeilClasses.External.Igusa.Sec10
import all WeilClasses.External.Igusa.Sec2_2
import all WeilClasses.External.Igusa.Sec2_4
import all WeilClasses.External.Markman.Sec8_2
import all WeilClasses.External.Orlov.Sec6_1
import all WeilClasses.External.Trautman.Sec2_3
import all WeilClasses.External.VanGeemen.Sec3
import all WeilClasses.Hermitian.ComplexStructures
import all WeilClasses.Hermitian.Defs
import all WeilClasses.Hodge.Ample
import all WeilClasses.Hodge.Defs
import all WeilClasses.Igusa.CM
import all WeilClasses.Igusa.Defs
import all WeilClasses.Igusa.Secant
import all WeilClasses.Main.Compare
import all WeilClasses.Main.Coordinates
import all WeilClasses.Main.Instances
import all WeilClasses.Main.Intro
import all WeilClasses.Main.Jacobian
import all WeilClasses.Main.Theorems
import all WeilClasses.Orlov.Basis
import all WeilClasses.Orlov.Cor1_3_2
import all WeilClasses.Orlov.Defs
import all WeilClasses.Orlov.Intro
import all WeilClasses.Orlov.Sec6_1
import all WeilClasses.Orlov.Sec6_2
import all WeilClasses.Orlov.Sec6_3
import all WeilClasses.Orlov.Sec6_4
import all WeilClasses.PeriodDomain.Defs
import all WeilClasses.PeriodDomain.SemiHodge
import all WeilClasses.PureSpinor.CM
import all WeilClasses.PureSpinor.Defs
import all WeilClasses.PureSpinor.Groups
import all WeilClasses.PureSpinor.Lemma2_2_1
import all WeilClasses.PureSpinor.Lemma2_2_4
import all WeilClasses.PureSpinor.Lemma2_2_6
import all WeilClasses.PureSpinor.Lemma2_2_7
import all WeilClasses.PureSpinor.Sec2_1
import all WeilClasses.PureSpinor.Stabilizer
import all WeilClasses.Secant.Defs
import all WeilClasses.Secant.Sec8_1
import all WeilClasses.Secant.Sec8_2
import all WeilClasses.Secant.Sec8_3
import all WeilClasses.Spinor.BaseChange
import all WeilClasses.Spinor.Defs
import all WeilClasses.Spinor.Embeddings
import all WeilClasses.Spinor.Integral
import all WeilClasses.WeilType.Basic
import all WeilClasses.WeilType.CliffordExp
import all WeilClasses.WeilType.Theta
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`WeilClasses/External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`. Keep one `import all` line per module of the library, each on its own
line: a module that is missing is still imported through the others, but without its proofs, and
the audit then misses the axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work in `WeilClasses/External/`, with a short label: the theorems proved
there and, in a conditional formalization, the propositions assumed as hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("hypothesis", ``WeilClasses.PullbackClosed),
   ("hypothesis", ``WeilClasses.SubalgebraClosed),
   ("hypothesis", ``WeilClasses.LefschetzOneOne),
   ("hypothesis", ``WeilClasses.VoisinLocus),
   ("hypothesis", ``WeilClasses.VanGeemenModuli),
   ("hypothesis", ``WeilClasses.SchoenDegeneration),
   ("hypothesis", ``WeilClasses.MoonenZarhinSimple),
   ("hypothesis", ``WeilClasses.RamonMariProducts),
   ("hypothesis", ``WeilClasses.MoonenZarhinLowDim),
   ("hypothesis", ``WeilClasses.SecantSheafDeformation),
   ("Chevalley", ``WeilClasses.chevalley_III_2_2),
   ("Chevalley", ``WeilClasses.chevalley_III_2_1),
   ("Chevalley", ``WeilClasses.chevalley_III_1_4_exists),
   ("Chevalley", ``WeilClasses.chevalley_III_1_4_unique),
   ("Chevalley", ``WeilClasses.chevalley_III_1_5_families),
   ("Chevalley", ``WeilClasses.chevalley_III_1_12),
   ("Chevalley", ``WeilClasses.chevalley_III_2_4),
   ("Chevalley", ``WeilClasses.chevalley_III_2_4_self),
   ("Chevalley", ``WeilClasses.chevalley_III_3_1_bijective),
   ("Chevalley", ``WeilClasses.chevalley_III_3_1_equivariant),
   ("Chevalley", ``WeilClasses.chevalley_III_3_2),
   ("Chevalley", ``WeilClasses.chevalley_sec3_3_lemma1),
   ("Chevalley", ``WeilClasses.chevalley_II_1_6_filtration),
   ("Chevalley", ``WeilClasses.chevalley_II_1_6_surjective),
   ("Chevalley", ``WeilClasses.chevalley_II_1_6_injective),
   ("Chevalley", ``WeilClasses.chevalley_sec3_3_conj_mem),
   ("Chevalley", ``WeilClasses.chevalley_sec3_3_equivariant),
   ("Chevalley", ``WeilClasses.chevalley_p85_transport_graded),
   ("Chevalley", ``WeilClasses.chevalley_III_1_7_mem),
   ("Chevalley", ``WeilClasses.chevalley_III_1_7_rho),
   ("Chevalley", ``WeilClasses.chevalley_III_3_2_III_4_5),
   ("GolyshevLuntsOrlov", ``WeilClasses.glo_prop3_2_1_e_field),
   ("GolyshevLuntsOrlov", ``WeilClasses.glo_prop3_2_1_e_integral),
   ("GolyshevLuntsOrlov", ``WeilClasses.glo_prop4_3_7),
   ("Huybrechts", ``WeilClasses.huybrechts_ex9_41),
   ("Huybrechts", ``WeilClasses.huybrechts_lemma9_23_X),
   ("Huybrechts", ``WeilClasses.huybrechts_lemma9_23_Xhat),
   ("Huybrechts", ``WeilClasses.huybrechts_cor9_24),
   ("Igusa", ``WeilClasses.igusa_prop3_invariant),
   ("Igusa (hypothesis)", ``WeilClasses.IgusaProp3NormalForm),
   ("Igusa", ``WeilClasses.igusa_prop3_normalForm_of_sq),
   ("Igusa", ``WeilClasses.igusa_prop3_orbit_complex),
   ("Igusa (hypothesis)", ``WeilClasses.IgusaProp3OrbitSubfield),
   ("Igusa", ``WeilClasses.igusa_prop3_orbit_subfield),
   ("Igusa", ``WeilClasses.igusa_prop3_normalForm),
   ("Igusa", ``WeilClasses.igusa_lemma2),
   ("Igusa", ``WeilClasses.igusa_lemma1_ker),
   ("Igusa", ``WeilClasses.igusa_lemma1_range),
   ("Igusa", ``WeilClasses.igusa_lemma1_dual),
   ("Igusa", ``WeilClasses.igusa_lemma1_sq),
   ("Igusa", ``WeilClasses.igusa_lemma2_stab_odd),
   ("Igusa", ``WeilClasses.igusa_lemma2_stab_even),
   ("Igusa", ``WeilClasses.igusa_sec2_mem),
   ("Igusa", ``WeilClasses.igusa_sec2_rho),
   ("Markman", ``WeilClasses.markmanM2_prop1_7),
   ("Orlov", ``WeilClasses.orlov_theorem2_10),
   ("Trautman", ``WeilClasses.trautman_theorem1_i),
   ("VanGeemen", ``WeilClasses.vanGeemen_def4_9)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Proposition 1.2.1", ``WeilClasses.proposition1_2_1),
   ("Proposition 1.3.1", ``WeilClasses.proposition1_3_1_eq),
   ("Proposition 1.3.1", ``WeilClasses.proposition1_3_1_equivariant),
   ("Corollary 1.3.2", ``WeilClasses.corollary1_3_2),
   ("Corollary 1.3.2", ``WeilClasses.corollary1_3_2_hodge),
   ("(1.3.2)", ``WeilClasses.equation1_3_2_equivariant),
   ("Theorem 1.4.1(1)", ``WeilClasses.theorem1_4_1_1),
   ("Theorem 1.4.1(2)", ``WeilClasses.theorem1_4_1_2_rank),
   ("Theorem 1.4.1(3)", ``WeilClasses.theorem1_4_1_3),
   ("Theorem 1.4.1(4)", ``WeilClasses.theorem1_4_1_4),
   ("Theorem 1.4.1(4)", ``WeilClasses.theorem1_4_1_4_finrank),
   ("Theorem 1.4.1 (3)", ``WeilClasses.theorem1_4_1_3_model),
   ("Theorem 1.4.1 (4)", ``WeilClasses.theorem1_4_1_4_model),
   ("Theorem 1.5.1", ``WeilClasses.theorem1_5_1),
   ("Corollary 1.6.1", ``WeilClasses.corollary1_6_1),
   ("Lemma 2.2.1", ``WeilClasses.lemma2_2_1),
   ("Lemma 2.2.1", ``WeilClasses.lemma2_2_1_even),
   ("Lemma 2.2.1", ``WeilClasses.lemma2_2_1_odd),
   ("Lemma 2.2.2", ``WeilClasses.lemma2_2_2),
   ("Lemma 2.2.2", ``WeilClasses.lemma2_2_2_restrict),
   ("Remark 2.2.3", ``WeilClasses.remark2_2_3_not_pure),
   ("Remark 2.2.3", ``WeilClasses.remark2_2_3_odd),
   ("Remark 2.2.3", ``WeilClasses.remark2_2_3_even),
   ("Remark 2.2.3", ``WeilClasses.remark2_2_3_determines),
   ("Remark 2.2.3", ``WeilClasses.remark2_2_3_unique_secant),
   ("Lemma 2.2.4", ``WeilClasses.lemma2_2_4),
   ("Remark 2.2.5", ``WeilClasses.remark2_2_5),
   ("Lemma 2.2.6", ``WeilClasses.lemma2_2_6),
   ("Lemma 2.2.6", ``WeilClasses.lemma2_2_6_V01),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_hodge),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_odd),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_even),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_middle),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_eq),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_indep),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_finrank),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_det₁),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_det₂),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_K_trivial),
   ("Lemma 2.2.7", ``WeilClasses.lemma2_2_7_trivial),
   ("Remark 2.3.1", ``WeilClasses.remark2_3_1_B0bar_apply),
   ("Remark 2.3.1", ``WeilClasses.remark2_3_1_altPart_add_pairing),
   ("Remark 2.3.1", ``WeilClasses.remark2_3_1_B0bar_eq_neg_half_c1P),
   ("Remark 2.3.1", ``WeilClasses.remark2_3_1_sym_equivariant),
   ("Remark 2.3.1", ``WeilClasses.remark2_3_1_sym_bijective),
   ("Lemma 2.3.2(1)", ``WeilClasses.lemma2_3_2_1),
   ("Lemma 2.3.2(2)", ``WeilClasses.lemma2_3_2_2),
   ("Lemma 2.4.2", ``WeilClasses.lemma2_4_2),
   ("Remark 2.4.3", ``WeilClasses.remark2_4_3_mem),
   ("Remark 2.4.3", ``WeilClasses.remark2_4_3_rho),
   ("Remark 2.4.3", ``WeilClasses.remark2_4_3_complexStructure),
   ("Remark 2.4.3", ``WeilClasses.remark2_4_3_exists_lift),
   ("Remark 2.4.3", ``WeilClasses.remark2_4_3),
   ("(2.4.4)", ``WeilClasses.equation2_4_4),
   ("Proposition 2.4.4", ``WeilClasses.proposition2_4_4),
   ("(2.4.5)", ``WeilClasses.equation2_4_5),
   ("(2.4.6)", ``WeilClasses.equation2_4_6_W₁),
   ("(2.4.6)", ``WeilClasses.equation2_4_6_W₂),
   ("Lemma 3.1.1", ``WeilClasses.lemma3_1_1),
   ("Lemma 3.1.2", ``WeilClasses.KSecant.s3_hasSignature),
   ("Lemma 3.1.2", ``WeilClasses.lemma3_1_2_hermitian),
   ("Lemma 3.1.2", ``WeilClasses.lemma3_1_2_linear),
   ("Lemma 3.1.2", ``WeilClasses.lemma3_1_2_invariant),
   ("Lemma 3.1.2", ``WeilClasses.lemma3_1_2_signature),
   ("Lemma 3.1.2", ``WeilClasses.lemma3_1_2_finiteIndex),
   ("Lemma 3.1.3", ``WeilClasses.lemma3_1_3),
   ("Lemma 3.2.1", ``WeilClasses.lemma3_2_1),
   ("(3.2.1)", ``WeilClasses.equation3_2_1),
   ("Corollary 3.2.2", ``WeilClasses.corollary3_2_2_rational),
   ("Corollary 3.2.2", ``WeilClasses.corollary3_2_2_hodge),
   ("Corollary 3.2.3", ``WeilClasses.corollary3_2_3_type11),
   ("Corollary 3.2.3", ``WeilClasses.corollary3_2_3_kahler),
   ("Corollary 3.2.3", ``WeilClasses.corollary3_2_3_comm),
   ("Corollary 3.2.3", ``WeilClasses.corollary3_2_3_weil),
   ("Corollary 3.2.3", ``WeilClasses.corollary3_2_3_polarization),
   ("Lemma 4.0.1", ``WeilClasses.lemma4_0_1_injective),
   ("Lemma 4.0.1", ``WeilClasses.lemma4_0_1_nonempty),
   ("Lemma 4.0.1", ``WeilClasses.lemma4_0_1_isOpen),
   ("Lemma 4.0.1", ``WeilClasses.lemma4_0_1_isEmbedding),
   ("Lemma 4.0.2", ``WeilClasses.lemma4_0_2),
   ("Lemma 4.0.3", ``WeilClasses.lemma4_0_3_hodgeWeil),
   ("Lemma 4.0.3", ``WeilClasses.lemma4_0_3_semiHodge),
   ("Corollary 4.0.4", ``WeilClasses.corollary4_0_4),
   ("(5.2.1)", ``WeilClasses.equation5_2_1),
   ("Lemma 5.2.1", ``WeilClasses.lemma5_2_1_1),
   ("Lemma 5.2.1", ``WeilClasses.lemma5_2_1_2),
   ("(5.2.2)", ``WeilClasses.equation5_2_2),
   ("Corollary 5.2.2", ``WeilClasses.corollary5_2_2_1),
   ("Corollary 5.2.2", ``WeilClasses.corollary5_2_2_2),
   ("(5.2.3)", ``WeilClasses.equation5_2_3),
   ("Remark 5.2.3", ``WeilClasses.remark5_2_3),
   ("Lemma 6.1.1", ``WeilClasses.lemma6_1_1),
   ("Proposition 6.1.2", ``WeilClasses.proposition6_1_2),
   ("(6.1.4)", ``WeilClasses.rhoPrime_eq_phiOrlov_conj),
   ("(6.1.8)", ``WeilClasses.equation6_1_8),
   ("(6.1.8)", ``WeilClasses.equation6_1_8_integral),
   ("(6.1.9)", ``WeilClasses.equation6_1_9),
   ("Lemma 6.2.3", ``WeilClasses.lemma6_2_3),
   ("Lemma 6.2.3", ``WeilClasses.lemma6_2_3_unique),
   ("(6.2.4)", ``WeilClasses.equation6_2_4),
   ("(6.2.4)", ``WeilClasses.equation6_2_4_exists),
   ("Remark 6.2.4", ``WeilClasses.remark6_2_4),
   ("Remark 6.2.4", ``WeilClasses.remark6_2_4_ell),
   ("Lemma 6.2.5", ``WeilClasses.lemma6_2_5),
   ("(6.2.5)", ``WeilClasses.equation6_2_5),
   ("Lemma 6.2.6(1)", ``WeilClasses.lemma6_2_6_1),
   ("Lemma 6.2.6(2)", ``WeilClasses.lemma6_2_6_2),
   ("(6.3.1)", ``WeilClasses.equation6_3_1),
   ("Lemma 6.3.1", ``WeilClasses.lemma6_3_1),
   ("(6.3.2)", ``WeilClasses.equation6_3_2),
   ("Lemma 6.3.2", ``WeilClasses.lemma6_3_2),
   ("Remark 6.3.3", ``WeilClasses.remark6_3_3),
   ("Proposition 6.4.1(1)", ``WeilClasses.proposition6_4_1_1_line₁),
   ("Proposition 6.4.1(1)", ``WeilClasses.proposition6_4_1_1_line₂),
   ("Proposition 6.4.1(1)", ``WeilClasses.proposition6_4_1_1),
   ("Proposition 6.4.1(2)", ``WeilClasses.proposition6_4_1_2_even),
   ("Proposition 6.4.1(2)", ``WeilClasses.proposition6_4_1_2_odd),
   ("(8.1.1)", ``WeilClasses.equation8_1_1),
   ("Lemma 8.1.1", ``WeilClasses.lemma8_1_1),
   ("(8.1.2)", ``WeilClasses.equation8_1_2),
   ("Lemma 8.2.1", ``WeilClasses.lemma8_2_1),
   ("Example 8.2.2", ``WeilClasses.example8_2_2),
   ("Lemma 8.3.1", ``WeilClasses.lemma8_3_1_rank),
   ("Lemma 8.3.1", ``WeilClasses.lemma8_3_1),
   ("Lemma 10.1.1", ``WeilClasses.lemma10_1_1),
   ("Lemma 10.1.1", ``WeilClasses.lemma10_1_1_stabilizer),
   ("Lemma 10.1.1", ``WeilClasses.lemma10_1_1_rational),
   ("Remark 10.1.2(1)", ``WeilClasses.remark10_1_2_orbit),
   ("Remark 10.1.2(1)", ``WeilClasses.remark10_1_2_value),
   ("Remark 10.1.2(2)", ``WeilClasses.remark10_1_2_secant),
   ("Remark 10.1.2(2)", ``WeilClasses.remark10_1_2_singular),
   ("Remark 10.1.2(2)", ``WeilClasses.remark10_1_2_rational),
   ("Lemma 10.2.1", ``WeilClasses.lemma10_2_1),
   ("Lemma 10.2.1", ``WeilClasses.lemma10_2_1_centralizer),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_theta_sq),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_w),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_steps),
   ("Example 10.2.2", ``WeilClasses.example10_2_2),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_principal),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_alpha),
   ("Example 10.2.2", ``WeilClasses.example10_2_2_field),
   ("Example 10.2.3", ``WeilClasses.example10_2_3),
   ("Example 10.2.3", ``WeilClasses.example10_2_3_field)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``WeilClasses.Challenge.Kd_Nm, ``WeilClasses.Challenge.fX_mul_self, ``WeilClasses.Challenge.JX_mem_weilDomain, ``WeilClasses.Challenge.discIs_XXhat, ``WeilClasses.Challenge.rank_chE, ``WeilClasses.Challenge.theorem1_4_1_3, ``WeilClasses.Challenge.theorem1_4_1_4, ``WeilClasses.Challenge.theorem1_5_1, ``WeilClasses.Challenge.corollary1_6_1]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`WeilClasses).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
