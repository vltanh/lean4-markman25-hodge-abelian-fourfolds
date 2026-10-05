# Credits

How this formalization was made, from the session transcript and the run log.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who requested the formalization and chose its scope: prove the paper's
  results about cohomology, Clifford algebras, spin representations and period domains, keep the sheaf theory of
  §§7–9 and the cited results about algebraic cycles as named hypotheses, and formalize them in layers later. They
  decided every change of a statement of the paper (Section 6 of [`REPORT.md`](REPORT.md)), the two authorized
  departures from the paper's proofs (Proposition 6.1.2, Lemma 4.0.2), and that two parts of Igusa's Proposition 3
  stay hypotheses.
- **Tool:** Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), run as an agent in Claude Code 2.1.288 (VS Code
  extension), in one session with sub-agents. It wrote the Lean code and the documents under the direction of the
  maintainer.
- **Procedure:** the skill [formalize-math-paper](https://github.com/vltanh/formalize-math-paper), version 2.1.0 (commit `397f71c`).
- **Review:** no person has reviewed the proofs. Independent AI agents reviewed the statements against the TeX source
  before any proof was written, compared every formal proof with the paper's proof afterwards, and verified the
  audit's findings and its literature survey, as described below.

## First formalization (4 October 2026)

How it was made:

- **Setup.** The main session fetched the paper's TeX source (v1 and v2), searched for later versions and earlier
  formalizations, surveyed Mathlib and Tau Ceti (one agent), set up the project on Lean `v4.35.0-rc3` with Mathlib and
  Tau Ceti, and asked the owner the scope questions.
- **Statements.** Five agents stated the results of §§2–6, §8 and §10 in parallel; the main session wrote the model of
  abelian varieties, the hypotheses, the explicit `X × X̂`, the main theorems and the Challenge. Eleven statements of
  the paper turned out false or misprinted: the owner approved each of the eight corrections of substance after seeing
  a counterexample, and the three obvious misprints and slips were corrected directly and reported.
- **Statement review.** Five reviewers checked every statement and definition against the TeX source (with numerical
  checks); they found two statements made false by the formalization itself (a hypothesis silently dropped from a
  `variable`), which were fixed, and one sign convention, which was corrected. The reviewed statements are the
  baseline (commit `95bc161`).
- **Proofs.** Fourteen prover agents proved the paper's results in parallel, on disjoint modules, each against a
  private snapshot of the build. Four agents then proved the cited results in `External/`. Two refactoring agents
  moved definitions upstream so that proofs cite the External results as the paper does.
- **Proof review.** Five reviewers compared every formal proof with the paper's proof in the TeX source and classified
  every route difference. They found departures without an admissible reason and cited results proved again instead of
  cited; five fix agents rewrote those steps to follow the paper. The main session narrowed the hypothesis for §§7–9
  so that it no longer contained a step the paper proves (Corollary 1.3.2).
- **Audit.** One agent drafted the survey of later work; two verifiers checked the findings about the paper against the
  TeX source in an exact model of its conventions, and the survey against its sources (with three helper agents of its
  own). The verifier of the survey found the author's correction of §2.1. A further agent checked [`REPORT.md`](REPORT.md),
  [`README.md`](README.md) and [`formalization.yaml`](formalization.yaml) against the TeX source, the Lean code and the verified survey; its corrections
  were applied.
- **Integration.** The main session integrated the work, ran the checks (statement diffs against the baseline, the
  dropped-variable scans, the axiom audit, the route check, Comparator), removed unused hypotheses and warnings, and
  wrote the documents.

Figures, from the start (4 October 2026, 07:51 CDT) to the commit that completed [`REPORT.md`](REPORT.md)
(22:16 CDT):

- elapsed time: 14 h 25 min;
- sub-agents: 52 (45 launched by the main session, 7 by other sub-agents), at most 10 running at once, 58.2 h of
  working time in all;
- tool calls: 9,829 (8,943 by sub-agents, 886 by the main session);
- tokens: 18.88 M output, 54.76 M input (uncached input and cache writes) and 3,834 M cache reads
  (sub-agents: 17.39 M, 50.95 M and 3,385 M; main session: 1.49 M, 3.81 M and 449 M);
- model calls: 9,236 (868 by the main session, 8,368 by sub-agents), all to `claude-opus-5-5`.

The figures are those that the session transcripts record. They leave out the time the owner spent answering
questions, which is included in the elapsed time, and the builds run by background commands, which are not agent
work.

## Roadmap, Layer 1 (4–5 October 2026)

At the owner's request, the main session wrote [`ROADMAP.md`](ROADMAP.md), after a survey of the Lean ecosystem by
one agent (its claims spot-checked by the main session), and then carried out the first layer:

- **Meyer's theorem.** The main session copied the Hasse–Minkowski development of jayyswan/hasse-minkowski (as
  packaged in Vilin97/lean-pool, Apache-2.0) into [`WeilClasses/External/HasseMinkowski/`](WeilClasses/External/HasseMinkowski), with two edits for this
  project's Mathlib commit.
- **Three provers in parallel**, each on new files against a private snapshot of the build: [van Geemen, Th. 5.2(3)]
  in the case used, through Landherr's theorem; Igusa's normal form; and [Schoen, Prop. 10] from push-forward of
  cycles, by Voisin's argument. The prover of the last corrected two steps of its brief (the class of the product it
  had been told to use is not a Hodge–Weil class; the discriminant of the fourfold must be taken positive).
- **Integration.** The main session removed the hypotheses `VanGeemenModuli`, [`SchoenDegeneration`](WeilClasses/External/Voisin/Lemma2_9.lean#L2221) (replaced by the
  standard [`PushforwardClosed`](Challenge.lean#L404)) and `IgusaProp3NormalForm`, narrowed [`IgusaProp3OrbitSubfield`](WeilClasses/External/Igusa/Sec10.lean#L2026), rebuilt, reran the
  checks and updated the documents.

Figures for this round, from 4 October 2026, 22:31 CDT to the commit that completed it (5 October 2026, 01:37 CDT):

- elapsed time: 3 h 6 min;
- sub-agents: 4, at most 3 running at once, 3.9 h of working time in all;
- tool calls: 775 (614 by sub-agents, 161 by the main session);
- model calls: 743 (165 by the main session, 578 by sub-agents), all to `claude-opus-5-5`.

