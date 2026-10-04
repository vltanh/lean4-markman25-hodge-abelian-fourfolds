# Chevalley, *The algebraic theory of spinors* (1954)

[Ch] C. Chevalley, *The algebraic theory of spinors*, Columbia Univ. Press, 1954. The quadratic
space is `V_F = H¹(X̂, F) ⊕ H¹(X, F)` with `Q(θ, w) = θ(w)` (maximal Witt index), over a field `F`
of characteristic zero; the spin representation is `S_F = ⋀• H¹(X, F)` with
`m_{(θ,w)} = L_w + D_θ`.
Each file of this directory states the results of [Ch] that the paper cites, named after the
section of the paper that first uses them. The sections below are written by the provers of the
files.

## `Sec2_3.lean`: [II.1.6], [Sec. 3.3], [p. 85] (prover SB)

Used in §2.3 for `B = B₀` (TeX lines 1064–1077) and, through Lemma 6.1.1, in §6.1. All six
statements are proved; none is a hypothesis.

Statements and how they relate to [Ch]:

* `ψ_B` is Mathlib's `CliffordAlgebra.changeForm` for the bilinear form `-B`, from `Q` to the zero
  form, i.e. into `CliffordAlgebra 0 = ⋀•V`: `ψ_B(1) = 1` and
  `ψ_B(v x) = v ∧ ψ_B(x) + B(v, ·) ⌋ ψ_B(x)` (Chevalley's `λ`, Bourbaki's `λ_B`). The statements
  hold for every `B` with `B(u, u) = Q(u)` (hypothesis `hB`); the paper uses `B = B₀`
  (`WeilClasses.psi`).
* `C(V)_k` is `CFilt k` (products of at most `k` vectors), `F^k(⋀•V) = ⊕_{i ≤ k} ⋀^i V` is
  `extFiltLE k`. The quotient `C(V)_k / C(V)_{k-1}` is not formed: the graded map
  `ψ̄_k(x mod C(V)_{k-1})` is `projDeg k (ψ_B x)` for `x ∈ C(V)_k`.
* [II.1.6]: `chevalley_II_1_6_filtration` (`ψ_B(C(V)_k) ⊆ F^k(⋀•V)`),
  `chevalley_II_1_6_surjective` and `chevalley_II_1_6_injective` (`ψ̄_k` is onto `⋀^k V`, with
  kernel `C(V)_{k-1}`, i.e. `C(V)_k / C(V)_{k-1} ≅ ⋀^k V`).
* [Sec. 3.3]: `chevalley_sec3_3_conj_mem` (conjugation `x ↦ g x g⁻¹` by `g ∈ Spin(V)` preserves
  `C(V)_k`) and `chevalley_sec3_3_equivariant` (`ψ̄_k(g x g⁻¹) = ⋀^k ρ_g (ψ̄_k(x))`).
* [p. 85, after III.3.1]: `chevalley_p85_transport_graded`: if `ψ_B(φ(y)) ∈ F^k(⋀•V)` for
  `y ∈ S ⊗ S`, then `ψ_B(φ((m_g ⊗ m_g) y)) ∈ F^k(⋀•V)` and its degree-`k` part is `⋀ρ_g` of the
  degree-`k` part of `ψ_B(φ(y))`: the action transported by `ψ_B ∘ φ` preserves the filtration, with
  associated graded action `⋀ρ`, whatever `B` is.

Proofs. `CFilt k` and `extFiltLE k` are Tau Ceti's Clifford degree filtrations
(`CliffordAlgebra.filtration`) of `C(V)` and of `CliffordAlgebra 0`; `ψ_B` is filtered and reflects
the filtration (`changeForm_mem_filtration(_iff)`), and `ψ_B(v₁ ⋯ v_j) = v₁ ∧ ⋯ ∧ v_j` modulo
`F^{j-1}` (`changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration`). Surjectivity lifts
`v₁ ∧ ⋯ ∧ v_k` to `v₁ ⋯ v_k`; injectivity uses that `ψ_B` is bijective (`changeFormEquiv`) and
reflects the filtration. Conjugation by `g ∈ Spin(V)` is `CliffordAlgebra.map` of the isometry `ρ_g`
(`sb_conjSpin_eq_map`, since `g⁻¹ = g*`), which maps products of `j` vectors to products of `j`
vectors; comparing leading terms on these spanning products gives the equivariance. [p. 85] follows
from [III.3.1] (`chevalley_III_3_1_equivariant` in `Sec2_2.lean`, extended from `s ⊗ t` to all of
`S ⊗ S` in `sb_varphi_map`) and [Sec. 3.3]; it is the only statement of this file that uses another
cited result. Public helpers: `sb_rhoIsometry` (`ρ_g` as an isometry of `Q`), `sb_coe_inv`,
`sb_conjSpin_eq_map`, `sb_varphi_map` (also used by `WeilClasses.External.Trautman.Sec2_3`).

## `Sec2_1.lean`, `Sec2_2.lean`, `Sec2_4.lean`, `Sec3.lean`: [III.1–III.4] (prover SA)

All fifteen statements are proved; none is a hypothesis. They are stated in the Fock model
`S = ⋀•H`, `V = H* × H`, `H = H¹(X, F) = F^{2n}`; a *pure spinor* is an even (odd) `w` whose
annihilator `ann w = ker (v ↦ m_v w)` is maximal isotropic (`dim 2n`).

Statements and their places in [Ch]:

* `Sec2_1.lean`: [III.2.2] `chevalley_III_2_2` (`m_v` is self-adjoint for the Mukai pairing,
  Chevalley's `β`) and [III.2.1] `chevalley_III_2_1` (`(g s, g t)_S = N(g) (s, t)_S`). Used in §2.1.
* `Sec2_2.lean`: [III.1.4] `chevalley_III_1_4_exists`, `chevalley_III_1_4_unique`; [III.1.5]
  `chevalley_III_1_5_families` (only the disjointness of the two families; the isotropic
  Grassmannian is not modeled); [III.1.12] `chevalley_III_1_12` (`n > 1`); [III.2.4]
  `chevalley_III_2_4`, `chevalley_III_2_4_self` (`n > 0`); [III.3.1]
  `chevalley_III_3_1_bijective`, `chevalley_III_3_1_equivariant` for Chevalley's
  `φ(u ⊗ v) = u [pt_X̂] τ(v)` (2.2.5); [III.3.2] `chevalley_III_3_2` (`φ(u ⊗ u)` spans
  `⋀^{2n} ker m_u ⊆ C(V)`); [§3.3, Lemma 1] `chevalley_sec3_3_lemma1`, restricted to pairs from the
  even family (as used in §6.4; `Spin` preserves the families).
* `Sec2_4.lean`: [III.1.7] `chevalley_III_1_7_mem`, `chevalley_III_1_7_rho` (`exp(u) ∈ Spin(V)` for
  `u ∈ ⋀² H`, acting by `(y, w) ↦ (y, w - y ⌋ u)`; the paper's (2.4.4)).
* `Sec3.lean`: [III.3.2 + III.4.5] `chevalley_III_3_2_III_4_5`: if `g ∈ Spin(V)` preserves
  `W = ker m_u` (`u` even pure), then `g u = c u` with `c² = det(ρ(g)|_W)` (proof of Lemma 3.1.1).

Proofs (by arguments in the model, not Chevalley's; no orbit or transitivity theorem is imported):

* III.2.2 by `m_{(θ,w)} = L_w + D_θ`, `τ(w ∧ s) = τ(s) ∧ w` and `∫ τ(D_θ s) t = ∫ τ(s) D_θ t`
  (`∫ ∘ D_θ = 0`); induction gives `(m_x s, t)_S = (s, m_{τ(x)} t)_S` (`sa_mukai_m_reverse`), and
  III.2.1 follows from `τ(g) g = N(g)` (membership in the Clifford group is not needed).
* III.1.7 for any isotropic `φ : M → V` and `B ∈ ⋀² M` (`sa_J`, `sa_exp_J_mem_spinGroup`,
  `sa_rho_exp_J`): the graded commutation `x J(s) = J(ℓ_x ⌋ s) + J(α s) x` gives
  `exp(J B) x exp(-J B) = x - φ(ℓ_x ⌋ B)`, and `exp(J B)` is even with `exp(J B)* = exp(-J B)`, so
  it lies in `Spin` by Tau Ceti's description of `spinGroup` as the even unitary Clifford group.
  With `M = H*` this also gives the `B`-fields fixing `H* × 0`.
* Normal form (`sa_normal_form`): every maximal isotropic `W` is `σ_y(H* × 0)` for `y` a product of
  vectors of norm `-1` and one `exp(J B)`, `B ∈ ⋀² H`; induction on `dim W ∩ (0 × H)` (a reflection
  in `(-b*, b)`, `(0, b) ∈ W`, lowers it; for `0`, `W` is the graph of an alternating `H* → H`).
  Since `K(H* × 0) = F·1` (spinors killed by all contractions), the spinors killed by `W` form the
  line `F·(y·1)`, of parity the number of reflections, with annihilator `W`: III.1.4, III.1.5.
* Pairs (`sa_pair`): `(W₁, W₂)` complementary, `W₁` even, is `ρ(g)(H* × 0, 0 × H)` with
  `g = y · exp(J β)`, `β ∈ ⋀² H*` (`W₂` pulled back is a graph over `H`). This gives
  §3.3 Lemma 1, and reduces III.2.4 (converse) and III.1.12 to the pair `(1, [pt])`, where
  `(1, [pt])_S = 1` and `ker m_{α + β[pt]} = 0` for `α, β ≠ 0`, `n > 1` (degrees `1 ≠ 2n - 1`,
  separated by the number operator). III.2.4 (first half): `(u₁, u₂)_S = ((m_v m_w + m_w m_v) u₁, u₂)_S`
  `= 0` for `v ∈ ker m_{u₁} ∩ ker m_{u₂}`, `(v, w)_V = 1`.
* III.3.1: `y · s[pt_X̂] = (m_y s)[pt_X̂]` (the left ideal `C(V)[pt_X̂]` is the spin representation)
  and its reverse give `φ(g s ⊗ g t) = g φ(s ⊗ t) g*` and make `im φ` a two-sided ideal containing
  `[pt_X̂] ≠ 0`; `C(V)` is simple (Tau Ceti, `SpinPolarizationData.isSimpleRing_cliffordAlgebra` for
  the hyperbolic polarization), so `φ` is onto, and bijective by `dim = 2^{4n}`.
* III.3.2 and III.4.5: `φ(u ⊗ u) = c² g [pt_X̂] g*` is a nonzero product `w₁ ⋯ w_{2n}` of a basis of
  `W = ker m_u`; these products form an alternating map on `W` (`sa_topMap`), so they span a line and
  transform by `det`: `c² φ(u ⊗ u) = g φ(u ⊗ u) g* = det(ρ(g)|_W) φ(u ⊗ u)`.

Imports: `Sec3.lean` imports `Sec2_1.lean` and `Sec2_4.lean` (helpers); `Sec2_2.lean` imports
`Sec3.lean`. None of these files imports `Sec2_3.lean` or `WeilClasses.External.Trautman`. Public
helpers are prefixed `sa_` (the structure `sa_Inter` of intertwiners, `sa_J`, `sa_kill`, `sa_W0`,
`sa_W0'`, `sa_topMap`, …); the helpers of `Sec2_2.lean` are private.
