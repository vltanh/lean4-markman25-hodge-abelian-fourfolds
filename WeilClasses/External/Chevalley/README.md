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
