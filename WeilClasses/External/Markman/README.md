# Markman, *The monodromy of generalized Kummer varieties ...* (2023)

[M2] E. Markman, *The monodromy of generalized Kummer varieties and algebraic cycles on their
intermediate Jacobians*, J. Eur. Math. Soc. (JEMS) 25 (2023), no. 1, 231–321 (arXiv:1805.11574;
the paper's reference `markman-generalized-kummers`). The model: `S = H*(X) = ⋀•H¹(X)`,
`S⁺ = H^{ev}(X)` (`Splus`), the pairing `(x, y)_S = ∫_X τ(x) y` (`mukai`); for an abelian surface
this is minus the Mukai pairing, which is the pairing [M2] puts on `S⁺`. A `K`-secant (`KSecant`)
is a pure spinor `u₁ ∈ S⁺_K`, `K = ℚ(√-d)`, independent of its conjugate `u₂ = σ(u₁)`; its rational
plane `Pℚ` is the set of rational points of `span_K{u₁, u₂}`.

The paper's other citations of [M2] (in §1; in §6: Theorem 1.5 = 13.4 there in §6.2, the proof of
Prop. 11.2 and (12.5) in the proof of Lemma 6.2.5; and in later sections) are not stated here.

## `Sec8_2.lean`: Proposition 1.7 (prover P12; module RF2)

Used in Example 8.2.2 (TeX lines 3773–3775: "Then `span_ℚ{w, h}` is a secant to the spinor variety
inducing complex multiplication by the imaginary quadratic number field `ℚ(√-d)`, where
`d = (w, w)(h, h)/4`, by [M2, Prop. 1.7]"; `example8_2_2` in `WeilClasses.Secant.Sec8_2`). Proved;
not a hypothesis.

* `markmanM2_prop1_7`: for `w, h ∈ S⁺_ℚ` (`n = 2`) with `(w, w)_S < 0`, `(h, h)_S < 0` and
  `(w, h)_S = 0`, there is a `K`-secant with `K = ℚ(√-d)`, `d = (w, w)_S (h, h)_S / 4`, whose
  rational plane is `span_ℚ{w, h}`.

The statement in [M2] (Prop. 1.7 = Prop. 12.6 and Cor. 12.9 there): `X` an abelian surface,
`w ∈ S⁺ = H^{ev}(X, ℤ)` the Chern character of the ideal sheaf of a subscheme of length `n + 1`,
`h ∈ S⁺` with `(h, w) = 0` and `(h, h) < 0`, `d = (w, w)(h, h)/4`: the universal torus over the
periods orthogonal to `w` and `h` is a complete family of polarized abelian fourfolds of Weil type of
discriminant `1` with complex multiplication by `ℚ(√-d)` (the complex multiplication is `m_w m_h`,
whose square on `V` is `-d`). **Special case used**: only its cohomological core, that the line
`ℙ(span{w, h})` meets the spinor variety in two conjugate points defined over `ℚ(√-d)`, i.e. that
`span{w, h}` is a `ℚ(√-d)`-secant; and for any rational `w` with `(w, w)_S < 0` (Example 8.2.2 takes
`w = ch(F)`), not only `ch(I_Z)`. The family of abelian fourfolds is not used.

Proof. For `n = 2` the even pure spinors are exactly the non-zero isotropic vectors of `S⁺`
(`s8_isEvenPureSpinor_two`): an isotropic `u = a + ω + b[pt]` with `a ≠ 0` is `a exp(ω/a)`
(`(u, u)_S = 2ab - ∫ω²`, `s8_eq_smul_exp_two`), and `exp(ω/a) = m_{exp(jω/a)}(1)` has a
`4`-dimensional annihilator (`s8_finrank_ann_exp`); if `a = 0` and `ω ≠ 0`, an Eichler transvection
`s ↦ s + D_{y'} D_y s` in `Spin(V)` (`s8_exists_spin_DD`) preserves the pairing (`s8_mukai_DD`, by
[Chevalley, III.2.2]: `D_z` is self-adjoint) and makes the degree-`0` part non-zero; if
`a = ω = 0`, then `u = b[pt]` and `ker m_{[pt]} = 0 × H¹(X)` (`s8_ann_pt_eq`). Then
`u₁ = w + c h`, `c = 2√-d/(h, h)_S`, is isotropic (`(u₁, u₁)_S = (w, w)_S + c² (h, h)_S = 0`), hence
pure; `u₂ = σ(u₁) = w - c h` is independent of `u₁` because `w` and `h` are (their Gram matrix is
`diag((w, w)_S, (h, h)_S)`, and independence over `ℚ` passes to `K` by real and imaginary parts,
`s8_bcS_pair_indep`); and the rational points of `span_K{u₁, u₂} = span_K{w, h}` are
`span_ℚ{w, h}`. The proof uses no result of the paper, only helpers of `WeilClasses.Secant.Defs` and
`WeilClasses.Secant.Sec8_1` and [Chevalley, III.2.2] (`chevalley_III_2_2`,
`WeilClasses.External.Chevalley.Sec2_1`). The argument is P12's, written for Example 8.2.2, which
cites this statement.

Public helpers (prefix `s8_`, P12's): `s8_Q_of_mem_ann`, `s8_ann_smul`, `s8_ann_one_eq`,
`s8_finrank_ann_one`, `s8_finrank_ann_m`, `s8_finrank_ann_exp`, `s8_ι_mul_pt`, `s8_eq_zero_of_D_pt`,
`s8_ann_pt_eq`, `s8_finrank_ann_pt`, `s8_mem_Splus_of_mem`, `s8_proj_odd_eq_zero`,
`s8_proj_zero_eq`, `s8_proj_top_eq`, `s8_m_ι_inl`, `s8_exists_spin_DD`, `s8_mukai_DD`,
`s8_exists_DD_ne_zero`, `s8_tau_pt_two`, `s8_Splus_two`, `s8_mukai_two`, `s8_exp_two`,
`s8_eq_smul_exp_two`, `s8_finrank_ann_two`, `s8_isEvenPureSpinor_two` (for `n = 2` the pure spinors
in `S⁺` are its non-zero isotropic vectors), `s8_bcS_tau` (also used in
`WeilClasses.Secant.Sec8_3`), `s8_mukai_bcS`, `s8_bcS_Splus`, `s8_σ_sqrtNeg`, `s8_σ_algebraMap`,
`s8_σS_bcS_add_smul`, `s8_bcS_pair_indep`.
