module

public import WeilClasses.Spinor.BaseChange
public import WeilClasses.Spinor.Integral
public import WeilClasses.Basic.Field

/-!
# Pure spinors and rational `K`-secant lines (paper §2.2)

* A subspace `W ⊆ V_F` is *maximal isotropic* if `Q` vanishes on it and `dim W = 2n`
  (half of `dim V = 4n`).
* An element `w ∈ S⁺_F` is an *even pure spinor* if the kernel of `m_w : V_F → S_F` is maximal
  isotropic ([Chevalley, III.1.4]); similarly for odd pure spinors.
* A *rational `K`-secant* (`WeilClasses.KSecant`) is given by an even pure spinor `u₁ ∈ S⁺_K` whose
  Galois conjugate `u₂ = σ(u₁)` spans a different line. The lines `ℓ̃ᵢ = K uᵢ` span the plane `P_K`,
  which is defined over `ℚ`; its rational points form the plane `P ⊆ S⁺_ℚ`. The choice of `u₁`
  among the two is the orientation of `P`. The maximal isotropic subspaces are `Wᵢ = ker m_{uᵢ}`.
* The stabilizers `Spin(V_K)_{ℓᵢ}`, `Spin(V_K)_{ℓ₁,ℓ₂}` (2.2.1), `Spin(V_K)_P`, `Spin(V_ℚ)_P` (2.2.2),
  the characters `detᵢ` and `χᵢ` (the action on `ℓ̃ᵢ`), the similarity group `Õ(V_ℚ)` (2.2.3) and
  the action `η : K^× → GL(V_ℚ)` (2.2.4).
* The restriction maps of [Igusa, Lemma 1], over any field `F` of characteristic zero:
  `annRestrict F n u : Spin(V_F)_{[u]} → End(ker m_u)` and
  `pairRestrict F n u₁ u₂ : Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`, `g ↦ ρ(g)|_{W₁}`,
  and `specialLinearUnits F W = SL(W) ⊆ GL(W)`. They are used both by the statements of record
  `WeilClasses.igusa_lemma1_*` (`WeilClasses.External.Igusa.Sec2_2`) and by §2.2
  (`WeilClasses.PureSpinor.Stabilizer`, which cites those statements).
-/

@[expose] public section

namespace WeilClasses

open CliffordAlgebra

section General

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- `W ⊆ V_F` is a maximal isotropic subspace: `Q` vanishes on `W` and `dim W = 2n`. -/
def IsMaxIsotropic (W : Submodule F (V F n)) : Prop :=
  (∀ v ∈ W, Q F n v = 0) ∧ Module.finrank F W = 2 * n

/-- The annihilator `ker (m_s : V_F → S_F)` of a spinor `s`. -/
noncomputable def ann (s : S F n) : Submodule F (V F n) := LinearMap.ker (mOf F n s)

/-- An even pure spinor: `w ∈ S⁺` with `ker m_w` maximal isotropic (§2.2). -/
def IsEvenPureSpinor (w : S F n) : Prop := w ∈ Splus F n ∧ IsMaxIsotropic F n (ann F n w)

/-- An odd pure spinor: `w ∈ S⁻` with `ker m_w` maximal isotropic (§2.2). -/
def IsOddPureSpinor (w : S F n) : Prop := w ∈ Sminus F n ∧ IsMaxIsotropic F n (ann F n w)

omit [CharZero F] in
/-- `m(g⁻¹) ∘ m(g) = id` for `g ∈ Spin(V_F)`. -/
theorem fnd_m_inv_m (g : Spin F n) (s : S F n) :
    m F n ((g⁻¹ : Spin F n) : C F n) (m F n (g : C F n) s) = s := by
  rw [← Module.End.mul_apply, ← map_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    map_one, Module.End.one_apply]

/-- The stabilizer in `Spin(V_F)` of the line spanned by a spinor `u`. -/
def lineStabilizer (u : S F n) : Subgroup (Spin F n) where
  carrier := {g | ∃ c : F, m F n (g : C F n) u = c • u}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm b a]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have key := fnd_m_inv_m F n g u
    by_cases ha0 : a = 0
    · rw [ha, ha0, zero_smul, map_zero] at key
      rw [← key, map_zero, smul_zero]
    · rw [ha, map_smul] at key
      exact (eq_inv_smul_iff₀ ha0).mpr key

/-- The subgroup of `Spin(V_F)` fixing every vector of a subspace `P ⊆ S_F`. -/
def fixingSpin (P : Submodule F (S F n)) : Subgroup (Spin F n) where
  carrier := {g | ∀ p ∈ P, m F n (g : C F n) p = p}
  one_mem' := by intro p _; simp
  mul_mem' := by
    rintro g h hg hh p hp
    rw [Submonoid.coe_mul, map_mul, Module.End.mul_apply, hh p hp, hg p hp]
  inv_mem' := by
    rintro g hg p hp
    conv_lhs => rw [← hg p hp]
    exact fnd_m_inv_m F n g p

/-- The stabilizer of the line `[u]` preserves `ker m_u`: if `m_v u = 0` and `g⁻¹ u = c u`, then
`m_{ρ(g) v} u = m_g m_v m_{g⁻¹} u = c m_g m_v u = 0`. -/
theorem rho_mem_ann_of_mem_lineStabilizer (u : S F n) (g : Spin F n)
    (hg : g ∈ lineStabilizer F n u) (v : V F n) (hv : v ∈ ann F n u) :
    rho F n g v ∈ ann F n u := by
  obtain ⟨c, hc⟩ := (lineStabilizer F n u).inv_mem hg
  simp only [ann, LinearMap.mem_ker, mOf, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply] at hv ⊢
  rw [ι_rho, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hs : star (g : C F n) = ((g⁻¹ : Spin F n) : C F n) := rfl
  rw [hs, hc, map_smul, hv, smul_zero, map_zero]

/-- The action `Spin(V_F)_{[u]} → End(ker m_u)` of the stabilizer of the line `[u]` on the isotropic
subspace `W = ker m_u`, by restriction of `ρ`. -/
noncomputable def annRestrict (u : S F n) : lineStabilizer F n u →* Module.End F (ann F n u) where
  toFun g := (rho F n (g : Spin F n)).toLinearMap.restrict
    (rho_mem_ann_of_mem_lineStabilizer F n u g g.2)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, OneMemClass.coe_one, LinearEquiv.coe_coe, rho,
      spinVectorAction_one, LinearEquiv.refl_apply, Module.End.one_apply]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Subgroup.coe_mul, LinearEquiv.coe_coe, rho,
      spinVectorAction_mul, LinearEquiv.mul_apply, Module.End.mul_apply]

/-- The homomorphism `Spin(V_F)_{[u₁]} ∩ Spin(V_F)_{[u₂]} → GL(ker m_{u₁})`, `g ↦ ρ(g)|_{W₁}`. -/
noncomputable def pairRestrict (u₁ u₂ : S F n) :
    (lineStabilizer F n u₁ ⊓ lineStabilizer F n u₂ : Subgroup (Spin F n)) →*
      (Module.End F (ann F n u₁))ˣ :=
  ((annRestrict F n u₁).comp (Subgroup.inclusion inf_le_left)).toHomUnits

/-- `SL(W)`: the automorphisms of determinant one, as a subgroup of `GL(W) = (End W)ˣ`. -/
noncomputable def specialLinearUnits (W : Type*) [AddCommGroup W] [Module F W] :
    Subgroup (Module.End F W)ˣ :=
  (Units.map (LinearMap.det : Module.End F W →* F)).ker

end General

/-! ## Rational `K`-secants -/

variable (n : ℕ) (d : ℚ)

/-- The Galois involution `σ` acting on `S_K` (on the coefficients of the basis `e_K`). -/
noncomputable abbrev σS : S (Kd d) n →+* S (Kd d) n := conjS (Kd.σ d) n

/-- The Galois involution `σ` acting on `V_K`. -/
noncomputable abbrev σV : V (Kd d) n →+ V (Kd d) n := conjV (Kd.σ d) n

/-- **A rational `K`-secant line** to the even spinor variety (§2.2): an even pure spinor
`u₁ ∈ S⁺_K` such that the lines `ℓ̃₁ = K u₁` and `ℓ̃₂ = K u₂`, `u₂ = σ(u₁)`, are distinct. The choice
of `u₁` (rather than `u₂`) is the orientation of the secant. -/
structure KSecant where
  /-- A pure spinor spanning `ℓ̃₁`. -/
  u₁ : S (Kd d) n
  isPure : IsEvenPureSpinor (Kd d) n u₁
  /-- `ℓ₁ ≠ ℓ₂`. -/
  linIndep : LinearIndependent (Kd d) ![u₁, σS n d u₁]

namespace KSecant

variable {n d} (P : KSecant n d)

/-- The conjugate pure spinor `u₂ = σ(u₁)`, spanning `ℓ̃₂`. -/
noncomputable def u₂ : S (Kd d) n := σS n d P.u₁

/-- The maximal isotropic subspace `W₁ = ker m_{u₁} ⊆ V_K` corresponding to `ℓ₁`. -/
noncomputable def W₁ : Submodule (Kd d) (V (Kd d) n) := ann (Kd d) n P.u₁

/-- The maximal isotropic subspace `W₂ = ker m_{u₂} ⊆ V_K` corresponding to `ℓ₂`. -/
noncomputable def W₂ : Submodule (Kd d) (V (Kd d) n) := ann (Kd d) n P.u₂

/-- The plane `P_K = ℓ̃₁ ⊕ ℓ̃₂ ⊆ S⁺_K`. -/
noncomputable def PK : Submodule (Kd d) (S (Kd d) n) := Submodule.span (Kd d) {P.u₁, P.u₂}

/-- The rational plane `P ⊆ S⁺_ℚ`: the rational points of `P_K`. -/
noncomputable def Pℚ : Submodule ℚ (S ℚ n) :=
  (P.PK.restrictScalars ℚ).comap (bcS ℚ (Kd d) n).toLinearMap

/-- `P` is isotropic for the Mukai pairing (1.2.3). -/
def IsIsotropic : Prop := ∀ a ∈ P.Pℚ, ∀ b ∈ P.Pℚ, mukai ℚ n a b = 0

/-- The stabilizer `Spin(V_K)_{ℓ₁,ℓ₂} = Spin(V_K)_{ℓ₁} ∩ Spin(V_K)_{ℓ₂}` (2.2.1). -/
noncomputable def spinL₁L₂ : Subgroup (Spin (Kd d) n) :=
  lineStabilizer (Kd d) n P.u₁ ⊓ lineStabilizer (Kd d) n P.u₂

/-- `Spin(V_K)_P`: the elements of `Spin(V_K)` fixing every vector of `P_K` (2.2.2). -/
noncomputable def spinPK : Subgroup (Spin (Kd d) n) := fixingSpin (Kd d) n P.PK

/-- `Spin(V_ℚ)_P`: the elements of `Spin(V_ℚ)` fixing every vector of `P` (2.2.2). -/
noncomputable def spinPℚ : Subgroup (Spin ℚ n) := fixingSpin ℚ n P.Pℚ

theorem rho_mem_W₁ (g : P.spinL₁L₂) (v : V (Kd d) n) (hv : v ∈ P.W₁) :
    rho (Kd d) n g v ∈ P.W₁ :=
  rho_mem_ann_of_mem_lineStabilizer (Kd d) n P.u₁ (g : Spin (Kd d) n)
    (Subgroup.mem_inf.mp g.2).1 v hv

theorem rho_mem_W₂ (g : P.spinL₁L₂) (v : V (Kd d) n) (hv : v ∈ P.W₂) :
    rho (Kd d) n g v ∈ P.W₂ :=
  rho_mem_ann_of_mem_lineStabilizer (Kd d) n P.u₂ (g : Spin (Kd d) n)
    (Subgroup.mem_inf.mp g.2).2 v hv

/-- The character `det₁ : Spin(V_K)_{ℓ₁,ℓ₂} → K^×`, the determinant of the action on `W₁`. -/
noncomputable def det₁ (g : P.spinL₁L₂) : Kd d :=
  LinearMap.det ((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
    (fun v hv => P.rho_mem_W₁ g v hv))

/-- The character `det₂ : Spin(V_K)_{ℓ₁,ℓ₂} → K^×`, the determinant of the action on `W₂`. -/
noncomputable def det₂ (g : P.spinL₁L₂) : Kd d :=
  LinearMap.det ((rho (Kd d) n g : V (Kd d) n →ₗ[Kd d] V (Kd d) n).restrict
    (fun v hv => P.rho_mem_W₂ g v hv))

/-- The character `χ₁` by which `Spin(V_K)_{ℓ₁,ℓ₂}` acts on the line `ℓ̃₁ = K u₁`. -/
noncomputable def χ₁ (g : P.spinL₁L₂) : Kd d := Classical.choose ((Subgroup.mem_inf.mp g.2).1)

/-- The character `χ₂` by which `Spin(V_K)_{ℓ₁,ℓ₂}` acts on the line `ℓ̃₂ = K u₂`. -/
noncomputable def χ₂ (g : P.spinL₁L₂) : Kd d := Classical.choose ((Subgroup.mem_inf.mp g.2).2)

/-- `W_{1,ℂ} ⊆ V_ℂ`: the complex span of `W₁ ⊆ V_K`. -/
noncomputable def W₁ℂ : Submodule ℂ (V ℂ n) := Submodule.span ℂ (bcV (Kd d) ℂ n '' P.W₁)

/-- `W_{2,ℂ} ⊆ V_ℂ`: the complex span of `W₂ ⊆ V_K`. -/
noncomputable def W₂ℂ : Submodule ℂ (V ℂ n) := Submodule.span ℂ (bcV (Kd d) ℂ n '' P.W₂)

/-- The real span `P_ℝ ⊆ S⁺_ℝ` of the rational plane `P`. -/
noncomputable def PR : Submodule ℝ (S ℝ n) := Submodule.span ℝ (bcS ℚ ℝ n '' P.Pℚ)

/-- **`Spin(V_ℝ)_P`**: the subgroup of `Spin(V_ℝ)` leaving every vector of `P` (equivalently of
`P_ℝ`) invariant (§3.2, §4). -/
noncomputable def spinPR : Subgroup (Spin ℝ n) := fixingSpin ℝ n P.PR

/-- The integral group `Spin(V)_P` of (2.2.2): the elements of the integral spin group `Spin(V)`
(`SpinZ n`) leaving every vector of `P` invariant. -/
noncomputable def spinPZ : Subgroup (Spin ℚ n) := SpinZ n ⊓ P.spinPℚ

end KSecant

end WeilClasses
