import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def RatDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ q : D.host.E, incA D q * cA D (incA D q) = 1 →
    ∃ γ ∈ GQ V, (mt V γ).det = incA D q

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_mul' (V : HSp D) (g g' : GA D V) :
    L2.Theta.mt V (g * g') = L2.Theta.mt V g * L2.Theta.mt V g' := by
  simp [L2.Theta.mt, map_mul]

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

theorem cM_mul' {n : ℕ} (x y : Matrix (Fin n) (Fin n) (AE D)) : cM (x * y) = cM x * cM y := by
  simp [cM, Matrix.map_mul]

theorem actHom_mul' (V W : HSp D) (g g' : GA D V) (h h' : GA D W) (w : WA V W) :
    actHom V W g h (actHom V W g' h' w) = actHom V W (g * g') (h * h') w := by
  unfold actHom
  split_ifs with hr
  · rw [mt_mul', mt_mul', cM_mul', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  · rw [mt_mul', mt_mul', cM_mul', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

theorem actHom_one' (V W : HSp D) (w : WA V W) : actHom V W 1 1 w = w := by
  unfold actHom
  split_ifs <;> simp [mt_one', cM]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

theorem scalar_step (hS : SvNSchur ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω)
    (hω' : IsWeilDatum ψ V W χ χ' ω') (p : GA D V × GA D W) : ∃ c : ℂ, ‖c‖ = 1 ∧ ω' p = c • ω p := by
  obtain ⟨c, hc, hT⟩ := hS (ω' p * ω p⁻¹) (by
      intro w₀ Φ Φ' hΦ
      have h1 := hω.om_heis p⁻¹.1 p⁻¹.2 w₀ Φ Φ' hΦ
      simp only [Prod.mk.eta] at h1
      have h2 := hω'.om_heis p.1 p.2 (actHom V W p⁻¹.1 p⁻¹.2 w₀) (ω p⁻¹ Φ) (ω p⁻¹ Φ') h1
      simp only [Prod.mk.eta, actHom_mul', Prod.fst_inv, Prod.snd_inv, mul_inv_cancel, actHom_one'] at h2
      simpa [Module.End.mul_apply] using h2)
    (by
      intro μ 𝓕 hμ h𝓕 Φ
      simp only [Module.End.mul_apply]
      rw [hω'.om_unit μ 𝓕 hμ h𝓕 p (ω p⁻¹ Φ), hω.om_unit μ 𝓕 hμ h𝓕 p⁻¹ Φ])
  refine ⟨c, hc, ?_⟩
  have e1 : ω' p = (ω' p * ω p⁻¹) * ω p := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [e1]
  ext Φ : 1
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  exact hT (ω p Φ)

theorem omega_inv_apply (p : GA D V × GA D W) (Φ : Hth ψ V W) : ω p (ω p⁻¹ Φ) = Φ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem scalar_unique (hΘ : ThetaNZ ψ V W) (p : GA D V × GA D W) (c c' : ℂ)
    (h : c • ω p = c' • ω p) : c = c' := by
  obtain ⟨Φ, hΦ⟩ := hΘ
  have := congrArg (fun T : Module.End ℂ (Hth ψ V W) => ((T (ω p⁻¹ Φ) : Hth ψ V W) : WA V W → ℂ) 0) h
  simp only [LinearMap.smul_apply, omega_inv_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hΦ this



theorem scalar_mul (hΘ : ThetaNZ ψ V W) (c : GA D V × GA D W → ℂ) (hc : ∀ p, ω' p = c p • ω p)
    (p q : GA D V × GA D W) : c (p * q) = c p * c q := by
  apply scalar_unique ψ V W ω hΘ (p * q)
  rw [← hc, map_mul, map_mul, hc p, hc q, smul_mul_smul_comm]

theorem scalar_split (hF : SplitFormsNZ ψ V W) (hω : IsWeilDatum ψ V W χ χ' ω) (hω' : IsWeilDatum ψ V W χ χ' ω')
    (e : AE D) (he : IsSplitIdem D e) (g : GA D V) (h : GA D W) (hg : SuppAt e V g) (hh : SuppAt e W h)
    (x y : (AE D)ˣ) (hx : IsDetAt e V g x) (hy : IsDetAt e W h y) (c : ℂ) (hc1 : ‖c‖ = 1)
    (hc : ω' (g, h) = c • ω (g, h)) : c = 1 := by
  obtain ⟨ℓ, hinv, Φ, hΦ⟩ := hF e he
  obtain ⟨r, hr, hr1⟩ := hω.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', hr1'⟩ := hω'.om_split e he g h hg hh x y hx hy
  have a1 := hr1 ℓ hinv Φ
  have a2 := hr1' ℓ hinv Φ
  rw [hc, LinearMap.smul_apply, map_smul, smul_eq_mul, a1] at a2
  have hs : ((splitFac V W χ χ' x y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : c * (r : ℂ) = (r' : ℂ) := by
    have hne : ((splitFac V W χ χ' x y : Circle) : ℂ) * ℓ Φ ≠ 0 := mul_ne_zero hs hΦ
    apply mul_right_cancel₀ hne
    linear_combination a2
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc' : c = ((r' / r : ℝ) : ℂ) := by
    push_cast; rw [← key]; field_simp
  rw [hc'] at hc1 ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr' hr)] at hc1
  rw [hc1]; simp

end Scalar

section Side

def toCircle {G : Type*} [Group G] (f : G → ℂ) (hf1 : ∀ g, ‖f g‖ = 1) (h1 : f 1 = 1)
    (hmul : ∀ g g', f (g * g') = f g * f g') : G →* Circle where
  toFun g := (⟨f g, by simp [Submonoid.unitSphere, hf1 g]⟩ : Submonoid.unitSphere ℂ)
  map_one' := Subtype.ext h1
  map_mul' g g' := Subtype.ext (hmul g g')

def detU (hD : DeterminantInUnitaryOne) (V : HSp D) (g : GA D V) : FirstPropositionFrame D :=
  ⟨Units.mkOfMulEqOne _ _ (hD D V g), hD D V g⟩


end Side


end Formalism.IndefR.flipTwoThree

end
