import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

section
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
end

section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

variable {D : D7}

abbrev sigE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sigE_sigE (a : D.host.E) : sigE D (sigE D a) = a := star_star a

theorem gram_herm (V : HSp D) (i j : Fin V.rank) : sigE D (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem cA_incA' (a : D.host.E) : cA D (incA D a) = incA D (sigE D a) := by
  simp [cA, incA, sigR, inclR]

theorem gramA_herm (V : HSp D) (i j : Fin V.rank) :
    cA D (V.gram.map (incA D) i j) = V.gram.map (incA D) j i := by
  simp only [Matrix.map_apply, cA_incA', gram_herm]

def mkGA (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) : GA D V :=
  let g : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨Matrix.nonsingInvUnit M hd, hM⟩
  g

theorem aniso_data (V : HSp D) (hn : 0 < V.rank) :
    ∃ (u : Fin V.rank → D.host.E) (ainv : D.host.E), ainv * hsq (sigE D) V.gram u = 1 ∧ sigE D ainv = ainv := by
  have : Nonempty (Fin V.rank) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := exists_aniso (sigE D) sigE_sigE V.gram (gram_herm V) (gram_det_ne V)
  refine ⟨u, (hsq (sigE D) V.gram u)⁻¹, inv_mul_cancel₀ hu, ?_⟩
  rw [map_inv₀, sigma_hsq (sigE D) sigE_sigE V.gram (gram_herm V) u]

theorem exists_GA_det (V : HSp D) (hn : 0 < V.rank) (x : AE D) (hx : cA D x * x = 1) (hxu : IsUnit x) :
    ∃ (R : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (g : GA D V), mt V g = 1 + (x - 1) • R ∧ (mt V g).det = x := by
  obtain ⟨u, ainv, ha, hainv⟩ := aniso_data V hn
  have haA : incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
    rw [← hsq_map (incA D) (sigE D) (cA D) (fun a => (cA_incA' a).symm), ← map_mul, ha, map_one]
  have hainvA : cA D (incA D ainv) = incA D ainv := by rw [cA_incA', hainv]
  set R := proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)
  have hM := proj_unitary (cA D) cA_cA (V.gram.map (incA D)) (gramA_herm V) (fun i => incA D (u i))
    (incA D ainv) haA hainvA x hx
  have hdet := det_proj' (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv) haA x
  exact ⟨R, mkGA V _ hM (by rw [hdet]; exact hxu), rfl, hdet⟩

theorem splitDet : SplitDetP := by
  intro D V hn e he x hx hsupp
  obtain ⟨R, g, hg, hdet⟩ := exists_GA_det V hn (x : AE D) (by rw [mul_comm]; exact hx) x.isUnit
  refine ⟨g, ?_, ?_, hdet⟩
  · intro i j
    rw [hg, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    unfold SuppAtU at hsupp
    rw [hsupp]
  · have hxi : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := x.mul_inv
    set xi : AE D := ((x⁻¹ : (AE D)ˣ) : AE D) with hxi_def
    set x0 : AE D := (x : AE D) with hx0
    have p1 : (e * x0 + (1 - e)) * (e * xi + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    have p2 : (e * xi + (1 - e)) * (e * x0 + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    obtain ⟨y, hy⟩ : ∃ y : (AE D)ˣ, (y : AE D) = e * x0 + (1 - e) := ⟨⟨_, _, p1, p2⟩, rfl⟩
    refine ⟨y, ?_⟩
    unfold IsDetAt
    rw [hy, hdet]

end Formalism.IndefR.flipTwoThree

end
end
