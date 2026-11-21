import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralUnfoldingDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralUnfoldingDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecondStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefLiftSmooth
theorem deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hω hθ hΦ hS _ hν h𝓕 hφ k τs Xs hX h
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  set κ := GlobalTheory.Mem.Lift.thKer ψ S T om with hκ
  let L : GlobalTheory.RealWeil.thetaSub ψ S T → GA D T → ℂ := fun f h => ∫ g in 𝓕, κ f g h * φ g ∂ν
  have hkinv : ∀ f, ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T), κ f (γ * g) h * φ (γ * g) = κ f g h * φ g := by
    intro f γ hγ g h
    have := hK.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [this, hφ.left γ hγ]
  have hcont : ∀ φ' ∈ Set.range L, Continuous φ' := by
    rintro _ ⟨f, rfl⟩
    exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun h g => κ f g h * φ g) (((hK.cont f).comp continuous_swap).mul (hφ.cont.comp continuous_snd))
      (fun γ hγ h g => hkinv f γ hγ g h)
  have hder : ∀ φ' ∈ Set.range L, ∀ τ, ∀ X ∈ lieAt T τ, ∃ φ'' ∈ Set.range L, ∀ h,
      HasDerivAt (fun t : ℝ => φ' (h * oneP θ T τ X t)) (φ'' h) 0 := by
    rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hK.derW τ X hX f
    refine ⟨L f', ⟨f', rfl⟩, fun h => ?_⟩
    have hoc := GlobalTheory.Mem.Lift.continuous_oneP (V := T) hθ hX
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t g => κ f g (h * oneP θ T τ X t) * φ g) (fun t g => κ f' g (h * oneP θ T τ X t) * φ g)
      (fun t => ((hK.cont f).comp (continuous_id.prodMk continuous_const)).mul hφ.cont)
      (((hK.cont f').comp (continuous_snd.prodMk (continuous_const.mul (hoc.comp continuous_fst)))).mul
        (hφ.cont.comp continuous_snd))
      (fun γ hγ t g => hkinv f γ hγ g _) (fun γ hγ t g => hkinv f' γ hγ g _)
      (fun t g => (GlobalTheory.Mem.Lift.hasDerivAt_oneP (φ := fun h => κ f g h) (φ' := fun h => κ f' g h) hθ hX
        (fun h => e g h) h t).mul_const (φ g)) 0
    simpa only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, L] using key
  have hsm := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T (Set.range L) hcont hder (L ⟨Φ, hΦ⟩) ⟨_, rfl⟩
  exact hsm k τs Xs hX h
end GlobalTheory.DefLiftSmooth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  first | exact @_root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | exact _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | (intros; apply _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefiniteLiftZfin
open Matrix
theorem definite_unitary_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ →
    (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
    IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧
      (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 hP hω hθ hΦ hS _ hH hF hφ
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  exact (hK.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ ⟨hφ, isCuspFun_of_posDef hS φ⟩ ⟨Φ, hΦ⟩).2.zfin
end GlobalTheory.DefiniteLiftZfin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_definite_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧ (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  first | exact @_root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | exact _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | (intros; apply _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftGrowthDef
theorem lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'
end GlobalTheory.LiftGrowthDef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  first | exact @_root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | exact _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | (intros; apply _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeilLevel
theorem weil_representation_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]
end GlobalTheory.WeilLevel
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_weil_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  first | exact @_root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | exact _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | (intros; apply _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ContDiff ComplexOrder
namespace GlobalTheory.ColLiftAut
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}
theorem thetaLift_isAutomorphicFunction (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    IsAutFun T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  refine ⟨fun γ hγ h => ?_, ?_, lift_continuous hW hΦ hS hν h𝓕 hφ⟩
  · simp only [kernel_left hW hΦ _ hγ]
  · obtain ⟨U, hU, hk⟩ := _root_.GlobalTheory.T.twist_weil_level_eq_conductor ψ S T χS χT om Φ hP hW hΦ
    refine ⟨U, hU, fun k hkU hkf h => ?_⟩
    simp only [kernel_right, hk k hkU hkf]
theorem thetaLift_isSmoothAutomorphicFunction (θ : InfFam D) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (hΦ : IsThetaFunO ψ S T Φ) (hS : ∀ τ, (gramAt D S τ).PosDef) (hT : ∀ τ, (gramAt D T τ).PosDef)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) :
    IsAutFunSm θ T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν :=
  { toIsAutFun := _root_.GlobalTheory.ColLiftAut.thetaLift_isAutomorphicFunction hP hW hΦ hS hν h𝓕 hφ.toIsAutFun
    smooth := _root_.GlobalTheory.T.twist_deformation_lift_smooth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    zfin := _root_.GlobalTheory.T.twist_definite_lift_finite_adeles ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    growth := _root_.GlobalTheory.T.twist_lift_moderate_growth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ }
end GlobalTheory.ColLiftAut
namespace GlobalTheory.ColLiftAut
theorem columnLift_isSmoothAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ φ hφ _
  have hW : IsWeilDatumO R.ψ (G.Xp j).V (G.Xp (j + 1)).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) (G.col t j).ω :=
    (hG.arrows.col t j hj).weil
  have hT : ∀ τ, (gramAt D (G.Xp (j + 1)).V τ).PosDef := posDef_of_nodeIs (hG.spaces.X j (by omega)) rfl
  have hSm : (∀ τ, (gramAt D (G.Xp j).V τ).PosDef) ∧ (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
    cases j with
    | zero =>
      exact ⟨posDef_of_nodeIs (hG.spaces.P D.R.m le_rfl) (by simp), ((hG.meas.P D.R.m le_rfl).1 rfl).1.1, ((hG.meas.P D.R.m le_rfl).1 rfl).2⟩
    | succ j' =>
      exact ⟨posDef_of_nodeIs (hG.spaces.X j' (by omega)) rfl, ((hG.meas.X j' (by omega)).1 trivial).1.1, ((hG.meas.X j' (by omega)).1 trivial).2⟩
  exact _root_.GlobalTheory.ColLiftAut.thetaLift_isSmoothAutomorphicFunction R.θ hPr hW hRB.inf hΦ hSm.1 hT hSm.2.1 hSm.2.2 hφ.1
end GlobalTheory.ColLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_isAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | exact _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | (intros; apply _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction <;> assumption)
end
end
