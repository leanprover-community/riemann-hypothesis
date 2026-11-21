import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrModel

theorem exists_model : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  intro D V μ _ _
  refine ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), RG V μ, LinearIsometryEquiv.refl ℂ _, ?_, ?_, fun g F => rfl, fun F ψ => Iff.rfl⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ,
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ _ inferInstance
        (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ)).ne⟩
  · exact ⟨fun g F => GlobalTheory.AutomorphicL2Unitary.lift_R g F, fun g F => GlobalTheory.AutomorphicL2Unitary.norm_R g F,
      fun F => (isUnitaryRep_RG (V := V) (μ := μ)).continuous_apply F⟩

end GlobalTheory.TrModel
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_L2AdelicQuotient_model_equivalence : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  atlas_forward_decl GlobalTheory.TrModel.exists_model
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.CuspRep

theorem isCuspFun_of_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  intro D V μ _ _ F hF ψ hψc hψl hFψ
  refine (GlobalTheory.Cusp.isCuspFun_iff hψl).2 fun W hW => ?_
  have hc := GlobalTheory.Cusp.cocompact_single (D := D) hW
  have := hc.isProbabilityMeasure
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have h1 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) =ᵐ[μ] 0 := by
    refine GlobalTheory.CuspAE.constTermOn_ae_eq_zero hc (closure_mono ?_ hF)
    rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, (GlobalTheory.Cusp.isCuspFun_iff hφ.2.1).1 hφ.2.2 W hW, e⟩
  have hcont := hc.continuous_constTermOn hψl hψc
  have h2 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) ψ =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hcont.locallyIntegrable fun S hS => ?_
    rw [GlobalTheory.CuspAE.setIntegral_constTermOn hc hψl hψc.stronglyMeasurable hψc.locallyIntegrable hS]
    calc _ = ∫ q, ∫ y in S, lift (GQ V) F (((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V) * y) ∂μ
            ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA (.single hW)) :=
          integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae
            ((measurePreserving_mul_left μ ((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V)).quasiMeasurePreserving.ae
              hFψ.symm)))
      _ = ∫ y in S, GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) y ∂μ :=
          (GlobalTheory.CuspAE.setIntegral_constTermOn hc (leftInv_lift F) hm (GlobalTheory.CuspAE.locallyIntegrable_lift F) hS).symm
      _ = 0 := by rw [integral_congr_ae (ae_restrict_of_ae h1)]; simp
  exact (hcont.ae_eq_iff_eq μ continuous_const).1 h2

end GlobalTheory.CuspRep
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_continuous_representative : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  atlas_forward_decl GlobalTheory.CuspRep.isCuspFun_of_mem_L2cusp
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open GlobalTheory.HolDict GlobalTheory.BackForm
open scoped Classical

namespace GlobalTheory.CuspRepr

set_option maxHeartbeats 4000000 in

theorem exists_allMaps : ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ), ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → (∀ k ∈ K, ∀ y, RG V μ (k : GA D V) (Φ y) = Φ y) → ∃ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro D θ hθ V S M μ _ _ Φ hΦ K hK hKfix
  obtain ⟨𝓕, ρ, e, hp, hρ, he, hrep⟩ := GlobalTheory.T.exists_L2AdelicQuotient_model_equivalence D V μ
  obtain ⟨hcusp, hequiv⟩ := (GlobalTheory.AutMult.mem_homDS hθ).1 hΦ
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), ∀ y, Φ' y = e (Φ y) :=
    ⟨(e.toContinuousLinearEquiv : DividedPowerChartLift V μ →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕)).compContinuousMultilinearMap Φ, fun _ => rfl⟩
  have e2 : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ' (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ' y) := by
    intro τ g hg y
    rw [hΦ', hΦ', hequiv τ g hg y, he]
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  let U : Subgroup (GA D V) := K.comap (GlobalTheory.AutMult.toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hK.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ' y) = Φ' y := by
    intro y k hk hk'
    have h1 : (⟨k, hk'⟩ : GfC V) ∈ K := by
      have h2 : GlobalTheory.AutMult.toFin V k ∈ K := hk
      rwa [show GlobalTheory.AutMult.toFin V k = ⟨k, hk'⟩ from GlobalTheory.AutMult.toFin_coe (⟨k, hk'⟩ : GfC V)] at h2
    rw [hΦ', ← he]
    exact congrArg e (hKfix _ h1 y)
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ' e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ' fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  have p1' : ∀ y : M.Vec, Repr V μ 𝓕 (e (Φ fun τ => (y τ : M.H τ))) (ψ y) := fun y => hΦ' _ ▸ p1 y
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ' fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ'.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ'.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  have hEq : GlobalTheory.RepSmooth.IsEquiv θ T := by
    intro τ g hg y z hz
    refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  have hSob : GlobalTheory.RepSmooth.IsSob T := by
    intro τ y x
    obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ' T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this
  have hmult : IsMultMap θ M ∅ (fun _ => 1) T := by
    refine ⟨fun y => ⟨p2 y, p3 y, GlobalTheory.RepSmooth.zfin hEq hSob y, N, fun l hl x => ?_⟩, fun y => ?_,
      fun y k hk => hk.elim, hEq, hSob⟩
    · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
      obtain ⟨C, hC⟩ := hgr x
      refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ' fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
      rw [hy', mul_right_comm]
      exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
    · exact GlobalTheory.T.cuspidal_of_continuous_representative D V μ _ (hcusp _) (ψ y) (p2 y).cont (p2 y).left ((hrep _ _).1 (p1' y))
  exact ⟨T, Submodule.subset_span hmult, fun v => (hrep _ _).1 (p1' v)⟩

end GlobalTheory.CuspRepr
end
end
