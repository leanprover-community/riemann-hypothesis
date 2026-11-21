import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryLocalPointLatticeGraphNormIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_projection_under_eq_residue_card_eq_absNorm : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal := by
  first | exact @GlobalTheory.PlaceProjAt.under_resCard | exact GlobalTheory.PlaceProjAt.under_resCard | (intros; apply GlobalTheory.PlaceProjAt.under_resCard <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_lift_residue_character_isTame_not_unramified : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  first | exact @GlobalTheory.tameLift_isTame_not_isUnram | exact GlobalTheory.tameLift_isTame_not_isUnram | (intros; apply GlobalTheory.tameLift_isTame_not_isUnram <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topological_iso_parahoric_chart_split_place : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  first | exact @GlobalTheory.ChartSplitIso.exists_equiv_emb | exact GlobalTheory.ChartSplitIso.exists_equiv_emb | (intros; apply GlobalTheory.ChartSplitIso.exists_equiv_emb <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped NNReal
namespace GlobalTheory.ChartHgt

open GlobalTheory.Doubling in

theorem hgtV_mul_stab (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {k k' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hk' : k' ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v (k * g * k') = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v g := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hI := GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) (gram_hdbl V) (isHermND_gram V)
    (isHermND_gram (dblSp V)) τ Λ (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
  congr 1
  have e1 : ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k * g * k', 1) =
      (ioDiag (R := Fv D.host.F v) (gram_hdbl V) k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig (dblSp V).gram v) *
        ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (g, 1) * ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k', k⁻¹) := by
    rw [coe_ioDiag, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  rw [e1]
  refine (HasIwasawa.hgtH_right (continuous_absEv v) (isCompact_KFin v) hI _
    ((ioH_mem_KFin (gram_hdbl V)).2 ⟨hk', inv_mem hk⟩)).trans ?_
  refine (HasIwasawa.hgtH_left (continuous_absEv v) (isCompact_KFin v) hI _ _).trans ?_
  rw [aH_ioDiag, abs_detH (absEv_conjUnit _ v) (isHermND_gram V).2, one_mul]

open ValuativeRel in

theorem nnnorm_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : (Fv F v)ˣ)
    (h : letI := GlobalTheory.LocalData.complRel v; valuation (Fv F v) (ϖ : Fv F v) = uniformizer (Fv F v)) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    ‖(ϖ : Fv F v)‖₊ = ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℕ) : ℝ≥0)⁻¹ := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
  apply GlobalTheory.norm_uniformiser_eq_inv_absNorm
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : Fv F v) < 1 := by
    rw [← he.lt_one_iff_lt_one, h]; exact uniformizer_lt_one
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have h2 : Valued.v p ≤ Valued.v (ϖ : Fv F v) := by
    rw [← he.le_iff_le, h, le_uniformizer_iff, he.lt_one_iff_lt_one, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have h0 : Valued.v (ϖ : Fv F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [hp, ← WithZero.exp_log h0, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold Formalism.UG.IsUnifV
  rw [← WithZero.exp_log h0]
  have : WithZero.log (Valued.v (ϖ : Fv F v)) = -1 := by omega
  rw [this]; rfl

theorem hgtFin_ioH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (hQ : Q = GlobalTheory.Doubling.dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (g : GlobalTheory.AdelicU.GLoc σ J v) :
    GlobalTheory.Doubling.hgtFin σ Q L v (GlobalTheory.Doubling.ioH (Fv F v) σ hQ (g, 1)) =
      GlobalTheory.Doubling.hgtFin σ (GlobalTheory.Doubling.dblGram finSumFinEquiv J) L v (GlobalTheory.Doubling.ioH (Fv F v) σ rfl (g, 1)) := by
  subst hQ; rfl

theorem min_zpow_inv (q : ℝ≥0) (hq : 1 ≤ q) (m : ℤ) : min ((q⁻¹) ^ m) (((q⁻¹) ^ m)⁻¹) = q ^ (-|m|) := by
  rw [_root_.inv_zpow', ← _root_.zpow_neg, neg_neg]
  rcases le_total 0 m with hm | hm
  · rw [abs_of_nonneg hm, min_eq_left (zpow_le_zpow_right₀ hq (by omega))]
  · rw [abs_of_nonpos hm, neg_neg, min_eq_right (zpow_le_zpow_right₀ hq (by omega))]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℝ≥0) (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem bridge : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ →
    Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v,
    (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) →
    ∃ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (β : GL (Fin s.V.rank) (Fv D.host.F v))
      (ε : Fin D.R.r ⊕ Blocks k D.R.t ≃ Fin s.V.rank), GlobalTheory.AdelicU.IsSplitBasis τ s.Λ β ∧
      ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1.submatrix ε ε = y.1 := by
  intro D s k v φ ι _ hfr ⟨ε, _, hε⟩ e he
  refine ⟨_, _, ε, GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ, fun y => ?_⟩
  have h2 := (hε y).2
  rw [he y, GlobalTheory.ChartStab.grpCo_emb] at h2
  exact h2

theorem isHgt_chart : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y) := by
  intro D s k v φ ι hΛ hβ hι e he x ϖ hϖ
  obtain ⟨τ, β, ε, hB, hy⟩ := bridge D s k v φ ι hΛ hβ hι e he
  have hΨ : ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1 =
      y.1.submatrix ε.symm ε.symm := fun y => by
    rw [← hy y, Matrix.submatrix_submatrix]; simp
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β).injective
      (Units.ext (by rw [map_mul, Units.val_mul, hΨ, hΨ, hΨ, Units.val_mul, Matrix.submatrix_mul_equiv]))
  have hK := GlobalTheory.ChartStab.chart_stab D s k v φ ι hΛ hβ hι e he
  refine ⟨fun κ hκ g => ⟨?_, ?_⟩, fun e' => ?_⟩
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ ((hK κ).2 hκ) (one_mem _) (e g)
    rwa [mul_one, ← hmul] at this
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ (one_mem _) ((hK κ).2 hκ) (e g)
    rwa [one_mul, ← hmul] at this
  · haveI := hΛ.1
    have hsd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
    obtain ⟨-, hval, -⟩ := (GlobalTheory.GraphNorm.graphNormFinite D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D)
      s.V.rank s.V.gram (GlobalTheory.Doubling.isHermND_gram s.V) s.Λ v hsd).1 τ β hB
      (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e'))
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.IsElemDiv (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D)
        (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')))
        (fun i => ϖ ^ e' (ε.symm i)) := by
      refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
      rw [hΨ, GlobalTheory.GLDoubling.val_torusElt, Matrix.submatrix_diagonal_equiv]
      simp
    have h1 := hval _ hd
    obtain ⟨-, -, -, -, hv⟩ := hϖ
    have hn := nnnorm_unif _ v ϖ hv
    have hq : 1 ≤ ((GlobalTheory.SplitWeil.resCard (Fv D.host.F v) : ℕ) : ℝ≥0) := by
      rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (fun h0 => v.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0))
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) =
        (GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt D.sp.cm.sig s.V.gram s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt
      exact congrArg _ (hgtFin_ioH_eq _ _ _ _ _ _ _)
    refine e2.trans ?_
    rw [h1]
    simp only [Units.val_zpow_eq_zpow_val, nnnorm_zpow, hn]
    simp only [min_zpow_inv _ hq]
    rw [prod_zpow_eq _ _ (zero_lt_one.trans_le hq).ne', NNReal.coe_zpow, NNReal.coe_natCast, Finset.sum_neg_distrib]
    congr 2
    exact Equiv.sum_comp ε.symm (fun a => |e' a|)

end GlobalTheory.ChartHgt
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingHeight_splitPlaceChart_biInvariant_torus_value : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y) := by
  atlas_forward_decl GlobalTheory.ChartHgt.isHgt_chart
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_chart_parahoric_eq_level : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  first | exact @GlobalTheory.chart_level_iff | exact GlobalTheory.chart_level_iff | (intros; apply GlobalTheory.chart_level_iff <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartChi

set_option maxHeartbeats 2000000 in

theorem levChi_chart : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd
  have hlev := (GlobalTheory.chart_level_iff D c w hw j hj s hs PP hPP v φ hφ ι hι y).2 hy
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hfl.selfDual hfl.frame hι
  have hv : v = PP.under (𝓞 D.host.F) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  rw [Lev.levG, Lev.mem_levA, hL] at hlev
  have hmem := hlev.2
  rw [mem_lev, mem_parLev] at hmem
  obtain ⟨⟨-, hS, -, hQ⟩, -⟩ := hmem
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : PP'.under (𝓞 D.host.F) ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [Lev.levChi, hL]
  set L := Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B with hLd
  have hLxq : L.xq = fun PP => (w.ξ PP)⁻¹ := by rw [hLd]; simp [Lev.datY]
  have hLPg : L.Pg = w.Pg := rfl
  have hLQ : L.Q = w.Q := rfl
  have hLr : L.r = D.R.r := rfl
  set x := Lev.finE s.V (ι y) with hx
  have h1 : ext1 L.P.H (⇑L.P.chi) (rTup s.β L x) = 1 := Lev.subgroupCharExtension_one_apply (LevelP.triv w.Pg D.R.r ℂ).H _
  have h2 : ∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, (L.cg (c + 1) PP) (dBlk (blkOf L.r L.t) (c + 1) (redFn s.β PP x)) = 1 := by
    refine Finset.prod_eq_one fun PP' hP' => Finset.prod_eq_one fun c' _ => ?_
    have hne : PP' ≠ PP := by
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    rw [hone PP' (hsub _ (Or.inl hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  have h3 : ∏ PP ∈ L.Q, (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) = (L.xq PP) (dBlk (blk2 L.r) 1 (redFn s.β PP x)) := by
    refine Finset.prod_eq_single PP (fun PP' hP' hne => ?_) (fun h => absurd hPP h)
    rw [hone PP' (hsub _ (Or.inr hP')) hne, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  unfold levFn
  rw [h1, h2, h3, one_mul, one_mul, hLxq]
  obtain ⟨⟨rr, -, -, hrel, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hQP : redFn s.β PP x ∈ blockTri (blk2 D.R.r) := hQ PP hPP
  obtain ⟨Y, hY⟩ := hS
  set G := (grpCo φ s.V (frCo φ s.β) (ι y)).val with hG
  have hi : intGL D.host.F D.host.E _ Y = s.β⁻¹ * x * s.β := by
    rw [← hY]
    simp [frGL, MulAut.conj_apply]
    group
  have hxm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) x =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom s.V (ι y)) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (x.val i j) = rdA φ ((Formalism.L2.Theta.matHom s.V (ι y)).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (s.β⁻¹ * x * s.β) = grpCo φ s.V (frCo φ s.β) (ι y) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hxm]
    rfl
  have key : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = G a b := by
    intro a b
    rw [hG, ← hm, ← hi]
    rfl
  have hint : ∀ a b, G a b ∈ v.adicCompletionIntegers D.host.F := fun a b => key a b ▸ (hN _ (Y.val a b).2).1
  have hred : ∀ a b, rr ⟨G a b, hint a b⟩ = (redFn s.β PP x).val a b := by
    intro a b
    obtain ⟨h, hh⟩ := hN _ (Y.val a b).2
    rw [← hY, redFn_frGL]
    have e : (⟨G a b, hint a b⟩ : v.adicCompletionIntegers D.host.F) = ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (Y.val a b : Lev.EAf D), h⟩ :=
      Subtype.ext (key a b).symm
    rw [e, hh]
    rfl
  have hT : ∀ i : Blocks j D.R.t, blk2 D.R.r (ε (.inr i)) = 1 := by
    intro i
    have := GlobalTheory.ChartLevel.eps_inr_ge ε hε i
    simp [blk2, not_lt.2 this]
  let f : Blocks j D.R.t → {a : Fin s.V.rank // blk2 D.R.r a = 1} := fun i => ⟨ε (.inr i), hT i⟩
  have hfb : Function.Bijective f := by
    constructor
    · intro i i' h
      have := congrArg Subtype.val h
      exact Sum.inr_injective (ε.injective this)
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := ε.surjective a
      rcases p with p | p
      · exfalso
        have hp : ((ε (.inl p) : Fin s.V.rank) : ℕ) < D.R.r := by rw [hε]; exact p.2
        simp [blk2, hp] at ha
      · exact ⟨p, rfl⟩
  let ef := Equiv.ofBijective f hfb
  let Gi : Matrix (Fin s.V.rank) (Fin s.V.rank) (v.adicCompletionIntegers D.host.F) := fun a b => ⟨G a b, hint a b⟩
  let A : Matrix {a : Fin s.V.rank // blk2 D.R.r a = 1} {a : Fin s.V.rank // blk2 D.R.r a = 1} (v.adicCompletionIntegers D.host.F) :=
    Gi.submatrix Subtype.val Subtype.val
  have hdA : (d : Fv D.host.F v) = ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) := by
    rw [hd]
    have e1 : ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
        (G.submatrix (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank) (Subtype.val : {a : Fin s.V.rank // blk2 D.R.r a = 1} → Fin s.V.rank)).det := by
      rw [show ((A.det : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = (v.adicCompletionIntegers D.host.F).subtype A.det from rfl,
        RingHom.map_det]
      congr 1
    rw [e1, ← Matrix.det_submatrix_equiv_self ef]
    congr 1
    refine Matrix.ext fun i i' => ?_
    have := congrFun (congrFun (hch y).2 (.inr i)) (.inr i')
    exact this.symm
  have hk : ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) = rr A.det := by
    rw [diag_block_det_val 1 hQP, RingHom.map_det]
    congr 1
    ext a b
    exact (hred a b).symm
  have hrel' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (d : Fv D.host.F v) ((dBlk (blk2 D.R.r) 1 (redFn s.β PP x) : (kP PP)ˣ) : kP PP) := by
    rw [hrel]
    refine ⟨hdA ▸ A.det.2, ?_⟩
    rw [hk]
    congr 1
    exact Subtype.ext hdA
  have hξd := hξ d _ hrel'
  show ((((w.ξ PP)⁻¹) (dBlk (blk2 D.R.r) 1 (redFn s.β PP x)) : ℂˣ) : ℂ) = _
  rw [MonoidHom.inv_apply, hξd]

end GlobalTheory.ChartChi
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_on_parahoric_chart_image : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  atlas_forward_decl GlobalTheory.ChartChi.levChi_chart
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartTwist

theorem chart_dict : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ
  have hpl := GlobalTheory.T.split_projection_under_eq_residue_card_eq_absNorm D v φ PP hφ
  refine ⟨hpl.1, hpl.2, fun ξl h => GlobalTheory.T.tame_lift_residue_character_isTame_not_unramified D v φ PP (w.ξ PP) hφ (hw.ne PP hPP) ξl h, ?_, ?_⟩
  · intro k hk μ hμ
    have hres := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hw.com k hk
    have hPg : PP ∈ c.Pg := by
      classical
      rw [hw.union]; exact Finset.mem_union.2 (Or.inr hPP)
    have hq : (c.chi (k + 1) PP)⁻¹ = w.ξ PP := by rw [hw.chiQ (k + 1) PP hPP, inv_inv]
    rcases hμ with hμ | hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).1) v φ hφ μ hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).2) v φ hφ μ hμ
  · intro ι hι
    have hfl := hs.choose_spec.2
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_topological_iso_parahoric_chart_split_place D s j v φ ι hfl.selfDual hfl.frame hι
    refine ⟨⟨e, he, GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hfl.selfDual hfl.frame hι e he, GlobalTheory.T.doublingHeight_splitPlaceChart_biInvariant_torus_value D s j v φ ι hfl.selfDual hfl.frame hι e he⟩,
      GlobalTheory.T.twisted_chain_chart_parahoric_eq_level D c w hw j hj s hs PP hPP v φ hφ ι hι, ?_⟩
    intro ξl hξ y hy d hd
    exact GlobalTheory.T.level_character_on_parahoric_chart_image D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd

end GlobalTheory.ChartTwist
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  atlas_forward_decl GlobalTheory.ChartTwist.chart_dict
end
