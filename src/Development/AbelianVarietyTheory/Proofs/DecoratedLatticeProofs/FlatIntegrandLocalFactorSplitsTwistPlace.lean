import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChainStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCompactParahoric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasSumBilateral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBiInvariantHasSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwistedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistCoef

theorem conj_unit {u : ℂˣ} (h : ‖(u : ℂ)‖ = 1) : conj (u : ℂ) = ((u⁻¹ : ℂˣ) : ℂ) := by
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    datum μ⁻¹ z = conj (datum μ z) := by
  unfold datum
  split_ifs with h
  · have h1 : ‖(((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      simp [Units.val_inv_eq_inv_val, norm_inv, hμ]
    rw [conj_unit h1]
    simp
  · simp

theorem om_datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (y : GL (A ⊕ D') k)
    (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    GlobalTheory.SplitWeil.om μ⁻¹ y (1 : GL (A ⊕ D) k) (datum μ⁻¹) z =
      conj (GlobalTheory.SplitWeil.om μ y (1 : GL (A ⊕ D) k) (datum μ) z) := by
  unfold GlobalTheory.SplitWeil.om
  rw [datum_inv_conj μ hμ]
  simp only [map_mul, Complex.conj_ofReal, conj_unit (hμ _), MonoidHom.inv_apply]
  simp

end Local

end GlobalTheory.TwistCoef

namespace GlobalTheory.TwistCoef

section IP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] {m n : Type} [Fintype m] [Fintype n]

theorem ip_conj (ν : Measure k) (F G : Matrix m n k → ℂ) :
    GlobalTheory.SplitWeil.ip ν (fun z => conj (F z)) (fun z => conj (G z)) = conj (GlobalTheory.SplitWeil.ip ν F G) := by
  unfold GlobalTheory.SplitWeil.ip
  rw [← integral_conj]
  congr 1
  funext z
  simp [map_mul]

end IP

theorem coef_split : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  intro D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP v φ hφ ι hι μT hμT _ _ ν hν cf hcf P x hx
  obtain ⟨-, hch'⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw (k + 1) hk s' hs' PP hPP
  obtain ⟨⟨e, he⟩, -, ⟨ι', hι'⟩, hμ⟩ := hch' v φ hφ
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨U, hU1, -⟩ := GlobalTheory.TwistChart.unit_section φ he
  have hunit : ∀ d, ‖(μT d : ℂ)‖ = 1 := fun d => by
    rw [hμT (U d) d ⟨e, he, (hU1 d).1, (hU1 d).2⟩]
    exact Circle.norm_coe _
  have hlift : LiftsChar φ PP μT (w.ξ PP) :=
    (GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v φ hφ).2.2.2.1 k hk μT (Or.inr hμT)
  obtain ⟨hW, hΦ, T, hT0, -, hTω, hC⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT μT hμS hμT hlift P m X hX
  obtain ⟨C, hC⟩ := hC ν hν x hx
  have key : ∀ y, coefW p.ω m X (p.pt P) (x * ι y) = C * conj (cf y) := by
    intro y
    have h1 : p.ω (x * ι y, 1) = p.ω (x, 1) * p.ω (ι y, ι' 1) := by
      rw [map_one, ← map_mul]
      simp
    unfold coefW
    rw [h1, ← hT0]
    simp only [Module.End.mul_apply]
    rw [hTω, hC, hcf, ← ip_conj]
    congr 2
    · funext z
      simp [GlobalTheory.ParHecke.omTwo, om_datum_inv_conj _ hunit]
    · funext z
      exact datum_inv_conj _ hunit z
  intro y
  have h0 := key 1
  rw [map_one, mul_one] at h0
  rw [key y, h0]
  ring

end GlobalTheory.TwistCoef
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCoefficient_splits_localFactor_twistPlace : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  atlas_forward_decl GlobalTheory.TwistCoef.coef_split
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
noncomputable section

namespace GlobalTheory.ChainTw.QuotUnr

theorem loc_eq_of_isRes {D : D7} {H H' : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ}
    (h : IsRes H PP a) (h' : IsRes H' PP a) (x : (PP.adicCompletion D.host.E)ˣ) (hx : Formalism.L2.Host.IsUnitAt PP x) :
    H.loc PP x = H'.loc PP x := by
  have ht := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP a h
  have ht' := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H' PP a h'
  obtain ⟨b, hb⟩ := GlobalTheory.GaussModulus.exists_int_approx PP (x := (x : PP.adicCompletion D.host.E)) (le_of_eq hx) 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hbv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = 1 := by
    have hx1 : Valued.v (x : PP.adicCompletion D.host.E) = 1 := hx
    have e : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = Valued.v (x : PP.adicCompletion D.host.E) :=
      Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hx1]; exact lt_of_le_of_lt hb hlt)
    rw [e, hx1]
  have hbP : b ∉ PP.asIdeal := by
    intro hm
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) < 1 := (PP.valuation_lt_one_iff_mem b).2 hm
    have h2 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) = 1 := by
      rw [← GlobalTheory.GaussModulus.valued_algebraMap]; exact hbv
    exact (ne_of_lt h1) h2
  have hb0 : (b : D.host.E) ≠ 0 := fun h0 => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  let kb : D.host.Eˣ := Units.mk0 _ hb0
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hu0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun h0 => hbP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let u : (kP PP)ˣ := Units.mk0 _ hu0
  have e1 := h b kb u rfl rfl
  have e2 := h' b kb u rfl rfl

  obtain ⟨y, hy⟩ : ∃ y : (PP.adicCompletion D.host.E)ˣ, y = x * (Formalism.L2.Host.atFin PP kb)⁻¹ := ⟨_, rfl⟩
  have hkv : Valued.v ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1 := hbv
  have hyu : Formalism.L2.Host.IsUnitAt PP y := by
    show Valued.v ((y : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hkv, inv_one, mul_one]
    exact hx
  have hy1 : Valued.v ((y : PP.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have hk0 : ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) =
        algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) := rfl
    have e : (y : PP.adicCompletion D.host.E) - 1 =
        ((x : PP.adicCompletion D.host.E) - algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) *
          (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E))⁻¹ := by
      have hne : algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) ≠ 0 := by
        rw [← hk0]; exact Units.ne_zero _
      rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, hk0, sub_mul, mul_inv_cancel₀ hne]
    rw [e, map_mul, map_inv₀, hbv, inv_one, mul_one]
    exact hb
  have hxy : x = Formalism.L2.Host.atFin PP kb * y := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hxy, map_mul, map_mul, ht y hyu hy1, ht' y hyu hy1, mul_one, mul_one]
  exact e1.symm.trans e2

end GlobalTheory.ChainTw.QuotUnr

open GlobalTheory.ChainTw.QuotUnr in

theorem GlobalTheory.ChainTw.quot_unrAt_twist : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  intro D c w hw PP hPP i j hi1 him hj1 hjm
  have hPg : PP ∈ c.Pg := by classical rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨Hi, hci, hri⟩ := hw.com.res ⟨i - 1, by omega⟩
  obtain ⟨Hj, hcj, hrj⟩ := hw.com.res ⟨j - 1, by omega⟩
  simp only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] at hci hri hcj hrj
  have ri := hri PP hPg
  have rj := hrj PP hPg
  rw [hw.chiQ i PP hPP] at ri
  rw [hw.chiQ j PP hPP] at rj
  intro x hx
  have li := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hci PP) x
  have lj := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hcj PP) x
  have split : GlobalTheory.LFun.locChar (c.μ i * (c.μ j)⁻¹) PP x =
      GlobalTheory.LFun.locChar (c.μ i) PP x * (GlobalTheory.LFun.locChar (c.μ j) PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [split, li, lj, loc_eq_of_isRes ri rj x hx, mul_inv_cancel]

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  atlas_forward_decl GlobalTheory.ChainTw.quot_unrAt_twist
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

noncomputable section

namespace GlobalTheory.LocUnifVal

theorem valued_eq_of_unif {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (ϖ : (Fv D.host.F v)ˣ)
    (hϖ : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = ValuativeRel.uniformizer (Fv D.host.F v)) :
    Valued.v (ϖ : Fv D.host.F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have key : ∀ a b : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) a ≤ ValuativeRel.valuation (Fv D.host.F v) b ↔
      Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (Fv D.host.F v)) a b).symm.trans
      (Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))) a b)
  have hlt : Valued.v (ϖ : Fv D.host.F v) < 1 := by
    have h1 : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) < ValuativeRel.valuation (Fv D.host.F v) 1 := by
      rw [map_one, hϖ]; exact ValuativeRel.uniformizer_lt_one
    rw [← map_one (Valued.v : Valuation (Fv D.host.F v) _)]
    exact lt_of_not_ge fun h => (not_le.2 h1) ((key _ _).2 h)
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer D.host.F
  have hx : Valued.v (algebraMap D.host.F (Fv D.host.F v) π) = WithZero.exp (-1 : ℤ) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Fv D.host.F v) := by
    rw [← hx]
    refine (key _ _).1 ?_
    rw [hϖ, ValuativeRel.le_uniformizer_iff, ← map_one (ValuativeRel.valuation (Fv D.host.F v))]
    refine lt_of_not_ge fun h => ?_
    have := (key _ _).1 h
    rw [map_one, hx] at this
    exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have h0 : Valued.v (ϖ : Fv D.host.F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [← WithZero.exp_log h0] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  intro D v φ PP hφ x ϖ hloc χ hχ
  obtain ⟨e, he, hx1, hx2, hx3⟩ := hloc
  have h : PP.under (𝓞 D.host.F) = v := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1.symm
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨hAt, rfl⟩
  have hxe : e * ((x : AE D) - 1) = (x : AE D) - 1 := by linear_combination -hx1
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x hxe
  have hτ : GlobalTheory.AdelicU.splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := (GlobalTheory.ResLift.eq_splitPrime hφ).symm
  have hc : (y : PP.adicCompletion D.host.E) = GlobalTheory.LFun.complMap h (ϖ : Fv D.host.F v) := by
    have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (x : AE D) := by
      rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt]; rfl
    rw [hy, GlobalTheory.LFun.compAt_apply, GlobalTheory.LFun.finAdEquiv_apply h, e1,
      GlobalTheory.LFun.ConjPlace.toCompl_eq (GlobalTheory.AdelicU.isCMExt_host D) h hτ, GlobalTheory.SplitProjChart.splitProj_emb, ← hx2]
    rfl
  have hu : Formalism.L2.Host.IsUnifAt PP y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hc, GlobalTheory.LFun.ConjPlace.valued_complMap (GlobalTheory.AdelicU.isCMExt_host D) h hτ]
    exact GlobalTheory.LocUnifVal.valued_eq_of_unif ϖ hx3
  have := hχ.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.LocUnifVal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  atlas_forward_decl GlobalTheory.LocUnifVal.value_eq_val
end

section
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun

theorem prod_map_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂˣ) (F : ℂˣ → ℂ) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

variable {K : Type} [Field K] [NumberField K]

theorem prod_fin_eq {N k t : ℕ} (w : HeightOneSpectrum (𝓞 K)) (z : ℕ → ℂˣ) (α : Fin N → ℂˣ)
    (hα : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, seg w (z i) t) (F : ℂˣ → ℂ) :
    ∏ j, F (α j) =
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range t, F (z i * npowU w (((t : ℂ) - 1) / 2 - l)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun j => F (α j)) = (Finset.univ.val.map α).map F from
      (Multiset.map_map _ _ _).symm, hα, prod_map_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [seg, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

theorem re_exp (t l : ℕ) : (((t : ℂ) - 1) / 2 - l).re = ((t : ℝ) - 1) / 2 - l := by
  simp

theorem npow_neg_nat (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    npow w (-(m : ℂ)) = (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ m)⁻¹ := by
  rw [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem prod_Icc_one (t : ℕ) (g : ℕ → ℂ) : ∏ n ∈ Finset.Icc 1 t, g n = ∏ l ∈ Finset.range t, g (l + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun l _ => by rw [add_comm]

theorem entry_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) (t l : ℕ) :
    ((z * npowU w (((t : ℂ) - 1) / 2 - l) : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (l + 1))⁻¹ := by
  rw [Units.val_mul, coe_npowU, mul_assoc, show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
    npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  congr 2
  push_cast
  ring

theorem entry_inv_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) {t l : ℕ} (hl : l < t) :
    (((z * npowU w (((t : ℂ) - 1) / 2 - l))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ)⁻¹ * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (t - 1 - l + 1))⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_mul, coe_npowU, mul_inv, mul_assoc,
    show (npow w (((t : ℂ) - 1) / 2 - l))⁻¹ = npow w (-(((t : ℂ) - 1) / 2 - l)) by
      rw [npow, npow, Complex.cpow_neg],
    show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  have e : ((t - 1 - l + 1 : ℕ) : ℂ) = t - l := by
    rw [show t - 1 - l + 1 = t - l by omega, Nat.cast_sub hl.le]
  rw [e]
  congr 2
  ring

end GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun GlobalTheory.LFun.SegFactor in
theorem GlobalTheory.LFun.seg_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  intro K _ _ w k t N z hz α hα
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm w
  have mem : ∀ j, ∃ i ∈ Finset.Icc 1 k, ∃ l < t, α j = z i * npowU w (((t : ℂ) - 1) / 2 - l) := by
    intro j
    have h1 : α j ∈ Finset.univ.val.map α := Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    rw [hα] at h1
    obtain ⟨i, hi, h2⟩ := Multiset.mem_sum.1 h1
    obtain ⟨l, hl, e⟩ := Multiset.mem_map.1 h2
    exact ⟨i, hi, l, Finset.mem_range.1 hl, e.symm⟩
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨i, -, l, hl, e⟩ := mem j
    have hn : ‖(α j : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2 - l) := by
      rw [e, Units.val_mul, norm_mul, hz, one_mul, coe_npowU, norm_npow, re_exp]
    have hl' : (l : ℝ) + 1 ≤ t := by exact_mod_cast hl
    have h0 : (0 : ℝ) ≤ l := l.cast_nonneg
    rw [hn, ← Real.rpow_neg (by linarith)]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hN.le (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)⟩
  · have eA : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor, prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - (β : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [entry_mul]
    have eB : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor]
      refine (prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - ((β⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)).trans ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹),
        ← Finset.prod_range_reflect (fun l => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ (l + 1))⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [entry_inv_mul w (z i) (Finset.mem_range.1 hl)]
    rw [eA, eB, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [mul_inv]
end
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segments_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  atlas_forward_decl GlobalTheory.LFun.seg_bounds_and_doubling_lFactor
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

noncomputable section

namespace GlobalTheory.QParL

theorem seg_eq_segL : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP →
    ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  intro D v φ PP hφ x ϖ hx z t
  obtain ⟨-, hq⟩ := GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ
  obtain ⟨e, -, -, -, hϖ⟩ := hx
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  refine Multiset.map_congr rfl fun n _ => ?_
  congr 1
  ext
  rw [GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem qPar_succ {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x (k + 1) = (qPar c PP x k).map (· * (Circle.toUnits (c.chS (k + 1) x) * (Circle.toUnits (c.chT (k + 1) x))⁻¹)) +
      GlobalTheory.LFun.seg PP (Circle.toUnits (c.chS (k + 1) x)) D.R.t := rfl

theorem card_qPar {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) : (qPar c PP x k).card = k * D.R.t := by
  induction k with
  | zero => simp [qPar]
  | succ k ih => rw [qPar_succ, Multiset.card_add, Multiset.card_map, ih, GlobalTheory.LFun.card_seg]; ring

theorem seg_map_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (z u : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w z t).map (· * u) = GlobalTheory.LFun.seg w (z * u) t := by
  simp only [GlobalTheory.LFun.seg, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun i _ => mul_right_comm _ _ _

theorem sum_map_mul {ι : Type} (s : Finset ι) (f : ι → Multiset ℂˣ) (u : ℂˣ) :
    (∑ i ∈ s, f i).map (· * u) = ∑ i ∈ s, (f i).map (· * u) :=
  map_sum (Multiset.mapAddMonoidHom (· * u)) f s

theorem qPar_closed {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x k = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * c.eps k) x)) D.R.t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qPar_succ, ih, sum_map_mul, Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [seg_map_mul, ← GlobalTheory.ChainOnto.ParClosed.eps_succ]
      congr 1
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
      ext
      simp only [Units.val_mul]
      ring
    · rw [GlobalTheory.ChainOnto.ParClosed.chS_succ]

theorem qPar_twist {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) =
      ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x)) D.R.t := by
  rw [qPar_closed, sum_map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [seg_map_mul, GlobalTheory.ChainOnto.ParClosed.chT_succ]
  congr 1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [_root_.mul_inv_rev]
  group

theorem invNormFactor_eq (q t k : ℕ) :
    GlobalTheory.GLDoubling.invNormFactor q (k * t) ((t : ℂ) / 2) =
      ((∏ n ∈ Finset.Ioc t ((k + 1) * t), (1 - ((q : ℝ) ^ n)⁻¹) : ℝ) : ℂ) := by
  unfold GlobalTheory.GLDoubling.invNormFactor
  push_cast
  rw [show (k + 1) * t = t + k * t by ring]
  generalize k * t = m
  have h1 : Finset.Ioc t (t + m) = (Finset.Icc 1 m).map (addLeftEmbedding t) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Icc, addLeftEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - t, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
  rw [h1, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (2 * ((t : ℂ) / 2) + (i : ℂ)) = ((addLeftEmbedding t i : ℕ) : ℂ) := by
    simp only [addLeftEmbedding_apply]; push_cast; ring
  rw [this, Complex.cpow_neg, Complex.cpow_natCast]

end GlobalTheory.QParL

open GlobalTheory.QParL in
theorem GlobalTheory.ChainTw.qPar_twist_lFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  intro D c w hw k hk PP hPP v φ hφ x ϖ hx
  refine ⟨seg_eq_segL D v φ PP hφ x ϖ hx, card_qPar c PP x k, fun α hα => ?_⟩
  rw [qPar_twist] at hα
  have hz : ∀ i ∈ Finset.Icc 1 k, Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x) =
      GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP := fun i hi =>
    GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value D v φ PP hφ x ϖ hx _ (GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place D c w hw PP hPP i (k + 1) (Finset.mem_Icc.1 hi).1
      (by have := (Finset.mem_Icc.1 hi).2; omega) (by omega) (by omega))
  have hα' : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k,
      GlobalTheory.LFun.seg PP (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) D.R.t := by
    rw [hα]; exact Finset.sum_congr rfl fun i hi => by rw [hz i hi]
  obtain ⟨hb, hL⟩ := GlobalTheory.T.segments_bounds_and_doubling_lFactor PP k D.R.t (k * D.R.t)
    (fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) (fun i => GlobalTheory.LFun.norm_val _ _) α hα'
  refine ⟨hb, ?_⟩
  rw [hL, invNormFactor_eq, blockL, zinv]

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_block_parameter_twist_L_factor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  atlas_forward_decl GlobalTheory.ChainTw.qPar_twist_lFactor
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem isHgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ H hH
  refine ⟨fun κ hκ g => ?_, fun e => ?_⟩
  · have hK : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ KO k (A ⊕ D) :=
      (mem_parahoric.1 (GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (one_mem _) hκ)).1
    have e1 : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * g) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) * emb₂ k (Equiv.refl (A ⊕ D)) (1, g) := by
      rw [← map_mul]; simp
    have e2 : emb₂ k (Equiv.refl (A ⊕ D)) (1, g * κ) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, g) * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) := by
      rw [← map_mul]; simp
    exact ⟨by simp only [e1]; exact (hH.1 _ hK _).1, by simp only [e2]; exact (hH.1 _ hK _).2⟩
  · show H (emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e)) = _
    rw [GlobalTheory.ChainStepSupp.emb₂_one_torusElt, mtor, hH.2]
    congr 2
    simp [sumAbs, Fintype.sum_sum_type]

end GlobalTheory.ParHecke
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  atlas_forward_decl GlobalTheory.ParHecke.isHgt_lower
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (n : ℕ) :
    (s.map (· * c)).esymm n = c ^ n * s.esymm n := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.sum_map_mul_left.symm]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hc : t.card = n := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hc, mul_comm, Multiset.map_id']

theorem genVal_map_mul (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) :
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  unfold genVal
  have e : ((B.map (· * c)).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (· * (c : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  rw [e, esymm_map_mul_const]
  ring

end GlobalTheory.ParHecke
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ), genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  atlas_forward_decl GlobalTheory.ParHecke.genVal_map_mul
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_torusElt_eq {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]

theorem sum_indic {n : Type} [Fintype n] [DecidableEq n] (s : Finset n) : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic, Finset.sum_ite_mem]

theorem reGL_symm_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m k) : GlobalTheory.ChainStepSupp.reGL k e.symm (GlobalTheory.ChainStepSupp.reGL k e g) = g := by
  ext i j
  simp [GlobalTheory.ChainStepSupp.val_reGL]

theorem reGL_mem_KO_iff {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} : GlobalTheory.ChainStepSupp.reGL k e g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => reGL_symm_reGL e g ▸ GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm h, GlobalTheory.ChainStepSupp.reGL_mem_KO e⟩

theorem unram_det_KO {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ KO k n) : μ₀ (GeneralLinearGroup.det κ) = 1 :=
  hμ _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hκ))

theorem unram_det_dcoset {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ}
    {s : Finset n} {g : GL n k}
    (h : ∃ κ ∈ KO k n, ∃ κ' ∈ KO k n, g = κ * torusElt k n ϖ (indic s) * κ') :
    μ₀ (GeneralLinearGroup.det g) = μ₀ ϖ ^ s.card := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := h
  rw [map_mul, map_mul, map_mul, map_mul, unram_det_KO hμ hκ, unram_det_KO hμ hκ', det_torusElt_eq, sum_indic,
    map_zpow, one_mul, mul_one, zpow_natCast]

open Classical in

theorem isRepsK_image {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g₀ : GL m k} {R : Finset (GL m k)} (hR : IsRepsK g₀ R) :
    IsRepsK (GlobalTheory.ChainStepSupp.reGL k e g₀) (R.image (GlobalTheory.ChainStepSupp.reGL k e)) := by
  refine ⟨fun g' hg' => ?_, fun κ hκ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hR.1 g hg
    exact ⟨_, GlobalTheory.ChainStepSupp.reGL_mem_KO e ha, _, GlobalTheory.ChainStepSupp.reGL_mem_KO e hb, by simp only [map_mul]⟩
  · obtain ⟨g, ⟨hg, hgK⟩, huniq⟩ := hR.2 (GlobalTheory.ChainStepSupp.reGL k e.symm κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm hκ)
    have key : ∀ x : GL m k, (GlobalTheory.ChainStepSupp.reGL k e x)⁻¹ * (κ * GlobalTheory.ChainStepSupp.reGL k e g₀) =
        GlobalTheory.ChainStepSupp.reGL k e (x⁻¹ * (GlobalTheory.ChainStepSupp.reGL k e.symm κ * g₀)) := by
      intro x
      rw [map_mul, map_mul, map_inv, GlobalTheory.ChainStepSupp.reGL_reGL_symm]
    refine ⟨GlobalTheory.ChainStepSupp.reGL k e g, ⟨Finset.mem_image_of_mem _ hg, ?_⟩, ?_⟩
    · rw [key]; exact GlobalTheory.ChainStepSupp.reGL_mem_KO e hgK
    · rintro y ⟨hy, hyK⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      rw [key, reGL_mem_KO_iff] at hyK
      rw [huniq x ⟨hx, hyK⟩]

theorem twist_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  intro k _ _ _ _ D _ _ N ε ϖ hϖ μ₀ hμ β f hf hH f₂ hf₂
  classical
  refine ⟨fun κ hκ m => ?_, fun s R hR m => ?_⟩
  · have hk1 := unram_det_KO hμ hκ
    have hρ := hf (GlobalTheory.ChainStepSupp.reGL k ε κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO ε hκ) (GlobalTheory.ChainStepSupp.reGL k ε m)
    simp only [hf₂, map_mul, hk1, one_mul, mul_one, hρ.1, hρ.2, and_self]
  · set ρ := GlobalTheory.ChainStepSupp.reGL k ε with hρdef
    set s' := s.map ε.toEmbedding with hs'
    have ht : ρ (torusElt k (Fin N) ϖ (indic s)) = torusElt k D ϖ (indic s') := by
      rw [hρdef, GlobalTheory.ChainStepSupp.reGL_torusElt]
      congr 1
      funext d
      simp [indic, hs', Finset.mem_map_equiv]
    have hR' : IsRepsK (torusElt k D ϖ (indic s')) (R.image ρ) := ht ▸ isRepsK_image ε hR
    have hcard : Fintype.card D = N := (Fintype.card_congr ε).symm.trans (Fintype.card_fin N)
    have hH' := hH s' _ hR' (ρ m)
    rw [Finset.sum_image (fun x _ y _ h => ρ.injective h), hs', Finset.card_map, hcard] at hH'
    have hterm : ∀ g ∈ R, f₂ (m * g) = ((((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
        (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card) * f (ρ m * ρ g) := by
      intro g hg
      rw [hf₂, map_mul, map_mul, map_mul, unram_det_dcoset hμ (hR.1 g hg), mul_inv, Units.val_mul, ← inv_pow,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hH', hf₂]
    ring

end GlobalTheory.TwistRenumber

end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  atlas_forward_decl GlobalTheory.TwistRenumber.twist_renumber
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistedZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cellFun (r l t : ℕ) (ϖ : kˣ) (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k) : ℂ :=
  ∑' e : {e : Fin (l * t) → ℤ // Antitone e},
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k)).indicator (fun _ => v e.1) g

theorem cellFun_of_mem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ)
    (hdisj : Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))))
    (e : {e : Fin (l * t) → ℤ // Antitone e}) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : cellFun r l t ϖ v g = v e.1 := by
  unfold cellFun
  rw [tsum_eq_single e]
  · exact Set.indicator_of_mem hg _
  · intro e' he'
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj he'.symm) hg) _

theorem cellFun_of_notMem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : ∀ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∉ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) :
    cellFun r l t ϖ v g = 0 := by
  unfold cellFun
  simp [Set.indicator_of_notMem (hg _)]

theorem mem_dcell_mul_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {ϖ : kˣ}
    {f : D → ℤ} {g j j' : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (hj' : j' ∈ parahoric k A D) :
    j * g * j' ∈ dcell ϖ f ↔ g ∈ dcell ϖ f := by
  unfold dcell
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h
    refine DoubleCoset.mem_doubleCoset.2 ⟨j⁻¹ * a, mul_mem (inv_mem hj) ha, b * j'⁻¹, mul_mem hb (inv_mem hj'), ?_⟩
    calc g = j⁻¹ * (j * g * j') * j'⁻¹ := by group
      _ = _ := by rw [e]; group
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 h
    exact DoubleCoset.mem_doubleCoset.2 ⟨j * a, mul_mem hj ha, b * j', mul_mem hb hj', by group⟩

theorem cellFun_biinv {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k)
    {j j' : GL (Fin r ⊕ Blocks l t) k} (hj : j ∈ parahoric k (Fin r) (Blocks l t))
    (hj' : j' ∈ parahoric k (Fin r) (Blocks l t)) : cellFun r l t ϖ v (j * g * j') = cellFun r l t ϖ v g := by
  unfold cellFun
  congr 1
  funext e
  by_cases h : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_dcell_mul_iff hj hj').2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((mem_dcell_mul_iff hj hj').1 h'))]

theorem torusElt_zero {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) : torusElt k n ϖ 0 = 1 := by
  ext i j
  simp [val_torusElt, Matrix.one_apply, diagonal_apply]

theorem mtor_zero {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) :
    (mtor ϖ (0 : D → ℤ) : GL (A ⊕ D) k) = 1 := by
  rw [mtor, Sum.elim_zero_zero, torusElt_zero]

theorem sumAbs_comp {N : ℕ} {D : Type} [Fintype D] (ε : Fin N ≃ D) (e : Fin N → ℤ) :
    sumAbs (e ∘ ε.symm) = sumAbs e := by
  unfold sumAbs
  exact Equiv.sum_comp ε.symm (fun i => |e i|)

theorem sumAbs_elim {A D : Type} [Fintype A] [Fintype D] (e : D → ℤ) :
    sumAbs (Sum.elim (0 : A → ℤ) e) = sumAbs e := by
  simp [sumAbs, Fintype.sum_sum_type]

theorem det_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.zpow_add, Units.val_mul, ih, Units.val_zpow_eq_zpow_val ϖ (e i)]

theorem zonalInt_one {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k))
    (hμK : μK (KO k (Fin N)) = 1) {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (hψ : IsBorelSph k γ ψ) :
    zonalInt μK ψ 1 = 1 := by
  have h1 : ψ 1 = 1 := by
    have hb : (1 : GL (Fin N) k) ∈ borel k (Fin N) := (mem_borel _).2 fun i j hij => by
      simp [Matrix.one_apply, (ne_of_lt hij).symm]
    rw [hψ.2 1 hb (fun _ => 1) (fun i => by simp)]
    have : ord k 1 = 0 := by
      have := ord_mul k 1 1
      simp at this
      exact this
    simp [this]
  have hK : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := fun κ hκ => by
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun (SplitFlip.isOpen_KO.measurableSet) hK]
  simp [Measure.real, hμK]

theorem hgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ),
    IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) :=
  GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock

theorem genVal_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ),
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n :=
  GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul

theorem twist_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ),
    (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) →
    ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
      f (GlobalTheory.ChainStepSupp.reGL k ε m)) →
    (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧
    ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m :=
  GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex

theorem lower_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ →
  ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) →
  ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k)) (ψ : GL (Fin (l * t)) k → ℂ),
  (∀ f : GL (Fin (l * t)) k → ℂ, (∀ κ ∈ KO k (Fin (l * t)), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset (Fin (l * t))) R, IsRepsK (torusElt k (Fin (l * t)) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (l * t) (Finset.univ.val.map α) s.card * f m) →
    ∀ m, f m = f 1 * zonalInt μK ψ m) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V)
    (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ e : Fin (l * t) → ℤ,
  ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
    (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) * ℓ x := by
  intro k _ _ _ _ ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH _ μK ψ hψ V _ _ π x ℓ hx hℓ e
  classical
  have hH' := hgt_lower k (Fin r) (Blocks l t) ϖ H hH
  set H' : GL (Blocks l t) k → ℝ := fun m => H (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) with hH'def
  set f : GL (Blocks l t) k → ℂ := fun m => (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    ℓ (π (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) x) / ((Real.sqrt (H' m) : ℝ) : ℂ) ^ Fintype.card (Fin r)
    with hfdef
  obtain ⟨hfK, hfH⟩ := GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen k (Fin r) (Blocks l t) ϖ hϖ ξ hξt hξr V π B x ℓ hx hℓ H' hH' f (fun m => rfl)
  set f₂ : GL (Fin (l * t)) k → ℂ := fun m => (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    f (GlobalTheory.ChainStepSupp.reGL k (blkEquiv l t) m) with hf₂def
  obtain ⟨hf₂K, hf₂H⟩ := twist_transport k (Blocks l t) (l * t) (blkEquiv l t) ϖ hϖ μ₀ hμ₀
    (B.map (· * (ξ ϖ)⁻¹)) f hfK hfH f₂ (fun m => rfl)
  have hα : Finset.univ.val.map α = (B.map (· * (ξ ϖ)⁻¹)).map (· * (μ₀ ϖ)⁻¹) := by
    rw [hαB, Multiset.map_map]
    congr 1
    funext b
    simp only [Function.comp, MonoidHom.mul_apply, _root_.mul_inv_rev]
    rw [mul_assoc, mul_comm (ξ ϖ)⁻¹]
  have hz := hψ f₂ hf₂K (fun s R hR m => by rw [hf₂H s R hR m, hα, genVal_map_mul _ _ _ _ _ (μ₀ ϖ)⁻¹])
  have hval := hz (torusElt k (Fin (l * t)) ϖ e)

  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hf₂1 : f₂ 1 = ℓ x := by
    have h1 : H' 1 = 1 := by
      have := hH'.2 0
      rw [torusElt_zero] at this
      rw [this]; simp [sumAbs]
    have he1 : emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) ((1 : GL (Fin r) k), (1 : GL (Blocks l t) k)) = 1 := map_one _
    simp only [hf₂def, hfdef, map_one, h1, Real.sqrt_one, he1]
    simp
  have hS : ((Real.sqrt (H' (torusElt k (Blocks l t) ϖ (e ∘ (blkEquiv l t).symm))) : ℝ) : ℂ) ^ Fintype.card (Fin r) =
      (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    rw [hH'.2, sumAbs_comp, Fintype.card_fin, ← Complex.ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast; ring
  have hsum : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
  have hval' : f₂ (torusElt k (Fin (l * t)) ϖ e) = (((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
      ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) /
        (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ)) := by
    simp only [hf₂def, hfdef]
    rw [GlobalTheory.ChainStepSupp.reGL_torusElt, GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hS, det_torusElt, det_torusElt, hsum]
    simp [map_zpow, Units.val_zpow_eq_zpow_val]
  have key := hval'.symm.trans (hval.trans (by rw [hf₂1]))
  have hA : ((μ₀ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((ξ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hSne : (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  rw [MonoidHom.mul_apply, Units.val_mul, mul_zpow]
  have alg : ∀ (X Y S L : ℂ), X ≠ 0 → Y ≠ 0 → S ≠ 0 → L = X * Y * S * (X⁻¹ * (Y⁻¹ * L / S)) := by
    intro X Y S L hX hY hS; field_simp
  have hAn := zpow_ne_zero (∑ i, e i) hA
  have hBn := zpow_ne_zero (∑ i, e i) hB
  calc ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x)
      = ((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) * ((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
          (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
          ((((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
            ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) / (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ))) :=
        alg _ _ _ _ hAn hBn hSne
    _ = _ := by rw [key]; ring

theorem local_zeta_twisted : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  intro hUD k _ _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hξr hμ₀ hμ₀u B α ρ hαB hαρ H hH _ _ m _ hm c hc
  classical
  letI : MeasurableSpace (GL (Fin (l * t)) k) := borel _
  haveI : BorelSpace (GL (Fin (l * t)) k) := ⟨rfl⟩
  obtain ⟨μK, hμKH, hμK⟩ := GlobalTheory.GLDoubling.Model.exists_haar (k := k) (l * t)
  haveI := hμKH
  obtain ⟨ψ, hψB, hψ⟩ := GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical k (l * t) μK hμK ϖ hϖ α
  obtain ⟨hvol, hdisj⟩ := GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint k ϖ hϖ r l t m hm μK hμK
  have hceq : c = fun g => ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ) :=
    funext hc
  obtain ⟨hcBi, hcSupp, hcVal⟩ := GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted k ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hμ₀ hμ₀u
  rw [← hceq] at hcBi hcSupp
  beta_reduce at hcVal
  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hq1 : (1:ℝ) < resCard k := by exact_mod_cast one_lt_resCard k
  set C0 : ℝ := volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ with hC0
  have hC0pos : 0 < C0 := by
    refine mul_pos ?_ (inv_pos.2 (pow_pos hq _))
    rw [GlobalTheory.ChainStepIdentities.volAdd_eq k ν hν r]
    refine Finset.prod_pos fun i hi => inv_pos.2 ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    unfold zetaAt
    exact inv_pos.2 (sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))))
  have hcv : ∀ e : Fin (l * t) → ℤ, c (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
      ((C0 * (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    intro e
    have hsE : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
    rw [hc, hcVal, hsE, sumAbs_comp, Complex.ofReal_mul C0, Complex.ofReal_cpow hq.le, hC0]
    push_cast
    ring
  have hc1 : c 1 = ((C0 : ℝ) : ℂ) := by
    have := hcVal 0
    rw [mtor_zero, ← hc] at this
    rw [this]; simp [sumAbs, C0]
  set w : (Fin (l * t) → ℤ) → ℂ := fun e => (((resCard k : ℝ) ^
      (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
      zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) with hw
  refine ⟨by rw [hc1]; exact_mod_cast hC0pos.ne', cellFun r l t ϖ w, ?_, ?_, ?_⟩
  · intro V _ _ π x ℓ hx hℓ g
    have hE := lower_eigen k ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH μK ψ hψ V π x ℓ hx hℓ
    by_cases hg : ∃ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
    · obtain ⟨e, hge⟩ := hg
      rw [cellFun_of_mem w hdisj e hge]
      obtain ⟨j, hj, j', hj', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hge
      set a := (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) with ha
      set d := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj)
      set d' := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj')
      have hc_eq : c (j * a * j') = (ξ d : ℂ) * (ξ d' : ℂ) * c a := by
        rw [mul_assoc, (hcBi j hj d rfl _).1, (hcBi j' hj' d' rfl a).2]; ring
      have hℓ_eq : ℓ (π (j * a * j') x) = (ξ d : ℂ) * (ξ d' : ℂ) * ℓ (π a x) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.1 j' hj' d' rfl]
        simp only [map_smul, smul_eq_mul]
        rw [hℓ j hj d rfl]; ring
      have u1 : starRingEnd ℂ (ξ d : ℂ) * (ξ d : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d]; simp
      have u2 : starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d']; simp
      have hM : ‖(((μ₀ * ξ) ϖ : ℂˣ) : ℂ)‖ = 1 := by
        rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ₀u, hξu, one_mul]
      have u3 : starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i) = 1 := by
        rw [map_zpow₀, ← mul_zpow, Complex.conj_mul', hM]; simp
      have hqab : (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) *
          (resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ)) =
          (resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) := by
        rw [← Real.rpow_add hq]; congr 1; push_cast; ring
      rw [hc_eq, hℓ_eq, hcv e.1, hE e.1, hc1, hw]
      simp only [map_mul, Complex.conj_ofReal]
      have hqab' := congrArg (fun y : ℝ => (y : ℂ)) hqab
      simp only [Complex.ofReal_mul] at hqab' ⊢
      linear_combination (↑C0 * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e.1) * ℓ x) *
        ((starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) * (starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u1 +
        ((starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u2 +
        (((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u3 + hqab')
    · simp only [not_exists] at hg
      have hc0 : c g = 0 := by
        by_contra hne
        obtain ⟨e, he, hge⟩ := GlobalTheory.T.support_parahoricBiTransforming_doubleCosets k ϖ hϖ r l t ξ hξt hξr c hcBi hcSupp g hne
        exact hg ⟨e, he⟩ hge
      rw [cellFun_of_notMem w hg, hc0]; simp
  · intro g hgJ
    have h0 : g ∈ dcell ϖ ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) := by
      have : ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) = 0 := rfl
      rw [this]
      unfold dcell
      rw [mtor_zero]
      exact DoubleCoset.mem_doubleCoset.2 ⟨g, hgJ, 1, one_mem _, by simp⟩
    rw [cellFun_of_mem w hdisj ⟨0, fun _ _ _ => le_refl _⟩ h0, hw]
    simp [sumAbs, torusElt_zero, zonalInt_one μK hμK hψB]
  · intro s hs
    obtain ⟨hsum, hhas⟩ := GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value hUD k (l * t) μK hμK ϖ hϖ α ρ hαρ ψ hψB s hs
    have hHtor : ∀ e : Fin (l * t) → ℤ, H (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (resCard k : ℝ) ^ (-(sumAbs e)) := by
      intro e; rw [mtor, hH.2, sumAbs_elim, sumAbs_comp]
    have hqC : ((resCard k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hterm : ∀ e : {e : Fin (l * t) → ℤ // Antitone e},
        (m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) *
          (cellFun r l t ϖ w (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) *
            (H (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) ^ (s - (t : ℂ) / 2)) =
        (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
          zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := by
      intro e
      have hmem : (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) ∈
          dcell ϖ (e.1 ∘ (blkEquiv l t).symm) :=
        DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
      rw [cellFun_of_mem w hdisj e hmem, hHtor, hvol e.1]
      simp only [hw]
      have e1 : (((resCard k : ℝ) ^ ((r : ℤ) * sumAbs e.1) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cpow hq.le, Real.rpow_intCast]
      have e2 : (((resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hq.le]
      have e3 : (((resCard k : ℝ) ^ (-(sumAbs e.1)) : ℝ) : ℂ) ^ (s - (t : ℂ) / 2) =
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) := by
        rw [← Real.rpow_intCast, Complex.cpow_mul_ofReal_nonneg hq.le]
      have e4 : (resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [Complex.ofReal_natCast]
      have hadd : ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [← Complex.cpow_add _ _ hqC, ← Complex.cpow_add _ _ hqC]
        congr 1
        push_cast
        ring
      rw [Complex.ofReal_mul, e1, e2, e3, e4, ← hadd]
      ring
    set F : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => cellFun r l t ϖ w g * (H g : ℂ) ^ (s - (t : ℂ) / 2) with hF
    have hFbi : ∀ g j, j ∈ parahoric k (Fin r) (Blocks l t) → ∀ j' ∈ parahoric k (Fin r) (Blocks l t),
        F (j * g * j') = F g := by
      intro g j hj j' hj'
      have hjK := (mem_parahoric.1 hj).1
      have hj'K := (mem_parahoric.1 hj').1
      simp only [hF, cellFun_biinv w g hj hj', (hH.1 j' hj'K (j * g)).2, (hH.1 j hjK g).1]
    have hsupp : ∀ g, F g ≠ 0 → ∃ e : {e : Fin (l * t) → ℤ // Antitone e},
        g ∈ DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t)) := by
      intro g hg
      by_contra hne
      simp only [not_exists] at hne
      apply hg
      simp only [hF, cellFun_of_notMem w hne, zero_mul]
    have hsumm : Summable fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) *
          ‖F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))‖ := by
      refine hsum.congr fun e => ?_
      change _ = m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) * _
      rw [← hterm e, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
    obtain ⟨hInt, hHas, -⟩ := GlobalTheory.integral_biInvariant_hasSum_doubleCoset (GL (Fin r ⊕ Blocks l t) k) m
      (parahoric k (Fin r) (Blocks l t)) GlobalTheory.ParHecke.Model.isOpen_parahoric GlobalTheory.ParHecke.Model.isCompact_parahoric
      {e : Fin (l * t) → ℤ // Antitone e} (fun e => mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) hdisj F hFbi hsupp hsumm
    refine ⟨hInt, ?_⟩
    have hfun : (fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        ((m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) : ℝ) : ℂ) *
          F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))) = fun e : {e : Fin (l * t) → ℤ // Antitone e} => (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
            zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := funext hterm
    rw [hfun] at hHas
    exact hHas.unique hhas

end GlobalTheory.TwistedZeta
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  atlas_forward_decl GlobalTheory.TwistedZeta.local_zeta_twisted
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

noncomputable section

namespace GlobalTheory.ChainTw.OnePlace

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Core.Rk.IP GlobalTheory.ParHecke GlobalTheory.Core.Rk.SphCoef

theorem transport {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H)
    (m : Measure G) [m.IsHaarMeasure] (P : Subgroup G) (hP : IsOpen (P : Set G)) (h1 : m P = 1) (f : G → ℂ)
    (hf : Integrable f m) :
    ∃ (J : Subgroup H) (μ : Measure H), IsOpen (J : Set H) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧
      Integrable (fun y => f (e.symm y)) μ ∧ (∀ y, y ∈ J ↔ e.symm y ∈ P) ∧ ∫ y, f (e.symm y) ∂μ = ∫ g, f g ∂m := by
  let e' : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have he : (e' : G → H) = e := rfl
  have hJ : ((P.comap e.symm.toMulEquiv.toMonoidHom : Subgroup H) : Set H) = e.symm ⁻¹' (P : Set G) := rfl
  refine ⟨P.comap e.symm.toMulEquiv.toMonoidHom, m.map e', ?_, ?_, ?_, ?_, fun y => Iff.rfl, ?_⟩
  · rw [hJ]; exact hP.preimage e.symm.continuous
  · rw [he]; exact e.isHaarMeasure_map m
  · rw [MeasurableEquiv.map_apply, hJ, he, ← h1]
    congr 1
    ext g; simp
  · rw [integrable_map_equiv]
    convert hf using 1
    funext g; simp [he]
  · rw [integral_map_equiv]
    simp [he]

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] (P : Subgroup G) (hP : IsOpen (P : Set G)) (hc : IsCompact (P : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m P = 1 := by
  let K : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨P, hc⟩, by
      simp only [hP.interior_eq]
      exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {D : D7}

theorem rcoef_eq_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {A : HSp D} (m : Measure (GA D A))
    (hm : m.IsHaarMeasure) {u₁ u₂ : GA D A → ℂ} (h1 : MemL2Quotient (GQ A) m u₁) (h2 : MemL2Quotient (GQ A) m u₂)
    (ι : GL (I ⊕ I') k →* GA D A) (x : GA D A) (hx : ∀ y, ι y * x = x * ι y) (ξ : kˣ →* ℂˣ) (hξ : GlobalTheory.SmGL.IsUnitaryChar ξ)
    (ϖ : kˣ) (B : Multiset ℂˣ) (hg : IsGen ((GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι) ξ ϖ B u₁)
    (ht : ∀ j ∈ parahoric k I I', ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ g, u₂ (g * ι j) = (ξ d : ℂ) * u₂ g) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (I ⊕ I') k) V) (u : V) (ℓ : V →ₗ[ℂ] ℂ),
      IsGen π ξ ϖ B u ∧ IsCoType π ξ ℓ ∧ (∀ y, ℓ (π y u) = rcoef m u₁ u₂ (x * ι y)) ∧ ℓ u = rcoef m u₁ u₂ x := by
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m F}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ρ : Representation ℂ (GL (I ⊕ I') k) (GA D A → ℂ) := (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι
  have hst : ∀ g, p ≤ p.comap (ρ g) := fun g F hF => MemL2Quotient.mul_right hF (ι g)
  let π : Representation ℂ (GL (I ⊕ I') k) p := ρ.subrepresentation p hst
  have hπ : ∀ g (F : p), ((π g F : p) : GA D A → ℂ) = ρ g F := fun _ _ => rfl
  let ℓ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left (MemL2Quotient.mul_right F.2 x) (MemL2Quotient.mul_right G.2 x) h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  refine ⟨p, inferInstance, inferInstance, π, ⟨u₁, h1⟩, ℓ, ⟨fun j hj d hd => Subtype.ext (hg.1 j hj d hd), hg.2.1,
    fun s R d hR => Subtype.ext ?_⟩, fun j hj d hd F => ?_, fun y => ?_, rfl⟩
  · rw [Submodule.coe_sum]
    exact hg.2.2 s R d hR
  · have e1 : rTr A x (π j F) = rTr A (ι j) (rTr A x F) := funext fun g => by
      show (F : GA D A → ℂ) (g * x * ι j) = (F : GA D A → ℂ) (g * ι j * x)
      rw [mul_assoc, mul_assoc, hx]
    have e2 := petersson_rTr (μ := m) (MemL2Quotient.mul_right F.2 x) h2 (ι j)
    have hn : (ξ d : ℂ) * conj (ξ d : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ d]; simp
    have e3 : ∀ φ : GA D A → ℂ, petersson A m φ u₂ = (ξ d : ℂ) * petersson A m φ (rTr A (ι j) u₂) := fun φ => by
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend, rTr, ht j hj d hd, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext q
      linear_combination (-(φ q.out * conj (u₂ q.out))) * hn
    show petersson A m (rTr A x (π j F)) u₂ = (ξ d : ℂ) * petersson A m (rTr A x F) u₂
    rw [e1, e3]
    exact congrArg _ e2
  · show petersson A m (rTr A x (ρ y u₁)) u₂ = petersson A m (rTr A (x * ι y) u₁) u₂
    congr 1
    funext g
    show u₁ (g * x * ι y) = u₁ (g * (x * ι y))
    rw [mul_assoc]

theorem val_type {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L)
    (g : GA D s.V) : PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ f) = PiTensorProduct.lift.symm u.1 f := by
      rw [PiTensorProduct.lift_symm]; rfl
    have := hT.lev f κ hκ g
    rw [← e] at this
    simp only [PiLocalization₂.val, map_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  | add a b ha hb =>
    simp only [PiLocalization₂.val, map_add, Pi.add_apply] at ha hb ⊢
    rw [ha, hb]; ring

theorem hgt_split {A : HSp D} {L : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat A} {a : GL (Fin A.rank) (AE D)} (hL : IsSelfDualC A L)
    (ha : GlobalTheory.Doubling.IsMaj A a) (Sf : Finset (HeightOneSpectrum (𝓞 D.host.F))) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ Sf) (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v 1 = 1) {x : GA D A} (hx : x ∈ openOff A L Sf)
    (hxv : proj D.sp.cm.sig A.gram v x = 1) (y : GlobalTheory.FinZeta.Gv A v) (t : ℂ) :
    GlobalTheory.Doubling.npow (hgtL A L a (x * emb D.sp.cm.sig A.gram v y)) t =
      GlobalTheory.Doubling.npow (hgtL A L a x) t * ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y : ℝ) : ℂ) ^ t := by
  classical
  obtain ⟨-, -, h⟩ := hgtL_props D A L a hL ha
  have hne : ∀ u, u ≠ v → proj D.sp.cm.sig A.gram u (x * emb D.sp.cm.sig A.gram v y) = proj D.sp.cm.sig A.gram u x :=
    fun u hu => by rw [map_mul, proj_emb_ne _ _ hu, mul_one]
  have hxy : x * emb D.sp.cm.sig A.gram v y ∈ openOff A L Sf := fun u hu => by
    rw [hne u (fun e => hu (e ▸ hv))]; exact hx u hu
  have e : (hgtL A L a (x * emb D.sp.cm.sig A.gram v y) : ℝ) = (hgtL A L a x : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := by
    rw [(h Sf).2 _ hxy, (h Sf).2 _ hx, ← Finset.mul_prod_erase Sf _ hv, ← Finset.mul_prod_erase Sf _ hv, hxv, h1,
      Finset.prod_congr rfl fun u hu => congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L u) (hne u (Finset.ne_of_mem_erase hu))]
    simp only [map_mul, projArch_emb, proj_emb_self, hxv, mul_one, one_mul]
    ring
  simp only [GlobalTheory.Doubling.npow]
  have h0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := NNReal.coe_nonneg _
  rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) h0]

theorem hgt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} {H : GL n k → ℝ} (hH : IsHgt ϖ H) {g : GL n k}
    (hg : g ∈ GlobalTheory.SplitWeil.KO k n) : H g = 1 := by
  have e : GlobalTheory.GLDoubling.torusElt k n ϖ 0 = 1 := by
    simp only [GlobalTheory.GLDoubling.torusElt, Pi.zero_apply, zpow_zero]
    exact map_one _
  have h := hH.2 0
  rw [e] at h
  rw [← mul_one g, (hH.1 g hg 1).1, h]
  simp [GlobalTheory.ZonalCellDecomposition.sumAbs]

set_option maxHeartbeats 1600000 in

theorem local_factor : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (ζ : GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hQ v₁ hv₁ v₂ hv₂ z hz PP hPP
  obtain ⟨⟨v, pr, hpr⟩, hch⟩ := GlobalTheory.T.exists_charts_at_twist_places_chain D c w hw k hk.le s hs PP hPP
  obtain ⟨-, ⟨x₀, ϖ, hxϖ⟩, ⟨ι, hι⟩, hchi⟩ := hch v pr hpr
  obtain ⟨μT, hμu, hμT⟩ := hchi (c.chT (k + 1))
  obtain ⟨hv, hres, htame, hlift, hdict⟩ := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v pr hpr
  subst hv
  have hL : LiftsChar pr PP μT (w.ξ PP) := hlift k hk μT (Or.inr hμT)
  obtain ⟨⟨e, he, -, hH⟩, hlev, hlc⟩ := hdict ι hι
  have hH := hH x₀ ϖ hxϖ
  obtain ⟨-, hcard, hα⟩ := GlobalTheory.T.lower_block_parameter_twist_L_factor D c w hw k hk PP hPP _ pr hpr x₀ ϖ hxϖ
  obtain ⟨α, hαe⟩ : ∃ α : Fin (k * D.R.t) → ℂˣ,
      Finset.univ.val.map α = (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) := by
    set M := (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) with hM
    have hl : M.toList.length = k * D.R.t := by rw [Multiset.length_toList, hM, Multiset.card_map, hcard]
    refine ⟨fun i => M.toList.get (i.cast hl.symm), ?_⟩
    rw [Fin.univ_val_map, ← List.ofFn_congr hl, List.ofFn_get, Multiset.coe_toList]
  obtain ⟨hbd, hval⟩ := hα α hαe
  obtain ⟨e₀, he₁, he₂, he₃, hϖ⟩ := id hxϖ
  have hμϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x₀) := hμT x₀ ϖ ⟨e₀, he₁, he₂, he₃⟩
  letI : MeasurableSpace (Fv D.host.F (PP.under (𝓞 D.host.F))) := borel _
  haveI : BorelSpace (Fv D.host.F (PP.under (𝓞 D.host.F))) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F)))) := borel _
  haveI : BorelSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F)))) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv D.host.F (PP.under (𝓞 D.host.F)))
  obtain ⟨hPo, hPc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric (Fv D.host.F (PP.under (𝓞 D.host.F)))
    (Fin D.R.r) (Blocks k D.R.t)
  obtain ⟨m₀, hm₀, hm₁⟩ := exists_haar _ hPo hPc
  obtain ⟨cf, hcf⟩ : ∃ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F))) → ℂ, ∀ g, cf g =
      GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) _) (datum μT)) (datum μT) :=
    ⟨_, fun _ => rfl⟩
  have hcoef := GlobalTheory.T.weilCoefficient_splits_localFactor_twistPlace D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP _ pr hpr ι hι μT hμT ν hν cf hcf φ
  obtain ⟨hc1, ζ₀, hζ, hζ1, hint⟩ := GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector hU _ ν hν ϖ hϖ D.R.r D.R.t k μT 1 hμu (htame μT hL).1 (htame μT hL).2
    (fun _ _ => rfl) (fun _ => by simp) (qPar c PP x₀ k) α (((D.R.t : ℝ) - 1) / 2) (by rw [one_mul, hμϖ]; exact hαe)
    (by rw [hres]; exact hbd) _ hH m₀ hm₁ cf (by rw [one_mul]; exact hcf)
  obtain ⟨hI, hIv⟩ := hint (z : ℂ) (by rw [Complex.ofReal_re]; linarith)
  obtain ⟨J, μ, hJo, hμH, hμ1, hμI, hJ, hμv⟩ := transport e m₀ _ hPo hm₁ _ hI
  obtain ⟨hr, -, hst⟩ := id hs
  obtain ⟨hr', -, hst'⟩ := id hs'
  have hH1 : ∀ y ∈ parahoric _ (Fin D.R.r) (Blocks k D.R.t), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) = 1 := fun y hy =>
    hgt_one hH (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric.1 hy).1
  refine ⟨J, μ, _, hJo, hμH, hμ1, hμI, fun y hy => ?_, fun g => ?_, fun hzt => ?_, fun x hx hxv y => ?_⟩
  · have hy' := (hJ y).1 hy
    simp only [hζ1 _ hy', hH1 _ hy']
    simp
  · rw [hJ, ← hlev, he, ContinuousMulEquiv.apply_symm_apply]
    rfl
  · rw [hμv, hIv, hres, ← hval, hzt]
    push_cast
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective y
    simp only [ContinuousMulEquiv.symm_apply_apply]
    have hθ := hw.com.inf
    haveI : s.ν.IsHaarMeasure := hst.haar
    have hL2 : ∀ (u : s.CC c), ∀ v ∈ s.KF, MemL2Quotient (GQ s.V) s.ν fun g => conj (PiLocalization₂.val u v g) := fun u v hv =>
      memL2_of_cusp_form hC hθ (mem_cuspForms.1
        (GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hθ s.M hst.sigOK u.1 u.2 v hv)).1
    obtain ⟨V, _, _, π, u, ℓ, hg, hco, hℓ, hℓ1⟩ := rcoef_eq_coef s.ν hst.haar (hL2 u₁ v₁ hv₁) (hL2 u₂ v₂ hv₂) ι x
      (fun y => by rw [he]; exact (commute_emb _ _ _ hxv).eq) μT hμu ϖ (qPar c PP x₀ k)
      (hQ v₁ PP hPP _ pr hpr x₀ ϖ hxϖ μT hL ι hι) (fun j hj d hd g => by
        rw [val_type u₂ v₂ ((hlev j).2 hj), hlc μT hL j hj d hd, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
          Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hμu d]
        simp)
    have h3 := hζ V π u ℓ hg hco y
    rw [hℓ, hℓ1] at h3
    have h2 := hcoef x (by simp only [gAt, hxv, map_one]) y
    have hS : PP.under (𝓞 D.host.F) ∈ c.S := by
      classical
      refine Finset.mem_image.2 ⟨PP, ?_, rfl⟩
      rw [hw.union]
      exact Finset.mem_union_right _ hPP
    have h5 := hgt_split (A := s.V) (L := s.Λ) hst.selfDual ha.1 c.S hS
      (by simpa using hH1 1 (one_mem _)) hx hxv (e y) ((z : ℂ) - (D.R.t : ℂ) / 2)
    have hs0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
      have a1 : s.V.rank = D.R.r + k * D.R.t := hst.rank
      have a2 : s'.V.rank = D.R.r + (k + 1) * D.R.t := hst'.rank
      rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, a1, a2]
      push_cast
      ring
    have hw' : ∀ g, wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g := fun _ => rfl
    have hc1' : conj (cf 1) ≠ 0 := by simpa using hc1
    simp only [flatInt, integrand, hs0, hw']
    rw [h5, ← he]
    apply mul_left_cancel₀ hc1'
    linear_combination (GlobalTheory.Doubling.npow (hgtL s.V s.Λ a x) ((z : ℂ) - (D.R.t : ℂ) / 2) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) : ℝ) : ℂ) ^ ((z : ℂ) - (D.R.t : ℂ) / 2)) *
      (rcoef s.ν (fun g => conj (PiLocalization₂.val u₁ v₁ g)) (fun g => conj (PiLocalization₂.val u₂ v₂ g)) (x * ι y) * h2 +
        coefW p.ω m X (p.pt φ) x * h3)

end GlobalTheory.ChainTw.OnePlace

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (ζ : GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  atlas_forward_decl GlobalTheory.ChainTw.OnePlace.local_factor
end
