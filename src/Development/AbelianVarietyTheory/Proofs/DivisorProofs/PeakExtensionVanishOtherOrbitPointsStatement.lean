module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peakExtension_vanish_other_orbit_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X → ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) → (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' → (∀ w ∈ Metric.ball (0 : V (nd X)) ρ', ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) → DifferentiableOn ℂ F (OmF X x) → ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z) ∂muF X x < ⊤ → ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) → ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  first | exact @GlobalTheory.PeakOrbit.vanish_translate | exact GlobalTheory.PeakOrbit.vanish_translate | (intros; apply GlobalTheory.PeakOrbit.vanish_translate <;> assumption)
