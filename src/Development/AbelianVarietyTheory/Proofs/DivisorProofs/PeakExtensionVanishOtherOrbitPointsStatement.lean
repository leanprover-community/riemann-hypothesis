module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

theorem _root_.GlobalTheory.T.peakExtension_vanish_other_orbit_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X → ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) → (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' → (∀ w ∈ Metric.ball (0 : V (nd X)) ρ', ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) → DifferentiableOn ℂ F (OmF X x) → ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z) ∂muF X x < ⊤ → ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) → ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  first | exact @GlobalTheory.PeakOrbit.vanish_translate | exact GlobalTheory.PeakOrbit.vanish_translate | (intros; apply GlobalTheory.PeakOrbit.vanish_translate <;> assumption)
