module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
