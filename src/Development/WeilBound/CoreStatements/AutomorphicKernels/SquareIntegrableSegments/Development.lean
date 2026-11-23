module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CohomologicalCsdTemperedOfUsed
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.ExistsUnitaryCentralTwist
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentOfTwistedSquareIntegrable
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TempProdUsedOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL (k := k)), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  exact PositivityTheory.PfEss.H13.segment_of_twisted_square_integrable hU

theorem exists_unitary_central_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)), ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1 := by
  exact PositivityTheory.PfEss.H2.exists_unitary_central_twist hA

theorem segment_gives_square_integrable (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL (k := k)), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  exact PositivityTheory.PfEss.H13.square_integrable_of_segment_twist (exists_unitary_central_twist hA) hA hF

theorem essSquareIntegrableSegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments := by
  intro k _ _ _ _ _ δ hδ
  exact ⟨segment_of_twisted_square_integrable (PositivityTheory.Zltwo.essSqIntUsed_of hE hS hL) k δ hδ, segment_gives_square_integrable hA hF k (hJ k) δ⟩

end PositivityTheory.PfEss

end
