module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandCc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandKill
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EqZeroOfTest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.KillsOfIdem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Unfold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.average_eq_zero :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ e f : G → ℂ, Continuous e → Integrable e μ → Continuous f → Integrable f μ →
        (∀ x, conv μ e e x = e x) → (∀ x, conv μ e f x = f x) →
        ∀ x, (Continuous fun y => ∫ m, f (x * m * y) ∂ν) → ∀ y, ∫ m, f (x * m * y) ∂ν = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hν hinv hray e f hec hei hfc hfi hee hef x hcont
  have hKe : Kills μ N a e := kills_of_idem G μ N a H e hray hec hei hee
  have hKf : Kills μ N a f := by
    intro s C h hh z
    rw [conv_assoc G μ e f h C hec hei hfc hfi hh.1 hh.2.1 hef z]
    exact hKe s _ _ (conv_isEig G μ N a f h s C hfi hh) z
  refine eq_zero_of_test G μ (fun y => ∫ m, f (x * m * y) ∂ν) hcont ?_
  intro ψ hψ hψc
  rw [← conv_average G μ N a H ν hν hinv hray f ψ hfc hfi hψ hψc x]
  exact conv_band G μ N a H f _ hray hfc hfi hKf
    (isBand_of_compact G N a H ν hν hinv hray ψ hψ hψc).1 x
