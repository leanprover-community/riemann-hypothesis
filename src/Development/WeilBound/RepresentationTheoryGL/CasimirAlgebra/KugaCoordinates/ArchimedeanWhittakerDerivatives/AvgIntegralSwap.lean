module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgIntervalIntegralSwap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgSubOfPer
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

namespace PositivityTheory.Rg.Cz

open GlobalTheory.CuspGeneric MeasureTheory

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G]

theorem avg_sub (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ Φ' : G → ℂ) (h : Per Γ Φ) (h' : Per Γ Φ') :
    avg Γ (fun x => Φ x - Φ' x) = avg Γ Φ - avg Γ Φ' :=
  GlobalTheory.CompanionTheory.CuspGeneric.avg_sub_of_per Γ hΓ Φ Φ' h h'

theorem avg_integral_swap (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (F : G × ℝ → ℂ) (hF : Continuous F)
    (hp : ∀ γ ∈ Γ, ∀ x s, F (γ + x, s) = F (x, s)) (t : ℝ) :
    avg Γ (fun x => ∫ s in (0 : ℝ)..t, F (x, s)) = ∫ s in (0 : ℝ)..t, avg Γ (fun x => F (x, s)) :=
  GlobalTheory.CompanionTheory.AvgSwap.avg_intervalIntegral_swap Γ hΓ F hF hp t

end PositivityTheory.Rg.Cz
