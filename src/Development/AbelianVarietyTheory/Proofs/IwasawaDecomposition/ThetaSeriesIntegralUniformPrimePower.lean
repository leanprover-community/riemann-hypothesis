module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCoverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0, GlobalTheory.T.unramified_descent_integral_forms_tower_cover D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

end GlobalTheory
