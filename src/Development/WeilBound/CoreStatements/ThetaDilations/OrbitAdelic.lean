module

public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import CompanionTheory.AutomorphicTheory.ThetaDilations.OrbitAdelic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

def LN (F ι : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  zero_mem' := fun _ => ⟨0, fun _ => zero_mem _, (mul_zero _).symm⟩
  add_mem' := fun ha hb i => by
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨y', hy', e'⟩ := hb i
    exact ⟨y + y', fun v => add_mem (hy v) (hy' v), by rw [Pi.add_apply, e, e', mul_add]⟩
  neg_mem' := fun ha i => by
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, fun v => neg_mem (hy v), by rw [Pi.neg_apply, e, mul_neg]⟩

end PositivityTheory.PlacePermOperatorBicommutantSpan
