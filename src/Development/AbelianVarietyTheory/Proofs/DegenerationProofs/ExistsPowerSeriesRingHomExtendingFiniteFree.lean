module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompCMulMap
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

open TensorProduct

namespace GlobalTheory

theorem powerSeries_extend_finite_free (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K]
    [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K)
    (io : O₁ →+* K) (h : ∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧
      Φ PowerSeries.X = i PowerSeries.X ∧
      ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first
  | exact @_root_.GlobalTheory.PowerSeriesCompositionMap.main
  | exact _root_.GlobalTheory.PowerSeriesCompositionMap.main
  | (apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerSeriesCompositionMap.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerSeriesCompositionMap.main ..)

end GlobalTheory
