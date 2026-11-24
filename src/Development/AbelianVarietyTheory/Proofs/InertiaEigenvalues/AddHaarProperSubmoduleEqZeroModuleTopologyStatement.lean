module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarProperSubmoduleEqZeroModuleTopology
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ s : Submodule F V, s ≠ ⊤ → μ (s : Set V) = 0 := by
  first | exact @GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | exact GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | (intros; apply GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero <;> assumption)
