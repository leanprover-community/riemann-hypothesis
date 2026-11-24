module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyUnivOfNullCone
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

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.isFibreFamily_univ_of_null_cone' : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  first | exact @GlobalTheory.isFibreFamily_univ_of_null_cone | exact GlobalTheory.isFibreFamily_univ_of_null_cone | (intros; apply GlobalTheory.isFibreFamily_univ_of_null_cone <;> assumption)
