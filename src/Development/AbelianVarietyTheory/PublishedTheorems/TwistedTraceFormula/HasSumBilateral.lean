module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG GlobalTheory.GLDoubling
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_haar (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] :
    ∃ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure ∧ μ (KO k (Fin n)) = 1 := by
  have ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isOpen_KO
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isCompact_KO
  let K : TopologicalSpace.PositiveCompacts (GL (Fin n) k) := ⟨⟨_, hc⟩, by
    rw [show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.GLDoubling.Model
