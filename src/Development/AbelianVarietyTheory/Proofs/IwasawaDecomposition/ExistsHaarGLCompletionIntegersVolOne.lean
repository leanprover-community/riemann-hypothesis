module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory

theorem haar_glInt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  intro L _ _ P r
  have hc : IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P) r
  have ho : IsOpen ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers P) r
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]; exact ⟨1, (GLint (OP P) r).one_mem⟩⟩
  refine ⟨Measure.haarMeasure K₀, Measure.isMulLeftInvariant_haarMeasure K₀, ?_⟩
  exact Measure.haarMeasure_self

end GlobalTheory
