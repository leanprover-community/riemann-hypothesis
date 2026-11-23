module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val

end MassDataLevelSSteps
