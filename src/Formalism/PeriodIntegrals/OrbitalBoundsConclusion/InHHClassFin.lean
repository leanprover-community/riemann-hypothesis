module

public import Formalism.PeriodIntegrals.InHHClassFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.CTFromBlocks
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.ClassSetFinIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.FrHformSumLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.LevelStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.OneMemKg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.SigConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem stabClassFinite : PI.InHHClassFin.StabClassFinite :=
  PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
    (fun _ _ Γ K K' h => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono Γ K K' h)
    (fun _ _ Γ K K' h hi => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx Γ K K' h hi)
    (fun _ _ _ _ Φ Γ K => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map Φ Γ K)
    PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd PI.UnitaryGroupMassFormula.InHHClassFin.sigConj PI.UnitaryGroupMassFormula.InHHClassFin.frameExists
    PI.UnitaryGroupMassFormula.InHHClassFin.frameIso PI.UnitaryGroupMassFormula.InHHClassFin.frameGram PI.UnitaryGroupMassFormula.InHHClassFin.frameRat
    PI.UnitaryGroupMassFormula.InHHClassFin.levelStep
