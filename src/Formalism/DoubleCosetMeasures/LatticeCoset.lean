module

public import Formalism.DoubleCosetMeasures.StatementV
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
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

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
