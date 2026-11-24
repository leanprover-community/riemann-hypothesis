module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ExistsLatticeNormGePow
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2OfX
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.PsiVTrPairAddLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.SetIntegralCharEqZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

theorem locFinX : PositivityTheory.SiegelWeilFormula.Gen.LocFinX := locFinX_of shellP convP dualP

theorem locFin2 : PositivityTheory.SiegelWeilFormula.Gen.LocFin2 := locFin2_of_X locFinX

end PositivityTheory.SiegelWeilFormula.SwLocFin
