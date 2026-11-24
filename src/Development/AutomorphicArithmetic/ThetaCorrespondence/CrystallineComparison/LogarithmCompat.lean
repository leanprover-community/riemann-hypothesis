module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.MemKerPowIff
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly
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

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem logarithm_compat : ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (equivDeRhamPlus l y) := by
  intro P AI y
  exact (LogF.isLog_iff l AI.ε y).trans (Cmp6.isLogA_iff_cP l AI.ε y)

end Formalism.BasicNotions.CmpTie
