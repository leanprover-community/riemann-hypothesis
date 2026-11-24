module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.StageZeroRow

theorem evW_of_atAll' {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.StageZeroRow
