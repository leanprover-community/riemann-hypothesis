module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.GramExponentArithmetic
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembFinal
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution
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

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.TestSideWords

theorem proposition5_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60 :=
  proposition5_of_three_parts D CLa Ck Crk Cdeg (restPick D CLa Ck Crk Cdeg) (restMemb D CLa Ck Crk Cdeg) (restNum D CLa Ck Crk Cdeg)

theorem stmtE_of_mem (D : Formalism.BasicNotions.D7) (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_MP D hM fun CLa Ck Crk Cdeg => proposition5_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
