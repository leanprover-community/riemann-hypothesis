module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig


open ReciprocityTheory.ChartRestriction.G.AI.I2 in
theorem pfCoord_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  rintro ⟨II, hSys, -, hPF, -⟩
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hL'
  have hU : UniqueStatement :=
    GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd hP (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι _)
    · exact h
  have hL's : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.isSmoothHerm_pull hv (hL j) (hL' j)
  have e1 : I K' ι' (mCoordIdeal y) d L' = II K' ι' (mCoordIdeal y) d L' :=
    hU K' ι' (I K' ι') (II K' ι') (IsIntersectionFamily.isRFamily (hI K' ι'))
      (IsIntersectionFamily.isRFamily (hSys K' ι')) _ d L' hd hP' hL's
  have e2 : I K ι (imageZ v (mCoordIdeal y)) d L = II K ι (imageZ v (mCoordIdeal y)) d L :=
    hU K ι (I K ι) (II K ι) (IsIntersectionFamily.isRFamily (hI K ι))
      (IsIntersectionFamily.isRFamily (hSys K ι)) _ d L hd hP hL
  rw [e1, e2]
  exact hPF K ι K' ι' κ v Ω y d L L' hv hP' hP hL hL'

theorem pfCoord : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement :=
  pfCoord_of_system

end PositivityTheory.HtPt.Aig
