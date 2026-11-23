module

import Development.WeilBound.CoreStatements.PlaceConnectedComponents.ArtinKer
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace CompanionTheory.FamInh

theorem isOpen_connInf (E : Type) [Field E] [NumberField E] :
    IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) :
      Set (InfiniteAdeleRing E)ˣ) := by
  apply PositivityTheory.FamInh.isOpen_connInf <;> assumption

theorem ofInfinite_eq_map (E : Type) [Field E] [NumberField E] (y : (InfiniteAdeleRing E)ˣ) :
    (ofInfinite y : IdeleGroup E) =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) y := by
  apply PositivityTheory.FamInh.ofInfinite_eq_map <;> assumption

theorem comap_connectedComponent (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by
  apply PositivityTheory.FamInh.comap_connectedComponent <;> assumption

end CompanionTheory.FamInh

end
