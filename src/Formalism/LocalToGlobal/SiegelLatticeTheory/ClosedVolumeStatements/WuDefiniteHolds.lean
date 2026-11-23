module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InHHClassFin
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Closed

section

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem WuDefinite_holds : Formalism.L2.SG.PoincareInHH.Cut.WuDefinite X u := by
  first
  | exact Formalism.L2.SG.PoincareInHH.Cut.wuDefinite_holds X u
  | exact Formalism.L2.SG.PoincareInHH.Cut.wuDefinite_holds (X := X) (u := u)

theorem ClassFin_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK := by
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  exact stabClassFinite X.B.I (fixSet X u) (WuDefinite_holds X u) (Ku X u hK) X.B.g (X.xu u) hg
    (fun h hh => ((Formalism.L2.SG.Closed.level_subgroup_properties X).1 _ hh).1)

theorem ColBound_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.Pf.ColBound X u hK := by
  first
  | exact Formalism.L2.SG.Pf.colBound_of X u hK (ClassFin_holds X u hK)
  | exact Formalism.L2.SG.Pf.colBound_of (X := X) (u := u) hK (ClassFin_holds X u hK)

theorem OmCover_holds (I : AutInst) : Formalism.L2.SG.Pf.OmCover I := by
  first
  | exact Formalism.L2.SG.Pf.omCover_holds I
  | exact Formalism.L2.SG.Pf.omCover_holds (I := I)

theorem MultPoly_holds : Formalism.L2.SG.PoincareInHH.Cut.MultPoly X :=
  Formalism.L2.SG.Pf.multPoly_holds_of'' X (OmCover_holds _)

end

end Formalism.L2.SG.Closed
