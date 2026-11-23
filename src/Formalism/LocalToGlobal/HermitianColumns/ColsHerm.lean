module

public import Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff
public import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty
public import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
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

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GTied (D : D7) (H : HermTied D) : Type :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    GLevTie (H.lev0 u) (D.gat u w hg)

structure FullTied (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  g : GTied D base
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

structure ColsHerm (D : D7) where
  base : HermCols D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : Lev0Tied D base atT
  ad : AdTied D base atT
  cof : CofTied D base atT
  piG : PiGConst D base atT levelZeroCompatibility
  stabMap : StabMapTied D base atT
  fvI : FvStepTied D base atT
  std : StdTied D
  baseL : BaseTied D base atT

def FullTied.cols {D : D7} (X : FullTied D) : ColsHerm D where
  base := X.base.toHermCols
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

end Formalism.L2.Herm

end
