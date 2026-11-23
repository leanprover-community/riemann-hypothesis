module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRa
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gC {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℂ :=
  if c.val < D.R.k then 1 else -(1 / ((Formalism.L2.SG.RealObj.Tw u : ℝ) : ℂ))

def RowParseval : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x y : (VS D).V),
    (∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) →
    (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    ∀ v : InfinitePlace X.B.I.F,
      ∑ c, rowV X u x v c * star (rowV X u y v c) * gC u c = X.B.I.φ v (X.ιE.symm ((VS D).hT x y))

def RowRank : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS),
    Nonempty (Module.Basis (Fin (Module.finrank ℚ D.host.E * (D.R.k + 1))) ℤ ((aaLbS X b).restrictScalars ℤ))

def TraceRe : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : D.host.E),
    ∑ v : InfinitePlace X.B.I.F, (X.B.I.φ v (X.ιE.symm t)).re = ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) / 2

end Formalism.L2.SG.Pf.NcReal.JX.CovB
