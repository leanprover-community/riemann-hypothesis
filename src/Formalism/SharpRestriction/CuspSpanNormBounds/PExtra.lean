module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PX

section GroupS0

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Exp (D : D7) : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def GDr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Lat.Gval (X.fl t) (X.fl' t))).re)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def RanksF (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

end Family

end GroupS0

section GroupS1

open Formalism.MainNotions.S

end GroupS1

section GroupS5

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def StdHypS (Cg cb Cu cT CT C0 Ch Cβ : ℝ) : Prop :=
  ∀ Cs Cs', OwnEv Fm fun C' Cl x i => StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ

def TFrame (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    ∀ w, 1 ≤ Tr (Fm.D x i) w * kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS)

end GroupS5

end Formalism.MainNotions.PX

end
