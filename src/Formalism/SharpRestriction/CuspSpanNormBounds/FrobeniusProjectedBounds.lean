module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FrobeniusProjectedBounds

open Formalism.BasicNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7)

def kR : ℝ := D.R.k

def mR : ℝ := D.R.m

def fR : ℝ := D.R.f

def rR : ℝ := D.R.rS

def nR : ℝ := D.R.r

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def Gam : ℝ := (D.mem D.u₀).A.GamP

end Letters


variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}



variable (D : D7)


def Hyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

section Statements

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

def adm5 (c C : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, hsNormSq (KOf D.s u u' (famNG D.s)) ≤
    (Real.exp (-(c * kR D * fR D * Real.log (kR D))) +
      (2 : ℝ) ^ (-(kR D - 2 * rR D - 5)) * Real.exp (C * mR D ^ 5 * fR D * large₂.sc.L)) *
      (du D u * du D u') / Dst D

def adm7 (c : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  |Dall D - Dst D| ≤ Real.exp (-(c * nR D * fR D * Real.log (nR D))) * Dst D

def eF (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / Gam D + 2 * Real.exp (-(kR D * fR D * Real.log (kR D)))

end Statements


variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]



variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Cg cb Cu cT CT C0 : ℝ)


end Formalism.MainNotions.FrobeniusProjectedBounds
