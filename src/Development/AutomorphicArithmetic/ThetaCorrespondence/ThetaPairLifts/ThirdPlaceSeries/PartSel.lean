module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3Iff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc
section Point
variable {D : D7} {O : Obj D} {c : ℝ}
def BundleCondition.TiePins (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
abbrev BundleCondition.Comparison₂ (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Type 1 := {Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q // b.TiePins Rr}
theorem BundleCondition.Comparison₂.psi {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1
theorem BundleCondition.Comparison₂.pins3 {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q := t.2.2.1
theorem BundleCondition.Comparison₂.pins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := let ⟨h, _⟩ := t.2.2.2; h
theorem BundleCondition.Comparison₂.recPins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationCompatible t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h
@[reducible] def BundleCondition.part (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) : _root_.GlobalTheory.Fc.Ind.PointSummands D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins
end Point
def HasCompatibility : BdP _root_.GlobalTheory.Fc.BundleCondition := fun _ _ _ b => Nonempty b.Comparison₂
section Sel
variable {𝒜 : FamClass}
abbrev CompatibleSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂
def summandSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) (τ : _root_.GlobalTheory.Fc.CompatibleSelection σ) : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)
end Sel
section Construction₂
end Construction₂
end GlobalTheory.Fc
end
end
